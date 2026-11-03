(** * LinuxProcessSem.Checks.Sys.Fs.EventFd — the eventfd2 (19) checker, and its proofs

    Mirrors [Sys/Fs/EventFd.v], which answers to Linux [fs/eventfd.c]:
    this file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import
  Fs.Open.

(** The gate is WRITTEN OUT rather than taken from
    [Sys.Fs.EventFd.eventfd2_einval_b], and the four lemmas below are
    what make the repetition worth its cost: they force this statement
    and the spec's to coincide.  Importing the spec's predicate would
    leave a wrong gate agreeing with itself, which is the reason
    [Checks/Sys/Fs/Timerfd] restates its own gate instead of sharing it.

    Note what the repetition does NOT buy, because the difference
    matters here more than usual: an identical MISTAKE made in both
    files still closes every proof.  These lemmas relate the checker to
    the spec and never either to Linux.  They do not show that the
    admitted mask really is Linux's [EFD_FLAGS_SET].

    [check_ret_only] carries the -EINVAL arm's obligation: it rejects
    any effect with a non-empty write, zero, unmap, copy or copy-in
    ledger, which is what pins that a conforming run may not smuggle a
    store past an arm that stores nothing.  An accepted flag word is
    [Open.check_new_fd_result]'s shape, the one [openat], [socket] and
    [accept4] share: an errno from [eventfd2_errnos], or the lowest free
    descriptor bound to [State.OEventFd flags], and nothing written. *)
Definition check_eventfd2 (flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if negb (Z.eqb (Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET) 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else check_new_fd_result eventfd2_errnos eff m
         (fun fd => with_fds (fd_insert (m_fds m) fd (FdOpaque (OEventFd flags))) m).

(** Both sides of every proof below branch on the same equality.
    Splitting THAT — rather than the assembled condition — is what keeps
    the tactic from depending on the two files spelling the gate with
    the same negation, which is exactly the coincidence the restatement
    exists to avoid relying on. *)
Ltac eventfd2_gate flags :=
  unfold eventfd2_spec, eventfd2_einval_b in *;
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET) 0);
  cbn [negb] in *.

Lemma check_eventfd2_sound_ok : forall flags eff m m' evs i,
  check_eventfd2 flags eff m = CheckOk m' evs ->
  eventfd2_spec flags i m (Ok eff m' evs).
Proof.
  intros flags eff m m' evs i H.
  unfold check_eventfd2 in H. eventfd2_gate flags; cbv iota in H |- *.
  - (* accepted: the injected errno, or the lowest free fd *)
    eapply bind_ok0; [apply get_model_ok|]. cbv beta.
    unfold check_new_fd_result in H.
    destruct eff as [ret ws zs us cs copyins]; destruct ws as [|w ws'];
      destruct zs as [|z zs']; destruct us as [|? ?];
      destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
    destruct (errno_ret_in eventfd2_errnos ret) eqn:He.
    + inversion H; clear H; subst.
      apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
      apply alt_l. eapply bind_ok0; [apply (choose_ok _ e); exact HIn|].
      apply pure_ok.
    + destruct (fd_lookup (m_fds m) ret) eqn:Hfr; [discriminate|].
      destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; [|discriminate].
      inversion H; clear H; subst. apply bv_eqb_eq in Heq.
      apply alt_r.
      eapply bind_ok0; [apply (choose_ok _ ret); split; assumption|].
      cbv beta. eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
  - apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->).
    apply pure_ok.
Qed.

Lemma check_eventfd2_sound_unmodeled : forall flags eff m i,
  check_eventfd2 flags eff m = CheckUnmodeled ->
  eventfd2_spec flags i m Unmodeled.
Proof.
  intros flags eff m i H.
  unfold check_eventfd2 in H. eventfd2_gate flags; cbv iota in H.
  - exfalso. exact (check_new_fd_result_no_unmodeled _ _ _ _ H).
  - exfalso. now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_eventfd2_complete_ok : forall flags eff m m' evs i,
  eventfd2_spec flags i m (Ok eff m' evs) ->
  check_eventfd2 flags eff m = CheckOk m' evs.
Proof.
  intros flags eff m m' evs i H.
  unfold check_eventfd2. eventfd2_gate flags; cbv iota in H |- *.
  - unfold check_new_fd_result. sys_unfold. cbv iota in H. inv_ok.
    + match goal with
      | |- context [errno_ret_in ?es (errno_ret ?e)] =>
          rewrite (errno_ret_in_intro es e) by assumption
      end.
      reflexivity.
    + rewrite errno_ret_in_alloc_fd by reflexivity.
      match goal with H : fd_lookup _ _ = None |- _ => rewrite H end.
      rewrite bv_eqb_refl. reflexivity.
  - sys_unfold; inv_ok; apply check_ret_only_ok_iff; auto.
Qed.

Lemma check_eventfd2_complete_unmodeled : forall flags m i eff,
  eventfd2_spec flags i m Unmodeled ->
  check_eventfd2 flags eff m = CheckUnmodeled.
Proof.
  intros flags m i eff H.
  unfold check_eventfd2. eventfd2_gate flags;
    sys_unfold; try reflexivity; inv_ok.
Qed.
