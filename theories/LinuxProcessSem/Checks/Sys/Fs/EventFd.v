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
  Prelude Fs.Open.

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

    BELOW THE GATE the call creates a descriptor, and the acceptor is
    [Fs.Open.check_new_fd_result], the one [openat] and [socket] use: an
    errno of [Sys.Fs.EventFd.eventfd2_errnos], or the lowest free fd
    with a new [State.FdEventfd] behind it.  The context is written out
    field for field as the spec builds it -- [count] is ARGUMENT 0, the
    low 32 bits of the register; EFD_SEMAPHORE and O_NONBLOCK come out
    of the flag word -- so a checker that stored the wrong counter or
    dropped a bit answers a different model, and the completeness lemma
    fails.

    [check_ret_only] and [check_new_fd_result] carry the rest of the
    obligation: each rejects any effect with a non-empty write, zero,
    unmap, copy or copy-in ledger, which is what pins that a conforming
    run may not smuggle a store past an arm that stores nothing.
    [eventfd2] reads no user memory and writes none, so all six ledgers
    are empty on every answer this arm gives. *)
Definition check_eventfd2 (i : SyscallInput) (flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (Z.eqb (Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET) 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    check_new_fd_result eventfd2_errnos eff m
      (fun fd =>
         with_fds
           (fd_insert (m_fds m) fd
              (FdEventfd
                 (mkEventfdCtx (bv_unsigned (abi_low32 (in_arg i 0)))
                    (negb (Z.eqb (Z.land (bv_unsigned flags) EFD_SEMAPHORE) 0))
                    (negb (Z.eqb (Z.land (bv_unsigned flags) O_NONBLOCK) 0)))))
           m).

(** Both sides of every proof below branch on the same equality.
    Splitting THAT — rather than the assembled condition — is what keeps
    the tactic from depending on the two files spelling the gate with
    the same negation, which is exactly the coincidence the restatement
    exists to avoid relying on. *)
Ltac eventfd2_gate flags :=
  unfold eventfd2_spec, eventfd2_einval_b in *;
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET) 0);
  cbn [negb] in *; cbv beta iota in *.

Lemma check_eventfd2_sound_ok : forall i flags eff m m' evs,
  check_eventfd2 i flags eff m = CheckOk m' evs ->
  eventfd2_spec flags i m (Ok eff m' evs).
Proof.
  intros i flags eff m m' evs H.
  unfold check_eventfd2 in H. eventfd2_gate flags.
  2:{ apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->).
      apply pure_ok. }
  (* past the gate: the injected failure, or the lowest free fd *)
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  unfold check_new_fd_result in H.
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|w ws'];
    destruct zs as [|z zs']; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
  destruct (errno_ret_in eventfd2_errnos ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0; [apply (choose_ok _ e); exact HIn|].
    apply pure_ok.
  - destruct (fd_lookup (m_fds m) ret) eqn:Hfr; [discriminate|].
    destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq.
    apply alt_r.
    eapply bind_ok0; [apply (choose_ok _ ret); split; assumption|].
    cbv beta. eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_eventfd2_sound_unmodeled : forall i flags eff m,
  check_eventfd2 i flags eff m = CheckUnmodeled ->
  eventfd2_spec flags i m Unmodeled.
Proof.
  intros i flags eff m H.
  unfold check_eventfd2 in H. eventfd2_gate flags.
  - now apply check_new_fd_result_no_unmodeled in H.
  - now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_eventfd2_complete_ok : forall i flags eff m m' evs,
  eventfd2_spec flags i m (Ok eff m' evs) ->
  check_eventfd2 i flags eff m = CheckOk m' evs.
Proof.
  intros i flags eff m m' evs H.
  unfold check_eventfd2. eventfd2_gate flags;
    sys_unfold; cbv beta iota zeta in H; inv_ok.
  - (* injected failure *)
    unfold check_new_fd_result.
    match goal with
    | |- context [errno_ret_in ?es (errno_ret ?e)] =>
        rewrite (errno_ret_in_intro es e) by assumption
    end.
    reflexivity.
  - (* success: the lowest free fd, holding the new counter *)
    unfold check_new_fd_result.
    rewrite errno_ret_in_alloc_fd by reflexivity.
    match goal with H : fd_lookup _ _ = None |- _ => rewrite H end.
    rewrite bv_eqb_refl. reflexivity.
  - apply check_ret_only_ok_iff; auto.
Qed.

(** Neither answer declines: the gate's -EINVAL and the [alt] past it
    are both total, so the premise is unsatisfiable on both arms. *)
Lemma check_eventfd2_complete_unmodeled : forall i flags m eff,
  eventfd2_spec flags i m Unmodeled ->
  check_eventfd2 i flags eff m = CheckUnmodeled.
Proof.
  intros i flags m eff H.
  unfold check_eventfd2. eventfd2_gate flags;
    sys_unfold; cbv beta iota zeta in H; exfalso; inv_ok.
Qed.
