(** * LinuxProcessSem.Checks.Sys.Kernel.Nsproxy — the setns (268) checker, and its proofs

    Mirrors [Sys/Kernel/Nsproxy.v], which answers to Linux
    [kernel/nsproxy.c]: this file holds the checkers for the syscalls
    defined there, and no others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export Prelude.

(** [Kernel.Nsproxy.setns_spec] as an acceptor, row for row: -EBADF on
    no descriptor and on an O_PATH one, the decline on [State.ONsFile],
    -EINVAL on every other kind.  Every answer is an errno that changes
    nothing. *)
Definition check_setns (fd : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdOpaque (OProcPath _)) => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdOpaque (ONsFile _)) => CheckUnmodeled
  | Some _ => check_ret_only eff (errno_ret EINVAL) m []
  end.

Lemma check_setns_sound_ok : forall fd eff m m' evs i,
  check_setns fd eff m = CheckOk m' evs ->
  setns_spec fd i m (Ok eff m' evs).
Proof.
  intros fd eff m m' evs i H.
  unfold check_setns in H. unfold setns_spec.
  destruct (fd_lookup (m_fds m) fd)
    as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |[p|p|fl|h|fl pos|mask fl|live|pt]]|] eqn:Hfd;
    try discriminate;
    apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
    (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota; srw Hfd;
    apply pure_ok.
Qed.

(** [check_setns] declines only [State.ONsFile], as the spec does; on
    every other kind, and on a closed fd, it answers, so those cases are
    discharged by ruling the hypothesis out. *)
Lemma check_setns_sound_unmodeled : forall fd eff m i,
  check_setns fd eff m = CheckUnmodeled -> setns_spec fd i m Unmodeled.
Proof.
  intros fd eff m i H. unfold check_setns in H. unfold setns_spec.
  destruct (fd_lookup (m_fds m) fd)
    as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |[p|p|fl|h|fl pos|mask fl|live|pt]]|] eqn:Hfd;
    try (now apply check_ret_only_no_unmodeled in H).
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd.
  apply unmodeled_intro.
Qed.

Lemma check_setns_complete_ok : forall fd eff m m' evs i,
  setns_spec fd i m (Ok eff m' evs) -> check_setns fd eff m = CheckOk m' evs.
Proof.
  intros fd eff m m' evs i H.
  unfold setns_spec in H. unfold check_setns. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd)
    as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |[p|p|fl|h|fl pos|mask fl|live|pt]]|] eqn:Hfd;
    hall Hfd; inv_ok;
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma check_setns_complete_unmodeled : forall fd m i eff,
  setns_spec fd i m Unmodeled -> check_setns fd eff m = CheckUnmodeled.
Proof.
  intros fd m i eff H.
  unfold setns_spec in H. unfold check_setns. sys_unfold. cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd)
    as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |[p|p|fl|h|fl pos|mask fl|live|pt]]|] eqn:Hfd;
    hall Hfd; inv_ok; try discriminate; reflexivity.
Qed.
