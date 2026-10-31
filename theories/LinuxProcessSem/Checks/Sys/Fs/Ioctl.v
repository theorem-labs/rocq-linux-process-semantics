(** * LinuxProcessSem.Checks.Sys.Fs.Ioctl — the ioctl (29) checkers, and their proofs

    Mirrors [Sys/Fs/Ioctl.v], which answers to Linux [fs/ioctl.c]: this
    file holds the checkers for the syscalls defined there, and no
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
  Prelude Fs.ReadWrite.

Definition check_ioctl (fd req : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdChannel _) | Some (FdFile _ _) | Some (FdFileW _ _) | Some FdDir
  | Some (FdSocket _) | Some (FdStream _ _ _) | Some (FdPipe _ _) | Some (FdFileA _ _)
  | Some (FdFileRW _ _) | Some (FdDevNull _ _) =>
      if tty_only_request req then check_ret_only eff (errno_ret ENOTTY) m []
      else CheckUnmodeled
  | Some FdUrandom => CheckUnmodeled
  end.

Lemma check_ioctl_sound_ok : forall fd req eff m m' evs i,
  check_ioctl fd req eff m = CheckOk m' evs -> ioctl_spec fd req i m (Ok eff m' evs).
Proof.
  intros fd req eff m m' evs i H.
  unfold check_ioctl in H. unfold ioctl_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  - (* enumerated open-fd arms: [e] must be destructed for the match to
       reduce; every constructor answers alike. *)
    destruct e; destruct (tty_only_request req) eqn:Hr; try discriminate;
      apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota;
      srw Hfd; apply pure_ok.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply pure_ok.
Qed.

Lemma check_ioctl_sound_unmodeled : forall fd req eff m i,
  check_ioctl fd req eff m = CheckUnmodeled -> ioctl_spec fd req i m Unmodeled.
Proof.
  intros fd req eff m i H.
  unfold check_ioctl in H. unfold ioctl_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  - (* enumerated open-fd arms: destruct [e] so the match reduces. *)
    destruct e; destruct (tty_only_request req) eqn:Hr;
      try (now apply check_ret_only_no_unmodeled in H);
      (eapply bind_unmodeled2; [apply get_model_ok|]); cbv beta iota;
      srw Hfd; apply unmodeled_intro.
  - now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_ioctl_complete_ok : forall fd req eff m m' evs i,
  ioctl_spec fd req i m (Ok eff m' evs) -> check_ioctl fd req eff m = CheckOk m' evs.
Proof.
  intros fd req eff m m' evs i H.
  unfold ioctl_spec in H. unfold check_ioctl. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; hall Hfd; inv_ok;
    try destruct e;
    try (destruct (tty_only_request req) eqn:Hr; hall Hr; inv_ok);
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma check_ioctl_complete_unmodeled : forall fd req m i eff,
  ioctl_spec fd req i m Unmodeled -> check_ioctl fd req eff m = CheckUnmodeled.
Proof.
  intros fd req m i eff H.
  unfold ioctl_spec in H. unfold check_ioctl. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; hall Hfd; inv_ok;
    try destruct e;
    try (destruct (tty_only_request req) eqn:Hr; hall Hr; inv_ok);
    reflexivity.
Qed.
