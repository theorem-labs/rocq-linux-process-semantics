(** * LinuxProcessSem.Checks.Sys.Fs.Sync — the fsync (82), fdatasync (83) checkers, and their proofs

    Mirrors [Sys/Fs/Sync.v], which answers to Linux [fs/sync.c]: this
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

Definition check_fsync (fd : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdChannel _) => check_ret_only eff (errno_ret EINVAL) m []
  | Some (FdSocket _)  => check_ret_only eff (errno_ret EINVAL) m []
  | Some (FdStream _ _ _) => check_ret_only eff (errno_ret EINVAL) m []
  | Some (FdDgram _)   => check_ret_only eff (errno_ret EINVAL) m []
  | Some (FdEventfd _) => check_ret_only eff (errno_ret EINVAL) m []
  | Some (FdPipe _ _)  => check_ret_only eff (errno_ret EINVAL) m []
  | Some (FdDevNull _ _) => check_ret_only eff (errno_ret EINVAL) m []
  | Some FdUrandom => check_ret_only eff (errno_ret EINVAL) m []
  | Some (FdFileA _ _) => check_ret_only eff (Z_to_bv 64 0) m []
  | Some (FdFileRW _ _) => check_ret_only eff (Z_to_bv 64 0) m []
  | Some (FdFile _ _)  => check_ret_only eff (Z_to_bv 64 0) m []
  | Some (FdFileW _ _) => check_ret_only eff (Z_to_bv 64 0) m []
  | Some FdDir         => check_ret_only eff (Z_to_bv 64 0) m []
  | Some (FdAnon _ _)  => check_ret_only eff (Z_to_bv 64 0) m []
  end.

Lemma check_fsync_sound_ok : forall fd eff m m' evs i,
  check_fsync fd eff m = CheckOk m' evs ->
  fsync_spec fd i m (Ok eff m' evs).
Proof.
  intros fd eff m m' evs i H.
  unfold check_fsync in H. unfold fsync_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; [destruct e|];
    apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
    (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota; srw Hfd;
    apply pure_ok.
Qed.

(** [check_fsync] never declines -- every [FdEntry] gets an answer, and
    so does a closed fd -- so this is discharged by ruling the hypothesis
    out rather than by exhibiting an [Unmodeled] run. *)

Lemma check_fsync_sound_unmodeled : forall fd eff m i,
  check_fsync fd eff m = CheckUnmodeled -> fsync_spec fd i m Unmodeled.
Proof.
  intros fd eff m i H. unfold check_fsync in H.
  destruct (fd_lookup (m_fds m) fd) as [e|]; [destruct e|];
    now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_fsync_complete_ok : forall fd eff m m' evs i,
  fsync_spec fd i m (Ok eff m' evs) -> check_fsync fd eff m = CheckOk m' evs.
Proof.
  intros fd eff m m' evs i H.
  unfold fsync_spec in H. unfold check_fsync. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; [destruct e|];
    hall Hfd; inv_ok;
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

(** Symmetrically, [fsync_spec] has no [unmodeled] arm, so the hypothesis
    here is contradictory. *)

Lemma check_fsync_complete_unmodeled : forall fd m i eff,
  fsync_spec fd i m Unmodeled -> check_fsync fd eff m = CheckUnmodeled.
Proof.
  intros fd m i eff H.
  unfold fsync_spec in H. sys_unfold. cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; [destruct e|];
    hall Hfd; inv_ok; discriminate.
Qed.

(* ------------------------------------------------------------- ftruncate *)
