(** * LinuxProcessSem.Checks.ProcsChildPidsFrame — which released answers move the list of unreaped children

    Not part of the trusted specification: QA on [State.procst_child_pids]
    across the released dispatcher, in the sense of [Checks.Examples]'s
    header, under its first reason.  The table side is
    [Checks.ProcsChildPids].

    - [syscall_spec_child_pids]: every [Ok] answer of the released spec
      keeps the list, except a clone's, which leaves the model alone with
      an errno or is [State.with_child] of the pid it returns.  A [Forall]
      over [checked_table], one checker lemma per arm, so a new arm that
      writes the list fails the build by name.
    - [sstep_child_pids_kept], [sstep_child_pids_clone]: so a released step
      that is not a successful clone keeps the list, and a successful clone
      ([Procs.clone_success_b]) appends the pid it returned. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs Vdso.
From LinuxProcessSemantics.Riscv Require Import Sem.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Signal Fork.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs VmMapsDisjoint ProcsWellFormed ProcsPrivateFrame ProcsSyncOnce
  ProcsPeerGates ProcsWait4Gate.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel Require Import Signal Fork.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

Definition cp_of (m : Model) : list word := m_child_pids m.

Ltac cp_frame H := repeat vm_step H; reflexivity.

Lemma check_efault_or_cp : forall fb eff m m' evs,
  check_efault_or fb eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof. intros fb eff m m' evs H. unfold check_efault_or in H. cp_frame H. Qed.

Lemma check_sigpipe_write_cp : forall eff m m' evs,
  check_sigpipe_write eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros eff m m' evs H. unfold check_sigpipe_write in H.
  destruct (sigpipe_declines m); cbv iota in H; [discriminate H|].
  apply check_ret_only_model in H; subst.
  unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); reflexivity.
Qed.

Lemma check_sigpipe_writev_cp : forall reads eff m m' evs,
  check_sigpipe_writev reads eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros reads eff m m' evs H. unfold check_sigpipe_writev in H.
  destruct (sigpipe_declines m); cbv iota in H; [discriminate H|].
  apply check_ret_only_copyins_model in H; subst.
  unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); reflexivity.
Qed.

Lemma check_readv_gap_cp : forall m' evs,
  check_readv_gap = CheckOk m' evs -> False.
Proof. intros m' evs H. unfold check_readv_gap in H. discriminate. Qed.

Lemma check_open_result_cp : forall eff m mk m' evs,
  (forall fd, cp_of (mk fd) = cp_of m) ->
  check_open_result eff m mk = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros eff m mk m' evs Hmk H.
  unfold check_open_result, check_new_fd_result in H.
  repeat vm_step H; try apply Hmk; reflexivity.
Qed.

Ltac cp_done H :=
  first
  [ apply check_efault_or_cp in H; exact H
  | apply check_sigpipe_write_cp in H; exact H
  | apply check_sigpipe_writev_cp in H; exact H
  | elim (check_readv_gap_cp _ _ H)
  | (eapply check_open_result_cp in H; [exact H | intros; reflexivity]) ].

Ltac cp_frame2 H :=
  repeat (vm_step H || cp_done H); try reflexivity.

Lemma check_read_cp : forall i fd buf count eff m m' evs,
  check_read i fd buf count eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_read, check_read_file_data, check_read_urandom, check_socket_pending_error,
    check_access_ok_zero in H.
  cbv zeta in H.
  repeat (vm_step H || cp_done H || (apply check_read_opaque_keeps in H; destruct H as [-> ->])); try reflexivity.
Qed.

Lemma check_write_cp : forall i fd buf count eff m m' evs,
  check_write i fd buf count eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_write, check_write_fault_extend, check_access_ok_zero in H.
  repeat (vm_step H || cp_done H || (apply check_write_opaque_keeps in H; destruct H as [-> ->])); try reflexivity.
Qed.

Lemma check_pread64_cp : forall i fd buf count pos eff m m' evs,
  check_pread64 i fd buf count pos eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pread64, check_read_urandom in H. cbv zeta in H. cp_frame2 H.
Qed.

Lemma check_pwrite64_cp : forall i fd buf count pos eff m m' evs,
  check_pwrite64 i fd buf count pos eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pwrite64, check_write_fault_extend in H. cp_frame2 H.
Qed.

(** OPENAT, ONE SUB-CHECKER AT A TIME.  Unfolding the whole of
    [check_openat] at once multiplies every guard of every arm into
    one case split; each lemma below unfolds one level and closes
    the calls below it by their lemmas. *)
Lemma openat_read_cp : forall p eff m m' evs,
  Open.check_openat_read p eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_read in H. cbv zeta in H.
  repeat (vm_step H || cp_done H); try reflexivity.
Qed.

Lemma openat_create_cp : forall p eff m m' evs,
  Open.check_openat_create p eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_create, check_create_wronly in H. cbv zeta in H.
  repeat (vm_step H || cp_done H); try reflexivity.
Qed.

Lemma openat_append_cp : forall excl p eff m m' evs,
  Open.check_openat_append excl p eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros excl p eff m m' evs H.
  unfold Open.check_openat_append, check_open_append in H. cbv zeta in H.
  repeat (vm_step H || cp_done H); try reflexivity.
Qed.

Lemma openat_rdwr_cp : forall creat trunc p eff m m' evs,
  Open.check_openat_rdwr creat trunc p eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros creat trunc p eff m m' evs H.
  unfold Open.check_openat_rdwr, check_open_rdwr in H. cbv zeta in H.
  repeat (vm_step H || cp_done H); try reflexivity.
Qed.

Lemma openat_rdwr_excl_cp : forall p eff m m' evs,
  Open.check_openat_rdwr_excl p eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_rdwr_excl, check_open_rdwr in H. cbv zeta in H.
  repeat (vm_step H || cp_done H); try reflexivity.
Qed.

Lemma openat_excl_cp : forall p eff m m' evs,
  Open.check_openat_excl p eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_excl, check_create_wronly in H. cbv zeta in H.
  repeat (vm_step H || cp_done H); try reflexivity.
Qed.

Lemma openat_dir_cp : forall p eff m m' evs,
  Open.check_openat_dir p eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_dir in H. cbv zeta in H.
  repeat (vm_step H || cp_done H); try reflexivity.
Qed.

Lemma openat_localtime_cp : forall flags eff m m' evs,
  Open.check_openat_localtime flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros flags eff m m' evs H.
  unfold Open.check_openat_localtime in H. cbv zeta in H.
  repeat (vm_step H || cp_done H); try reflexivity.
Qed.

Lemma openat_devnull_cp : forall flags eff m m' evs,
  Open.check_openat_devnull flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros flags eff m m' evs H.
  unfold Open.check_openat_devnull, Open.check_open_devnull in H. cbv zeta in H.
  repeat (vm_step H || cp_done H); try reflexivity.
Qed.

Lemma openat_urandom_cp : forall flags eff m m' evs,
  Open.check_openat_urandom flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros flags eff m m' evs H.
  unfold Open.check_openat_urandom, Open.check_open_urandom in H. cbv zeta in H.
  repeat (vm_step H || cp_done H); try reflexivity.
Qed.

Lemma openat_proc_result_cp : forall o eff m m' evs,
  Open.check_proc_open_result o eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros o eff m m' evs H.
  unfold Open.check_proc_open_result in H. cbv zeta in H.
  repeat (vm_step H || cp_done H); try reflexivity.
Qed.

Local Ltac openat_sub_cp_tmp H :=
  lazymatch type of H with
  | Open.check_openat_read _ _ _ = CheckOk _ _ => apply openat_read_cp in H; exact H
  | Open.check_openat_create _ _ _ = CheckOk _ _ => apply openat_create_cp in H; exact H
  end.

Lemma openat_tmp_cp : forall n p flags eff m m' evs,
  Open.check_openat_tmp n p flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros n p flags eff m m' evs H.
  unfold Open.check_openat_tmp in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_cp_tmp H || cp_done H); try reflexivity.
Qed.

Local Ltac openat_sub_cp_sep H :=
  lazymatch type of H with
  | Open.check_openat_localtime _ _ _ = CheckOk _ _ => apply openat_localtime_cp in H; exact H
  | Open.check_openat_devnull _ _ _ = CheckOk _ _ => apply openat_devnull_cp in H; exact H
  | Open.check_openat_urandom _ _ _ = CheckOk _ _ => apply openat_urandom_cp in H; exact H
  | Open.check_openat_tmp _ _ _ _ _ = CheckOk _ _ => apply openat_tmp_cp in H; exact H
  end.

Lemma openat_sep_cp : forall p flags eff m m' evs,
  Open.check_openat_sep p flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros p flags eff m m' evs H.
  unfold Open.check_openat_sep in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_cp_sep H || cp_done H); try reflexivity.
Qed.

Local Ltac openat_sub_cp_resolved H :=
  lazymatch type of H with
  | Open.check_openat_read _ _ _ = CheckOk _ _ => apply openat_read_cp in H; exact H
  | Open.check_openat_create _ _ _ = CheckOk _ _ => apply openat_create_cp in H; exact H
  | Open.check_openat_excl _ _ _ = CheckOk _ _ => apply openat_excl_cp in H; exact H
  | Open.check_openat_dir _ _ _ = CheckOk _ _ => apply openat_dir_cp in H; exact H
  | Open.check_openat_append _ _ _ _ = CheckOk _ _ => apply openat_append_cp in H; exact H
  | Open.check_openat_rdwr _ _ _ _ _ = CheckOk _ _ => apply openat_rdwr_cp in H; exact H
  | Open.check_openat_rdwr_excl _ _ _ = CheckOk _ _ => apply openat_rdwr_excl_cp in H; exact H
  | Open.check_openat_sep _ _ _ _ = CheckOk _ _ => apply openat_sep_cp in H; exact H
  end.

Lemma openat_resolved_cp : forall p flags eff m m' evs,
  Open.check_openat_resolved p flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros p flags eff m m' evs H.
  unfold Open.check_openat_resolved in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_cp_resolved H || cp_done H); try reflexivity.
Qed.

Local Ltac openat_sub_cp_proc H :=
  lazymatch type of H with
  | Open.check_proc_open_result _ _ _ = CheckOk _ _ => apply openat_proc_result_cp in H; exact H
  end.

Lemma openat_proc_cp : forall c flags eff m m' evs,
  Open.check_openat_proc c flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros c flags eff m m' evs H.
  unfold Open.check_openat_proc in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_cp_proc H || cp_done H); try reflexivity.
Qed.

Local Ltac openat_sub_cp_body H :=
  lazymatch type of H with
  | Open.check_openat_proc _ _ _ _ = CheckOk _ _ => apply openat_proc_cp in H; exact H
  | Open.check_openat_resolved _ _ _ _ = CheckOk _ _ => apply openat_resolved_cp in H; exact H
  end.

Lemma openat_body_cp : forall i dirfd pathp flags eff m m' evs,
  Open.check_openat_body i dirfd pathp flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold Open.check_openat_body in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_cp_body H || cp_done H); try reflexivity.
Qed.

Local Ltac openat_sub_cp_top H :=
  lazymatch type of H with
  | Open.check_openat_body _ _ _ _ _ _ = CheckOk _ _ => apply openat_body_cp in H; exact H
  end.

Lemma check_openat_cp : forall i dirfd pathp flags eff m m' evs,
  check_openat i dirfd pathp flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_openat in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_cp_top H || cp_done H); try reflexivity.
Qed.

Lemma check_close_cp : forall fd eff m m' evs,
  check_close fd eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof. intros fd eff m m' evs H. unfold check_close in H. cp_frame2 H. Qed.

Lemma check_close_range_cp : forall fd max_fd flags eff m m' evs,
  check_close_range fd max_fd flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros fd max_fd flags eff m m' evs H. unfold check_close_range in H.
  cp_frame2 H.
Qed.

Lemma check_lseek_cp : forall fd off whence eff m m' evs,
  check_lseek fd off whence eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros fd off whence eff m m' evs H. unfold check_lseek in H. cp_frame2 H.
Qed.

Lemma check_getcwd_cp : forall size eff m m' evs,
  check_getcwd size eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros size eff m m' evs H. unfold check_getcwd in H. cp_frame2 H.
Qed.

Lemma check_getrandom_cp : forall i buf cap flags eff m m' evs,
  check_getrandom i buf cap flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i buf cap flags eff m m' evs H.
  unfold check_getrandom, check_getrandom_zero in H. cp_frame2 H.
Qed.

Lemma check_readlinkat_cp : forall i dirfd eff m m' evs,
  check_readlinkat i dirfd eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros i dirfd eff m m' evs H. unfold check_readlinkat in H. cbv zeta in H.
  cp_frame2 H.
Qed.

Lemma check_exit_cp : forall code eff m m' evs,
  check_exit code eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof. intros code eff m m' evs H. unfold check_exit in H. cp_frame2 H. Qed.

Lemma check_set_tid_address_cp : forall eff m m' evs,
  check_set_tid_address eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros eff m m' evs H. unfold check_set_tid_address in H. cp_frame2 H.
Qed.

Lemma check_ioctl_cp : forall fd req eff m m' evs,
  check_ioctl fd req eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof. intros fd req eff m m' evs H. unfold check_ioctl in H. cp_frame2 H. Qed.

Lemma check_writev_cp : forall i fd iov iovcnt eff m m' evs,
  check_writev i fd iov iovcnt eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_writev, check_write_fault_extend in H. cp_frame2 H.
Qed.

Lemma check_readv_imported_cp : forall i fd r iovs0 eff m m' evs,
  check_readv_imported i fd r iovs0 eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i fd r iovs0 eff m m' evs H.
  unfold check_readv_imported in H.
  cp_frame2 H.
Qed.

Lemma check_readv_cp : forall i fd iov iovcnt eff m m' evs,
  check_readv i fd iov iovcnt eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_readv in H.
  repeat (vm_step H || cp_done H
          || (apply check_readv_imported_cp in H; exact H));
  try reflexivity.
Qed.

Lemma check_wait4_cp : forall i upid stat_addr options rusage eff m m' evs,
  check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i upid stat_addr options rusage eff m m' evs H.
  unfold check_wait4 in H. cp_frame2 H.
Qed.

Lemma check_epoll_create1_cp : forall flags32 eff m m' evs,
  check_epoll_create1 flags32 eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros flags32 eff m m' evs H. unfold check_epoll_create1 in H. cp_frame2 H.
Qed.

Lemma check_epoll_ctl_cp : forall i epfd op32 tfd event eff m m' evs,
  check_epoll_ctl i epfd op32 tfd event eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i epfd op32 tfd event eff m m' evs H.
  unfold check_epoll_ctl in H. cp_frame2 H.
Qed.

Lemma check_epoll_pwait_cp :
  forall i epfd events maxevents32 sigmask sigsetsize eff m m' evs,
  check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m
    = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i epfd events maxevents32 sigmask sigsetsize eff m m' evs H.
  unfold check_epoll_pwait in H. cp_frame2 H.
Qed.

Lemma check_fsync_cp : forall fd eff m m' evs,
  check_fsync fd eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof. intros fd eff m m' evs H. unfold check_fsync in H. cp_frame2 H. Qed.

Lemma check_getdents64_cp : forall i fd dirent count eff m m' evs,
  check_getdents64 i fd dirent count eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros i fd dirent count eff m m' evs H.
  unfold check_getdents64 in H.
  repeat (vm_step H || cp_done H || (apply check_getdents64_opaque_fds in H; destruct H as ((fds & ->) & ->))); try reflexivity.
Qed.

Lemma check_flock_cp : forall fd cmd eff m m' evs,
  check_flock fd cmd eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros fd cmd eff m m' evs H. unfold check_flock in H. cp_frame2 H.
Qed.

Lemma check_timerfd_create_cp : forall clkid flags eff m m' evs,
  check_timerfd_create clkid flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros clkid flags eff m m' evs H.
  unfold check_timerfd_create in H. cp_frame2 H.
Qed.

Lemma check_eventfd2_cp : forall flags eff m m' evs,
  check_eventfd2 flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros flags eff m m' evs H.
  unfold check_eventfd2, check_new_fd_result in H. cp_frame2 H.
Qed.

Lemma check_signalfd4_cp : forall i ufd mask sizemask flags eff m m' evs,
  check_signalfd4 i ufd mask sizemask flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i ufd mask sizemask flags eff m m' evs H.
  unfold check_signalfd4, check_new_fd_result in H. cp_frame2 H.
Qed.

Lemma check_uname_cp : forall i name eff m m' evs,
  check_uname i name eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i name eff m m' evs H.
  unfold check_uname, check_uname_copy in H. cp_frame2 H.
Qed.

Lemma check_prlimit64_cp :
  forall i pid resource new_rlim old_rlim eff m m' evs,
  check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i pid resource new_rlim old_rlim eff m m' evs H.
  unfold check_prlimit64, check_rlim64_read in H. cp_frame2 H.
Qed.

Lemma check_capget_cp : forall i header dataptr eff m m' evs,
  check_capget i header dataptr eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i header dataptr eff m m' evs H.
  unfold check_capget, check_capget_copy in H. cp_frame2 H.
Qed.

Lemma check_capset_cp : forall i header data eff m m' evs,
  check_capset i header data eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i header data eff m m' evs H.
  unfold check_capset in H. cp_frame2 H.
Qed.

Lemma check_ftruncate_cp : forall fd len eff m m' evs,
  check_ftruncate fd len eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros fd len eff m m' evs H. unfold check_ftruncate in H. cp_frame2 H.
Qed.

Lemma check_getpid_cp : forall eff m m' evs,
  check_getpid eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof. exact check_set_tid_address_cp. Qed.

Lemma check_gettid_cp : forall eff m m' evs,
  check_gettid eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof. exact check_set_tid_address_cp. Qed.

Lemma check_getppid_cp : forall eff m m' evs,
  check_getppid eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof. intros eff m m' evs H. unfold check_getppid in H. cp_frame2 H. Qed.

Lemma check_setsid_cp : forall eff m m' evs,
  check_setsid eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof. intros eff m m' evs H. unfold check_setsid in H. cp_frame2 H. Qed.

Lemma check_getsid_cp : forall pid eff m m' evs,
  check_getsid pid eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros pid eff m m' evs H. unfold check_getsid, check_getppid in H.
  cp_frame2 H.
Qed.

Lemma check_prctl_cp : forall i option_ arg2 eff m m' evs,
  check_prctl i option_ arg2 eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros i option_ arg2 eff m m' evs H.
  unfold check_prctl, check_ret_writes in H. cp_frame2 H.
Qed.

Lemma check_gettimeofday_cp : forall i tv tz eff m m' evs,
  check_gettimeofday i tv tz eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i tv tz eff m m' evs H.
  unfold check_gettimeofday in H. cp_frame2 H.
Qed.

Lemma check_clock_gettime_cp : forall i clkid tp eff m m' evs,
  check_clock_gettime i clkid tp eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i clkid tp eff m m' evs H.
  unfold check_clock_gettime in H. cp_frame2 H.
Qed.

Lemma check_clock_getres_cp : forall i clkid tp eff m m' evs,
  check_clock_getres i clkid tp eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i clkid tp eff m m' evs H.
  unfold check_clock_getres, check_clock_getres_result in H. cp_frame2 H.
Qed.

Lemma check_nanosleep_cp : forall i rqtp rmtp eff m m' evs,
  check_nanosleep i rqtp rmtp eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i rqtp rmtp eff m m' evs H.
  unfold check_nanosleep in H. cp_frame2 H.
Qed.

Lemma check_dup_cp : forall oldfd eff m m' evs,
  check_dup oldfd eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros oldfd eff m m' evs H.
  unfold check_dup, check_dup_result in H. cp_frame2 H.
Qed.

Lemma check_dup3_cp : forall oldfd newfd flags eff m m' evs,
  check_dup3 oldfd newfd flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros oldfd newfd flags eff m m' evs H. unfold check_dup3 in H. cp_frame2 H.
Qed.

Lemma check_unlinkat_cp : forall i dirfd pathp flags eff m m' evs,
  check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_unlinkat, Namei.check_unlinkat_body, Namei.check_unlinkat_tmp,
    Namei.check_unlink_found, check_unlink_result in H.
  cp_frame2 H.
Qed.

Lemma check_faccessat_cp : forall i dirfd pathp mode eff m m' evs,
  check_faccessat i dirfd pathp mode eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i dirfd pathp mode eff m m' evs H.
  unfold check_faccessat, Open.check_faccessat_body, check_access_exists in H.
  cp_frame2 H.
Qed.

Lemma check_faccessat2_cp : forall i dirfd pathp mode flags eff m m' evs,
  check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i dirfd pathp mode flags eff m m' evs H.
  unfold check_faccessat2, Open.check_faccessat_body, check_access_exists in H.
  cp_frame2 H.
Qed.

Lemma check_pselect6_cp : forall i n32 inp outp exp tsp sig eff m m' evs,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H.
  unfold check_pselect6 in H. cp_frame2 H.
Qed.

Lemma check_ppoll_cp : forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold check_ppoll in H. cp_frame2 H.
Qed.

Lemma check_newfstatat_cp : forall i dirfd pathp flag eff m m' evs,
  check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i dirfd pathp flag eff m m' evs H.
  unfold check_newfstatat, check_newfstatat_proc, check_newfstatat_proc_errno in H.
  cp_frame2 H.
Qed.

Lemma check_fstat_file_cp : forall i p statbuf eff m m' evs,
  check_fstat_file i p statbuf eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i p statbuf eff m m' evs H.
  unfold check_fstat_file in H.
  destruct (fs_lookup (m_fs m) p) as [data|]; [|discriminate].
  destruct (negb (access_okb statbuf STAT_SIZE)); [cp_frame2 H|].
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE)) as [w|];
    [|discriminate].
  assert (Hdel : exists pin,
             check_fstat_deliver statbuf (length data) p pin eff m
             = CheckOk m' evs).
  { destruct (statpin_lookup (m_statpins m) p) as [b0|]; [|eauto].
    destruct (negb (stat_buf_wf b0)); [discriminate|eauto]. }
  destruct Hdel as (pin & Hd).
  apply check_fstat_deliver_ok in Hd
    as (bs & _ & _ & _ & _ & [(b1 & _ & _ & ->)|(_ & ->)]);
    [reflexivity|autorewrite with model; reflexivity].
Qed.

Lemma check_fstat_chrdev_cp : forall ok p i statbuf eff m m' evs,
  check_fstat_chrdev ok p i statbuf eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros ok p i statbuf eff m m' evs H.
  unfold check_fstat_chrdev in H.
  destruct (negb (access_okb statbuf STAT_SIZE)); [cp_frame2 H|].
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE)) as [w|];
    [|discriminate].
  assert (Hdel : exists pin,
             check_fstat_deliver_by ok statbuf p pin eff m
             = CheckOk m' evs).
  { destruct (statpin_lookup (m_statpins m) p) as [b0|]; [|eauto].
    destruct (negb (stat_buf_wf b0 && ok b0)%bool); [discriminate|eauto]. }
  destruct Hdel as (pin & Hd).
  apply check_fstat_deliver_by_ok in Hd
    as (bs & _ & _ & _ & _ & [(b1 & _ & _ & ->)|(_ & ->)]);
    [reflexivity|autorewrite with model; reflexivity].
Qed.

Lemma check_fstat_devnull_cp : forall i statbuf eff m m' evs,
  check_fstat_devnull i statbuf eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof. intros. eapply check_fstat_chrdev_cp. exact H. Qed.

Lemma check_fstat_urandom_cp : forall i statbuf eff m m' evs,
  check_fstat_urandom i statbuf eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof. intros. eapply check_fstat_chrdev_cp. exact H. Qed.

(** The /proc/self/fd directory's [fstat] hands back the model it was
    given; the other opaque objects decline. *)
Lemma check_fstat_opaque_cp : forall i o statbuf eff m m' evs,
  check_fstat_opaque i o statbuf eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros i o statbuf eff m m' evs H.
  apply check_fstat_opaque_keeps in H as (-> & _). reflexivity.
Qed.

Lemma check_fstat_cp : forall i fd statbuf eff m m' evs,
  check_fstat i fd statbuf eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros i fd statbuf eff m m' evs H. unfold check_fstat in H.
  destruct (fd_lookup (m_fds m) fd) as [e|]; [|cp_frame2 H].
  destruct e; try discriminate;
    first [eapply check_fstat_file_cp; exact H
          |eapply check_fstat_devnull_cp; exact H
          |eapply check_fstat_urandom_cp; exact H
          |eapply check_fstat_opaque_cp; exact H].
Qed.

Lemma check_getid_cp : forall sel eff m m' evs,
  check_getid sel eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof. intros sel eff m m' evs H. unfold check_getid in H. cp_frame2 H. Qed.

Lemma check_getresid_cp : forall i get rp ep sp eff m m' evs,
  check_getresid i get rp ep sp eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i get rp ep sp eff m m' evs H.
  unfold check_getresid, check_ret_writes in H. cp_frame2 H.
Qed.

Lemma check_setid_cp : forall get put user v eff m m' evs,
  check_setid get put user v eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros get put user v eff m m' evs H.
  unfold check_setid, check_setid_result in H. cp_frame2 H.
Qed.

Lemma check_setresid_cp : forall get put user r e sv eff m m' evs,
  check_setresid get put user r e sv eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros get put user r e sv eff m m' evs H.
  unfold check_setresid, check_setid_result in H. cp_frame2 H.
Qed.

Lemma check_getgroups_cp : forall gidsetsize eff m m' evs,
  check_getgroups gidsetsize eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros gidsetsize eff m m' evs H. unfold check_getgroups in H. cp_frame2 H.
Qed.

Lemma check_setgroups_cp : forall i eff m m' evs,
  check_setgroups i eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros i eff m m' evs H. unfold check_setgroups in H. cp_frame2 H.
Qed.

Lemma check_socket_cp : forall domain type protocol eff m m' evs,
  check_socket domain type protocol eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros domain type protocol eff m m' evs H.
  unfold check_socket, check_new_fd_result, check_errno_or_list in H. cp_frame2 H.
Qed.

Lemma check_bind_cp : forall i fd addrp addrlen eff m m' evs,
  check_bind i fd addrp addrlen eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold check_bind, check_errno_or_success in H. cp_frame2 H.
Qed.

Lemma check_listen_cp : forall fd backlog eff m m' evs,
  check_listen fd backlog eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros fd backlog eff m m' evs H.
  unfold check_listen, check_errno_or_success, check_errno_only in H.
  cp_frame2 H.
Qed.

Lemma check_connect_cp : forall i fd addrp addrlen eff m m' evs,
  check_connect i fd addrp addrlen eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold check_connect in H. cp_frame2 H.
Qed.

Lemma check_accept4_cp : forall fd addrp addrlenp flags eff m m' evs,
  check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros fd addrp addrlenp flags eff m m' evs H.
  (* [check_errno_only] is unfolded alongside, the way
     [check_read_cp] unfolds [check_access_ok_zero]: it is the arm
     [check_accept4] takes once [Net.Socket.conn_ix_exhausted] holds, and
     [vm_step] sees no [if] or [match] through a folded definition, so
     without the unfold that branch leaves an open goal. *)
  unfold check_accept4, check_new_fd_result, check_errno_or_success,
    check_errno_only, check_errno_or_list in H. cp_frame2 H.
Qed.

Lemma check_fcntl_cp : forall fd cmd arg eff m m' evs,
  check_fcntl fd cmd arg eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros fd cmd arg eff m m' evs H. unfold check_fcntl in H. cp_frame2 H.
Qed.

Lemma check_sched_setscheduler_cp : forall i pid policy param eff m m' evs,
  check_sched_setscheduler i pid policy param eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i pid policy param eff m m' evs H.
  unfold check_sched_setscheduler in H. cp_frame2 H.
Qed.

Lemma check_sched_getaffinity_cp : forall len eff m m' evs,
  check_sched_getaffinity len eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros len eff m m' evs H. unfold check_sched_getaffinity in H. cp_frame2 H.
Qed.

Lemma check_sched_yield_cp : forall eff m m' evs,
  check_sched_yield eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros eff m m' evs H. unfold check_sched_yield in H. cp_frame2 H.
Qed.

Lemma check_sigaltstack_cp : forall i uss uoss eff m m' evs,
  check_sigaltstack i uss uoss eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i uss uoss eff m m' evs H.
  unfold check_sigaltstack in H. cp_frame2 H.
Qed.

Lemma check_rt_sigaction_cp : forall i sig act oact ss eff m m' evs,
  check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i sig act oact ss eff m m' evs H.
  unfold check_rt_sigaction in H. cp_frame2 H.
Qed.

Lemma check_getsockname_cp : forall fd eff m m' evs,
  check_getsockname fd eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros fd eff m m' evs H.
  unfold check_getsockname, check_getsockname_core in H. cp_frame2 H.
Qed.

Lemma check_getpeername_cp : forall fd eff m m' evs,
  check_getpeername fd eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros fd eff m m' evs H.
  unfold check_getpeername, check_getpeername_core in H. cp_frame2 H.
Qed.

Lemma check_setsockopt_cp : forall fd level optlen eff m m' evs,
  check_setsockopt fd level optlen eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros fd level optlen eff m m' evs H.
  unfold check_setsockopt, check_setsockopt_core in H. cp_frame2 H.
Qed.

Lemma check_getsockopt_cp : forall i fd level optlenp eff m m' evs,
  check_getsockopt i fd level optlenp eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i fd level optlenp eff m m' evs H.
  unfold check_getsockopt, check_getsockopt_core in H. cp_frame2 H.
Qed.

Lemma check_shutdown_cp : forall fd how eff m m' evs,
  check_shutdown fd how eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros fd how eff m m' evs H.
  unfold check_shutdown, check_shutdown_core in H. cp_frame2 H.
Qed.

Lemma check_send_on_socket_cp :
  forall pre acc fd sk total bs eff m m' evs,
  check_send_on_socket pre acc fd sk total bs eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros pre acc fd sk total bs eff m m' evs H.
  unfold check_send_on_socket in H. cp_frame2 H.
Qed.

Lemma check_recv_fd_answer_cp : forall fds fd eff m m' evs,
  check_recv_fd_answer fds fd eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros fds fd eff m m' evs H.
  unfold check_recv_fd_answer in H. cp_frame2 H.
Qed.

Lemma check_socketpair_cp : forall i family type protocol sv eff m m' evs,
  check_socketpair i family type protocol sv eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i family type protocol sv eff m m' evs H.
  unfold check_socketpair, check_socketpair_written, check_socketpair_faulted
    in H. cp_frame2 H.
Qed.

Lemma check_recvfrom_cp : forall i fd buf size eff m m' evs,
  check_recvfrom i fd buf size eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i fd buf size eff m m' evs H.
  unfold check_recvfrom, check_access_ok_zero, check_recv_fd_answer in H.
  cp_frame2 H.
Qed.

Lemma check_recvmsg_cp : forall fd flags eff m m' evs,
  check_recvmsg fd flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros fd flags eff m m' evs H.
  unfold check_recvmsg, check_recv_fd_answer in H. cp_frame2 H.
Qed.

Lemma check_sendto_cp : forall i fd buf count flags addrp eff m m' evs,
  check_sendto i fd buf count flags addrp eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i fd buf count flags addrp eff m m' evs H.
  unfold check_sendto, check_access_ok_zero, check_send_on_socket in H.
  cp_frame2 H.
Qed.

Lemma check_sendmsg_cp : forall i fd msgp flags eff m m' evs,
  check_sendmsg i fd msgp flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i fd msgp flags eff m m' evs H.
  unfold check_sendmsg, check_send_on_socket in H. cp_frame2 H.
Qed.

Lemma check_pipe2_cp : forall i fildes flags eff m m' evs,
  check_pipe2 i fildes flags eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i fildes flags eff m m' evs H.
  unfold check_pipe2, pipe2_model in H. cp_frame2 H.
Qed.

Lemma check_futex_cp : forall i uaddr op val utime eff m m' evs,
  check_futex i uaddr op val utime eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i uaddr op val utime eff m m' evs H.
  unfold check_futex, check_futex_wake_private, check_futex_wait_private in H.
  cp_frame2 H.
Qed.

Lemma check_set_robust_list_cp : forall len eff m m' evs,
  check_set_robust_list len eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros len eff m m' evs H.
  unfold check_set_robust_list in H. cp_frame2 H.
Qed.

(** The memory-management arms build their post-models through the
    wrappers of [Sys.Mm]; two of them branch or recurse, so they get a
    lemma, and every other wrapper keeps [cp_of] by conversion. *)
Lemma cp_of_forget_vm_ranges : forall rs m, cp_of (forget_vm_ranges rs m) = cp_of m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma cp_of_with_brk_next : forall m req r, cp_of (with_brk_next m req r) = cp_of m.
Proof.
  intros m req r. unfold with_brk_next. cbv zeta.
  rewrite cp_of_forget_vm_ranges. reflexivity.
Qed.

Lemma cp_of_with_mmap_backing : forall flags a n m,
  cp_of (with_mmap_backing flags a n m) = cp_of m.
Proof.
  intros flags a n m. unfold with_mmap_backing.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.

Lemma cp_of_with_mmap_replacement : forall flags a n m,
  cp_of (with_mmap_replacement flags a n m) = cp_of m.
Proof.
  intros flags a n m. unfold with_mmap_replacement.
  rewrite cp_of_with_mmap_backing. reflexivity.
Qed.

(** Split [H] on every [if] and [match] to a leaf, as [MmStepFrame] does. *)
Local Ltac mm_walk H :=
  repeat (cbv beta iota zeta in H;
          lazymatch type of H with
          | CheckOk _ _ = CheckOk _ _ => fail
          | _ => match type of H with
                 | context [match ?x with _ => _ end] => destruct x
                 end
          end);
  try discriminate H.

Local Ltac mm_leaf H :=
  injection H as <- <-;
  rewrite ?cp_of_with_mmap_backing, ?cp_of_with_mmap_replacement, ?cp_of_with_brk_next;
  reflexivity.

Lemma check_brk_cp : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros req [ret ws zs us cs ci] m m' evs H.
  unfold check_brk in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_mmap_cp : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H.
  unfold check_mmap, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_mremap_cp : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H.
  unfold check_mremap, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_munmap_cp : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H.
  unfold check_munmap, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_mprotect_cp : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H.
  unfold check_mprotect, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_madvise_cp : forall addr len advice eff m m' evs,
  check_madvise addr len advice eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros addr len advice [ret ws zs us cs ci] m m' evs H.
  unfold check_madvise in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
  dif H; [discriminate|].
  dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
  dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
  dif H; [|discriminate].
  destruct ws, us, cs, ci; try discriminate.
  dif H; [|discriminate]. injection H as <- <-. reflexivity.
Qed.

Lemma cp_of_sigmask_deliver_model : forall new m,
  cp_of (sigmask_deliver_model new m) = cp_of m.
Proof.
  intros new m. unfold sigmask_deliver_model.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    reflexivity.
Qed.

Lemma check_rt_sigprocmask_cp : forall i how nset oset ss eff m m' evs,
  check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs ->
  cp_of m' = cp_of m.
Proof.
  intros i how nset oset ss eff m m' evs H.
  unfold check_rt_sigprocmask in H.
  destruct (negb (bv_eqb ss (Z_to_bv 64 NSIG_BYTES))) eqn:Hss;
    cbv beta iota zeta in H.
  { apply check_ret_only_ok_iff in H. now destruct H as (_ & -> & _). }
  destruct (w_is0 nset) eqn:Hn; cbv beta iota in H.
  { destruct (w_is0 oset) eqn:Ho; cbv beta iota in H.
    - apply check_ret_only_ok_iff in H. now destruct H as (_ & -> & _).
    - apply check_write_oset_ok_iff in H. now destruct H as (-> & _ & _ & _). }
  destruct (sigset_at (in_mem i) nset) as [raw|] eqn:Hr; cbv beta iota in H.
  2:{ apply check_ret_only_ok_iff in H. now destruct H as (_ & -> & _). }
  destruct (negb (how_valid how)) eqn:Hh; cbv beta iota zeta in H.
  { apply check_ret_only_copyins_ok_iff in H. now destruct H as (_ & -> & _). }
  destruct (w_is0 oset) eqn:Ho; cbv beta iota in H.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (_ & -> & _).
    now rewrite cp_of_sigmask_deliver_model. }
  unfold check_write_oset_copyins in H.
  destruct (check_write_oset i oset (m_sigmask m) (clear_copyins eff)
              (sigmask_deliver_model (sigmask_apply how (m_sigmask m)
                               (sigmask_strip raw)) m))
    as [m2 evs2| |] eqn:Hcw; [|discriminate|discriminate].
  destruct (access_ranges_eqb (eff_copyins eff)
              [(nset, Z.to_nat NSIG_BYTES)]); [|discriminate].
  apply check_write_oset_ok_iff in Hcw. destruct Hcw as (-> & _ & _ & _).
  inversion H; subst. now rewrite cp_of_sigmask_deliver_model.
Qed.

Lemma check_tkill_cp : forall pid sig eff m m' evs,
  check_tkill pid sig eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros pid sig eff m m' evs H.
  unfold check_tkill, check_tkill_self, check_send_sigabrt in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; cbv beta iota in H
         | match ?x with _ => _ end = _ => destruct x; cbv beta iota in H
         end;
    try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (_ & -> & _);
         reflexivity);
    inversion H; subst; autorewrite with model; reflexivity.
Qed.

Lemma check_tgkill_cp : forall tgid pid sig eff m m' evs,
  check_tgkill tgid pid sig eff m = CheckOk m' evs -> cp_of m' = cp_of m.
Proof.
  intros tgid pid sig eff m m' evs H.
  unfold check_tgkill, check_tkill_self, check_send_sigabrt in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; cbv beta iota in H
         | match ?x with _ => _ end = _ => destruct x; cbv beta iota in H
         end;
    try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (_ & -> & _);
         reflexivity);
    inversion H; subst; autorewrite with model; reflexivity.
Qed.

(** The clone arms: the model as it was with an errno, or [with_child] of a
    pid in the envelope, over the model as it was or, for the namespace
    word, over the model the caller keeps ([Kernel.Fork.forfeit_model]). *)
Lemma clone_errno_error : forall r,
  errno_ret_in clone_errnos r = true -> addr_is_error_b r = true.
Proof.
  intros r H. apply errno_ret_in_true in H as (e & Hin & ->).
  destruct (errnos_ok_range clone_errnos e eq_refl Hin) as [H1 H2].
  exact (errno_ret_error_b e H1 H2).
Qed.

Lemma errno_any_error : forall r, errno_any_b r = true -> addr_is_error_b r = true.
Proof. intros r H. unfold errno_any_b in H. apply andb_true_iff in H as [H _]. exact H. Qed.

Local Ltac clone_leaf :=
  first
  [ left; split; [reflexivity | first [ apply clone_errno_error; assumption
                                       | apply errno_any_error; assumption ]]
  | right; split; [first [left; reflexivity | right; reflexivity] | assumption] ].

Lemma check_clone_cp : forall flags eff m m' evs,
  check_clone flags eff m = CheckOk m' evs ->
  (m' = m /\ addr_is_error_b (eff_ret eff) = true)
  \/ ((m' = with_child (eff_ret eff) m \/ m' = with_child (eff_ret eff) (forfeit_model m))
      /\ clone_pid_ok_b m (eff_ret eff) = true).
Proof.
  intros flags [ret ws zs us cs ci] m m' evs H.
  unfold check_clone, check_clone_resolve, check_clone_answer,
    check_clone_ns_resolve, check_clone_ns_answer in H.
  repeat vm_step H.
  all: clone_leaf.
Qed.

Lemma check_clone3_cp : forall i uargs size eff m m' evs,
  check_clone3 i uargs size eff m = CheckOk m' evs ->
  (m' = m /\ addr_is_error_b (eff_ret eff) = true)
  \/ ((m' = with_child (eff_ret eff) m \/ m' = with_child (eff_ret eff) (forfeit_model m))
      /\ clone_pid_ok_b m (eff_ret eff) = true).
Proof.
  intros i uargs size eff m m' evs H.
  unfold check_clone3, check_clone3_resolve, check_clone_answer in H.
  repeat (lazymatch type of H with
          | check_ret_only _ _ _ _ = CheckOk _ _ =>
              apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->)
          | _ => vm_step H
          end).
  all: first
    [ clone_leaf
    | left; split; [reflexivity | vm_compute; reflexivity] ].
Qed.


(* =========================================================================
   Every arm: the list, or a clone's own answer
   ========================================================================= *)

Definition clone_answer (eff : SyscallEffect) (m m' : Model) : Prop :=
  (m' = m /\ addr_is_error_b (eff_ret eff) = true)
  \/ ((m' = with_child (eff_ret eff) m \/ m' = with_child (eff_ret eff) (forfeit_model m))
      /\ clone_pid_ok_b m (eff_ret eff) = true).

Definition arm_cp (c : CheckedArm) : Prop :=
  forall i eff m m' evs, ca_check c i eff m = CheckOk m' evs ->
    (clone_sysno (ca_no c) = false /\ cp_of m' = cp_of m)
    \/ (clone_sysno (ca_no c) = true /\ clone_answer eff m m').

Lemma checked_table_cp : Forall arm_cp checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_cp).
  all: unfold arm_cp; intros i eff m m' evs H; autorewrite with arm_unfold in H.
  all: first
    [ right; split; [vm_compute; reflexivity | exact (check_clone_cp _ _ _ _ _ H)]
    | right; split; [vm_compute; reflexivity | exact (check_clone3_cp _ _ _ _ _ _ _ H)]
    | left; split; [vm_compute; reflexivity|];
      first
      [
          eapply check_read_cp; eassumption
        | eapply check_brk_cp; eassumption
        | eapply check_munmap_cp; eassumption
        | eapply check_mremap_cp; eassumption
        | eapply check_mmap_cp; eassumption
        | eapply check_mprotect_cp; eassumption
        | eapply check_write_cp; eassumption
        | eapply check_pread64_cp; eassumption
        | eapply check_pwrite64_cp; eassumption
        | eapply check_openat_cp; eassumption
        | eapply check_close_cp; eassumption
        | eapply check_close_range_cp; eassumption
        | eapply check_lseek_cp; eassumption
        | eapply check_getcwd_cp; eassumption
        | eapply check_getrandom_cp; eassumption
        | eapply check_readlinkat_cp; eassumption
        | eapply check_exit_cp; eassumption
        | eapply check_set_tid_address_cp; eassumption
        | eapply check_ioctl_cp; eassumption
        | eapply check_writev_cp; eassumption
        | eapply check_readv_imported_cp; eassumption
        | eapply check_readv_cp; eassumption
        | eapply check_wait4_cp; eassumption
        | eapply check_epoll_create1_cp; eassumption
        | eapply check_epoll_ctl_cp; eassumption
        | eapply check_epoll_pwait_cp; eassumption
        | eapply check_fsync_cp; eassumption
        | eapply check_getdents64_cp; eassumption
        | eapply check_flock_cp; eassumption
        | eapply check_timerfd_create_cp; eassumption
        | eapply check_eventfd2_cp; eassumption
        | eapply check_signalfd4_cp; eassumption
        | eapply check_uname_cp; eassumption
        | eapply check_prlimit64_cp; eassumption
        | eapply check_capget_cp; eassumption
        | eapply check_capset_cp; eassumption
        | eapply check_ftruncate_cp; eassumption
        | eapply check_getpid_cp; eassumption
        | eapply check_gettid_cp; eassumption
        | eapply check_getppid_cp; eassumption
        | eapply check_setsid_cp; eassumption
        | eapply check_getsid_cp; eassumption
        | eapply check_prctl_cp; eassumption
        | eapply check_gettimeofday_cp; eassumption
        | eapply check_clock_gettime_cp; eassumption
        | eapply check_clock_getres_cp; eassumption
        | eapply check_nanosleep_cp; eassumption
        | eapply check_dup_cp; eassumption
        | eapply check_dup3_cp; eassumption
        | eapply check_unlinkat_cp; eassumption
        | eapply check_faccessat_cp; eassumption
        | eapply check_faccessat2_cp; eassumption
        | eapply check_pselect6_cp; eassumption
        | eapply check_ppoll_cp; eassumption
        | eapply check_newfstatat_cp; eassumption
        | eapply check_fstat_file_cp; eassumption
        | eapply check_fstat_chrdev_cp; eassumption
        | eapply check_fstat_devnull_cp; eassumption
        | eapply check_fstat_urandom_cp; eassumption
        | eapply check_fstat_cp; eassumption
        | eapply check_getid_cp; eassumption
        | eapply check_getresid_cp; eassumption
        | eapply check_setid_cp; eassumption
        | eapply check_setresid_cp; eassumption
        | eapply check_getgroups_cp; eassumption
        | eapply check_setgroups_cp; eassumption
        | eapply check_socket_cp; eassumption
        | eapply check_bind_cp; eassumption
        | eapply check_listen_cp; eassumption
        | eapply check_connect_cp; eassumption
        | eapply check_accept4_cp; eassumption
        | eapply check_fcntl_cp; eassumption
        | eapply check_sched_setscheduler_cp; eassumption
        | eapply check_sched_getaffinity_cp; eassumption
        | eapply check_sched_yield_cp; eassumption
        | eapply check_sigaltstack_cp; eassumption
        | eapply check_rt_sigaction_cp; eassumption
        | eapply check_getsockname_cp; eassumption
        | eapply check_getpeername_cp; eassumption
        | eapply check_setsockopt_cp; eassumption
        | eapply check_getsockopt_cp; eassumption
        | eapply check_shutdown_cp; eassumption
        | eapply check_send_on_socket_cp; eassumption
        | eapply check_recv_fd_answer_cp; eassumption
        | eapply check_socketpair_cp; eassumption
        | eapply check_recvfrom_cp; eassumption
        | eapply check_recvmsg_cp; eassumption
        | eapply check_sendto_cp; eassumption
        | eapply check_sendmsg_cp; eassumption
        | eapply check_pipe2_cp; eassumption
        | eapply check_futex_cp; eassumption
        | eapply check_set_robust_list_cp; eassumption
        | eapply check_madvise_cp; eassumption
        | eapply check_rt_sigprocmask_cp; eassumption
        | eapply check_tkill_cp; eassumption
        | eapply check_tgkill_cp; eassumption
      ]
    | fail 1 "checked_table_cp has no case for this arm: give its checker a *_cp lemma above" ].
Qed.

(** THE SPEC FACT: every released answer keeps the list, but a clone's,
    which leaves the model alone with an errno or is [with_child] of the
    pid it returns. *)
Theorem syscall_spec_child_pids : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  (clone_sysno (bv_unsigned (in_sysno i)) = false /\ cp_of m' = cp_of m)
  \/ (clone_sysno (bv_unsigned (in_sysno i)) = true /\ clone_answer eff m m').
Proof.
  intros i m eff m' evs H. apply check_syscall_ok_iff in H.
  unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_cp as Hall. rewrite Forall_forall in Hall.
  rewrite <- (lookup_ca_no _ _ _ Elk).
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H).
Qed.

(* =========================================================================
   The released step
   ========================================================================= *)

Lemma cp_bvmap_get_set_same {n A} (k k' : bv n) (x : A) m :
  k = k' -> bvmap_get k' (bvmap_set k x m) = Some x.
Proof. intros ->. apply bvmap_get_set_same. Qed.

Lemma cp_a0_after_effect : forall ms eff,
  ms_gpr (advance_past_svc (apply_effect ms eff)) 0 = eff_ret eff.
Proof.
  intros ms eff. unfold ms_gpr, advance_past_svc, apply_effect, set_reg, reg_get. simpl.
  erewrite cp_bvmap_get_set_same by (apply bv_eq; reflexivity). reflexivity.
Qed.

Lemma clone_pid_not_error : forall m r,
  clone_pid_ok_b m r = true -> addr_is_error_b r = false.
Proof.
  intros m r H. unfold clone_pid_ok_b in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
  apply Z.ltb_lt in H. unfold addr_is_error_b. apply Z.ltb_ge.
  assert (Hb : (PID_MAX_ENVELOPE <= two_pow_64 - 4096)%Z)
    by (apply Z.leb_le; reflexivity).
  lia.
Qed.

Lemma cp_materialize : forall m acc m'',
  materialize_model_accesses m acc = Some m'' -> cp_of m'' = cp_of m.
Proof.
  intros m acc m'' H.
  destruct (materialize_model_accesses_frame _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _).
  unfold cp_of, m_child_pids. rewrite Hp. reflexivity.
Qed.

Lemma halted_with_child : forall r m, m_halted (with_child r m) = m_halted m.
Proof. reflexivity. Qed.

Lemma killed_with_child : forall r m, m_killed (with_child r m) = m_killed m.
Proof. reflexivity. Qed.

Lemma killed_none_of_running : forall m, m_halted m = None -> m_killed m = None.
Proof.
  intros m H. unfold m_killed, m_halted in *. rewrite H.
  destruct (procst_killed (m_proc m)); reflexivity.
Qed.

(** A clone's answer never halts nor kills the caller. *)
Lemma clone_answer_running : forall eff m m',
  clone_answer eff m m' -> m_halted m = None ->
  m_halted m' = None /\ m_killed m' = None.
Proof.
  intros eff m m' [(-> & _) | ([-> | ->] & _)] Hh.
  - split; [exact Hh | exact (killed_none_of_running _ Hh)].
  - rewrite halted_with_child, killed_with_child.
    split; [exact Hh | exact (killed_none_of_running _ Hh)].
  - rewrite halted_with_child, killed_with_child.
    split; [exact Hh | exact (killed_none_of_running m Hh)].
Qed.

(** THE STEP FACTS.  A released step that is not a successful clone keeps
    the list; a successful clone appends the pid it returned. *)
Theorem sstep_child_pids_kept : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  clone_success_b c c' = false ->
  cp_of (cfg_model c') = cp_of (cfg_model c).
Proof.
  intros segs cfg c evs c' H Hcs.
  inversion H; subst; cbn [cfg_ms cfg_model] in Hcs |- *.
  - (* an instruction *)
    match goal with
    | Ha : mi_account_step _ _ _ = MachineOk _ |- _ =>
        destruct (mi_account_step_model_frame _ _ _ _ _ Ha)
          as (_ & _ & _ & _ & _ & Hp & _)
    end.
    unfold cp_of, m_child_pids. rewrite Hp. reflexivity.
  - (* a vDSO call: never a clone *)
    match goal with
    | Hsp : syscall_spec _ _ (Ok _ _ _), Hf : vdso_fn_sysno ?fn = Some _,
      Hm : materialize_model_accesses ?m' _ = Some ?m'' |- _ =>
        destruct (syscall_spec_child_pids _ _ _ _ _ Hsp) as [(_ & E) | (Hc & _)];
        [ transitivity (cp_of m''); [reflexivity|];
          rewrite (cp_materialize _ _ _ Hm); exact E
        | exfalso; cbn [in_sysno sys_input] in Hc;
          destruct fn; cbn [vdso_fn_sysno] in Hf; try discriminate Hf;
          injection Hf as <-; vm_compute in Hc; discriminate Hc ]
    end.
  - (* a system call that returns *)
    match goal with
    | Hsp : syscall_spec (sys_input _ _ ?x8) _ (Ok ?eff _ _),
      Hs : ms_svc_pending _ = Some ?x8,
      Hm : materialize_model_accesses _ _ = Some _ |- _ =>
        rewrite (cp_materialize _ _ _ Hm);
        destruct (syscall_spec_child_pids _ _ _ _ _ Hsp)
          as [(_ & E) | (Hc & [(-> & _) | ([-> | ->] & Hok)])];
        [ exact E | reflexivity | exfalso | exfalso ];
        unfold clone_success_b in Hcs; cbn [cfg_ms] in Hcs; rewrite Hs in Hcs;
        cbn [in_sysno sys_input] in Hc; rewrite Hc, cp_a0_after_effect,
          (clone_pid_not_error _ _ Hok) in Hcs; discriminate Hcs
    end.
  - (* an exit: a clone's answer would not halt *)
    match goal with
    | Hsp : syscall_spec _ ?m (Ok _ ?m' _), Hh : m_halted ?m = None,
      Hx : m_halted ?m' = Some _ |- _ =>
        destruct (syscall_spec_child_pids _ _ _ _ _ Hsp) as [(_ & E) | (_ & Ha)];
        [ exact E
        | exfalso; destruct (clone_answer_running _ _ _ Ha Hh) as (Hh' & _);
          rewrite Hh' in Hx; discriminate Hx ]
    end.
  - (* a kill: likewise *)
    match goal with
    | Hsp : syscall_spec _ ?m (Ok _ ?m' _), Hh : m_halted ?m = None,
      Hk : m_killed ?m' = Some _ |- _ =>
        destruct (syscall_spec_child_pids _ _ _ _ _ Hsp) as [(_ & E) | (_ & Ha)];
        [ exact E
        | exfalso; destruct (clone_answer_running _ _ _ Ha Hh) as (_ & Hk');
          rewrite Hk' in Hk; discriminate Hk ]
    end.
Qed.

Theorem sstep_child_pids_clone : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  clone_success_b c c' = true ->
  cp_of (cfg_model c') = cp_of (cfg_model c) ++ [ms_gpr (cfg_ms c') 0].
Proof.
  intros segs cfg c evs c' H Hcs.
  inversion H; subst; cbn [cfg_ms cfg_model] in Hcs |- *.
  - (* an instruction: no call pending *)
    unfold clone_success_b in Hcs. cbn [cfg_ms] in Hcs.
    match goal with Hs : ms_svc_pending _ = None |- _ => rewrite Hs in Hcs end.
    discriminate Hcs.
  - unfold clone_success_b in Hcs. cbn [cfg_ms] in Hcs.
    match goal with Hs : ms_svc_pending _ = None |- _ => rewrite Hs in Hcs end.
    discriminate Hcs.
  - (* a system call that returns *)
    match goal with
    | Hsp : syscall_spec (sys_input _ _ ?x8) _ (Ok ?eff _ _),
      Hs : ms_svc_pending _ = Some ?x8,
      Hm : materialize_model_accesses _ _ = Some _ |- _ =>
        rewrite (cp_materialize _ _ _ Hm), cp_a0_after_effect;
        unfold clone_success_b in Hcs; cbn [cfg_ms] in Hcs; rewrite Hs in Hcs;
        rewrite cp_a0_after_effect in Hcs;
        apply andb_true_iff in Hcs as [Hc Hne];
        destruct (syscall_spec_child_pids _ _ _ _ _ Hsp)
          as [(Hc' & _) | (_ & [(_ & He) | ([-> | ->] & _)])];
        [ cbn [in_sysno sys_input] in Hc'; rewrite Hc in Hc'; discriminate Hc'
        | rewrite He in Hne; discriminate Hne
        | reflexivity
        | reflexivity ]
    end.
  - (* an exit: a clone's answer would not halt *)
    exfalso.
    match goal with
    | Hsp : syscall_spec _ ?m (Ok _ ?m' _), Hh : m_halted ?m = None,
      Hx : m_halted ?m' = Some _, Hs : ms_svc_pending _ = Some ?x8 |- _ =>
        unfold clone_success_b in Hcs; cbn [cfg_ms] in Hcs; rewrite Hs in Hcs;
        apply andb_true_iff in Hcs as [Hc _];
        destruct (syscall_spec_child_pids _ _ _ _ _ Hsp) as [(Hc' & _) | (_ & Ha)];
        [ cbn [in_sysno sys_input] in Hc'; rewrite Hc in Hc'; discriminate Hc'
        | destruct (clone_answer_running _ _ _ Ha Hh) as (Hh' & _);
          rewrite Hh' in Hx; discriminate Hx ]
    end.
  - (* a kill: likewise *)
    exfalso.
    match goal with
    | Hsp : syscall_spec _ ?m (Ok _ ?m' _), Hh : m_halted ?m = None,
      Hk : m_killed ?m' = Some _, Hs : ms_svc_pending _ = Some ?x8 |- _ =>
        unfold clone_success_b in Hcs; cbn [cfg_ms] in Hcs; rewrite Hs in Hcs;
        apply andb_true_iff in Hcs as [Hc _];
        destruct (syscall_spec_child_pids _ _ _ _ _ Hsp) as [(Hc' & _) | (_ & Ha)];
        [ cbn [in_sysno sys_input] in Hc'; rewrite Hc in Hc'; discriminate Hc'
        | destruct (clone_answer_running _ _ _ Ha Hh) as (_ & Hk');
          rewrite Hk' in Hk; discriminate Hk ]
    end.
Qed.


