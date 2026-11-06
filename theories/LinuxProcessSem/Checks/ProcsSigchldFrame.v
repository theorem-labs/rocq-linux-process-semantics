(** * LinuxProcessSem.Checks.ProcsSigchldFrame — how released answers move the SIGCHLD install bit and [m_has_children]

    Not part of the trusted specification: QA on [State.procst_sigchld_dfl]
    and [State.procst_children] across the released dispatcher, in the
    sense of [Checks.Examples]'s header, under its first reason.  The
    table side is [Checks.ProcsSigchld] and [Checks.ProcsSigchldRule].

    - [syscall_spec_sigchld]: every [Ok] answer of the released spec keeps
      the pair (the bit, [m_has_children]) ([sd_of]), except an
      [rt_sigaction]'s (134), whose SIGCHLD SIG_DFL install
      ([Kernel.Signal.sigchld_dfl_install]) leaves
      [Kernel.Signal.sigchld_install_model] of the model, which sets the
      bit only in a process with no recorded child; and a clone's, which
      keeps the bit and may set [m_has_children].  No admitted answer
      CLEARS either: [Kernel.Signal.rt_sigaction_spec] declines every
      other SIGCHLD install, SIG_IGN, a handler and SA_NOCLDWAIT included.
      A [Forall] over [checked_table], one checker lemma per arm, so a new
      arm that writes either fails the build by name.  The per-arm lemmas
      are [Checks.ProcsChildPidsFrame]'s, read at this pair instead of the
      child list; the clone arms reuse that file's [check_clone_cp] and
      [check_clone3_cp].
    - Its readings: [syscall_spec_sigchld_mono] (the bit is never cleared),
      [syscall_spec_has_children_mono] ([m_has_children] is never
      cleared), [syscall_spec_sigchld_no_set_with_children] (a model with
      [m_has_children] set never gets the bit set), and
      [syscall_spec_hc_ok] (a non-empty list of unreaped children implies
      [m_has_children]).
    - [sstep_sigchld_mono], [sstep_sigchld_no_set_with_children] and
      [sstep_hc_ok]: the same of a released step. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs Vdso.
From LinuxProcessSemantics.Riscv Require Import Sem.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Signal Fork.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs VmMapsDisjoint ProcsWellFormed ProcsPrivateFrame ProcsSyncOnce
  ProcsPeerGates ProcsWait4Gate ProcsChildPidsFrame.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel Require Import Signal Fork.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(** The bit and the persistent "has had a child" flag, as a function of
    the model. *)
Definition sd_of (m : Model) : bool * bool := (m_sigchld_dfl m, m_has_children m).

(** What a released answer at number [n] does to the pair: keeps it; or,
    at [rt_sigaction] (134) only, leaves [sigchld_install_model] of it;
    or, at a clone only, keeps the bit and sets [m_has_children]. *)
Definition sd_kept (n : Z) (m m' : Model) : Prop :=
  sd_of m' = sd_of m
  \/ ((n =? 134)%Z = true /\ sd_of m' = sd_of (sigchld_install_model m))
  \/ (clone_sysno n = true /\ m_sigchld_dfl m' = m_sigchld_dfl m
      /\ m_has_children m' = true).

Ltac sd_frame H := repeat vm_step H; reflexivity.

Lemma check_efault_or_sd : forall fb eff m m' evs,
  check_efault_or fb eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof. intros fb eff m m' evs H. unfold check_efault_or in H. sd_frame H. Qed.

Lemma check_sigpipe_write_sd : forall eff m m' evs,
  check_sigpipe_write eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros eff m m' evs H. unfold check_sigpipe_write in H.
  destruct (sigpipe_declines m); cbv iota in H; [discriminate H|].
  apply check_ret_only_model in H; subst.
  unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); reflexivity.
Qed.

Lemma check_sigpipe_writev_sd : forall reads eff m m' evs,
  check_sigpipe_writev reads eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros reads eff m m' evs H. unfold check_sigpipe_writev in H.
  destruct (sigpipe_declines m); cbv iota in H; [discriminate H|].
  apply check_ret_only_copyins_model in H; subst.
  unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); reflexivity.
Qed.

Lemma check_readv_gap_sd : forall m' evs,
  check_readv_gap = CheckOk m' evs -> False.
Proof. intros m' evs H. unfold check_readv_gap in H. discriminate. Qed.

Lemma check_open_result_sd : forall eff m mk m' evs,
  (forall fd, sd_of (mk fd) = sd_of m) ->
  check_open_result eff m mk = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros eff m mk m' evs Hmk H.
  unfold check_open_result, check_new_fd_result in H.
  repeat vm_step H; try apply Hmk; reflexivity.
Qed.

Ltac sd_done H :=
  first
  [ apply check_efault_or_sd in H; exact H
  | apply check_sigpipe_write_sd in H; exact H
  | apply check_sigpipe_writev_sd in H; exact H
  | elim (check_readv_gap_sd _ _ H)
  | (eapply check_open_result_sd in H; [exact H | intros; reflexivity]) ].

Ltac sd_frame2 H :=
  repeat (vm_step H || sd_done H); try reflexivity.

(** READ'S AND WRITE'S HELPERS, as [Checks.VmMapsDisjoint] proves them
    for the address space, one lemma each: a stream-pair end's read and
    send, the /proc/sys file, the eventfd, the unnamed file and the
    write-fault extension.  Each closes its own step, so the frame lemmas
    of [read], [write], [pread64], [pwrite64], [writev], [pwritev2],
    [sendto] and [recvfrom] close these calls by name. *)
Lemma check_stream_read_empty_sd : forall fd id side st nonblock eff m m' evs,
  check_stream_read_empty fd id side st nonblock eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros fd id side st nonblock eff m m' evs H.
  unfold check_stream_read_empty, check_stream_read_reset in H. sd_frame2 H.
Qed.

Lemma check_stream_read_sd :
  forall fd id side st nonblock buf count i eff m m' evs,
  check_stream_read fd id side st nonblock buf count i eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros fd id side st nonblock buf count i eff m m' evs H.
  unfold check_stream_read, check_stream_read_empty, check_stream_read_reset in H.
  cbv beta zeta in H. sd_frame2 H.
Qed.

Lemma check_stream_send_sd :
  forall id side st nonblock nosignal n src ledger eff m m' evs,
  check_stream_send id side st nonblock nosignal n src ledger eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros id side st nonblock nosignal n src ledger eff m m' evs H.
  unfold check_stream_send in H. cbv beta zeta in H. sd_frame2 H.
Qed.

Lemma check_stream_write_sd :
  forall id side st nonblock nosignal buf count i eff m m' evs,
  check_stream_write id side st nonblock nosignal buf count i eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros id side st nonblock nosignal buf count i eff m m' evs H.
  unfold check_stream_write in H. eapply check_stream_send_sd. exact H.
Qed.

Ltac sd_stream H :=
  first
  [ apply check_stream_read_sd in H; exact H
  | apply check_stream_read_empty_sd in H; exact H
  | apply check_stream_write_sd in H; exact H
  | apply check_stream_send_sd in H; exact H ].

Ltac sd_frame3 H :=
  repeat (vm_step H || sd_done H || sd_stream H); try reflexivity.

Lemma sd_read_urandom : forall i buf count eff m m' evs,
  check_read_urandom i buf count eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros i buf count eff m m' evs H. unfold check_read_urandom, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H);
  try reflexivity.
Qed.

Lemma sd_socket_pending_error : forall e fd peer ch buf count i eff m m' evs,
  check_socket_pending_error e fd peer ch buf count i eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros e fd peer ch buf count i eff m m' evs H.
  unfold check_socket_pending_error, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H);
  try reflexivity.
Qed.

Lemma sd_write_fault_extend : forall reads m p off eff m' evs,
  check_write_fault_extend reads m p off eff = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros reads m p off eff m' evs H. unfold check_write_fault_extend, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H);
  try reflexivity.
Qed.

Lemma sd_read_proc : forall i buf count eff m m' evs,
  check_read_proc i buf count eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros i buf count eff m m' evs H.
  unfold check_read_proc, check_read_proc_bare in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H);
  try reflexivity.
Qed.

Lemma sd_eventfd_read : forall fd ctx buf count i eff m m' evs,
  check_eventfd_read fd ctx buf count i eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros fd ctx buf count i eff m m' evs H. unfold check_eventfd_read in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H);
  try reflexivity.
Qed.

Lemma sd_eventfd_write : forall fd ctx buf count i eff m m' evs,
  check_eventfd_write fd ctx buf count i eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros fd ctx buf count i eff m m' evs H. unfold check_eventfd_write in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H);
  try reflexivity.
Qed.

Lemma sd_anon_fault_extend : forall reads m id data dst eff m' evs,
  check_anon_fault_extend reads m id data dst eff = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros reads m id data dst eff m' evs H. unfold check_anon_fault_extend in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H);
  try reflexivity.
Qed.

Lemma sd_anon_write_fault : forall reads m id af eff m' evs,
  check_anon_write_fault reads m id af eff = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros reads m id af eff m' evs H. unfold check_anon_write_fault in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H
          || (eapply sd_anon_fault_extend in H; exact H));
  try reflexivity.
Qed.

Lemma check_read_sd : forall i fd buf count eff m m' evs,
  check_read i fd buf count eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_read, check_read_file_data, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H || sd_stream H
          || (apply check_read_opaque_keeps in H; destruct H as [-> ->])
          || (eapply sd_read_urandom in H; exact H)
          || (eapply sd_socket_pending_error in H; exact H)
          || (eapply sd_read_proc in H; exact H)
          || (eapply sd_eventfd_read in H; exact H));
  try reflexivity.
Qed.

Lemma check_write_sd : forall i fd buf count eff m m' evs,
  check_write i fd buf count eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_write, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H || sd_stream H
          || (apply check_write_opaque_keeps in H; destruct H as [-> ->])
          || (eapply sd_write_fault_extend in H; exact H)
          || (eapply sd_eventfd_write in H; exact H)
          || (eapply sd_anon_write_fault in H; exact H));
  try reflexivity.
Qed.

Lemma check_pread64_sd : forall i fd buf count pos eff m m' evs,
  check_pread64 i fd buf count pos eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pread64 in H. cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H
          || (eapply sd_read_urandom in H; exact H));
  try reflexivity.
Qed.

Lemma check_pwrite64_sd : forall i fd buf count pos eff m m' evs,
  check_pwrite64 i fd buf count pos eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pwrite64 in H. cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H
          || (eapply sd_write_fault_extend in H; exact H)
          || (eapply sd_anon_fault_extend in H; exact H));
  try reflexivity.
Qed.

(** OPENAT, ONE SUB-CHECKER AT A TIME.  Unfolding the whole of
    [check_openat] at once multiplies every guard of every arm into
    one case split; each lemma below unfolds one level and closes
    the calls below it by their lemmas. *)
Lemma openat_read_sd : forall p eff m m' evs,
  Open.check_openat_read p eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_read in H. cbv zeta in H.
  repeat (vm_step H || sd_done H); try reflexivity.
Qed.

Lemma openat_create_sd : forall p eff m m' evs,
  Open.check_openat_create p eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_create, check_create_wronly in H. cbv zeta in H.
  repeat (vm_step H || sd_done H); try reflexivity.
Qed.

Lemma openat_append_sd : forall excl p eff m m' evs,
  Open.check_openat_append excl p eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros excl p eff m m' evs H.
  unfold Open.check_openat_append, check_open_append in H. cbv zeta in H.
  repeat (vm_step H || sd_done H); try reflexivity.
Qed.

Lemma openat_rdwr_sd : forall creat trunc p eff m m' evs,
  Open.check_openat_rdwr creat trunc p eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros creat trunc p eff m m' evs H.
  unfold Open.check_openat_rdwr, check_open_rdwr in H. cbv zeta in H.
  repeat (vm_step H || sd_done H); try reflexivity.
Qed.

Lemma openat_rdwr_excl_sd : forall p eff m m' evs,
  Open.check_openat_rdwr_excl p eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_rdwr_excl, check_open_rdwr in H. cbv zeta in H.
  repeat (vm_step H || sd_done H); try reflexivity.
Qed.

Lemma openat_excl_sd : forall p eff m m' evs,
  Open.check_openat_excl p eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_excl, check_create_wronly in H. cbv zeta in H.
  repeat (vm_step H || sd_done H); try reflexivity.
Qed.

Lemma openat_dir_sd : forall p eff m m' evs,
  Open.check_openat_dir p eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_dir in H. cbv zeta in H.
  repeat (vm_step H || sd_done H); try reflexivity.
Qed.

Lemma openat_localtime_sd : forall flags eff m m' evs,
  Open.check_openat_localtime flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros flags eff m m' evs H.
  unfold Open.check_openat_localtime in H. cbv zeta in H.
  repeat (vm_step H || sd_done H); try reflexivity.
Qed.

Lemma openat_devnull_sd : forall flags eff m m' evs,
  Open.check_openat_devnull flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros flags eff m m' evs H.
  unfold Open.check_openat_devnull, Open.check_open_devnull in H. cbv zeta in H.
  repeat (vm_step H || sd_done H); try reflexivity.
Qed.

Lemma openat_urandom_sd : forall flags eff m m' evs,
  Open.check_openat_urandom flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros flags eff m m' evs H.
  unfold Open.check_openat_urandom, Open.check_open_urandom in H. cbv zeta in H.
  repeat (vm_step H || sd_done H); try reflexivity.
Qed.

Lemma openat_proc_result_sd : forall o eff m m' evs,
  Open.check_proc_open_result o eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros o eff m m' evs H.
  unfold Open.check_proc_open_result in H. cbv zeta in H.
  repeat (vm_step H || sd_done H); try reflexivity.
Qed.

Local Ltac openat_sub_sd_tmp H :=
  lazymatch type of H with
  | Open.check_openat_read _ _ _ = CheckOk _ _ => apply openat_read_sd in H; exact H
  | Open.check_openat_create _ _ _ = CheckOk _ _ => apply openat_create_sd in H; exact H
  | Open.check_openat_rdwr_excl _ _ _ = CheckOk _ _ => apply openat_rdwr_excl_sd in H; exact H
  end.

Lemma openat_tmp_sd : forall n p flags eff m m' evs,
  Open.check_openat_tmp n p flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros n p flags eff m m' evs H.
  unfold Open.check_openat_tmp in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_sd_tmp H || sd_done H); try reflexivity.
Qed.

Local Ltac openat_sub_sd_sep H :=
  lazymatch type of H with
  | Open.check_openat_localtime _ _ _ = CheckOk _ _ => apply openat_localtime_sd in H; exact H
  | Open.check_openat_devnull _ _ _ = CheckOk _ _ => apply openat_devnull_sd in H; exact H
  | Open.check_openat_urandom _ _ _ = CheckOk _ _ => apply openat_urandom_sd in H; exact H
  | Open.check_openat_tmp _ _ _ _ _ = CheckOk _ _ => apply openat_tmp_sd in H; exact H
  end.

Lemma openat_sep_sd : forall p flags eff m m' evs,
  Open.check_openat_sep p flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros p flags eff m m' evs H.
  unfold Open.check_openat_sep in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_sd_sep H || sd_done H); try reflexivity.
Qed.

Local Ltac openat_sub_sd_resolved H :=
  lazymatch type of H with
  | Open.check_openat_read _ _ _ = CheckOk _ _ => apply openat_read_sd in H; exact H
  | Open.check_openat_create _ _ _ = CheckOk _ _ => apply openat_create_sd in H; exact H
  | Open.check_openat_excl _ _ _ = CheckOk _ _ => apply openat_excl_sd in H; exact H
  | Open.check_openat_dir _ _ _ = CheckOk _ _ => apply openat_dir_sd in H; exact H
  | Open.check_openat_append _ _ _ _ = CheckOk _ _ => apply openat_append_sd in H; exact H
  | Open.check_openat_rdwr _ _ _ _ _ = CheckOk _ _ => apply openat_rdwr_sd in H; exact H
  | Open.check_openat_rdwr_excl _ _ _ = CheckOk _ _ => apply openat_rdwr_excl_sd in H; exact H
  | Open.check_openat_sep _ _ _ _ = CheckOk _ _ => apply openat_sep_sd in H; exact H
  end.

Lemma openat_resolved_sd : forall p flags eff m m' evs,
  Open.check_openat_resolved p flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros p flags eff m m' evs H.
  unfold Open.check_openat_resolved in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_sd_resolved H || sd_done H); try reflexivity.
Qed.

(** The "/proc/self/fd/N" reopen installs a descriptor with [with_fds]
    and nothing else. *)
Lemma openat_procfd_sd : forall n flags eff m m' evs,
  Open.check_openat_procfd n flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros n flags eff m m' evs H.
  unfold Open.check_openat_procfd in H. cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H); try reflexivity.
Qed.

Local Ltac openat_sub_sd_proc H :=
  lazymatch type of H with
  | Open.check_proc_open_result _ _ _ = CheckOk _ _ => apply openat_proc_result_sd in H; exact H
  | Open.check_openat_procfd _ _ _ _ = CheckOk _ _ => apply openat_procfd_sd in H; exact H
  end.

Lemma openat_proc_sd : forall c flags eff m m' evs,
  Open.check_openat_proc c flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros c flags eff m m' evs H.
  unfold Open.check_openat_proc in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_sd_proc H || sd_done H); try reflexivity.
Qed.

Local Ltac openat_sub_sd_body H :=
  lazymatch type of H with
  | Open.check_openat_proc _ _ _ _ = CheckOk _ _ => apply openat_proc_sd in H; exact H
  | Open.check_openat_resolved _ _ _ _ = CheckOk _ _ => apply openat_resolved_sd in H; exact H
  end.

Lemma openat_body_sd : forall i dirfd pathp flags eff m m' evs,
  Open.check_openat_body i dirfd pathp flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold Open.check_openat_body in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_sd_body H || sd_done H); try reflexivity.
Qed.

Local Ltac openat_sub_sd_top H :=
  lazymatch type of H with
  | Open.check_openat_body _ _ _ _ _ _ = CheckOk _ _ => apply openat_body_sd in H; exact H
  end.

Lemma check_openat_table_sd : forall i dirfd pathp flags eff m m' evs,
  check_openat_table i dirfd pathp flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_openat_table in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_sd_top H || sd_done H); try reflexivity.
Qed.

(** The close-on-exec step writes [State.m_cloexec] alone. *)
Lemma check_openat_sd : forall i dirfd pathp flags eff m m' evs,
  check_openat i dirfd pathp flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i dirfd pathp flags eff m m' evs H. unfold check_openat in H.
  destruct (check_openat_table i dirfd pathp flags eff m) as [m0 evs0| |] eqn:E;
    try discriminate H.
  injection H as <- <-. apply check_openat_table_sd in E.
  unfold open_cloexec_model. destruct (addr_is_error_b (eff_ret eff)); [exact E|].
  destruct (fd_lookup (m_fds m0) (eff_ret eff)); exact E.
Qed.

Lemma check_close_sd : forall fd eff m m' evs,
  check_close fd eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof. intros fd eff m m' evs H. unfold check_close in H. sd_frame2 H. Qed.

Lemma check_close_range_sd : forall fd max_fd flags eff m m' evs,
  check_close_range fd max_fd flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros fd max_fd flags eff m m' evs H. unfold check_close_range in H.
  sd_frame2 H.
Qed.

Lemma check_lseek_sd : forall fd off whence eff m m' evs,
  check_lseek fd off whence eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros fd off whence eff m m' evs H. unfold check_lseek in H. sd_frame2 H.
Qed.

Lemma check_getcwd_sd : forall size eff m m' evs,
  check_getcwd size eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros size eff m m' evs H. unfold check_getcwd in H. sd_frame2 H.
Qed.

Lemma check_getrandom_sd : forall i buf cap flags eff m m' evs,
  check_getrandom i buf cap flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i buf cap flags eff m m' evs H.
  unfold check_getrandom, check_getrandom_zero in H. sd_frame2 H.
Qed.

Lemma check_readlinkat_sd : forall i dirfd eff m m' evs,
  check_readlinkat i dirfd eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros i dirfd eff m m' evs H. unfold check_readlinkat in H. cbv zeta in H.
  sd_frame2 H.
Qed.

Lemma check_exit_sd : forall code eff m m' evs,
  check_exit code eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof. intros code eff m m' evs H. unfold check_exit in H. sd_frame2 H. Qed.

Lemma check_set_tid_address_sd : forall eff m m' evs,
  check_set_tid_address eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros eff m m' evs H. unfold check_set_tid_address in H. sd_frame2 H.
Qed.

Lemma check_ioctl_sd : forall i fd req eff m m' evs,
  check_ioctl i fd req eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros i fd req eff m m' evs H.
  unfold check_ioctl, check_siocgifindex, check_ifreq_writeback in H. sd_frame2 H.
Qed.

Lemma check_writev_sd : forall i fd iov iovcnt eff m m' evs,
  check_writev i fd iov iovcnt eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_writev in H. cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H || sd_stream H
          || (eapply sd_write_fault_extend in H; exact H)
          || (eapply sd_anon_write_fault in H; exact H));
  try reflexivity.
Qed.

Lemma check_pwritev2_sd :
  forall i fd iov iovcnt pos_l pos_h flags eff m m' evs,
  check_pwritev2 i fd iov iovcnt pos_l pos_h flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd iov iovcnt pos_l pos_h flags eff m m' evs H.
  unfold check_pwritev2 in H. cbv beta iota zeta in H.
  repeat (vm_step H || sd_done H || sd_stream H
          || (eapply sd_anon_fault_extend in H; exact H));
  try reflexivity.
Qed.

Lemma check_readv_imported_sd : forall i fd r iovs0 eff m m' evs,
  check_readv_imported i fd r iovs0 eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd r iovs0 eff m m' evs H.
  unfold check_readv_imported in H.
  sd_frame3 H.
Qed.

Lemma check_readv_sd : forall i fd iov iovcnt eff m m' evs,
  check_readv i fd iov iovcnt eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_readv in H.
  repeat (vm_step H || sd_done H
          || (apply check_readv_imported_sd in H; exact H));
  try reflexivity.
Qed.

(** [wait4] keeps the bit: its reap removes a recorded pid and nothing
    else. *)
Lemma check_wait4_sd : forall i upid stat_addr options rusage eff m m' evs,
  check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i upid stat_addr options rusage eff m m' evs H.
  unfold check_wait4 in H.
  repeat (cbv beta iota zeta in H;
          lazymatch type of H with
          | CheckOk _ _ = CheckOk _ _ => fail
          | _ => first
                 [ discriminate H
                 | match type of H with
                   | context [match ?x with _ => _ end] => destruct x eqn:?
                   | context [if ?b then _ else _] => destruct b eqn:?
                   end ]
          end).
  all: injection H as <- _.
  all: reflexivity.
Qed.

Lemma check_epoll_create1_sd : forall flags32 eff m m' evs,
  check_epoll_create1 flags32 eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros flags32 eff m m' evs H. unfold check_epoll_create1 in H. sd_frame2 H.
Qed.

Lemma check_epoll_ctl_sd : forall i epfd op32 tfd event eff m m' evs,
  check_epoll_ctl i epfd op32 tfd event eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i epfd op32 tfd event eff m m' evs H.
  unfold check_epoll_ctl in H. sd_frame2 H.
Qed.

Lemma check_epoll_pwait_sd :
  forall i epfd events maxevents32 sigmask sigsetsize eff m m' evs,
  check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m
    = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i epfd events maxevents32 sigmask sigsetsize eff m m' evs H.
  unfold check_epoll_pwait in H. sd_frame2 H.
Qed.

Lemma check_fsync_sd : forall fd eff m m' evs,
  check_fsync fd eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof. intros fd eff m m' evs H. unfold check_fsync in H. sd_frame2 H. Qed.

Lemma check_getdents64_sd : forall i fd dirent count eff m m' evs,
  check_getdents64 i fd dirent count eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros i fd dirent count eff m m' evs H.
  unfold check_getdents64 in H.
  repeat (vm_step H || sd_done H || (apply check_getdents64_opaque_fds in H; destruct H as ((fds & ->) & ->))); try reflexivity.
Qed.

Lemma check_flock_sd : forall fd cmd eff m m' evs,
  check_flock fd cmd eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros fd cmd eff m m' evs H. unfold check_flock in H. sd_frame2 H.
Qed.

Lemma check_timerfd_create_sd : forall clkid flags eff m m' evs,
  check_timerfd_create clkid flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros clkid flags eff m m' evs H.
  unfold check_timerfd_create in H. sd_frame2 H.
Qed.

Lemma check_eventfd2_sd : forall i flags eff m m' evs,
  check_eventfd2 i flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i flags eff m m' evs H.
  unfold check_eventfd2, check_new_fd_result in H. sd_frame2 H.
Qed.

Lemma check_signalfd4_sd : forall i ufd mask sizemask flags eff m m' evs,
  check_signalfd4 i ufd mask sizemask flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i ufd mask sizemask flags eff m m' evs H.
  unfold check_signalfd4, check_new_fd_result in H. sd_frame2 H.
Qed.

Lemma check_uname_sd : forall i name eff m m' evs,
  check_uname i name eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i name eff m m' evs H.
  unfold check_uname, check_uname_copy in H. sd_frame2 H.
Qed.

Lemma check_prlimit64_sd :
  forall i pid resource new_rlim old_rlim eff m m' evs,
  check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i pid resource new_rlim old_rlim eff m m' evs H.
  unfold check_prlimit64, check_rlim64_read in H. sd_frame2 H.
Qed.

Lemma check_capget_sd : forall i header dataptr eff m m' evs,
  check_capget i header dataptr eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i header dataptr eff m m' evs H.
  unfold check_capget, check_capget_copy in H. sd_frame2 H.
Qed.

Lemma check_capset_sd : forall i header data eff m m' evs,
  check_capset i header data eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i header data eff m m' evs H.
  unfold check_capset in H. sd_frame2 H.
Qed.

Lemma check_ftruncate_sd : forall fd len eff m m' evs,
  check_ftruncate fd len eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros fd len eff m m' evs H. unfold check_ftruncate in H. sd_frame2 H.
Qed.

Lemma check_getpid_sd : forall eff m m' evs,
  check_getpid eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof. exact check_set_tid_address_sd. Qed.

Lemma check_gettid_sd : forall eff m m' evs,
  check_gettid eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof. exact check_set_tid_address_sd. Qed.

Lemma check_getppid_sd : forall eff m m' evs,
  check_getppid eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof. intros eff m m' evs H. unfold check_getppid in H. sd_frame2 H. Qed.

Lemma check_setsid_sd : forall eff m m' evs,
  check_setsid eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof. intros eff m m' evs H. unfold check_setsid in H. sd_frame2 H. Qed.

Lemma check_getsid_sd : forall pid eff m m' evs,
  check_getsid pid eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros pid eff m m' evs H. unfold check_getsid, check_pid_choice in H.
  sd_frame2 H.
Qed.

Lemma check_prctl_sd : forall i option_ arg2 eff m m' evs,
  check_prctl i option_ arg2 eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros i option_ arg2 eff m m' evs H.
  unfold check_prctl, check_ret_writes in H. sd_frame2 H.
Qed.

Lemma check_gettimeofday_sd : forall i tv tz eff m m' evs,
  check_gettimeofday i tv tz eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i tv tz eff m m' evs H.
  unfold check_gettimeofday in H. sd_frame2 H.
Qed.

Lemma check_clock_gettime_sd : forall i clkid tp eff m m' evs,
  check_clock_gettime i clkid tp eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i clkid tp eff m m' evs H.
  unfold check_clock_gettime in H. sd_frame2 H.
Qed.

Lemma check_clock_getres_sd : forall i clkid tp eff m m' evs,
  check_clock_getres i clkid tp eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i clkid tp eff m m' evs H.
  unfold check_clock_getres, check_clock_getres_result in H. sd_frame2 H.
Qed.

Lemma check_nanosleep_sd : forall i rqtp rmtp eff m m' evs,
  check_nanosleep i rqtp rmtp eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i rqtp rmtp eff m m' evs H.
  unfold check_nanosleep in H. sd_frame2 H.
Qed.

Lemma check_dup_sd : forall oldfd eff m m' evs,
  check_dup oldfd eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros oldfd eff m m' evs H.
  unfold check_dup, check_dup_result in H. sd_frame2 H.
Qed.

Lemma check_dup3_sd : forall oldfd newfd flags eff m m' evs,
  check_dup3 oldfd newfd flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros oldfd newfd flags eff m m' evs H. unfold check_dup3 in H. sd_frame2 H.
Qed.

Lemma check_unlinkat_sd : forall i dirfd pathp flags eff m m' evs,
  check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_unlinkat, Namei.check_unlinkat_body, Namei.check_unlinkat_tmp,
    Namei.check_unlink_found, check_unlink_result, Namei.check_unlink_open_tmp,
    check_unlink_open_result, check_unlink_type_result in H.
  sd_frame2 H.
Qed.

Lemma check_faccessat_sd : forall i dirfd pathp mode eff m m' evs,
  check_faccessat i dirfd pathp mode eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i dirfd pathp mode eff m m' evs H.
  unfold check_faccessat, Open.check_faccessat_body, check_access_exists in H.
  sd_frame2 H.
Qed.

Lemma check_faccessat2_sd : forall i dirfd pathp mode flags eff m m' evs,
  check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i dirfd pathp mode flags eff m m' evs H.
  unfold check_faccessat2, Open.check_faccessat_body, check_access_exists in H.
  sd_frame2 H.
Qed.

Lemma check_pselect6_sd : forall i n32 inp outp exp tsp sig eff m m' evs,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H.
  unfold check_pselect6, check_pselect_answer in H. sd_frame2 H.
Qed.

Lemma check_ppoll_sd : forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold check_ppoll, check_pselect_answer in H. sd_frame2 H.
Qed.

Lemma check_newfstatat_sd : forall i dirfd pathp flag eff m m' evs,
  check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i dirfd pathp flag eff m m' evs H.
  unfold check_newfstatat, check_newfstatat_proc, check_newfstatat_proc_errno in H.
  sd_frame2 H.
Qed.

Lemma check_fstat_file_sd : forall i p statbuf eff m m' evs,
  check_fstat_file i p statbuf eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i p statbuf eff m m' evs H.
  unfold check_fstat_file in H.
  destruct (fs_lookup (m_fs m) p) as [data|]; [|discriminate].
  destruct (negb (access_okb statbuf STAT_SIZE)); [sd_frame2 H|].
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

Lemma check_fstat_chrdev_sd : forall ok p i statbuf eff m m' evs,
  check_fstat_chrdev ok p i statbuf eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros ok p i statbuf eff m m' evs H.
  unfold check_fstat_chrdev in H.
  destruct (negb (access_okb statbuf STAT_SIZE)); [sd_frame2 H|].
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

Lemma check_fstat_devnull_sd : forall i statbuf eff m m' evs,
  check_fstat_devnull i statbuf eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof. intros. eapply check_fstat_chrdev_sd. exact H. Qed.

Lemma check_fstat_urandom_sd : forall i statbuf eff m m' evs,
  check_fstat_urandom i statbuf eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof. intros. eapply check_fstat_chrdev_sd. exact H. Qed.

(** The /proc/self/fd directory's [fstat] hands back the model it was
    given; the other opaque objects decline. *)
Lemma check_fstat_opaque_sd : forall i o statbuf eff m m' evs,
  check_fstat_opaque i o statbuf eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros i o statbuf eff m m' evs H.
  apply check_fstat_opaque_keeps in H as (-> & _). reflexivity.
Qed.

Lemma check_fstat_anon_sd : forall i id af statbuf eff m m' evs,
  check_fstat_anon i id af statbuf eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i id af statbuf eff m m' evs H.
  unfold check_fstat_anon in H.
  destruct (negb (access_okb statbuf STAT_SIZE)); [sd_frame2 H|].
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE)) as [w|];
    [|discriminate].
  assert (Hdel : exists pin,
             check_fstat_anon_deliver statbuf id (length (af_data af)) pin eff m
             = CheckOk m' evs).
  { destruct (af_pin af) as [b0|]; [|eauto].
    destruct (negb (stat_buf_wf b0 && stat_is_reg b0 && stat_nlink_zero b0)%bool);
      [discriminate|eauto]. }
  destruct Hdel as (pin & Hd).
  apply check_fstat_anon_deliver_ok in Hd
    as (bs & _ & _ & _ & _ & _ & _ & [(b1 & _ & _ & ->)|(_ & ->)]);
    first [reflexivity | autorewrite with model; reflexivity].
Qed.

Lemma check_fstat_sd : forall i fd statbuf eff m m' evs,
  check_fstat i fd statbuf eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros i fd statbuf eff m m' evs H. unfold check_fstat in H.
  destruct (fd_lookup (m_fds m) fd) as [e|]; [|sd_frame2 H].
  destruct e as [ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| |sid side st|ctx|fam|aid af|o|i0 sd st];
    cbv iota in H; try discriminate.
  (* the unnamed file: past the agreement test *)
  all: try (destruct (negb (anon_agree (m_fds m) aid af)); cbv iota in H;
            [discriminate|]).
  all: first [eapply check_fstat_file_sd; exact H
             |eapply check_fstat_devnull_sd; exact H
             |eapply check_fstat_urandom_sd; exact H
             |eapply check_fstat_anon_sd; exact H
             |eapply check_fstat_opaque_sd; exact H].
Qed.

Lemma check_getid_sd : forall sel eff m m' evs,
  check_getid sel eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof. intros sel eff m m' evs H. unfold check_getid in H. sd_frame2 H. Qed.

Lemma check_getresid_sd : forall i get rp ep sp eff m m' evs,
  check_getresid i get rp ep sp eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i get rp ep sp eff m m' evs H.
  unfold check_getresid, check_ret_writes in H. sd_frame2 H.
Qed.

Lemma check_setid_sd : forall get put user v eff m m' evs,
  check_setid get put user v eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros get put user v eff m m' evs H.
  unfold check_setid, check_setid_result in H. sd_frame2 H.
Qed.

Lemma check_setresid_sd : forall get put user r e sv eff m m' evs,
  check_setresid get put user r e sv eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros get put user r e sv eff m m' evs H.
  unfold check_setresid, check_setid_result in H. sd_frame2 H.
Qed.

Lemma check_getgroups_sd : forall gidsetsize eff m m' evs,
  check_getgroups gidsetsize eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros gidsetsize eff m m' evs H. unfold check_getgroups in H. sd_frame2 H.
Qed.

Lemma check_setgroups_sd : forall i eff m m' evs,
  check_setgroups i eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros i eff m m' evs H. unfold check_setgroups in H. sd_frame2 H.
Qed.

Lemma check_socket_sd : forall domain type protocol eff m m' evs,
  check_socket domain type protocol eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros domain type protocol eff m m' evs H.
  unfold check_socket, check_new_fd_result, check_errno_or_list in H. sd_frame2 H.
Qed.

Lemma check_bind_sd : forall i fd addrp addrlen eff m m' evs,
  check_bind i fd addrp addrlen eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold check_bind, check_errno_or_success in H. sd_frame2 H.
Qed.

Lemma check_listen_sd : forall fd backlog eff m m' evs,
  check_listen fd backlog eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros fd backlog eff m m' evs H.
  unfold check_listen, check_errno_or_success, check_errno_only in H.
  sd_frame2 H.
Qed.

Lemma check_connect_sd : forall i fd addrp addrlen eff m m' evs,
  check_connect i fd addrp addrlen eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold check_connect in H. sd_frame2 H.
Qed.

Lemma check_accept4_sd : forall fd addrp addrlenp flags eff m m' evs,
  check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros fd addrp addrlenp flags eff m m' evs H.
  (* [check_errno_only] is unfolded alongside, the way
     [check_read_sd] unfolds [check_access_ok_zero]: it is the arm
     [check_accept4] takes once [Net.Socket.conn_ix_exhausted] holds, and
     [vm_step] sees no [if] or [match] through a folded definition, so
     without the unfold that branch leaves an open goal. *)
  unfold check_accept4, check_new_fd_result, check_errno_or_success,
    check_errno_only, check_errno_or_list in H. sd_frame2 H.
Qed.

Lemma check_fcntl_sd : forall fd cmd arg eff m m' evs,
  check_fcntl fd cmd arg eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros fd cmd arg eff m m' evs H. unfold check_fcntl in H. sd_frame2 H.
Qed.

Lemma check_sched_setscheduler_sd : forall i pid policy param eff m m' evs,
  check_sched_setscheduler i pid policy param eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i pid policy param eff m m' evs H.
  unfold check_sched_setscheduler in H. sd_frame2 H.
Qed.

Lemma check_sched_getaffinity_sd : forall len eff m m' evs,
  check_sched_getaffinity len eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros len eff m m' evs H. unfold check_sched_getaffinity in H. sd_frame2 H.
Qed.

Lemma check_sched_yield_sd : forall eff m m' evs,
  check_sched_yield eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros eff m m' evs H. unfold check_sched_yield in H. sd_frame2 H.
Qed.

Lemma check_sigaltstack_sd : forall i uss uoss eff m m' evs,
  check_sigaltstack i uss uoss eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i uss uoss eff m m' evs H.
  unfold check_sigaltstack in H. sd_frame2 H.
Qed.

(** [rt_sigaction] keeps the pair, or its SIGCHLD SIG_DFL install
    ([Kernel.Signal.sigchld_dfl_install]) leaves
    [Kernel.Signal.sigchld_install_model] of the model: the bit set when
    the process has no recorded child, and kept otherwise.  No answer
    clears it: every other SIGCHLD install (SIG_IGN, a handler,
    SA_NOCLDWAIT) declines. *)
Lemma check_rt_sigaction_sd : forall i sig act oact ss eff m m' evs,
  check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs ->
  sd_of m' = sd_of m \/ sd_of m' = sd_of (sigchld_install_model m).
Proof.
  intros i sig act oact ss eff m m' evs H.
  unfold check_rt_sigaction in H.
  destruct (negb (bv_eqb ss (Z_to_bv 64 8))); cbv beta iota in H; [left; sd_frame2 H|].
  destruct (Z.eqb (bv_unsigned sig) SIGPIPE); cbv beta iota in H.
  { (* the SIGPIPE arm: [check_rt_sigaction_sigpipe] is opaque to the
       cascade, and its install carries the bit and [m_has_children] *)
    destruct (check_rt_sigaction_sigpipe_model _ _ _ _ _ _ _ H) as [-> | (a & ->)];
      left; reflexivity. }
  repeat (vm_step H || (apply check_efault_or_sd in H; left; exact H));
    first [left; reflexivity | right; reflexivity].
Qed.

Lemma check_getsockname_sd : forall i fd eff m m' evs,
  check_getsockname i fd eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd eff m m' evs H.
  unfold check_getsockname, check_getsockname_core, check_stream_getname,
    check_ret_writes_copyins in H.
  cbv zeta in H. sd_frame2 H.
Qed.

Lemma check_getpeername_sd : forall i fd eff m m' evs,
  check_getpeername i fd eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd eff m m' evs H.
  unfold check_getpeername, check_getpeername_core, check_stream_getname,
    check_ret_writes_copyins in H.
  cbv zeta in H. sd_frame2 H.
Qed.

Lemma check_setsockopt_sd : forall i fd level optlen eff m m' evs,
  check_setsockopt i fd level optlen eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd level optlen eff m m' evs H.
  unfold check_setsockopt, check_seqpacket_setsockopt, check_setsockopt_core,
    check_stream_setsockopt in H.
  cbv zeta in H. sd_frame2 H.
Qed.

Lemma check_getsockopt_sd : forall i fd level optlenp eff m m' evs,
  check_getsockopt i fd level optlenp eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd level optlenp eff m m' evs H.
  unfold check_getsockopt, check_getsockopt_core, check_stream_getsockopt,
    check_ret_writes_copyins in H.
  cbv zeta in H. sd_frame2 H.
Qed.

Lemma check_shutdown_sd : forall fd how eff m m' evs,
  check_shutdown fd how eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros fd how eff m m' evs H.
  unfold check_shutdown, check_shutdown_core, check_stream_shutdown in H.
  cbv zeta in H. sd_frame2 H.
Qed.

Lemma check_send_on_socket_sd :
  forall pre acc fd sk total bs eff m m' evs,
  check_send_on_socket pre acc fd sk total bs eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros pre acc fd sk total bs eff m m' evs H.
  unfold check_send_on_socket in H. sd_frame2 H.
Qed.

Lemma check_recv_fd_answer_sd : forall fds fd eff m m' evs,
  check_recv_fd_answer fds fd eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros fds fd eff m m' evs H.
  unfold check_recv_fd_answer in H. sd_frame2 H.
Qed.

Lemma check_socketpair_sd : forall i family type protocol sv eff m m' evs,
  check_socketpair i family type protocol sv eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i family type protocol sv eff m m' evs H.
  unfold check_socketpair, check_socketpair_unix, check_socketpair_seqpacket_written,
    check_socketpair_unix_written, check_socketpair_written, check_socketpair_faulted,
    check_errno_only in H.
  cbv zeta in H.
  sd_frame2 H.
Qed.
Print Assumptions check_socketpair_sd.

Lemma check_recvfrom_sd : forall i fd buf size eff m m' evs,
  check_recvfrom i fd buf size eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd buf size eff m m' evs H.
  unfold check_recvfrom, check_access_ok_zero, check_recv_fd_answer in H.
  sd_frame3 H.
Qed.

Lemma check_recvmsg_sd : forall i fd flags eff m m' evs,
  check_recvmsg i fd flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd flags eff m m' evs H.
  unfold check_recvmsg, check_seqpacket_recvmsg, check_recvmsg_eof_writes,
    check_ret_writes_copyins, check_recv_fd_answer in H. sd_frame2 H.
Qed.

Lemma check_sendto_sd : forall i fd buf count flags addrp eff m m' evs,
  check_sendto i fd buf count flags addrp eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd buf count flags addrp eff m m' evs H.
  unfold check_sendto, check_access_ok_zero, check_send_on_socket in H.
  sd_frame3 H.
Qed.

Lemma check_sendmsg_sd : forall i fd msgp flags eff m m' evs,
  check_sendmsg i fd msgp flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fd msgp flags eff m m' evs H.
  unfold check_sendmsg, check_send_on_socket in H. sd_frame2 H.
Qed.

Lemma check_pipe2_sd : forall i fildes flags eff m m' evs,
  check_pipe2 i fildes flags eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i fildes flags eff m m' evs H.
  unfold check_pipe2, pipe2_model in H. sd_frame2 H.
Qed.

Lemma check_futex_sd : forall i uaddr op val utime eff m m' evs,
  check_futex i uaddr op val utime eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros i uaddr op val utime eff m m' evs H.
  unfold check_futex, check_futex_wake_private, check_futex_wait_private in H.
  sd_frame2 H.
Qed.

Lemma check_set_robust_list_sd : forall len eff m m' evs,
  check_set_robust_list len eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros len eff m m' evs H.
  unfold check_set_robust_list in H. sd_frame2 H.
Qed.

Lemma check_setns_sd : forall fd eff m m' evs,
  check_setns fd eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
Proof.
  intros fd eff m m' evs H.
  unfold check_setns in H. sd_frame2 H.
Qed.

(** The memory-management arms build their post-models through the
    wrappers of [Sys.Mm]; two of them branch or recurse, so they get a
    lemma, and every other wrapper keeps [sd_of] by conversion. *)
Lemma sd_of_forget_vm_ranges : forall rs m, sd_of (forget_vm_ranges rs m) = sd_of m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma sd_of_with_brk_next : forall m req r, sd_of (with_brk_next m req r) = sd_of m.
Proof.
  intros m req r. unfold with_brk_next. cbv zeta.
  rewrite sd_of_forget_vm_ranges. reflexivity.
Qed.

Lemma sd_of_with_mmap_backing : forall flags a n m,
  sd_of (with_mmap_backing flags a n m) = sd_of m.
Proof.
  intros flags a n m. unfold with_mmap_backing.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.

Lemma sd_of_with_mmap_replacement : forall flags a n m,
  sd_of (with_mmap_replacement flags a n m) = sd_of m.
Proof.
  intros flags a n m. unfold with_mmap_replacement.
  rewrite sd_of_with_mmap_backing. reflexivity.
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
  rewrite ?sd_of_with_mmap_backing, ?sd_of_with_mmap_replacement, ?sd_of_with_brk_next;
  reflexivity.

Lemma check_brk_sd : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros req [ret ws zs us cs ci] m m' evs H.
  unfold check_brk in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_mmap_sd : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H.
  (* [unfold] takes its names in order: [check_ret_only] goes last, so
     the one inside [check_mmap_fixed_overflow] (the -ENOMEM answer) is
     opened too, as [MmStepFrame.check_mmap_mm_frame] does. *)
  unfold check_mmap, check_mmap_fixed_overflow, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_mremap_sd : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H.
  unfold check_mremap, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_munmap_sd : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H.
  unfold check_munmap, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_mprotect_sd : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H.
  unfold check_mprotect, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_madvise_sd : forall addr len advice eff m m' evs,
  check_madvise addr len advice eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
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

Lemma sd_of_sigmask_deliver_model : forall new m,
  sd_of (sigmask_deliver_model new m) = sd_of m.
Proof.
  intros new m. unfold sigmask_deliver_model.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    reflexivity.
Qed.

Lemma check_rt_sigprocmask_sd : forall i how nset oset ss eff m m' evs,
  check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs ->
  sd_of m' = sd_of m.
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
    now rewrite sd_of_sigmask_deliver_model. }
  unfold check_write_oset_copyins in H.
  destruct (check_write_oset i oset (m_sigmask m) (clear_copyins eff)
              (sigmask_deliver_model (sigmask_apply how (m_sigmask m)
                               (sigmask_strip raw)) m))
    as [m2 evs2| |] eqn:Hcw; [|discriminate|discriminate].
  destruct (access_ranges_eqb (eff_copyins eff)
              [(nset, Z.to_nat NSIG_BYTES)]); [|discriminate].
  apply check_write_oset_ok_iff in Hcw. destruct Hcw as (-> & _ & _ & _).
  inversion H; subst. now rewrite sd_of_sigmask_deliver_model.
Qed.

Lemma check_kill_sd : forall pid sig eff m m' evs,
  check_kill pid sig eff m = CheckOk m' evs -> sd_of m' = sd_of m.
Proof.
  intros pid sig eff m m' evs H.
  unfold check_kill, check_kill_self in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; cbv beta iota in H
         | match ?x with _ => _ end = _ => destruct x; cbv beta iota in H
         end;
    try discriminate;
    apply check_ret_only_ok_iff in H; destruct H as (_ & -> & _);
    autorewrite with model; reflexivity.
Qed.

Lemma check_tkill_sd : forall pid sig eff m m' evs,
  check_tkill pid sig eff m = CheckOk m' evs -> sd_of m' = sd_of m.
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

Lemma check_tgkill_sd : forall tgid pid sig eff m m' evs,
  check_tgkill tgid pid sig eff m = CheckOk m' evs -> sd_of m' = sd_of m.
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


(** A clone's answer carries the bit, and the pid side sets
    [m_has_children]: [Kernel.Fork.clone_child_made] is [State.with_child]
    over [State.with_fds], and both pass the rest of [m_proc] across by
    conversion. *)
Lemma clone_answer_sd : forall eff m m', clone_answer eff m m' ->
  sd_of m' = sd_of m \/ (m_sigchld_dfl m' = m_sigchld_dfl m /\ m_has_children m' = true).
Proof.
  intros eff m m' [(-> & _) | (-> & _)]; [left; reflexivity | right; split; reflexivity].
Qed.

Definition arm_sd (c : CheckedArm) : Prop :=
  forall i eff m m' evs, ca_check c i eff m = CheckOk m' evs -> sd_kept (ca_no c) m m'.

Lemma checked_table_sd : Forall arm_sd checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_sd).
  all: unfold arm_sd; intros i eff m m' evs H; autorewrite with arm_unfold in H.
  (* The three special arms are picked by their number first, a closed
     [vm_compute], as [checked_table_cp] does; only then is [H] read
     against [check_clone_cp], [check_clone3_cp] or
     [check_rt_sigaction_sd].  Elaborating those three against another
     arm's [H] first did not finish at the [sched_setscheduler] arm
     (more than fifteen minutes there; this form takes seconds). *)
  all: lazymatch goal with
  | |- sd_kept ?n _ _ =>
    first
    [ assert_succeeds (assert ((n =? 220)%Z = true) by (vm_compute; reflexivity));
      destruct (clone_answer_sd _ _ _ (check_clone_cp _ _ _ _ _ H)) as [E | E];
      [ left; exact E | right; right; split; [vm_compute; reflexivity | exact E] ]
    | assert_succeeds (assert ((n =? 435)%Z = true) by (vm_compute; reflexivity));
      destruct (clone_answer_sd _ _ _ (check_clone3_cp _ _ _ _ _ _ _ H)) as [E | E];
      [ left; exact E | right; right; split; [vm_compute; reflexivity | exact E] ]
    | assert_succeeds (assert ((n =? 134)%Z = true) by (vm_compute; reflexivity));
      destruct (check_rt_sigaction_sd _ _ _ _ _ _ _ _ _ H) as [E | E];
      [ left; exact E | right; left; split; [vm_compute; reflexivity | exact E] ]
    | left;
      first
      [ eapply check_wait4_sd; eassumption
        | eapply check_read_sd; eassumption
        | eapply check_brk_sd; eassumption
        | eapply check_munmap_sd; eassumption
        | eapply check_mremap_sd; eassumption
        | eapply check_mmap_sd; eassumption
        | eapply check_mprotect_sd; eassumption
        | eapply check_write_sd; eassumption
        | eapply check_pread64_sd; eassumption
        | eapply check_pwrite64_sd; eassumption
        | eapply check_openat_sd; eassumption
        | eapply check_close_sd; eassumption
        | eapply check_close_range_sd; eassumption
        | eapply check_lseek_sd; eassumption
        | eapply check_getcwd_sd; eassumption
        | eapply check_getrandom_sd; eassumption
        | eapply check_readlinkat_sd; eassumption
        | eapply check_exit_sd; eassumption
        | eapply check_set_tid_address_sd; eassumption
        | eapply check_ioctl_sd; eassumption
        | eapply check_writev_sd; eassumption
        | eapply check_pwritev2_sd; eassumption
        | eapply check_readv_imported_sd; eassumption
        | eapply check_readv_sd; eassumption
        | eapply check_epoll_create1_sd; eassumption
        | eapply check_epoll_ctl_sd; eassumption
        | eapply check_epoll_pwait_sd; eassumption
        | eapply check_fsync_sd; eassumption
        | eapply check_getdents64_sd; eassumption
        | eapply check_flock_sd; eassumption
        | eapply check_timerfd_create_sd; eassumption
        | eapply check_eventfd2_sd; eassumption
        | eapply check_signalfd4_sd; eassumption
        | eapply check_uname_sd; eassumption
        | eapply check_prlimit64_sd; eassumption
        | eapply check_capget_sd; eassumption
        | eapply check_capset_sd; eassumption
        | eapply check_ftruncate_sd; eassumption
        | eapply check_getpid_sd; eassumption
        | eapply check_gettid_sd; eassumption
        | eapply check_getppid_sd; eassumption
        | eapply check_setsid_sd; eassumption
        | eapply check_getsid_sd; eassumption
        | eapply check_prctl_sd; eassumption
        | eapply check_gettimeofday_sd; eassumption
        | eapply check_clock_gettime_sd; eassumption
        | eapply check_clock_getres_sd; eassumption
        | eapply check_nanosleep_sd; eassumption
        | eapply check_dup_sd; eassumption
        | eapply check_dup3_sd; eassumption
        | eapply check_unlinkat_sd; eassumption
        | eapply check_faccessat_sd; eassumption
        | eapply check_faccessat2_sd; eassumption
        | eapply check_pselect6_sd; eassumption
        | eapply check_ppoll_sd; eassumption
        | eapply check_newfstatat_sd; eassumption
        | eapply check_fstat_file_sd; eassumption
        | eapply check_fstat_chrdev_sd; eassumption
        | eapply check_fstat_devnull_sd; eassumption
        | eapply check_fstat_urandom_sd; eassumption
        | eapply check_fstat_sd; eassumption
        | eapply check_getid_sd; eassumption
        | eapply check_getresid_sd; eassumption
        | eapply check_setid_sd; eassumption
        | eapply check_setresid_sd; eassumption
        | eapply check_getgroups_sd; eassumption
        | eapply check_setgroups_sd; eassumption
        | eapply check_socket_sd; eassumption
        | eapply check_bind_sd; eassumption
        | eapply check_listen_sd; eassumption
        | eapply check_connect_sd; eassumption
        | eapply check_accept4_sd; eassumption
        | eapply check_fcntl_sd; eassumption
        | eapply check_sched_setscheduler_sd; eassumption
        | eapply check_sched_getaffinity_sd; eassumption
        | eapply check_sched_yield_sd; eassumption
        | eapply check_sigaltstack_sd; eassumption
        | eapply check_getsockname_sd; eassumption
        | eapply check_getpeername_sd; eassumption
        | eapply check_setsockopt_sd; eassumption
        | eapply check_getsockopt_sd; eassumption
        | eapply check_shutdown_sd; eassumption
        | eapply check_send_on_socket_sd; eassumption
        | eapply check_recv_fd_answer_sd; eassumption
        | eapply check_socketpair_sd; eassumption
        | eapply check_recvfrom_sd; eassumption
        | eapply check_recvmsg_sd; eassumption
        | eapply check_sendto_sd; eassumption
        | eapply check_sendmsg_sd; eassumption
        | eapply check_pipe2_sd; eassumption
        | eapply check_futex_sd; eassumption
        | eapply check_set_robust_list_sd; eassumption
        | eapply check_setns_sd; eassumption
        | eapply check_madvise_sd; eassumption
        | eapply check_rt_sigprocmask_sd; eassumption
        | eapply check_kill_sd; eassumption
        | eapply check_tkill_sd; eassumption
        | eapply check_tgkill_sd; eassumption
      ]
    | fail 1 "checked_table_sd has no case for this arm: give its checker a *_sd lemma above" ]
  end.
Qed.

(** THE SPEC FACT: every released answer keeps the pair, but an
    [rt_sigaction]'s, which may leave [sigchld_install_model] of it, and a
    clone's, which keeps the bit and may set [m_has_children]. *)
Theorem syscall_spec_sigchld : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  sd_kept (bv_unsigned (in_sysno i)) m m'.
Proof.
  intros i m eff m' evs H. apply check_syscall_ok_iff in H.
  unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_sd as Hall. rewrite Forall_forall in Hall.
  rewrite <- (lookup_ca_no _ _ _ Elk).
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H).
Qed.

(** The install's two components, by conversion. *)
Lemma sd_install_bit : forall m,
  m_sigchld_dfl (sigchld_install_model m) = m_sigchld_dfl m || negb (m_has_children m).
Proof. reflexivity. Qed.

Lemma sd_install_hc : forall m,
  m_has_children (sigchld_install_model m) = m_has_children m.
Proof. reflexivity. Qed.

(** So no released answer clears the bit ... *)
Corollary syscall_spec_sigchld_mono : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  m_sigchld_dfl m = true -> m_sigchld_dfl m' = true.
Proof.
  intros i m eff m' evs H Hd.
  destruct (syscall_spec_sigchld _ _ _ _ _ H) as [E | [(_ & E) | (_ & E & _)]];
    try unfold sd_of in E.
  - injection E as E1 E2. rewrite E1. exact Hd.
  - injection E as E1 E2. rewrite E1, sd_install_bit, Hd. reflexivity.
  - rewrite E. exact Hd.
Qed.

(** ... nor [m_has_children] ... *)
Corollary syscall_spec_has_children_mono : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  m_has_children m = true -> m_has_children m' = true.
Proof.
  intros i m eff m' evs H Hc.
  destruct (syscall_spec_sigchld _ _ _ _ _ H) as [E | [(_ & E) | (_ & _ & E)]];
    try unfold sd_of in E.
  - injection E as E1 E2. rewrite E2. exact Hc.
  - injection E as E1 E2. rewrite E2, sd_install_hc. exact Hc.
  - exact E.
Qed.

(** ... and none sets the bit of a process that has had a child: the
    rule [Kernel.Signal.sigchld_install_model] states. *)
Corollary syscall_spec_sigchld_no_set_with_children : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  m_has_children m = true -> m_sigchld_dfl m = false -> m_sigchld_dfl m' = false.
Proof.
  intros i m eff m' evs H Hc Hd.
  destruct (syscall_spec_sigchld _ _ _ _ _ H) as [E | [(_ & E) | (_ & E & _)]];
    try unfold sd_of in E.
  - injection E as E1 E2. rewrite E1. exact Hd.
  - injection E as E1 E2. rewrite E1, sd_install_bit, Hd, Hc. reflexivity.
  - rewrite E. exact Hd.
Qed.

(** A process with an unreaped child on its list has had a child. *)
Definition hc_ok (m : Model) : Prop := m_child_pids m <> [] -> m_has_children m = true.

Corollary syscall_spec_hc_ok : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) -> hc_ok m -> hc_ok m'.
Proof.
  intros i m eff m' evs H Hok Hn.
  destruct (syscall_spec_child_pids _ _ _ _ _ H)
    as [(_ & [E | (_ & q & _ & E)]) | (_ & [(-> & _) | (-> & _)])].
  - apply (syscall_spec_has_children_mono _ _ _ _ _ H). apply Hok.
    unfold cp_of in E. rewrite <- E. exact Hn.
  - apply (syscall_spec_has_children_mono _ _ _ _ _ H). apply Hok.
    intros Hm. apply Hn. unfold cp_of in E. rewrite E, Hm. reflexivity.
  - exact (Hok Hn).
  - reflexivity.
Qed.

(* =========================================================================
   The released step
   ========================================================================= *)

Lemma sd_materialize : forall m acc m'',
  materialize_model_accesses m acc = Some m'' -> m_sigchld_dfl m'' = m_sigchld_dfl m.
Proof.
  intros m acc m'' H.
  destruct (materialize_model_accesses_frame _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _).
  unfold m_sigchld_dfl. rewrite Hp. reflexivity.
Qed.

(** A released step either keeps the model's [ProcState] or ends in the
    [ProcState] of a released answer. *)
Lemma sstep_proc_cases : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  m_proc (cfg_model c') = m_proc (cfg_model c)
  \/ exists i eff m' evs',
       syscall_spec i (cfg_model c) (Ok eff m' evs') /\ m_proc (cfg_model c') = m_proc m'.
Proof.
  intros segs cfg c evs c' H.
  inversion H; subst; cbn [cfg_ms cfg_model].
  - (* an instruction *)
    left.
    match goal with
    | Ha : mi_account_step _ _ _ = MachineOk _ |- _ =>
        destruct (mi_account_step_model_frame _ _ _ _ _ Ha)
          as (_ & _ & _ & _ & _ & Hp & _)
    end.
    exact Hp.
  - (* a vDSO call *)
    right.
    match goal with
    | Hsp : syscall_spec ?i _ (Ok ?eff ?m' ?ev),
      Hm : materialize_model_accesses ?m' _ = Some ?m'' |- _ =>
        exists i, eff, m', ev; split; [exact Hsp|];
        destruct (materialize_model_accesses_frame _ _ _ Hm)
          as (_ & _ & _ & _ & _ & Hp & _);
        transitivity (m_proc m''); [reflexivity | exact Hp]
    end.
  - (* a system call that returns *)
    right.
    match goal with
    | Hsp : syscall_spec ?i _ (Ok ?eff ?m' ?ev),
      Hm : materialize_model_accesses ?m' _ = Some ?m'' |- _ =>
        exists i, eff, m', ev; split; [exact Hsp|];
        destruct (materialize_model_accesses_frame _ _ _ Hm)
          as (_ & _ & _ & _ & _ & Hp & _);
        exact Hp
    end.
  - (* an exit *)
    right.
    match goal with
    | Hsp : syscall_spec ?i _ (Ok ?eff ?m' ?ev) |- _ =>
        exists i, eff, m', ev; split; [exact Hsp | reflexivity]
    end.
  - (* a kill *)
    right.
    match goal with
    | Hsp : syscall_spec ?i _ (Ok ?eff ?m' ?ev) |- _ =>
        exists i, eff, m', ev; split; [exact Hsp | reflexivity]
    end.
Qed.

(** THE STEP FACTS: a released step never clears the bit, never sets it
    in a process that has had a child, and keeps [hc_ok]. *)
Theorem sstep_sigchld_mono : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  m_sigchld_dfl (cfg_model c) = true ->
  m_sigchld_dfl (cfg_model c') = true.
Proof.
  intros segs cfg c evs c' H Hd.
  destruct (sstep_proc_cases _ _ _ _ _ H) as [Hp | (i & eff & m' & ev & Hsp & Hp)];
    unfold m_sigchld_dfl in *; rewrite Hp;
    [ exact Hd | exact (syscall_spec_sigchld_mono _ _ _ _ _ Hsp Hd) ].
Qed.

Theorem sstep_sigchld_no_set_with_children : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  m_has_children (cfg_model c) = true ->
  m_sigchld_dfl (cfg_model c) = false ->
  m_sigchld_dfl (cfg_model c') = false.
Proof.
  intros segs cfg c evs c' H Hc Hd.
  destruct (sstep_proc_cases _ _ _ _ _ H) as [Hp | (i & eff & m' & ev & Hsp & Hp)];
    unfold m_sigchld_dfl in *; rewrite Hp;
    [ exact Hd | exact (syscall_spec_sigchld_no_set_with_children _ _ _ _ _ Hsp Hc Hd) ].
Qed.

Theorem sstep_hc_ok : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  hc_ok (cfg_model c) -> hc_ok (cfg_model c').
Proof.
  intros segs cfg c evs c' H Hok.
  destruct (sstep_proc_cases _ _ _ _ _ H) as [Hp | (i & eff & m' & ev & Hsp & Hp)];
    unfold hc_ok, m_child_pids, m_has_children in *; rewrite Hp;
    [ exact Hok | exact (syscall_spec_hc_ok _ _ _ _ _ Hsp Hok) ].
Qed.
