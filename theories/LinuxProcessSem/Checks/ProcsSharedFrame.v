(** * LinuxProcessSem.Checks.ProcsSharedFrame — a class-(B) call keeps every peer's references valid

    Not part of the trusted specification: QA on [Procs.multiproc_shared_sysnos],
    in the sense of [Checks.Examples]'s header, under its first reason: the
    statements are universally quantified over configurations and steps.

    ** What this pins

    [Procs.multiproc_allowed] admits the class-(B) numbers while another
    entry lives.  They change [m_fsys] or [m_io], which every entry sees, so
    the argument is not that nothing changes but that nothing another entry
    HOLDS goes stale.  What a peer holds that names the file system is a
    file descriptor of the four file kinds (a path and an offset of its own)
    and a stat pin keyed by path; nothing it holds names [m_io].  Both stay
    valid because the file system only grows.

    - [syscall_spec_shared_frame]: every [Ok] outcome of the released spec
      at a class-(B) number keeps every path of [m_fs] and the caller's tid.
      A [Forall] over [checked_table], as in [ProcsPrivateFrame].
    - [pstep_at_shared_frame]: a [pstep_at] step of entry [p] with a
      class-(B) call pending keeps [pcfg_root], [sh_ofd], [sh_pipes] and
      [sh_ns]; the new [sh_fsys] keeps every path of the old; every other
      entry is unchanged but for the orphaning when the step halted [p]
      (write and writev can kill the caller by SIGPIPE).
    - [pstep_at_shared_consistent]: so another entry whose file descriptors
      all named files of the file system still does after the step, with
      the same machine state and model; only the two spliced slots it sees
      changed.  [pstep_x_at_shared_frame]: the frame under [ext_agrees].
    - [eventfd_declined] and [eventfd_rw_keeps_model]: Linux has ONE
      counter per eventfd, however many processes hold it.  At ftruncate,
      lseek, readv, writev, pread64 and pwrite64 (46, 62, 65-68), with an
      eventfd at the descriptor, every [Ok] answer leaves the model alone,
      emits nothing, writes no user memory and returns an errno.  [read]
      and [write] (63, 64) answer a non-blocking eventfd with no counter
      in the model at all (the counter is the environment's), and every
      [Ok] answer leaves the model alone and emits nothing.  A counter in
      the model must move into [shared] first; an arm that keeps one per
      process breaks these lemmas, which is the point. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs VmMapsDisjoint ProcsWellFormed ProcsPrivateFrame.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude DispatchCompute.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(* =========================================================================
   A file system that only grows
   ========================================================================= *)

(** Every path of [fs] is a path of [fs']. *)
Definition fs_grows (fs fs' : Fs.Fs) : Prop :=
  forall k d, fs_lookup fs k = Some d -> exists d', fs_lookup fs' k = Some d'.

Lemma fs_grows_refl : forall fs, fs_grows fs fs.
Proof. intros fs k d H. exists d. exact H. Qed.

Lemma fs_grows_trans : forall a b c, fs_grows a b -> fs_grows b c -> fs_grows a c.
Proof.
  intros a b c Hab Hbc k d H. destruct (Hab k d H) as (d1 & H1). exact (Hbc k d1 H1).
Qed.

(** Insert or replace keeps every path. *)
Lemma fs_grows_set : forall fs p d, fs_grows fs (fs_set fs p d).
Proof.
  induction fs as [|[q e] r IH]; intros p d k x H; cbn [fs_lookup] in H; [discriminate H|].
  cbn [fs_set].
  destruct (path_ltb p q).
  - cbn [fs_lookup]. destruct (path_eqb k p); [eexists; reflexivity|].
    rewrite H. eexists; reflexivity.
  - destruct (path_eqb p q) eqn:Epq.
    + apply path_eqb_eq in Epq. subst q. cbn [fs_lookup].
      destruct (path_eqb k p) eqn:Ekp; [eexists; reflexivity|]. rewrite H. eexists; reflexivity.
    + cbn [fs_lookup]. destruct (path_eqb k q); [eexists; reflexivity|].
      exact (IH p d k x H).
Qed.

Lemma fs_grows_append_open : forall fs p, fs_grows fs (append_open_fs fs p).
Proof.
  intros fs p. unfold append_open_fs.
  destruct (fs_lookup fs p); [apply fs_grows_refl | apply fs_grows_set].
Qed.


(** Shared calls may grow the file system, but do not first-pin a tid. *)
Definition fs_tid_frame (m m' : Model) : Prop :=
  fs_grows (m_fs m) (m_fs m') /\ m_tid m' = m_tid m.

(** A checker leaf keeps the tid, and keeps every path by conversion or
    by one [fs_set] or [append_open_fs]. *)
Ltac fs_leaf :=
  unfold fs_tid_frame; split;
    [ first [exact (fs_grows_refl _) | eapply fs_grows_set | eapply fs_grows_append_open]
    | reflexivity ].

Lemma check_efault_or_fs : forall fb eff m m' evs,
  check_efault_or fb eff m = CheckOk m' evs -> fs_tid_frame m m'.
Proof. intros fb eff m m' evs H. unfold check_efault_or in H. repeat vm_step H; fs_leaf. Qed.

Lemma check_sigpipe_write_fs : forall eff m m' evs,
  check_sigpipe_write eff m = CheckOk m' evs -> fs_tid_frame m m'.
Proof.
  intros eff m m' evs H. unfold check_sigpipe_write in H.
  destruct (sigpipe_declines m); cbv iota in H; [discriminate H|].
  apply check_ret_only_model in H; subst.
  unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); fs_leaf.
Qed.

Lemma check_sigpipe_writev_fs : forall reads eff m m' evs,
  check_sigpipe_writev reads eff m = CheckOk m' evs -> fs_tid_frame m m'.
Proof.
  intros reads eff m m' evs H. unfold check_sigpipe_writev in H.
  destruct (sigpipe_declines m); cbv iota in H; [discriminate H|].
  apply check_ret_only_copyins_model in H; subst.
  unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); fs_leaf.
Qed.

Lemma check_open_result_fs : forall eff m mk m' evs,
  (forall fd, fs_tid_frame m (mk fd)) ->
  check_open_result eff m mk = CheckOk m' evs -> fs_tid_frame m m'.
Proof.
  intros eff m mk m' evs Hmk H.
  unfold check_open_result, check_new_fd_result in H.
  repeat vm_step H; try apply Hmk; fs_leaf.
Qed.

Lemma check_write_open_result_fs : forall eff m mk m' evs,
  (forall fd, fs_tid_frame m (mk fd)) ->
  check_write_open_result eff m mk = CheckOk m' evs -> fs_tid_frame m m'.
Proof.
  intros eff m mk m' evs Hmk H.
  unfold check_write_open_result, check_new_fd_result in H.
  repeat vm_step H; try apply Hmk; fs_leaf.
Qed.

Lemma check_write_open_create_result_fs : forall eff m mk m' evs,
  (forall fd, fs_tid_frame m (mk fd)) ->
  check_write_open_create_result eff m mk = CheckOk m' evs -> fs_tid_frame m m'.
Proof.
  intros eff m mk m' evs Hmk H.
  unfold check_write_open_create_result, check_new_fd_result in H.
  repeat vm_step H; try apply Hmk; fs_leaf.
Qed.

Ltac fs_done H :=
  first
  [ apply check_efault_or_fs in H; exact H
  | apply check_sigpipe_write_fs in H; exact H
  | apply check_sigpipe_writev_fs in H; exact H
  | elim (check_readv_gap_sh _ _ H)
  | (eapply check_open_result_fs in H; [exact H | intros; fs_leaf])
  | (eapply check_write_open_result_fs in H; [exact H | intros; fs_leaf])
  | (eapply check_write_open_create_result_fs in H; [exact H | intros; fs_leaf]) ].

Ltac fs_frame H :=
  repeat (vm_step H || fs_done H); try fs_leaf.

(** READ'S AND WRITE'S HELPERS, as [Checks.VmMapsDisjoint] proves them
    for the address space and [Checks.ProcsChildPidsFrame] for the child
    lists, one lemma each: a stream-pair end's read and send, the
    /proc/sys file, the eventfd, the unnamed file and the write-fault
    extension.  Each closes its own step, so the frame lemmas of [read],
    [write], [pwrite64], [readv] and [writev] close these calls by name.
    None of them writes the file system: the stream ends and the unnamed
    file live in the descriptor table. *)
Lemma check_stream_read_empty_fs : forall fd id side st nonblock eff m m' evs,
  check_stream_read_empty fd id side st nonblock eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros fd id side st nonblock eff m m' evs H.
  unfold check_stream_read_empty, check_stream_read_reset in H. fs_frame H.
Qed.

Lemma check_stream_read_fs :
  forall fd id side st nonblock buf count i eff m m' evs,
  check_stream_read fd id side st nonblock buf count i eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros fd id side st nonblock buf count i eff m m' evs H.
  unfold check_stream_read, check_stream_read_empty, check_stream_read_reset in H.
  cbv beta zeta in H. fs_frame H.
Qed.

Lemma check_stream_send_fs :
  forall id side st nonblock nosignal n src ledger eff m m' evs,
  check_stream_send id side st nonblock nosignal n src ledger eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros id side st nonblock nosignal n src ledger eff m m' evs H.
  unfold check_stream_send in H. cbv beta zeta in H. fs_frame H.
Qed.

Lemma check_stream_write_fs :
  forall id side st nonblock nosignal buf count i eff m m' evs,
  check_stream_write id side st nonblock nosignal buf count i eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros id side st nonblock nosignal buf count i eff m m' evs H.
  unfold check_stream_write in H. eapply check_stream_send_fs. exact H.
Qed.

Ltac fs_stream H :=
  first
  [ apply check_stream_read_fs in H; exact H
  | apply check_stream_read_empty_fs in H; exact H
  | apply check_stream_write_fs in H; exact H
  | apply check_stream_send_fs in H; exact H ].

Ltac fs_frame3 H :=
  repeat (vm_step H || fs_done H || fs_stream H); try fs_leaf.

Lemma fs_read_urandom : forall i buf count eff m m' evs,
  check_read_urandom i buf count eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros i buf count eff m m' evs H. unfold check_read_urandom, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fs_done H);
  try fs_leaf.
Qed.

Lemma fs_socket_pending_error : forall e fd peer ch buf count i eff m m' evs,
  check_socket_pending_error e fd peer ch buf count i eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros e fd peer ch buf count i eff m m' evs H.
  unfold check_socket_pending_error, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fs_done H);
  try fs_leaf.
Qed.

Lemma fs_write_fault_extend : forall reads m p off eff m' evs,
  check_write_fault_extend reads m p off eff = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros reads m p off eff m' evs H. unfold check_write_fault_extend, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fs_done H);
  try fs_leaf.
Qed.

Lemma fs_read_proc : forall i buf count eff m m' evs,
  check_read_proc i buf count eff m = CheckOk m' evs -> fs_tid_frame m m'.
Proof.
  intros i buf count eff m m' evs H.
  unfold check_read_proc, check_read_proc_bare in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fs_done H);
  try fs_leaf.
Qed.

Lemma fs_eventfd_read : forall fd ctx buf count i eff m m' evs,
  check_eventfd_read fd ctx buf count i eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros fd ctx buf count i eff m m' evs H. unfold check_eventfd_read in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fs_done H);
  try fs_leaf.
Qed.

Lemma fs_eventfd_write : forall fd ctx buf count i eff m m' evs,
  check_eventfd_write fd ctx buf count i eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros fd ctx buf count i eff m m' evs H. unfold check_eventfd_write in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fs_done H);
  try fs_leaf.
Qed.

Lemma fs_anon_fault_extend : forall reads m id data dst eff m' evs,
  check_anon_fault_extend reads m id data dst eff = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros reads m id data dst eff m' evs H. unfold check_anon_fault_extend in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fs_done H);
  try fs_leaf.
Qed.

Lemma fs_anon_write_fault : forall reads m id af eff m' evs,
  check_anon_write_fault reads m id af eff = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros reads m id af eff m' evs H. unfold check_anon_write_fault in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fs_done H
          || (eapply fs_anon_fault_extend in H; exact H));
  try fs_leaf.
Qed.

Lemma check_ftruncate_fs : forall fd len eff m m' evs,
  check_ftruncate fd len eff m = CheckOk m' evs -> fs_tid_frame m m'.
Proof.
  intros fd len eff m m' evs H. unfold check_ftruncate in H. fs_frame H.
Qed.

Lemma check_faccessat_fs : forall i dirfd pathp mode eff m m' evs,
  check_faccessat i dirfd pathp mode eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros i dirfd pathp mode eff m m' evs H.
  unfold check_faccessat, Open.check_faccessat_body, check_access_exists in H.
  fs_frame H.
Qed.

(** OPENAT, ONE SUB-CHECKER AT A TIME.  Unfolding the whole of
    [check_openat] at once multiplies every guard of every arm into
    one case split; each lemma below unfolds one level and closes
    the calls below it by their lemmas. *)
Lemma openat_read_fs : forall p eff m m' evs,
  Open.check_openat_read p eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_read in H. cbv zeta in H.
  repeat (vm_step H || fs_done H); try fs_leaf.
Qed.

Lemma openat_create_fs : forall p eff m m' evs,
  Open.check_openat_create p eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_create, check_create_wronly in H. cbv zeta in H.
  repeat (vm_step H || fs_done H); try fs_leaf.
Qed.

Lemma openat_append_fs : forall excl p eff m m' evs,
  Open.check_openat_append excl p eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros excl p eff m m' evs H.
  unfold Open.check_openat_append, check_open_append in H. cbv zeta in H.
  repeat (vm_step H || fs_done H); try fs_leaf.
Qed.

Lemma openat_rdwr_fs : forall creat trunc p eff m m' evs,
  Open.check_openat_rdwr creat trunc p eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros creat trunc p eff m m' evs H.
  unfold Open.check_openat_rdwr, check_open_rdwr in H. cbv zeta in H.
  repeat (vm_step H || fs_done H); try fs_leaf.
Qed.

Lemma openat_rdwr_excl_fs : forall p eff m m' evs,
  Open.check_openat_rdwr_excl p eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_rdwr_excl, check_open_rdwr in H. cbv zeta in H.
  repeat (vm_step H || fs_done H); try fs_leaf.
Qed.

Lemma openat_excl_fs : forall p eff m m' evs,
  Open.check_openat_excl p eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_excl, check_create_wronly in H. cbv zeta in H.
  repeat (vm_step H || fs_done H); try fs_leaf.
Qed.

Lemma openat_dir_fs : forall p eff m m' evs,
  Open.check_openat_dir p eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros p eff m m' evs H.
  unfold Open.check_openat_dir in H. cbv zeta in H.
  repeat (vm_step H || fs_done H); try fs_leaf.
Qed.

Lemma openat_localtime_fs : forall flags eff m m' evs,
  Open.check_openat_localtime flags eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros flags eff m m' evs H.
  unfold Open.check_openat_localtime in H. cbv zeta in H.
  repeat (vm_step H || fs_done H); try fs_leaf.
Qed.

Lemma openat_devnull_fs : forall flags eff m m' evs,
  Open.check_openat_devnull flags eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros flags eff m m' evs H.
  unfold Open.check_openat_devnull, Open.check_open_devnull in H. cbv zeta in H.
  repeat (vm_step H || fs_done H); try fs_leaf.
Qed.

Lemma openat_urandom_fs : forall flags eff m m' evs,
  Open.check_openat_urandom flags eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros flags eff m m' evs H.
  unfold Open.check_openat_urandom, Open.check_open_urandom in H. cbv zeta in H.
  repeat (vm_step H || fs_done H); try fs_leaf.
Qed.

Lemma openat_proc_result_fs : forall o eff m m' evs,
  Open.check_proc_open_result o eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros o eff m m' evs H.
  unfold Open.check_proc_open_result in H. cbv zeta in H.
  repeat (vm_step H || fs_done H); try fs_leaf.
Qed.

Local Ltac openat_sub_fs_tmp H :=
  lazymatch type of H with
  | Open.check_openat_read _ _ _ = CheckOk _ _ => apply openat_read_fs in H; exact H
  | Open.check_openat_create _ _ _ = CheckOk _ _ => apply openat_create_fs in H; exact H
  | Open.check_openat_rdwr_excl _ _ _ = CheckOk _ _ => apply openat_rdwr_excl_fs in H; exact H
  end.

Lemma openat_tmp_fs : forall n p flags eff m m' evs,
  Open.check_openat_tmp n p flags eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros n p flags eff m m' evs H.
  unfold Open.check_openat_tmp in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_fs_tmp H || fs_done H); try fs_leaf.
Qed.

Local Ltac openat_sub_fs_sep H :=
  lazymatch type of H with
  | Open.check_openat_localtime _ _ _ = CheckOk _ _ => apply openat_localtime_fs in H; exact H
  | Open.check_openat_devnull _ _ _ = CheckOk _ _ => apply openat_devnull_fs in H; exact H
  | Open.check_openat_urandom _ _ _ = CheckOk _ _ => apply openat_urandom_fs in H; exact H
  | Open.check_openat_tmp _ _ _ _ _ = CheckOk _ _ => apply openat_tmp_fs in H; exact H
  end.

Lemma openat_sep_fs : forall p flags eff m m' evs,
  Open.check_openat_sep p flags eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros p flags eff m m' evs H.
  unfold Open.check_openat_sep in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_fs_sep H || fs_done H); try fs_leaf.
Qed.

Local Ltac openat_sub_fs_resolved H :=
  lazymatch type of H with
  | Open.check_openat_read _ _ _ = CheckOk _ _ => apply openat_read_fs in H; exact H
  | Open.check_openat_create _ _ _ = CheckOk _ _ => apply openat_create_fs in H; exact H
  | Open.check_openat_excl _ _ _ = CheckOk _ _ => apply openat_excl_fs in H; exact H
  | Open.check_openat_dir _ _ _ = CheckOk _ _ => apply openat_dir_fs in H; exact H
  | Open.check_openat_append _ _ _ _ = CheckOk _ _ => apply openat_append_fs in H; exact H
  | Open.check_openat_rdwr _ _ _ _ _ = CheckOk _ _ => apply openat_rdwr_fs in H; exact H
  | Open.check_openat_rdwr_excl _ _ _ = CheckOk _ _ => apply openat_rdwr_excl_fs in H; exact H
  | Open.check_openat_sep _ _ _ _ = CheckOk _ _ => apply openat_sep_fs in H; exact H
  end.

Lemma openat_resolved_fs : forall p flags eff m m' evs,
  Open.check_openat_resolved p flags eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros p flags eff m m' evs H.
  unfold Open.check_openat_resolved in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_fs_resolved H || fs_done H); try fs_leaf.
Qed.

(** The "/proc/self/fd/N" reopen installs a descriptor with [with_fds]
    and nothing else. *)
Lemma openat_procfd_fs : forall n flags eff m m' evs,
  Open.check_openat_procfd n flags eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros n flags eff m m' evs H.
  unfold Open.check_openat_procfd in H. cbv beta iota zeta in H.
  repeat (vm_step H || fs_done H); try fs_leaf.
Qed.

Local Ltac openat_sub_fs_proc H :=
  lazymatch type of H with
  | Open.check_proc_open_result _ _ _ = CheckOk _ _ => apply openat_proc_result_fs in H; exact H
  | Open.check_openat_procfd _ _ _ _ = CheckOk _ _ => apply openat_procfd_fs in H; exact H
  end.

Lemma openat_proc_fs : forall c flags eff m m' evs,
  Open.check_openat_proc c flags eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros c flags eff m m' evs H.
  unfold Open.check_openat_proc in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_fs_proc H || fs_done H); try fs_leaf.
Qed.

Local Ltac openat_sub_fs_body H :=
  lazymatch type of H with
  | Open.check_openat_proc _ _ _ _ = CheckOk _ _ => apply openat_proc_fs in H; exact H
  | Open.check_openat_resolved _ _ _ _ = CheckOk _ _ => apply openat_resolved_fs in H; exact H
  end.

Lemma openat_body_fs : forall i dirfd pathp flags eff m m' evs,
  Open.check_openat_body i dirfd pathp flags eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold Open.check_openat_body in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_fs_body H || fs_done H); try fs_leaf.
Qed.

Local Ltac openat_sub_fs_top H :=
  lazymatch type of H with
  | Open.check_openat_body _ _ _ _ _ _ = CheckOk _ _ => apply openat_body_fs in H; exact H
  end.

Lemma check_openat_table_fs : forall i dirfd pathp flags eff m m' evs,
  check_openat_table i dirfd pathp flags eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_openat_table in H. cbv zeta in H.
  repeat (vm_step H || openat_sub_fs_top H || fs_done H); try fs_leaf.
Qed.

(** The close-on-exec step writes [State.m_cloexec] alone. *)
Lemma check_openat_fs : forall i dirfd pathp flags eff m m' evs,
  check_openat i dirfd pathp flags eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H. unfold check_openat in H.
  destruct (check_openat_table i dirfd pathp flags eff m) as [m0 evs0| |] eqn:E;
    try discriminate H.
  injection H as <- <-. apply check_openat_table_fs in E.
  unfold open_cloexec_model. destruct (addr_is_error_b (eff_ret eff)); [exact E|].
  destruct (fd_lookup (m_fds m0) (eff_ret eff)); exact E.
Qed.

Lemma check_lseek_fs : forall fd off whence eff m m' evs,
  check_lseek fd off whence eff m = CheckOk m' evs -> fs_tid_frame m m'.
Proof.
  intros fd off whence eff m m' evs H. unfold check_lseek in H. fs_frame H.
Qed.

Lemma check_read_fs : forall i fd buf count eff m m' evs,
  check_read i fd buf count eff m = CheckOk m' evs -> fs_tid_frame m m'.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_read, check_read_file_data, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fs_done H || fs_stream H
          || (apply check_read_opaque_keeps in H; destruct H as [-> ->])
          || (eapply fs_read_urandom in H; exact H)
          || (eapply fs_socket_pending_error in H; exact H)
          || (eapply fs_read_proc in H; exact H)
          || (eapply fs_eventfd_read in H; exact H));
  try fs_leaf.
Qed.

Lemma check_write_fs : forall i fd buf count eff m m' evs,
  check_write i fd buf count eff m = CheckOk m' evs -> fs_tid_frame m m'.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_write, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fs_done H || fs_stream H
          || (apply check_write_opaque_keeps in H; destruct H as [-> ->])
          || (eapply fs_write_fault_extend in H; exact H)
          || (eapply fs_eventfd_write in H; exact H)
          || (eapply fs_anon_write_fault in H; exact H));
  try fs_leaf.
Qed.

Lemma check_readv_imported_fs : forall i fd r iovs0 eff m m' evs,
  check_readv_imported i fd r iovs0 eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros i fd r iovs0 eff m m' evs H.
  unfold check_readv_imported in H.
  fs_frame3 H.
Qed.

Lemma check_readv_fs : forall i fd iov iovcnt eff m m' evs,
  check_readv i fd iov iovcnt eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_readv in H.
  repeat (vm_step H || fs_done H
          || (apply check_readv_imported_fs in H; exact H));
  try fs_leaf.
Qed.

Lemma check_writev_fs : forall i fd iov iovcnt eff m m' evs,
  check_writev i fd iov iovcnt eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_writev in H. cbv beta iota zeta in H.
  repeat (vm_step H || fs_done H || fs_stream H
          || (eapply fs_write_fault_extend in H; exact H)
          || (eapply fs_anon_write_fault in H; exact H));
  try fs_leaf.
Qed.

Lemma check_pread64_fs : forall i fd buf count pos eff m m' evs,
  check_pread64 i fd buf count pos eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pread64, check_read_urandom in H. cbv zeta in H. fs_frame H.
Qed.

Lemma check_pwrite64_fs : forall i fd buf count pos eff m m' evs,
  check_pwrite64 i fd buf count pos eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pwrite64 in H. cbv beta iota zeta in H.
  repeat (vm_step H || fs_done H
          || (eapply fs_write_fault_extend in H; exact H)
          || (eapply fs_anon_fault_extend in H; exact H));
  try fs_leaf.
Qed.

Lemma check_readlinkat_fs : forall i dirfd eff m m' evs,
  check_readlinkat i dirfd eff m = CheckOk m' evs -> fs_tid_frame m m'.
Proof.
  intros i dirfd eff m m' evs H. unfold check_readlinkat in H. cbv zeta in H.
  fs_frame H.
Qed.

Lemma check_newfstatat_fs : forall i dirfd pathp flag eff m m' evs,
  check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros i dirfd pathp flag eff m m' evs H.
  unfold check_newfstatat, check_newfstatat_proc, check_newfstatat_proc_errno in H.
  fs_frame H.
Qed.

Lemma check_accept4_fs : forall fd addrp addrlenp flags eff m m' evs,
  check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros fd addrp addrlenp flags eff m m' evs H.
  (* [check_errno_only] is unfolded alongside, the way
     [check_read_fs] unfolds [check_access_ok_zero]: it is the arm
     [check_accept4] takes once [Net.Socket.conn_ix_exhausted] holds, and
     [vm_step] sees no [if] or [match] through a folded definition, so
     without the unfold that branch leaves an open goal. *)
  unfold check_accept4, check_new_fd_result, check_errno_or_success,
    check_errno_only, check_errno_or_list in H. fs_frame H.
Qed.

Lemma check_faccessat2_fs : forall i dirfd pathp mode flags eff m m' evs,
  check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs ->
  fs_tid_frame m m'.
Proof.
  intros i dirfd pathp mode flags eff m m' evs H.
  unfold check_faccessat2, Open.check_faccessat_body, check_access_exists in H.
  fs_frame H.
Qed.

(* =========================================================================
   Every class-(B) arm keeps every path
   ========================================================================= *)

Definition arm_shared_frame (c : CheckedArm) : Prop :=
  List.existsb (Z.eqb (ca_no c)) multiproc_shared_sysnos = true ->
  forall i eff m m' evs, ca_check c i eff m = CheckOk m' evs -> fs_tid_frame m m'.

Lemma checked_table_shared_frame : Forall arm_shared_frame checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_shared_frame).
  all: unfold arm_shared_frame; intros Hp i eff m m' evs H.
  all: first
    [ exfalso; clear H; vm_compute in Hp; discriminate Hp
    | autorewrite with arm_unfold in H;
      first
      [
        eapply check_ftruncate_fs; eassumption
        | eapply check_faccessat_fs; eassumption
        | eapply check_openat_fs; eassumption
        | eapply check_lseek_fs; eassumption
        | eapply check_read_fs; eassumption
        | eapply check_write_fs; eassumption
        | eapply check_readv_fs; eassumption
        | eapply check_writev_fs; eassumption
        | eapply check_pread64_fs; eassumption
        | eapply check_pwrite64_fs; eassumption
        | eapply check_readlinkat_fs; eassumption
        | eapply check_newfstatat_fs; eassumption
        | eapply check_accept4_fs; eassumption
        | eapply check_faccessat2_fs; eassumption
      | fail 2 "checked_table_shared_frame has no case for this class-(B) arm: give its checker a *_fs lemma above and add it to the list" ] ].
Qed.

(** At a class-(B) number, every [Ok] outcome of the released spec keeps
    every path and the caller's tid. *)
Theorem syscall_spec_shared_frame : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  List.existsb (Z.eqb (bv_unsigned (in_sysno i))) multiproc_shared_sysnos = true ->
  fs_tid_frame m m'.
Proof.
  intros i m eff m' evs H Hp. apply check_syscall_ok_iff in H.
  unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_shared_frame as Hall. rewrite Forall_forall in Hall.
  refine (Hall c (lookup_ca_In _ _ _ Elk) _ i eff m m' evs H).
  rewrite (lookup_ca_no _ _ _ Elk). exact Hp.
Qed.

(** The released class-(B) step keeps every path and the caller's tid. *)
Lemma sstep_shared_frame : forall segs cfg c evs c',
  multiproc_shared c = true ->
  sstep_cfg segs cfg c evs (SNext c') -> fs_tid_frame (cfg_model c) (cfg_model c').
Proof.
  intros segs cfg c evs c' Hp H.
  inversion H; subst; unfold multiproc_shared in Hp; cbn [cfg_ms cfg_model] in Hp |- *.
  all: match goal with
       | Hs : ms_svc_pending ?s = None |- _ => rewrite Hs in Hp; discriminate Hp
       | Hs : ms_svc_pending ?s = Some _ |- _ => rewrite Hs in Hp
       end.
  all: match goal with
       | Hsp : syscall_spec (sys_input _ _ _) _ (Ok _ _ _) |- _ =>
           pose proof (syscall_spec_shared_frame _ _ _ _ _ Hsp) as Hg;
           cbn [in_sysno sys_input] in Hg; specialize (Hg Hp)
       end.
  all: first
    [ exact Hg
    | match goal with
      | Hm : materialize_model_accesses _ _ = Some _ |- _ =>
          pose proof (sh_of_materialize _ _ _ Hm) as Hsh;
          pose proof (f_equal fst Hsh) as Hf;
          pose proof (f_equal (fun x => snd (snd x)) Hsh) as Ht;
          cbn [sh_of fst snd] in Hf, Ht;
          unfold fs_tid_frame, m_fs in Hg |- *; rewrite Hf, Ht; exact Hg
      end ].
Qed.

(* =========================================================================
   The step frame
   ========================================================================= *)

Lemma shared_not_clone : forall c,
  clone_pending_b c = true -> multiproc_shared c = false.
Proof.
  intros c H. unfold clone_pending_b, clone_sysno in H. unfold multiproc_shared.
  destruct (ms_svc_pending (cfg_ms c)) as [x8|]; [|discriminate H].
  apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H; rewrite H; reflexivity.
Qed.

Lemma shared_not_intercept : forall c,
  wait4_intercept_b c = true -> multiproc_shared c = false.
Proof.
  intros c H. unfold wait4_intercept_b in H. unfold multiproc_shared.
  destruct (ms_svc_pending (cfg_ms c)) as [x8|]; [|discriminate H].
  apply andb_true_iff in H as [H _]. apply Z.eqb_eq in H. rewrite H. reflexivity.
Qed.

Lemma shared_not_owned : forall P e,
  wait4_owned_b P e = true -> multiproc_shared (pe_cfg (pcfg_shared P) e) = false.
Proof.
  intros P e H. destruct (wait4_owned_260 P e H) as (x8 & Hs & H260).
  unfold multiproc_shared. cbn [cfg_ms pe_cfg]. rewrite Hs, H260. reflexivity.
Qed.

Lemma shared_not_pin : forall P e,
  root_pin_pending_b P e = true -> multiproc_shared (pe_cfg (pcfg_shared P) e) = false.
Proof.
  intros P e H. unfold root_pin_pending_b in H. unfold multiproc_shared.
  cbn [cfg_ms pe_cfg]. destruct (ms_svc_pending (pe_ms e)) as [x8|]; [|discriminate H].
  destruct (Z.eqb (bv_unsigned x8) 173) eqn:E; [|discriminate H].
  apply Z.eqb_eq in E. rewrite E. reflexivity.
Qed.

Lemma shared_not_sync : forall P e,
  sync_pending_b P e = true -> multiproc_shared (pe_cfg (pcfg_shared P) e) = false.
Proof.
  intros P e H. destruct (sync_pending_sysno _ _ H) as (x8 & Hs & Hin).
  unfold multiproc_shared. cbn [cfg_ms pe_cfg]. rewrite Hs.
  cbn [multiproc_synced_sysnos List.existsb] in Hin.
  repeat (apply orb_true_iff in Hin as [E|Hin];
          [apply Z.eqb_eq in E; rewrite E; reflexivity|]).
  discriminate Hin.
Qed.

(** THE FRAME.  A step of [p] at a class-(B) call keeps the root and the
    three shared tables it does not splice, lets the file system only grow,
    and keeps every other entry but for the orphaning of [p]'s children
    when the step halted [p]. *)
Theorem pstep_at_shared_frame : forall segs cfg p P evs P' e,
  look P p = Some e ->
  multiproc_shared (pe_cfg (pcfg_shared P) e) = true ->
  pstep_at segs cfg p P evs (PNext P') ->
  pcfg_root P' = pcfg_root P
  /\ sh_ofd (pcfg_shared P') = sh_ofd (pcfg_shared P)
  /\ sh_pipes (pcfg_shared P') = sh_pipes (pcfg_shared P)
  /\ sh_ns (pcfg_shared P') = sh_ns (pcfg_shared P)
  /\ fs_grows (fsst_image (sh_fsys (pcfg_shared P))) (fsst_image (sh_fsys (pcfg_shared P')))
  /\ (forall q, q <> p ->
        match look P q, look P' q with
        | None, None => True
        | Some f, Some f' => orphaned_or_same p f f'
        | _, _ => False
        end).
Proof.
  intros segs cfg p P evs P' e Hl Hp H.
  destruct (pstep_next_cases _ _ _ _ _ _ H) as (e1 & Hl1 & Hpid & Hcases).
  rewrite Hl in Hl1. injection Hl1 as <-. subst p.
  destruct Hcases as
    [ (c' & Hs & _ & _ & ->)
    | [ (c' & q & _ & Hsucc & _)
      | [ (Hwt & _) | [ (Hwo & _) | [ (Hsy & _ & _) | (Hrp & _ & _) ] ] ] ] ].
  - destruct (sstep_shared_frame _ _ _ _ _ Hp Hs) as (Hg & Htid).
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split.
    + exact Hg.
    + intros q Hne. unfold look, absorb. cbn [pcfg_procs].
      rewrite first_root_pin_children_same_tid by exact Htid.
      rewrite orphan_at_exit_map, look_in_orphan, look_in_replace_other by exact Hne.
      destruct (look_in (pcfg_procs P) q) as [f|]; cbn [option_map];
        [apply orphan_slot_orphaned | exact I].
  - rewrite (shared_not_clone _ (clone_success_pending _ _ Hsucc)) in Hp. discriminate Hp.
  - rewrite (shared_not_intercept _ Hwt) in Hp. discriminate Hp.
  - rewrite (shared_not_owned _ _ Hwo) in Hp. discriminate Hp.
  - rewrite (shared_not_sync _ _ Hsy) in Hp. discriminate Hp.
  - rewrite (shared_not_pin _ _ Hrp) in Hp. discriminate Hp.
Qed.

(** The path a file descriptor names, for the four kinds that name one. *)
Definition fd_file_path (ent : FdEntry) : option path :=
  match ent with
  | FdFile p _ | FdFileW p _ | FdFileA p _ | FdFileRW p _ => Some p
  | _ => None
  end.

(** Every file descriptor of the entry names a file of [fs]. *)
Definition fds_in_fs (fs : Fs.Fs) (f : ProcessEntry) : Prop :=
  forall fd ent p,
    fd_lookup (m_fds (pe_model f)) fd = Some ent -> fd_file_path ent = Some p ->
    exists d, fs_lookup fs p = Some d.

(** THE CONSISTENCY.  Another entry keeps its machine state and model, and
    if its file descriptors all named files before the step they all do
    after it: no reference a peer holds into the file system goes stale. *)
Corollary pstep_at_shared_consistent : forall segs cfg p P evs P' e q f,
  look P p = Some e ->
  multiproc_shared (pe_cfg (pcfg_shared P) e) = true ->
  pstep_at segs cfg p P evs (PNext P') ->
  q <> p -> look P q = Some f ->
  fds_in_fs (fsst_image (sh_fsys (pcfg_shared P))) f ->
  exists f', look P' q = Some f'
    /\ pe_ms f' = pe_ms f /\ pe_model f' = pe_model f
    /\ fds_in_fs (fsst_image (sh_fsys (pcfg_shared P'))) f'.
Proof.
  intros segs cfg p P evs P' e q f Hl Hp H Hne Hf Hin.
  destruct (pstep_at_shared_frame segs cfg p P evs P' e Hl Hp H)
    as (_ & _ & _ & _ & Hg & Hq).
  specialize (Hq q Hne). rewrite Hf in Hq.
  destruct (look P' q) as [f'|]; [|contradiction].
  assert (Hms : pe_ms f' = pe_ms f /\ pe_model f' = pe_model f)
    by (destruct Hq as [-> | (_ & ->)]; split; reflexivity).
  destruct Hms as [Hms Hmo].
  exists f'. split; [reflexivity|]. split; [exact Hms|]. split; [exact Hmo|].
  intros fd ent pth Hfd Hpath. rewrite Hmo in Hfd.
  destruct (Hin fd ent pth Hfd Hpath) as (d & Hd).
  exact (Hg pth d Hd).
Qed.

(** The extended relation, wherever it agrees with the core's. *)
Corollary pstep_x_at_shared_frame : forall ext cenv segs cfg p P evs P' e,
  ext_agrees ext cenv segs P ->
  look P p = Some e ->
  multiproc_shared (pe_cfg (pcfg_shared P) e) = true ->
  pstep_x_at ext cenv segs cfg p P evs (PNext P') ->
  pcfg_root P' = pcfg_root P
  /\ sh_ofd (pcfg_shared P') = sh_ofd (pcfg_shared P)
  /\ sh_pipes (pcfg_shared P') = sh_pipes (pcfg_shared P)
  /\ sh_ns (pcfg_shared P') = sh_ns (pcfg_shared P)
  /\ fs_grows (fsst_image (sh_fsys (pcfg_shared P))) (fsst_image (sh_fsys (pcfg_shared P')))
  /\ (forall q, q <> p ->
        match look P q, look P' q with
        | None, None => True
        | Some f, Some f' => orphaned_or_same p f f'
        | _, _ => False
        end).
Proof.
  intros ext cenv segs cfg p P evs P' e Hag Hl Hp H.
  apply (pstep_at_shared_frame segs cfg p P evs P' e Hl Hp).
  exact (proj1 (pstep_x_at_agree_iff ext cenv segs cfg p P evs (PNext P') Hag) H).
Qed.

(* =========================================================================
   The eventfd copy: no class-(B) arm answers from it
   ========================================================================= *)

(** The class-(B) numbers whose argument 0 is a descriptor they read or
    write and which DECLINE an eventfd: ftruncate, lseek, readv, writev,
    pread64, pwrite64.  [read] (63) and [write] (64) answer a non-blocking
    eventfd ([eventfd_rw_keeps_model] below). *)
Definition eventfd_io_sysnos : list Z := [46; 62; 65; 66; 67; 68]%Z.

(** An answer that is an argument errno and nothing else. *)
Definition errno_only (m : Model) (eff : SyscallEffect) (m' : Model) (evs : list event)
    : Prop :=
  m' = m /\ evs = [] /\ eff_writes eff = [] /\ addr_is_error_b (eff_ret eff) = true.

Local Ltac efd_walk H Hfd :=
  cbv beta iota zeta in H; rewrite Hfd in H;
  try (unfold readable_fd in H);
  repeat (cbv beta iota zeta in H;
          lazymatch type of H with
          | CheckOk _ _ = CheckOk _ _ => fail
          | _ => match type of H with
                 | context [match ?x with _ => _ end] => destruct x
                 | context [if ?b then _ else _] => destruct b
                 end
          end);
  try discriminate H.

Local Ltac efd_leaf H :=
  first
  [ apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->)
  | apply check_ret_only_copyins_ok_iff in H; destruct H as (-> & -> & ->) ];
  unfold errno_only; repeat split; vm_compute; reflexivity.

(** THE PIN.  With an eventfd at the descriptor, every [Ok] answer of these
    arms is an errno that changes nothing: the arms decline the descriptor
    ([unmodeled]) and answer only argument checks taken before its kind is
    read. *)
Theorem eventfd_declined : forall i m eff m' evs f,
  List.In (bv_unsigned (in_sysno i)) eventfd_io_sysnos ->
  fd_lookup (m_fds m) (fd32 (in_arg i 0)) = Some (FdOpaque (OEventFd f)) ->
  syscall_spec i m (Ok eff m' evs) ->
  errno_only m eff m' evs.
Proof.
  intros i m eff m' evs f Hin Hfd H. apply check_syscall_ok_iff in H.
  cbn [eventfd_io_sysnos List.In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; symmetry in E.
  - assert (Hc : check_syscall i eff m = ca_check arm_ftruncate i eff m)
      by (unfold check_syscall; rewrite E; reflexivity).
    rewrite Hc in H. autorewrite with arm_unfold in H.
    unfold check_ftruncate in H. efd_walk H Hfd. all: efd_leaf H.
  - assert (Hc : check_syscall i eff m = ca_check arm_lseek i eff m)
      by (unfold check_syscall; rewrite E; reflexivity).
    rewrite Hc in H. autorewrite with arm_unfold in H.
    unfold check_lseek in H. efd_walk H Hfd. all: efd_leaf H.
  - assert (Hc : check_syscall i eff m = ca_check arm_readv i eff m)
      by (unfold check_syscall; rewrite E; reflexivity).
    rewrite Hc in H. autorewrite with arm_unfold in H.
    unfold check_readv in H. efd_walk H Hfd. all: efd_leaf H.
  - assert (Hc : check_syscall i eff m = ca_check arm_writev i eff m)
      by (unfold check_syscall; rewrite E; reflexivity).
    rewrite Hc in H. autorewrite with arm_unfold in H.
    unfold check_writev in H. efd_walk H Hfd. all: efd_leaf H.
  - assert (Hc : check_syscall i eff m = ca_check arm_pread64 i eff m)
      by (unfold check_syscall; rewrite E; reflexivity).
    rewrite Hc in H. autorewrite with arm_unfold in H.
    unfold check_pread64 in H. efd_walk H Hfd. all: efd_leaf H.
  - assert (Hc : check_syscall i eff m = ca_check arm_pwrite64 i eff m)
      by (unfold check_syscall; rewrite E; reflexivity).
    rewrite Hc in H. autorewrite with arm_unfold in H.
    unfold check_pwrite64 in H. efd_walk H Hfd. all: efd_leaf H.
Qed.

Local Ltac efd_keep H :=
  repeat (cbv beta iota zeta in H;
          lazymatch type of H with
          | CheckOk _ _ = CheckOk _ _ => fail
          | check_ret_only _ _ _ _ = CheckOk _ _ => fail
          | check_ret_only_copyins _ _ _ _ _ = CheckOk _ _ => fail
          | _ => match type of H with
                 | context [match ?x with _ => _ end] => destruct x
                 | context [if ?b then _ else _] => destruct b
                 end
          end);
  first
  [ discriminate H
  | injection H as <- <-; split; reflexivity
  | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
    split; reflexivity
  | apply check_ret_only_copyins_ok_iff in H; destruct H as (-> & -> & ->);
    split; reflexivity ].

(** READ AND WRITE ON AN EVENTFD keep the model.  [read] (63) and [write]
    (64) answer a non-blocking eventfd ([Fs.ReadWrite.read_eventfd_spec],
    [Fs.ReadWrite.write_eventfd_spec]) without a counter: the counter is
    the ENVIRONMENT's, so a read returns any value the kernel could hold
    and a write any answer it could give, and a peer's write is one more
    environment write.  Every [Ok] answer leaves the model as it was and
    emits nothing, so nothing per process can drift from the counter
    Linux has once.  A counter in the model must go into the shared state
    ([Procs.shared]) first; such a change breaks this lemma. *)
Theorem eventfd_rw_keeps_model : forall i m eff m' evs f,
  (bv_unsigned (in_sysno i) = 63%Z \/ bv_unsigned (in_sysno i) = 64%Z) ->
  fd_lookup (m_fds m) (fd32 (in_arg i 0)) = Some (FdOpaque (OEventFd f)) ->
  syscall_spec i m (Ok eff m' evs) ->
  m' = m /\ evs = [].
Proof.
  intros i m eff m' evs f [E|E] Hfd H; apply check_syscall_ok_iff in H.
  - assert (Hc : check_syscall i eff m = ca_check arm_read i eff m)
      by (unfold check_syscall; rewrite E; reflexivity).
    rewrite Hc in H. autorewrite with arm_unfold in H.
    unfold check_read, check_read_urandom, check_socket_pending_error,
      check_access_ok_zero in H.
    efd_walk H Hfd.
    all: first [ exact (check_read_opaque_keeps _ _ _ _ _ _ _ _ H) | efd_keep H ].
  - assert (Hc : check_syscall i eff m = ca_check arm_write i eff m)
      by (unfold check_syscall; rewrite E; reflexivity).
    rewrite Hc in H. autorewrite with arm_unfold in H.
    unfold check_write, check_write_fault_extend, check_access_ok_zero in H.
    efd_walk H Hfd.
    all: first [ exact (check_write_opaque_keeps _ _ _ _ _ _ _ _ H) | efd_keep H ].
Qed.
