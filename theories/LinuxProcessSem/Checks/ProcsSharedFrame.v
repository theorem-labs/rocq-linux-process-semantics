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

    - [syscall_spec_shared_grows]: every [Ok] outcome of the released spec
      at a class-(B) number keeps every path of [m_fs] present.  A [Forall]
      over [checked_table], as in [ProcsPrivateFrame].
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

(** A leaf of a checker walk: the post-model's file system is the old one,
    one [fs_set] over it, or [append_open_fs] of it, by conversion. *)
Ltac fs_leaf :=
  first
  [ exact (fs_grows_refl _)
  | eapply fs_grows_set
  | eapply fs_grows_append_open ].

Lemma check_efault_or_fs : forall fb eff m m' evs,
  check_efault_or fb eff m = CheckOk m' evs -> fs_grows (m_fs m) (m_fs m').
Proof. intros fb eff m m' evs H. unfold check_efault_or in H. repeat vm_step H; fs_leaf. Qed.

Lemma check_sigpipe_write_fs : forall eff m m' evs,
  check_sigpipe_write eff m = CheckOk m' evs -> fs_grows (m_fs m) (m_fs m').
Proof.
  intros eff m m' evs H. unfold check_sigpipe_write in H.
  apply check_ret_only_model in H; subst.
  unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); fs_leaf.
Qed.

Lemma check_sigpipe_writev_fs : forall reads eff m m' evs,
  check_sigpipe_writev reads eff m = CheckOk m' evs -> fs_grows (m_fs m) (m_fs m').
Proof.
  intros reads eff m m' evs H. unfold check_sigpipe_writev in H.
  apply check_ret_only_copyins_model in H; subst.
  unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); fs_leaf.
Qed.

Lemma check_open_result_fs : forall eff m mk m' evs,
  (forall fd, fs_grows (m_fs m) (m_fs (mk fd))) ->
  check_open_result eff m mk = CheckOk m' evs -> fs_grows (m_fs m) (m_fs m').
Proof.
  intros eff m mk m' evs Hmk H.
  unfold check_open_result, check_new_fd_result in H.
  repeat vm_step H; try apply Hmk; fs_leaf.
Qed.

Ltac fs_done H :=
  first
  [ apply check_efault_or_fs in H; exact H
  | apply check_sigpipe_write_fs in H; exact H
  | apply check_sigpipe_writev_fs in H; exact H
  | elim (check_readv_gap_sh _ _ H)
  | (eapply check_open_result_fs in H; [exact H | intros; fs_leaf]) ].

Ltac fs_frame H :=
  repeat (vm_step H || fs_done H); try fs_leaf.

Lemma check_ftruncate_fs : forall fd len eff m m' evs,
  check_ftruncate fd len eff m = CheckOk m' evs -> fs_grows (m_fs m) (m_fs m').
Proof.
  intros fd len eff m m' evs H. unfold check_ftruncate in H. fs_frame H.
Qed.

Lemma check_faccessat_fs : forall i dirfd pathp mode eff m m' evs,
  check_faccessat i dirfd pathp mode eff m = CheckOk m' evs ->
  fs_grows (m_fs m) (m_fs m').
Proof.
  intros i dirfd pathp mode eff m m' evs H.
  unfold check_faccessat, Open.check_faccessat_body, check_access_exists in H.
  fs_frame H.
Qed.

Lemma check_openat_fs : forall i dirfd pathp flags eff m m' evs,
  check_openat i dirfd pathp flags eff m = CheckOk m' evs ->
  fs_grows (m_fs m) (m_fs m').
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  (* openat's body and its copy-in wrapper are [Local] to
     [Checks/Sys/Fs/Open.v]; nothing they do reaches the address
     space, and naming them here is what lets [fs_frame] see that. *)
  unfold check_openat, Open.check_openat_body, Open.check_openat_resolved,
    Open.check_openat_sep, Open.check_openat_localtime,
    Open.check_openat_devnull, Open.check_open_devnull,
    Open.check_openat_urandom, Open.check_open_urandom,
    Open.check_openat_tmp,
    Open.check_openat_read, Open.check_openat_create, Open.check_openat_excl,
    Open.check_openat_dir, Open.check_openat_append,
    Open.check_openat_rdwr, Open.check_openat_rdwr_excl,
    Open.check_openat_proc, Open.check_proc_open_result,
    check_create_wronly, check_open_append, check_open_rdwr in H.
  fs_frame H.
Qed.

Lemma check_lseek_fs : forall fd off whence eff m m' evs,
  check_lseek fd off whence eff m = CheckOk m' evs -> fs_grows (m_fs m) (m_fs m').
Proof.
  intros fd off whence eff m m' evs H. unfold check_lseek in H. fs_frame H.
Qed.

Lemma check_read_fs : forall i fd buf count eff m m' evs,
  check_read i fd buf count eff m = CheckOk m' evs -> fs_grows (m_fs m) (m_fs m').
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_read, check_read_urandom, check_socket_pending_error,
    check_access_ok_zero, check_read_proc, check_read_proc_bare in H.
  cbv zeta in H. fs_frame H.
Qed.

Lemma check_write_fs : forall i fd buf count eff m m' evs,
  check_write i fd buf count eff m = CheckOk m' evs -> fs_grows (m_fs m) (m_fs m').
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_write, check_write_fault_extend, check_access_ok_zero in H.
  fs_frame H.
Qed.

Lemma check_readv_imported_fs : forall i fd r iovs0 eff m m' evs,
  check_readv_imported i fd r iovs0 eff m = CheckOk m' evs ->
  fs_grows (m_fs m) (m_fs m').
Proof.
  intros i fd r iovs0 eff m m' evs H.
  unfold check_readv_imported in H.
  fs_frame H.
Qed.

Lemma check_readv_fs : forall i fd iov iovcnt eff m m' evs,
  check_readv i fd iov iovcnt eff m = CheckOk m' evs ->
  fs_grows (m_fs m) (m_fs m').
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_readv in H.
  repeat (vm_step H || fs_done H
          || (apply check_readv_imported_fs in H; exact H));
  try fs_leaf.
Qed.

Lemma check_writev_fs : forall i fd iov iovcnt eff m m' evs,
  check_writev i fd iov iovcnt eff m = CheckOk m' evs ->
  fs_grows (m_fs m) (m_fs m').
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_writev, check_write_fault_extend in H. fs_frame H.
Qed.

Lemma check_pread64_fs : forall i fd buf count pos eff m m' evs,
  check_pread64 i fd buf count pos eff m = CheckOk m' evs ->
  fs_grows (m_fs m) (m_fs m').
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pread64, check_read_urandom in H. cbv zeta in H. fs_frame H.
Qed.

Lemma check_pwrite64_fs : forall i fd buf count pos eff m m' evs,
  check_pwrite64 i fd buf count pos eff m = CheckOk m' evs ->
  fs_grows (m_fs m) (m_fs m').
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pwrite64, check_write_fault_extend in H. fs_frame H.
Qed.

Lemma check_readlinkat_fs : forall i dirfd eff m m' evs,
  check_readlinkat i dirfd eff m = CheckOk m' evs -> fs_grows (m_fs m) (m_fs m').
Proof.
  intros i dirfd eff m m' evs H. unfold check_readlinkat in H. cbv zeta in H.
  fs_frame H.
Qed.

Lemma check_newfstatat_fs : forall i dirfd pathp flag eff m m' evs,
  check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs ->
  fs_grows (m_fs m) (m_fs m').
Proof.
  intros i dirfd pathp flag eff m m' evs H.
  unfold check_newfstatat, check_newfstatat_proc, check_newfstatat_proc_errno in H.
  fs_frame H.
Qed.

Lemma check_accept4_fs : forall fd addrp addrlenp flags eff m m' evs,
  check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs ->
  fs_grows (m_fs m) (m_fs m').
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
  fs_grows (m_fs m) (m_fs m').
Proof.
  intros i dirfd pathp mode flags eff m m' evs H.
  unfold check_faccessat2, Open.check_faccessat_body, check_access_exists in H.
  fs_frame H.
Qed.

(* =========================================================================
   Every class-(B) arm keeps every path
   ========================================================================= *)

Definition arm_shared_grows (c : CheckedArm) : Prop :=
  List.existsb (Z.eqb (ca_no c)) multiproc_shared_sysnos = true ->
  forall i eff m m' evs, ca_check c i eff m = CheckOk m' evs -> fs_grows (m_fs m) (m_fs m').

Lemma checked_table_shared_grows : Forall arm_shared_grows checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_shared_grows).
  all: unfold arm_shared_grows; intros Hp i eff m m' evs H.
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
      | fail 2 "checked_table_shared_grows has no case for this class-(B) arm: give its checker a *_fs lemma above and add it to the list" ] ].
Qed.

(** THE SPEC FACT: at a class-(B) number, every [Ok] outcome of the
    released spec keeps every path of the file system. *)
Theorem syscall_spec_shared_grows : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  List.existsb (Z.eqb (bv_unsigned (in_sysno i))) multiproc_shared_sysnos = true ->
  fs_grows (m_fs m) (m_fs m').
Proof.
  intros i m eff m' evs H Hp. apply check_syscall_ok_iff in H.
  unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_shared_grows as Hall. rewrite Forall_forall in Hall.
  refine (Hall c (lookup_ca_In _ _ _ Elk) _ i eff m m' evs H).
  rewrite (lookup_ca_no _ _ _ Elk). exact Hp.
Qed.

(** The released step at a class-(B) call keeps every path. *)
Lemma sstep_shared_grows : forall segs cfg c evs c',
  multiproc_shared c = true ->
  sstep_cfg segs cfg c evs (SNext c') -> fs_grows (m_fs (cfg_model c)) (m_fs (cfg_model c')).
Proof.
  intros segs cfg c evs c' Hp H.
  inversion H; subst; unfold multiproc_shared in Hp; cbn [cfg_ms cfg_model] in Hp |- *.
  all: match goal with
       | Hs : ms_svc_pending ?s = None |- _ => rewrite Hs in Hp; discriminate Hp
       | Hs : ms_svc_pending ?s = Some _ |- _ => rewrite Hs in Hp
       end.
  all: match goal with
       | Hsp : syscall_spec (sys_input _ _ _) _ (Ok _ _ _) |- _ =>
           pose proof (syscall_spec_shared_grows _ _ _ _ _ Hsp) as Hg;
           cbn [in_sysno sys_input] in Hg; specialize (Hg Hp)
       end.
  all: first
    [ exact Hg
    | match goal with
      | Hm : materialize_model_accesses _ _ = Some _ |- _ =>
          pose proof (sh_of_materialize _ _ _ Hm) as Hsh;
          unfold sh_of in Hsh; injection Hsh as Hf _;
          unfold m_fs; rewrite Hf; exact Hg
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
      | [ (Hwt & _) | [ (Hwo & _) | (Hsy & _ & _) ] ] ] ].
  - pose proof (sstep_shared_grows _ _ _ _ _ Hp Hs) as Hg.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split.
    + exact Hg.
    + intros q Hne. unfold look, absorb. cbn [pcfg_procs].
      rewrite orphan_at_exit_map, look_in_orphan, look_in_replace_other by exact Hne.
      destruct (look_in (pcfg_procs P) q) as [f|]; cbn [option_map];
        [apply orphan_slot_orphaned | exact I].
  - rewrite (shared_not_clone _ (clone_success_pending _ _ Hsucc)) in Hp. discriminate Hp.
  - rewrite (shared_not_intercept _ Hwt) in Hp. discriminate Hp.
  - rewrite (shared_not_owned _ _ Hwo) in Hp. discriminate Hp.
  - rewrite (shared_not_sync _ _ Hsy) in Hp. discriminate Hp.
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
      check_access_ok_zero, check_read_opaque, check_read_proc,
      check_read_proc_bare, check_read_eventfd, check_eventfd_deliver in H.
    efd_walk H Hfd. all: efd_keep H.
  - assert (Hc : check_syscall i eff m = ca_check arm_write i eff m)
      by (unfold check_syscall; rewrite E; reflexivity).
    rewrite Hc in H. autorewrite with arm_unfold in H.
    unfold check_write, check_write_fault_extend, check_access_ok_zero,
      check_write_opaque, check_write_eventfd in H.
    efd_walk H Hfd. all: efd_keep H.
Qed.
