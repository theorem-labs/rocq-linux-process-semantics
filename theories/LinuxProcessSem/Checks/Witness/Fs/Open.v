(** * LinuxProcessSem.Checks.Witness.Fs.Open — the openat (56), close (57), ftruncate (46) witnesses, and their proofs

    Mirrors [Sys/Fs/Open.v], which answers to Linux [fs/open.c]: this
    file holds the witnesses for the syscalls defined there, and no
    others.

    Split out of [Checks/Progress.v], which keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from.

    Ported from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude Fs.ReadWrite.

(** THE INJECTABLE ERRNO IS AVAILABLE ON EVERY ARM THAT CAN SUCCEED,
    which is what lets these witnesses stay short: each such arm is an
    [alt] whose left branch is [openat_errnos], and ENOMEM heads that
    list, so the witness never has to build the changed file system or
    pick a descriptor number. *)
Local Lemma open_env_failure : forall (c : Sys SyscallEffect) i m,
  alt (e <- errno_from openat_errnos ;; err_ret e) c i m
      (ret_outcome (errno_ret witness_errno) m).
Proof.
  intros c i m. apply alt_l.
  eapply bind_step; [apply (errno_head_witness ENOMEM)|].
  unfold err_ret, ret_only, ret_outcome. apply pure_ok.
Qed.

(** A write open of an existing file stands beside its -ETXTBSY while
    no descriptor writes it ([Open.open_write_existing]), so the
    injectable errno is the right branch there, and the only branch
    while one does. *)
Local Ltac ow_split :=
  try (match goal with
       | |- context [ino_write_held ?a ?b] => destruct (ino_write_held a b); cbv beta iota
       end).
Local Ltac open_env := unfold open_write_existing, open_result_spec, create_wronly,
  open_append, open_rdwr; ow_split;
  first [ apply open_env_failure | apply alt_r; apply open_env_failure ].

(** A device row: the decline of a device entry away from its own name
    ([Open.dev_at_home]), else the injectable errno. *)
Local Definition dev_witness (k : Fs.path) (d : DevKind) (m : Model)
    : outcome SyscallEffect :=
  if negb (dev_at_home k d) then Unmodeled
  else ret_outcome (errno_ret witness_errno) m.

Local Lemma dev_witness_ok : forall k d rd wr i m,
  (match d with
   | DevNull => open_devnull k m rd wr
   | DevUrandom => open_urandom k m rd wr
   end) i m (dev_witness k d m).
Proof.
  intros k d rd wr i m. unfold dev_witness.
  destruct d; unfold open_devnull, open_urandom;
    (destruct (negb (dev_at_home k _)); [apply unmodeled_intro|open_env]).
Qed.

Local Ltac dev_env :=
  match goal with
  | |- open_devnull ?k ?m ?rd ?wr ?i ?m' _ =>
      exact (dev_witness_ok k DevNull rd wr i m)
  | |- open_urandom ?k ?m ?rd ?wr ?i ?m' _ =>
      exact (dev_witness_ok k DevUrandom rd wr i m)
  end.

(** Mirrors [Open.openat_read_spec] row for row. *)
Local Definition openat_read_witness (r : Fs.Resolved) (m : Model)
    : outcome SyscallEffect :=
  match r with
  | Fs.RFound k e =>
      match e with
      | EDev d => dev_witness k d m
      | EDir | EFile _ => ret_outcome (errno_ret witness_errno) m
      | ELink _ => ret_outcome (errno_ret ELOOP) m
      end
  | Fs.RMissing _ _ => ret_outcome (errno_ret ENOENT) m
  | Fs.RNotDir _ => ret_outcome (errno_ret ENOTDIR) m
  | Fs.RAbsent _ => ret_outcome (errno_ret ENOENT) m
  | Fs.RLoop => ret_outcome (errno_ret ELOOP) m
  | Fs.ROutside => Unmodeled
  | Fs.RParent _ _ => Unmodeled
  end.

Local Lemma openat_read_witness_ok : forall r i m,
  openat_read_spec r m i m (openat_read_witness r m).
Proof.
  intros r i m. unfold openat_read_spec, openat_read_witness.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
    try apply pure_ok; try apply unmodeled_intro.
  destruct e as [data| |dk|body]; cbv iota;
    [open_env|open_env|destruct dk; dev_env|apply pure_ok].
Qed.

(** Mirrors [Open.openat_create_spec] and, with [excl], the append
    shapes of [Open.openat_append_spec]: the rows are the clobbering
    shape's with a different descriptor kind. *)
Local Definition openat_create_witness (excl : bool) (r : Fs.Resolved)
    (m : Model) : outcome SyscallEffect :=
  match r with
  | Fs.RNotDir _ => ret_outcome (errno_ret ENOTDIR) m
  | Fs.RAbsent _ => ret_outcome (errno_ret ENOENT) m
  | Fs.RLoop => ret_outcome (errno_ret ELOOP) m
  | Fs.ROutside => Unmodeled
  | Fs.RParent _ _ => ret_outcome (errno_ret EISDIR) m
  | Fs.RMissing _ _ => ret_outcome (errno_ret witness_errno) m
  | Fs.RFound k e =>
      if excl then ret_outcome (errno_ret EEXIST) m
      else
        match e with
        | EDir => ret_outcome (errno_ret EISDIR) m
        | EFile _ => ret_outcome (errno_ret witness_errno) m
        | EDev d => dev_witness k d m
        | ELink _ => ret_outcome (errno_ret ELOOP) m
        end
  end.

Local Lemma openat_create_witness_ok : forall r i m,
  openat_create_spec r m i m (openat_create_witness false r m).
Proof.
  intros r i m. unfold openat_create_spec, openat_create_witness.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
    try apply pure_ok; try apply unmodeled_intro; [|open_env].
  destruct e as [data| |dk|body]; cbv iota;
    [open_env|apply pure_ok|destruct dk; dev_env|apply pure_ok].
Qed.

(** Mirrors [Open.openat_excl_spec] and [Open.openat_rdwr_excl_spec],
    which differ only in the descriptor kind the success branch would
    mint — and the witness never reaches that branch. *)
Local Definition openat_excl_witness (r : Fs.Resolved) (m : Model)
    : outcome SyscallEffect :=
  match r with
  | Fs.RNotDir _ => ret_outcome (errno_ret ENOTDIR) m
  | Fs.RAbsent _ => ret_outcome (errno_ret ENOENT) m
  | Fs.RLoop => ret_outcome (errno_ret ELOOP) m
  | Fs.ROutside => Unmodeled
  | Fs.RParent _ _ => ret_outcome (errno_ret EISDIR) m
  | Fs.RMissing _ _ => ret_outcome (errno_ret witness_errno) m
  | Fs.RFound _ _ => ret_outcome (errno_ret EEXIST) m
  end.

Local Lemma openat_excl_witness_ok : forall r i m,
  openat_excl_spec r m i m (openat_excl_witness r m).
Proof.
  intros r i m. unfold openat_excl_spec, openat_excl_witness.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
    first [apply pure_ok | apply unmodeled_intro | open_env].
Qed.

Local Lemma openat_rdwr_excl_witness_ok : forall r i m,
  openat_rdwr_excl_spec r m i m (openat_excl_witness r m).
Proof.
  intros r i m. unfold openat_rdwr_excl_spec, openat_excl_witness.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
    first [apply pure_ok | apply unmodeled_intro | open_env].
Qed.

Local Lemma openat_append_witness_ok : forall excl r i m,
  openat_append_spec excl r m i m (openat_create_witness excl r m).
Proof.
  intros excl r i m. unfold openat_append_spec, openat_create_witness.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
    try apply pure_ok; try apply unmodeled_intro; [|open_env].
  destruct excl; cbv iota; [apply pure_ok|].
  destruct e as [data| |dk|body]; cbv iota;
    [open_env|apply pure_ok|destruct dk; dev_env|apply pure_ok].
Qed.

(** Mirrors [Open.openat_rdwr_spec]. *)
Local Definition openat_rdwr_witness (creat trunc : bool) (r : Fs.Resolved)
    (m : Model) : outcome SyscallEffect :=
  match r with
  | Fs.RNotDir _ => ret_outcome (errno_ret ENOTDIR) m
  | Fs.RAbsent _ => ret_outcome (errno_ret ENOENT) m
  | Fs.RLoop => ret_outcome (errno_ret ELOOP) m
  | Fs.ROutside => Unmodeled
  | Fs.RParent _ _ => if creat then ret_outcome (errno_ret EISDIR) m else Unmodeled
  | Fs.RMissing _ _ =>
      if creat then ret_outcome (errno_ret witness_errno) m
      else ret_outcome (errno_ret ENOENT) m
  | Fs.RFound k e =>
      match e with
      | EDir => ret_outcome (errno_ret EISDIR) m
      | EFile _ => ret_outcome (errno_ret witness_errno) m
      | EDev d => dev_witness k d m
      | ELink _ => ret_outcome (errno_ret ELOOP) m
      end
  end.

Local Lemma openat_rdwr_witness_ok : forall creat trunc r i m,
  openat_rdwr_spec creat trunc r m i m (openat_rdwr_witness creat trunc r m).
Proof.
  intros creat trunc r i m.
  unfold openat_rdwr_spec, openat_rdwr_witness.
  destruct creat; destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
    try apply pure_ok; try apply unmodeled_intro;
    try (destruct e as [data| |dk|body]; cbv iota;
         [open_env|apply pure_ok|destruct dk; dev_env|apply pure_ok]);
    open_env.
Qed.

(** Mirrors [Open.openat_dir_spec]. *)
Local Definition openat_dir_witness (r : Fs.Resolved) (m : Model)
    : outcome SyscallEffect :=
  match r with
  | Fs.RFound _ EDir => ret_outcome (errno_ret witness_errno) m
  | Fs.RFound _ (EFile _) => ret_outcome (errno_ret ENOTDIR) m
  | Fs.RFound _ (EDev _) => ret_outcome (errno_ret ENOTDIR) m
  | Fs.RFound _ (ELink _) => ret_outcome (errno_ret ENOTDIR) m
  | Fs.RMissing _ _ => ret_outcome (errno_ret ENOENT) m
  | Fs.RNotDir _ => ret_outcome (errno_ret ENOTDIR) m
  | Fs.RAbsent _ => ret_outcome (errno_ret ENOENT) m
  | Fs.RLoop => ret_outcome (errno_ret ELOOP) m
  | Fs.ROutside => Unmodeled
  | Fs.RParent _ _ => Unmodeled
  end.

Local Lemma openat_dir_witness_ok : forall r i m,
  openat_dir_spec r m i m (openat_dir_witness r m).
Proof.
  intros r i m. unfold openat_dir_spec, openat_dir_witness.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
    try apply pure_ok; try apply unmodeled_intro.
  destruct e as [data| |dk|body]; cbv iota; try apply pure_ok;
    try apply unmodeled_intro.
  open_env.
Qed.

(** Mirrors [Open.openat_procfd_spec]: a reopen of a regular file takes
    the env-failure branch of each of its three words, so the witness
    builds no new descriptor. *)
Local Definition openat_procfd_witness (n flags : word) (m : Model)
    : outcome SyscallEffect :=
  let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
  if negb (Z.eqb fl 0 || Z.eqb fl wr_create_flags
           || Z.eqb fl append_create_flags)%bool then Unmodeled
  else
  match fd_lookup (m_fds m) n with
  | None => ret_outcome (errno_ret ENOENT) m
  | Some (FdFile _ _) | Some (FdFileW _ _) | Some (FdFileA _ _)
  | Some (FdFileRW _ _) => ret_outcome (errno_ret witness_errno) m
  | Some (FdChannel _) | Some (FdDir _)
  | Some (FdSocket _) | Some (FdPipe _ _) | Some (FdDevNull _ _)
  | Some (FdUrandom _ _) | Some (FdStream _ _ _) | Some (FdEventfd _)
  | Some (FdDgram _) => Unmodeled
  end.

Local Lemma openat_procfd_witness_ok : forall n flags i m,
  openat_procfd_spec n flags m i m (openat_procfd_witness n flags m).
Proof.
  intros n flags i m.
  unfold openat_procfd_spec, openat_procfd_witness, open_result_spec,
    open_write_existing, create_wronly, open_append. cbv zeta.
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0
                  || Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                       wr_create_flags
                  || Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                       append_create_flags)%bool);
    [apply unmodeled_intro|].
  destruct (fd_lookup (m_fds m) n)
    as [[ch|q cur|q cur|q cur|q cur|k|sk|pid pw|rd wr|urd uwr|sid side st|ctx|fam]|];
    try apply unmodeled_intro; try apply pure_ok.
  all: destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
      [|destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                    wr_create_flags)];
      ow_split; first [ apply open_env_failure | apply alt_r; apply open_env_failure ].
Qed.

(** Mirrors [File.unused_fd_none_spec]: the -EMFILE where it is forced,
    the decline above it. *)
Local Definition unused_fd_none_witness (m : Model) : outcome SyscallEffect :=
  if (bv_unsigned (m_nofile m) <=? bv_unsigned (alloc_fd (m_fds m)) + 1)%Z
  then ret_outcome (errno_ret EMFILE) m
  else Unmodeled.

Local Definition openat_core_witness (dirfd pathp flags : word)
    (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if negb (modeled_open_flags flags) then Unmodeled  (* unmodeled flag combination *)
  else if openat_name_fetched i pathp && lowest_fd_none (m_fds m)
  then unused_fd_none_witness m                      (* no free descriptor *)
  else match read_cstr (in_mem i) pathp with
       | CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m  (* over-long path *)
       | CstrFault => ret_outcome (errno_ret EFAULT) m          (* unreadable path *)
       | CstrOk p =>
           if path_eqb p [] then ret_outcome (errno_ret ENOENT) m  (* empty pathname *)
           else if negb (bv_eqb dirfd AT_FDCWD32) then Unmodeled   (* unmodeled dirfd *)
           else
             match proc_self_fd p with
             | Some n => openat_procfd_witness n flags m
             | None =>
             let '(r, _, _) := Fs.resolve (open_walk_mode flags) (m_fs m) (m_cwd m) p in
             let fl := open_shape flags in
             if Z.eqb fl 0 then openat_read_witness r m
             else if Z.eqb fl wr_create_flags then openat_create_witness false r m
             else if is_excl_create fl then openat_excl_witness r m
             else if Z.eqb fl O_DIRECTORY then openat_dir_witness r m
             else if Z.eqb fl append_create_flags then openat_create_witness false r m
             else if rdwr_open_word fl then
               openat_rdwr_witness (flag_set fl O_CREAT) (flag_set fl O_TRUNC) r m
             else if is_rdwr_excl_create fl then openat_excl_witness r m
             else if is_excl_append_create fl then openat_create_witness true r m
             else Unmodeled   (* unreachable: [modeled_open_flags flags] holds *)
             end
       end.

Definition openat_witness (dirfd pathp flags : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  outcome_copyins
    [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (openat_core_witness dirfd pathp flags i m).

Local Lemma openat_core_witness_ok : forall dirfd pathp flags i m,
  openat_core_spec dirfd pathp flags i m
    (openat_core_witness dirfd pathp flags i m).
Proof.
  intros. unfold openat_core_spec, openat_core_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (negb (modeled_open_flags flags)) eqn:Hfl; cbv iota;
    [apply unmodeled_intro|].
  destruct (openat_name_fetched i pathp && lowest_fd_none (m_fds m)); cbv iota.
  { unfold unused_fd_none_spec, unused_fd_none_witness.
    destruct (bv_unsigned (m_nofile m) <=? bv_unsigned (alloc_fd (m_fds m)) + 1)%Z;
      cbv iota; [apply pure_ok | apply unmodeled_intro]. }
  apply walk_refusals_intro. unfold openat_body_spec.
  destruct (read_cstr (in_mem i) pathp) as [p| |] eqn:Hp; cbv iota;
    [|apply pure_ok|apply pure_ok].
  destruct (path_eqb p []) eqn:Hpe; cbv iota; [apply pure_ok|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; cbv iota;
    [apply unmodeled_intro|].
  unfold openat_resolved_spec.
  destruct (proc_self_fd p) as [n|]; [apply openat_procfd_witness_ok|].
  destruct (Fs.resolve (open_walk_mode flags) (m_fs m) (m_cwd m) p)
    as [[r lk] ts] eqn:Hr.
  cbv iota zeta.
  destruct (Z.eqb (open_shape flags) 0); cbv iota; [apply openat_read_witness_ok|].
  destruct (Z.eqb (open_shape flags) wr_create_flags); cbv iota;
    [apply openat_create_witness_ok|].
  destruct (is_excl_create (open_shape flags)); cbv iota;
    [apply openat_excl_witness_ok|].
  destruct (Z.eqb (open_shape flags) O_DIRECTORY); cbv iota;
    [apply openat_dir_witness_ok|].
  destruct (Z.eqb (open_shape flags) append_create_flags); cbv iota;
    [apply openat_append_witness_ok|].
  destruct (rdwr_open_word (open_shape flags)); cbv iota;
    [apply openat_rdwr_witness_ok|].
  destruct (is_rdwr_excl_create (open_shape flags)); cbv iota;
    [apply openat_rdwr_excl_witness_ok|].
  destruct (is_excl_append_create (open_shape flags)); cbv iota;
    [apply openat_append_witness_ok|apply unmodeled_intro].
Qed.

Lemma openat_witness_ok : forall dirfd pathp flags i m,
  openat_spec dirfd pathp flags i m (openat_witness dirfd pathp flags i m).
Proof.
  intros. unfold openat_spec, openat_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  apply getname_refusals_intro.
  apply record_copyins_outcome. apply openat_core_witness_ok.
Qed.

(* =========================================================================
   close (57) — deterministic: remove the fd or -EBADF
   ========================================================================= *)

Definition close_witness (fd : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some _ => ret_outcome (Z_to_bv 64 0) (with_fds (fd_remove (m_fds m) fd) m)
  end.

Lemma close_witness_ok : forall fd i m, close_spec fd i m (close_witness fd m).
Proof.
  intros. unfold close_spec, close_witness.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  - eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. eapply bind_step; [apply modify_ok|]. apply pure_ok.
  - eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
Qed.

(* =========================================================================
   ftruncate (46)
   ========================================================================= *)

Definition ftruncate_witness (fd len : word) (m : Model)
    : outcome SyscallEffect :=
  if (bv_signed len <? 0)%Z then ret_outcome (errno_ret EINVAL) m
  else
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdChannel _) => ret_outcome (errno_ret EINVAL) m
  | Some (FdSocket _) => ret_outcome (errno_ret EINVAL) m  (* S_ISSOCK, not S_ISREG *)
  | Some (FdStream _ _ _) => ret_outcome (errno_ret EINVAL) m  (* S_ISSOCK too *)
  | Some (FdDgram _) => ret_outcome (errno_ret EINVAL) m  (* and a datagram socket *)
  | Some (FdEventfd _) => ret_outcome (errno_ret EINVAL) m  (* no type bits: not S_ISREG *)
  | Some (FdPipe _ _) => ret_outcome (errno_ret EINVAL) m  (* S_IFIFO, not S_ISREG *)
  | Some (FdDevNull _ _) => ret_outcome (errno_ret EINVAL) m  (* S_IFCHR, not S_ISREG *)
  | Some (FdUrandom _ _) => ret_outcome (errno_ret EINVAL) m  (* S_IFCHR again *)
  | Some (FdFile _ _) => ret_outcome (errno_ret EINVAL) m
  | Some (FdDir _) => ret_outcome (errno_ret EINVAL) m
  | Some (FdFileA p _) | Some (FdFileW p _) | Some (FdFileRW p _) =>
      (* a writable regular file: see [Open.ftruncate_spec] *)
      let data := Fs.fs_ino_data (m_fs m) p in
      if negb (modeled_truncate_gap data len) then Unmodeled
      else ret_outcome (Z_to_bv 64 0)
             (with_fs (Fs.fs_set_ino_data (m_fs m) p (file_truncate data len)) m)
  end.

Lemma ftruncate_witness_ok : forall fd len i m,
  ftruncate_spec fd len i m (ftruncate_witness fd len m).
Proof.
  intros. unfold ftruncate_spec, ftruncate_witness.
  destruct ((bv_signed len <? 0)%Z) eqn:Hneg; [apply pure_ok|].
  destruct (fd_lookup (m_fds m) fd) as [[ch|p cur|p cur|p cur|p cur|k|sk|pid pw|rd wr|urd uwr|id side st|ctx|fam]|] eqn:Hfd;
    try (eapply bind_step; [apply get_model_ok|];
         cbv beta iota; srw Hfd; apply pure_ok).
  all: destruct (negb (modeled_truncate_gap (Fs.fs_ino_data (m_fs m) p) len)) eqn:Hgap;
       [ eapply bind_step; [apply get_model_ok|];
         cbv beta iota; srw Hfd; srw Hgap; apply unmodeled_intro
       | eapply bind_step; [apply get_model_ok|];
         cbv beta iota; srw Hfd; srw Hgap;
         eapply bind_step; [apply modify_ok|]; apply pure_ok ].
Qed.

(** faccessat witness: the deterministic errno arms, the fail-closed
    [Unmodeled] (a device among them), or — where the path resolves to
    anything else — plain SUCCESS.  That is
    the [alt]'s RIGHT branch, unlike the openat and unlinkat witnesses
    which take the injectable-errno branch to avoid building a new model
    state.  Nothing has to be built here: faccessat changes no state, so
    both alternatives return the same model and the success one is the
    outcome a real run actually produces. *)
Local Definition faccessat_body_witness (md : Fs.WalkMode) (dirfd pathp : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match read_cstr (in_mem i) pathp with
  | CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m
  | CstrFault => ret_outcome (errno_ret EFAULT) m
  | CstrOk p =>
      if path_eqb p [] then ret_outcome (errno_ret ENOENT) m
      else if negb (bv_eqb dirfd AT_FDCWD32) then Unmodeled
      else
        let '(r, _, _) := Fs.resolve md (m_fs m) (m_cwd m) p in
        match r with
        | Fs.RFound _ (Fs.EDev _) => Unmodeled
        | Fs.RFound _ _ => ret_outcome (Z_to_bv 64 0) m
        | Fs.RMissing _ _ => ret_outcome (errno_ret ENOENT) m
        | Fs.RNotDir _ => ret_outcome (errno_ret ENOTDIR) m
        | Fs.RAbsent _ => ret_outcome (errno_ret ENOENT) m
        | Fs.RLoop => ret_outcome (errno_ret ELOOP) m
        | Fs.ROutside => Unmodeled
        | Fs.RParent _ _ => Unmodeled
        end
  end.

(** Both mode arms carry no copy-in — the kernel decides the mode before
    [user_path_at] — and every other arm carries the one pathname range
    [Fs.Open.faccessat_spec] records. *)
Definition faccessat_witness (dirfd pathp mode : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (modeled_access_mode mode) then ret_outcome (errno_ret EINVAL) m
  else if negb (access_mode_f_ok mode) then Unmodeled
  else
    outcome_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
      (faccessat_body_witness (Fs.WalkFull true false) dirfd pathp i m).

Local Lemma faccessat_body_witness_ok : forall md dirfd pathp i m,
  faccessat_body_spec md dirfd pathp i m i m
    (faccessat_body_witness md dirfd pathp i m).
Proof.
  intros. unfold faccessat_body_spec, faccessat_body_witness.
  destruct (read_cstr (in_mem i) pathp) as [p| |];
    [|apply pure_ok|apply pure_ok].
  destruct (path_eqb p []); [apply pure_ok|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); [apply unmodeled_intro|].
  destruct (Fs.resolve md (m_fs m) (m_cwd m) p) as [[r lk] ts]; cbv iota beta zeta.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
    try apply pure_ok; try apply unmodeled_intro.
  destruct e; cbv iota; try apply unmodeled_intro;
    unfold access_exists_spec; apply pure_ok.
Qed.

Lemma faccessat_witness_ok : forall dirfd pathp mode i m,
  faccessat_spec dirfd pathp mode i m (faccessat_witness dirfd pathp mode i m).
Proof.
  intros. unfold faccessat_spec, faccessat_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota.
  destruct (negb (modeled_access_mode mode)); [apply pure_ok|].
  destruct (negb (access_mode_f_ok mode)); [apply unmodeled_intro|].
  apply getname_refusals_intro.
  apply record_copyins_outcome. apply walk_refusals_intro. apply faccessat_body_witness_ok.
Qed.

(** faccessat2's witness is faccessat's, under one more -EINVAL and one
    more decline: [do_faccessat] is the shared body, so past the flag
    word there is nothing new to build. *)
Definition faccessat2_witness (dirfd pathp mode flags : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if negb (modeled_access_mode mode) then ret_outcome (errno_ret EINVAL) m
  else if negb (valid_access_flags flags) then ret_outcome (errno_ret EINVAL) m
  else if negb (modeled_access_flags flags) then Unmodeled
  else if negb (access_mode_f_ok mode) then Unmodeled
  else
    outcome_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
      (faccessat_body_witness (access_walk_mode flags) dirfd pathp i m).

Lemma faccessat2_witness_ok : forall dirfd pathp mode flags i m,
  faccessat2_spec dirfd pathp mode flags i m
    (faccessat2_witness dirfd pathp mode flags i m).
Proof.
  intros. unfold faccessat2_spec, faccessat2_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota.
  destruct (negb (modeled_access_mode mode)); [apply pure_ok|].
  destruct (negb (valid_access_flags flags)); [apply pure_ok|].
  destruct (negb (modeled_access_flags flags)); [apply unmodeled_intro|].
  destruct (negb (access_mode_f_ok mode)); [apply unmodeled_intro|].
  apply getname_refusals_intro.
  apply record_copyins_outcome. apply walk_refusals_intro. apply faccessat_body_witness_ok.
Qed.
