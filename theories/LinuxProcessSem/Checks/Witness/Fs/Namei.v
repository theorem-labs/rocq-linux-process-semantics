(** * LinuxProcessSem.Checks.Witness.Fs.Namei — the mkdirat (34) and unlinkat (35) witnesses, and their proofs

    Mirrors [Sys/Fs/Namei.v], which answers to Linux [fs/namei.c]: this
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
  Prelude.

(** unlinkat and mkdirat witnesses: the deterministic errno arms, the
    fail-closed [Unmodeled], or — where the call could succeed — the
    injectable environment failure, which needs no model state.  On that
    arm the witness takes the [alt]'s LEFT branch, exactly as the openat
    witness does, so it never has to build the changed file system.  A
    type answer that admits earlier refusals beside it is witnessed by
    the type errno itself, the [alt]'s RIGHT branch. *)

(** Mirrors [Fs.Namei.unlinkat_file_spec] row for row. *)
Local Definition unlinkat_file_witness (r : Fs.Resolved) (lk : Fs.LastKind)
    (ts : bool) (m : Model) : outcome SyscallEffect :=
  match r with
  | Fs.RNotDir _ => ret_outcome (errno_ret ENOTDIR) m
  | Fs.RAbsent _ => ret_outcome (errno_ret ENOENT) m
  | Fs.RLoop => ret_outcome (errno_ret ELOOP) m
  | Fs.RParent _ _ => Unmodeled
  | Fs.ROutside => Unmodeled
  | Fs.RMissing _ _ =>
      match unlink_nonnorm_errno lk with
      | Some e => ret_outcome (errno_ret e) m
      | None => ret_outcome (errno_ret ENOENT) m
      end
  | Fs.RFound k e =>
      match unlink_nonnorm_errno lk with
      | Some er => ret_outcome (errno_ret er) m
      | None =>
          match e with
          | EDir => ret_outcome (errno_ret EISDIR) m
          | EDev _ => Unmodeled
          | EFile _ | ELink _ =>
              if ts then ret_outcome (errno_ret ENOTDIR) m
              else ret_outcome (errno_ret witness_errno) m
          end
      end
  end.

(** Mirrors [Fs.Namei.rmdir_spec] row for row. *)
Local Definition rmdir_witness (r : Fs.Resolved) (lk : Fs.LastKind)
    (m : Model) : outcome SyscallEffect :=
  match r with
  | Fs.RNotDir _ => ret_outcome (errno_ret ENOTDIR) m
  | Fs.RAbsent _ => ret_outcome (errno_ret ENOENT) m
  | Fs.RLoop => ret_outcome (errno_ret ELOOP) m
  | Fs.RParent _ _ => Unmodeled
  | Fs.ROutside => Unmodeled
  | Fs.RMissing _ _ =>
      match rmdir_nonnorm_errno lk with
      | Some e => ret_outcome (errno_ret e) m
      | None => ret_outcome (errno_ret ENOENT) m
      end
  | Fs.RFound k e =>
      match rmdir_nonnorm_errno lk with
      | Some er => ret_outcome (errno_ret er) m
      | None =>
          match e with
          | EFile _ | EDev _ | ELink _ => ret_outcome (errno_ret ENOTDIR) m
          | EDir =>
              if top_level_key k then Unmodeled
              else if path_eqb k (m_cwd m) then Unmodeled
              else if key_strictly_under k (m_cwd m) then Unmodeled
              else if fd_names_dir (m_fds m) k then Unmodeled
              else if negb (fs_dir_empty (m_fs m) k)
              then ret_outcome (errno_ret ENOTEMPTY) m
              else ret_outcome (errno_ret witness_errno) m
          end
      end
  end.

Local Definition unlinkat_body_witness (dirfd pathp flags : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match read_cstr (in_mem i) pathp with
  | CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m
  | CstrFault => ret_outcome (errno_ret EFAULT) m
  | CstrOk p =>
      if path_eqb p [] then ret_outcome (errno_ret ENOENT) m
      else if negb (bv_eqb dirfd AT_FDCWD32) then Unmodeled
      else
        let '(r, lk, ts) := Fs.resolve_parent (m_fs m) (m_cwd m) p in
        if unlink_rmdir flags then rmdir_witness r lk m
        else unlinkat_file_witness r lk ts m
  end.

(** The flag arm carries no copy-in — the kernel decides it before
    [getname()] — and every other arm carries the one pathname range
    [Fs.Namei.unlinkat_spec] records. *)
Definition unlinkat_witness (dirfd pathp flags : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (modeled_unlink_flags flags) then ret_outcome (errno_ret EINVAL) m
  else
    outcome_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
      (unlinkat_body_witness dirfd pathp flags i m).

(** mkdirat (34): the deterministic errnos, the declines, and the
    injectable failure on the one arm that creates. *)
Local Definition mkdirat_body_witness (dirfd pathp : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match read_cstr (in_mem i) pathp with
  | CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m
  | CstrFault => ret_outcome (errno_ret EFAULT) m
  | CstrOk p =>
      if path_eqb p [] then ret_outcome (errno_ret ENOENT) m
      else if negb (bv_eqb dirfd AT_FDCWD32) then Unmodeled
      else
        let '(r, lk, _) := Fs.resolve_parent (m_fs m) (m_cwd m) p in
        match r with
        | Fs.RNotDir _ => ret_outcome (errno_ret ENOTDIR) m
        | Fs.RAbsent _ => ret_outcome (errno_ret ENOENT) m
        | Fs.RLoop => ret_outcome (errno_ret ELOOP) m
        | Fs.RParent _ _ => Unmodeled
        | Fs.ROutside => Unmodeled
        | Fs.RFound _ _ =>
            match mkdir_nonnorm_errno lk with
            | Some e => ret_outcome (errno_ret e) m
            | None => ret_outcome (errno_ret EEXIST) m
            end
        | Fs.RMissing par _ =>
            match mkdir_nonnorm_errno lk with
            | Some e => ret_outcome (errno_ret e) m
            | None =>
                if Nat.ltb Fs.dir_count_max
                     (S (Fs.dl_counting (Fs.fs_dir_links (m_fs m) par)))
                then Unmodeled
                else ret_outcome (errno_ret witness_errno) m
            end
        end
  end.

Definition mkdirat_witness (dirfd pathp : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  outcome_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (mkdirat_body_witness dirfd pathp i m).

Local Lemma unlinkat_file_witness_ok : forall r lk ts i m,
  unlinkat_file_spec r lk ts m i m (unlinkat_file_witness r lk ts m).
Proof.
  intros r lk ts i m. unfold unlinkat_file_spec, unlinkat_file_witness.
  (* the prefix outcomes first, exactly as the arm reads them *)
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
    try apply pure_ok; try apply unmodeled_intro.
  - (* RFound: the kind switch, then the found cells *)
    destruct (unlink_nonnorm_errno lk); cbv iota; [apply pure_ok|].
    destruct e as [ino| |dk|body]; cbv iota;
      [ | destruct ts; apply alt_r; apply pure_ok | apply unmodeled_intro | ].
    all: destruct ts; cbv iota; [apply alt_r; apply pure_ok|].
    + unfold unlink_file_spec.
      apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
    + unfold unlink_remove_spec.
      apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
  - (* RMissing: the kind switch, then -ENOENT beside the earlier refusals *)
    destruct (unlink_nonnorm_errno lk); cbv iota; [apply pure_ok|].
    apply alt_r. apply pure_ok.
Qed.

Local Lemma rmdir_witness_ok : forall r lk i m,
  rmdir_spec r lk m i m (rmdir_witness r lk m).
Proof.
  intros r lk i m. unfold rmdir_spec, rmdir_witness.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
    try apply pure_ok; try apply unmodeled_intro.
  - destruct (rmdir_nonnorm_errno lk); cbv iota; [apply pure_ok|].
    destruct e as [ino| |dk|body]; cbv iota; try (apply alt_r; apply pure_ok).
    destruct (top_level_key k); cbv iota; [apply unmodeled_intro|].
    destruct (path_eqb k (m_cwd m)); cbv iota; [apply unmodeled_intro|].
    destruct (key_strictly_under k (m_cwd m)); cbv iota; [apply unmodeled_intro|].
    destruct (fd_names_dir (m_fds m) k); cbv iota; [apply unmodeled_intro|].
    destruct (negb (fs_dir_empty (m_fs m) k)); cbv iota;
      [apply alt_r; apply pure_ok|].
    apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
  - destruct (rmdir_nonnorm_errno lk); cbv iota; [apply pure_ok|].
    apply alt_r. apply pure_ok.
Qed.

Local Lemma unlinkat_body_witness_ok : forall dirfd pathp flags i m,
  unlinkat_body_spec dirfd pathp flags i m i m
    (unlinkat_body_witness dirfd pathp flags i m).
Proof.
  intros. unfold unlinkat_body_spec, unlinkat_body_witness.
  destruct (read_cstr (in_mem i) pathp) as [p| |];
    [|apply pure_ok|apply pure_ok].
  destruct (path_eqb p []); [apply pure_ok|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); [apply unmodeled_intro|].
  destruct (Fs.resolve_parent (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta.
  destruct (unlink_rmdir flags);
    [apply rmdir_witness_ok | apply unlinkat_file_witness_ok].
Qed.

Local Lemma mkdirat_body_witness_ok : forall dirfd pathp i m,
  mkdirat_body_spec dirfd pathp i m i m (mkdirat_body_witness dirfd pathp i m).
Proof.
  intros. unfold mkdirat_body_spec, mkdirat_body_witness.
  destruct (read_cstr (in_mem i) pathp) as [p| |];
    [|apply pure_ok|apply pure_ok].
  destruct (path_eqb p []); [apply pure_ok|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); [apply unmodeled_intro|].
  destruct (Fs.resolve_parent (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
    try apply pure_ok; try apply unmodeled_intro.
  - destruct (mkdir_nonnorm_errno lk); cbv iota; apply pure_ok.
  - destruct (mkdir_nonnorm_errno lk); cbv iota; [apply pure_ok|].
    destruct (Nat.ltb Fs.dir_count_max
                (S (Fs.dl_counting (Fs.fs_dir_links (m_fs m) par)))); cbv iota;
      [apply unmodeled_intro|].
    apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
Qed.

Lemma mkdirat_witness_ok : forall dirfd pathp i m,
  mkdirat_spec dirfd pathp i m (mkdirat_witness dirfd pathp i m).
Proof.
  intros. unfold mkdirat_spec, mkdirat_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  apply getname_refusals_intro.
  apply record_copyins_outcome. apply walk_refusals_intro. apply mkdirat_body_witness_ok.
Qed.

Lemma unlinkat_witness_ok : forall dirfd pathp flags i m,
  unlinkat_spec dirfd pathp flags i m (unlinkat_witness dirfd pathp flags i m).
Proof.
  intros. unfold unlinkat_spec, unlinkat_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota.
  destruct (negb (modeled_unlink_flags flags)) eqn:Hfl.
  { apply pure_ok. }
  apply getname_refusals_intro.
  apply record_copyins_outcome. apply walk_refusals_intro. apply unlinkat_body_witness_ok.
Qed.
