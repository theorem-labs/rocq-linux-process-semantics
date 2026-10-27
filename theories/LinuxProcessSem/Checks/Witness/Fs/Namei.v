(** * LinuxProcessSem.Checks.Witness.Fs.Namei — the unlinkat (35) witness, and its proof

    Mirrors [Sys/Fs/Namei.v], which answers to Linux [fs/namei.c]: this
    file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude.

(** unlinkat witness: the deterministic errno arms, the fail-closed
    [Unmodeled], or — where the removal could succeed — the injectable
    environment failure, which needs no model state.  On that arm the
    witness takes the [alt]'s LEFT branch, exactly as the openat witness
    does, so it never has to build the removed file system. *)
(** Mirrors [Fs.Namei.unlink_found_spec]: the removal is witnessed by
    the [alt]'s LEFT branch, so the witness never builds the removed
    file system. *)
Local Definition unlink_found_witness (p c : path) (flags : word) (m : Model)
    : outcome SyscallEffect :=
  if unlink_rmdir flags then ret_outcome (errno_ret ENOTDIR) m
  else if path_trailing_slash p then ret_outcome (errno_ret ENOTDIR) m
  else if fd_names_path (m_fds m) c then Unmodeled
  else ret_outcome (errno_ret witness_errno) m.

(** Mirrors [Fs.Namei.unlinkat_tmp_spec]. *)
Local Definition unlinkat_tmp_witness (n p c : path) (flags : word) (m : Model)
    : outcome SyscallEffect :=
  if unlink_rmdir flags then Unmodeled
  else if Nat.ltb NAME_MAX (length n) then Unmodeled
  else if fs_under (m_fs m) c then ret_outcome (errno_ret EISDIR) m
  else
    match fs_lookup (m_fs m) c with
    | None => ret_outcome (errno_ret ENOENT) m
    | Some _ => unlink_found_witness p c flags m
    end.

Local Definition unlinkat_body_witness (dirfd pathp flags : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match user_read_cstr i m pathp with
       | UOk CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m
       | UFault | UOk CstrFault => ret_outcome (errno_ret EFAULT) m
       | USpecial => Unmodeled
       | UOk (CstrOk p) =>
           if path_eqb p [] then ret_outcome (errno_ret ENOENT) m
           else if negb (bv_eqb dirfd AT_FDCWD32) then Unmodeled
           else
             let c := path_strip_trailing_slashes p in
             if path_eqb c [] then
               (if unlink_rmdir flags then ret_outcome (errno_ret EBUSY) m
                else ret_outcome (errno_ret EISDIR) m)
             else if path_has_slash c then
               (match tmp_name c with
                | Some n => unlinkat_tmp_witness n p c flags m
                | None => Unmodeled
                end)
             else if path_eqb c dot_path then
               (if unlink_rmdir flags then ret_outcome (errno_ret EINVAL) m
                else ret_outcome (errno_ret EISDIR) m)
             else if path_eqb c dotdot_path then
               (if unlink_rmdir flags then ret_outcome (errno_ret ENOTEMPTY) m
                else ret_outcome (errno_ret EISDIR) m)
             else if Nat.ltb NAME_MAX (length c) then Unmodeled
             else if fs_under (m_fs m) c then Unmodeled
             else
             match fs_lookup (m_fs m) c with
             | None => ret_outcome (errno_ret ENOENT) m
             | Some _ => unlink_found_witness p c flags m
             end
  end.

(** The flag arm carries no copy-in — the kernel decides it before
    [getname()] — and every other arm carries the one pathname range
    [Fs.Namei.unlinkat_spec] records. *)
Definition unlinkat_witness (dirfd pathp flags : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (modeled_unlink_flags flags) then ret_outcome (errno_ret EINVAL) m
  else
    outcome_copyins [(pathp, user_cstr_access_len i m pathp)]
      (unlinkat_body_witness dirfd pathp flags i m).

(** Read the input and the model, the two steps every arm of
    [Fs.Namei.unlinkat_spec] begins with. *)
Ltac unlinkat_open :=
  eapply bind_step; [apply input_ok|]; cbv beta;
  eapply bind_step; [apply get_model_ok|]; cbv beta iota zeta.

Local Lemma unlink_found_witness_ok : forall p c flags i m,
  unlink_found_spec p c flags m i m (unlink_found_witness p c flags m).
Proof.
  intros. unfold unlink_found_spec, unlink_found_witness.
  destruct (unlink_rmdir flags); [apply pure_ok|].
  destruct (path_trailing_slash p); [apply pure_ok|].
  destruct (fd_names_path (m_fds m) c); [apply unmodeled_intro|].
  apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
Qed.

Local Lemma unlinkat_tmp_witness_ok : forall n p c flags i m,
  unlinkat_tmp_spec n p c flags m i m (unlinkat_tmp_witness n p c flags m).
Proof.
  intros. unfold unlinkat_tmp_spec, unlinkat_tmp_witness.
  destruct (unlink_rmdir flags); [apply unmodeled_intro|].
  destruct (Nat.ltb NAME_MAX (length n)); [apply unmodeled_intro|].
  destruct (fs_under (m_fs m) c); [apply pure_ok|].
  destruct (fs_lookup (m_fs m) c) as [data|]; [|apply pure_ok].
  apply unlink_found_witness_ok.
Qed.

Local Lemma unlinkat_body_witness_ok : forall dirfd pathp flags i m,
  unlinkat_body_spec dirfd pathp flags i m i m
    (unlinkat_body_witness dirfd pathp flags i m).
Proof.
  intros. unfold unlinkat_body_spec, unlinkat_body_witness.
  (* Both sides read the same guards in the same order, so one [destruct]
     settles each; the body opens no binds, which is what the wrapper
     below peels instead. *)
  destruct (user_read_cstr i m pathp) as [[p| |]| |];
    [|apply pure_ok|apply pure_ok|apply pure_ok|apply unmodeled_intro].
  destruct (path_eqb p []); [apply pure_ok|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); [apply unmodeled_intro|].
  cbv zeta.
  destruct (path_eqb (path_strip_trailing_slashes p) []);
    [destruct (unlink_rmdir flags); apply pure_ok|].
  destruct (path_has_slash (path_strip_trailing_slashes p)).
  { destruct (tmp_name (path_strip_trailing_slashes p)) as [n|];
      [apply unlinkat_tmp_witness_ok|apply unmodeled_intro]. }
  destruct (path_eqb (path_strip_trailing_slashes p) dot_path);
    [destruct (unlink_rmdir flags); apply pure_ok|].
  destruct (path_eqb (path_strip_trailing_slashes p) dotdot_path);
    [destruct (unlink_rmdir flags); apply pure_ok|].
  destruct (Nat.ltb NAME_MAX (length (path_strip_trailing_slashes p)));
    [apply unmodeled_intro|].
  destruct (fs_under (m_fs m) (path_strip_trailing_slashes p));
    [apply unmodeled_intro|].
  destruct (fs_lookup (m_fs m) (path_strip_trailing_slashes p)) as [data|];
    [|apply pure_ok].
  apply unlink_found_witness_ok.
Qed.

Lemma unlinkat_witness_ok : forall dirfd pathp flags i m,
  unlinkat_spec dirfd pathp flags i m (unlinkat_witness dirfd pathp flags i m).
Proof.
  intros. unfold unlinkat_spec, unlinkat_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota.
  destruct (negb (modeled_unlink_flags flags)) eqn:Hfl.
  { apply pure_ok. }
  apply record_copyins_outcome. apply unlinkat_body_witness_ok.
Qed.
