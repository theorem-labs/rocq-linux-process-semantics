(** * LinuxProcessSem.Checks.Witness.Fs.File — the dup (23), dup3 (24) and close_range (436) witnesses, and their proofs

    Mirrors [Sys/Fs/File.v], which answers to Linux [fs/file.c]: this
    file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from.

    dup allocates, so its witness takes the environment-failure branch,
    as openat's does; dup3 and close_range are deterministic on every
    arm they answer and have none to take. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude.

Definition dup_witness (oldfd : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) oldfd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some e =>
      if negb (dup_modeled_entry e) then Unmodeled
      else ret_outcome (errno_ret witness_errno) m
  end.

Lemma dup_witness_ok : forall oldfd i m,
  dup_spec oldfd i m (dup_witness oldfd m).
Proof.
  intros. unfold dup_spec, dup_witness.
  destruct (fd_lookup (m_fds m) oldfd) as [e|] eqn:Hfd.
  - destruct (negb (dup_modeled_entry e)) eqn:Hk.
    + eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hk. apply unmodeled_intro.
    + eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hk.
      apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
  - eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
Qed.

Definition dup3_witness (oldfd newfd flags : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (dup3_flags_ok flags) then ret_outcome (errno_ret EINVAL) m
  else if bv_eqb oldfd newfd then ret_outcome (errno_ret EINVAL) m
  else if negb (dup3_newfd_under_limit newfd m)
       then ret_outcome (errno_ret EBADF) m
  else
    match fd_lookup (m_fds m) oldfd with
    | None => ret_outcome (errno_ret EBADF) m
    | Some e =>
        if negb (dup_modeled_entry e) then Unmodeled
        else
          match fd_lookup (m_fds m) newfd with
          | None =>
              if Z.ltb (bv_unsigned newfd) NR_OPEN_DEFAULT
              then ret_outcome newfd (with_fds (fd_insert (m_fds m) newfd e) m)
              else Unmodeled
          | Some _ =>
              ret_outcome newfd (with_fds (fd_insert (m_fds m) newfd e) m)
          end
    end.

Lemma dup3_witness_ok : forall oldfd newfd flags i m,
  dup3_spec oldfd newfd flags i m (dup3_witness oldfd newfd flags m).
Proof.
  intros. unfold dup3_spec, dup3_witness.
  destruct (negb (dup3_flags_ok flags)) eqn:Hf.
  { eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta. apply pure_ok. }
  destruct (bv_eqb oldfd newfd) eqn:Hne.
  { eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta. apply pure_ok. }
  destruct (negb (dup3_newfd_under_limit newfd m)) eqn:Hl.
  { eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hl. apply pure_ok. }
  destruct (fd_lookup (m_fds m) oldfd) as [e|] eqn:Hfd.
  - destruct (negb (dup_modeled_entry e)) eqn:Hk.
    + eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hl; srw Hfd; srw Hk. apply unmodeled_intro.
    + destruct (fd_lookup (m_fds m) newfd) as [e2|] eqn:Hnf.
      * eapply bind_step; [apply get_model_ok|].
        cbv beta iota zeta; srw Hl; srw Hfd; srw Hk; srw Hnf.
        eapply bind_step; [apply modify_ok|]. apply pure_ok.
      * destruct (Z.ltb (bv_unsigned newfd) NR_OPEN_DEFAULT) eqn:Hb.
        { eapply bind_step; [apply get_model_ok|].
          cbv beta iota zeta; srw Hl; srw Hfd; srw Hk; srw Hnf.
          eapply bind_step; [apply modify_ok|]. apply pure_ok. }
        eapply bind_step; [apply get_model_ok|].
        cbv beta iota zeta; srw Hl; srw Hfd; srw Hk; srw Hnf.
        apply unmodeled_intro.
  - eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hl; srw Hfd. apply pure_ok.
Qed.

(** close_range: the spec's own answer on every arm -- the two -EINVALs,
    the decline for a known flag, and 0 with the range removed. *)
Definition close_range_witness (fd max_fd flags : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (Z.eqb (Z.ldiff (bv_unsigned flags)
                          (Z.lor CLOSE_RANGE_UNSHARE CLOSE_RANGE_CLOEXEC)) 0)
  then ret_outcome (errno_ret EINVAL) m
  else if (bv_unsigned max_fd <? bv_unsigned fd)%Z
  then ret_outcome (errno_ret EINVAL) m
  else if negb (Z.eqb (bv_unsigned flags) 0) then Unmodeled
  else ret_outcome (Z_to_bv 64 0)
         (with_fds (close_range_fds fd max_fd (m_fds m)) m).

Lemma close_range_witness_ok : forall fd max_fd flags i m,
  close_range_spec fd max_fd flags i m (close_range_witness fd max_fd flags m).
Proof.
  intros. unfold close_range_spec, close_range_witness.
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned flags)
                                 (Z.lor CLOSE_RANGE_UNSHARE CLOSE_RANGE_CLOEXEC)) 0));
    [apply pure_ok|].
  destruct ((bv_unsigned max_fd <? bv_unsigned fd)%Z); [apply pure_ok|].
  destruct (negb (Z.eqb (bv_unsigned flags) 0)); [apply unmodeled_intro|].
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  eapply bind_step; [apply modify_ok|]. apply pure_ok.
Qed.
