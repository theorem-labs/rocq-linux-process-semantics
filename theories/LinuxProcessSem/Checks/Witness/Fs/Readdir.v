(** * LinuxProcessSem.Checks.Witness.Fs.Readdir — the getdents64 (61) witness, and its proof

    Mirrors [Sys/Fs/Readdir.v], which answers to Linux [fs/readdir.c]:
    this file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export Prelude.

(** On the directory arm the witness takes -EINVAL rather than the
    injected -ENOENT: it is the answer the model actually derives from
    [count], while a directory removed out from under the fd is a
    condition no modeled state decides.  Above the small-buffer band,
    failing closed is itself the admissible outcome. *)
Definition getdents64_witness (fd count : word) (m : Model)
    : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdChannel _) => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdFile _ _)  => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdFileW _ _) => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdFileA _ _) => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdFileRW _ _) => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdPipe _ _)  => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdSocket _)  => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdDevNull _ _) => ret_outcome (errno_ret ENOTDIR) m
  | Some FdUrandom => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdOpaque _) => Unmodeled   (* declined by the spec *)
  | Some FdDir =>
      if getdents64_no_room count
      then ret_outcome (errno_ret EINVAL) m
      else Unmodeled
  end.

Lemma getdents64_witness_ok : forall fd count i m,
  getdents64_spec fd count i m (getdents64_witness fd count m).
Proof.
  intros fd count i m. unfold getdents64_spec, getdents64_witness.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; [destruct e|];
    (eapply bind_step; [apply get_model_ok|]);
    cbv beta iota zeta; srw Hfd; try solve [apply pure_ok | apply unmodeled_intro].
  destruct (getdents64_no_room count) eqn:Hroom; [|apply unmodeled_intro].
  apply alt_r. unfold err_ret, ret_only, ret_outcome. apply pure_ok.
Qed.
