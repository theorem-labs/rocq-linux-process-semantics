(** * LinuxProcessSem.Checks.Witness.Fs.Sync — the fsync (82), fdatasync (83) witnesses, and their proofs

    Mirrors [Sys/Fs/Sync.v], which answers to Linux [fs/sync.c]: this
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
  Prelude Fs.ReadWrite.

Definition fsync_witness (fd : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdChannel _) => ret_outcome (errno_ret EINVAL) m
  | Some (FdSocket _)  => ret_outcome (errno_ret EINVAL) m  (* no [.fsync] on a socket *)
  | Some (FdStream _ _ _) => ret_outcome (errno_ret EINVAL) m  (* [socket_file_ops] too *)
  | Some (FdDgram _)   => ret_outcome (errno_ret EINVAL) m    (* and a datagram socket *)
  | Some (FdEventfd _) => ret_outcome (errno_ret EINVAL) m    (* no [.fsync] in [eventfd_fops] *)
  | Some (FdPipe _ _)  => ret_outcome (errno_ret EINVAL) m
  | Some (FdDevNull _ _) => ret_outcome (errno_ret EINVAL) m
  | Some FdUrandom => ret_outcome (errno_ret EINVAL) m
  | Some (FdFileA _ _) => ret_outcome (Z_to_bv 64 0) m
  | Some (FdFileRW _ _) => ret_outcome (Z_to_bv 64 0) m
  | Some (FdFile _ _)  => ret_outcome (Z_to_bv 64 0) m
  | Some (FdFileW _ _) => ret_outcome (Z_to_bv 64 0) m
  | Some FdDir         => ret_outcome (Z_to_bv 64 0) m
  end.

Lemma fsync_witness_ok : forall fd i m, fsync_spec fd i m (fsync_witness fd m).
Proof.
  intros. unfold fsync_spec, fsync_witness.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; [destruct e|];
    (eapply bind_step; [apply get_model_ok|]);
    cbv beta iota zeta; srw Hfd; apply pure_ok.
Qed.

(* =========================================================================
   prlimit64 (261) — witness: the modeled arms are deterministic apart
   from the environment's first choice of the inherited limit, and 16
   zero bytes are a well-formed pair (soft = hard = 0), so they serve.
   ========================================================================= *)
