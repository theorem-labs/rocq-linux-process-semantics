(** * LinuxProcessSem.Checks.Witness.Fs.Ioctl — the ioctl (29) witnesses, and their proofs

    Mirrors [Sys/Fs/Ioctl.v], which answers to Linux [fs/ioctl.c]: this
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

Definition ioctl_witness (fd req : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdChannel _) | Some (FdFile _ _) | Some (FdFileW _ _) | Some FdDir
  | Some (FdSocket _) | Some (FdPipe _ _) | Some (FdFileA _ _)
  | Some (FdFileRW _ _) | Some (FdDevNull _ _) =>
      if tty_only_request req then ret_outcome (errno_ret ENOTTY) m
      else Unmodeled
  | Some FdUrandom => Unmodeled
  | Some (FdOpaque _) => Unmodeled   (* declined on every request *)
  end.

Lemma ioctl_witness_ok : forall fd req i m, ioctl_spec fd req i m (ioctl_witness fd req m).
Proof.
  intros. unfold ioctl_spec, ioctl_witness.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  - (* the open-fd arms are enumerated, so [e] must be destructed for the
       match to reduce; every constructor answers alike. *)
    destruct e; destruct (tty_only_request req) eqn:Hr;
      (eapply bind_step; [apply get_model_ok|]);
      cbv beta iota; srw Hfd;
      first [apply pure_ok | apply unmodeled_intro].
  - eapply bind_step; [apply get_model_ok|].
    cbv beta iota; srw Hfd. apply pure_ok.
Qed.
