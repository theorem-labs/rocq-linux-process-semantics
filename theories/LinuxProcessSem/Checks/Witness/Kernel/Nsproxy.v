(** * LinuxProcessSem.Checks.Witness.Kernel.Nsproxy — the setns (268) witness, and its proof

    Mirrors [Sys/Kernel/Nsproxy.v], which answers to Linux
    [kernel/nsproxy.c]: this file holds the witnesses for the syscalls
    defined there, and no others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export Prelude.

(** Every outcome of [Kernel.Nsproxy.setns_spec] is one fixed answer, so
    the witness is that answer. *)
Definition setns_witness (fd : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdOpaque (OProcPath _)) => ret_outcome (errno_ret EBADF) m
  | Some (FdOpaque (ONsFile _)) => Unmodeled
  | Some _ => ret_outcome (errno_ret EINVAL) m
  end.

Lemma setns_witness_ok : forall fd i m, setns_spec fd i m (setns_witness fd m).
Proof.
  intros. unfold setns_spec, setns_witness.
  destruct (fd_lookup (m_fds m) fd)
    as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |[p|p|fl|h|fl pos|mask fl|live|pt]]|] eqn:Hfd;
    (eapply bind_step; [apply get_model_ok|]);
    cbv beta iota zeta; srw Hfd; solve [apply pure_ok | apply unmodeled_intro].
Qed.
