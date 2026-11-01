(** * LinuxProcessSem.Checks.Witness.Fs.EventFd — the eventfd2 (19) witness, and its proof

    Mirrors [Sys/Fs/EventFd.v], which answers to Linux [fs/eventfd.c]:
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
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude.

(** The gate is written out for the third time; [Checks/Sys/Fs/EventFd]
    says why the three layers restate it rather than share one
    predicate.

    An accepted flag word exhibits the FIRST of [eventfd2_errnos], the
    allocation failure: an alternative the spec always admits, whatever
    the descriptor table holds, so the witness needs no free-fd
    argument.  The descriptor itself is the spec's other alternative,
    and [Checks.Cases.Fs.EventFd] pins that it is admitted. *)
Definition eventfd2_witness (flags : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (Z.eqb (Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET) 0)
  then ret_outcome (errno_ret EINVAL) m
  else ret_outcome (errno_ret ENOMEM) m.

Lemma eventfd2_witness_ok : forall flags i m,
  eventfd2_spec flags i m (eventfd2_witness flags m).
Proof.
  intros flags i m.
  unfold eventfd2_spec, eventfd2_einval_b, eventfd2_witness.
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET) 0);
    cbn [negb]; cbv iota.
  - eapply bind_step; [apply get_model_ok|]. cbv beta.
    apply alt_l. eapply bind_step; [apply (choose_ok _ ENOMEM); cbn; auto|].
    apply pure_ok.
  - apply pure_ok.
Qed.
