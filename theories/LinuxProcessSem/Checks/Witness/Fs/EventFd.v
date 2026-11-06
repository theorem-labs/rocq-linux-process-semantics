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

    Past the gate the spec is an [alt] of the injected failure and the
    new descriptor, and this takes the ERRNO side, as [socket_witness]
    and [openat_witness] do: [Sys.Fs.EventFd.eventfd2_errnos] is headed
    by ENOMEM, so [errno_head_witness] supplies the outcome and the
    success branch's [lowest_fd] never has to be shown inhabited. *)
Definition eventfd2_witness (flags : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (Z.eqb (Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET) 0)
  then ret_outcome (errno_ret EINVAL) m
  else ret_outcome (errno_ret witness_errno) m.   (* the kmalloc's -ENOMEM *)

Lemma eventfd2_witness_ok : forall flags i m,
  eventfd2_spec flags i m (eventfd2_witness flags m).
Proof.
  intros flags i m.
  unfold eventfd2_spec, eventfd2_einval_b, eventfd2_witness.
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET) 0);
    cbn [negb]; cbv beta iota.
  - eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|]. cbv beta zeta.
    apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
  - apply pure_ok.
Qed.
