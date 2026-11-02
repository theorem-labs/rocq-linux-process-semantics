(** * LinuxProcessSem.Checks.Progress — receptiveness: the model is never stuck

    For every syscall input (number, register arguments, pre-syscall
    memory) and every model state, [syscall_spec] admits SOME outcome —
    an [Ok] effect or an explicit [Unmodeled].  Together with the machine step
    being total-or-illegal, this validates that the trace semantics has
    no stuck-and-not-halted configurations (see the note in Run.v).

    WHAT IT DOES AND DOES NOT CERTIFY, because the difference is easy to
    over-read.  [receptive] exhibits ONE admissible outcome for every
    input and model state -- the witness -- so what it certifies is that
    no spec is STUCK.  It does not certify that any particular ARM is
    inhabited.  The only way to write a non-receptive spec in this DSL
    is a [choose] with an unsatisfiable predicate, but one to the RIGHT
    of an [alt] whose left branch always answers is invisible here: the
    witness takes the left branch, the right is never evaluated, and
    this theorem still proves.  That is not hypothetical, it is how
    [openat] is built -- [Witness/Fs/Open.v]'s [openat_core_witness]
    answers from [openat_errnos] on every path it reaches, so
    [Fs.File.lowest_fd]'s [choose] on the success side is never shown
    inhabited.  [Sys/Fs/Open.v] says the same thing from the other
    direction, noting that EMFILE and ENFILE are in that set partly to
    "keep the spec receptive when no free fd < 2^31 exists".

    Syscall arguments and returns are [word = bv 64], errnos are [Z],
    and the brk/word choices follow the Z-side predicates of Specs.v.

    The witnesses are EXPLICIT DEFINITIONS, not existentials buried in
    proof scripts: each [<sys>_witness] is a computable function from the
    syscall's inputs and the model to a concrete outcome (the one-byte
    delivery — or, at end of input, the 0 return — for channel reads,
    the ENOMEM failure branch for mmap/openat, …),
    and [<sys>_witness_ok] proves the spec admits it.  [receptive] then
    states [syscall_spec i m (syscall_spec_witness i m)] — so the chosen
    outcome is readable here rather than recoverable only by stepping
    through the proof. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* =========================================================================
   Proof kit
   ========================================================================= *)

From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Dispatch.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude Uaccess Fs.DPath Fs.File Fs.ReadWrite Fs.Open Fs.Sync Fs.Stat Fs.Select
  Fs.Ioctl Fs.Fcntl Fs.Locks Fs.Namei Fs.Readdir Fs.Timerfd Fs.Pipe
  Fs.EventPoll Fs.EventFd Mm.Mmap Mm.Mremap Mm.Mprotect Mm.Madvise Kernel.Exit
  Kernel.Capability
  Kernel.Fork Kernel.Futex.Syscalls Kernel.Groups
  Kernel.Sched.Syscalls Kernel.Signal Kernel.Sys
  Kernel.Time.Hrtimer Kernel.Time.PosixTimers Kernel.Time.Time
  Net.Socket
  Drivers.Char.Random.

(** The witness for this input's syscall, from the same table the spec and
    the checker dispatch over.  A number with no arm has no witness and is
    [Unmodeled] -- which is what [receptive] then has to show, once. *)
Definition syscall_spec_witness (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match lookup_ca checked_table (bv_unsigned (in_sysno i)) with
  | Some c => ca_witness c i m
  | None   => Unmodeled
  end.

(** The dispatcher is receptive: [syscall_spec_witness i m] is an
    admissible outcome for every input and model state. *)
(** Receptivity in one lookup: the spec dispatches over [spec_table], the
    witness over [checked_table], and [checked_table_arms] says those are
    the same surface -- so the arm that answers is the arm whose
    [ca_receptive] field is exactly this goal.  No case analysis over the
    numbers, and nothing here grows when a syscall is added. *)
Theorem receptive : forall (i : SyscallInput) (m : Model),
  syscall_spec i m (syscall_spec_witness i m).
Proof.
  intros i m. unfold syscall_spec, dispatch, syscall_spec_witness.
  rewrite <- checked_table_arms, lookup_ca_arm.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    cbn [option_map]; [ apply (ca_receptive c) | apply unmodeled_intro ].
Qed.

Corollary receptive_ex : forall (i : SyscallInput) (m : Model),
  exists o, syscall_spec i m o.
Proof. intros. eexists. apply receptive. Qed.
