import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Signal
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Kernel.Signal — the signal arms on the checked surface

The registration of `Checks/Sys/Kernel/Signal.lean`'s checkers in
`checked_table`, in the one file that registration writes.
`tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files
under `Checks/Arms/`, one per checker twin, so that registering an arm
creates or edits no hub but this file; its docstring is the shape it reads
and what it refuses. The file holds three sections, each in the
namespace its declarations had when those three hubs were written by
hand, so that no name moved with the file:

- `Checks.Sys.Table`: each `CheckedArm` and its four `arm_unfold` lemmas,
  in syscall-number order;
- `Checks.VmMapsDisjoint.Arms`: each arm's ledger fact,
  `arm_<name>_preserves_vm`, which `checked_table_preserves_vm`'s
  alternation names;
- `Checks.Invariants`: one `<invariant>_arm_<name>` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`, which
  `registry_preserves`'s alternation names.

The checker twin is shared by more than one registration ticket, so each
arm carries its own `/- ### name (N) -/` heading in every section and
everything particular to an arm is in that arm's own docstrings.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arms are the rows of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table`, read at that commit. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### tkill (130) -/

/-- The acceptor `arm_tkill` holds, `check_tkill` at registers `a0` and `a1`,
behind a name the unifier does not unfold.  The alternations
`tools/gen_lean_checked.py` renders (`checked_table_preserves_vm`,
`registry_preserves`) try every arm's fact against every arm's goal, and
`arm_preserves inv c` reads `c.ca_check` alone, so a mismatched
alternative compares two arms' acceptors; with `check_tkill` open
that comparison ran past the recursion limit on this tree (the build of
both generated modules failed at `arm_tkill`'s alternative), which
`first` does not catch.  Held
irreducible, the comparison stops at this name and the alternative fails
as a mismatch.  `check_tkill_a0_a1_eq` opens it, and
`ca_check_arm_tkill` states the arm through it.  `arm_tgkill` needs no
such name: with this one held and `check_tgkill` open, both modules
build.  Lean-only: Rocq's `arm_tkill` holds the checker itself. -/
@[irreducible] def check_tkill_a0_a1 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_result :=
  Checks.Sys.Kernel.Signal.check_tkill (Sys.Syscall.pid32 (in_arg i 0))
    (Sys.Kernel.Signal.sig32 (in_arg i 1)) eff m

/-- `check_tkill_a0_a1` is `check_tkill` at `a0` and `a1`, by its equation
lemma.  Lean-only, as the wrapper is. -/
theorem check_tkill_a0_a1_eq (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_tkill_a0_a1 i eff m = Checks.Sys.Kernel.Signal.check_tkill (Sys.Syscall.pid32 (in_arg i 0))
      (Sys.Kernel.Signal.sig32 (in_arg i 1)) eff m := by
  unfold check_tkill_a0_a1
  rfl

/-- tkill (130).  The checker's own answer is `CheckUnmodeled` on every
shape whenever the model's abort declaration is clear
(`check_tkill_off_declines_symbolically`, in the checker's Cases file), so
an arm on a number the task did not ask for behaves as a number with no
arm (Rocq's docstring on `arm_tkill`).  The target is register `a0` and the signal
`a1`, each cut to its low 32 bits: riscv64's `__riscv_sys_tkill` hands the
registers over in order, `orig_a0` then `a1` (`SC_RISCV_REGS_TO_ARGS`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46), and the
wrapper narrows each to the type `SYSCALL_DEFINE2(tkill, pid_t, pid, int,
sig)` declares (kernel/signal.c:4192, same version) through `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46), so the
`pid <= 0` test at kernel/signal.c:4195-4196 reads the narrowed `int`.
`Sys.Syscall.pid32` and `Sys.Kernel.Signal.sig32` are that reading,
applied here at the boundary as Rocq's `arm_tkill` applies it.  `ca_arm`
is the term `Sys/Registry/Kernel/Signal.lean`'s row builds, which
`checked_table_arms` checks.  `ca_check` holds the checker
behind `check_tkill_a0_a1`, whose docstring says why. -/
def arm_tkill : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 130
    (fun i => Sys.Kernel.Signal.tkill_spec (Sys.Syscall.pid32 (in_arg i 0))
      (Sys.Kernel.Signal.sig32 (in_arg i 1)) i)
  ca_check := fun i eff m => check_tkill_a0_a1 i eff m
  ca_witness := fun i m =>
    Checks.Sys.Kernel.Signal.tkill_witness (Sys.Syscall.pid32 (in_arg i 0))
      (Sys.Kernel.Signal.sig32 (in_arg i 1)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Signal.check_tkill_sound_ok (Sys.Syscall.pid32 (in_arg i 0))
      (Sys.Kernel.Signal.sig32 (in_arg i 1)) eff m m' evs i
      ((check_tkill_a0_a1_eq i eff m).symm.trans h)
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Signal.check_tkill_sound_unmodeled (Sys.Syscall.pid32 (in_arg i 0))
      (Sys.Kernel.Signal.sig32 (in_arg i 1)) eff m i
      ((check_tkill_a0_a1_eq i eff m).symm.trans h)
  ca_complete_ok := fun i eff m m' evs h =>
    (check_tkill_a0_a1_eq i eff m).trans
      (Checks.Sys.Kernel.Signal.check_tkill_complete_ok (Sys.Syscall.pid32 (in_arg i 0))
        (Sys.Kernel.Signal.sig32 (in_arg i 1)) eff m m' evs i h)
  ca_complete_unmodeled := fun i m eff h =>
    (check_tkill_a0_a1_eq i eff m).trans
      (Checks.Sys.Kernel.Signal.check_tkill_complete_unmodeled (Sys.Syscall.pid32 (in_arg i 0))
        (Sys.Kernel.Signal.sig32 (in_arg i 1)) m i eff h)
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Signal.tkill_witness_ok (Sys.Syscall.pid32 (in_arg i 0))
      (Sys.Kernel.Signal.sig32 (in_arg i 1)) i m

@[arm_unfold] theorem ca_check_arm_tkill (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_tkill.ca_check i eff m
      = Checks.Sys.Kernel.Signal.check_tkill (Sys.Syscall.pid32 (in_arg i 0))
          (Sys.Kernel.Signal.sig32 (in_arg i 1)) eff m :=
  check_tkill_a0_a1_eq i eff m
@[arm_unfold] theorem ca_witness_arm_tkill (i : SyscallInput) (m : Model) :
    arm_tkill.ca_witness i m
      = Checks.Sys.Kernel.Signal.tkill_witness (Sys.Syscall.pid32 (in_arg i 0))
          (Sys.Kernel.Signal.sig32 (in_arg i 1)) m := rfl
@[arm_unfold] theorem sa_spec_arm_tkill (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_tkill.ca_arm.sa_spec i m o
      = Sys.Kernel.Signal.tkill_spec (Sys.Syscall.pid32 (in_arg i 0))
          (Sys.Kernel.Signal.sig32 (in_arg i 1)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_tkill : ca_no arm_tkill = 130 := rfl

/- ### tgkill (131) -/

/-- tgkill (131).  The same declaration gate as `arm_tkill`, so the same
behaviour on a task that did not declare the abort (the same theorem's
second conjunct).  The thread-group id
is register `a0`, the target `a1` and the signal `a2`, each cut to its low
32 bits by the same wrapper (`SC_RISCV_REGS_TO_ARGS`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, and `__SC_CAST`,
include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46) to the types
`SYSCALL_DEFINE3(tgkill, pid_t, tgid, pid_t, pid, int, sig)` declares
(kernel/signal.c:4176, same version), whose `pid <= 0 || tgid <= 0` test
(:4179-4180) reads the narrowed `int`s.  `ca_arm` is the term
`Sys/Registry/Kernel/Signal.lean`'s row builds. -/
def arm_tgkill : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 131
    (fun i => Sys.Kernel.Signal.tgkill_spec (Sys.Syscall.pid32 (in_arg i 0))
      (Sys.Syscall.pid32 (in_arg i 1)) (Sys.Kernel.Signal.sig32 (in_arg i 2)) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Signal.check_tgkill (Sys.Syscall.pid32 (in_arg i 0))
      (Sys.Syscall.pid32 (in_arg i 1)) (Sys.Kernel.Signal.sig32 (in_arg i 2)) eff m
  ca_witness := fun i m =>
    Checks.Sys.Kernel.Signal.tgkill_witness (Sys.Syscall.pid32 (in_arg i 0))
      (Sys.Syscall.pid32 (in_arg i 1)) (Sys.Kernel.Signal.sig32 (in_arg i 2)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Signal.check_tgkill_sound_ok (Sys.Syscall.pid32 (in_arg i 0))
      (Sys.Syscall.pid32 (in_arg i 1)) (Sys.Kernel.Signal.sig32 (in_arg i 2)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Signal.check_tgkill_sound_unmodeled (Sys.Syscall.pid32 (in_arg i 0))
      (Sys.Syscall.pid32 (in_arg i 1)) (Sys.Kernel.Signal.sig32 (in_arg i 2)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Signal.check_tgkill_complete_ok (Sys.Syscall.pid32 (in_arg i 0))
      (Sys.Syscall.pid32 (in_arg i 1)) (Sys.Kernel.Signal.sig32 (in_arg i 2)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Signal.check_tgkill_complete_unmodeled (Sys.Syscall.pid32 (in_arg i 0))
      (Sys.Syscall.pid32 (in_arg i 1)) (Sys.Kernel.Signal.sig32 (in_arg i 2)) m i eff h
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Signal.tgkill_witness_ok (Sys.Syscall.pid32 (in_arg i 0))
      (Sys.Syscall.pid32 (in_arg i 1)) (Sys.Kernel.Signal.sig32 (in_arg i 2)) i m

@[arm_unfold] theorem ca_check_arm_tgkill (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_tgkill.ca_check i eff m
      = Checks.Sys.Kernel.Signal.check_tgkill (Sys.Syscall.pid32 (in_arg i 0))
          (Sys.Syscall.pid32 (in_arg i 1)) (Sys.Kernel.Signal.sig32 (in_arg i 2)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_tgkill (i : SyscallInput) (m : Model) :
    arm_tgkill.ca_witness i m
      = Checks.Sys.Kernel.Signal.tgkill_witness (Sys.Syscall.pid32 (in_arg i 0))
          (Sys.Syscall.pid32 (in_arg i 1)) (Sys.Kernel.Signal.sig32 (in_arg i 2)) m := rfl
@[arm_unfold] theorem sa_spec_arm_tgkill (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_tgkill.ca_arm.sa_spec i m o
      = Sys.Kernel.Signal.tgkill_spec (Sys.Syscall.pid32 (in_arg i 0))
          (Sys.Syscall.pid32 (in_arg i 1)) (Sys.Kernel.Signal.sig32 (in_arg i 2)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_tgkill : ca_no arm_tgkill = 131 := rfl

/- ### sigaltstack (132) -/

/-- sigaltstack (132).  The two pointers are registers `a0` (`uss`) and
`a1` (`uoss`), read whole: `SYSCALL_DEFINE2(sigaltstack, const stack_t
__user *, uss, stack_t __user *, uoss)` (kernel/signal.c:4455, Linux
v6.18.46) declares both as pointers, 64 bits on riscv64, so `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, same version) narrows
nothing.  The checker also takes the input itself, to read the `stack_t`
at `uss` from the memory the call was made against.  `ca_arm` is the term
`Sys/Registry/Kernel/Signal.lean`'s row builds. -/
def arm_sigaltstack : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 132
    (fun i => Sys.Kernel.Signal.sigaltstack_spec (in_arg i 0) (in_arg i 1) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Signal.check_sigaltstack i (in_arg i 0) (in_arg i 1) eff m
  ca_witness := fun i m =>
    Checks.Sys.Kernel.Signal.sigaltstack_witness (in_arg i 0) (in_arg i 1) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Signal.check_sigaltstack_sound_ok i (in_arg i 0) (in_arg i 1) eff m m'
      evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Signal.check_sigaltstack_sound_unmodeled i (in_arg i 0) (in_arg i 1) eff
      m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Signal.check_sigaltstack_complete_ok i (in_arg i 0) (in_arg i 1) eff m
      m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Signal.check_sigaltstack_complete_unmodeled i (in_arg i 0) (in_arg i 1)
      m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Signal.sigaltstack_witness_ok (in_arg i 0) (in_arg i 1) i m

@[arm_unfold] theorem ca_check_arm_sigaltstack (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_sigaltstack.ca_check i eff m
      = Checks.Sys.Kernel.Signal.check_sigaltstack i (in_arg i 0) (in_arg i 1) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_sigaltstack (i : SyscallInput) (m : Model) :
    arm_sigaltstack.ca_witness i m
      = Checks.Sys.Kernel.Signal.sigaltstack_witness (in_arg i 0) (in_arg i 1) i m := rfl
@[arm_unfold] theorem sa_spec_arm_sigaltstack (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_sigaltstack.ca_arm.sa_spec i m o
      = Sys.Kernel.Signal.sigaltstack_spec (in_arg i 0) (in_arg i 1) i m o := rfl
@[arm_unfold] theorem ca_no_arm_sigaltstack : ca_no arm_sigaltstack = 132 := rfl

/- ### rt_sigaction (134) -/

/-- rt_sigaction (134).  THE SIGNAL IS REGISTER `a0` CUT TO ITS LOW 32
BITS; `act`, `oact` AND `sigsetsize` ARE `a1`, `a2` AND `a3` READ WHOLE.
riscv64's `__riscv_sys_rt_sigaction` hands the registers over in order,
`orig_a0` then `a1` to `a3` (`SC_RISCV_REGS_TO_ARGS` under `CONFIG_64BIT`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46), and the
wrapper narrows each to the type `SYSCALL_DEFINE4(rt_sigaction, int, sig,
const struct sigaction __user *, act, struct sigaction __user *, oact,
size_t, sigsetsize)` declares (kernel/signal.c:4638-4641, same version)
through `__SC_CAST` (include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46): `int` is
32 bits, and the two pointers and `size_t` are 64.  `Sys.Kernel.Signal.sig32
(in_arg i 0)` is that reading, applied here at the boundary as Rocq's
`arm_rt_sigaction` applies it, so the checker and the witness receive the
narrowed signal and neither narrows again, and `sigsetsize` reaches the
size test whole, as `if (sigsetsize != sizeof(sigset_t))`
(kernel/signal.c:4647-4648, Linux v6.18.46) reads it.  `Checks/Cases/Checks/Sys/Kernel/Signal.lean`
pins both halves over the table.  `ca_arm` is the term
`Sys/Registry/Kernel/Signal.lean`'s row builds, which `checked_table_arms`
checks.  The ledger fact this arm owes `checked_table_preserves_vm`
is `check_rt_sigaction_frame`, which Rocq states beside the alternation
rather than beside the checker, and so is stated below. -/
def arm_rt_sigaction : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 134 (fun i =>
    Sys.Kernel.Signal.rt_sigaction_spec (Sys.Kernel.Signal.sig32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Signal.check_rt_sigaction i (Sys.Kernel.Signal.sig32 (in_arg i 0))
      (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m =>
    Checks.Sys.Kernel.Signal.rt_sigaction_witness (Sys.Kernel.Signal.sig32 (in_arg i 0))
      (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Signal.check_rt_sigaction_sound_ok i (Sys.Kernel.Signal.sig32 (in_arg i 0))
      (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Signal.check_rt_sigaction_sound_unmodeled i
      (Sys.Kernel.Signal.sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Signal.check_rt_sigaction_complete_ok i
      (Sys.Kernel.Signal.sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Signal.check_rt_sigaction_complete_unmodeled i
      (Sys.Kernel.Signal.sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Signal.rt_sigaction_witness_ok (Sys.Kernel.Signal.sig32 (in_arg i 0))
      (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

@[arm_unfold] theorem ca_check_arm_rt_sigaction (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_rt_sigaction.ca_check i eff m
      = Checks.Sys.Kernel.Signal.check_rt_sigaction i (Sys.Kernel.Signal.sig32 (in_arg i 0))
          (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_rt_sigaction (i : SyscallInput) (m : Model) :
    arm_rt_sigaction.ca_witness i m
      = Checks.Sys.Kernel.Signal.rt_sigaction_witness (Sys.Kernel.Signal.sig32 (in_arg i 0))
          (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := rfl
@[arm_unfold] theorem sa_spec_arm_rt_sigaction (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_rt_sigaction.ca_arm.sa_spec i m o
      = Sys.Kernel.Signal.rt_sigaction_spec (Sys.Kernel.Signal.sig32 (in_arg i 0)) (in_arg i 1)
          (in_arg i 2) (in_arg i 3) i m o := rfl
@[arm_unfold] theorem ca_no_arm_rt_sigaction : ca_no arm_rt_sigaction = 134 := rfl

/- ### rt_sigprocmask (135) -/

/-- rt_sigprocmask (135).  `how` IS REGISTER `a0` CUT TO ITS LOW 32 BITS;
`nset`, `oset` AND `sigsetsize` ARE `a1`, `a2` AND `a3` READ WHOLE.  The
registers arrive in order through the same `SC_RISCV_REGS_TO_ARGS`
(arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46) and are
narrowed through the same `__SC_CAST` (include/linux/syscalls.h:132,
applied at arch/riscv/include/asm/syscall_wrapper.h:88, same version) to
the types `SYSCALL_DEFINE4(rt_sigprocmask, int, how, sigset_t __user *,
nset, sigset_t __user *, oset, size_t, sigsetsize)` declares
(kernel/signal.c:3327-3328, Linux v6.18.46): `int how` is 32 bits, the
pointers and `size_t` 64.  `Sys.Syscall.how32 (in_arg i 0)` is that
reading, applied here as Rocq's `arm_rt_sigprocmask` applies it; a
`sigsetsize` with a bit above 32 is therefore the wrong size, not the
right one, at the test on kernel/signal.c:3334-3335 (Linux v6.18.46), and
`Checks/Cases/Checks/Sys/Kernel/Signal.lean` pins that over the table
beside the narrowing of `how`.  `ca_arm` is the term
`Sys/Registry/Kernel/Signal.lean`'s row builds.  The ledger fact this arm
owes is `check_rt_sigprocmask_frame`, beside the checker in
`Checks/Sys/Kernel/Signal.lean`, where Rocq states it too. -/
def arm_rt_sigprocmask : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 135 (fun i =>
    Sys.Kernel.Signal.rt_sigprocmask_spec (Sys.Syscall.how32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Signal.check_rt_sigprocmask i (Sys.Syscall.how32 (in_arg i 0))
      (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m =>
    Checks.Sys.Kernel.Signal.rt_sigprocmask_witness (Sys.Syscall.how32 (in_arg i 0))
      (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Signal.check_rt_sigprocmask_sound_ok i (Sys.Syscall.how32 (in_arg i 0))
      (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Signal.check_rt_sigprocmask_sound_unmodeled i
      (Sys.Syscall.how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Signal.check_rt_sigprocmask_complete_ok i
      (Sys.Syscall.how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Signal.check_rt_sigprocmask_complete_unmodeled i
      (Sys.Syscall.how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Signal.rt_sigprocmask_witness_ok (Sys.Syscall.how32 (in_arg i 0))
      (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

@[arm_unfold] theorem ca_check_arm_rt_sigprocmask (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_rt_sigprocmask.ca_check i eff m
      = Checks.Sys.Kernel.Signal.check_rt_sigprocmask i (Sys.Syscall.how32 (in_arg i 0))
          (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_rt_sigprocmask (i : SyscallInput) (m : Model) :
    arm_rt_sigprocmask.ca_witness i m
      = Checks.Sys.Kernel.Signal.rt_sigprocmask_witness (Sys.Syscall.how32 (in_arg i 0))
          (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := rfl
@[arm_unfold] theorem sa_spec_arm_rt_sigprocmask (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_rt_sigprocmask.ca_arm.sa_spec i m o
      = Sys.Kernel.Signal.rt_sigprocmask_spec (Sys.Syscall.how32 (in_arg i 0)) (in_arg i 1)
          (in_arg i 2) (in_arg i 3) i m o := rfl
@[arm_unfold] theorem ca_no_arm_rt_sigprocmask : ca_no arm_rt_sigprocmask = 135 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/- ### tkill (130) -/

/-- `tkill` (130): the accepted model is the one handed in, or the
delivery's — the pending bit or the kill — and both rebuild `ProcState`
alone, so the ledger is what it was (`check_tkill_frame`, stated beside
the checker in `Checks/Sys/Kernel/Signal.lean`). -/
theorem arm_tkill_preserves_vm : arm_preserves_vm arm_tkill :=
  arm_preserves_of_frame arm_tkill (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Signal.check_tkill_frame _ _ eff m m' evs h)

/- ### tgkill (131) -/

/-- `tgkill` (131): likewise, through `check_tgkill_frame`. -/
theorem arm_tgkill_preserves_vm : arm_preserves_vm arm_tgkill :=
  arm_preserves_of_frame arm_tgkill (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Signal.check_tgkill_frame _ _ _ eff m m' evs h)

/- ### sigaltstack (132) -/

/-- What an accepted `sigaltstack` hands back: the model it was given,
on every bare-return answer, or `with_sigaltstack_installed m`, on the
install.  Rocq has no such lemma: its `check_sigaltstack_frame` runs
`vm_frame2` over the checker in place.  Here `vm_step`'s loop over this
checker runs past `maxRecDepth` (measured on this tree, while each step
it takes elaborates alone), so the gates are split by hand, one
`split at h` per gate in the checker's order, into this disjunction, and
both the ledger frame below and the descriptor-state frame in
`Checks.Invariants` read it.  Lean-only. -/
theorem check_sigaltstack_ok_model (i : SyscallInput) (uss uoss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Signal.check_sigaltstack i uss uoss eff m = CheckOk m' evs) :
    m' = m ∨ m' = with_sigaltstack_installed m := by
  unfold Checks.Sys.Kernel.Signal.check_sigaltstack at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · exact Or.inl (check_ret_only_model h)
  split at h
  · exact Or.inl (check_ret_only_model h)
  split at h
  · exact Or.inl (check_ret_only_model h)
  split at h
  · exact Or.inl (check_ret_only_model h)
  split at h
  · cases h
  split at h
  · exact Or.inl (check_ret_only_model h)
  exact Or.inr (check_ret_only_model h)

/-- sigaltstack answers a bare return on every arm, and the one arm that
moves the model hands back `with_sigaltstack_installed m`, which rebuilds
the process state alone.  Stated here and not beside the checker because
Rocq keeps it in `VmMapsDisjoint.v`, where the checker twin's header says
its twin belongs to the registration.  Rocq:
`VmMapsDisjoint.check_sigaltstack_frame`. -/
theorem check_sigaltstack_frame (i : SyscallInput) (uss uoss : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Signal.check_sigaltstack i uss uoss eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  rcases check_sigaltstack_ok_model i uss uoss eff m m' evs h with rfl | rfl
  · rfl
  · exact m_vmmaps_with_sigaltstack_installed m

/-- `sigaltstack` (132): the frame lemma above. -/
theorem arm_sigaltstack_preserves_vm : arm_preserves_vm arm_sigaltstack :=
  arm_preserves_of_frame arm_sigaltstack (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_sigaltstack_frame _ _ _ eff m m' evs h)

/- ### rt_sigaction (134) -/

/-- `check_rt_sigaction` answers a bare return over the model it was handed
on every arm that accepts, so the memory ledger is what it was.  Rocq
states this beside the alternation (`VmMapsDisjoint.v`), not beside the
checker, and its proof, `vm_frame2` after opening the checker, needs no
lemma that lives beside the checker, so by the rule
`Checks/Sys/Kernel/Signal.lean`'s header gives for frame lemmas its twin is
the registration's.
Rocq: `VmMapsDisjoint.check_rt_sigaction_frame`. -/
theorem check_rt_sigaction_frame (i : SyscallInput) (sig act oact ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Signal.check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold Checks.Sys.Kernel.Signal.check_rt_sigaction at h
  vm_frame2 h

/-- `rt_sigaction` (134): the frame just above. -/
theorem arm_rt_sigaction_preserves_vm : arm_preserves_vm arm_rt_sigaction :=
  arm_preserves_of_frame arm_rt_sigaction (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_rt_sigaction_frame i _ _ _ _ eff m m' evs h)

/- ### rt_sigprocmask (135) -/

/-- `rt_sigprocmask` (135): the accepted model is the one handed in or
the mask install over it, `Sys.Kernel.Signal.sigmask_deliver_model`,
which rebuilds the process state alone (`check_rt_sigprocmask_frame`,
stated beside the checker in `Checks/Sys/Kernel/Signal.lean`). -/
theorem arm_rt_sigprocmask_preserves_vm : arm_preserves_vm arm_rt_sigprocmask :=
  arm_preserves_of_frame arm_rt_sigprocmask (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Signal.check_rt_sigprocmask_frame i _ _ _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! The two registry entries beside `vm_wf` read the `m_fd` subsystem, so
one frame lemma per checker over the whole record answers both, as in the
other arm files.  Neither has a Rocq twin: the Rocq tree registers no
`m_fd` invariant. -/

/- ### tkill (130) -/

/-- The delivery rebuilds `ProcState` alone — `State.with_sigabrt_pending`
and `State.with_killed` both hand `m.m_fd` back — so the descriptor
subsystem is the one it was handed.  Lean-only, the descriptor-state
counterpart of `check_send_sigabrt_frame`; the two fd-reading registry
entries have no Rocq twin. -/
theorem check_send_sigabrt_fd_state_frame (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Kernel.Signal.check_send_sigabrt eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  obtain ⟨-, -, rfl⟩ := (Checks.Sys.Kernel.Signal.check_send_sigabrt_ok_iff _ _ _ _).mp h
  split <;> rfl

/-- The shared tail of `tkill` and `tgkill` hands back the model it was
given on every bare-return answer and the delivery's on the SIGABRT one. -/
theorem check_tkill_self_fd_state_frame (pid sig : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Kernel.Signal.check_tkill_self pid sig eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Signal.check_tkill_self at h
  (repeat' vm_step h) <;> first | rfl | exact check_send_sigabrt_fd_state_frame _ _ _ _ h

/-- `check_tkill`: the -EINVAL of `SYSCALL_DEFINE2(tkill)`'s `pid <= 0`
(kernel/signal.c:4195-4196, Linux v6.18.46) hands back the model, and the
rest is the shared tail. -/
theorem check_tkill_fd_state_frame (pid sig : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Kernel.Signal.check_tkill pid sig eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Signal.check_tkill at h
  (repeat' vm_step h) <;> first | rfl | exact check_tkill_self_fd_state_frame _ _ _ _ _ _ h

/-- `vm_wf` × `tkill`: the ledger fact above. -/
theorem vm_wf_arm_tkill : arm_preserves inv_vm_wf arm_tkill :=
  Arms.arm_tkill_preserves_vm

/-- `fd_table_unique` × `tkill`: no answer the arm accepts touches a
descriptor. -/
theorem fd_table_unique_arm_tkill : arm_preserves inv_fd_table_unique arm_tkill :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_tkill (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_tkill_fd_state_frame _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `tkill`: no pipe is touched. -/
theorem pipes_within_capacity_arm_tkill :
    arm_preserves inv_pipes_within_capacity arm_tkill :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_tkill (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_tkill_fd_state_frame _ _ eff m m' evs h))

/- ### tgkill (131) -/

/-- `check_tgkill`: the -EINVAL of `SYSCALL_DEFINE3(tgkill)`'s
`pid <= 0 || tgid <= 0` (kernel/signal.c:4179-4180, Linux v6.18.46) and
the -ESRCH of a foreign thread group hand back the model, and the rest is
the shared tail. -/
theorem check_tgkill_fd_state_frame (tgid pid sig : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Signal.check_tgkill tgid pid sig eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Signal.check_tgkill at h
  (repeat' vm_step h) <;> first | rfl | exact check_tkill_self_fd_state_frame _ _ _ _ _ _ h

/-- `vm_wf` × `tgkill`: the ledger fact above. -/
theorem vm_wf_arm_tgkill : arm_preserves inv_vm_wf arm_tgkill :=
  Arms.arm_tgkill_preserves_vm

/-- `fd_table_unique` × `tgkill`: no answer the arm accepts touches a
descriptor. -/
theorem fd_table_unique_arm_tgkill : arm_preserves inv_fd_table_unique arm_tgkill :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_tgkill (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_tgkill_fd_state_frame _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `tgkill`: no pipe is touched. -/
theorem pipes_within_capacity_arm_tgkill :
    arm_preserves inv_pipes_within_capacity arm_tgkill :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_tgkill (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_tgkill_fd_state_frame _ _ _ eff m m' evs h))

/- ### sigaltstack (132) -/

/-- `check_sigaltstack` hands back the model it was given on every
bare-return answer and `with_sigaltstack_installed m` on the install,
which rebuilds `ProcState` alone (`Arms.check_sigaltstack_ok_model`). -/
theorem check_sigaltstack_fd_state_frame (i : SyscallInput) (uss uoss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Signal.check_sigaltstack i uss uoss eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  rcases Arms.check_sigaltstack_ok_model i uss uoss eff m m' evs h with rfl | rfl <;> rfl

/-- `vm_wf` × `sigaltstack`: the ledger fact above. -/
theorem vm_wf_arm_sigaltstack : arm_preserves inv_vm_wf arm_sigaltstack :=
  Arms.arm_sigaltstack_preserves_vm

/-- `fd_table_unique` × `sigaltstack`: the install records a bit in the
process state and no descriptor. -/
theorem fd_table_unique_arm_sigaltstack :
    arm_preserves inv_fd_table_unique arm_sigaltstack :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_sigaltstack (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_sigaltstack_fd_state_frame _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `sigaltstack`: no pipe is touched. -/
theorem pipes_within_capacity_arm_sigaltstack :
    arm_preserves inv_pipes_within_capacity arm_sigaltstack :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_sigaltstack
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes
        (check_sigaltstack_fd_state_frame _ _ _ eff m m' evs h))

/- ### rt_sigaction (134) -/

/-- `check_rt_sigaction` hands back the model it was given on every
accepting arm, so the descriptor subsystem is the one it was handed.
The walk is `vm_frame`'s, which substitutes the model and closes with
`rfl` whatever projection the goal takes of it. -/
theorem check_rt_sigaction_fd_state_frame (i : SyscallInput) (sig act oact ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Signal.check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Signal.check_rt_sigaction at h
  vm_frame h

/-- `vm_wf` × `rt_sigaction`: the ledger fact above. -/
theorem vm_wf_arm_rt_sigaction : arm_preserves inv_vm_wf arm_rt_sigaction :=
  Arms.arm_rt_sigaction_preserves_vm

/-- `fd_table_unique` × `rt_sigaction`: no disposition this model accepts
opens, closes or binds a descriptor; the frame is the one above. -/
theorem fd_table_unique_arm_rt_sigaction :
    arm_preserves inv_fd_table_unique arm_rt_sigaction :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_rt_sigaction (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_rt_sigaction_fd_state_frame i _ _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `rt_sigaction`: no pipe is touched. -/
theorem pipes_within_capacity_arm_rt_sigaction :
    arm_preserves inv_pipes_within_capacity arm_rt_sigaction :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_rt_sigaction
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes
        (check_rt_sigaction_fd_state_frame i _ _ _ _ eff m m' evs h))

/- ### rt_sigprocmask (135) -/

open LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
  LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
  LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Signal in
/-- The two models `check_rt_sigprocmask` can accept: the one handed in,
on every arm that installs nothing — the size test's -EINVAL, a NULL
`nset` with or without the `oset` copy-out, `copy_from_user`'s -EFAULT
and a bad `how`'s -EINVAL — or the mask install over it, with the
SIGABRT delivery an unblock of a pending one takes, on the two arms past
`sigprocmask` (kernel/signal.c:3339-3354, Linux v6.18.46).  The walk is
`check_rt_sigprocmask_frame`'s, branch for branch, stated once over the
model so that each invariant reading another part of it is one
projection; `check_rt_sigprocmask_frame` keeps its own walk because it is
the Rocq twin and states the ledger alone. -/
theorem check_rt_sigprocmask_model_shape (i : SyscallInput) (how nset oset ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Signal.check_rt_sigprocmask i how nset oset ss eff m
      = CheckOk m' evs) :
    m' = m ∨ ∃ new, m' = sigmask_deliver_model new m := by
  unfold Checks.Sys.Kernel.Signal.check_rt_sigprocmask at h
  cases hss : bv_eqb ss (Z_to_bv 64 NSIG_BYTES) with
  | false =>
    simp only [hss, Bool.not_false, ↓reduceIte] at h
    exact Or.inl (check_ret_only_model h)
  | true =>
  simp only [hss, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hn : w_is0 nset with
  | true =>
    simp only [hn, ↓reduceIte] at h
    cases ho : w_is0 oset with
    | true =>
      simp only [ho, ↓reduceIte] at h
      exact Or.inl (check_ret_only_model h)
    | false =>
      simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
      exact Or.inl ((Checks.Sys.Kernel.Signal.check_write_oset_ok_iff _ _ _ _ _ _ _).mp h).1
  | false =>
  simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
  cases hr : sigset_at i.in_mem nset with
  | none =>
    simp only [hr] at h
    exact Or.inl (check_ret_only_model h)
  | some raw =>
  simp only [hr] at h
  cases hh : how_valid how with
  | false =>
    simp only [hh, Bool.not_false, ↓reduceIte] at h
    exact Or.inl (check_ret_only_copyins_model h)
  | true =>
  simp only [hh, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases ho : w_is0 oset with
  | true =>
    simp only [ho, ↓reduceIte] at h
    exact Or.inr ⟨_, check_ret_only_copyins_model h⟩
  | false =>
    simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
    exact Or.inr ⟨_,
      ((Checks.Sys.Kernel.Signal.check_write_oset_copyins_ok_iff _ _ _ _ _ _ _ _).mp h).1⟩

open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Signal in
/-- `check_rt_sigprocmask` writes the blocked mask, and on a delivery the
kill, and nothing else, so the descriptor subsystem is the one it was
handed: `sigmask_deliver_model`'s two branches are `State.with_sigmask`
and `State.with_killed` over it, each of which rebuilds `ProcState` and
carries `m_fd` across (`State/Model.lean`). -/
theorem check_rt_sigprocmask_fd_state_frame (i : SyscallInput) (how nset oset ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Signal.check_rt_sigprocmask i how nset oset ss eff m
      = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  rcases check_rt_sigprocmask_model_shape i how nset oset ss eff m m' evs h with
    rfl | ⟨new, rfl⟩
  · rfl
  · unfold sigmask_deliver_model
    split <;> rfl

/-- `vm_wf` × `rt_sigprocmask`: the ledger fact above. -/
theorem vm_wf_arm_rt_sigprocmask : arm_preserves inv_vm_wf arm_rt_sigprocmask :=
  Arms.arm_rt_sigprocmask_preserves_vm

/-- `fd_table_unique` × `rt_sigprocmask`: the mask is not the descriptor
table; the frame is the one above. -/
theorem fd_table_unique_arm_rt_sigprocmask :
    arm_preserves inv_fd_table_unique arm_rt_sigprocmask :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_rt_sigprocmask
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_table
        (check_rt_sigprocmask_fd_state_frame i _ _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `rt_sigprocmask`: no pipe is touched. -/
theorem pipes_within_capacity_arm_rt_sigprocmask :
    arm_preserves inv_pipes_within_capacity arm_rt_sigprocmask :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_rt_sigprocmask
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes
        (check_rt_sigprocmask_fd_state_frame i _ _ _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
