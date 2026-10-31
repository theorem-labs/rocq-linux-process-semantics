import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.Time
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Kernel.Time.Time — gettimeofday on the checked surface

The registration of `Checks/Sys/Kernel/Time/Time.lean`'s checker in
`checked_table`, in the one file that registration writes; the shape
`tools/gen_lean_checked.py` reads is its docstring's, and
`Checks/Arms/Kernel/Exit.lean` says what each of the three sections below
is for.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arm is the row of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table`, read at that commit.

THE TWO FRAME LEMMAS LIVE HERE, not beside the checker, because the
checker's file belongs to the ticket that ported it and this registration
creates or edits no hub but this file.  The tree's rule, which
`Checks/Arms/Kernel/Exit.lean` states, is that a checker's frame lemma
lives beside the checker; `check_gettimeofday_frame` is the first Rocq
twin to live in an arm file instead, and moving both lemmas to
`Checks/Sys/Kernel/Time/Time.lean` is owed and changes nothing but their
home.  Rocq closes `check_gettimeofday_frame` in
`Checks/VmMapsDisjoint.v` by unfolding the checker; the twin below reads
the checker's inversion lemma instead: an accepted answer hands back the
model it was given (`check_gettimeofday_ok_inv`'s first conjunct), so
every projection of it, the mapping ledger and the descriptor state
alike, is unchanged. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### gettimeofday (169) -/

/-- gettimeofday (169).  The arguments are registers `a0` and `a1`, read
whole: `SYSCALL_DEFINE2(gettimeofday, struct __kernel_old_timeval __user *,
tv, struct timezone __user *, tz)` (kernel/time/time.c:140-141, Linux
v6.18.46) declares two pointers; `SC_RISCV_REGS_TO_ARGS`
(arch/riscv/include/asm/syscall_wrapper.h:21-23, Linux v6.18.46) hands
them `regs->orig_a0` and `regs->a1` in that order, and `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46) casts from
the 64-bit register without narrowing.  `ca_arm` is the term
`Sys/Registry/Kernel/Time/Time.lean`'s `gettimeofday_arm` builds, which
`checked_table_arms` checks. -/
def arm_gettimeofday : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 169
    (fun i => Sys.Kernel.Time.Time.gettimeofday_spec (in_arg i 0) (in_arg i 1) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Time.Time.check_gettimeofday i (in_arg i 0) (in_arg i 1) eff m
  ca_witness := fun i m =>
    Checks.Sys.Kernel.Time.Time.gettimeofday_witness (in_arg i 0) (in_arg i 1) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Time.Time.check_gettimeofday_sound_ok i (in_arg i 0) (in_arg i 1) eff m m'
      evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Time.Time.check_gettimeofday_sound_unmodeled i (in_arg i 0) (in_arg i 1)
      eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Time.Time.check_gettimeofday_complete_ok i (in_arg i 0) (in_arg i 1) eff m
      m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Time.Time.check_gettimeofday_complete_unmodeled i (in_arg i 0) (in_arg i 1)
      m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Time.Time.gettimeofday_witness_ok i (in_arg i 0) (in_arg i 1) m

@[arm_unfold] theorem ca_check_arm_gettimeofday (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    arm_gettimeofday.ca_check i eff m
      = Checks.Sys.Kernel.Time.Time.check_gettimeofday i (in_arg i 0) (in_arg i 1) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_gettimeofday (i : SyscallInput) (m : Model) :
    arm_gettimeofday.ca_witness i m
      = Checks.Sys.Kernel.Time.Time.gettimeofday_witness (in_arg i 0) (in_arg i 1) i m := rfl
@[arm_unfold] theorem sa_spec_arm_gettimeofday (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_gettimeofday.ca_arm.sa_spec i m o
      = Sys.Kernel.Time.Time.gettimeofday_spec (in_arg i 0) (in_arg i 1) i m o := rfl
@[arm_unfold] theorem ca_no_arm_gettimeofday : ca_no arm_gettimeofday = 169 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- Rocq's `check_gettimeofday_frame` (`Checks/VmMapsDisjoint.v`): an
accepted answer leaves the mapping ledger as it was.  The checker only
ever accepts with the model it was handed, which
`check_gettimeofday_ok_inv` states. -/
theorem check_gettimeofday_frame (i : SyscallInput) (tv tz : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Time.Time.check_gettimeofday i tv tz eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨rfl, _⟩ := Checks.Sys.Kernel.Time.Time.check_gettimeofday_ok_inv i tv tz eff m m' evs h
  rfl

/-- `gettimeofday` (169): the ledger is untouched (`check_gettimeofday_frame`). -/
theorem arm_gettimeofday_preserves_vm : arm_preserves_vm arm_gettimeofday :=
  arm_preserves_of_frame arm_gettimeofday (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_gettimeofday_frame i _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `check_gettimeofday` accepts only with the model it was handed, so the
descriptor subsystem is the one it was handed.  Lean-only: the Rocq tree
registers no `m_fd` invariant, so there is no twin.  Same proof as
`check_gettimeofday_frame` with a different projection at the end. -/
theorem check_gettimeofday_fd_state_frame (i : SyscallInput) (tv tz : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Time.Time.check_gettimeofday i tv tz eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  obtain ⟨rfl, _⟩ := Checks.Sys.Kernel.Time.Time.check_gettimeofday_ok_inv i tv tz eff m m' evs h
  rfl

/-- `vm_wf` × `gettimeofday`: the ledger fact above. -/
theorem vm_wf_arm_gettimeofday : arm_preserves inv_vm_wf arm_gettimeofday :=
  Arms.arm_gettimeofday_preserves_vm

/-- `fd_table_unique` × `gettimeofday`. -/
theorem fd_table_unique_arm_gettimeofday : arm_preserves inv_fd_table_unique arm_gettimeofday :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_gettimeofday (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_gettimeofday_fd_state_frame i _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `gettimeofday`. -/
theorem pipes_within_capacity_arm_gettimeofday :
    arm_preserves inv_pipes_within_capacity arm_gettimeofday :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_gettimeofday
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes (check_gettimeofday_fd_state_frame i _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
