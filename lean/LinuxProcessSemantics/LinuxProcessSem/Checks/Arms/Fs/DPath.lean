import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.DPath
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Fs.DPath — getcwd on the checked surface

The registration of `Checks/Sys/Fs/DPath.lean`'s checker in
`checked_table`.  `tools/gen_lean_checked.py`'s docstring is the shape
this file has to have, and what it renders from it.

WHY THE FRAME LEMMAS ARE HERE and not beside the checker.  The checker's
header hands Rocq's `check_getcwd_frame` to this registration, and a
registration writes the arm file and the arm's Cases twins, not the
checker, which is its C ticket's (`docs/lean-port/BRIEF.md` section 4).
So they are stated here, in the sections whose facts consume them, as
`Checks/Arms/Fs/Timerfd.lean` states its own.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arm is the row of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table` for 17 (`arm_getcwd`), read at that commit. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### getcwd (17) -/

/-- getcwd (17).  `SYSCALL_DEFINE2(getcwd, char __user *, buf, unsigned
long, size)` (fs/d_path.c:412, Linux v6.18.46): `buf` is register `a0`
and `size` is `a1` — riscv64's wrapper passes the registers in order
(`SC_RISCV_REGS_TO_ARGS` under `CONFIG_64BIT`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46) — and
each reaches `__do_sys_getcwd` through `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46).  An
`unsigned long` is the register's width on riscv64, so the cast keeps
all 64 bits of `a1`.  So the arm hands the spec, the checker and the
witness `in_arg i 1` whole, the reading Rocq's `arm_getcwd` applies.
`ca_arm` is the term `Sys/Registry/Fs/DPath.lean`'s row builds, which
`checked_table_arms` checks. -/
def arm_getcwd : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 17 (fun i => Sys.Fs.DPath.getcwd_spec (in_arg i 1) i)
  ca_check := fun i eff m => Checks.Sys.Fs.DPath.check_getcwd (in_arg i 1) eff m
  ca_witness := fun i m => Checks.Sys.Fs.DPath.getcwd_witness (in_arg i 1) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.DPath.check_getcwd_sound_ok (in_arg i 1) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.DPath.check_getcwd_sound_unmodeled (in_arg i 1) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.DPath.check_getcwd_complete_ok (in_arg i 1) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.DPath.check_getcwd_complete_unmodeled (in_arg i 1) m i eff h
  ca_receptive := fun i m => Checks.Sys.Fs.DPath.getcwd_witness_ok (in_arg i 1) i m

@[arm_unfold] theorem ca_check_arm_getcwd (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_getcwd.ca_check i eff m = Checks.Sys.Fs.DPath.check_getcwd (in_arg i 1) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_getcwd (i : SyscallInput) (m : Model) :
    arm_getcwd.ca_witness i m = Checks.Sys.Fs.DPath.getcwd_witness (in_arg i 1) m := rfl
@[arm_unfold] theorem sa_spec_arm_getcwd (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_getcwd.ca_arm.sa_spec i m o = Sys.Fs.DPath.getcwd_spec (in_arg i 1) i m o := rfl
@[arm_unfold] theorem ca_no_arm_getcwd : ca_no arm_getcwd = 17 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- Every answer `check_getcwd` accepts hands back the model it was handed
and no event.  Lean-only: the two frame lemmas below are its projections,
where Rocq's `check_getcwd_frame` closes the same case split by its
`vm_frame2` tactic.  The accepted answers are the bare errno returns of
`SYSCALL_DEFINE2(getcwd)` at `size ≤ 1`, every one of them decided
before the copy out to `buf` at fs/d_path.c:441 (Linux v6.18.46, commit
1f99e9ab748f); above that band the checker declines. -/
theorem check_getcwd_ok_model (size : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.DPath.check_getcwd size eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  unfold Checks.Sys.Fs.DPath.check_getcwd at h
  split at h
  · cases h
  · split at h
    · split at h
      · injection h with hm hevs
        exact ⟨hm.symm, hevs.symm⟩
      · split at h
        · injection h with hm hevs
          exact ⟨hm.symm, hevs.symm⟩
        · cases h
    · cases h

/-- Rocq: `VmMapsDisjoint.check_getcwd_frame`.  The ledger is the one the
checker was handed, by `check_getcwd_ok_model`.  A `*_frame` rather than a
`*_preserves`: nothing is written for `vm_wf` to be re-established over.
This stops being the right shape if the checker ever accepts the success
branch the spec declines today, whose `copy_to_user` writes `buf`. -/
theorem check_getcwd_frame (size : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.DPath.check_getcwd size eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨rfl, -⟩ := check_getcwd_ok_model size eff m m' evs h
  rfl

/-- `getcwd` (17): the accepted model is the model handed in, so the
ledger is what it was (`check_getcwd_frame`, above). -/
theorem arm_getcwd_preserves_vm : arm_preserves_vm arm_getcwd :=
  arm_preserves_of_frame arm_getcwd (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_getcwd_frame _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## The descriptor-state frame lemma

Lean-only: the Rocq tree registers no invariant over `m_fd`, so this has
no Rocq twin.  The two registry entries beside `vm_wf` read the descriptor
subsystem, and one frame lemma over the whole record answers both. -/

/-- `check_getcwd` hands back the model it was handed on every answer it
accepts (`check_getcwd_ok_model`), so the descriptor subsystem is the one
it was handed: the body of `SYSCALL_DEFINE2(getcwd)` (fs/d_path.c:412-448,
Linux v6.18.46) reads `current->fs` and takes no descriptor. -/
theorem check_getcwd_fd_state_frame (size : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.DPath.check_getcwd size eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  obtain ⟨rfl, -⟩ := Arms.check_getcwd_ok_model size eff m m' evs h
  rfl

/-- `vm_wf` × `getcwd`: the ledger fact above. -/
theorem vm_wf_arm_getcwd : arm_preserves inv_vm_wf arm_getcwd :=
  Arms.arm_getcwd_preserves_vm

/-- `fd_table_unique` × `getcwd`. -/
theorem fd_table_unique_arm_getcwd : arm_preserves inv_fd_table_unique arm_getcwd :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_getcwd
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_table (check_getcwd_fd_state_frame _ eff m m' evs h))

/-- `pipes_within_capacity` × `getcwd`. -/
theorem pipes_within_capacity_arm_getcwd :
    arm_preserves inv_pipes_within_capacity arm_getcwd :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_getcwd
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes (check_getcwd_fd_state_frame _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
