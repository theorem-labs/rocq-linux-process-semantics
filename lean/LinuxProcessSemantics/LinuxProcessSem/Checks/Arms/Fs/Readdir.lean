import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Readdir
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Fs.Readdir — getdents64 on the checked surface

The registration of `Checks/Sys/Fs/Readdir.lean`'s checker in
`checked_table`, in the shape read by `tools/gen_lean_checked.py`.
The frame lemma `Checks.Sys.Fs.Readdir.check_getdents64_frame` is beside
the checker; this file consumes it.

Rocq's `arm_getdents64` in `Checks/Sys/Dispatch.v` was read at the
baseline above and at f44244ad6b80: its text is identical. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### getdents64 (61) -/

/-- getdents64 (61).  Linux v6.18.46 (commit 1f99e9ab748f),
fs/readdir.c:397-398, `SYSCALL_DEFINE3(getdents64)`, declares fd and
count as unsigned int.  The riscv64 register order comes from
`SC_RISCV_REGS_TO_ARGS` under CONFIG_64BIT
(arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46,
commit 1f99e9ab748f); `__SC_CAST`
(include/linux/syscalls.h:132, applied by `__SYSCALL_DEFINEx` at
arch/riscv/include/asm/syscall_wrapper.h:88) casts a0 to unsigned int,
hence `fd32`.  These locations are Linux v6.18.46, commit 1f99e9ab748f.
Count is handed whole to the spec, whose `getdents64_ctx_count` reads
its low half as the int assigned at fs/readdir.c:403
(`SYSCALL_DEFINE3(getdents64)`; include/linux/fs.h:2210,
struct dir_context, Linux v6.18.46, commit 1f99e9ab748f).
The spec leaves a1 unread: this is the reading Rocq's `arm_getdents64`
applies.  `checked_table_arms` checks the arm against
`Sys/Registry/Fs/Readdir.lean`'s term. -/
def arm_getdents64 : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 61 (fun i => Sys.Fs.Readdir.getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i)
  ca_check := fun i eff m => Checks.Sys.Fs.Readdir.check_getdents64 (fd32 (in_arg i 0)) (in_arg i 2) eff m
  ca_witness := fun i m => Checks.Sys.Fs.Readdir.getdents64_witness (fd32 (in_arg i 0)) (in_arg i 2) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Readdir.check_getdents64_sound_ok (fd32 (in_arg i 0)) (in_arg i 2) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Readdir.check_getdents64_sound_unmodeled (fd32 (in_arg i 0)) (in_arg i 2) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Readdir.check_getdents64_complete_ok (fd32 (in_arg i 0)) (in_arg i 2) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Readdir.check_getdents64_complete_unmodeled (fd32 (in_arg i 0)) (in_arg i 2) m i eff h
  ca_receptive := fun i m => Checks.Sys.Fs.Readdir.getdents64_witness_ok (fd32 (in_arg i 0)) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_getdents64 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_getdents64.ca_check i eff m = Checks.Sys.Fs.Readdir.check_getdents64 (fd32 (in_arg i 0)) (in_arg i 2) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_getdents64 (i : SyscallInput) (m : Model) :
    arm_getdents64.ca_witness i m = Checks.Sys.Fs.Readdir.getdents64_witness (fd32 (in_arg i 0)) (in_arg i 2) m := rfl
@[arm_unfold] theorem sa_spec_arm_getdents64 (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_getdents64.ca_arm.sa_spec i m o = Sys.Fs.Readdir.getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_getdents64 : ca_no arm_getdents64 = 61 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- Lean-only model and event frame.  The directory gate is split without
reducing its signed-count conversion, following `check_getdents64_frame`. -/
theorem check_getdents64_ok_model (fd count : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.Readdir.check_getdents64 fd count eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  unfold Checks.Sys.Fs.Readdir.check_getdents64 at h
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    rw [hfd] at h
    exact ⟨((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1,
      ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.2⟩
  | some e =>
    rw [hfd] at h
    cases e
    case FdDir =>
      dsimp only at h
      split at h
      · split at h
        · split at h
          · cases h; exact ⟨rfl, rfl⟩
          · split at h
            · cases h; exact ⟨rfl, rfl⟩
            · cases h
        · cases h
      · cases h
    case FdFileA => dsimp only at h; cases h
    case FdFileRW => dsimp only at h; cases h
    all_goals exact ⟨((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1,
      ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.2⟩

/-- Rocq's VM frame, consumed from the checker. -/
theorem arm_getdents64_preserves_vm : arm_preserves_vm arm_getdents64 :=
  arm_preserves_of_frame arm_getdents64 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Fs.Readdir.check_getdents64_frame _ _ eff m m' evs h)

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

/-- Linux takes fd_pos in `SYSCALL_DEFINE3(getdents64)`
(fs/readdir.c:400, Linux v6.18.46, commit 1f99e9ab748f).
The accepted failure answers return the model unchanged
(`check_getdents64_ok_model`), which yields this descriptor-state frame.
This is a model frame, not a claim about f_pos after a successful listing;
the checker declines the directory branch with room. -/
theorem check_getdents64_fd_state_frame (fd count : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.Readdir.check_getdents64 fd count eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  exact congrArg Model.m_fd (Arms.check_getdents64_ok_model fd count eff m m' evs h).1

/-- `vm_wf` × `getdents64`: the ledger fact above. -/
theorem vm_wf_arm_getdents64 : arm_preserves inv_vm_wf arm_getdents64 :=
  Arms.arm_getdents64_preserves_vm

/-- `fd_table_unique` × `getdents64`. -/
theorem fd_table_unique_arm_getdents64 : arm_preserves inv_fd_table_unique arm_getdents64 :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_getdents64
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_table (check_getdents64_fd_state_frame _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `getdents64`. -/
theorem pipes_within_capacity_arm_getdents64 :
    arm_preserves inv_pipes_within_capacity arm_getdents64 :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_getdents64
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes (check_getdents64_fd_state_frame _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
