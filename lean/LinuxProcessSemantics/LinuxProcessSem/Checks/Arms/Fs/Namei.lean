import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Namei
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # LinuxProcessSem.Checks.Arms.Fs.Namei — unlinkat on the checked surface

The registration follows the arm-file contract in
`tools/gen_lean_checked.py`; the checker supplies the frame lemmas.
Rocq's `arm_unlinkat`, its projection lemmas and `arm_unfold` hints in
`theories/LinuxProcessSem/Checks/Sys/Dispatch.v` read the same at the
baseline and HEAD (753eaff8c), as does the statement of
`check_unlinkat_frame` in `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`,
whose HEAD proof additionally unfolds `check_unlinkat_tmp` and
`check_unlink_found`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/-- `SYSCALL_DEFINE3(unlinkat, int, dfd, const char __user *, pathname,
int, flag)` (fs/namei.c:4775-4782, Linux v6.18.46, commit 1f99e9ab748f)
receives a0, a1 and a2 in order through `SC_RISCV_REGS_TO_ARGS`
(arch/riscv/include/asm/syscall_wrapper.h:21-24); `__SYSCALL_DEFINEx`
(:82-96, especially :88) applies `__SC_CAST`
(include/linux/syscalls.h:132, Linux v6.18.46), at that same commit.
The `int dfd` cast keeps a0's low 32 bits, represented by `fd32` in
`Sys/Syscall.lean`, while the pathname pointer keeps the register width.
The arm passes a2 whole because `modeled_unlink_flags` and `unlink_rmdir`
in `Sys/Fs/Namei.lean` apply `flag32` themselves, matching the `int flag`
cast before the flag tests at fs/namei.c:4777-4780 (Linux v6.18.46). -/
def arm_unlinkat : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 35 (fun i => Sys.Fs.Namei.unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.Namei.check_unlinkat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.Namei.unlinkat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Namei.check_unlinkat_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Namei.check_unlinkat_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Namei.check_unlinkat_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Namei.check_unlinkat_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.Namei.unlinkat_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_unlinkat (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_unlinkat.ca_check i eff m =
      Checks.Sys.Fs.Namei.check_unlinkat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_unlinkat (i : SyscallInput) (m : Model) :
    arm_unlinkat.ca_witness i m =
      Checks.Sys.Fs.Namei.unlinkat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl
@[arm_unfold] theorem sa_spec_arm_unlinkat (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_unlinkat.ca_arm.sa_spec i m o =
      Sys.Fs.Namei.unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_unlinkat : ca_no arm_unlinkat = 35 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- The checker's existing ledger frame supplies the arm obligation. -/
theorem arm_unlinkat_preserves_vm : arm_preserves_vm arm_unlinkat :=
  arm_preserves_of_frame arm_unlinkat (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Fs.Namei.check_unlinkat_frame i _ _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- The VM obligation, through the registry's ledger view. -/
theorem vm_wf_arm_unlinkat : arm_preserves inv_vm_wf arm_unlinkat :=
  Arms.arm_unlinkat_preserves_vm

/-- The descriptor table is a projection of the existing descriptor frame. -/
theorem fd_table_unique_arm_unlinkat : arm_preserves inv_fd_table_unique arm_unlinkat :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_unlinkat
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_table
        (Checks.Sys.Fs.Namei.check_unlinkat_fd_state_frame i _ _ _ eff m m' evs h))

/-- The pipe table is the other descriptor-frame projection. -/
theorem pipes_within_capacity_arm_unlinkat : arm_preserves inv_pipes_within_capacity arm_unlinkat :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_unlinkat
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes
        (Checks.Sys.Fs.Namei.check_unlinkat_fd_state_frame i _ _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
