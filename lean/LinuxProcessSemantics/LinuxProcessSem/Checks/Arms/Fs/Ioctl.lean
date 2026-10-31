import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Ioctl
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Fs.Ioctl — ioctl on the checked surface

The registration of `Checks/Sys/Fs/Ioctl.lean`'s checker in
`checked_table`.  `tools/gen_lean_checked.py`'s docstring is the shape
this file has to have, and what it renders from it.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains:
`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s `arm_ioctl` and
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`'s `check_ioctl_frame` were read
at that commit, and both read the same at `f44244ad6b80`, the commit the port
plan names, and at HEAD.

THE VM FRAME LEMMA is already beside the checker, where its C ticket put
it, so this registration consumes it without stating another.  The
Lean-only `check_ioctl_ok_model` below supplies the descriptor-state
frame for the other two entries of `Checks/InvariantRegistry.lean`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/-- ioctl (29).  `SYSCALL_DEFINE3(ioctl, unsigned int, fd, unsigned int,
cmd, unsigned long, arg)` (fs/ioctl.c:583, Linux v6.18.46) receives
`orig_a0`, `a1`, `a2` in order through riscv64's `SC_RISCV_REGS_TO_ARGS`
(arch/riscv/include/asm/syscall_wrapper.h:21-24, same version).
`__SC_CAST` (include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46) narrows fd
and cmd to `unsigned int`, so the arm applies `fd32` to a0 and `cmd32`
to a1 for spec, checker and witness, as Rocq's `arm_ioctl` does.
`arg` (a2) is handed to nothing because the spec takes no third
argument: every answering arm is return-only, and the spec file's
docstring explains why -ENOTTY writes nothing through arg.  `ca_arm`
is the registry's term, checked by `checked_table_arms`. -/
def arm_ioctl : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 29 (fun i => Sys.Fs.Ioctl.ioctl_spec (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.cmd32 (in_arg i 1)) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.Ioctl.check_ioctl (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.cmd32 (in_arg i 1)) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.Ioctl.ioctl_witness (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.cmd32 (in_arg i 1)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Ioctl.check_ioctl_sound_ok (Sys.Syscall.fd32 (in_arg i 0))
      (Sys.Syscall.cmd32 (in_arg i 1)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Ioctl.check_ioctl_sound_unmodeled (Sys.Syscall.fd32 (in_arg i 0))
      (Sys.Syscall.cmd32 (in_arg i 1)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Ioctl.check_ioctl_complete_ok (Sys.Syscall.fd32 (in_arg i 0))
      (Sys.Syscall.cmd32 (in_arg i 1)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Ioctl.check_ioctl_complete_unmodeled (Sys.Syscall.fd32 (in_arg i 0))
      (Sys.Syscall.cmd32 (in_arg i 1)) m i eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.Ioctl.ioctl_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.cmd32 (in_arg i 1)) i m

@[arm_unfold] theorem ca_check_arm_ioctl (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_ioctl.ca_check i eff m
      = Checks.Sys.Fs.Ioctl.check_ioctl (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.cmd32 (in_arg i 1)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_ioctl (i : SyscallInput) (m : Model) :
    arm_ioctl.ca_witness i m
      = Checks.Sys.Fs.Ioctl.ioctl_witness (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.cmd32 (in_arg i 1)) m := rfl
@[arm_unfold] theorem sa_spec_arm_ioctl (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_ioctl.ca_arm.sa_spec i m o
      = Sys.Fs.Ioctl.ioctl_spec (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.cmd32 (in_arg i 1)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_ioctl : ca_no arm_ioctl = 29 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- Every accepted answer leaves the model unchanged and emits no event.
Lean-only: the descriptor-state frame below projects this fact, while
Rocq's `VmMapsDisjoint.check_ioctl_frame` uses `vm_frame2` directly. -/
theorem check_ioctl_ok_model (fd req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.Ioctl.check_ioctl fd req eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  unfold Checks.Sys.Fs.Ioctl.check_ioctl at h
  split at h
  · cases h
  · split at h <;>
      first
      | exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
      | cases h
      | (split at h
         · exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
         · cases h)

/-- From `check_ioctl_frame` beside the checker (Rocq: `VmMapsDisjoint.check_ioctl_frame`). -/
theorem arm_ioctl_preserves_vm : arm_preserves_vm arm_ioctl :=
  arm_preserves_of_frame arm_ioctl (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Fs.Ioctl.check_ioctl_frame _ _ eff m m' evs h)

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

/-- `SYSCALL_DEFINE3(ioctl)` installs or drops no descriptor on any path
this checker accepts: -EBADF at fs/ioctl.c:588-589, and -ENOTTY from
`vfs_ioctl` at fs/ioctl.c:44-56 (Linux v6.18.46).  The Lean-only
`check_ioctl_ok_model` supplies the frame over the whole descriptor state. -/
theorem check_ioctl_fd_state_frame (fd req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.Ioctl.check_ioctl fd req eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  obtain ⟨rfl, -⟩ := Arms.check_ioctl_ok_model fd req eff m m' evs h
  rfl

/-- `vm_wf` × `ioctl`: the ledger fact above. -/
theorem vm_wf_arm_ioctl : arm_preserves inv_vm_wf arm_ioctl :=
  Arms.arm_ioctl_preserves_vm

/-- `fd_table_unique` × `ioctl`. -/
theorem fd_table_unique_arm_ioctl : arm_preserves inv_fd_table_unique arm_ioctl :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_ioctl
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_table (check_ioctl_fd_state_frame _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `ioctl`. -/
theorem pipes_within_capacity_arm_ioctl :
    arm_preserves inv_pipes_within_capacity arm_ioctl :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_ioctl
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes (check_ioctl_fd_state_frame _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
