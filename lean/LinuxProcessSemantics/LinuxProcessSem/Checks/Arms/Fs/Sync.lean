import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Sync
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # LinuxProcessSem.Checks.Arms.Fs.Sync — fsync and fdatasync on the checked surface

The registration of `Checks/Sys/Fs/Sync.lean` follows the contract in
`tools/gen_lean_checked.py`: the arms and their unfolding facts live in
`Checks.Sys.Table`, the ledger facts in `Checks.VmMapsDisjoint.Arms`,
and the invariant facts in `Checks.Invariants`.

The two arms and their three unfolding lemmas in
`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`, and `check_fsync_frame`
in `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, read identically at
f44244ad6b80, a71fd38a0857 and HEAD (753eaff8c).

The VM facts consume the existing checker frame; the Lean-only descriptor
view frames share `check_fsync_ok_model`, so their argument has one home. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/-- fsync (82). `SYSCALL_DEFINE1(fsync, unsigned int, fd)`
(fs/sync.c:215, Linux v6.18.46, commit 1f99e9ab748f) calls
`do_fsync(fd, 0)` (fs/sync.c:205-213, 217).
`SC_RISCV_REGS_TO_ARGS` supplies `orig_a0` first
(arch/riscv/include/asm/syscall_wrapper.h:21-24), and
`__SYSCALL_DEFINEx` (:82-95) applies `__SC_CAST`
(include/linux/syscalls.h:132, Linux v6.18.46) at wrapper line 88.
The `unsigned int` cast keeps the low 32 bits of a0; `Sys.Syscall.fd32`
computes that cut via `abi_low32` in `Sys/Syscall.lean`.
The spec term is the registry row's, checked by `checked_table_arms`. -/
def arm_fsync : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 82 (fun i => Sys.Fs.Sync.fsync_spec (Sys.Syscall.fd32 (in_arg i 0)) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.Sync.check_fsync (Sys.Syscall.fd32 (in_arg i 0)) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.Sync.fsync_witness (Sys.Syscall.fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Sync.check_fsync_sound_ok (Sys.Syscall.fd32 (in_arg i 0)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Sync.check_fsync_sound_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Sync.check_fsync_complete_ok (Sys.Syscall.fd32 (in_arg i 0)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Sync.check_fsync_complete_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) m i eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.Sync.fsync_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) i m

@[arm_unfold] theorem ca_check_arm_fsync (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_fsync.ca_check i eff m
      = Checks.Sys.Fs.Sync.check_fsync (Sys.Syscall.fd32 (in_arg i 0)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_fsync (i : SyscallInput) (m : Model) :
    arm_fsync.ca_witness i m = Checks.Sys.Fs.Sync.fsync_witness (Sys.Syscall.fd32 (in_arg i 0)) m := rfl
@[arm_unfold] theorem sa_spec_arm_fsync (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_fsync.ca_arm.sa_spec i m o = Sys.Fs.Sync.fsync_spec (Sys.Syscall.fd32 (in_arg i 0)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_fsync : ca_no arm_fsync = 82 := rfl

/-- fdatasync (83). `SYSCALL_DEFINE1(fdatasync, unsigned int, fd)`
(fs/sync.c:220, Linux v6.18.46, commit 1f99e9ab748f) calls
`do_fsync(fd, 1)` (fs/sync.c:205-213, 222).
`SC_RISCV_REGS_TO_ARGS` supplies `orig_a0` first
(arch/riscv/include/asm/syscall_wrapper.h:21-24), and
`__SYSCALL_DEFINEx` (:82-95) applies `__SC_CAST`
(include/linux/syscalls.h:132, Linux v6.18.46) at wrapper line 88.
The `unsigned int` cast keeps the low 32 bits of a0; `Sys.Syscall.fd32`
computes that cut via `abi_low32` in `Sys/Syscall.lean`.
The shared checker follows `Sys/Fs/Sync.lean`'s `fsync_spec` docstring:
the two early errno tests precede the use of `datasync`, and the successful
flush distinction is outside the model's durability state; that docstring
also records the filesystem premise and the writeback-error bound.
The spec term is the registry row's, checked by `checked_table_arms`. -/
def arm_fdatasync : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 83 (fun i => Sys.Fs.Sync.fsync_spec (Sys.Syscall.fd32 (in_arg i 0)) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.Sync.check_fsync (Sys.Syscall.fd32 (in_arg i 0)) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.Sync.fsync_witness (Sys.Syscall.fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Sync.check_fsync_sound_ok (Sys.Syscall.fd32 (in_arg i 0)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Sync.check_fsync_sound_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Sync.check_fsync_complete_ok (Sys.Syscall.fd32 (in_arg i 0)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Sync.check_fsync_complete_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) m i eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.Sync.fsync_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) i m

@[arm_unfold] theorem ca_check_arm_fdatasync (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_fdatasync.ca_check i eff m
      = Checks.Sys.Fs.Sync.check_fsync (Sys.Syscall.fd32 (in_arg i 0)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_fdatasync (i : SyscallInput) (m : Model) :
    arm_fdatasync.ca_witness i m = Checks.Sys.Fs.Sync.fsync_witness (Sys.Syscall.fd32 (in_arg i 0)) m := rfl
@[arm_unfold] theorem sa_spec_arm_fdatasync (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_fdatasync.ca_arm.sa_spec i m o = Sys.Fs.Sync.fsync_spec (Sys.Syscall.fd32 (in_arg i 0)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_fdatasync : ca_no arm_fdatasync = 83 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- The existing `check_fsync_frame` supplies the ledger equality. -/
theorem arm_fsync_preserves_vm : arm_preserves_vm arm_fsync :=
  arm_preserves_of_frame arm_fsync (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Fs.Sync.check_fsync_frame _ eff m m' evs h)

/-- The existing `check_fsync_frame` supplies the ledger equality. -/
theorem arm_fdatasync_preserves_vm : arm_preserves_vm arm_fdatasync :=
  arm_preserves_of_frame arm_fdatasync (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Fs.Sync.check_fsync_frame _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- Lean-only: the accepted post-model and events, used by the descriptor
view frames. The return-only interface follows fs/sync.c:191-202
(`vfs_fsync`) and fs/sync.c:205-213 (`do_fsync`), Linux v6.18.46,
commit 1f99e9ab748f. -/
theorem check_fsync_ok_model (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.Sync.check_fsync fd eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  unfold Checks.Sys.Fs.Sync.check_fsync at h
  generalize fd_lookup (m_fds m) fd = r at h
  cases r with
  | none =>
    dsimp only at h
    rw [check_ret_only_ok_iff] at h
    exact ⟨h.2.1, h.2.2⟩
  | some e =>
    cases e
    -- `FdFileA` and `FdFileRW` answer 0 with the other file kinds now, so
    -- the return-only closer below carries them too.
    all_goals
      dsimp only at h
      rw [check_ret_only_ok_iff] at h
      exact ⟨h.2.1, h.2.2⟩

/-- The descriptor-state projection of `check_fsync_ok_model`. -/
theorem check_fsync_fd_state_frame (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.Sync.check_fsync fd eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  obtain ⟨rfl, -⟩ := check_fsync_ok_model fd eff m m' evs h
  rfl

/-- The descriptor-table view of `check_fsync_fd_state_frame`. -/
theorem check_fsync_fds_frame (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.Sync.check_fsync fd eff m = CheckOk m' evs) :
    m_fds m' = m_fds m :=
  congrArg FdState.fdst_table (check_fsync_fd_state_frame fd eff m m' evs h)

/-- The pipe view of `check_fsync_fd_state_frame`. -/
theorem check_fsync_pipes_frame (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.Sync.check_fsync fd eff m = CheckOk m' evs) :
    m_pipes m' = m_pipes m :=
  congrArg FdState.fdst_pipes (check_fsync_fd_state_frame fd eff m m' evs h)

/-- The ledger invariant through the existing frame. -/
theorem vm_wf_arm_fsync : arm_preserves inv_vm_wf arm_fsync :=
  Arms.arm_fsync_preserves_vm

/-- The `fd_table_unique` invariant through its shared view frame. -/
theorem fd_table_unique_arm_fsync : arm_preserves inv_fd_table_unique arm_fsync :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_fsync
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact check_fsync_fds_frame _ eff m m' evs h)

/-- The `pipes_within_capacity` invariant through its shared view frame. -/
theorem pipes_within_capacity_arm_fsync : arm_preserves inv_pipes_within_capacity arm_fsync :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_fsync
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact check_fsync_pipes_frame _ eff m m' evs h)

/-- The ledger invariant through the existing frame. -/
theorem vm_wf_arm_fdatasync : arm_preserves inv_vm_wf arm_fdatasync :=
  Arms.arm_fdatasync_preserves_vm

/-- The `fd_table_unique` invariant through its shared view frame. -/
theorem fd_table_unique_arm_fdatasync : arm_preserves inv_fd_table_unique arm_fdatasync :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_fdatasync
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact check_fsync_fds_frame _ eff m m' evs h)

/-- The `pipes_within_capacity` invariant through its shared view frame. -/
theorem pipes_within_capacity_arm_fdatasync : arm_preserves inv_pipes_within_capacity arm_fdatasync :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_fdatasync
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact check_fsync_pipes_frame _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
