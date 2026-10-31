import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Locks
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # LinuxProcessSem.Checks.Arms.Fs.Locks — flock on the checked surface

The registration of `Checks/Sys/Fs/Locks.lean`'s checker in
`checked_table`, in the shape `tools/gen_lean_checked.py` reads.
The baseline above is where the row for 32 (`arm_flock`) was read in
`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`, with its unfolding
lemmas. The checker's `check_flock_frame` twins the ledger fact in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v` at that commit.
The descriptor-state frame below is Lean-only: Rocq has no corresponding
invariant registry. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/-- flock (32). `SYSCALL_DEFINE2(flock, unsigned int, fd, unsigned int,
cmd)` (fs/locks.c:2135, Linux v6.18.46) declares both arguments as
32-bit unsigned integers. Riscv64's `SC_RISCV_REGS_TO_ARGS`
(arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46) passes
`orig_a0` then `a1`; `__SYSCALL_DEFINEx` applies `__SC_CAST` at
arch/riscv/include/asm/syscall_wrapper.h:82-88 (Linux v6.18.46).
That cast is `(__force t) a` (include/linux/syscalls.h:132, Linux
v6.18.46), so both high halves are discarded before the syscall body.
The arm applies `fd32` and `cmd32` at that boundary to the spec, checker
and witness, as Rocq's `arm_flock` does. `ca_arm` is the term built by
`Sys/Registry/Fs/Locks.lean`, checked by `checked_table_arms`. -/
def arm_flock : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 32 (fun i => Sys.Fs.Locks.flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i)
  ca_check := fun i eff m => Checks.Sys.Fs.Locks.check_flock (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m
  ca_witness := fun i m => Checks.Sys.Fs.Locks.flock_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Locks.check_flock_sound_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Locks.check_flock_sound_unmodeled (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Locks.check_flock_complete_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Locks.check_flock_complete_unmodeled (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m i eff h
  ca_receptive := fun i m => Checks.Sys.Fs.Locks.flock_witness_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m

@[arm_unfold] theorem ca_check_arm_flock (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_flock.ca_check i eff m = Checks.Sys.Fs.Locks.check_flock (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_flock (i : SyscallInput) (m : Model) :
    arm_flock.ca_witness i m = Checks.Sys.Fs.Locks.flock_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m := rfl
@[arm_unfold] theorem sa_spec_arm_flock (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_flock.ca_arm.sa_spec i m o = Sys.Fs.Locks.flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_flock : ca_no arm_flock = 32 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Locks
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Locks

/-- Lean-only helper for the view frames: flock changes lock state, which
this model does not carry. The syscall body (fs/locks.c:2135-2183, Linux
v6.18.46) writes no user memory or descriptor entry; `flock_make_lock`
(:465-475) builds the lock request separately. -/
theorem check_flock_ok_model (fd cmd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_flock fd cmd eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  unfold check_flock at h
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at h
    cases hmand : flock_mand_b cmd <;> cases hok : flock_cmd_ok_b cmd <;>
      simp only [hmand, hok, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, reduceCtorEq] at h
    rw [check_ret_only_ok_iff] at h
    exact h.2
  | some e =>
  simp only [hfd] at h
  cases hmand : flock_mand_b cmd with
  | true =>
    simp only [hmand, ↓reduceIte, reduceCtorEq] at h
  | false =>
  cases hok : flock_cmd_ok_b cmd with
  | false =>
    simp only [hmand, hok, Bool.false_eq_true, Bool.not_false, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    exact h.2
  | true =>
  simp only [hmand, hok, Bool.false_eq_true, Bool.not_true, ↓reduceIte] at h
  cases hun : flock_unlock_b cmd with
  | true =>
    simp only [hun, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    exact h.2
  | false =>
  simp only [hun, Bool.false_eq_true, ↓reduceIte] at h
  cases e with
  | FdFile _ _ => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdFileW _ _ => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdFileA _ _ => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdFileRW _ _ => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdChannel c => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdDir => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdSocket sk => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdPipe id w => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdDevNull rd wr =>
    dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | FdUrandom => dsimp only at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-- The ledger fact from the checker, through the arm boundary. -/
theorem arm_flock_preserves_vm : arm_preserves_vm arm_flock :=
  arm_preserves_of_frame arm_flock (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_flock_frame _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.BvBase
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

/-- The descriptor-state projection of `check_flock_ok_model`: the lock
request in `flock_make_lock` (fs/locks.c:465-475, Linux v6.18.46) carries
its owner without replacing the descriptor or touching pipe contents. -/
theorem check_flock_fd_state_frame (fd cmd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.Locks.check_flock fd cmd eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  obtain ⟨rfl, -⟩ := Arms.check_flock_ok_model fd cmd eff m m' evs h
  rfl

/-- `vm_wf` × `flock`: the ledger fact above. -/
theorem vm_wf_arm_flock : arm_preserves inv_vm_wf arm_flock :=
  Arms.arm_flock_preserves_vm

/-- `fd_table_unique` × `flock`. -/
theorem fd_table_unique_arm_flock : arm_preserves inv_fd_table_unique arm_flock :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_flock
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_table (check_flock_fd_state_frame _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `flock`. -/
theorem pipes_within_capacity_arm_flock :
    arm_preserves inv_pipes_within_capacity arm_flock :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_flock
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes (check_flock_fd_state_frame _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
