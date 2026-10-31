import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Fcntl
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Rocq's `arm_fcntl`, `ca_check_arm_fcntl`, `ca_witness_arm_fcntl`
and `sa_spec_arm_fcntl` in `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`,
and `check_fcntl_frame` in `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`,
read identically at f44244ad6b80, a71fd38a0857 and HEAD when this registration
was written. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/-- fcntl (25). `SYSCALL_DEFINE3(fcntl, unsigned int, fd, unsigned int,
cmd, unsigned long, arg)` (fs/fcntl.c:574, Linux v6.18.46, commit
1f99e9ab748f) takes a0, a1 and a2 in that order through riscv64's
`SC_RISCV_REGS_TO_ARGS` (arch/riscv/include/asm/syscall_wrapper.h:21-24,
same version). `__SC_CAST` (include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46) casts to
those declared types: `unsigned int` retains the low 32 bits of a0/a1,
which `fd32`/`cmd32` in `Sys/Syscall.lean` compute, and `unsigned long`
retains the 64-bit a2 word. The witness projection
`ca_witness_arm_fcntl` pins that same decoding for the witness. -/
def arm_fcntl : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 25 (fun i => Sys.Fs.Fcntl.fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i)
  ca_check := fun i eff m => Checks.Sys.Fs.Fcntl.check_fcntl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) eff m
  ca_witness := fun i m => Checks.Sys.Fs.Fcntl.fcntl_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Fcntl.check_fcntl_sound_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Fcntl.check_fcntl_sound_unmodeled (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Fcntl.check_fcntl_complete_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Fcntl.check_fcntl_complete_unmodeled (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) m i eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.Fcntl.fcntl_witness_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_fcntl (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_fcntl.ca_check i eff m = Checks.Sys.Fs.Fcntl.check_fcntl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_fcntl (i : SyscallInput) (m : Model) :
    arm_fcntl.ca_witness i m = Checks.Sys.Fs.Fcntl.fcntl_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) m := rfl
@[arm_unfold] theorem sa_spec_arm_fcntl (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_fcntl.ca_arm.sa_spec i m o = Sys.Fs.Fcntl.fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_fcntl : ca_no arm_fcntl = 25 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Fcntl
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Fcntl
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- Lean-only: the descriptor-view facts below need the post-model itself,
rather than the VM projection of the checker's existing frame lemma.
This proof must change if an accepted command starts recording fd state. -/
theorem check_fcntl_ok_model (fd cmd arg : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_fcntl fd cmd arg eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  unfold check_fcntl at h
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at h
    exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
  | some e =>
    simp only [hfd] at h
    cases hd : bv_eqb cmd F_SETFD with
    | true =>
      simp only [hd, ↓reduceIte] at h
      exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
    | false =>
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
      cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on e arg) with
      | true =>
        simp only [hl, ↓reduceIte] at h
        exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
      | false =>
        simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
        cases hg : bv_eqb cmd F_GETFL with
        | true =>
          simp only [hg, ↓reduceIte] at h
          cases hgf : getfl_f_flags e with
          | some fl =>
            simp only [hgf] at h
            exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
          | none =>
            simp only [hgf] at h
            cases h
        | false =>
          simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
          cases h

/-- The VM obligation uses the C ticket's frame lemma. -/
theorem arm_fcntl_preserves_vm : arm_preserves_vm arm_fcntl :=
  arm_preserves_of_frame arm_fcntl (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Fs.Fcntl.check_fcntl_frame _ _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- Lean-only descriptor projection of `check_fcntl_ok_model`; the Rocq
registry has no descriptor-state invariant requiring this projection. -/
theorem check_fcntl_fd_state_frame (fd cmd arg : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.Fcntl.check_fcntl fd cmd arg eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  obtain ⟨rfl, -⟩ := Arms.check_fcntl_ok_model fd cmd arg eff m m' evs h
  rfl

/-- The registry's VM entry, through the existing frame lemma. -/
theorem vm_wf_arm_fcntl : arm_preserves inv_vm_wf arm_fcntl :=
  Arms.arm_fcntl_preserves_vm

/-- The descriptor-table view of `check_fcntl_fd_state_frame`. -/
theorem fd_table_unique_arm_fcntl : arm_preserves inv_fd_table_unique arm_fcntl :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_fcntl
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_table (check_fcntl_fd_state_frame _ _ _ eff m m' evs h))

/-- The pipe-buffer view of `check_fcntl_fd_state_frame`. -/
theorem pipes_within_capacity_arm_fcntl : arm_preserves inv_pipes_within_capacity arm_fcntl :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_fcntl
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes (check_fcntl_fd_state_frame _ _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
