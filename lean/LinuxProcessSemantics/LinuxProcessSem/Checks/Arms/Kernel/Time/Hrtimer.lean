import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.Hrtimer
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Kernel.Time.Hrtimer — nanosleep on the checked surface

The registration of `Checks/Sys/Kernel/Time/Hrtimer.lean`'s checker in
`checked_table`.  `tools/gen_lean_checked.py`'s docstring is the shape
this file has to have, and what it renders from it.

WHY THE FRAME LEMMAS ARE HERE and not beside the checker.  The tree's
rule is that a checker's frame lemma lives beside the checker, and
`Checks/Sys/Kernel/Time/Hrtimer.lean` states none: its header hands the
frame lemma to this registration.  A registration writes the arm file and
the arm's Cases twins, not the checker, which is its C ticket's
(`docs/lean-port/BRIEF.md` section 4), so the lemmas are stated here, in
the sections whose facts consume them, as `Checks/Arms/Fs/Timerfd.lean`
states its own.  Moving them beside the checker changes nothing but their
home.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arm is the row of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table` for 101, and the frame lemma is
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`'s
`check_nanosleep_frame`, both read at that commit. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### nanosleep (101) -/

/-- nanosleep (101).  The five proof fields are the file's own
obligation: an arm that cannot supply them does not exist.  The request
pointer is register `a0` and the remainder pointer `a1`: riscv64's
wrapper passes the registers in order (`SC_RISCV_REGS_TO_ARGS` under
`CONFIG_64BIT`, arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux
v6.18.46), and both parameters of `SYSCALL_DEFINE2(nanosleep, struct
__kernel_timespec __user *, rqtp, struct __kernel_timespec __user *,
rmtp)` (kernel/time/hrtimer.c:2189-2190, Linux v6.18.46) are pointers,
as wide as the register on riscv64, so the `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46) the wrapper
applies keeps every bit of each.  So the arm hands the spec, the checker
and the witness `in_arg i 0` and `in_arg i 1` whole, the reading Rocq's
`arm_nanosleep` applies, and the checker the input itself as well, whose
`in_mem` and `in_wmem` it reads the request and the destination through;
`ca_arm` is the term `Sys/Registry/Kernel/Time/Hrtimer.lean`'s row
builds, which `checked_table_arms` checks. -/
def arm_nanosleep : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 101
    (fun i => Sys.Kernel.Time.Hrtimer.nanosleep_spec (in_arg i 0) (in_arg i 1) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Time.Hrtimer.check_nanosleep i (in_arg i 0) (in_arg i 1) eff m
  ca_witness := fun i m =>
    Checks.Sys.Kernel.Time.Hrtimer.nanosleep_witness (in_arg i 0) (in_arg i 1) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Time.Hrtimer.check_nanosleep_sound_ok i (in_arg i 0) (in_arg i 1)
      eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Time.Hrtimer.check_nanosleep_sound_unmodeled i (in_arg i 0)
      (in_arg i 1) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Time.Hrtimer.check_nanosleep_complete_ok i (in_arg i 0) (in_arg i 1)
      eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Time.Hrtimer.check_nanosleep_complete_unmodeled i (in_arg i 0)
      (in_arg i 1) m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Time.Hrtimer.nanosleep_witness_ok i (in_arg i 0) (in_arg i 1) m

@[arm_unfold] theorem ca_check_arm_nanosleep (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_nanosleep.ca_check i eff m
      = Checks.Sys.Kernel.Time.Hrtimer.check_nanosleep i (in_arg i 0) (in_arg i 1) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_nanosleep (i : SyscallInput) (m : Model) :
    arm_nanosleep.ca_witness i m
      = Checks.Sys.Kernel.Time.Hrtimer.nanosleep_witness (in_arg i 0) (in_arg i 1) i m := rfl
@[arm_unfold] theorem sa_spec_arm_nanosleep (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_nanosleep.ca_arm.sa_spec i m o
      = Sys.Kernel.Time.Hrtimer.nanosleep_spec (in_arg i 0) (in_arg i 1) i m o := rfl
@[arm_unfold] theorem ca_no_arm_nanosleep : ca_no arm_nanosleep = 101 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- What an accepted `nanosleep` does to the model: nothing, or a new
clock.  The accepting leaves of `check_nanosleep` are the -EINVAL,
which `check_ret_only_copyins` answers with the model it was handed; the
completed sleep at either `rmtp`, and the interruption that reports a
remainder, each `with_clock` of the model handed in; and the
interruption at a NULL `rmtp`, which hands that model back.  The two
frame lemmas below are this one read through a projection `with_clock`
does not touch. -/
theorem check_nanosleep_ok_is_a_clock_step (i : SyscallInput) (rqtp rmtp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Time.Hrtimer.check_nanosleep i rqtp rmtp eff m = CheckOk m' evs) :
    m' = m ∨ ∃ t, m' = with_clock t m := by
  unfold Checks.Sys.Kernel.Time.Hrtimer.check_nanosleep at h
  rcases hrq : read_bytes_map i.in_mem rqtp (Z_to_bv 64 16) with _ | req
  · simp only [hrq, reduceCtorEq] at h
  · simp only [hrq] at h
    cases hv : Sys.Kernel.Time.Hrtimer.timespec_valid_b req with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at h
      obtain ⟨-, rfl, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
      exact Or.inl rfl
    | true =>
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hrm : Sys.Syscall.w_is0 rmtp with
      | true =>
        simp only [hrm, ↓reduceIte, check_copyins] at h
        cases hc : access_ranges_eqb eff.eff_copyins [(rqtp, 16)] with
        | false => simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        | true =>
          simp only [hc, ↓reduceIte] at h
          split at h
          · split at h
            · injection h with hm
              exact Or.inr ⟨_, hm.symm⟩
            · split at h
              · injection h with hm
                exact Or.inl hm.symm
              · cases h
          · cases h
      | false =>
        simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h
        rcases hrm2 : read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) with _ | w
        · simp only [hrm2, reduceCtorEq] at h
        · simp only [hrm2, check_copyins] at h
          cases hc : access_ranges_eqb eff.eff_copyins [(rqtp, 16)] with
          | false => simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
          | true =>
            simp only [hc, ↓reduceIte] at h
            split at h
            · split at h
              · injection h with hm
                exact Or.inr ⟨_, hm.symm⟩
              · cases h
            · split at h
              · injection h with hm
                exact Or.inr ⟨_, hm.symm⟩
              · cases h
            · cases h

/-- Rocq: `VmMapsDisjoint.check_nanosleep_frame`.  `nanosleep` maps
nothing: `SYSCALL_DEFINE2(nanosleep)` (kernel/time/hrtimer.c:2189-2205,
Linux v6.18.46) reads and validates the request and hands it to
`hrtimer_nanosleep` (:2159-2185), which sleeps on an `hrtimer_sleeper`
on its own stack (:2166) and reaches user memory only through
`nanosleep_copyout`'s `put_timespec64` (:2103), a copy into the
destination.  The checker's side is
`check_nanosleep_ok_is_a_clock_step`: every accepted model is the one
handed in or its `with_clock`, which carries `m_vm` across unchanged, so
the ledger is what it was. -/
theorem check_nanosleep_frame (i : SyscallInput) (rqtp rmtp : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Time.Hrtimer.check_nanosleep i rqtp rmtp eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  rcases check_nanosleep_ok_is_a_clock_step i rqtp rmtp eff m m' evs h with rfl | ⟨t, rfl⟩
  · rfl
  · rfl

/-- `nanosleep` (101): an answer the checker accepts leaves the ledger as
it was (`check_nanosleep_frame`, above). -/
theorem arm_nanosleep_preserves_vm : arm_preserves_vm arm_nanosleep :=
  arm_preserves_of_frame arm_nanosleep (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_nanosleep_frame i _ _ eff m m' evs h)

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
no Rocq twin.  The two registry entries beside `vm_wf` read the
descriptor subsystem, and one frame lemma over the whole record answers
both. -/

/-- The descriptor subsystem `check_nanosleep` hands back is the one it
was handed.  `nanosleep` takes no descriptor and allocates none:
neither `SYSCALL_DEFINE2(nanosleep)` (kernel/time/hrtimer.c:2189-2205,
Linux v6.18.46) nor the `hrtimer_nanosleep` it calls (:2159-2185) reads
or installs one.  The accepted model is the one handed in or its
`with_clock`, which carries `m_fd` across unchanged
(`Arms.check_nanosleep_ok_is_a_clock_step`). -/
theorem check_nanosleep_fd_state_frame (i : SyscallInput) (rqtp rmtp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Time.Hrtimer.check_nanosleep i rqtp rmtp eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  rcases Arms.check_nanosleep_ok_is_a_clock_step i rqtp rmtp eff m m' evs h with rfl | ⟨t, rfl⟩
  · rfl
  · rfl

/-- `vm_wf` × `nanosleep`: the ledger fact above. -/
theorem vm_wf_arm_nanosleep : arm_preserves inv_vm_wf arm_nanosleep :=
  Arms.arm_nanosleep_preserves_vm

/-- `fd_table_unique` × `nanosleep`. -/
theorem fd_table_unique_arm_nanosleep : arm_preserves inv_fd_table_unique arm_nanosleep :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_nanosleep (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_nanosleep_fd_state_frame i _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `nanosleep`. -/
theorem pipes_within_capacity_arm_nanosleep :
    arm_preserves inv_pipes_within_capacity arm_nanosleep :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_nanosleep
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes (check_nanosleep_fd_state_frame i _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
