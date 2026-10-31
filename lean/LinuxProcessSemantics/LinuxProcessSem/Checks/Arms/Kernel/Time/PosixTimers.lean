import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.PosixTimers
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Kernel.Time.PosixTimers — clock_gettime on the checked surface

The registration of `Checks/Sys/Kernel/Time/PosixTimers.lean`'s checker in
`checked_table`, in the one file that registration writes.
`tools/gen_lean_checked.py`'s docstring is the shape this file has to
have, and what it renders from it.  The file holds three sections, each in
the namespace the other arm files use for it:

- `Checks.Sys.Table`: the `CheckedArm` (`arm_clock_gettime`) and its four
  `arm_unfold` lemmas;
- `Checks.VmMapsDisjoint.Arms`: the arm's ledger fact,
  `arm_clock_gettime_preserves_vm`, built from
  `check_clock_gettime_frame`, which the checker file states;
- `Checks.Invariants`: one `<invariant>_arm_clock_gettime` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`, and the
  descriptor-state frame the two `m_fd` entries rest on.

WHY THE DESCRIPTOR-STATE FRAME IS HERE and not beside the checker.  The
tree's rule is that a checker's frame lemma lives beside the checker.  The
checker file is its C ticket's, and this ticket's brief does not name it
among its registration points, so the frame is stated here, in the
section whose facts consume it, as `Checks/Arms/Fs/Timerfd.lean` and
`Checks/Arms/Drivers/Char/Random.lean` state theirs.  Moving it beside
`check_clock_gettime_frame` changes nothing but its home.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arm is the row of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table` for 113, read at that commit, where it is byte-identical
to f44244ad6b80's. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### clock_gettime (113) -/

/-- clock_gettime (113).  The five proof fields are the file's own
obligation: an arm that cannot supply them does not exist.  The clock id
is register `a0` and the destination `a1`: riscv64's wrapper passes the
registers in order (`SC_RISCV_REGS_TO_ARGS` under `CONFIG_64BIT`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46), and
narrows each to the type `SYSCALL_DEFINE2(clock_gettime, const
clockid_t, which_clock, struct __kernel_timespec __user *, tp)` declares
(kernel/time/posix-timers.c:1136-1137, Linux v6.18.46) through
`__SC_CAST` (include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46).
`clockid_t` is `__kernel_clockid_t` (include/linux/types.h:32), an `int`
(include/uapi/asm-generic/posix_types.h:96, both Linux v6.18.46), so the
id is the register's low 32 bits before `clockid_to_kclock` reads it at
kernel/time/posix-timers.c:1139; the destination is a pointer, the
register's width on riscv64, so the cast keeps all of `a1`.  The arm hands
the spec, the checker and the witness `clockid32 (in_arg i 0)` and
`in_arg i 1`, the reading Rocq's `arm_clock_gettime` applies; `ca_arm` is
the term `Sys/Registry/Kernel/Time/PosixTimers.lean`'s row builds, which
`checked_table_arms` checks. -/
def arm_clock_gettime : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 113
    (fun i => Sys.Kernel.Time.PosixTimers.clock_gettime_spec (Sys.Syscall.clockid32 (in_arg i 0))
      (in_arg i 1) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Time.PosixTimers.check_clock_gettime i
      (Sys.Syscall.clockid32 (in_arg i 0)) (in_arg i 1) eff m
  ca_witness := fun i m =>
    Checks.Sys.Kernel.Time.PosixTimers.clock_gettime_witness
      (Sys.Syscall.clockid32 (in_arg i 0)) (in_arg i 1) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Time.PosixTimers.check_clock_gettime_sound_ok i
      (Sys.Syscall.clockid32 (in_arg i 0)) (in_arg i 1) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Time.PosixTimers.check_clock_gettime_sound_unmodeled i
      (Sys.Syscall.clockid32 (in_arg i 0)) (in_arg i 1) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Time.PosixTimers.check_clock_gettime_complete_ok i
      (Sys.Syscall.clockid32 (in_arg i 0)) (in_arg i 1) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Time.PosixTimers.check_clock_gettime_complete_unmodeled i
      (Sys.Syscall.clockid32 (in_arg i 0)) (in_arg i 1) m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Time.PosixTimers.clock_gettime_witness_ok i
      (Sys.Syscall.clockid32 (in_arg i 0)) (in_arg i 1) m

@[arm_unfold] theorem ca_check_arm_clock_gettime (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_clock_gettime.ca_check i eff m
      = Checks.Sys.Kernel.Time.PosixTimers.check_clock_gettime i
          (Sys.Syscall.clockid32 (in_arg i 0)) (in_arg i 1) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_clock_gettime (i : SyscallInput) (m : Model) :
    arm_clock_gettime.ca_witness i m
      = Checks.Sys.Kernel.Time.PosixTimers.clock_gettime_witness
          (Sys.Syscall.clockid32 (in_arg i 0)) (in_arg i 1) i m := rfl
@[arm_unfold] theorem sa_spec_arm_clock_gettime (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_clock_gettime.ca_arm.sa_spec i m o
      = Sys.Kernel.Time.PosixTimers.clock_gettime_spec (Sys.Syscall.clockid32 (in_arg i 0))
          (in_arg i 1) i m o := rfl
@[arm_unfold] theorem ca_no_arm_clock_gettime : ca_no arm_clock_gettime = 113 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `clock_gettime` (113): an answer the checker accepts leaves the ledger
as it was (`check_clock_gettime_frame`, the twin of Rocq's
`VmMapsDisjoint.check_clock_gettime_frame`, stated beside the checker in
`Checks/Sys/Kernel/Time/PosixTimers.lean`). -/
theorem arm_clock_gettime_preserves_vm : arm_preserves_vm arm_clock_gettime :=
  arm_preserves_of_frame arm_clock_gettime (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Time.PosixTimers.check_clock_gettime_frame i _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## The descriptor-state frame

The two registry entries beside `vm_wf` read the `m_fd` subsystem, so one
frame lemma over the whole record answers both.  Rocq registers no `m_fd`
invariant, which is why it has no Rocq twin.

The proof is `check_clock_gettime_frame`'s, gate for gate, with the goal
read one field over: the two arms that record nothing hand back the model
they were given, closed by `rfl`, and the monotonic arm hands back
`with_clock … m`, closed by `m_fd_with_clock`.  The gates are crossed the
way that proof crosses them, the envelope gate by `rw` alone, and the
monotonic leaf is closed by a lemma taken once on an abstract clock rather
than by `rfl` at the use site, for the reason the section "Crossing the
recorded-clock gate" of `Checks/Sys/Kernel/Time/PosixTimers.lean` gives. -/

/-- `with_clock` rewrites the time component and leaves the descriptor
subsystem alone. -/
theorem m_fd_with_clock (t : word) (m : Model) : (with_clock t m).m_fd = m.m_fd := rfl

open LinuxProcessSemantics.LinuxProcessSem.BvBase
  LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
  LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.PosixTimers in
/-- The descriptor subsystem `check_clock_gettime` hands back is the one it
was handed. -/
theorem check_clock_gettime_fd_state_frame (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_clock_gettime i clkid tp eff m = CheckOk m' evs) : m'.m_fd = m.m_fd := by
  unfold check_clock_gettime at h
  by_cases hrt : bv_unsigned clkid = CLOCK_REALTIME
  · simp only [hrt, ↓reduceIte] at h
    rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
    · simp only [hdst, reduceCtorEq] at h
    · simp only [hdst] at h
      split at h
      next =>
        split at h
        next =>
          cases h
          rfl
        next => cases h
      next => cases h
  · simp only [hrt, ↓reduceIte] at h
    by_cases hcp : bv_unsigned clkid = CLOCK_PROCESS_CPUTIME_ID
    · simp only [hcp, ↓reduceIte] at h
      rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
      · simp only [hdst, reduceCtorEq] at h
      · simp only [hdst] at h
        split at h
        next =>
          split at h
          next =>
            cases h
            rfl
          next => cases h
        next => cases h
    · simp only [hcp, ↓reduceIte] at h
      by_cases hid : bv_unsigned clkid = CLOCK_MONOTONIC
      · simp only [hid, ne_eq, not_true_eq_false, ↓reduceIte] at h
        by_cases henv : bv_unsigned (m_clock m) < CLOCK_NS_ENVELOPE
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro henv))] at h
          rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
          · simp only [hdst, reduceCtorEq] at h
          · simp only [hdst] at h
            split at h
            next =>
              split at h
              next =>
                cases h
                exact m_fd_with_clock _ _
              next => cases h
            next => cases h
        · rw [ite_eq_left_of_eq_true _ _ (eq_true henv)] at h
          cases h
      · simp only [hid, ne_eq, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- `vm_wf` × `clock_gettime`: the ledger fact above. -/
theorem vm_wf_arm_clock_gettime : arm_preserves inv_vm_wf arm_clock_gettime :=
  Arms.arm_clock_gettime_preserves_vm

/-- `fd_table_unique` × `clock_gettime`: the checker's accepted models
differ from the one it was given in the time component at most; the frame
is above. -/
theorem fd_table_unique_arm_clock_gettime :
    arm_preserves inv_fd_table_unique arm_clock_gettime :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_clock_gettime
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_table (check_clock_gettime_fd_state_frame i _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `clock_gettime`: no pipe is touched. -/
theorem pipes_within_capacity_arm_clock_gettime :
    arm_preserves inv_pipes_within_capacity arm_clock_gettime :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_clock_gettime
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes (check_clock_gettime_fd_state_frame i _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
