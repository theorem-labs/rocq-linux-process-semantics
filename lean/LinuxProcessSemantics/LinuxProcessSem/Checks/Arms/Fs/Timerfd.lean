import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Timerfd
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Fs.Timerfd — timerfd_create on the checked surface

The registration of `Checks/Sys/Fs/Timerfd.lean`'s checker in
`checked_table`.  `tools/gen_lean_checked.py`'s docstring is the shape
this file has to have, and what it renders from it.

WHY THE TWO FRAME LEMMAS ARE HERE and not beside the checker.  The tree's
rule is that a checker's frame lemma lives beside the checker, and
`Checks/Sys/Fs/Timerfd.lean` states none: its header hands the ledger
frame to this registration.  A registration writes the arm file and the
arm's Cases twins, not the checker, which is its C ticket's
(`docs/lean-port/BRIEF.md` section 4), so the two lemmas are stated here,
in the sections whose facts consume them, as `Checks/Arms/Kernel/Exit.lean`
states its descriptor frame.  Moving them beside the checker changes
nothing but their home.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arm is the row of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table`, read at that commit. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### timerfd_create (85) -/

/-- timerfd_create (85).  The five proof fields are the file's own
obligation: an arm that cannot supply them does not exist.  The clock id
is register `a0` and the flag word `a1` — riscv64's wrapper passes the
registers in order (`SC_RISCV_REGS_TO_ARGS` under `CONFIG_64BIT`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46) — and
each is narrowed to the `int` that `SYSCALL_DEFINE2(timerfd_create, int,
clockid, int, flags)` declares (fs/timerfd.c:394, Linux v6.18.46) through
`__SC_CAST` (include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46) before the
gate at fs/timerfd.c:404-410 reads either.  So the arm hands the spec,
the checker and the witness `clockid32 (in_arg i 0)` and
`flag32 (in_arg i 1)`, the reading Rocq's `arm_timerfd_create` applies;
`ca_arm` is the term `Sys/Registry/Fs/Timerfd.lean`'s row builds, which
`checked_table_arms` checks. -/
def arm_timerfd_create : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 85
    (fun i => Sys.Fs.Timerfd.timerfd_create_spec (Sys.Syscall.clockid32 (in_arg i 0))
      (Sys.Syscall.flag32 (in_arg i 1)) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.Timerfd.check_timerfd_create (Sys.Syscall.clockid32 (in_arg i 0))
      (Sys.Syscall.flag32 (in_arg i 1)) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.Timerfd.timerfd_create_witness (Sys.Syscall.clockid32 (in_arg i 0))
      (Sys.Syscall.flag32 (in_arg i 1)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Timerfd.check_timerfd_create_sound_ok (Sys.Syscall.clockid32 (in_arg i 0))
      (Sys.Syscall.flag32 (in_arg i 1)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Timerfd.check_timerfd_create_sound_unmodeled
      (Sys.Syscall.clockid32 (in_arg i 0)) (Sys.Syscall.flag32 (in_arg i 1)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Timerfd.check_timerfd_create_complete_ok (Sys.Syscall.clockid32 (in_arg i 0))
      (Sys.Syscall.flag32 (in_arg i 1)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Timerfd.check_timerfd_create_complete_unmodeled
      (Sys.Syscall.clockid32 (in_arg i 0)) (Sys.Syscall.flag32 (in_arg i 1)) m i eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.Timerfd.timerfd_create_witness_ok (Sys.Syscall.clockid32 (in_arg i 0))
      (Sys.Syscall.flag32 (in_arg i 1)) i m

@[arm_unfold] theorem ca_check_arm_timerfd_create (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_timerfd_create.ca_check i eff m
      = Checks.Sys.Fs.Timerfd.check_timerfd_create (Sys.Syscall.clockid32 (in_arg i 0))
          (Sys.Syscall.flag32 (in_arg i 1)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_timerfd_create (i : SyscallInput) (m : Model) :
    arm_timerfd_create.ca_witness i m
      = Checks.Sys.Fs.Timerfd.timerfd_create_witness (Sys.Syscall.clockid32 (in_arg i 0))
          (Sys.Syscall.flag32 (in_arg i 1)) m := rfl
@[arm_unfold] theorem sa_spec_arm_timerfd_create (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_timerfd_create.ca_arm.sa_spec i m o
      = Sys.Fs.Timerfd.timerfd_create_spec (Sys.Syscall.clockid32 (in_arg i 0))
          (Sys.Syscall.flag32 (in_arg i 1)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_timerfd_create : ca_no arm_timerfd_create = 85 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- Rocq: `VmMapsDisjoint.check_timerfd_create_frame`.  The checker's one
accepted answer is the -EINVAL `timerfd_create` returns at
fs/timerfd.c:410 (Linux v6.18.46, commit 1f99e9ab748f), before the
`kzalloc` at fs/timerfd.c:417 and before the descriptor is reserved at
:435, and `check_ret_only` hands back the model it was handed; every input past
the gate is declined.  So the arm touches no field of the model,
`m_vmmaps` included.  A `*_frame` rather than a `*_preserves`: nothing is
written for `vm_wf` to be re-established over.  This stops being the
right shape if the arm ever grows the success branch the spec declines,
though not because of memory: the descriptor would land in `m_fd`, which
the descriptor frame below states.

Proved from `check_ret_only_ok_iff`, as `check_eventfd2_frame` is: the
accepted branch is `check_ret_only`, whose `_ok_iff` hands the model back,
and the declined branch never accepts. -/
theorem check_timerfd_create_frame (clkid flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.Timerfd.check_timerfd_create clkid flags eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold Checks.Sys.Fs.Timerfd.check_timerfd_create at h
  split at h
  · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  · cases h

/-- `timerfd_create` (85): the accepted model is the model handed in, so
the ledger is what it was (`check_timerfd_create_frame`, above). -/
theorem arm_timerfd_create_preserves_vm : arm_preserves_vm arm_timerfd_create :=
  arm_preserves_of_frame arm_timerfd_create (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_timerfd_create_frame _ _ eff m m' evs h)

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

/-- `check_timerfd_create` hands back the model it was handed on the one
answer it accepts, so the descriptor subsystem is the one it was handed.
That answer is the -EINVAL `timerfd_create` returns at fs/timerfd.c:410
(Linux v6.18.46, commit 1f99e9ab748f), before `timerfd_create` reserves
a descriptor at fs/timerfd.c:435 and builds the file it is bound to at
:441; an input that passes the gate, the only path that binds one, is declined.
The proof is `check_timerfd_create_frame`'s with the other projection at
the end. -/
theorem check_timerfd_create_fd_state_frame (clkid flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.Timerfd.check_timerfd_create clkid flags eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Fs.Timerfd.check_timerfd_create at h
  split at h
  · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  · cases h

/-- `vm_wf` × `timerfd_create`: the ledger fact above. -/
theorem vm_wf_arm_timerfd_create : arm_preserves inv_vm_wf arm_timerfd_create :=
  Arms.arm_timerfd_create_preserves_vm

/-- `fd_table_unique` × `timerfd_create`. -/
theorem fd_table_unique_arm_timerfd_create :
    arm_preserves inv_fd_table_unique arm_timerfd_create :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_timerfd_create
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_table (check_timerfd_create_fd_state_frame _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `timerfd_create`. -/
theorem pipes_within_capacity_arm_timerfd_create :
    arm_preserves inv_pipes_within_capacity arm_timerfd_create :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_timerfd_create
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes (check_timerfd_create_fd_state_frame _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
