import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Sched.Syscalls
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: 6e7c0d18ddbaa2d453318f0af4665958350a1871 -/

/-! # LinuxProcessSem.Checks.Arms.Kernel.Sched.Syscalls — sched_setscheduler, sched_getaffinity and sched_yield on the checked surface

The registration of `Checks/Sys/Kernel/Sched/Syscalls.lean`'s three
checkers in `checked_table`, in the one file that registration writes.
`tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files
under `Checks/Arms/`, one per checker twin, so that registering an arm
creates or edits no hub but this file; its docstring is the shape it reads
and what it refuses. The file holds three sections, each in the
namespace its declarations had when those three hubs were written by
hand, so that no name moved with the file:

- `Checks.Sys.Table`: the `CheckedArm`s (`arm_sched_setscheduler`,
  `arm_sched_getaffinity` and `arm_sched_yield`) and their four
  `arm_unfold` lemmas each;
- `Checks.VmMapsDisjoint.Arms`: each arm's ledger fact,
  `arm_<name>_preserves_vm`, which `checked_table_preserves_vm`'s
  alternation names;
- `Checks.Invariants`: one `<invariant>_arm_<name>` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`, which
  `registry_preserves`'s alternation names.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arms are the rows of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table`, read at that commit.  It is the checker twin's baseline,
6e7c0d18d, rather than the f44244ad the ticket named, and for the twin's
reason: f44244ad is not an ancestor of the day branch, and it predates the
`sched_yield` arm this file registers.  `Checks/Sys/Dispatch.v`,
`Checks/VmMapsDisjoint.v`, `Checks/Sys/Kernel/Sched/Syscalls.v` and
`Checks/Cases/Kernel/Sched/Syscalls.v` read the same at the baseline and
at the day branch this file was written on. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch


/- ### sched_setscheduler (119) -/

/-- This wrapper supplies the checker with the three argument registers.
The unfolding equation supplies its value to proofs.
The NULL gate blocks reduction on symbolic arguments before the signed comparisons.
The arm and generated alternatives now build without irreducibility attributes on this wrapper or the spec. -/
def check_sched_setscheduler_regs (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : check_result :=
  Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler i
    (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m

/-- This equation exposes the register wrapper without reducing the checker's signed comparisons. -/
theorem check_sched_setscheduler_regs_eq (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_sched_setscheduler_regs i eff m =
      Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler i
        (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m := rfl


/-- sched_setscheduler (119).  THE THREE ARGUMENTS ARE REGISTERS `a0`,
`a1` AND `a2`, HANDED OVER WHOLE.  riscv64's `__riscv_sys_sched_setscheduler`
passes the registers in order, `orig_a0` then `a1` and `a2`
(`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24,
Linux v6.18.46), and the wrapper narrows each to the type
`SYSCALL_DEFINE3(sched_setscheduler, pid_t, pid, int, policy, struct
sched_param __user *, param)` declares (kernel/sched/syscalls.c:962, same
version) through `__SC_CAST` (include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46).  The arm
does not narrow: Rocq's `arm_sched_setscheduler` hands the spec the three
64-bit words, and the spec reads `pid` and `policy` through `sint32` and
`abi_low32` itself, so a narrowing here would be a second one.  `param`
is a pointer and stays whole.  `ca_arm` is the term
`Sys/Registry/Kernel/Sched/Syscalls.lean`'s row builds, which
`checked_table_arms` checks.  The ledger fact this arm owes
`checked_table_preserves_vm` is `check_sched_setscheduler_frame`, beside
the checker. -/
def arm_sched_setscheduler : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 119 (fun i => Sys.Kernel.Sched.Syscalls.sched_setscheduler_spec
    (in_arg i 0) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_sched_setscheduler_regs i eff m
  ca_witness := fun i m => Checks.Sys.Kernel.Sched.Syscalls.sched_setscheduler_witness
    (in_arg i 0) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler_sound_ok i
      (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m m' evs
      ((check_sched_setscheduler_regs_eq i eff m).symm.trans h)
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler_sound_unmodeled i
      (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m
      ((check_sched_setscheduler_regs_eq i eff m).symm.trans h)
  ca_complete_ok := fun i eff m m' evs h =>
    (check_sched_setscheduler_regs_eq i eff m).trans
      (Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler_complete_ok i
        (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m m' evs h)
  ca_complete_unmodeled := fun i m eff h =>
    (check_sched_setscheduler_regs_eq i eff m).trans
      (Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler_complete_unmodeled i
        (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m h)
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Sched.Syscalls.sched_setscheduler_witness_ok i
      (in_arg i 0) (in_arg i 1) (in_arg i 2) m

@[arm_unfold] theorem ca_check_arm_sched_setscheduler (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    arm_sched_setscheduler.ca_check i eff m =
      Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler i
        (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m :=
  check_sched_setscheduler_regs_eq i eff m
@[arm_unfold] theorem ca_witness_arm_sched_setscheduler (i : SyscallInput) (m : Model) :
    arm_sched_setscheduler.ca_witness i m =
      Checks.Sys.Kernel.Sched.Syscalls.sched_setscheduler_witness
        (in_arg i 0) (in_arg i 1) (in_arg i 2) i m := by
  dsimp only [arm_sched_setscheduler]
@[arm_unfold] theorem sa_spec_arm_sched_setscheduler (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_sched_setscheduler.ca_arm.sa_spec i m o =
      Sys.Kernel.Sched.Syscalls.sched_setscheduler_spec
        (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_sched_setscheduler : ca_no arm_sched_setscheduler = 119 := rfl

/- ### sched_getaffinity (123) -/

/-- sched_getaffinity (123).  THE LENGTH IS REGISTER `a1`, HANDED OVER
WHOLE, AND `a0` AND `a2` ARE NOT READ.  The registers arrive in order as
for `sched_setscheduler` above (`SC_RISCV_REGS_TO_ARGS`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46), narrowed
to the types `SYSCALL_DEFINE3(sched_getaffinity, pid_t, pid, unsigned int,
len, unsigned long __user *, user_mask_ptr)` declares
(kernel/sched/syscalls.c:1329-1330, same version) through `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46).  The two
gates the model answers (kernel/sched/syscalls.c:1335-1338, Linux
v6.18.46) read `len` alone, and the spec cuts it to its low 32 bits
itself, as Rocq's `arm_sched_getaffinity` leaves it to; neither `pid` nor
`user_mask_ptr` is reached before a length the gates let through, and
every such length is declined, so the arm passing `in_arg i 1` alone is
exact rather than a narrowing.  Reading `a0` instead would answer the
pid's value as a length.  `ca_arm` is the term
`Sys/Registry/Kernel/Sched/Syscalls.lean`'s row builds, which
`checked_table_arms` checks.  The ledger fact is
`check_sched_getaffinity_frame`, beside the checker. -/
def arm_sched_getaffinity : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 123 (fun i => Sys.Kernel.Sched.Syscalls.sched_getaffinity_spec
    (in_arg i 1) i)
  ca_check := fun i eff m => Checks.Sys.Kernel.Sched.Syscalls.check_sched_getaffinity
    (in_arg i 1) eff m
  ca_witness := fun i m => Checks.Sys.Kernel.Sched.Syscalls.sched_getaffinity_witness
    (in_arg i 1) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sched.Syscalls.check_sched_getaffinity_sound_ok (in_arg i 1) eff m m' evs
      i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Sched.Syscalls.check_sched_getaffinity_sound_unmodeled (in_arg i 1) eff m
      i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sched.Syscalls.check_sched_getaffinity_complete_ok (in_arg i 1) eff m m'
      evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sched.Syscalls.check_sched_getaffinity_complete_unmodeled (in_arg i 1) m
      i eff h
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Sched.Syscalls.sched_getaffinity_witness_ok (in_arg i 1) i m

@[arm_unfold] theorem ca_check_arm_sched_getaffinity (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    arm_sched_getaffinity.ca_check i eff m =
      Checks.Sys.Kernel.Sched.Syscalls.check_sched_getaffinity (in_arg i 1) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_sched_getaffinity (i : SyscallInput) (m : Model) :
    arm_sched_getaffinity.ca_witness i m =
      Checks.Sys.Kernel.Sched.Syscalls.sched_getaffinity_witness (in_arg i 1) m := rfl
@[arm_unfold] theorem sa_spec_arm_sched_getaffinity (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_sched_getaffinity.ca_arm.sa_spec i m o =
      Sys.Kernel.Sched.Syscalls.sched_getaffinity_spec (in_arg i 1) i m o := rfl
@[arm_unfold] theorem ca_no_arm_sched_getaffinity : ca_no arm_sched_getaffinity = 123 := rfl

/- ### sched_yield (124) -/

/-- sched_yield (124).  NO REGISTER IS READ.  `SYSCALL_DEFINE0(sched_yield)`
(kernel/sched/syscalls.c:1382, Linux v6.18.46) expands on riscv64 to a
`__riscv_sys_sched_yield` whose one parameter, the saved registers, is
named `__unused` (arch/riscv/include/asm/syscall_wrapper.h:99-103, same
version), and the body returns 0 after `do_sched_yield`, so no argument
word can change the answer; the spec's docstring carries that reading.
The checker and witness take no argument, and the arm hands them none.
`ca_arm` is the term `Sys/Registry/Kernel/Sched/Syscalls.lean`'s row
builds, which `checked_table_arms` checks.  The ledger fact is
`check_sched_yield_frame`, beside the checker. -/
def arm_sched_yield : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 124 (fun i => Sys.Kernel.Sched.Syscalls.sched_yield_spec i)
  ca_check := fun _ eff m => Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield eff m
  ca_witness := fun _ m => Checks.Sys.Kernel.Sched.Syscalls.sched_yield_witness m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield_sound_ok eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield_sound_unmodeled eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield_complete_ok eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield_complete_unmodeled i m eff h
  ca_receptive := fun i m => Checks.Sys.Kernel.Sched.Syscalls.sched_yield_witness_ok i m

@[arm_unfold] theorem ca_check_arm_sched_yield (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    arm_sched_yield.ca_check i eff m = Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield eff m :=
  rfl
@[arm_unfold] theorem ca_witness_arm_sched_yield (i : SyscallInput) (m : Model) :
    arm_sched_yield.ca_witness i m = Checks.Sys.Kernel.Sched.Syscalls.sched_yield_witness m := rfl
@[arm_unfold] theorem sa_spec_arm_sched_yield (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_sched_yield.ca_arm.sa_spec i m o = Sys.Kernel.Sched.Syscalls.sched_yield_spec i m o := rfl
@[arm_unfold] theorem ca_no_arm_sched_yield : ca_no arm_sched_yield = 124 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `sched_setscheduler` (119): every `CheckOk` is a `check_ret_only` or
`check_ret_only_copyins` verdict on the model handed in, so the ledger is
what it was (`check_sched_setscheduler_frame`, stated beside the checker
in `Checks/Sys/Kernel/Sched/Syscalls.lean`). -/
theorem arm_sched_setscheduler_preserves_vm : arm_preserves_vm arm_sched_setscheduler :=
  arm_preserves_of_frame arm_sched_setscheduler (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler_frame i _ _ _ eff m m' evs h)

/-- `sched_getaffinity` (123): an errno or a decline, so the ledger is
untouched (`check_sched_getaffinity_frame`). -/
theorem arm_sched_getaffinity_preserves_vm : arm_preserves_vm arm_sched_getaffinity :=
  arm_preserves_of_frame arm_sched_getaffinity (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sched.Syscalls.check_sched_getaffinity_frame _ eff m m' evs h)

/-- `sched_yield` (124): a bare 0 on the model handed in
(`check_sched_yield_frame`). -/
theorem arm_sched_yield_preserves_vm : arm_preserves_vm arm_sched_yield :=
  arm_preserves_of_frame arm_sched_yield (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield_frame eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## The descriptor-state frame lemmas

The two registry entries beside `vm_wf` read the `m_fd` subsystem, so one
frame lemma per checker over the whole record answers both.  They belong
beside the checkers, in `Checks/Sys/Kernel/Sched/Syscalls.lean`, which
states the ledger frames; they are here because this ticket writes the
arm file and not the checker twin, as `Checks/Arms/Kernel/Exit.lean`'s
is, and moving them there changes nothing but their home.  Each is its
checker's ledger frame proof with a different projection at the end: no
checker here builds a model, so every `CheckOk` hands back the model it
was given. -/

theorem check_sched_setscheduler_fd_state_frame (i : SyscallInput) (pid policy param : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler i pid policy param eff m =
      CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler at h
  cases hnull : w_is0 param
  · simp only [hnull, Bool.false_eq_true, ↓reduceIte] at h
    cases hearly : (decide (sint32 policy < 0) || decide (sint32 pid < 0))
    · simp only [hearly, Bool.false_eq_true, ↓reduceIte] at h
      cases hread : read_bytes_map i.in_mem param (Z_to_bv 64 4) with
      | none =>
        rw [hread] at h
        dsimp only at h
        cases hacc : access_okb param 4
        · simp only [hacc, Bool.not_false, ↓reduceIte] at h
          obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
          rfl
        · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | some bs =>
        rw [hread] at h
        dsimp only at h
        cases hself : Sys.Kernel.Sched.Syscalls.sched_targets_self_b pid m
        · simp only [hself, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
        · simp only [hself, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hans : Sys.Kernel.Sched.Syscalls.sched_setscheduler_answer
              (bv_unsigned (abi_low32 policy)) (bv_unsigned (le_bytes_to_word bs)) with
          | some r =>
            rw [hans] at h
            dsimp only at h
            obtain ⟨-, rfl, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
            rfl
          | none =>
            rw [hans] at h
            dsimp only at h
            exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    · simp only [hearly, ↓reduceIte] at h
      cases h
  · simp only [hnull, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl

/-- `check_sched_getaffinity` answers an errno or declines. -/
theorem check_sched_getaffinity_fd_state_frame (len : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Sched.Syscalls.check_sched_getaffinity len eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Sched.Syscalls.check_sched_getaffinity at h
  cases hlen : Sys.Kernel.Sched.Syscalls.affinity_len_einval_b len
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  · simp only [hlen, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl

/-- `check_sched_yield` is a bare `check_ret_only`. -/
theorem check_sched_yield_fd_state_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield at h
  obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
  rfl

/-- `vm_wf` × `sched_setscheduler`: the ledger fact above. -/
theorem vm_wf_arm_sched_setscheduler : arm_preserves inv_vm_wf arm_sched_setscheduler :=
  Arms.arm_sched_setscheduler_preserves_vm

/-- `vm_wf` × `sched_getaffinity`: likewise. -/
theorem vm_wf_arm_sched_getaffinity : arm_preserves inv_vm_wf arm_sched_getaffinity :=
  Arms.arm_sched_getaffinity_preserves_vm

/-- `vm_wf` × `sched_yield`: likewise. -/
theorem vm_wf_arm_sched_yield : arm_preserves inv_vm_wf arm_sched_yield :=
  Arms.arm_sched_yield_preserves_vm

/-- `fd_table_unique` × `sched_setscheduler`. -/
theorem fd_table_unique_arm_sched_setscheduler :
    arm_preserves inv_fd_table_unique arm_sched_setscheduler :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_sched_setscheduler
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_table
        (check_sched_setscheduler_fd_state_frame i _ _ _ eff m m' evs h))

/-- `fd_table_unique` × `sched_getaffinity`. -/
theorem fd_table_unique_arm_sched_getaffinity :
    arm_preserves inv_fd_table_unique arm_sched_getaffinity :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_sched_getaffinity
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_table (check_sched_getaffinity_fd_state_frame _ eff m m' evs h))

/-- `fd_table_unique` × `sched_yield`. -/
theorem fd_table_unique_arm_sched_yield : arm_preserves inv_fd_table_unique arm_sched_yield :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_sched_yield (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_sched_yield_fd_state_frame eff m m' evs h))

/-- `pipes_within_capacity` × `sched_setscheduler`. -/
theorem pipes_within_capacity_arm_sched_setscheduler :
    arm_preserves inv_pipes_within_capacity arm_sched_setscheduler :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_sched_setscheduler
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes
        (check_sched_setscheduler_fd_state_frame i _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `sched_getaffinity`. -/
theorem pipes_within_capacity_arm_sched_getaffinity :
    arm_preserves inv_pipes_within_capacity arm_sched_getaffinity :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_sched_getaffinity
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes (check_sched_getaffinity_fd_state_frame _ eff m m' evs h))

/-- `pipes_within_capacity` × `sched_yield`. -/
theorem pipes_within_capacity_arm_sched_yield :
    arm_preserves inv_pipes_within_capacity arm_sched_yield :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_sched_yield
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes (check_sched_yield_fd_state_frame eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
