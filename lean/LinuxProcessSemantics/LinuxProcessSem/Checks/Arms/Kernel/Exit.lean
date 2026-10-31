import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Exit
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Kernel.Exit — exit and exit_group on the checked surface

The registration of `Checks/Sys/Kernel/Exit.lean`'s checker, under both
numbers it answers in `checked_table`, in the one file that registration
writes. `tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files
under `Checks/Arms/`, one per checker twin, so that registering an arm
creates or edits no hub but this file; its docstring is the shape it reads
and what it refuses. The file holds three sections, each in the
namespace its declarations had when those three hubs were written by
hand, so that no name moved with the file:

- `Checks.Sys.Table`: the `CheckedArm` (`arm_exit` and `arm_exit_group`)
  and its four `arm_unfold` lemmas;
- `Checks.VmMapsDisjoint.Arms`: the arm's ledger fact,
  `arm_<name>_preserves_vm`, which `checked_table_preserves_vm`'s
  alternation names;
- `Checks.Invariants`: one `<invariant>_arm_<name>` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`, which
  `registry_preserves`'s alternation names.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arms are the rows of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table`, read at that commit. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### exit (93) -/

/-- exit (93).  The five proof fields are the file's own obligation: an
arm that cannot supply them does not exist.  The argument is register
`a0`, read whole: riscv's wrapper hands `__do_sys_exit` the register as
`(__force int) error_code` (`__SC_CAST`, include/linux/syscalls.h:132,
applied at arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46)
and the body keeps only the low byte (kernel/exit.c:1085-1088, Linux
v6.18.46); the low byte of the narrowed word is the low byte of the
whole one, so the checker masks the 64-bit register and no `int` cast is
needed.  `ca_arm` is the term `Sys/SyscallTable.lean`'s row builds, which
`checked_table_arms` checks. -/
def arm_exit : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 93 (fun i => Sys.Kernel.Exit.exit_spec (in_arg i 0) i)
  ca_check := fun i eff m => Checks.Sys.Kernel.Exit.check_exit (in_arg i 0) eff m
  ca_witness := fun i m => Checks.Sys.Kernel.Exit.exit_witness (in_arg i 0) m
  ca_sound_ok := fun i eff m m' evs h => Checks.Sys.Kernel.Exit.check_exit_sound_ok (in_arg i 0) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h => Checks.Sys.Kernel.Exit.check_exit_sound_unmodeled (in_arg i 0) eff m i h
  ca_complete_ok := fun i eff m m' evs h => Checks.Sys.Kernel.Exit.check_exit_complete_ok (in_arg i 0) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Exit.check_exit_complete_unmodeled (in_arg i 0) m i eff h
  ca_receptive := fun i m => Checks.Sys.Kernel.Exit.exit_witness_ok (in_arg i 0) i m

@[arm_unfold] theorem ca_check_arm_exit (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_exit.ca_check i eff m = Checks.Sys.Kernel.Exit.check_exit (in_arg i 0) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_exit (i : SyscallInput) (m : Model) :
    arm_exit.ca_witness i m = Checks.Sys.Kernel.Exit.exit_witness (in_arg i 0) m := rfl
@[arm_unfold] theorem sa_spec_arm_exit (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_exit.ca_arm.sa_spec i m o = Sys.Kernel.Exit.exit_spec (in_arg i 0) i m o := rfl
@[arm_unfold] theorem ca_no_arm_exit : ca_no arm_exit = 93 := rfl

/- ### exit_group (94) -/

/-- exit_group (94).  The same checker, witness and proofs under the next
number: the spec is shared — `Sys/Kernel/Exit.lean` says why the two
branches `do_group_exit` (kernel/exit.c:1099-1111, Linux v6.18.46) adds
over `do_exit` are unreachable in this model — so the arm differs from
`arm_exit` in its number alone, and `Sys/SyscallTable.lean` builds both
rows the same way. -/
def arm_exit_group : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 94 (fun i => Sys.Kernel.Exit.exit_spec (in_arg i 0) i)
  ca_check := fun i eff m => Checks.Sys.Kernel.Exit.check_exit (in_arg i 0) eff m
  ca_witness := fun i m => Checks.Sys.Kernel.Exit.exit_witness (in_arg i 0) m
  ca_sound_ok := fun i eff m m' evs h => Checks.Sys.Kernel.Exit.check_exit_sound_ok (in_arg i 0) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h => Checks.Sys.Kernel.Exit.check_exit_sound_unmodeled (in_arg i 0) eff m i h
  ca_complete_ok := fun i eff m m' evs h => Checks.Sys.Kernel.Exit.check_exit_complete_ok (in_arg i 0) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Exit.check_exit_complete_unmodeled (in_arg i 0) m i eff h
  ca_receptive := fun i m => Checks.Sys.Kernel.Exit.exit_witness_ok (in_arg i 0) i m

@[arm_unfold] theorem ca_check_arm_exit_group (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_exit_group.ca_check i eff m = Checks.Sys.Kernel.Exit.check_exit (in_arg i 0) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_exit_group (i : SyscallInput) (m : Model) :
    arm_exit_group.ca_witness i m = Checks.Sys.Kernel.Exit.exit_witness (in_arg i 0) m := rfl
@[arm_unfold] theorem sa_spec_arm_exit_group (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_exit_group.ca_arm.sa_spec i m o = Sys.Kernel.Exit.exit_spec (in_arg i 0) i m o := rfl
@[arm_unfold] theorem ca_no_arm_exit_group : ca_no arm_exit_group = 94 := rfl

/- ### wait4 (260) -/

/-- wait4 (260).  The row applies `pid32` and `waitopts32` to the two
`int` arguments of `SYSCALL_DEFINE4(wait4, ...)` (kernel/exit.c,
Linux v6.18.46), leaving both pointers whole.  The per-gate argument is
`Checks.Sys.Kernel.Exit.check_wait4`'s docstring; this registration
supplies its checker, witness and proofs at the same arguments as the
spec row. -/
def arm_wait4 : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 260
    (fun i => Sys.Kernel.Exit.wait4_spec (pid32 (in_arg i 0)) (in_arg i 1)
      (waitopts32 (in_arg i 2)) (in_arg i 3) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Exit.check_wait4 i (pid32 (in_arg i 0)) (in_arg i 1)
      (waitopts32 (in_arg i 2)) (in_arg i 3) eff m
  ca_witness := fun i m =>
    Checks.Sys.Kernel.Exit.wait4_witness (pid32 (in_arg i 0)) (in_arg i 1)
      (waitopts32 (in_arg i 2)) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Exit.check_wait4_sound_ok i (pid32 (in_arg i 0)) (in_arg i 1)
      (waitopts32 (in_arg i 2)) (in_arg i 3) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Exit.check_wait4_sound_unmodeled i (pid32 (in_arg i 0)) (in_arg i 1)
      (waitopts32 (in_arg i 2)) (in_arg i 3) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Exit.check_wait4_complete_ok i (pid32 (in_arg i 0)) (in_arg i 1)
      (waitopts32 (in_arg i 2)) (in_arg i 3) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Exit.check_wait4_complete_unmodeled i (pid32 (in_arg i 0)) (in_arg i 1)
      (waitopts32 (in_arg i 2)) (in_arg i 3) m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Exit.wait4_witness_ok (pid32 (in_arg i 0)) (in_arg i 1)
      (waitopts32 (in_arg i 2)) (in_arg i 3) i m

@[arm_unfold] theorem ca_check_arm_wait4 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_wait4.ca_check i eff m =
      Checks.Sys.Kernel.Exit.check_wait4 i (pid32 (in_arg i 0)) (in_arg i 1)
        (waitopts32 (in_arg i 2)) (in_arg i 3) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_wait4 (i : SyscallInput) (m : Model) :
    arm_wait4.ca_witness i m =
      Checks.Sys.Kernel.Exit.wait4_witness (pid32 (in_arg i 0)) (in_arg i 1)
        (waitopts32 (in_arg i 2)) (in_arg i 3) i m := rfl
@[arm_unfold] theorem sa_spec_arm_wait4 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_wait4.ca_arm.sa_spec i m o =
      Sys.Kernel.Exit.wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2))
        (in_arg i 3) i m o := rfl
@[arm_unfold] theorem ca_no_arm_wait4 : ca_no arm_wait4 = 260 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `exit` (93): the accepted model is `with_halted` of the model handed
in, so the ledger is what it was (`check_exit_frame`, stated beside the
checker in `Checks/Sys/Kernel/Exit.lean`). -/
theorem arm_exit_preserves_vm : arm_preserves_vm arm_exit :=
  arm_preserves_of_frame arm_exit (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Exit.check_exit_frame _ eff m m' evs h)

/-- `exit_group` (94): the same checker, so the same frame lemma. -/
theorem arm_exit_group_preserves_vm : arm_preserves_vm arm_exit_group :=
  arm_preserves_of_frame arm_exit_group (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Exit.check_exit_frame _ eff m m' evs h)

/-- `wait4` (260): its checker keeps the accepted model's ledger. -/
theorem arm_wait4_preserves_vm : arm_preserves_vm arm_wait4 :=
  arm_preserves_of_frame arm_wait4 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Exit.check_wait4_frame i _ _ _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## The descriptor-state frame lemma

The two registry entries beside `vm_wf` read the `m_fd` subsystem, so one
frame lemma per checker over the whole record answers both.  The tree's
rule is that a checker's frame lemma lives beside the checker, and this
one belongs in `Checks/Sys/Kernel/Exit.lean`; it was written beside the
registry by ticket I3, which kept its Lean edits to the registry's own
files, and moving it there changes nothing but its home. -/

/-- `check_exit` rebuilds the process state and nothing else, so the
descriptor subsystem is the one it was handed.  Same proof as
`check_exit_frame` (`Checks/Sys/Kernel/Exit.lean`) with a different
projection at the end. -/
theorem check_exit_fd_state_frame (code : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Kernel.Exit.check_exit code eff m = CheckOk m' evs) : m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Exit.check_exit at h
  obtain ⟨_, rfl, _⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
  rfl

/-- `vm_wf` × `exit`: the ledger fact above. -/
theorem vm_wf_arm_exit : arm_preserves inv_vm_wf arm_exit :=
  Arms.arm_exit_preserves_vm

/-- `vm_wf` × `exit_group`: likewise. -/
theorem vm_wf_arm_exit_group : arm_preserves inv_vm_wf arm_exit_group :=
  Arms.arm_exit_group_preserves_vm

/-- `vm_wf` × `wait4`: the ledger fact above. -/
theorem vm_wf_arm_wait4 : arm_preserves inv_vm_wf arm_wait4 :=
  Arms.arm_wait4_preserves_vm

/-- `fd_table_unique` × `exit`. -/
theorem fd_table_unique_arm_exit : arm_preserves inv_fd_table_unique arm_exit :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_exit (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_exit_fd_state_frame _ eff m m' evs h))

/-- `fd_table_unique` × `exit_group`: the same checker. -/
theorem fd_table_unique_arm_exit_group : arm_preserves inv_fd_table_unique arm_exit_group :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_exit_group (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_exit_fd_state_frame _ eff m m' evs h))

/-- `fd_table_unique` × `wait4`: its descriptor-state frame. -/
theorem fd_table_unique_arm_wait4 : arm_preserves inv_fd_table_unique arm_wait4 :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_wait4 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table
      (Checks.Sys.Kernel.Exit.check_wait4_fd_state_frame i _ _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `exit`. -/
theorem pipes_within_capacity_arm_exit : arm_preserves inv_pipes_within_capacity arm_exit :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_exit (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_exit_fd_state_frame _ eff m m' evs h))

/-- `pipes_within_capacity` × `exit_group`. -/
theorem pipes_within_capacity_arm_exit_group :
    arm_preserves inv_pipes_within_capacity arm_exit_group :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_exit_group (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_exit_fd_state_frame _ eff m m' evs h))

/-- `pipes_within_capacity` × `wait4`: the same descriptor-state frame. -/
theorem pipes_within_capacity_arm_wait4 : arm_preserves inv_pipes_within_capacity arm_wait4 :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_wait4 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes
      (Checks.Sys.Kernel.Exit.check_wait4_fd_state_frame i _ _ _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
