import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Groups
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Kernel.Groups — getgroups and setgroups on the checked surface

The registration of `Checks/Sys/Kernel/Groups.lean`'s two checkers, under
the numbers they answer in `checked_table`, in the one file that
registration writes. `tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files under
`Checks/Arms/`, one per checker twin; its docstring is the shape it reads
and what it refuses. The file holds three sections, in the namespaces
`Checks/Arms/Kernel/Exit.lean` names:

- `Checks.Sys.Table`: the `CheckedArm`s (`arm_getgroups`, `arm_setgroups`)
  and their four `arm_unfold` lemmas each;
- `Checks.VmMapsDisjoint.Arms`: each arm's ledger fact,
  `arm_<name>_preserves_vm`;
- `Checks.Invariants`: one `<invariant>_arm_<name>` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the arms
are the rows of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table` (`arm_getgroups`, `arm_setgroups`), read at that commit. -/

/-! ## Why the getgroups spec, checker and witness are irreducible in this file

`getgroups` narrows its size with `Sys.Syscall.sint32`, and any `whnf` or
unification that reaches the decision on `sint32` of a symbolic word
recurses one unit at a time on the literal 2^31 and hits the recursion
limit (`Checks/Sys/Kernel/Groups.lean`'s proofs section says so of the
checker).  The structure instance below and its `rfl` lemmas are checked
by unification, and unfolding the three would put that decision in front
of it; held irreducible here they are compared by name.  The attribute is
local to this file, and `unfold` still opens each of the three through its
equation lemma, which is what the frame lemmas below do. -/

attribute [local irreducible] LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Groups.getgroups_spec
  LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Groups.check_getgroups
  LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Groups.getgroups_witness

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### getgroups (158) -/

/-- The acceptor `arm_getgroups` holds, `check_getgroups` at register `a0`,
behind a name the unifier does not unfold.  The alternations
`tools/gen_lean_checked.py` renders (`checked_table_preserves_vm`,
`registry_preserves`) try every arm's fact against every arm's goal, and
`arm_preserves inv c` reads `c.ca_check` alone, so a mismatched
alternative compares two arms' acceptors; with `check_getgroups` open
that comparison reaches the `sint32` decision this file's header names and
dies with the recursion limit, which `first` does not catch.  Held
irreducible, the comparison stops at this name and the alternative fails
as a mismatch.  `check_getgroups_a0_eq` opens it, and
`ca_check_arm_getgroups` states the arm through it, so nothing past the
arm sees the wrapper.  Lean-only: Rocq's `arm_getgroups` holds the checker
itself, since Rocq's unifier has no such limit to dodge. -/
@[irreducible] def check_getgroups_a0 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_result :=
  Checks.Sys.Kernel.Groups.check_getgroups (in_arg i 0) eff m

/-- `check_getgroups_a0` is `check_getgroups` at `a0`, by its equation
lemma.  Lean-only, as the wrapper is. -/
theorem check_getgroups_a0_eq (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_getgroups_a0 i eff m = Checks.Sys.Kernel.Groups.check_getgroups (in_arg i 0) eff m := by
  unfold check_getgroups_a0
  rfl

/-- getgroups (158).  The one argument the arm reads is register `a0`, the
whole word: `SYSCALL_DEFINE2(getgroups, int, gidsetsize, ...)`
(kernel/groups.c, Linux v6.18.46) receives it through riscv's wrapper as
`(__force int) gidsetsize` (`__SC_CAST`, include/linux/syscalls.h, applied
at arch/riscv/include/asm/syscall_wrapper.h, Linux v6.18.46), and the
narrowing is the checker's own `sint32`, so the arm hands it the register
unnarrowed.  `grouplist` (`a1`) is not read: the spec answers only the
branches on which nothing is stored through it -- a size of 0, a negative
size, a size below `ngroups`, and a nonzero size over an empty list, where
`groups_to_user`'s loop (kernel/groups.c, Linux v6.18.46) runs zero times
-- and declines the rest, including a stored `ngroups` above `NGROUPS_MAX`
(`Sys/Kernel/Groups.lean`). -/
def arm_getgroups : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 158 (fun i => Sys.Kernel.Groups.getgroups_spec (in_arg i 0) i)
  ca_check := fun i eff m => check_getgroups_a0 i eff m
  ca_witness := fun i m => Checks.Sys.Kernel.Groups.getgroups_witness (in_arg i 0) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Groups.check_getgroups_sound_ok (in_arg i 0) eff m m' evs i
      ((check_getgroups_a0_eq i eff m).symm.trans h)
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Groups.check_getgroups_sound_unmodeled (in_arg i 0) eff m i
      ((check_getgroups_a0_eq i eff m).symm.trans h)
  ca_complete_ok := fun i eff m m' evs h =>
    (check_getgroups_a0_eq i eff m).trans
      (Checks.Sys.Kernel.Groups.check_getgroups_complete_ok (in_arg i 0) eff m m' evs i h)
  ca_complete_unmodeled := fun i m eff h =>
    (check_getgroups_a0_eq i eff m).trans
      (Checks.Sys.Kernel.Groups.check_getgroups_complete_unmodeled (in_arg i 0) i m eff h)
  ca_receptive := fun i m => Checks.Sys.Kernel.Groups.getgroups_witness_ok (in_arg i 0) i m

@[arm_unfold] theorem ca_check_arm_getgroups (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_getgroups.ca_check i eff m = Checks.Sys.Kernel.Groups.check_getgroups (in_arg i 0) eff m :=
  check_getgroups_a0_eq i eff m
@[arm_unfold] theorem ca_witness_arm_getgroups (i : SyscallInput) (m : Model) :
    arm_getgroups.ca_witness i m = Checks.Sys.Kernel.Groups.getgroups_witness (in_arg i 0) m := rfl
@[arm_unfold] theorem sa_spec_arm_getgroups (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_getgroups.ca_arm.sa_spec i m o = Sys.Kernel.Groups.getgroups_spec (in_arg i 0) i m o := rfl
@[arm_unfold] theorem ca_no_arm_getgroups : ca_no arm_getgroups = 158 := rfl

/- ### setgroups (159) -/

/-- setgroups (159).  The arm reads no argument at all, which is the
kernel's order and not a shortcut: `SYSCALL_DEFINE2(setgroups, ...)`
(kernel/groups.c, Linux v6.18.46) asks `may_setgroups` before it looks at
`gidsetsize` or `grouplist`, so an unprivileged caller is refused `-EPERM`
whatever it passed, and the privileged path, which reads both, is the
spec's `unmodeled`. -/
def arm_setgroups : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 159 (fun i => Sys.Kernel.Groups.setgroups_spec i)
  ca_check := fun _ eff m => Checks.Sys.Kernel.Groups.check_setgroups eff m
  ca_witness := fun _ m => Checks.Sys.Kernel.Groups.setgroups_witness m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Groups.check_setgroups_sound_ok eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Groups.check_setgroups_sound_unmodeled eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Groups.check_setgroups_complete_ok eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Groups.check_setgroups_complete_unmodeled i m eff h
  ca_receptive := fun i m => Checks.Sys.Kernel.Groups.setgroups_witness_ok i m

@[arm_unfold] theorem ca_check_arm_setgroups (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_setgroups.ca_check i eff m = Checks.Sys.Kernel.Groups.check_setgroups eff m := rfl
@[arm_unfold] theorem ca_witness_arm_setgroups (i : SyscallInput) (m : Model) :
    arm_setgroups.ca_witness i m = Checks.Sys.Kernel.Groups.setgroups_witness m := rfl
@[arm_unfold] theorem sa_spec_arm_setgroups (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_setgroups.ca_arm.sa_spec i m o = Sys.Kernel.Groups.setgroups_spec i m o := rfl
@[arm_unfold] theorem ca_no_arm_setgroups : ca_no arm_setgroups = 159 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `getgroups` (158): every accepting branch is a `ret_only`, which hands
back the model it was given, so the ledger is what it was
(`check_getgroups_frame`, stated beside the checker in
`Checks/Sys/Kernel/Groups.lean`). -/
theorem arm_getgroups_preserves_vm : arm_preserves_vm arm_getgroups :=
  arm_preserves_of_frame arm_getgroups (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Groups.check_getgroups_frame _ eff m m' evs h)

/-- `setgroups` (159): the one accepting branch is the `-EPERM` `ret_only`
(`check_setgroups_frame`). -/
theorem arm_setgroups_preserves_vm : arm_preserves_vm arm_setgroups :=
  arm_preserves_of_frame arm_setgroups (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Groups.check_setgroups_frame eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## The descriptor-state frame lemmas

The two registry entries beside `vm_wf` read the `m_fd` subsystem, so one
frame lemma per checker over the whole record answers both.  The tree's
rule is that a checker's frame lemma lives beside the checker, and these
belong in `Checks/Sys/Kernel/Groups.lean`; they are written here, as
`Checks/Arms/Kernel/Exit.lean` wrote `check_exit_fd_state_frame`, because
the registration ticket's Lean edits are this file, and moving them there
changes nothing but their home. -/

/-- `check_getgroups` accepts only through `check_ret_only`, so the
descriptor subsystem is the one it was handed.  Same case split as
`check_getgroups_frame` (`Checks/Sys/Kernel/Groups.lean`), including its
`generalize` of the `sint32` decision, which that file's proofs section
says a symbolic word needs.  Lean-only: the Rocq tree registers no `m_fd`
invariant, so it has no descriptor frame to twin. -/
theorem check_getgroups_fd_state_frame (gidsetsize : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Kernel.Groups.check_getgroups gidsetsize eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Groups.check_getgroups at h
  dsimp only at h
  generalize Sys.Syscall.sint32 gidsetsize = n at h
  by_cases hneg : n < 0
  · simp only [hneg, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  · simp only [hneg, ↓reduceIte] at h
    by_cases hmax : Sys.Uapi.NGROUPS_MAX < (((m_creds m).cr_groups).length : Int)
    · exact absurd h (by simp only [hmax, ↓reduceIte, reduceCtorEq, not_false_eq_true])
    · simp only [hmax, ↓reduceIte] at h
      by_cases hzero : n = 0
      · simp only [hzero, ↓reduceIte] at h
        rw [check_ret_only_ok_iff] at h
        obtain ⟨-, rfl, -⟩ := h
        rfl
      · simp only [hzero, ↓reduceIte] at h
        by_cases hsmall : n < (((m_creds m).cr_groups).length : Int)
        · simp only [hsmall, ↓reduceIte] at h
          rw [check_ret_only_ok_iff] at h
          obtain ⟨-, rfl, -⟩ := h
          rfl
        · simp only [hsmall, ↓reduceIte] at h
          by_cases hempty : (((m_creds m).cr_groups).length : Int) = 0
          · simp only [hempty, ↓reduceIte] at h
            rw [check_ret_only_ok_iff] at h
            obtain ⟨-, rfl, -⟩ := h
            rfl
          · exact absurd h (by simp only [hempty, ↓reduceIte, reduceCtorEq, not_false_eq_true])

/-- `check_setgroups` accepts only through its `-EPERM` `check_ret_only`.
Lean-only, for the reason `check_getgroups_fd_state_frame` gives. -/
theorem check_setgroups_fd_state_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Groups.check_setgroups eff m = CheckOk m' evs) : m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Groups.check_setgroups at h
  cases hp : creds_privileged (m_creds m)
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  · exact absurd h (by simp only [hp, ↓reduceIte, reduceCtorEq, not_false_eq_true])

/-- `vm_wf` × `getgroups`: the ledger fact above. -/
theorem vm_wf_arm_getgroups : arm_preserves inv_vm_wf arm_getgroups :=
  Arms.arm_getgroups_preserves_vm

/-- `vm_wf` × `setgroups`: likewise. -/
theorem vm_wf_arm_setgroups : arm_preserves inv_vm_wf arm_setgroups :=
  Arms.arm_setgroups_preserves_vm

/-- `fd_table_unique` × `getgroups`. -/
theorem fd_table_unique_arm_getgroups : arm_preserves inv_fd_table_unique arm_getgroups :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_getgroups (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_getgroups_fd_state_frame _ eff m m' evs h))

/-- `fd_table_unique` × `setgroups`. -/
theorem fd_table_unique_arm_setgroups : arm_preserves inv_fd_table_unique arm_setgroups :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_setgroups (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_setgroups_fd_state_frame eff m m' evs h))

/-- `pipes_within_capacity` × `getgroups`. -/
theorem pipes_within_capacity_arm_getgroups :
    arm_preserves inv_pipes_within_capacity arm_getgroups :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_getgroups (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_getgroups_fd_state_frame _ eff m m' evs h))

/-- `pipes_within_capacity` × `setgroups`. -/
theorem pipes_within_capacity_arm_setgroups :
    arm_preserves inv_pipes_within_capacity arm_setgroups :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_setgroups (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_setgroups_fd_state_frame eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
