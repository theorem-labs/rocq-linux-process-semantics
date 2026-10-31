import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Mm.Mmap — brk, munmap and mmap on the checked surface

The registration of `Checks/Sys/Mm/Mmap.lean`'s three checkers in
`checked_table`, in the one file that registration writes.
`tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files
under `Checks/Arms/`, one per checker twin, so that registering an arm
creates or edits no hub but this file; its docstring is the shape it reads
and what it refuses. The file holds three sections, each in the
namespace its declarations had when those three hubs were written by
hand, so that no name moved with the file:

- `Checks.Sys.Table`: the `CheckedArm` (`arm_brk`, `arm_munmap` and
  `arm_mmap`) and its four `arm_unfold` lemmas;
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
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### brk (214) -/

/-- brk (214).  The register is read whole, as `brk_spec` reads it:
`SYSCALL_DEFINE1(brk, unsigned long, brk)` (mm/mmap.c, Linux v6.18.46)
takes its one argument as `unsigned long`, so no narrowing is owed.
`ca_arm` is the term `Sys/Registry/Mm/Mmap.lean`'s row builds, which
`checked_table_arms` checks.  The ledger fact this arm owes
`checked_table_preserves_vm` is `check_brk_preserves`, beside the
checker. -/
def arm_brk : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 214 (fun i => Sys.Mm.Mmap.brk_spec (in_arg i 0) i)
  ca_check := fun i eff m => Checks.Sys.Mm.Mmap.check_brk (in_arg i 0) eff m
  ca_witness := fun i m => Checks.Sys.Mm.Mmap.brk_witness (in_arg i 0) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Mm.Mmap.check_brk_sound_ok (in_arg i 0) i eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Mm.Mmap.check_brk_sound_unmodeled (in_arg i 0) i eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Mm.Mmap.check_brk_complete_ok (in_arg i 0) i eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Mm.Mmap.check_brk_complete_unmodeled (in_arg i 0) i m eff h
  ca_receptive := fun i m => Checks.Sys.Mm.Mmap.brk_witness_ok (in_arg i 0) i m

@[arm_unfold] theorem ca_check_arm_brk (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_brk.ca_check i eff m = Checks.Sys.Mm.Mmap.check_brk (in_arg i 0) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_brk (i : SyscallInput) (m : Model) :
    arm_brk.ca_witness i m = Checks.Sys.Mm.Mmap.brk_witness (in_arg i 0) m := rfl
@[arm_unfold] theorem sa_spec_arm_brk (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_brk.ca_arm.sa_spec i m o = Sys.Mm.Mmap.brk_spec (in_arg i 0) i m o := rfl
@[arm_unfold] theorem ca_no_arm_brk : ca_no arm_brk = 214 := rfl

/- ### munmap (215) -/

/-- munmap (215).  Both registers are read whole, as `munmap_spec` reads
them: `SYSCALL_DEFINE2(munmap, unsigned long, addr, size_t, len)`
(mm/mmap.c, Linux v6.18.46) takes two 64-bit types on riscv64, and the
`untagged_addr` it applies to `addr` (arch/riscv/include/asm/uaccess.h,
same version) is the identity while the process's pointer-masking length
is zero — which it is on every `execve`, and stays so until
`prctl(PR_SET_TAGGED_ADDR_CTRL)` or a tracer sets it through
`set_tagged_addr_ctrl` (arch/riscv/kernel/process.c, Linux v6.18.46),
the argument `Sys/Uaccess.lean` carries for `access_ok` — so no narrowing
is owed; the words go to `__vm_munmap` and `do_vmi_munmap` (mm/vma.c,
Linux v6.18.46), whose alignment, VA and length checks the spec models.
`ca_arm` is the term `Sys/Registry/Mm/Mmap.lean`'s row builds, which
`checked_table_arms` checks.  The ledger fact this arm owes
`checked_table_preserves_vm` is `check_munmap_preserves`, beside the
checker. -/
def arm_munmap : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 215 (fun i => Sys.Mm.Mmap.munmap_spec (in_arg i 0) (in_arg i 1) i)
  ca_check := fun i eff m => Checks.Sys.Mm.Mmap.check_munmap (in_arg i 0) (in_arg i 1) eff m
  ca_witness := fun i m => Checks.Sys.Mm.Mmap.munmap_witness (in_arg i 0) (in_arg i 1) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Mm.Mmap.check_munmap_sound_ok (in_arg i 0) (in_arg i 1) i eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Mm.Mmap.check_munmap_sound_unmodeled (in_arg i 0) (in_arg i 1) i eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Mm.Mmap.check_munmap_complete_ok (in_arg i 0) (in_arg i 1) i eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Mm.Mmap.check_munmap_complete_unmodeled (in_arg i 0) (in_arg i 1) i m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Mm.Mmap.munmap_witness_ok (in_arg i 0) (in_arg i 1) i m

@[arm_unfold] theorem ca_check_arm_munmap (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_munmap.ca_check i eff m
      = Checks.Sys.Mm.Mmap.check_munmap (in_arg i 0) (in_arg i 1) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_munmap (i : SyscallInput) (m : Model) :
    arm_munmap.ca_witness i m = Checks.Sys.Mm.Mmap.munmap_witness (in_arg i 0) (in_arg i 1) m := rfl
@[arm_unfold] theorem sa_spec_arm_munmap (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_munmap.ca_arm.sa_spec i m o = Sys.Mm.Mmap.munmap_spec (in_arg i 0) (in_arg i 1) i m o := rfl
@[arm_unfold] theorem ca_no_arm_munmap : ca_no arm_munmap = 215 := rfl

/- ### mmap (222) -/

/-- mmap (222).  The six registers are read whole, as `mmap_spec` reads
them: riscv's `riscv_sys_mmap` (arch/riscv/kernel/sys_riscv.c, Linux
v6.18.46) and the `SYSCALL_DEFINE6(mmap, …)` that calls it take all six
arguments as `unsigned long`, and the anonymous arm the spec models
never reads `fd` (`ksys_mmap_pgoff`, mm/mmap.c, same version, resolves a
file only inside `if (!(flags & MAP_ANONYMOUS))`), so no narrowing is
owed.  `ca_arm` is the term `Sys/SyscallTable.lean`'s row builds, which
`checked_table_arms` checks.  The ledger fact this arm owes
`checked_table_preserves_vm` is `check_mmap_preserves`, beside the
checker. -/
def arm_mmap : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 222 (fun i => Sys.Mm.Mmap.mmap_spec (in_arg i 0) (in_arg i 1)
    (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)
  ca_check := fun i eff m => Checks.Sys.Mm.Mmap.check_mmap (in_arg i 0) (in_arg i 1)
    (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m
  ca_witness := fun i m => Checks.Sys.Mm.Mmap.mmap_witness (in_arg i 0) (in_arg i 1)
    (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m
  ca_sound_ok := fun i eff m m' evs h => Checks.Sys.Mm.Mmap.check_mmap_sound_ok (in_arg i 0)
    (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h => Checks.Sys.Mm.Mmap.check_mmap_sound_unmodeled
    (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m i h
  ca_complete_ok := fun i eff m m' evs h => Checks.Sys.Mm.Mmap.check_mmap_complete_ok
    (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h => Checks.Sys.Mm.Mmap.check_mmap_complete_unmodeled
    (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m i eff h
  ca_receptive := fun i m => Checks.Sys.Mm.Mmap.mmap_witness_ok (in_arg i 0) (in_arg i 1)
    (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m

@[arm_unfold] theorem ca_check_arm_mmap (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_mmap.ca_check i eff m = Checks.Sys.Mm.Mmap.check_mmap (in_arg i 0) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_mmap (i : SyscallInput) (m : Model) :
    arm_mmap.ca_witness i m = Checks.Sys.Mm.Mmap.mmap_witness (in_arg i 0) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m := rfl
@[arm_unfold] theorem sa_spec_arm_mmap (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_mmap.ca_arm.sa_spec i m o = Sys.Mm.Mmap.mmap_spec (in_arg i 0) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o := rfl
@[arm_unfold] theorem ca_no_arm_mmap : ca_no arm_mmap = 222 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `brk` (214): no frame lemma — a grow grants and a shrink frees — so
the preserves lemma directly (`check_brk_preserves`, stated beside the
checker in `Checks/Sys/Mm/Mmap.lean`). -/
theorem arm_brk_preserves_vm : arm_preserves_vm arm_brk :=
  fun i eff m m' evs h hwf => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Mm.Mmap.check_brk_preserves _ eff m m' evs h hwf

/-- `munmap` (215): likewise — an exact teardown removes an entry
(`check_munmap_preserves`, same file). -/
theorem arm_munmap_preserves_vm : arm_preserves_vm arm_munmap :=
  fun i eff m m' evs h hwf => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Mm.Mmap.check_munmap_preserves _ _ eff m m' evs h hwf

/-- `mmap` (222): no frame lemma — a grant changes the ledger — so the
preserves lemma directly (`check_mmap_preserves`, stated beside the
checker in `Checks/Sys/Mm/Mmap.lean`). -/
theorem arm_mmap_preserves_vm : arm_preserves_vm arm_mmap :=
  fun i eff m m' evs h hwf => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Mm.Mmap.check_mmap_preserves _ _ _ _ _ _ eff m m' evs h hwf

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
belong in `Checks/Sys/Mm/Mmap.lean`; they were written beside the
registry by ticket I3, which kept its Lean edits to the registry's own
files, and moving it there changes nothing but its home. -/

/-! ### `check_mmap`

TWO REASONS THE `mmap` FRAME IS NOT ONE LINE, both found by building it.

FIRST, `vm_frame` does not apply.  Its loop reaches every branch through
`split at h`, and `split` on `check_mmap`'s outermost guard runs its own
`simp` out of steps: the guards sit above a match on `SyscallEffect`
whose branches are the whole checker, so the discriminant abstraction is
over a term the size of the file.  `Checks/Sys/Mm/Mmap.lean`'s own
`check_mmap_preserves` meets this and answers it the same way — `by_cases`
on each guard with `ite_eq_left`/`ite_eq_right`, and `split at h` only
INSIDE a policy branch, where the term is small enough — so the skeleton
below is that proof's, with `vm_frame` finishing each branch.  It is not
a copy for its own sake: the branch structure is the checker's, so the
two proofs go stale together, and a policy arm added to `check_mmap`
fails this lemma with an unsolved `if` rather than passing vacuously.

SECOND, `rfl` does not close every branch, because `with_mmap_backing` is
an `if` on MAP_NORESERVE rather than a record update: both of its answers
keep `m_fd`, but neither is the other, so the projection has to be taken
through the branch once.  The two lemmas below do that, and `fd_frame`
is `vm_frame` with them in its closer. -/

set_option maxRecDepth 20000 in
/-- `MAP_NORESERVE` decides whether a grant records lazy backing; neither
answer touches the descriptor subsystem.  `vm_add_lazy` rebuilds the
model through `with_vm_backing`, which carries `m.m_fd` across
(`State/Model.lean`), so each branch is `rfl` and only the `if` needs
taking apart. -/
theorem fd_state_with_mmap_backing (flags a n : word) (m : Model) :
    (Sys.Mm.Mmap.with_mmap_backing flags a n m).m_fd = m.m_fd := by
  unfold Sys.Mm.Mmap.with_mmap_backing
  cases Sys.Mm.Mmap.mmap_noreserve_b flags <;> rfl

set_option maxRecDepth 20000 in
/-- A replacement is a `vm_forget_range` under that same grant, and
`vm_forget_range` is `with_vm_backing` too. -/
theorem fd_state_with_mmap_replacement (flags a n : word) (m : Model) :
    (Sys.Mm.Mmap.with_mmap_replacement flags a n m).m_fd = m.m_fd := by
  unfold Sys.Mm.Mmap.with_mmap_replacement
  rw [fd_state_with_mmap_backing] <;> rfl

/-- `vm_frame` with the two lemmas above in its closer.  The `<;> rfl`
after each `rw` is there because `rw` closes a goal only when its own
`rfl` attempt succeeds, and the remaining model is a stack of plain
definitions it does not unfold; on a goal `rw` did close, `<;> rfl` runs
`rfl` on no goals and succeeds. -/
macro "fd_frame " h:ident : tactic =>
  `(tactic| (repeat' vm_step $h:ident) <;>
      first
        | rfl
        | (rw [fd_state_with_mmap_backing] <;> rfl)
        | (rw [fd_state_with_mmap_replacement] <;> rfl))

-- The budgets are measured, not guessed, and each is load-bearing on its
-- own (both deep reviews of #1096 rebuilt the module with each removed in
-- turn): without `maxHeartbeats` the FIRST `by_cases` times out at
-- `whnf` with the default 200000, since deciding the guard means
-- reducing a term that is the whole `check_mmap` with every policy
-- branch inlined; without `maxRecDepth` the stock 512 is exhausted by
-- `fd_frame` in the `hg1`, `hp3` and `hp4` branches -- every branch
-- whose accepted model goes through `with_mmap_backing`.  40000 is the
-- first round figure above what the deepest of them needs; 20000 does
-- for the two small lemmas above.
-- WHY THIS LEMMA NEEDS THEM AND `check_mmap_preserves` (`Checks/Sys/Mm/
-- Mmap.lean`), which walks the same seven guards, needs neither: that
-- proof reads `m_vmmaps`, the field these arms WRITE, and `vm_step` has
-- a rewrite lemma for every setter on the path; this one reads `m_fd`,
-- which the path only CARRIES, through `with_vm_backing`'s
-- `Model.mkModelOf m.m_fd ...`, and the two lemmas above reach it by
-- `rfl` through the whole model stack.  The State-level fact that
-- would retire all three budgets is the `m_fd` twin of
-- `m_vmmaps_with_vm_backing` (`State/Model.lean`), which the model does
-- not state today; add it there and `fd_frame` shrinks to a rewrite.
-- If a future `check_mmap` arm makes either budget fail again, the
-- number to raise is the one the error names.
-- The MAP_FIXED_NOREPLACE port (A18) added the `hp5` and `hp6` branches,
-- whose grants go through `with_mmap_backing` too, and both proofs walk
-- them, so both walk nine top-level guards, `hg1`-`hg3` and `hp1`-`hp6`,
-- where the count above says seven.  Nor is the branch list above the
-- set of branches through `with_mmap_backing`, before the port or after
-- it: `hg1` answers -EINVAL without a grant, and the hint-placed grants
-- of `hp1` and `hp2` go through it as well.  This lemma closes on all
-- nine under the same two budgets; which branches alone exhaust the
-- stock 512 was not re-measured.
set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- `check_mmap` writes the memory ledger and the lazy backing and
nothing else, so the descriptor subsystem is the one it was handed. -/
theorem check_mmap_fd_state_frame (addr len prot flags fd off : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Mm.Mmap.check_mmap addr len prot flags fd off eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Mm.Mmap.check_mmap at h
  dsimp only at h
  generalize page_round_up_Z (bv_unsigned len) = N at h
  generalize bv_unsigned addr = A at h
  by_cases hg1 : (!Sys.Mm.Mmap.mmap_off_aligned_b off) = true
  · rw [ite_eq_left hg1] at h; fd_frame h
  rw [ite_eq_right hg1] at h
  by_cases hg2 : (!Sys.Mm.Mmap.mmap_anon_b flags) = true
  · rw [ite_eq_left hg2] at h; cases h
  rw [ite_eq_right hg2] at h
  by_cases hg3 : Sys.Syscall.w_is0 len = true
  · rw [ite_eq_left hg3] at h; fd_frame h
  rw [ite_eq_right hg3] at h
  by_cases hp1 : Sys.Mm.Mmap.mmap_modeled_b prot flags off = true
  · rw [ite_eq_left hp1] at h; fd_frame h
  rw [ite_eq_right hp1] at h
  by_cases hp2 : Sys.Mm.Mmap.mmap_noaccess_b prot flags off = true
  · rw [ite_eq_left hp2] at h; fd_frame h
  rw [ite_eq_right hp2] at h
  by_cases hp3 : Sys.Mm.Mmap.mmap_fixed_noaccess_b prot flags off = true
  · rw [ite_eq_left hp3] at h
    by_cases hw : two_pow_64 ≤ A + N
    · rw [ite_eq_left hw] at h
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h
      all_goals first | cases h | rw [check_ret_only_model h]
    · rw [ite_eq_right hw] at h
      fd_frame h
  rw [ite_eq_right hp3] at h
  by_cases hp4 : Sys.Mm.Mmap.mmap_fixed_rw_b prot flags off = true
  · rw [ite_eq_left hp4] at h
    by_cases hw : two_pow_64 ≤ A + N
    · rw [ite_eq_left hw] at h
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h
      all_goals first | cases h | rw [check_ret_only_model h]
    · rw [ite_eq_right hw] at h
      fd_frame h
  rw [ite_eq_right hp4] at h
  by_cases hp5 : Sys.Mm.Mmap.mmap_noreplace_noaccess_b prot flags off = true
  · rw [ite_eq_left hp5] at h
    by_cases hw : two_pow_64 ≤ A + N
    · rw [ite_eq_left hw] at h
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h
      all_goals first | cases h | rw [check_ret_only_model h]
    · rw [ite_eq_right hw] at h
      fd_frame h
  rw [ite_eq_right hp5] at h
  by_cases hp6 : Sys.Mm.Mmap.mmap_noreplace_rw_b prot flags off = true
  · rw [ite_eq_left hp6] at h
    by_cases hw : two_pow_64 ≤ A + N
    · rw [ite_eq_left hw] at h
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h
      all_goals first | cases h | rw [check_ret_only_model h]
    · rw [ite_eq_right hw] at h
      fd_frame h
  rw [ite_eq_right hp6] at h
  cases h

/-- `vm_wf` × `brk`: likewise; this arm writes the ledger both ways, a grow
granting and a shrink freeing, and the fact behind it is
`check_brk_preserves`.  The `mmap` entry below calls itself "the entry
whose arm does write the ledger": it was written when `mmap` was the only
registered arm that did, and this entry and `munmap`'s are the others. -/
theorem vm_wf_arm_brk : arm_preserves inv_vm_wf arm_brk :=
  Arms.arm_brk_preserves_vm

/-- `vm_wf` × `munmap`: likewise; the fact behind it is
`check_munmap_preserves`. -/
theorem vm_wf_arm_munmap : arm_preserves inv_vm_wf arm_munmap :=
  Arms.arm_munmap_preserves_vm

/-- `vm_wf` × `mmap`: likewise; this is the entry whose arm does write
the ledger, and the fact behind it is `check_mmap_preserves`. -/
theorem vm_wf_arm_mmap : arm_preserves inv_vm_wf arm_mmap :=
  Arms.arm_mmap_preserves_vm

/-- `fd_table_unique` × `brk`: the break touches no descriptor; the frame
is stated beside the checker, as the header above says these should be. -/
theorem fd_table_unique_arm_brk : arm_preserves inv_fd_table_unique arm_brk :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_brk (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table
      (Checks.Sys.Mm.Mmap.check_brk_fd_state_frame _ eff m m' evs h))

/-- `fd_table_unique` × `munmap`: a teardown touches no descriptor. -/
theorem fd_table_unique_arm_munmap : arm_preserves inv_fd_table_unique arm_munmap :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_munmap (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table
      (Checks.Sys.Mm.Mmap.check_munmap_fd_state_frame _ _ eff m m' evs h))

/-- `fd_table_unique` × `mmap`: an anonymous grant touches no descriptor. -/
theorem fd_table_unique_arm_mmap : arm_preserves inv_fd_table_unique arm_mmap :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_mmap (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_mmap_fd_state_frame _ _ _ _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `brk`. -/
theorem pipes_within_capacity_arm_brk : arm_preserves inv_pipes_within_capacity arm_brk :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_brk (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes
      (Checks.Sys.Mm.Mmap.check_brk_fd_state_frame _ eff m m' evs h))

/-- `pipes_within_capacity` × `munmap`. -/
theorem pipes_within_capacity_arm_munmap :
    arm_preserves inv_pipes_within_capacity arm_munmap :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_munmap (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes
      (Checks.Sys.Mm.Mmap.check_munmap_fd_state_frame _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `mmap`. -/
theorem pipes_within_capacity_arm_mmap : arm_preserves inv_pipes_within_capacity arm_mmap :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_mmap (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_mmap_fd_state_frame _ _ _ _ _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
