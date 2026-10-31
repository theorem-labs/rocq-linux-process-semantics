import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mremap
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Mm.Mremap — mremap on the checked surface

The registration of `Checks/Sys/Mm/Mremap.lean`'s checker in
`checked_table`, in the one file that registration writes.
`tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files
under `Checks/Arms/`, one per checker twin, so that registering an arm
creates or edits no hub but this file; its docstring is the shape it reads
and what it refuses. The file holds three sections, each in the
namespace its declarations had when those three hubs were written by
hand, so that no name moved with the file:

- `Checks.Sys.Table`: the `CheckedArm` (`arm_mremap`) and its four
  `arm_unfold` lemmas;
- `Checks.VmMapsDisjoint.Arms`: the arm's ledger fact,
  `arm_<name>_preserves_vm`, which `checked_table_preserves_vm`'s
  alternation names;
- `Checks.Invariants`: one `<invariant>_arm_<name>` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`, which
  `registry_preserves`'s alternation names.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arms are the rows of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table`, read at that commit.

TWO LEMMAS THE ARM IS BUILT FROM ARE STATED HERE, not beside the checker.
The checker twin landed without them (its header gives the registration
to this ticket), and this ticket's files are the arm file and the pins:
`check_mremap_preserves`, Rocq's lemma of that name in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, whose Lean twin the
hand-written `Checks/VmMapsDisjoint.lean` does not carry, and
`check_mremap_fd_state_frame`, which has no Rocq twin because Rocq's
invariant registry is `vm_wf` alone.  The tree's rule is that a checker's
frame lemma lives beside the checker, as `check_munmap_fd_state_frame`
does in `Checks/Sys/Mm/Mmap.lean`; moving these two there changes nothing
but their home. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### mremap (216) -/

/-- mremap (216).  The four registers `a0`-`a3` are read whole, as
`mremap_spec` reads them, and `a4` (`new_addr`) is not read at all:
`SYSCALL_DEFINE5(mremap, unsigned long, addr, unsigned long, old_len,
unsigned long, new_len, unsigned long, flags, unsigned long, new_addr)`
(mm/mremap.c, Linux v6.18.46) declares all five `unsigned long`, 64 bits
on riscv64, so no narrowing is owed; `do_mremap` reads `new_addr` only
under `MREMAP_FIXED` or `MREMAP_DONTUNMAP` (`vrm_implies_new_addr`,
mm/mremap.c, same version), and the spec declines every flag word but
`MREMAP_MAYMOVE`.  The `untagged_addr` the syscall body applies to
`addr` before `do_mremap` sees it (arch/riscv/include/asm/uaccess.h, same
version) is the identity while
the process's pointer-masking length is zero, as the `munmap` arm in
`Checks/Arms/Mm/Mmap.lean` records.  `ca_arm` is the term
`Sys/Registry/Mm/Mremap.lean`'s row builds, which `checked_table_arms`
checks.  The ledger fact this arm owes `checked_table_preserves_vm` is
`check_mremap_preserves`, below. -/
def arm_mremap : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 216
    (fun i => Sys.Mm.Mremap.mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m =>
    Checks.Sys.Mm.Mremap.check_mremap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m =>
    Checks.Sys.Mm.Mremap.mremap_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Mm.Mremap.check_mremap_sound_ok (in_arg i 0) (in_arg i 1) (in_arg i 2)
      (in_arg i 3) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Mm.Mremap.check_mremap_sound_unmodeled (in_arg i 0) (in_arg i 1) (in_arg i 2)
      (in_arg i 3) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Mm.Mremap.check_mremap_complete_ok (in_arg i 0) (in_arg i 1) (in_arg i 2)
      (in_arg i 3) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Mm.Mremap.check_mremap_complete_unmodeled (in_arg i 0) (in_arg i 1) (in_arg i 2)
      (in_arg i 3) m i eff h
  ca_receptive := fun i m =>
    Checks.Sys.Mm.Mremap.mremap_witness_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

@[arm_unfold] theorem ca_check_arm_mremap (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_mremap.ca_check i eff m = Checks.Sys.Mm.Mremap.check_mremap (in_arg i 0) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_mremap (i : SyscallInput) (m : Model) :
    arm_mremap.ca_witness i m = Checks.Sys.Mm.Mremap.mremap_witness (in_arg i 0) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) m := rfl
@[arm_unfold] theorem sa_spec_arm_mremap (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_mremap.ca_arm.sa_spec i m o = Sys.Mm.Mremap.mremap_spec (in_arg i 0) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) i m o := rfl
@[arm_unfold] theorem ca_no_arm_mremap : ca_no arm_mremap = 216 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- An accepted `mremap` keeps the ledger well formed.  Rocq:
`VmMapsDisjoint.check_mremap_preserves`, whose proof this follows branch
for branch: errno answers hand the model back; a grow in place and a move each
drop the source entry and record the new one over a range that
`mremap_inplace_grow_b` or `mremap_fresh_b` found free of the rest
(`maps_wf_cons_free` over `maps_wf_filter`).  The two nonzero-size facts
come from the size gate (`page_align_is0_b` false, so the rounded
`new_len` is positive) and from the ceiling conjunct each placement
predicate carries, which keeps the rounded length below `2^64` so `u64`
reads it back.

The gates are walked with the checker twin's idiom, for the reason its
header gives: a `Bool` gate by `cases hg : …`, the `TASK_SIZE` and
non-growth comparisons by `Decidable.em`, each followed by `simp only [hg,
↓reduceIte] at h`, so that no tactic reduces an `if` on
`page_round_up_Z (bv_unsigned w)` to find its head. -/
theorem check_mremap_preserves (old old_size new_size flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Mm.Mremap.check_mremap old old_size new_size flags eff m = CheckOk m' evs)
    (hwf : vm_wf (m_vmmaps m)) : vm_wf (m_vmmaps m') := by
  unfold Checks.Sys.Mm.Mremap.check_mremap at h
  have hac := alloc_top_lt (m_vmmaps m)
  unfold two_pow_64 at hac
  have hor := word_range old
  cases hshape : (!(bv_unsigned flags == MREMAP_MAYMOVE)) with
  | true => simp only [hshape, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [hshape, Bool.false_eq_true, ↓reduceIte] at h
  cases halign : (!(bv_unsigned old % page_size == 0)) with
  | true =>
    simp only [halign, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [halign, Bool.false_eq_true, ↓reduceIte] at h
  cases hnew : page_align_is0_b new_size with
  | true =>
    simp only [hnew, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [hnew, Bool.false_eq_true, ↓reduceIte] at h
  have htask := Decidable.em (TASK_SIZE < page_round_up_Z (bv_unsigned new_size))
  cases htask with
  | inl htask => simp only [htask, ↓reduceIte, reduceCtorEq] at h
  | inr htask =>
  simp only [htask, ↓reduceIte] at h
  cases hold : page_align_is0_b old_size with
  | true => simp only [hold, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [hold, Bool.false_eq_true, ↓reduceIte] at h
  cases hsrc : (!(mremap_source_b (m_vmmaps m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
                    (page_round_up_Z (bv_unsigned old_size))
                  && mremap_backing_uniform_b m old
                    (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))) with
  | true => simp only [hsrc, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [hsrc, Bool.false_eq_true, ↓reduceIte] at h
  have heq := Decidable.em (page_round_up_Z (bv_unsigned new_size) ≤ page_round_up_Z (bv_unsigned old_size))
  cases heq with
  | inl heq => simp only [heq, ↓reduceIte, reduceCtorEq] at h
  | inr heq =>
  simp only [heq, ↓reduceIte] at h
  -- the new length is a nonzero number of pages
  unfold page_align_is0_b at hnew
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hnew
  obtain ⟨hnew0, -⟩ := hnew
  have hnewZ : 0 < page_round_up_Z (bv_unsigned new_size) :=
    page_round_up_pos _ (by have := w_is0_false new_size hnew0; have := word_range new_size; omega)
  -- the source is a live entry, and its size fits in a word; the
  -- backing-uniformity conjunct is about the sparse ledgers, not about
  -- `vm_maps`, and the ownership conjuncts are what this needs
  simp only [Bool.not_eq_false', Bool.and_eq_true] at hsrc
  obtain ⟨hsrc, -⟩ := hsrc
  unfold mremap_source_b at hsrc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsrc
  obtain ⟨⟨⟨hoceil, -⟩, hhas⟩, -⟩ := hsrc
  have holdZ := Checks.Sys.Mm.Mremap.page_round_up_Z_word_nonneg old_size
  obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons w ws => simp only [reduceCtorEq] at h
  | nil =>
  cases copyins with
  | cons c copyins => simp only [reduceCtorEq] at h
  | nil =>
  dsimp only at h
  cases herr : errno_ret_in mremap_errnos r with
  | true =>
    simp only [herr, ↓reduceIte] at h
    cases zs with
    | cons z zs => simp only [reduceCtorEq] at h
    | nil =>
    cases us with
    | cons u us => simp only [reduceCtorEq] at h
    | nil =>
    cases cs with
    | cons c cs => simp only [reduceCtorEq] at h
    | nil =>
    simp only [check_result.CheckOk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hwf
  | false =>
  simp only [herr, Bool.false_eq_true, ↓reduceIte] at h
  cases hret : bv_eqb r old with
  | true =>
    simp only [hret, ↓reduceIte] at h
    cases hgrow : mremap_inplace_grow_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
        (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) with
    | true =>
      simp only [hgrow, ↓reduceIte] at h
      split at h
      · simp only [check_result.CheckOk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        unfold mremap_inplace_grow_b at hgrow
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hgrow
        obtain ⟨⟨hgceil, hgfree⟩, -⟩ := hgrow
        simp only [vm_wf, vmm_mremap_next, mremap_maps_next]
        exact maps_wf_cons_free _ old _ (maps_wf_filter _ _ hwf)
          (by rw [u64 _ (by omega) (by omega)]; omega)
          (region_free_app_r _ _ _ _ hgfree)
      · simp only [reduceCtorEq] at h
    | false => simp only [hgrow, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

  | false =>
  -- the move: the source entry dropped, the destination recorded
  simp only [hret, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · rename_i hmove
    simp only [check_result.CheckOk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true] at hmove
    obtain ⟨⟨⟨⟨-, hfresh⟩, -⟩, -⟩, -⟩ := hmove
    -- SIX conjuncts, as Rocq's proof counts them: destination distinct
    -- from the source, aligned, positive, under the ceiling,
    -- `region_free` and the final budget.  The ceiling and `region_free`
    -- are the two this proof uses.
    unfold mremap_fresh_b at hfresh
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfresh
    obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hfceil⟩, hffree⟩, -⟩ := hfresh
    have hrr := word_range r
    simp only [vm_wf, vmm_mremap_next, mremap_maps_next]
    exact maps_wf_cons_free _ r _ (maps_wf_filter _ _ hwf)
      (by rw [u64 _ (by omega) (by omega)]; omega)
      (region_free_filter _ _ _ _ (region_free_app_r _ _ _ _ hffree))
  · simp only [reduceCtorEq] at h

/-- `mremap` (216): no frame lemma — a resize or a move rewrites the
ledger — so the preserves lemma directly (`check_mremap_preserves`,
above). -/
theorem arm_mremap_preserves_vm : arm_preserves_vm arm_mremap :=
  fun i eff m m' evs h hwf => by
    simp only [arm_unfold] at h
    exact check_mremap_preserves _ _ _ _ eff m m' evs h hwf

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## The descriptor-state frame lemma

The two registry entries beside `vm_wf` read the `m_fd` subsystem, so one
frame lemma over the whole record answers both. -/

/-- A resize or a move writes the ledger and the lazy backing and nothing
else: `mremap_model_next` is `vm_resize_backing` over `with_vmmaps`, and
both rebuild the model around the `m_fd` they were handed
(`State/Model.lean`'s `with_vm_backing` and `with_vmmaps`), so the
projection is `rfl` without deciding the `if` on the source's laziness
inside `vm_resize_backing`. -/
theorem fd_state_mremap_model_next (m : Model) (old old_n dst new_n : word) :
    (mremap_model_next m old old_n dst new_n).m_fd = m.m_fd := rfl

/-- `check_mremap` writes the memory ledger and the lazy backing and
nothing else, so the descriptor subsystem is the one it was handed.  The
walk is `check_mremap_preserves`'s, for the same reason; every accepted
model is `m` itself or `mremap_model_next` of it. -/
theorem check_mremap_fd_state_frame (old old_size new_size flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : Checks.Sys.Mm.Mremap.check_mremap old old_size new_size flags eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Mm.Mremap.check_mremap at h
  cases hshape : (!(bv_unsigned flags == MREMAP_MAYMOVE)) with
  | true => simp only [hshape, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [hshape, Bool.false_eq_true, ↓reduceIte] at h
  cases halign : (!(bv_unsigned old % page_size == 0)) with
  | true =>
    simp only [halign, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [halign, Bool.false_eq_true, ↓reduceIte] at h
  cases hnew : page_align_is0_b new_size with
  | true =>
    simp only [hnew, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [hnew, Bool.false_eq_true, ↓reduceIte] at h
  have htask := Decidable.em (TASK_SIZE < page_round_up_Z (bv_unsigned new_size))
  cases htask with
  | inl htask => simp only [htask, ↓reduceIte, reduceCtorEq] at h
  | inr htask =>
  simp only [htask, ↓reduceIte] at h
  cases hold : page_align_is0_b old_size with
  | true => simp only [hold, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [hold, Bool.false_eq_true, ↓reduceIte] at h
  cases hsrc : (!(mremap_source_b (m_vmmaps m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
                    (page_round_up_Z (bv_unsigned old_size))
                  && mremap_backing_uniform_b m old
                    (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))) with
  | true => simp only [hsrc, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [hsrc, Bool.false_eq_true, ↓reduceIte] at h
  have heq := Decidable.em (page_round_up_Z (bv_unsigned new_size) ≤ page_round_up_Z (bv_unsigned old_size))
  cases heq with
  | inl heq => simp only [heq, ↓reduceIte, reduceCtorEq] at h
  | inr heq =>
  simp only [heq, ↓reduceIte] at h
  obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons w ws => simp only [reduceCtorEq] at h
  | nil =>
  cases copyins with
  | cons c copyins => simp only [reduceCtorEq] at h
  | nil =>
  dsimp only at h
  cases herr : errno_ret_in mremap_errnos r with
  | true =>
    simp only [herr, ↓reduceIte] at h
    cases zs with
    | cons z zs => simp only [reduceCtorEq] at h
    | nil =>
    cases us with
    | cons u us => simp only [reduceCtorEq] at h
    | nil =>
    cases cs with
    | cons c cs => simp only [reduceCtorEq] at h
    | nil =>
    simp only [check_result.CheckOk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | false =>
  simp only [herr, Bool.false_eq_true, ↓reduceIte] at h
  cases hret : bv_eqb r old with
  | true =>
    simp only [hret, ↓reduceIte] at h
    cases hgrow : mremap_inplace_grow_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
        (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) with
    | true =>
      simp only [hgrow, ↓reduceIte] at h
      split at h
      · simp only [check_result.CheckOk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact fd_state_mremap_model_next _ _ _ _ _
      · simp only [reduceCtorEq] at h
    | false => simp only [hgrow, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

  | false =>
  simp only [hret, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · simp only [check_result.CheckOk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fd_state_mremap_model_next _ _ _ _ _
  · simp only [reduceCtorEq] at h

/-- `vm_wf` × `mremap`: this arm writes the ledger, and the fact behind it
is `check_mremap_preserves`. -/
theorem vm_wf_arm_mremap : arm_preserves inv_vm_wf arm_mremap :=
  Arms.arm_mremap_preserves_vm

/-- `fd_table_unique` × `mremap`: a resize or a move touches no
descriptor. -/
theorem fd_table_unique_arm_mremap : arm_preserves inv_fd_table_unique arm_mremap :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_mremap (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_mremap_fd_state_frame _ _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `mremap`. -/
theorem pipes_within_capacity_arm_mremap :
    arm_preserves inv_pipes_within_capacity arm_mremap :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_mremap (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_mremap_fd_state_frame _ _ _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
