import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Mm.Mremap — the mremap (216) checker, its witness, and their proofs

Mirrors `theories/LinuxProcessSem/Checks/Sys/Mm/Mremap.v` and
`theories/LinuxProcessSem/Checks/Witness/Mm/Mremap.v`, which hold the
checker and the witness for the syscall `Sys/Mm/Mremap.v` defines, and no
other: the executable acceptor `check_mremap`, the four lemmas relating it
to the relational `mremap_spec` of `Sys/Mm/Mremap.lean`, the progress
witness `mremap_witness`, and the lemma that the spec admits what the
witness exhibits.  The checker and the witness are the computable side of
the spec and are NOT part of the trusted specification; what a run may
trust is the spec, and these lemmas are what lets a verdict of the checker
stand for an answer of the spec.  Its pins are
`Checks/Cases/Checks/Sys/Mm/Mremap.lean`.

The Rocq checker's helper lemmas lean on
`page_round_up_Z_nonneg`, which Rocq proves in `Checks/BudgetPremise.v` and
again in `Checks/Sys/Mm/Mmap.v` and no Lean module carries; the two
non-negativity facts are established inline from `word_unsigned_range`
by `omega`, which decides division by the literal `page_size`.

THE PROOFS keep Rocq's shape, gate by gate.  Each direction walks the
gates in the spec's order: a `Bool` gate is split with `cases hg : …` and
re-reduced with `simp only [hg, ↓reduceIte]` on both sides, so that the
checker and the spec are always looking at the same branch.  Past
`get_model` the effect is destructured into its six fields; the errno
return, the `bv_eqb r old` test, the two
placement guards are split in the checker's order; and the accepted
effect's fields are recovered from the three list equalities
(`listNN_eqb_eq`, `listCopy_eqb_eq`) before the spec's `alt`/`bind`
witness is assembled from `choose_ok`, `modify_ok` and `pure_ok`.  The
complete direction works the `alt` apart with `alt_iff`, `bind_choose_iff`
and `bind_modify_iff`, then makes the checker's tests fire by rewriting
with the facts the spec's branch established — `errno_ret_in_intro` on
the errno branch, `bv_eqb_refl` and the two `*_ret_not_errno` lemmas on
the success branches.  Rocq's `Int` comparisons `Z.ltb`/`Z.leb` are
Lean's decidable `<`/`≤`, as in the spec twin.

ONE LEAN-ONLY CONSTRAINT shapes the tactic choice.  A default-transparency
`whnf` of `Int.decLt`/`Int.decLe`/`Int.decEq` on `page_round_up_Z
(bv_unsigned w)` does not get stuck on `w`: `Int.add`/`Int.sub` match on
both operands, `Nat.add x 4096` peels one `succ` at a time, and the
reduction is thousands of steps deep before anything is stuck, so
`maxRecDepth` fires (raising it does not help — `TASK_SIZE` is `2^47`).
Every tactic that reduces the goal to find its head — `by_cases`,
`rcases`, `split`, `exact`, `refine`, `apply` — trips it while the goal is
the spec applied with such an `if` at its head.  So a `Prop` gate
(`TASK_SIZE <`, the non-growth comparison) is split with `have hg :=
Decidable.em …; cases hg with …`, which reduces nothing, a `Bool` gate with
`cases hg : …`, and a goal is closed only after `simp only [hg,
↓reduceIte]` has removed the `if`.  In the complete direction the spec
applied is the HYPOTHESIS `h`, and the `constructorNameAsVariable` linter
`whnf`s every hypothesis's type, so it is switched off on those two
theorems, as `Checks/Sys/Kernel/Groups.lean` does for the same reason.
The `rfl` patterns keep the spec's term on the LEFT (`outcome.Ok.inj
h.symm`, `hzs.symm`): `rcases` `whnf`s the right-hand side first to see
whether it is a variable, and `mremap_inplace_effect`/`mremap_tail` begin
with such an `if`.  The kernel has the same trap: `unfold` of that `if`
while it is the discriminant of the checker's `match` lets `simp`'s
matcher reduction take a definitional step through the `Decidable`
instance, and the kernel replays it thousands of frames deep.  So the
complete direction first proves the effect equal to its constructor form
(`heff`), rewrites with it, and only then unfolds the checker. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mremap

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-- Accept an observed `mremap` effect exactly when `mremap_spec` admits it.
The gates retain the Linux reading (v6.18.46, commit 1f99e9ab748f):
flags, alignment, zero rounded new length and TASK_SIZE are checked by
`check_mremap_params` (mm/mremap.c:1759-1776), after `do_mremap` rounds
both lengths (:1917-1918). Alignment and zero new length now decline
because QEMU 11.1.1 linux-user/mmap.c `target_mremap`:1194-1209 allocates
before host validation. Zero old length declines at the duplicate-shm
boundary (`check_prep_vma`, mm/mremap.c:1690-1694, Linux v6.18.46); source coverage uses
its VMA checks (:1658-1659, :1720-1721), narrowed to a tracked uniformly
backed mapping. Non-growth declines because `mremap_at` (:1557-1572)
keeps Linux equal/shrinking calls in place while QEMU may move or fail.
Past those gates, `expand_vma` (mm/mremap.c:1512-1544, Linux v6.18.46) either extends in
place (`expand_vma_in_place`) or obtains a fresh destination
(`vrm_set_new_addr`) and invokes `move_vma`; the exact ledgers follow
those effects. `mremap_spec` carries the QEMU host assumptions and the
TASK_SIZE cross-version argument.
On grows, the `bv_eqb r old` test comes after the errno test. The helper
lemmas below prove those tests disjoint for every accepted return.
Rocq: `Mremap.check_mremap`. -/
def check_mremap (old old_size new_size flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if !(bv_unsigned flags == MREMAP_MAYMOVE) then CheckUnmodeled
  else if !(bv_unsigned old % page_size == 0) then CheckUnmodeled
  else if page_align_is0_b new_size then CheckUnmodeled
  else if TASK_SIZE < page_round_up_Z (bv_unsigned new_size) then CheckUnmodeled
  else if page_align_is0_b old_size then CheckUnmodeled
  else
    let old_nZ := page_round_up_Z (bv_unsigned old_size)
    let new_nZ := page_round_up_Z (bv_unsigned new_size)
    let old_n := Z_to_bv 64 old_nZ
    let new_n := Z_to_bv 64 new_nZ
    if !(mremap_source_b (m_vmmaps m) old old_n old_nZ && mremap_backing_uniform_b m old old_n)
    then CheckUnmodeled
    else if new_nZ ≤ old_nZ then CheckUnmodeled
    else
      match eff with
      | SyscallEffect.mkEffectU r [] zs us cs [] =>
          if errno_ret_in mremap_errnos r then
            match zs, us, cs with
            | [], [], [] => CheckOk m []
            | _, _, _ => CheckReject
          else if bv_eqb r old then
            if mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ then
              if listNN_eqb zs (mremap_tail old old_n old_nZ new_nZ) && listNN_eqb us []
                 && listCopy_eqb cs []
              then CheckOk (mremap_model_next m old old_n old new_n) []
              else CheckReject
            else CheckReject
          else if (old_nZ < new_nZ) && mremap_fresh_b m old_nZ new_nZ old old_n r new_n
                  && listNN_eqb zs (mremap_tail r old_n old_nZ new_nZ)
                  && listNN_eqb us [(old, old_n)] && listCopy_eqb cs [MemCopy.mkCopy old r old_n]
          then CheckOk (mremap_model_next m old old_n r new_n) []
          else CheckReject
      | _ => CheckReject

/-! ## The helper lemmas

Rocq's three, under their names, and two Lean-side conveniences.  The
first two are what keeps the checker's errno test from firing on a
successful return: a source that passes `mremap_source_b` ends at or below
`alloc_top`, and so does a destination that passes `mremap_fresh_b`, and
`alloc_top` sits a whole stack below `2^64` (`State.alloc_top_room`), so
neither address is in the errno window `[2^64-4095, 2^64-1]` that
`errno_ret_in_below` needs it out of.  The third is the `!(bv_eqb dst old)`
conjunct of `mremap_fresh_b` read back as an equation.  The two
conveniences are the reflexive instances of the prelude's list-equality
lemmas and the non-negativity of a rounded word, which Rocq's proofs
inline (`page_round_up_Z_nonneg`, Rocq's `Checks/BudgetPremise.v` and
`Checks/Sys/Mm/Mmap.v`, has no Lean twin). -/

/-- A modeled source's address is never an encoded errno.
Rocq: `Mremap.mremap_source_ret_not_errno`. -/
theorem mremap_source_ret_not_errno (h : VmMaps) (old old_n : word) (old_nZ : Int)
    (hn : 0 ≤ old_nZ) (hsrc : mremap_source_b h old old_n old_nZ = true) :
    errno_ret_in mremap_errnos old = false := by
  unfold mremap_source_b at hsrc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsrc
  obtain ⟨⟨⟨hbound, -⟩, -⟩, -⟩ := hsrc
  apply errno_ret_in_below mremap_errnos old rfl
  have hroom := alloc_top_room h
  unfold stack_max_size at hroom
  omega

/-- A fresh destination's address is never an encoded errno.
Rocq: `Mremap.mremap_fresh_ret_not_errno`. -/
theorem mremap_fresh_ret_not_errno (m : Model) (old_nZ new_nZ : Int) (old old_n dst new_n : word)
    (hn : 0 ≤ new_nZ) (hfresh : mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true) :
    errno_ret_in mremap_errnos dst = false := by
  unfold mremap_fresh_b at hfresh
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfresh
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hbound⟩, -⟩, -⟩ := hfresh
  apply errno_ret_in_below mremap_errnos dst rfl
  have hroom := alloc_top_room (m_vmmaps m)
  unfold stack_max_size at hroom
  omega

/-- A fresh destination is not the source.  Rocq: `Mremap.mremap_fresh_neq_old`. -/
theorem mremap_fresh_neq_old (m : Model) (old_nZ new_nZ : Int) (old old_n dst new_n : word)
    (hfresh : mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true) :
    bv_eqb dst old = false := by
  unfold mremap_fresh_b at hfresh
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfresh
  exact hfresh.1.1.1.1.1

/-- `page_round_up_Z` of a word's value is non-negative. -/
theorem page_round_up_Z_word_nonneg (w : word) : 0 ≤ page_round_up_Z (bv_unsigned w) := by
  have hw := word_unsigned_range w
  unfold page_round_up_Z page_size
  omega

/-- The reflexive instance of `listNN_eqb_eq`. -/
theorem listNN_eqb_refl (l : List (word × word)) : listNN_eqb l l = true :=
  (listNN_eqb_eq l l).mpr rfl

/-- The reflexive instance of `listCopy_eqb_eq`. -/
theorem listCopy_eqb_refl (l : List MemCopy) : listCopy_eqb l l = true :=
  (listCopy_eqb_eq l l).mpr rfl

/-! ## The four lemmas -/

/-- Accepting is sound: an accepted effect is one the spec admits, with the
spec's own post-model and events.  Rocq: `Mremap.check_mremap_sound_ok`. -/
theorem check_mremap_sound_ok (old old_size new_size flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : check_mremap old old_size new_size flags eff m = CheckOk m' evs) :
    mremap_spec old old_size new_size flags i m (Ok eff m' evs) := by
  unfold check_mremap at h
  unfold mremap_spec
  cases hshape : (!(bv_unsigned flags == MREMAP_MAYMOVE)) with
  | true => simp only [hshape, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [hshape, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases halign : (!(bv_unsigned old % page_size == 0)) with
  | true =>
    simp only [halign, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [halign, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hnew : page_align_is0_b new_size with
  | true =>
    simp only [hnew, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [hnew, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have htask := Decidable.em (TASK_SIZE < page_round_up_Z (bv_unsigned new_size))
  cases htask with
  | inl htask => simp only [htask, ↓reduceIte, reduceCtorEq] at h
  | inr htask =>
  simp only [htask, ↓reduceIte] at h ⊢
  cases hold : page_align_is0_b old_size with
  | true => simp only [hold, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [hold, Bool.false_eq_true, ↓reduceIte] at h ⊢
  simp only [bind_get_model_iff]
  cases hsrc : (!(mremap_source_b (m_vmmaps m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
                    (page_round_up_Z (bv_unsigned old_size))
                  && mremap_backing_uniform_b m old
                    (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))) with
  | true => simp only [hsrc, ↓reduceIte, reduceCtorEq] at h
  | false =>
  simp only [hsrc, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have heq := Decidable.em (page_round_up_Z (bv_unsigned new_size) ≤ page_round_up_Z (bv_unsigned old_size))
  cases heq with
  | inl heq =>
    simp only [heq, ↓reduceIte, reduceCtorEq] at h
  | inr heq =>
  simp only [heq, ↓reduceIte] at h ⊢
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
    obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp herr
    apply alt_l
    exact bind_ok0 _ _ _ _ _ _ _ _ _ (choose_ok _ e i _ hin) (pure_ok _ i _)
  | false =>
  simp only [herr, Bool.false_eq_true, ↓reduceIte] at h
  cases hret : bv_eqb r old with
  | true =>
    simp only [hret, ↓reduceIte] at h
    rw [(bv_eqb_eq r old).mp hret]
    apply alt_r
    have hlt : ¬ page_round_up_Z (bv_unsigned new_size) < page_round_up_Z (bv_unsigned old_size) := by omega
    cases hgrow : mremap_inplace_grow_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
        (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) with
    | true =>
      simp only [hgrow, ↓reduceIte] at h ⊢
      split at h
      · rename_i hfields
        simp only [check_result.CheckOk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Bool.and_eq_true, listNN_eqb_eq, listCopy_eqb_eq] at hfields
        obtain ⟨⟨hzs, rfl⟩, rfl⟩ := hfields
        obtain rfl := hzs.symm
        apply alt_l
        refine bind_ok0 _ _ _ _ _ _ _ _ _ (modify_ok _ i _) ?_
        unfold mremap_inplace_effect
        simp only [hlt, ↓reduceIte]
        exact pure_ok _ i _
      · simp only [reduceCtorEq] at h
    | false => simp only [hgrow, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | false =>
  -- the move
  simp only [hret, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · rename_i hmove
    simp only [check_result.CheckOk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq, listNN_eqb_eq, listCopy_eqb_eq] at hmove
    obtain ⟨⟨⟨⟨hlt, hfresh⟩, hzs⟩, rfl⟩, rfl⟩ := hmove
    obtain rfl := hzs.symm
    apply alt_r
    cases mremap_inplace_grow_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
        (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) with
    | true =>
      simp only [↓reduceIte]
      apply alt_r
      exact bind_ok0 _ _ _ _ _ _ _ _ _ (choose_ok _ r i _ hfresh)
        (bind_ok0 _ _ _ _ _ _ _ _ _ (modify_ok _ i _) (pure_ok _ i _))
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact bind_ok0 _ _ _ _ _ _ _ _ _ (choose_ok _ r i _ hfresh)
        (bind_ok0 _ _ _ _ _ _ _ _ _ (modify_ok _ i _) (pure_ok _ i _))
  · simp only [reduceCtorEq] at h

/-- Declining is sound: wherever the checker says `CheckUnmodeled`, the spec
has an `Unmodeled` run. Past the non-growth gate the checker never
 declines, so the remaining arms
are ruled out by the shape of `h`.  Rocq: `Mremap.check_mremap_sound_unmodeled`. -/
theorem check_mremap_sound_unmodeled (old old_size new_size flags : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (h : check_mremap old old_size new_size flags eff m = CheckUnmodeled) :
    mremap_spec old old_size new_size flags i m Unmodeled := by
  unfold check_mremap at h
  unfold mremap_spec
  cases hshape : (!(bv_unsigned flags == MREMAP_MAYMOVE)) with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [hshape, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases halign : (!(bv_unsigned old % page_size == 0)) with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [halign, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hnew : page_align_is0_b new_size with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [hnew, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have htask := Decidable.em (TASK_SIZE < page_round_up_Z (bv_unsigned new_size))
  cases htask with
  | inl htask =>
    simp only [htask, ↓reduceIte]
    exact unmodeled_intro i m
  | inr htask =>
  simp only [htask, ↓reduceIte] at h ⊢
  cases hold : page_align_is0_b old_size with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [hold, Bool.false_eq_true, ↓reduceIte] at h ⊢
  simp only [bind_get_model_iff]
  cases hsrc : (!(mremap_source_b (m_vmmaps m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
                    (page_round_up_Z (bv_unsigned old_size))
                  && mremap_backing_uniform_b m old
                    (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))) with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [hsrc, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have heq := Decidable.em (page_round_up_Z (bv_unsigned new_size) ≤ page_round_up_Z (bv_unsigned old_size))
  cases heq with
  | inl heq =>
    simp only [heq, ↓reduceIte]
    exact unmodeled_intro i m
  | inr heq =>
  simp only [heq, ↓reduceIte] at h
  exfalso
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
    cases zs <;> cases us <;> cases cs <;> simp only [reduceCtorEq] at h
  | false =>
  simp only [herr, Bool.false_eq_true, ↓reduceIte] at h
  cases hret : bv_eqb r old with
  | true =>
    simp only [hret, ↓reduceIte] at h
    split at h <;> (try split at h) <;> (try split at h) <;> simp only [reduceCtorEq] at h
  | false =>
    simp only [hret, Bool.false_eq_true, ↓reduceIte] at h
    split at h <;> simp only [reduceCtorEq] at h

set_option linter.constructorNameAsVariable false in
/-- Accepting is complete: every effect the spec admits is accepted, with
the spec's post-model and events.  Rocq: `Mremap.check_mremap_complete_ok`.
The linter is off for the reason the header gives: `h` is the spec
applied, and the linter's `whnf` of it runs past `maxRecDepth`. -/
theorem check_mremap_complete_ok (old old_size new_size flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : mremap_spec old old_size new_size flags i m (Ok eff m' evs)) :
    check_mremap old old_size new_size flags eff m = CheckOk m' evs := by
  unfold mremap_spec at h
  cases hshape : (!(bv_unsigned flags == MREMAP_MAYMOVE)) with
  | true => simp only [hshape, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
  | false =>
  simp only [hshape, Bool.false_eq_true, ↓reduceIte] at h
  cases halign : (!(bv_unsigned old % page_size == 0)) with
  | true =>
    simp only [halign, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
  | false =>
  simp only [halign, Bool.false_eq_true, ↓reduceIte] at h
  cases hnew : page_align_is0_b new_size with
  | true =>
    simp only [hnew, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
  | false =>
  simp only [hnew, Bool.false_eq_true, ↓reduceIte] at h
  by_cases htask : TASK_SIZE < page_round_up_Z (bv_unsigned new_size)
  · simp only [htask, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
  simp only [htask, ↓reduceIte] at h
  cases hold : page_align_is0_b old_size with
  | true => simp only [hold, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
  | false =>
  simp only [hold, Bool.false_eq_true, ↓reduceIte, bind_get_model_iff] at h
  cases hsrc : (!(mremap_source_b (m_vmmaps m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
                    (page_round_up_Z (bv_unsigned old_size))
                  && mremap_backing_uniform_b m old
                    (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))) with
  | true => simp only [hsrc, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
  | false =>
  simp only [hsrc, Bool.false_eq_true, ↓reduceIte] at h
  have hsource : mremap_source_b (m_vmmaps m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
      (page_round_up_Z (bv_unsigned old_size)) = true := by
    have hsrc' := hsrc
    simp only [Bool.not_eq_false', Bool.and_eq_true] at hsrc'
    exact hsrc'.1
  have hold_errno : errno_ret_in mremap_errnos old = false :=
    mremap_source_ret_not_errno (m_vmmaps m) old _ _ (page_round_up_Z_word_nonneg old_size) hsource
  have hnew_nonneg := page_round_up_Z_word_nonneg new_size
  have heq := Decidable.em (page_round_up_Z (bv_unsigned new_size) ≤ page_round_up_Z (bv_unsigned old_size))
  cases heq with
  | inl heq =>
    simp only [heq, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
  | inr heq =>
  simp only [heq, ↓reduceIte, alt_iff] at h
  rcases h with herr | hsucc
  · -- the errno branch
    simp only [errno_from, bind_choose_iff, err_ret, ret_only, pure_iff] at herr
    obtain ⟨e, hin, hp⟩ := herr
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj hp.symm
    unfold check_mremap
    simp only [hshape, halign, hnew, htask, hold, hsrc, heq, Bool.false_eq_true, ↓reduceIte,
      errno_ret_in_intro mremap_errnos e hin]
  · have hlt : ¬ page_round_up_Z (bv_unsigned new_size) < page_round_up_Z (bv_unsigned old_size) := by omega
    have hmove : page_round_up_Z (bv_unsigned old_size) < page_round_up_Z (bv_unsigned new_size) := by
      omega
    have move_case : ∀ dst : word,
        mremap_fresh_b m (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size))
          old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = true →
        check_mremap old old_size new_size flags
          (mremap_move_effect old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst
            (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size))) m
        = CheckOk (mremap_model_next m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))) [] := by
      intro dst hfresh
      unfold check_mremap mremap_move_effect
      simp only [hshape, halign, hnew, htask, hold, hsrc, heq, Bool.false_eq_true, ↓reduceIte,
        mremap_fresh_ret_not_errno m _ _ old _ dst _ hnew_nonneg hfresh,
        mremap_fresh_neq_old m _ _ old _ dst _ hfresh, decide_eq_true hmove, hfresh,
        listNN_eqb_refl, listCopy_eqb_refl, Bool.true_and]
    cases hgrow : mremap_inplace_grow_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
        (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) with
    | true =>
      simp only [hgrow, ↓reduceIte, alt_iff] at hsucc
      rcases hsucc with hinpl | hmv
      · -- grow in place
        simp only [bind_modify_iff, pure_iff] at hinpl
        obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj hinpl.symm
        have heff : mremap_inplace_effect old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
            (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size))
            = SyscallEffect.mkEffectU old []
                (mremap_tail old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
                  (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)))
                [] [] [] := by
          unfold mremap_inplace_effect
          simp only [hlt, ↓reduceIte]
        rw [heff]
        unfold check_mremap
        simp only [hshape, halign, hnew, htask, hold, hsrc, heq, hgrow, Bool.false_eq_true,
          ↓reduceIte, hold_errno, bv_eqb_refl, listNN_eqb_refl, listCopy_eqb_refl, Bool.true_and]
      · -- move, beside an admitted in-place grow
        simp only [bind_choose_iff, bind_modify_iff, pure_iff] at hmv
        obtain ⟨dst, hfresh, hp⟩ := hmv
        obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj hp.symm
        exact move_case dst hfresh
    | false =>
      simp only [hgrow, Bool.false_eq_true, ↓reduceIte, bind_choose_iff, bind_modify_iff, pure_iff]
        at hsucc
      obtain ⟨dst, hfresh, hp⟩ := hsucc
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj hp.symm
      exact move_case dst hfresh

set_option linter.constructorNameAsVariable false in
/-- Declining is complete: every `Unmodeled` run of the spec is one the
checker declines. Past the non-growth gate every run is an `Ok`, so
 the hypothesis is a constructor
mismatch on each remaining arm.  Rocq: `Mremap.check_mremap_complete_unmodeled`.
The linter is off for the reason the header gives. -/
theorem check_mremap_complete_unmodeled (old old_size new_size flags : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (h : mremap_spec old old_size new_size flags i m Unmodeled) :
    check_mremap old old_size new_size flags eff m = CheckUnmodeled := by
  unfold mremap_spec at h
  unfold check_mremap
  cases hshape : (!(bv_unsigned flags == MREMAP_MAYMOVE)) with
  | true => simp only [↓reduceIte]
  | false =>
  simp only [hshape, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases halign : (!(bv_unsigned old % page_size == 0)) with
  | true => simp only [↓reduceIte]
  | false =>
  simp only [halign, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hnew : page_align_is0_b new_size with
  | true => simp only [↓reduceIte]
  | false =>
  simp only [hnew, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases htask : TASK_SIZE < page_round_up_Z (bv_unsigned new_size)
  · simp only [htask, ↓reduceIte]
  simp only [htask, ↓reduceIte] at h ⊢
  cases hold : page_align_is0_b old_size with
  | true => simp only [↓reduceIte]
  | false =>
  simp only [hold, Bool.false_eq_true, ↓reduceIte] at h ⊢
  simp only [bind_get_model_iff] at h
  cases hsrc : (!(mremap_source_b (m_vmmaps m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
                  (page_round_up_Z (bv_unsigned old_size))
                && mremap_backing_uniform_b m old
                  (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))) with
  | true => simp only [↓reduceIte]
  | false =>
  simp only [hsrc, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have heq := Decidable.em (page_round_up_Z (bv_unsigned new_size) ≤ page_round_up_Z (bv_unsigned old_size))
  cases heq with
  | inl heq =>
    simp only [heq, ↓reduceIte]
  | inr heq =>
  simp only [heq, ↓reduceIte, alt_iff] at h
  exfalso
  rcases h with herr | hsucc
  · simp only [errno_from, bind_choose_iff, err_ret, ret_only, pure_iff, reduceCtorEq, and_false,
    exists_false] at herr
  · cases hgrow : mremap_inplace_grow_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
        (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) with
    | true =>
      simp only [hgrow, ↓reduceIte, alt_iff, bind_modify_iff, bind_choose_iff, pure_iff,
        reduceCtorEq, and_false, exists_false, or_self] at hsucc
    | false =>
      simp only [hgrow, Bool.false_eq_true, ↓reduceIte, bind_choose_iff, bind_modify_iff, pure_iff,
        reduceCtorEq, and_false, exists_false] at hsucc

/-! ## The witness — `Checks/Witness/Mm/Mremap.v`

One admissible outcome per arm of the spec, which is what progress is
proved from: `Unmodeled` on each of the spec's declines, and on every
grow the -ENOMEM the spec's `alt` always offers (`witness_errno`, the
head of `mremap_errnos`) — never the success, whose shape depends on a
placement the witness would have to search for. -/

/-- One outcome `mremap_spec` admits, for every input.
Rocq: `Mremap.mremap_witness`. -/
def mremap_witness (old old_size new_size flags : word) (m : Model) : outcome SyscallEffect :=
  if !(bv_unsigned flags == MREMAP_MAYMOVE) then Unmodeled
  else if !(bv_unsigned old % page_size == 0) then Unmodeled
  else if page_align_is0_b new_size then Unmodeled
  else if TASK_SIZE < page_round_up_Z (bv_unsigned new_size) then Unmodeled
  else if page_align_is0_b old_size then Unmodeled
  else
    let old_nZ := page_round_up_Z (bv_unsigned old_size)
    let new_nZ := page_round_up_Z (bv_unsigned new_size)
    let old_n := Z_to_bv 64 old_nZ
    if !(mremap_source_b (m_vmmaps m) old old_n old_nZ && mremap_backing_uniform_b m old old_n)
    then Unmodeled
    else if new_nZ ≤ old_nZ then Unmodeled
    else ret_outcome (errno_ret witness_errno) m

/-- The spec admits the witness's outcome.  Rocq: `Mremap.mremap_witness_ok`. -/
theorem mremap_witness_ok (old old_size new_size flags : word) (i : SyscallInput) (m : Model) :
    mremap_spec old old_size new_size flags i m (mremap_witness old old_size new_size flags m) := by
  unfold mremap_spec mremap_witness
  cases (!(bv_unsigned flags == MREMAP_MAYMOVE)) with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases (!(bv_unsigned old % page_size == 0)) with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases page_align_is0_b new_size with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  have htask := Decidable.em (TASK_SIZE < page_round_up_Z (bv_unsigned new_size))
  cases htask with
  | inl htask =>
    simp only [htask, ↓reduceIte]
    exact unmodeled_intro i m
  | inr htask =>
  simp only [htask, ↓reduceIte]
  cases page_align_is0_b old_size with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp only [bind_get_model_iff]
  cases (!(mremap_source_b (m_vmmaps m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
             (page_round_up_Z (bv_unsigned old_size))
           && mremap_backing_uniform_b m old
             (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))) with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hle := Decidable.em (page_round_up_Z (bv_unsigned new_size) ≤ page_round_up_Z (bv_unsigned old_size))
  cases hle with
  | inl hle =>
    simp only [hle, ↓reduceIte]
    exact unmodeled_intro i m
  | inr hle =>
  simp only [hle, ↓reduceIte]
  apply alt_l
  exact bind_step _ _ i m ENOMEM m _ (errno_head_witness ENOMEM [] i m) (pure_ok _ i _)

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mremap
