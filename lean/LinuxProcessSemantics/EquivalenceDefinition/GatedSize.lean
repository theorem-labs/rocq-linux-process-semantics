-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/GatedSize.v
import LinuxProcessSemantics.EquivalenceDefinition.Measure

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # EquivalenceDefinition.GatedSize — slicing the input space by gate verdicts

Mirrors `theories/EquivalenceDefinition/GatedSize.v`. Its header gives the
size-scoring argument: ordered gates partition finite inputs, and each
program owes equivalence only on its part. Complement-weight bounds let a
consumer charge unproven mass at the most expensive part.

TRUST BOUNDARY: this file is part of the trusted specification.

Rocq's `Q` becomes core Lean's reduced `Rat`; lemmas over `Qeq` are
stated over `=` as in `Measure`, keeping the Rocq names and shapes.
Rocq's `List.Forall` is consistently a bounded universal quantifier here.

Disjointness follows from the slice shape without assumptions on gates.
Exhaustiveness retains the per-gate excluded-middle hypothesis; this file
does not decide the infinitely branching acceptance judgment. Finite
inputs denote shared process inputs, with independent entries and source
and target allocation budgets fixed by role; the classifier has its own
budget. The finite-input surjection explains the finite restriction.

An entry-less gate accepts vacuously and swallows the residue, leaving all
later parts empty. An entry-less source OR target also makes a slice
obligation vacuous. Consumers owe `Equivalence.IMAGE_WF` for every image;
only its brk-satisfiability clause inhabits entries, while fetchability and
readable headers constrain runs. Empty slices are intentional: their
complement-weight bound charges the whole space.

The weight bound deduplicates cores, not records, as `Measure` does. Its
predicate remains record-indexed: it bounds cores having SOME representative
outside the predicate, the union over each fibre. Weights and total mass
are trusted task metadata; a submission choosing zero weights would erase
the obligation.

Configured programs follow the task's shared `cfg`, but gates are pinned
to forced-only so that their own reads cannot be refused without cause.
The weight bound needs no configured twin: runs occur only inside its
predicate. No monotonicity between configurations is claimed: filtering
both trace sets need not preserve their equality. The Rocq discussion is
an argument for withholding a lemma, not a proved counterexample. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.GatedSize

open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.EquivalenceDefinition.Classifier
open LinuxProcessSemantics.EquivalenceDefinition.Measure

/-! ## The slices and their partition laws -/

/-- Gate `G` accepts and every gate ordered before it refuses. Refusal
is negated acceptance without validity: consumers carry validity separately,
so the residue after no gates remains the whole input space. -/
def slice_accept (prev : List Image) (G : Image) (f : FinProcInput) : Prop :=
  accepts G f ∧ ∀ G' ∈ prev, ¬ accepts G' f

/-- The final, ungated part consists of inputs every preceding gate refuses. -/
def slice_rest (prev : List Image) (f : FinProcInput) : Prop :=
  ∀ G' ∈ prev, ¬ accepts G' f

/-- A later gate's prefix excludes acceptance by an earlier gate. -/
theorem slices_disjoint_accept_accept (prev : List Image) (G : Image)
    (prev' : List Image) (G' : Image) (f : FinProcInput) :
    G ∈ prev' → slice_accept prev G f → slice_accept prev' G' f → False :=
  fun hin ha hb => hb.2 G hin ha.1

/-- The residue excludes each gate it lists. -/
theorem slices_disjoint_accept_rest (prev : List Image) (G : Image)
    (prev' : List Image) (f : FinProcInput) :
    G ∈ prev' → slice_accept prev G f → slice_rest prev' f → False :=
  fun hin ha hr => hr G hin ha.1

/-- With no gates the one remaining program covers the whole input space. -/
theorem slice_rest_nil (f : FinProcInput) : slice_rest [] f :=
  fun _ hin => (List.not_mem_nil hin).elim

/-- Per-gate decidability locates the first accepting gate, or the residue.
The exhibited prefix is precisely the prefix its slice consumes. -/
theorem slices_exhaustive (gates : List Image) (f : FinProcInput) :
    (∀ G ∈ gates, accepts G f ∨ ¬ accepts G f) →
    (∃ prev G suffix, gates = prev ++ G :: suffix ∧ slice_accept prev G f) ∨
      slice_rest gates f := by
  induction gates with
  | nil => exact fun _ => Or.inr (slice_rest_nil f)
  | cons g gates ih =>
    intro hd
    rcases hd g List.mem_cons_self with ha | hn
    · exact Or.inl ⟨[], g, gates, rfl, ha, slice_rest_nil f⟩
    · rcases ih (fun G hG => hd G (List.mem_cons_of_mem g hG)) with hex | hr
      · obtain ⟨prev, G, suffix, heq, hacc, hprev⟩ := hex
        refine Or.inl ⟨g :: prev, G, suffix, ?_, hacc, ?_⟩
        · rw [List.cons_append, heq]
        · intro G' hin
          rcases List.mem_cons.mp hin with rfl | hin
          · exact hn
          · exact hprev G' hin
      · apply Or.inr
        intro G hin
        rcases List.mem_cons.mp hin with rfl | hin
        · exact hn
        · exact hr G hin

/-! ## Per-slice equivalence -/

/-- The target reproduces the source on every valid finite input in `P`.
Entries are independent and inside the input quantifier, with a shared
process input and allocation budgets fixed by role. The predicate is arbitrary, so the shell does not depend on a particular gate list. -/
def gated_slice_T (Src A : Image) (P : FinProcInput → Prop) : Prop :=
  ∀ f : FinProcInput, valid_fin_input f → P f →
    ∀ en_s en_a,
      valid_entry Src en_s (to_proc_input f) →
      valid_entry A en_a (to_proc_input f) →
      strong_equiv Src A en_s en_a (to_proc_input f)

/-- The error-free twin has no all-errors escape and no separate modeled conjunct.
Entries are independent and inside the input quantifier, with a shared
process input and allocation budgets fixed by role. The predicate is arbitrary, so the shell does not depend on a particular gate list. -/
def gated_slice_error_free_T (Src A : Image) (P : FinProcInput → Prop) : Prop :=
  ∀ f : FinProcInput, valid_fin_input f → P f →
    ∀ en_s en_a,
      valid_entry Src en_s (to_proc_input f) →
      valid_entry A en_a (to_proc_input f) →
      strong_equiv_error_free Src A en_s en_a (to_proc_input f)

/-- Universal equivalence implies equivalence on any slice at the same configuration. -/
theorem gated_slice_of_universal (Src A : Image) (P : FinProcInput → Prop) :
    strong_universal_T Src A → gated_slice_T Src A P :=
  fun h f hf _ es ea hs ha => h es ea (to_proc_input f) hs ha hf

/-- Shrinking the slice weakens its obligation. -/
theorem gated_slice_mono (Src A : Image) (P P' : FinProcInput → Prop) :
    (∀ f, P' f → P f) → gated_slice_T Src A P → gated_slice_T Src A P' :=
  fun hsub h f hf hp es ea hs ha => h f hf (hsub f hp) es ea hs ha

/-- One valid input inside the slice and two valid entries witness refutation. -/
theorem gated_slice_refuted (Src A : Image) (P : FinProcInput → Prop)
    (f : FinProcInput) (en_s en_a : ExecEntry) :
    valid_fin_input f → P f →
    valid_entry Src en_s (to_proc_input f) →
    valid_entry A en_a (to_proc_input f) →
    ¬ strong_equiv Src A en_s en_a (to_proc_input f) →
    ¬ gated_slice_T Src A P :=
  fun hf hp hs ha hne h => hne (h f hf hp en_s en_a hs ha)

/-- Universal equivalence implies equivalence on any slice at the same configuration. -/
theorem gated_slice_error_free_of_universal (Src A : Image) (P : FinProcInput → Prop) :
    strong_universal_error_free_T Src A → gated_slice_error_free_T Src A P :=
  fun h f hf _ es ea hs ha => h es ea (to_proc_input f) hs ha hf

/-- Shrinking the slice weakens its obligation. -/
theorem gated_slice_error_free_mono (Src A : Image) (P P' : FinProcInput → Prop) :
    (∀ f, P' f → P f) → gated_slice_error_free_T Src A P → gated_slice_error_free_T Src A P' :=
  fun hsub h f hf hp es ea hs ha => h f hf (hsub f hp) es ea hs ha

/-- One valid input inside the slice and two valid entries witness refutation. -/
theorem gated_slice_error_free_refuted (Src A : Image) (P : FinProcInput → Prop)
    (f : FinProcInput) (en_s en_a : ExecEntry) :
    valid_fin_input f → P f →
    valid_entry Src en_s (to_proc_input f) →
    valid_entry A en_a (to_proc_input f) →
    ¬ strong_equiv_error_free Src A en_s en_a (to_proc_input f) →
    ¬ gated_slice_error_free_T Src A P :=
  fun hf hp hs ha hne h => hne (h f hf hp en_s en_a hs ha)

/-! ## Predicate-indexed mass bounds -/

/-- Every list of valid finite inputs outside `P`, duplicate-free on
cores, weighs at most `b * M`. Validity belongs to each membership claim,
exactly as in classifier rejection. The quantifier is over every list,
never a submission-chosen sample; `w` and `M` are trusted task metadata.
Record-indexed `P` bounds the union of outside representatives over fibres. -/
def weight_bound_pred_T (P : FinProcInput → Prop) (w : FinProcInput → Rat)
    (M b : Rat) : Prop :=
  ∀ l : List FinProcInput, (l.map fin_core).Nodup →
    (∀ f ∈ l, valid_fin_input f ∧ ¬ P f) → sum_weights w l ≤ b * M

/-- Classifier rejection is exactly validity conjoined with nonacceptance. -/
theorem weight_bound_pred_of_classifier (C : Image) (w : FinProcInput → Rat) (M b : Rat) :
    weight_bound_T C w M b ↔ weight_bound_pred_T (accepts C) w M b := Iff.rfl

/-- Increasing the bound preserves it when the total mass is nonnegative. -/
theorem weight_bound_pred_mono (P : FinProcInput → Prop) (w : FinProcInput → Rat)
    (M b b' : Rat) :
    0 ≤ M → b ≤ b' → weight_bound_pred_T P w M b → weight_bound_pred_T P w M b' := by
  intro hM hbb hb l hnd hall
  exact Rat.le_trans (hb l hnd hall) (Rat.mul_le_mul_of_nonneg_right hbb hM)

/-- Rational equality transports the total and the bound together. -/
theorem weight_bound_pred_qeq (P : FinProcInput → Prop) (w : FinProcInput → Rat)
    (M M' b b' : Rat) :
    M = M' → b = b' → weight_bound_pred_T P w M b → weight_bound_pred_T P w M' b' := by
  intro hM hb
  subst M'
  subst b'
  exact id

/-- An entry-less gate swallows precisely the preceding residue.
The consuming checker owes image well-formedness to close this route. -/
theorem slice_accept_vacuous_no_entries (prev : List Image) (G : Image)
    (f : FinProcInput) :
    (∀ en, ¬ valid_entry G en (to_proc_input f)) →
    (slice_accept prev G f ↔ slice_rest prev f) :=
  fun hno => ⟨fun h => h.2, fun hr => ⟨accepts_vacuous_no_entries G f hno, hr⟩⟩

/-- Once an entry-less gate is in the prefix, the residue is empty. -/
theorem slice_rest_vacuous_no_entries (prev : List Image) (G : Image)
    (f : FinProcInput) :
    G ∈ prev → (∀ en, ¬ valid_entry G en (to_proc_input f)) →
    ¬ slice_rest prev f :=
  fun hin hno hr => hr G hin (accepts_vacuous_no_entries G f hno)

/-- Two valid outside inputs with distinct cores refute a unit bound
at unit weight and total mass. Distinct records alone do not suffice. -/
theorem weight_bound_pred_refutable (P : FinProcInput → Prop) (f1 f2 : FinProcInput) :
    valid_fin_input f1 → ¬ P f1 → valid_fin_input f2 → ¬ P f2 →
    fin_core f1 ≠ fin_core f2 → ¬ weight_bound_pred_T P (fun _ => 1) 1 1 := by
  intro hv1 hp1 hv2 hp2 hne hb
  have hnd : ([f1, f2].map fin_core).Nodup := by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
      List.not_mem_nil, List.nodup_nil, hne, not_false_eq_true, and_self]
  have hsum := hb [f1, f2] hnd (by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨hv1, hp1⟩
    · exact (List.mem_singleton.mp hf) ▸ ⟨hv2, hp2⟩)
  dsimp only [sum_weights, List.foldr] at hsum
  exact (by decide +kernel : ¬ ((1 : Rat) + (1 + 0) ≤ 1 * 1)) hsum

/-- Repeating one outside input meets membership and breaks the arithmetic;
core duplicate-freedom is exactly what excludes this list from the bound. -/
theorem weight_bound_pred_needs_nodup (P : FinProcInput → Prop) (f : FinProcInput) :
    valid_fin_input f → ¬ P f →
    ¬ ([f, f].map fin_core).Nodup ∧
    (∀ f' ∈ [f, f], valid_fin_input f' ∧ ¬ P f') ∧
    ¬ (sum_weights (fun _ => 1) [f, f] ≤ 1 * 1) := by
  intro hv hp
  refine ⟨?_, ?_, ?_⟩
  · intro hnd
    exact (List.nodup_cons.mp hnd).1 (List.mem_singleton.mpr rfl)
  · intro f' hin
    rcases List.mem_cons.mp hin with rfl | hin
    · exact ⟨hv, hp⟩
    · exact (List.mem_singleton.mp hin) ▸ ⟨hv, hp⟩
  · exact (by decide +kernel : ¬ ((1 : Rat) + (1 + 0) ≤ 1 * 1))

/-! ## Forced-only gates and configured program obligations -/

/-- Gate `G` accepts and every gate ordered before it refuses. Refusal
is negated acceptance without validity: consumers carry validity separately,
so the residue after no gates remains the whole input space. Gates run at forced-only, independently of the task configuration. -/
def slice_accept_fo (prev : List Image) (G : Image) (f : FinProcInput) : Prop :=
  accepts_fo G f ∧ ∀ G' ∈ prev, ¬ accepts_fo G' f

/-- The final, ungated part consists of inputs every preceding gate refuses. -/
def slice_rest_fo (prev : List Image) (f : FinProcInput) : Prop :=
  ∀ G' ∈ prev, ¬ accepts_fo G' f

/-- A later gate's prefix excludes acceptance by an earlier gate. -/
theorem slices_disjoint_accept_accept_fo (prev : List Image) (G : Image)
    (prev' : List Image) (G' : Image) (f : FinProcInput) :
    G ∈ prev' → slice_accept_fo prev G f → slice_accept_fo prev' G' f → False :=
  fun hin ha hb => hb.2 G hin ha.1

/-- The residue excludes each gate it lists. -/
theorem slices_disjoint_accept_rest_fo (prev : List Image) (G : Image)
    (prev' : List Image) (f : FinProcInput) :
    G ∈ prev' → slice_accept_fo prev G f → slice_rest_fo prev' f → False :=
  fun hin ha hr => hr G hin ha.1

/-- With no gates the one remaining program covers the whole input space. -/
theorem slice_rest_fo_nil (f : FinProcInput) : slice_rest_fo [] f :=
  fun _ hin => (List.not_mem_nil hin).elim

/-- Per-gate decidability locates the first accepting gate, or the residue.
The exhibited prefix is precisely the prefix its slice consumes. -/
theorem slices_exhaustive_fo (gates : List Image) (f : FinProcInput) :
    (∀ G ∈ gates, accepts_fo G f ∨ ¬ accepts_fo G f) →
    (∃ prev G suffix, gates = prev ++ G :: suffix ∧ slice_accept_fo prev G f) ∨
      slice_rest_fo gates f := by
  induction gates with
  | nil => exact fun _ => Or.inr (slice_rest_fo_nil f)
  | cons g gates ih =>
    intro hd
    rcases hd g List.mem_cons_self with ha | hn
    · exact Or.inl ⟨[], g, gates, rfl, ha, slice_rest_fo_nil f⟩
    · rcases ih (fun G hG => hd G (List.mem_cons_of_mem g hG)) with hex | hr
      · obtain ⟨prev, G, suffix, heq, hacc, hprev⟩ := hex
        refine Or.inl ⟨g :: prev, G, suffix, ?_, hacc, ?_⟩
        · rw [List.cons_append, heq]
        · intro G' hin
          rcases List.mem_cons.mp hin with rfl | hin
          · exact hn
          · exact hprev G' hin
      · apply Or.inr
        intro G hin
        rcases List.mem_cons.mp hin with rfl | hin
        · exact hn
        · exact hr G hin

/-- An entry-less gate swallows precisely the preceding residue.
The consuming checker owes image well-formedness to close this route. -/
theorem slice_accept_fo_vacuous_no_entries (prev : List Image) (G : Image)
    (f : FinProcInput) :
    (∀ en, ¬ valid_entry G en (to_proc_input f)) →
    (slice_accept_fo prev G f ↔ slice_rest_fo prev f) :=
  fun hno => ⟨fun h => h.2, fun hr => ⟨accepts_fo_vacuous_no_entries G f hno, hr⟩⟩

/-- Once an entry-less gate is in the prefix, the residue is empty. -/
theorem slice_rest_fo_vacuous_no_entries (prev : List Image) (G : Image)
    (f : FinProcInput) :
    G ∈ prev → (∀ en, ¬ valid_entry G en (to_proc_input f)) →
    ¬ slice_rest_fo prev f :=
  fun hin hno hr => hr G hin (accepts_fo_vacuous_no_entries G f hno)

/-- The predicate bound at forced-only acceptance is exactly the forced-only
classifier weight bound; the measure layer itself has no run to configure. -/
theorem weight_bound_pred_of_classifier_fo (C : Image) (w : FinProcInput → Rat) (M b : Rat) :
    weight_bound_T_fo C w M b ↔ weight_bound_pred_T (accepts_fo C) w M b := Iff.rfl

/-- The target reproduces the source on every valid finite input in `P`.
Entries are independent and inside the input quantifier, with a shared
process input and allocation budgets fixed by role. Both program runs use the task configuration; the gate predicate chooses its own runs. -/
def gated_slice_T_scfg (cfg : SpuriousCfg) (Src A : Image) (P : FinProcInput → Prop) : Prop :=
  ∀ f : FinProcInput, valid_fin_input f → P f →
    ∀ en_s en_a,
      valid_entry Src en_s (to_proc_input f) →
      valid_entry A en_a (to_proc_input f) →
      strong_equiv_scfg cfg Src A en_s en_a (to_proc_input f)

/-- The error-free twin has no all-errors escape and no separate modeled conjunct.
Entries are independent and inside the input quantifier, with a shared
process input and allocation budgets fixed by role. Both program runs use the task configuration; the gate predicate chooses its own runs. -/
def gated_slice_error_free_T_scfg (cfg : SpuriousCfg) (Src A : Image) (P : FinProcInput → Prop) : Prop :=
  ∀ f : FinProcInput, valid_fin_input f → P f →
    ∀ en_s en_a,
      valid_entry Src en_s (to_proc_input f) →
      valid_entry A en_a (to_proc_input f) →
      strong_equiv_error_free_scfg cfg Src A en_s en_a (to_proc_input f)

/-- At may-fail the configured contract is propositionally the baseline contract. -/
theorem gated_slice_T_scfg_may_fail (Src A : Image) (P : FinProcInput → Prop) :
    gated_slice_T_scfg may_fail_cfg Src A P ↔ gated_slice_T Src A P :=
  ⟨fun h f hf hp es ea hs ha =>
    (strong_equiv_scfg_may_fail Src A es ea (to_proc_input f)).mp
      (h f hf hp es ea hs ha),
   fun h f hf hp es ea hs ha =>
    (strong_equiv_scfg_may_fail Src A es ea (to_proc_input f)).mpr
      (h f hf hp es ea hs ha)⟩

/-- Universal equivalence implies equivalence on any slice at the same configuration. -/
theorem gated_slice_T_scfg_of_universal (cfg : SpuriousCfg) (Src A : Image) (P : FinProcInput → Prop) :
    strong_universal_T_scfg cfg Src A → gated_slice_T_scfg cfg Src A P :=
  fun h f hf _ es ea hs ha => h es ea (to_proc_input f) hs ha hf

/-- Shrinking the slice weakens its obligation. -/
theorem gated_slice_T_scfg_mono (cfg : SpuriousCfg) (Src A : Image) (P P' : FinProcInput → Prop) :
    (∀ f, P' f → P f) → gated_slice_T_scfg cfg Src A P → gated_slice_T_scfg cfg Src A P' :=
  fun hsub h f hf hp es ea hs ha => h f hf (hsub f hp) es ea hs ha

/-- One valid input inside the slice and two valid entries witness refutation. -/
theorem gated_slice_T_scfg_refuted (cfg : SpuriousCfg) (Src A : Image) (P : FinProcInput → Prop)
    (f : FinProcInput) (en_s en_a : ExecEntry) :
    valid_fin_input f → P f →
    valid_entry Src en_s (to_proc_input f) →
    valid_entry A en_a (to_proc_input f) →
    ¬ strong_equiv_scfg cfg Src A en_s en_a (to_proc_input f) →
    ¬ gated_slice_T_scfg cfg Src A P :=
  fun hf hp hs ha hne h => hne (h f hf hp en_s en_a hs ha)

/-- At may-fail the configured contract is propositionally the baseline contract. -/
theorem gated_slice_error_free_T_scfg_may_fail (Src A : Image) (P : FinProcInput → Prop) :
    gated_slice_error_free_T_scfg may_fail_cfg Src A P ↔ gated_slice_error_free_T Src A P :=
  ⟨fun h f hf hp es ea hs ha =>
    (strong_equiv_error_free_scfg_may_fail Src A es ea (to_proc_input f)).mp
      (h f hf hp es ea hs ha),
   fun h f hf hp es ea hs ha =>
    (strong_equiv_error_free_scfg_may_fail Src A es ea (to_proc_input f)).mpr
      (h f hf hp es ea hs ha)⟩

/-- Universal equivalence implies equivalence on any slice at the same configuration. -/
theorem gated_slice_error_free_T_scfg_of_universal (cfg : SpuriousCfg) (Src A : Image) (P : FinProcInput → Prop) :
    strong_universal_error_free_T_scfg cfg Src A → gated_slice_error_free_T_scfg cfg Src A P :=
  fun h f hf _ es ea hs ha => h es ea (to_proc_input f) hs ha hf

/-- Shrinking the slice weakens its obligation. -/
theorem gated_slice_error_free_T_scfg_mono (cfg : SpuriousCfg) (Src A : Image) (P P' : FinProcInput → Prop) :
    (∀ f, P' f → P f) → gated_slice_error_free_T_scfg cfg Src A P → gated_slice_error_free_T_scfg cfg Src A P' :=
  fun hsub h f hf hp es ea hs ha => h f hf (hsub f hp) es ea hs ha

/-- One valid input inside the slice and two valid entries witness refutation. -/
theorem gated_slice_error_free_T_scfg_refuted (cfg : SpuriousCfg) (Src A : Image) (P : FinProcInput → Prop)
    (f : FinProcInput) (en_s en_a : ExecEntry) :
    valid_fin_input f → P f →
    valid_entry Src en_s (to_proc_input f) →
    valid_entry A en_a (to_proc_input f) →
    ¬ strong_equiv_error_free_scfg cfg Src A en_s en_a (to_proc_input f) →
    ¬ gated_slice_error_free_T_scfg cfg Src A P :=
  fun hf hp hs ha hne h => hne (h f hf hp en_s en_a hs ha)

/-- An entry-less source empties the source-entry quantifier. -/
theorem gated_slice_T_scfg_vacuous_no_source_entries (cfg : SpuriousCfg) (Src A : Image) (P : FinProcInput → Prop) :
    (∀ f en, ¬ valid_entry Src en (to_proc_input f)) → gated_slice_T_scfg cfg Src A P :=
  fun h f _ _ es _ hs _ => (h f es hs).elim

/-- A slice containing no valid input carries no equivalence obligation;
the complement bound still charges its mass. -/
theorem gated_slice_T_scfg_vacuous_empty_slice (cfg : SpuriousCfg) (Src A : Image) (P : FinProcInput → Prop) :
    (∀ f, valid_fin_input f → ¬ P f) → gated_slice_T_scfg cfg Src A P :=
  fun h f hf hp => (h f hf hp).elim

/-- An entry-less target empties the target-entry quantifier just as a source does. -/
theorem gated_slice_T_scfg_vacuous_no_target_entries (cfg : SpuriousCfg) (Src A : Image) (P : FinProcInput → Prop) :
    (∀ f en, ¬ valid_entry A en (to_proc_input f)) → gated_slice_T_scfg cfg Src A P :=
  fun h f _ _ _ ea _ ha => (h f ea ha).elim

/-- An entry-less source empties the source-entry quantifier. -/
theorem gated_slice_error_free_T_scfg_vacuous_no_source_entries (cfg : SpuriousCfg) (Src A : Image) (P : FinProcInput → Prop) :
    (∀ f en, ¬ valid_entry Src en (to_proc_input f)) → gated_slice_error_free_T_scfg cfg Src A P :=
  fun h f _ _ es _ hs _ => (h f es hs).elim

/-- A slice containing no valid input carries no equivalence obligation;
the complement bound still charges its mass. -/
theorem gated_slice_error_free_T_scfg_vacuous_empty_slice (cfg : SpuriousCfg) (Src A : Image) (P : FinProcInput → Prop) :
    (∀ f, valid_fin_input f → ¬ P f) → gated_slice_error_free_T_scfg cfg Src A P :=
  fun h f hf hp => (h f hf hp).elim

/-- An entry-less target empties the target-entry quantifier just as a source does. -/
theorem gated_slice_error_free_T_scfg_vacuous_no_target_entries (cfg : SpuriousCfg) (Src A : Image) (P : FinProcInput → Prop) :
    (∀ f en, ¬ valid_entry A en (to_proc_input f)) → gated_slice_error_free_T_scfg cfg Src A P :=
  fun h f _ _ _ ea _ ha => (h f ea ha).elim

/-- An entry-less source empties the source-entry quantifier. -/
theorem gated_slice_T_vacuous_no_source_entries (Src A : Image) (P : FinProcInput → Prop) :
    (∀ f en, ¬ valid_entry Src en (to_proc_input f)) → gated_slice_T Src A P :=
  fun h => (gated_slice_T_scfg_may_fail Src A P).mp
    (gated_slice_T_scfg_vacuous_no_source_entries may_fail_cfg Src A P h)

/-- A slice containing no valid input carries no equivalence obligation;
the complement bound still charges its mass. -/
theorem gated_slice_T_vacuous_empty_slice (Src A : Image) (P : FinProcInput → Prop) :
    (∀ f, valid_fin_input f → ¬ P f) → gated_slice_T Src A P :=
  fun h => (gated_slice_T_scfg_may_fail Src A P).mp
    (gated_slice_T_scfg_vacuous_empty_slice may_fail_cfg Src A P h)

/-- An entry-less target empties the target-entry quantifier just as a source does. -/
theorem gated_slice_T_vacuous_no_target_entries (Src A : Image) (P : FinProcInput → Prop) :
    (∀ f en, ¬ valid_entry A en (to_proc_input f)) → gated_slice_T Src A P :=
  fun h => (gated_slice_T_scfg_may_fail Src A P).mp
    (gated_slice_T_scfg_vacuous_no_target_entries may_fail_cfg Src A P h)

/-- An entry-less source empties the source-entry quantifier. -/
theorem gated_slice_error_free_T_vacuous_no_source_entries (Src A : Image) (P : FinProcInput → Prop) :
    (∀ f en, ¬ valid_entry Src en (to_proc_input f)) → gated_slice_error_free_T Src A P :=
  fun h => (gated_slice_error_free_T_scfg_may_fail Src A P).mp
    (gated_slice_error_free_T_scfg_vacuous_no_source_entries may_fail_cfg Src A P h)

/-- A slice containing no valid input carries no equivalence obligation;
the complement bound still charges its mass. -/
theorem gated_slice_error_free_T_vacuous_empty_slice (Src A : Image) (P : FinProcInput → Prop) :
    (∀ f, valid_fin_input f → ¬ P f) → gated_slice_error_free_T Src A P :=
  fun h => (gated_slice_error_free_T_scfg_may_fail Src A P).mp
    (gated_slice_error_free_T_scfg_vacuous_empty_slice may_fail_cfg Src A P h)

/-- An entry-less target empties the target-entry quantifier just as a source does. -/
theorem gated_slice_error_free_T_vacuous_no_target_entries (Src A : Image) (P : FinProcInput → Prop) :
    (∀ f en, ¬ valid_entry A en (to_proc_input f)) → gated_slice_error_free_T Src A P :=
  fun h => (gated_slice_error_free_T_scfg_may_fail Src A P).mp
    (gated_slice_error_free_T_scfg_vacuous_no_target_entries may_fail_cfg Src A P h)

end LinuxProcessSemantics.EquivalenceDefinition.GatedSize
