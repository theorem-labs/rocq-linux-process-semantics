import LinuxProcessSemantics.EquivalenceDefinition.Classifier

/-! rocq-baseline: 43f322ba3c8ed9cee0e632da3b7ed0b91210f84c -/

/-! # EquivalenceDefinition.Measure — weighted measure of the fire set

Mirrors `theories/EquivalenceDefinition/Measure.v`. The arguments for
reading duplicate-freedom on cores rather than records, for the finite
partial sum, and for what the quotient costs stay in that file's header,
so there is one place to correct them.

TRUST BOUNDARY: this file is part of the trusted specification.

Rocq's `Q` becomes core Lean's `Rat`, whose structure carries `reduced : num.natAbs.Coprime den`, so two values that
are Rocq-`Qeq` are equal here.  Each lemma Rocq states over `Qeq` is
stated over `=`; `weight_bound_qeq`, `weight_bound_fo_qeq` and
`sum_weights_ext` keep their Rocq names and shapes.

Rocq's `DISTRIBUTION` module type becomes the structure `Distribution`:
a consumer takes a `D : Distribution` where Rocq takes a module
`W : DISTRIBUTION`, and reads `D.w` and `D.M` where Rocq reads `W.w`
and `W.M`. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.Measure

open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.EquivalenceDefinition.Classifier

/-! ## Summing weights over a list of inputs -/

/-- The sum of `w` over `l`, zero on the empty list. -/
def sum_weights (w : FinProcInput → Rat) (l : List FinProcInput) : Rat :=
  List.foldr (fun f acc => w f + acc) 0 l

theorem sum_weights_nil (w : FinProcInput → Rat) : sum_weights w [] = 0 := by
  rfl

theorem sum_weights_cons (w : FinProcInput → Rat) (f : FinProcInput) (l : List FinProcInput) :
    sum_weights w (f :: l) = w f + sum_weights w l := by
  rfl

/-- `sum_weights` respects pointwise equality of the weight. -/
theorem sum_weights_ext (w1 w2 : FinProcInput → Rat) (l : List FinProcInput) :
    (∀ f, w1 f = w2 f) → sum_weights w1 l = sum_weights w2 l := by
  intro h
  induction l with
  | nil => rfl
  | cons f l ih => rw [sum_weights_cons, sum_weights_cons, h f, ih]

/-! ## The weight-bound obligation -/

/-- `C`'s rejected inputs never weigh more than `b` times the declared
total `M`: for every list whose entries `Classifier.rejects` under `C`
and whose `FinInput.fin_core`s are duplicate-free, the sum does not
exceed `b * M`. -/
def weight_bound_T (C : Image) (w : FinProcInput → Rat) (M b : Rat) : Prop :=
  ∀ l : List FinProcInput,
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l → rejects C f) →
    sum_weights w l ≤ b * M

/-! ## The declared distribution -/

/-- A task-supplied weight function and declared total.  Why the
instance is trusted task metadata rather than the submission's choice,
and why `w_core_blind` is what makes the per-core charge of
`weight_bound_T` well defined, is argued at `DISTRIBUTION` in
`Measure.v`. -/
structure Distribution where
  w : FinProcInput → Rat
  M : Rat
  w_nonneg : ∀ f, 0 ≤ w f
  /-- `weight_bound_mono` needs this and cannot get it from `w_nonneg`:
  `M` is declared, not summed, so nothing here forces it to agree in
  sign with the weights it is the total of.  Without it a consumer
  holding a `D : Distribution` has nothing to discharge that
  hypothesis with. -/
  M_nonneg : 0 ≤ M
  w_core_blind : ∀ f g, fin_core f = fin_core g → w f = w g

/-! ## Monotonicity and transport -/

/-- A bound proved at `b` is a bound at any larger `b'`, given `M`
nonnegative. -/
theorem weight_bound_mono (C : Image) (w : FinProcInput → Rat) (M b b' : Rat) :
    0 ≤ M → b ≤ b' → weight_bound_T C w M b → weight_bound_T C w M b' := by
  intro hM hbb hb l hnd hall
  exact Rat.le_trans (hb l hnd hall) (Rat.mul_le_mul_of_nonneg_right hbb hM)

theorem weight_bound_qeq (C : Image) (w : FinProcInput → Rat) (M M' b b' : Rat) :
    M = M' → b = b' → weight_bound_T C w M b → weight_bound_T C w M' b' := by
  intro hM hb
  subst M'
  subst b'
  exact id

theorem weight_bound_T_ext (C : Image) (w1 w2 : FinProcInput → Rat) (M b : Rat) :
    (∀ f, w1 f = w2 f) → weight_bound_T C w1 M b → weight_bound_T C w2 M b := by
  intro hw hb l hnd hall
  rw [← sum_weights_ext w1 w2 l hw]
  exact hb l hnd hall

/-! ## `weight_bound_T` bites -/

/-- The bound `1` at unit weight and total `1` fails as soon as two
inputs with distinct cores are both rejected.  The closing step compares
the closed `Rat` terms `1 + (1 + 0)` and `1 * 1`; `Rat.add` and `Rat.mul`
normalize through `Nat.gcd`, which the elaborator's reduction does not
unfold, so `decide +kernel` has the kernel evaluate the comparison. -/
theorem weight_bound_refutable (C : Image) (f1 f2 : FinProcInput) :
    rejects C f1 → rejects C f2 → fin_core f1 ≠ fin_core f2 →
    ¬ weight_bound_T C (fun _ => 1) 1 1 := by
  intro hr1 hr2 hne hb
  have hnd : ([f1, f2].map fin_core).Nodup := by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
      List.not_mem_nil, List.nodup_nil, hne, not_false_eq_true, and_self]
  have hsum := hb [f1, f2] hnd (by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hr1
    · exact (List.mem_singleton.mp hf) ▸ hr2)
  dsimp only [sum_weights, List.foldr] at hsum
  exact (by decide +kernel : ¬ ((1 : Rat) + (1 + 0) ≤ 1 * 1)) hsum

/-! ## The weight bound over the classifier pinned to forced-only -/

/-- `weight_bound_T` with `Classifier.rejects_fo` in place of
`Classifier.rejects`. -/
def weight_bound_T_fo (C : Image) (w : FinProcInput → Rat) (M b : Rat) : Prop :=
  ∀ l : List FinProcInput,
    (l.map fin_core).Nodup →
    (∀ f, f ∈ l → rejects_fo C f) →
    sum_weights w l ≤ b * M

theorem weight_bound_fo_mono (C : Image) (w : FinProcInput → Rat) (M b b' : Rat) :
    0 ≤ M → b ≤ b' → weight_bound_T_fo C w M b → weight_bound_T_fo C w M b' := by
  intro hM hbb hb l hnd hall
  exact Rat.le_trans (hb l hnd hall) (Rat.mul_le_mul_of_nonneg_right hbb hM)

theorem weight_bound_fo_qeq (C : Image) (w : FinProcInput → Rat) (M M' b b' : Rat) :
    M = M' → b = b' → weight_bound_T_fo C w M b → weight_bound_T_fo C w M' b' := by
  intro hM hb
  subst M'
  subst b'
  exact id

/-- Where the filter question is answered, the forced-only bound is
weaker than the unconfigured one, through
`Classifier.rejects_of_rejects_fo`. -/
theorem weight_bound_T_fo_of_weight_bound_T (C : Image) (w : FinProcInput → Rat) (M b : Rat) :
    classifier_decided C → weight_bound_T C w M b → weight_bound_T_fo C w M b := by
  intro hd hb l hnd hall
  exact hb l hnd (fun f hf => rejects_of_rejects_fo C f hd (hall f hf))

/-- The forced-only bound bites exactly as `weight_bound_refutable`
does, and closes the same way. -/
theorem weight_bound_fo_refutable (C : Image) (f1 f2 : FinProcInput) :
    rejects_fo C f1 → rejects_fo C f2 → fin_core f1 ≠ fin_core f2 →
    ¬ weight_bound_T_fo C (fun _ => 1) 1 1 := by
  intro hr1 hr2 hne hb
  have hnd : ([f1, f2].map fin_core).Nodup := by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
      List.not_mem_nil, List.nodup_nil, hne, not_false_eq_true, and_self]
  have hsum := hb [f1, f2] hnd (by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hr1
    · exact (List.mem_singleton.mp hf) ▸ hr2)
  dsimp only [sum_weights, List.foldr] at hsum
  exact (by decide +kernel : ¬ ((1 : Rat) + (1 + 0) ≤ 1 * 1)) hsum

end LinuxProcessSemantics.EquivalenceDefinition.Measure
