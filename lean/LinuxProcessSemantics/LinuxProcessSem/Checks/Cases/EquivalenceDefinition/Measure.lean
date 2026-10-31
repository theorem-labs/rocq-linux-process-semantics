import LinuxProcessSemantics.EquivalenceDefinition.Measure
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Classifier

/-! # Checks.Cases.EquivalenceDefinition.Measure — weight-bound statement pins

Not part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Measure

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.EquivalenceDefinition.Classifier
open LinuxProcessSemantics.EquivalenceDefinition.Measure
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Classifier

/-! ## A-Measure: input weights and the weight bound -/

/-- Summing input weights equals folding addition over the mapped weights.
model: `sum_weights_nil` and `sum_weights_cons`. -/
theorem sum_weights_iff (w : FinProcInput → Rat) (l : List FinProcInput) :
    sum_weights w l = (l.map w).foldr (· + ·) 0 := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    simp only [sum_weights_cons, List.map_cons, List.foldr_cons, ih]

/-- Two occurrences of the launch each contribute one to the sum.
model: `sum_weights` and `launch`. -/
theorem sum_weights_accept : sum_weights (fun _ => 1) [launch, launch] = 2 := by
  decide +kernel

/-- The sum counts both occurrences even when their records coincide.
model: `sum_weights` and `launch`. -/
theorem sum_weights_refute : sum_weights (fun _ => 1) [launch, launch] ≠ 1 := by
  decide +kernel

/-- The weight bound quantifies over pairwise distinct cores of valid nonaccepted inputs.
model: `weight_bound_T`, `rejects`, and `sum_weights_iff`. -/
theorem weight_bound_T_iff (C : Image) (w : FinProcInput → Rat) (M b : Rat) :
    weight_bound_T C w M b ↔
    ∀ l : List FinProcInput, l.Pairwise (fun f g => fin_core f ≠ fin_core g) →
      (∀ f ∈ l, valid_fin_input f ∧ ¬ accepts C f) →
      (l.map w).foldr (· + ·) 0 ≤ b * M := by
  simp only [weight_bound_T, List.nodup_iff_pairwise_ne, List.pairwise_map,
    rejects, sum_weights_iff]

/-- An image with no valid entries has a zero rejection-weight bound.
model: `weight_bound_T`, `accepts_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem weight_bound_T_accept :
    weight_bound_T brk_unplaceable_image (fun _ => 1) 1 0 := by
  intro l _ hall
  cases l with
  | nil => decide +kernel
  | cons f l =>
    exact ((hall f (List.mem_cons_self)).2
      (accepts_vacuous_no_entries _ _
        (fun en => brk_unplaceable_image_has_no_entry en _))).elim

/-- A rejected launch of unit weight refutes a zero bound.
model: `weight_bound_T`, `sum_weights`, and `rejects_accept`. -/
theorem weight_bound_T_refute :
    ¬ weight_bound_T undecodable_image (fun _ => 1) 1 0 := by
  intro hb
  have hsum := hb [launch] (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
    (fun f hf => (List.mem_singleton.mp hf) ▸ rejects_accept)
  dsimp only [sum_weights, List.foldr] at hsum
  exact (by decide +kernel : ¬ ((1 : Rat) + 0 ≤ 0 * 1)) hsum

/-- The forced-only bound quantifies over pairwise distinct cores of valid nonaccepted inputs.
model: `weight_bound_T_fo`, `rejects_fo`, and `sum_weights_iff`. -/
theorem weight_bound_T_fo_iff (C : Image) (w : FinProcInput → Rat) (M b : Rat) :
    weight_bound_T_fo C w M b ↔
    ∀ l : List FinProcInput, l.Pairwise (fun f g => fin_core f ≠ fin_core g) →
      (∀ f ∈ l, valid_fin_input f ∧ ¬ accepts_fo C f) →
      (l.map w).foldr (· + ·) 0 ≤ b * M := by
  simp only [weight_bound_T_fo, List.nodup_iff_pairwise_ne, List.pairwise_map,
    rejects_fo, sum_weights_iff]

/-- An image with no valid entries has a zero forced-only rejection-weight bound.
model: `weight_bound_T_fo`, `accepts_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem weight_bound_T_fo_accept :
    weight_bound_T_fo brk_unplaceable_image (fun _ => 1) 1 0 := by
  intro l _ hall
  cases l with
  | nil => decide +kernel
  | cons f l =>
    exact ((hall f (List.mem_cons_self)).2
      (accepts_fo_vacuous_no_entries _ _
        (fun en => brk_unplaceable_image_has_no_entry en _))).elim

/-- A launch rejected under forced-only classification refutes a zero bound.
model: `weight_bound_T_fo`, `sum_weights`, and `rejects_fo_accept`. -/
theorem weight_bound_T_fo_refute :
    ¬ weight_bound_T_fo undecodable_image (fun _ => 1) 1 0 := by
  intro hb
  have hsum := hb [launch] (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
    (fun f hf => (List.mem_singleton.mp hf) ▸ rejects_fo_accept)
  dsimp only [sum_weights, List.foldr] at hsum
  exact (by decide +kernel : ¬ ((1 : Rat) + 0 ≤ 0 * 1)) hsum

/-- The launch with a different user identifier retains its input core. -/
def launch_other_uid : FinProcInput := { launch with fin_uid := Z_to_bv 64 0 }

/-- The launch with a different standard-input byte changes its input core. -/
def launch_other_stdin : FinProcInput := { launch with fin_stdin := [Z_to_bv 8 0x62] }

/-- Changing standard input yields two distinct cores.
model: `fin_core`, `launch`, and `launch_other_stdin`. -/
theorem cores_nodup_accept : ([launch, launch_other_stdin].map fin_core).Nodup := by
  have hne : fin_core launch ≠ fin_core launch_other_stdin := by
    intro h
    have hs := congrArg FinCore.core_stdin h
    exact (by decide : launch.fin_stdin ≠ launch_other_stdin.fin_stdin) hs
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
    List.not_mem_nil, List.nodup_nil, hne, not_false_eq_true, and_self]

/-- Changing only the user identifier gives distinct records with a repeated core.
model: `fin_core`, `launch`, and `launch_other_uid`. -/
theorem cores_nodup_refute :
    launch_other_uid ≠ launch ∧ ¬ ([launch, launch_other_uid].map fin_core).Nodup := by
  constructor
  · intro h
    have hu := congrArg FinProcInput.fin_uid h
    exact (by decide : launch_other_uid.fin_uid ≠ launch.fin_uid) hu
  · intro h
    exact (List.nodup_cons.mp h).1 (List.mem_singleton.mpr rfl)

/-! ## A-Measure: the declared distribution -/

/-- Zero weights and a zero declared total satisfy the distribution obligations.
model: `Distribution`. -/
def zero_distribution : Distribution where
  w := fun _ => 0
  M := 0
  w_nonneg := by intro _; decide +kernel
  M_nonneg := by decide +kernel
  w_core_blind := by intro _ _ _; rfl

/-- A distribution can have zero total and zero weight on every input.
model: `Distribution` and `zero_distribution`. -/
theorem distribution_accept : ∃ D : Distribution, D.M = 0 ∧ ∀ f, D.w f = 0 := by
  exact ⟨zero_distribution, rfl, fun _ => rfl⟩

/-- Two positive weights distinguished by standard input, a field of the core.
model: `Distribution` and `fin_core`. -/
def core_distribution : Distribution where
  w := fun f => if (fin_core f).core_stdin = launch.fin_stdin then 1 else 2
  M := 3
  w_nonneg := by intro f; split <;> decide +kernel
  M_nonneg := by decide +kernel
  w_core_blind := by intro f g h; rw [h]

/-- Positive weights may vary with the input core while the declared total is positive.
model: `Distribution`, `fin_core`, `launch`, and `launch_other_stdin`. -/
theorem distribution_nonzero_accept : ∃ D : Distribution,
    D.M = 3 ∧ D.w launch = 1 ∧ D.w launch_other_stdin = 2 ∧
    D.w launch_other_uid = 1 := by
  refine ⟨core_distribution, ?_⟩
  decide +kernel

/-- A distribution cannot declare a negative total.
model: `Distribution.M_nonneg`. -/
theorem distribution_refute_M : ¬ ∃ D : Distribution, D.M = -1 := by
  rintro ⟨D, hM⟩
  have h := D.M_nonneg
  rw [hM] at h
  exact (by decide +kernel : ¬ ((0 : Rat) ≤ -1)) h

/-- A distribution cannot assign a negative weight to the launch.
model: `Distribution.w_nonneg` and `launch`. -/
theorem distribution_refute_w : ¬ ∃ D : Distribution, D.w launch = -1 := by
  rintro ⟨D, hw⟩
  have h := D.w_nonneg launch
  rw [hw] at h
  exact (by decide +kernel : ¬ ((0 : Rat) ≤ -1)) h

/-- Changing only the user identifier cannot change a distribution's weight.
model: `Distribution.w_core_blind`, `fin_core`, `launch`, and `launch_other_uid`. -/
theorem distribution_refute_core :
    ¬ ∃ D : Distribution, D.w launch = 0 ∧ D.w launch_other_uid = 1 := by
  rintro ⟨D, hw, hu⟩
  have hcore : fin_core launch_other_uid = fin_core launch := rfl
  have h := D.w_core_blind launch_other_uid launch hcore
  rw [hu, hw] at h
  exact (by decide +kernel : (1 : Rat) ≠ 0) h

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Measure
