import LinuxProcessSemantics.EquivalenceDefinition.GatedSize
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Measure

/-! # Checks.Cases.EquivalenceDefinition.GatedSize — gated-slice statement pins

Not part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.GatedSize

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.EquivalenceDefinition.Classifier
open LinuxProcessSemantics.EquivalenceDefinition.Measure
open LinuxProcessSemantics.EquivalenceDefinition.GatedSize
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Classifier
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Measure

/-! ## A-GatedSize: the gated-slice statements -/

/-- The accepting part requires the gate's zero verdict and excludes
every earlier gate's universal zero verdict, with no input-validity clause.
model: `accepts_iff` and `slice_accept`. -/
theorem slice_accept_iff (prev : List Image) (G : Image) (f : FinProcInput) :
    slice_accept prev G f ↔
    (∀ en, valid_entry G en (to_proc_input f) →
      must_exit_with (Z_to_bv 64 0) G target_alloc_limit en (to_proc_input f)) ∧
    (∀ G' ∈ prev, ¬ (∀ en, valid_entry G' en (to_proc_input f) →
      must_exit_with (Z_to_bv 64 0) G' target_alloc_limit en (to_proc_input f))) := Iff.rfl

/-- The accepting gate receives the launch after a gate that refuses it.
model: `accepts_accept`, `accepts_refute`, and `slice_accept`. -/
theorem slice_accept_accept :
    slice_accept [undecodable_image] brk_unplaceable_image launch :=
  ⟨accepts_accept, fun _G hG => (List.mem_singleton.mp hG) ▸ accepts_refute⟩

/-- Acceptance by an earlier gate excludes the later accepting gate's slice.
model: `accepts_accept` and `slice_accept`'s prefix-refusal clause. -/
theorem slice_accept_refute :
    ¬ slice_accept [brk_unplaceable_image] brk_unplaceable_image launch :=
  fun h => h.2 _ (List.mem_singleton.mpr rfl) accepts_accept

/-- The residue excludes
every earlier gate's universal zero verdict, with no input-validity clause.
model: `accepts_iff` and `slice_rest`. -/
theorem slice_rest_iff (prev : List Image) (f : FinProcInput) :
    slice_rest prev f ↔
    (∀ G' ∈ prev, ¬ (∀ en, valid_entry G' en (to_proc_input f) →
      must_exit_with (Z_to_bv 64 0) G' target_alloc_limit en (to_proc_input f))) := Iff.rfl

/-- A refused concrete launch remains in the final part.
model: `accepts_refute` and `slice_rest`. -/
theorem slice_rest_accept : slice_rest [undecodable_image] launch :=
  fun _G hG => (List.mem_singleton.mp hG) ▸ accepts_refute

/-- A gate that accepts the launch removes it from the residue.
model: `accepts_accept` and `slice_rest`. -/
theorem slice_rest_refute : ¬ slice_rest [brk_unplaceable_image] launch :=
  fun h => h _ (List.mem_singleton.mpr rfl) accepts_accept

/-- The accepting part requires the gate's zero verdict and excludes
every earlier gate's universal zero verdict, with no input-validity clause.
model: `accepts_fo_iff` and `slice_accept_fo`. -/
theorem slice_accept_fo_iff (prev : List Image) (G : Image) (f : FinProcInput) :
    slice_accept_fo prev G f ↔
    (∀ en, valid_entry G en (to_proc_input f) →
      must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) G target_alloc_limit en (to_proc_input f)) ∧
    (∀ G' ∈ prev, ¬ (∀ en, valid_entry G' en (to_proc_input f) →
      must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) G' target_alloc_limit en (to_proc_input f))) := Iff.rfl

/-- The accepting gate receives the launch after a gate that refuses it.
model: `accepts_fo_accept`, `accepts_fo_refute`, and `slice_accept_fo`. -/
theorem slice_accept_fo_accept :
    slice_accept_fo [undecodable_image] brk_unplaceable_image launch :=
  ⟨accepts_fo_accept, fun _G hG => (List.mem_singleton.mp hG) ▸ accepts_fo_refute⟩

/-- Acceptance by an earlier gate excludes the later accepting gate's slice.
model: `accepts_fo_accept` and `slice_accept_fo`'s prefix-refusal clause. -/
theorem slice_accept_fo_refute :
    ¬ slice_accept_fo [brk_unplaceable_image] brk_unplaceable_image launch :=
  fun h => h.2 _ (List.mem_singleton.mpr rfl) accepts_fo_accept

/-- The residue excludes
every earlier gate's universal zero verdict, with no input-validity clause.
model: `accepts_fo_iff` and `slice_rest_fo`. -/
theorem slice_rest_fo_iff (prev : List Image) (f : FinProcInput) :
    slice_rest_fo prev f ↔
    (∀ G' ∈ prev, ¬ (∀ en, valid_entry G' en (to_proc_input f) →
      must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) G' target_alloc_limit en (to_proc_input f))) := Iff.rfl

/-- A refused concrete launch remains in the final part.
model: `accepts_fo_refute` and `slice_rest_fo`. -/
theorem slice_rest_fo_accept : slice_rest_fo [undecodable_image] launch :=
  fun _G hG => (List.mem_singleton.mp hG) ▸ accepts_fo_refute

/-- A gate that accepts the launch removes it from the residue.
model: `accepts_fo_accept` and `slice_rest_fo`. -/
theorem slice_rest_fo_refute : ¬ slice_rest_fo [brk_unplaceable_image] launch :=
  fun h => h _ (List.mem_singleton.mpr rfl) accepts_fo_accept

/-- The slice contract fixes independent entries, one shared input, and
role budgets; the conclusion spells out the underlying run fields.
model: `gated_slice_T` and `strong_equiv`. -/
theorem gated_slice_T_iff (Src A : Image) (P : FinProcInput → Prop) :
    gated_slice_T Src A P ↔
    ∀ f, valid_fin_input f → P f → ∀ es ea,
      valid_entry Src es (to_proc_input f) →
      valid_entry A ea (to_proc_input f) →
      ¬ (run Src source_alloc_limit es (to_proc_input f)).bh_unmodeled ∧
      ((run Src source_alloc_limit es (to_proc_input f)).bh_all_errors ∨
        ((∀ tr, (run Src source_alloc_limit es (to_proc_input f)).bh_traces tr ↔
          (run A target_alloc_limit ea (to_proc_input f)).bh_traces tr) ∧ ¬ (run A target_alloc_limit ea (to_proc_input f)).bh_errors)) := Iff.rfl

/-- An empty part owes no comparison even for the concrete undecodable images.
model: `gated_slice_T_vacuous_empty_slice`. -/
theorem gated_slice_T_accept :
    gated_slice_T undecodable_image undecodable_image (fun _ => False) :=
  gated_slice_T_vacuous_empty_slice _ _ _ (fun _ _ h => h)

/-- The valid launch belongs to its singleton part and has valid entries
on both sides; its undecodable source is unmodeled.
model: `launch_is_valid`, `classifier_launch_entry`, and `undecodable_run_unmodeled`. -/
theorem gated_slice_T_refute :
    ¬ gated_slice_T undecodable_image undecodable_image (fun f => f = launch) := by
  intro h
  exact (h launch launch_is_valid rfl demo_entry demo_entry
    classifier_launch_entry classifier_launch_entry).1 (undecodable_run_unmodeled _ _)

/-- The slice contract fixes independent entries, one shared input, and
role budgets; the conclusion spells out the underlying run fields.
model: `gated_slice_error_free_T` and `strong_equiv_error_free`. -/
theorem gated_slice_error_free_T_iff (Src A : Image) (P : FinProcInput → Prop) :
    gated_slice_error_free_T Src A P ↔
    ∀ f, valid_fin_input f → P f → ∀ es ea,
      valid_entry Src es (to_proc_input f) →
      valid_entry A ea (to_proc_input f) →
      ¬ (run Src source_alloc_limit es (to_proc_input f)).bh_errors ∧
      ¬ (run A target_alloc_limit ea (to_proc_input f)).bh_errors ∧
      (∀ tr, (run Src source_alloc_limit es (to_proc_input f)).bh_traces tr ↔
        (run A target_alloc_limit ea (to_proc_input f)).bh_traces tr) := Iff.rfl

/-- An empty part owes no comparison even for the concrete undecodable images.
model: `gated_slice_error_free_T_vacuous_empty_slice`. -/
theorem gated_slice_error_free_T_accept :
    gated_slice_error_free_T undecodable_image undecodable_image (fun _ => False) :=
  gated_slice_error_free_T_vacuous_empty_slice _ _ _ (fun _ _ h => h)

/-- The valid launch belongs to its singleton part and has valid entries
on both sides; its undecodable source errors.
model: `launch_is_valid`, `classifier_launch_entry`, and `undecodable_run_unmodeled`. -/
theorem gated_slice_error_free_T_refute :
    ¬ gated_slice_error_free_T undecodable_image undecodable_image (fun f => f = launch) := by
  intro h
  exact (h launch launch_is_valid rfl demo_entry demo_entry
    classifier_launch_entry classifier_launch_entry).1 (run_unmodeled_errors _ _ _ _ (undecodable_run_unmodeled _ _))

/-- The slice contract fixes independent entries, one shared input, and
role budgets; the conclusion spells out the underlying run fields.
model: `gated_slice_T_scfg` and `strong_equiv_scfg`. -/
theorem gated_slice_T_scfg_iff (cfg : SpuriousCfg) (Src A : Image) (P : FinProcInput → Prop) :
    gated_slice_T_scfg cfg Src A P ↔
    ∀ f, valid_fin_input f → P f → ∀ es ea,
      valid_entry Src es (to_proc_input f) →
      valid_entry A ea (to_proc_input f) →
      ¬ (run_scfg cfg Src source_alloc_limit es (to_proc_input f)).bh_unmodeled ∧
      ((run_scfg cfg Src source_alloc_limit es (to_proc_input f)).bh_all_errors ∨
        ((∀ tr, (run_scfg cfg Src source_alloc_limit es (to_proc_input f)).bh_traces tr ↔
          (run_scfg cfg A target_alloc_limit ea (to_proc_input f)).bh_traces tr) ∧ ¬ (run_scfg cfg A target_alloc_limit ea (to_proc_input f)).bh_errors)) := Iff.rfl

/-- An empty part owes no comparison even for the concrete undecodable images.
model: `gated_slice_T_scfg_vacuous_empty_slice`. -/
theorem gated_slice_T_scfg_accept :
    gated_slice_T_scfg forced_only_cfg undecodable_image undecodable_image (fun _ => False) :=
  gated_slice_T_scfg_vacuous_empty_slice forced_only_cfg _ _ _ (fun _ _ h => h)

/-- The valid launch belongs to its singleton part and has valid entries
on both sides; its undecodable source is unmodeled.
model: `launch_is_valid`, `classifier_launch_entry`, and `undecodable_run_scfg_unmodeled`. -/
theorem gated_slice_T_scfg_refute :
    ¬ gated_slice_T_scfg forced_only_cfg undecodable_image undecodable_image (fun f => f = launch) := by
  intro h
  exact (h launch launch_is_valid rfl demo_entry demo_entry
    classifier_launch_entry classifier_launch_entry).1 (undecodable_run_scfg_unmodeled forced_only_cfg _ _)

/-- The slice contract fixes independent entries, one shared input, and
role budgets; the conclusion spells out the underlying run fields.
model: `gated_slice_error_free_T_scfg` and `strong_equiv_error_free_scfg`. -/
theorem gated_slice_error_free_T_scfg_iff (cfg : SpuriousCfg) (Src A : Image) (P : FinProcInput → Prop) :
    gated_slice_error_free_T_scfg cfg Src A P ↔
    ∀ f, valid_fin_input f → P f → ∀ es ea,
      valid_entry Src es (to_proc_input f) →
      valid_entry A ea (to_proc_input f) →
      ¬ (run_scfg cfg Src source_alloc_limit es (to_proc_input f)).bh_errors ∧
      ¬ (run_scfg cfg A target_alloc_limit ea (to_proc_input f)).bh_errors ∧
      (∀ tr, (run_scfg cfg Src source_alloc_limit es (to_proc_input f)).bh_traces tr ↔
        (run_scfg cfg A target_alloc_limit ea (to_proc_input f)).bh_traces tr) := Iff.rfl

/-- An empty part owes no comparison even for the concrete undecodable images.
model: `gated_slice_error_free_T_scfg_vacuous_empty_slice`. -/
theorem gated_slice_error_free_T_scfg_accept :
    gated_slice_error_free_T_scfg forced_only_cfg undecodable_image undecodable_image (fun _ => False) :=
  gated_slice_error_free_T_scfg_vacuous_empty_slice forced_only_cfg _ _ _ (fun _ _ h => h)

/-- The valid launch belongs to its singleton part and has valid entries
on both sides; its undecodable source errors.
model: `launch_is_valid`, `classifier_launch_entry`, and `undecodable_run_scfg_unmodeled`. -/
theorem gated_slice_error_free_T_scfg_refute :
    ¬ gated_slice_error_free_T_scfg forced_only_cfg undecodable_image undecodable_image (fun f => f = launch) := by
  intro h
  exact (h launch launch_is_valid rfl demo_entry demo_entry
    classifier_launch_entry classifier_launch_entry).1 (run_scfg_unmodeled_errors forced_only_cfg _ _ _ _ (undecodable_run_scfg_unmodeled forced_only_cfg _ _))

/-- The bound ranges over pairwise distinct cores outside the predicate,
with validity at each member and weights independently folded after mapping.
model: `weight_bound_pred_T` and `sum_weights_iff`. -/
theorem weight_bound_pred_T_iff (P : FinProcInput → Prop) (w : FinProcInput → Rat)
    (M b : Rat) :
    weight_bound_pred_T P w M b ↔
    ∀ l : List FinProcInput, l.Pairwise (fun f g => fin_core f ≠ fin_core g) →
      (∀ f ∈ l, valid_fin_input f ∧ ¬ P f) →
      (l.map w).foldr (· + ·) 0 ≤ b * M := by
  simp only [weight_bound_pred_T, List.nodup_iff_pairwise_ne, List.pairwise_map,
    sum_weights_iff]

/-- The predicate accepting every input through the entry-less gate leaves
zero outside mass even at unit weight.
model: `weight_bound_pred_of_classifier` and `weight_bound_T_accept`. -/
theorem weight_bound_pred_T_accept :
    weight_bound_pred_T (accepts brk_unplaceable_image) (fun _ => 1) 1 0 :=
  (weight_bound_pred_of_classifier _ _ _ _).mp weight_bound_T_accept

/-- The two concrete valid launches have distinct cores and lie outside the
empty predicate; their unit weights sum to two, exceeding the claimed one.
model: `cores_nodup_accept`, `launch_is_valid`, and `valid_fin_input_stdin_irrelevant`. -/
theorem weight_bound_pred_T_refute :
    ¬ weight_bound_pred_T (fun _ => False) (fun _ => 1) 1 1 := by
  apply weight_bound_pred_refutable _ launch launch_other_stdin
  · exact launch_is_valid
  · exact fun h => h
  · exact valid_fin_input_stdin_irrelevant launch _ launch_is_valid
  · exact fun h => h
  · intro heq
    exact (List.nodup_cons.mp cores_nodup_accept).1 (List.mem_singleton.mpr heq)

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.GatedSize
