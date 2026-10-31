import LinuxProcessSemantics.EquivalenceDefinition.Classifier
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.FinInput
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Equivalence
import LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Run

/-! # Checks.Cases.EquivalenceDefinition.Classifier — classifier statement pins

Not part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Classifier

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.EquivalenceDefinition.Classifier
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Equivalence

/-! ## A-Classifier: the unconfigured classifier statements -/

/-- The classifier budget is 512 GiB.
model: `classifier_alloc_limit` and the numeric `target_alloc_limit`. -/
theorem classifier_alloc_limit_value :
    classifier_alloc_limit = 0x8000000000 := by decide

/-- The classifier budget equals the target budget.
model: `classifier_alloc_limit` aliases `target_alloc_limit`. -/
theorem classifier_alloc_limit_accept :
    classifier_alloc_limit = target_alloc_limit := rfl

/-- The source budget is not the classifier budget.
model: `classifier_alloc_limit`, `source_alloc_limit`, and `target_alloc_limit`. -/
theorem classifier_alloc_limit_refute :
    classifier_alloc_limit ≠ source_alloc_limit := by decide

/-- Agreement compares trace prefixes and the three existential error facts.
model: `agree` and `trace_equiv` expanded into behavior fields. -/
theorem agree_iff (X Y : Image) (lim : Int) (inp : ProcInput) :
    agree X Y lim inp ↔
    (∀ enX enY, valid_entry X enX inp → valid_entry Y enY inp →
      ∀ tr, (run X lim enX inp).bh_traces tr ↔
        (run Y lim enY inp).bh_traces tr)
    ∧ ((∃ en, valid_entry X en inp ∧ (run X lim en inp).bh_errors)
        ↔ (∃ en, valid_entry Y en inp ∧ (run Y lim en inp).bh_errors))
    ∧ ((∃ en, valid_entry X en inp ∧ (run X lim en inp).bh_all_errors)
        ↔ (∃ en, valid_entry Y en inp ∧ (run Y lim en inp).bh_all_errors))
    ∧ ((∃ en, valid_entry X en inp ∧ (run X lim en inp).bh_unmodeled)
        ↔ (∃ en, valid_entry Y en inp ∧ (run Y lim en inp).bh_unmodeled)) := Iff.rfl

/-- Good inputs require error-freedom and equal trace sets at valid entry pairs.
model: `good_input`, `strong_equiv_error_free`, `error_free`, and `trace_equiv`. -/
theorem good_input_iff (O1 O2 : Image) (inp : ProcInput) :
    good_input O1 O2 inp ↔
    ∀ en1 en2, valid_entry O1 en1 inp → valid_entry O2 en2 inp →
      (¬ (run O1 source_alloc_limit en1 inp).bh_errors)
      ∧ (¬ (run O2 target_alloc_limit en2 inp).bh_errors)
      ∧ (∀ tr, (run O1 source_alloc_limit en1 inp).bh_traces tr ↔
          (run O2 target_alloc_limit en2 inp).bh_traces tr) := Iff.rfl

/-- Error-free inputs exclude source-budget errors at valid entries.
model: `error_free_input` and `error_free` expanded into `bh_errors`. -/
theorem error_free_input_iff (O : Image) (inp : ProcInput) :
    error_free_input O inp ↔
    ∀ enO, valid_entry O enO inp → ¬ (run O source_alloc_limit enO inp).bh_errors := Iff.rfl

/-- Deciding requires per-entry correctness and one of the two terminating verdicts.
model: `decides`, the two verdict words, and the classifier budget alias. -/
theorem decides_iff (C : Image) (spec : ProcInput → Prop) :
    decides C spec ↔
    ∀ f : FinProcInput, valid_fin_input f →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (spec (to_proc_input f)))
        ∧ (must_exit_with (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- Classifier totality requires exit 0 or exit 1 on valid finite inputs and entries.
model: `classifier_total_T`, the verdict words, and `classifier_alloc_limit`. -/
theorem classifier_total_T_iff (C : Image) :
    classifier_total_T C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      ∀ en, valid_entry C en (to_proc_input f) →
        must_exit_with (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
        ∨ must_exit_with (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f) := Iff.rfl

/-- Patch classification decides both agreement judgments at their separate role budgets.
model: `classifies_patch_diff_T`, `decides`, and `agree` expanded into exits and behavior fields. -/
theorem classifies_patch_diff_T_iff (O1 P1 O2 P2 C : Image) :
    classifies_patch_diff_T O1 P1 O2 P2 C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (((∀ enX enY, valid_entry O1 enX (to_proc_input f) → valid_entry P1 enY (to_proc_input f) →
              ∀ tr, (run O1 source_alloc_limit enX (to_proc_input f)).bh_traces tr ↔
                (run P1 source_alloc_limit enY (to_proc_input f)).bh_traces tr)
            ∧ ((∃ en, valid_entry O1 en (to_proc_input f) ∧ (run O1 source_alloc_limit en (to_proc_input f)).bh_errors)
                ↔ (∃ en, valid_entry P1 en (to_proc_input f) ∧ (run P1 source_alloc_limit en (to_proc_input f)).bh_errors))
            ∧ ((∃ en, valid_entry O1 en (to_proc_input f) ∧ (run O1 source_alloc_limit en (to_proc_input f)).bh_all_errors)
                ↔ (∃ en, valid_entry P1 en (to_proc_input f) ∧ (run P1 source_alloc_limit en (to_proc_input f)).bh_all_errors))
            ∧ ((∃ en, valid_entry O1 en (to_proc_input f) ∧ (run O1 source_alloc_limit en (to_proc_input f)).bh_unmodeled)
                ↔ (∃ en, valid_entry P1 en (to_proc_input f) ∧ (run P1 source_alloc_limit en (to_proc_input f)).bh_unmodeled)))
          ∧ ((∀ enX enY, valid_entry O2 enX (to_proc_input f) → valid_entry P2 enY (to_proc_input f) →
              ∀ tr, (run O2 target_alloc_limit enX (to_proc_input f)).bh_traces tr ↔
                (run P2 target_alloc_limit enY (to_proc_input f)).bh_traces tr)
            ∧ ((∃ en, valid_entry O2 en (to_proc_input f) ∧ (run O2 target_alloc_limit en (to_proc_input f)).bh_errors)
                ↔ (∃ en, valid_entry P2 en (to_proc_input f) ∧ (run P2 target_alloc_limit en (to_proc_input f)).bh_errors))
            ∧ ((∃ en, valid_entry O2 en (to_proc_input f) ∧ (run O2 target_alloc_limit en (to_proc_input f)).bh_all_errors)
                ↔ (∃ en, valid_entry P2 en (to_proc_input f) ∧ (run P2 target_alloc_limit en (to_proc_input f)).bh_all_errors))
            ∧ ((∃ en, valid_entry O2 en (to_proc_input f) ∧ (run O2 target_alloc_limit en (to_proc_input f)).bh_unmodeled)
                ↔ (∃ en, valid_entry P2 en (to_proc_input f) ∧ (run P2 target_alloc_limit en (to_proc_input f)).bh_unmodeled)))))
        ∧ (must_exit_with (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- Good-input classification decides source and target safety with trace equality.
model: `classifies_good_inputs_T`, `decides`, and `good_input` expanded into exits and behavior fields. -/
theorem classifies_good_inputs_T_iff (O1 O2 C : Image) :
    classifies_good_inputs_T O1 O2 C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (∀ en1 en2, valid_entry O1 en1 (to_proc_input f) → valid_entry O2 en2 (to_proc_input f) →
              (¬ (run O1 source_alloc_limit en1 (to_proc_input f)).bh_errors)
              ∧ (¬ (run O2 target_alloc_limit en2 (to_proc_input f)).bh_errors)
              ∧ (∀ tr, (run O1 source_alloc_limit en1 (to_proc_input f)).bh_traces tr ↔
                  (run O2 target_alloc_limit en2 (to_proc_input f)).bh_traces tr)))
        ∧ (must_exit_with (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- Error-free-input classification decides safety of the original at the source budget.
model: `classifies_error_free_inputs_T`, `decides`, and `error_free_input` expanded into exits and errors. -/
theorem classifies_error_free_inputs_T_iff (O C : Image) :
    classifies_error_free_inputs_T O C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (∀ enO, valid_entry O enO (to_proc_input f) → ¬ (run O source_alloc_limit enO (to_proc_input f)).bh_errors))
        ∧ (must_exit_with (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- Acceptance requires exit 0 at each valid entry.
model: `accepts`, `verdict_accept`, and `classifier_alloc_limit`. -/
theorem accepts_iff (C : Image) (f : FinProcInput) :
    accepts C f ↔
    ∀ en, valid_entry C en (to_proc_input f) →
      must_exit_with (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) := Iff.rfl

/-- Rejection requires a valid finite input and negates the universal accepting verdict.
model: `rejects` and `accepts` expanded into validity and `must_exit_with`. -/
theorem rejects_iff (C : Image) (f : FinProcInput) :
    rejects C f ↔ valid_fin_input f ∧
      ¬ (∀ en, valid_entry C en (to_proc_input f) →
        must_exit_with (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- The shared launch has a valid entry for the undecodable image, reused by the refutation pins.
model: `undecodable_entry_valid` and the Sv48, argv, and envp clauses of `launch_is_valid`. -/
theorem classifier_launch_entry :
    valid_entry undecodable_image demo_entry (to_proc_input launch) := undecodable_entry_valid _
      (valid_input_va_size _ launch_is_valid)
      (valid_input_argv _ launch_is_valid) (valid_input_envp _ launch_is_valid)

/-- Two concrete images with no valid entry agree on the launch.
model: `agree_vacuous_no_entries` and `brk_unplaceable_image_has_no_entry`. -/
theorem agree_accept :
    agree brk_unplaceable_image brk_unplaceable_image source_alloc_limit (to_proc_input launch) := agree_vacuous_no_entries _ _ _ _
      (fun en => brk_unplaceable_image_has_no_entry en _) (fun en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable image disagrees with the entry-less image on coverage.
model: `agree` compares `bh_unmodeled`; `undecodable_run_unmodeled` supplies the unmatched witness. -/
theorem agree_refute :
    ¬ agree undecodable_image brk_unplaceable_image source_alloc_limit (to_proc_input launch) := by
  intro h
  obtain ⟨en, hen, _⟩ := h.2.2.2.mp
    ⟨demo_entry, classifier_launch_entry, undecodable_run_unmodeled _ _⟩
  exact brk_unplaceable_image_has_no_entry en _ hen

/-- The entry-less second image makes the concrete launch good.
model: `good_input_vacuous_no_second_entries` and `brk_unplaceable_image_has_no_entry`. -/
theorem good_input_accept :
    good_input undecodable_image brk_unplaceable_image (to_proc_input launch) := good_input_vacuous_no_second_entries _ _ _ (fun en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable image is not good against itself at the concrete launch.
model: `good_input_refuted_by_source_error` and `run_unmodeled_errors` at `undecodable_run_unmodeled`. -/
theorem good_input_refute :
    ¬ good_input undecodable_image undecodable_image (to_proc_input launch) := good_input_refuted_by_source_error _ _ _ demo_entry demo_entry
      classifier_launch_entry classifier_launch_entry (run_unmodeled_errors _ _ _ _ (undecodable_run_unmodeled _ _))

/-- The entry-less original is error-free at the concrete launch.
model: `error_free_input_vacuous_no_entries` and `brk_unplaceable_image_has_no_entry`. -/
theorem error_free_input_accept :
    error_free_input brk_unplaceable_image (to_proc_input launch) := error_free_input_vacuous_no_entries _ _ (fun en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable original is not error-free at the concrete launch.
model: `error_free_input_refuted_by_error` and `run_unmodeled_errors` at `undecodable_run_unmodeled`. -/
theorem error_free_input_refute :
    ¬ error_free_input undecodable_image (to_proc_input launch) := error_free_input_refuted_by_error _ _ demo_entry classifier_launch_entry
      (run_unmodeled_errors _ _ _ _ (undecodable_run_unmodeled _ _))

/-- The entry-less classifier accepts the concrete launch.
model: `accepts_vacuous_no_entries` and `brk_unplaceable_image_has_no_entry`. -/
theorem accepts_accept :
    accepts brk_unplaceable_image launch := accepts_vacuous_no_entries _ _ (fun en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable classifier does not accept the concrete launch.
model: `accepts_refuted_by_entry`, `must_exit_with_refuted_by_error`, and `undecodable_run_unmodeled`. -/
theorem accepts_refute :
    ¬ accepts undecodable_image launch := accepts_refuted_by_entry _ _ demo_entry classifier_launch_entry
      (must_exit_with_refuted_by_error _ _ _ _ _ (run_unmodeled_errors _ _ _ _ (undecodable_run_unmodeled _ _)))

/-- The undecodable classifier rejects the valid concrete launch.
model: `rejects`, `launch_is_valid`, and `accepts_refute`. -/
theorem rejects_accept :
    rejects undecodable_image launch := ⟨launch_is_valid, accepts_refute⟩

/-- The entry-less classifier does not reject the concrete launch.
model: `rejects` negates acceptance, while `accepts_accept` establishes it. -/
theorem rejects_refute :
    ¬ rejects brk_unplaceable_image launch := fun h => h.2 accepts_accept

/-- The entry-less classifier satisfies totality.
model: `classifier_total_T_vacuous_no_entries` and `brk_unplaceable_image_has_no_entry`. -/
theorem classifier_total_T_accept :
    classifier_total_T brk_unplaceable_image := classifier_total_T_vacuous_no_entries _ (fun _ en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable classifier fails totality on the concrete launch.
model: `classifier_total_T_refuted_by_undecided`, `must_exit_with_refuted_by_error`, and `undecodable_run_unmodeled`. -/
theorem classifier_total_T_refute :
    ¬ classifier_total_T undecodable_image := classifier_total_T_refuted_by_undecided _ launch demo_entry launch_is_valid
      classifier_launch_entry
      (must_exit_with_refuted_by_error _ _ _ _ _ (run_unmodeled_errors _ _ _ _ (undecodable_run_unmodeled _ _)))
      (must_exit_with_refuted_by_error _ _ _ _ _ (run_unmodeled_errors _ _ _ _ (undecodable_run_unmodeled _ _)))

/-- The entry-less classifier decides the false property vacuously.
model: `decides_vacuous_no_entries` and `brk_unplaceable_image_has_no_entry`. -/
theorem decides_accept :
    decides brk_unplaceable_image (fun _ => False) := decides_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable classifier fails to decide the false property.
model: `decides_implies_total` and `classifier_total_T_refute` at the concrete launch. -/
theorem decides_refute :
    ¬ decides undecodable_image (fun _ => False) := fun h => classifier_total_T_refute (decides_implies_total _ _ h)

/-- Exit zero holds at the classifier budget for every entry and input.
model: `Checks.Omni.exit0_exec` and `OmniEquivalence.must_exit_with_iff`.
-/
theorem exit0_classifier_verdict (en : ExecEntry) (inp : ProcInput) :
    must_exit_with verdict_accept exit0_image classifier_alloc_limit en inp :=
  (LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.must_exit_with_iff _ _ _ _ _).2
    (LinuxProcessSemantics.LinuxProcessSem.OmniRun.exec_conseq _ _ _ _
      (Checks.Omni.exit0_exec _ _ _ _ _ _) (fun _ _ h => h.2))

/-- The accepting classifier has an entry at the valid finite launch.
model: `valid_entry` has the same reservation bounds for `exit0_image` and `undecodable_image`.
-/
theorem exit0_classifier_entry : valid_entry exit0_image demo_entry (to_proc_input launch) := by
  rw [valid_entry_sv48 _ _ _ (valid_input_va_size _ launch_is_valid)]
  refine ⟨by unfold valid_sp; decide, by unfold valid_brk; decide,
    by unfold valid_mmap_base; decide, ?_⟩
  exact classifier_launch_entry.2.2.2

/-- A real terminating classifier decides the declaration shared by every valid finite input.
model: `decides` and the exit-zero witness at every entry, with `exit0_classifier_entry` inhabiting the range.
-/
theorem decides_exit0_accept : decides exit0_image (fun inp => inp.in_va_size = .Sv48) := by
  intro f hf en _
  have h := exit0_classifier_verdict en (to_proc_input f)
  exact ⟨⟨fun _ => valid_input_va_size _ hf, fun _ => h⟩, Or.inl h⟩

/-- Totality cannot excuse an accepting verdict for the false property.
model: `decides_refuted_by_wrong_verdict` at the inhabited finite launch.
-/
theorem decides_exit0_refute : ¬ decides exit0_image (fun _ => False) :=
  decides_refuted_by_wrong_verdict _ _ launch demo_entry launch_is_valid
    exit0_classifier_entry (exit0_classifier_verdict _ _) (fun h => h)

/-- The entry-less classifier satisfies `classifies_patch_diff_T` for the concrete originals.
model: `classifies_patch_diff_T`, `decides_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_patch_diff_T_accept :
    classifies_patch_diff_T brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image := decides_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable classifier fails `classifies_patch_diff_T` for the concrete originals.
model: `classifies_patch_diff_T`, `decides_implies_total`, and `classifier_total_T_refute` at the concrete launch. -/
theorem classifies_patch_diff_T_refute :
    ¬ classifies_patch_diff_T brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image undecodable_image := fun h => classifier_total_T_refute (decides_implies_total _ _ h)

/-- The entry-less classifier satisfies `classifies_good_inputs_T` for the concrete originals.
model: `classifies_good_inputs_T`, `decides_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_good_inputs_T_accept :
    classifies_good_inputs_T brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image := decides_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable classifier fails `classifies_good_inputs_T` for the concrete originals.
model: `classifies_good_inputs_T`, `decides_implies_total`, and `classifier_total_T_refute` at the concrete launch. -/
theorem classifies_good_inputs_T_refute :
    ¬ classifies_good_inputs_T brk_unplaceable_image brk_unplaceable_image undecodable_image := fun h => classifier_total_T_refute (decides_implies_total _ _ h)

/-- The entry-less classifier satisfies `classifies_error_free_inputs_T` for the concrete originals.
model: `classifies_error_free_inputs_T`, `decides_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_error_free_inputs_T_accept :
    classifies_error_free_inputs_T brk_unplaceable_image brk_unplaceable_image := decides_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable classifier fails `classifies_error_free_inputs_T` for the concrete originals.
model: `classifies_error_free_inputs_T`, `decides_implies_total`, and `classifier_total_T_refute` at the concrete launch. -/
theorem classifies_error_free_inputs_T_refute :
    ¬ classifies_error_free_inputs_T brk_unplaceable_image undecodable_image := fun h => classifier_total_T_refute (decides_implies_total _ _ h)

/-! ## A-Classifier-fo: the configured, fail-only and hwcap classifier statements -/

open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-- Configured agreement compares trace prefixes and all three existential error facts.
model: `agree_s` expanded into configured behaviors and verdicts. -/
theorem agree_s_iff (cfg : SpuriousCfg) (X Y : Image) (lim : Int) (inp : ProcInput) :
    agree_s cfg X Y lim inp ↔
    (∀ enX enY, valid_entry X enX inp → valid_entry Y enY inp →
      ∀ tr, (run_scfg cfg X lim enX inp).bh_traces tr ↔
        (run_scfg cfg Y lim enY inp).bh_traces tr)
    ∧ ((∃ en, valid_entry X en inp ∧ (run_scfg cfg X lim en inp).bh_errors)
        ↔ (∃ en, valid_entry Y en inp ∧ (run_scfg cfg Y lim en inp).bh_errors))
    ∧ ((∃ en, valid_entry X en inp ∧ (run_scfg cfg X lim en inp).bh_all_errors)
        ↔ (∃ en, valid_entry Y en inp ∧ (run_scfg cfg Y lim en inp).bh_all_errors))
    ∧ ((∃ en, valid_entry X en inp ∧ (run_scfg cfg X lim en inp).bh_unmodeled)
        ↔ (∃ en, valid_entry Y en inp ∧ (run_scfg cfg Y lim en inp).bh_unmodeled)) := Iff.rfl

/-- Configured goodness requires source and target error-freedom with equal traces.
model: `good_input_s` expanded into configured behaviors and verdicts. -/
theorem good_input_s_iff (cfg : SpuriousCfg) (O1 O2 : Image) (inp : ProcInput) :
    good_input_s cfg O1 O2 inp ↔
    ∀ en1 en2, valid_entry O1 en1 inp → valid_entry O2 en2 inp →
      (¬ (run_scfg cfg O1 source_alloc_limit en1 inp).bh_errors)
      ∧ (¬ (run_scfg cfg O2 target_alloc_limit en2 inp).bh_errors)
      ∧ (∀ tr, (run_scfg cfg O1 source_alloc_limit en1 inp).bh_traces tr ↔
          (run_scfg cfg O2 target_alloc_limit en2 inp).bh_traces tr) := Iff.rfl

/-- The forced-only decider gives the correct verdict and terminates at valid entries.
model: `decides_fo` expanded into entry quantifiers and verdicts. -/
theorem decides_fo_iff (C : Image) (spec : ProcInput → Prop) :
    decides_fo C spec ↔
    ∀ f : FinProcInput, valid_fin_input f →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (spec (to_proc_input f)))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- Forced-only totality requires an accepting or rejecting exit at valid entries.
model: `classifier_total_T_fo` expanded into entry quantifiers and verdicts. -/
theorem classifier_total_T_fo_iff (C : Image) :
    classifier_total_T_fo C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      ∀ en, valid_entry C en (to_proc_input f) →
        must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
        ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f) := Iff.rfl

/-- The forced-only classifier decides both configured agreements at their role budgets.
model: `classifies_patch_diff_T_s` expanded into configured behaviors and verdicts. -/
theorem classifies_patch_diff_T_s_iff (cfg : SpuriousCfg) (O1 P1 O2 P2 C : Image) :
    classifies_patch_diff_T_s cfg O1 P1 O2 P2 C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (((∀ enX enY, valid_entry O1 enX (to_proc_input f) → valid_entry P1 enY (to_proc_input f) →
              ∀ tr, (run_scfg cfg O1 source_alloc_limit enX (to_proc_input f)).bh_traces tr ↔
                (run_scfg cfg P1 source_alloc_limit enY (to_proc_input f)).bh_traces tr)
            ∧ ((∃ en, valid_entry O1 en (to_proc_input f) ∧ (run_scfg cfg O1 source_alloc_limit en (to_proc_input f)).bh_errors)
                ↔ (∃ en, valid_entry P1 en (to_proc_input f) ∧ (run_scfg cfg P1 source_alloc_limit en (to_proc_input f)).bh_errors))
            ∧ ((∃ en, valid_entry O1 en (to_proc_input f) ∧ (run_scfg cfg O1 source_alloc_limit en (to_proc_input f)).bh_all_errors)
                ↔ (∃ en, valid_entry P1 en (to_proc_input f) ∧ (run_scfg cfg P1 source_alloc_limit en (to_proc_input f)).bh_all_errors))
            ∧ ((∃ en, valid_entry O1 en (to_proc_input f) ∧ (run_scfg cfg O1 source_alloc_limit en (to_proc_input f)).bh_unmodeled)
                ↔ (∃ en, valid_entry P1 en (to_proc_input f) ∧ (run_scfg cfg P1 source_alloc_limit en (to_proc_input f)).bh_unmodeled)))
          ∧ ((∀ enX enY, valid_entry O2 enX (to_proc_input f) → valid_entry P2 enY (to_proc_input f) →
              ∀ tr, (run_scfg cfg O2 target_alloc_limit enX (to_proc_input f)).bh_traces tr ↔
                (run_scfg cfg P2 target_alloc_limit enY (to_proc_input f)).bh_traces tr)
            ∧ ((∃ en, valid_entry O2 en (to_proc_input f) ∧ (run_scfg cfg O2 target_alloc_limit en (to_proc_input f)).bh_errors)
                ↔ (∃ en, valid_entry P2 en (to_proc_input f) ∧ (run_scfg cfg P2 target_alloc_limit en (to_proc_input f)).bh_errors))
            ∧ ((∃ en, valid_entry O2 en (to_proc_input f) ∧ (run_scfg cfg O2 target_alloc_limit en (to_proc_input f)).bh_all_errors)
                ↔ (∃ en, valid_entry P2 en (to_proc_input f) ∧ (run_scfg cfg P2 target_alloc_limit en (to_proc_input f)).bh_all_errors))
            ∧ ((∃ en, valid_entry O2 en (to_proc_input f) ∧ (run_scfg cfg O2 target_alloc_limit en (to_proc_input f)).bh_unmodeled)
                ↔ (∃ en, valid_entry P2 en (to_proc_input f) ∧ (run_scfg cfg P2 target_alloc_limit en (to_proc_input f)).bh_unmodeled)))))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- The forced-only classifier decides configured error-freedom and trace equality.
model: `classifies_good_inputs_T_s` expanded into configured behaviors and verdicts. -/
theorem classifies_good_inputs_T_s_iff (cfg : SpuriousCfg) (O1 O2 C : Image) :
    classifies_good_inputs_T_s cfg O1 O2 C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (∀ en1 en2, valid_entry O1 en1 (to_proc_input f) → valid_entry O2 en2 (to_proc_input f) →
              (¬ (run_scfg cfg O1 source_alloc_limit en1 (to_proc_input f)).bh_errors)
              ∧ (¬ (run_scfg cfg O2 target_alloc_limit en2 (to_proc_input f)).bh_errors)
              ∧ (∀ tr, (run_scfg cfg O1 source_alloc_limit en1 (to_proc_input f)).bh_traces tr ↔
                  (run_scfg cfg O2 target_alloc_limit en2 (to_proc_input f)).bh_traces tr)))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- The forced-only decider gives the correct verdict and terminates at valid entries. The input declares RV64GC.
model: `decides_fo_hwcap_rv64gc` expanded into entry quantifiers and verdicts. -/
theorem decides_fo_hwcap_rv64gc_iff (C : Image) (spec : ProcInput → Prop) :
    decides_fo_hwcap_rv64gc C spec ↔
    ∀ f : FinProcInput, valid_fin_input f →
      (to_proc_input f).in_hwcap = hwcap_rv64gc →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (spec (to_proc_input f)))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- The forced-only decider gives the correct verdict and terminates at valid entries. The input declares RV64GCV.
model: `decides_fo_hwcap_rv64gcv` expanded into entry quantifiers and verdicts. -/
theorem decides_fo_hwcap_rv64gcv_iff (C : Image) (spec : ProcInput → Prop) :
    decides_fo_hwcap_rv64gcv C spec ↔
    ∀ f : FinProcInput, valid_fin_input f →
      (to_proc_input f).in_hwcap = hwcap_rv64gcv →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (spec (to_proc_input f)))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- The forced-only classifier decides both configured agreements at their role budgets. The input declares RV64GC.
model: `classifies_patch_diff_T_s_hwcap_rv64gc` expanded into configured behaviors and verdicts. -/
theorem classifies_patch_diff_T_s_hwcap_rv64gc_iff (cfg : SpuriousCfg) (O1 P1 O2 P2 C : Image) :
    classifies_patch_diff_T_s_hwcap_rv64gc cfg O1 P1 O2 P2 C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      (to_proc_input f).in_hwcap = hwcap_rv64gc →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (((∀ enX enY, valid_entry O1 enX (to_proc_input f) → valid_entry P1 enY (to_proc_input f) →
              ∀ tr, (run_scfg cfg O1 source_alloc_limit enX (to_proc_input f)).bh_traces tr ↔
                (run_scfg cfg P1 source_alloc_limit enY (to_proc_input f)).bh_traces tr)
            ∧ ((∃ en, valid_entry O1 en (to_proc_input f) ∧ (run_scfg cfg O1 source_alloc_limit en (to_proc_input f)).bh_errors)
                ↔ (∃ en, valid_entry P1 en (to_proc_input f) ∧ (run_scfg cfg P1 source_alloc_limit en (to_proc_input f)).bh_errors))
            ∧ ((∃ en, valid_entry O1 en (to_proc_input f) ∧ (run_scfg cfg O1 source_alloc_limit en (to_proc_input f)).bh_all_errors)
                ↔ (∃ en, valid_entry P1 en (to_proc_input f) ∧ (run_scfg cfg P1 source_alloc_limit en (to_proc_input f)).bh_all_errors))
            ∧ ((∃ en, valid_entry O1 en (to_proc_input f) ∧ (run_scfg cfg O1 source_alloc_limit en (to_proc_input f)).bh_unmodeled)
                ↔ (∃ en, valid_entry P1 en (to_proc_input f) ∧ (run_scfg cfg P1 source_alloc_limit en (to_proc_input f)).bh_unmodeled)))
          ∧ ((∀ enX enY, valid_entry O2 enX (to_proc_input f) → valid_entry P2 enY (to_proc_input f) →
              ∀ tr, (run_scfg cfg O2 target_alloc_limit enX (to_proc_input f)).bh_traces tr ↔
                (run_scfg cfg P2 target_alloc_limit enY (to_proc_input f)).bh_traces tr)
            ∧ ((∃ en, valid_entry O2 en (to_proc_input f) ∧ (run_scfg cfg O2 target_alloc_limit en (to_proc_input f)).bh_errors)
                ↔ (∃ en, valid_entry P2 en (to_proc_input f) ∧ (run_scfg cfg P2 target_alloc_limit en (to_proc_input f)).bh_errors))
            ∧ ((∃ en, valid_entry O2 en (to_proc_input f) ∧ (run_scfg cfg O2 target_alloc_limit en (to_proc_input f)).bh_all_errors)
                ↔ (∃ en, valid_entry P2 en (to_proc_input f) ∧ (run_scfg cfg P2 target_alloc_limit en (to_proc_input f)).bh_all_errors))
            ∧ ((∃ en, valid_entry O2 en (to_proc_input f) ∧ (run_scfg cfg O2 target_alloc_limit en (to_proc_input f)).bh_unmodeled)
                ↔ (∃ en, valid_entry P2 en (to_proc_input f) ∧ (run_scfg cfg P2 target_alloc_limit en (to_proc_input f)).bh_unmodeled)))))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- The forced-only classifier decides both configured agreements at their role budgets. The input declares RV64GCV.
model: `classifies_patch_diff_T_s_hwcap_rv64gcv` expanded into configured behaviors and verdicts. -/
theorem classifies_patch_diff_T_s_hwcap_rv64gcv_iff (cfg : SpuriousCfg) (O1 P1 O2 P2 C : Image) :
    classifies_patch_diff_T_s_hwcap_rv64gcv cfg O1 P1 O2 P2 C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      (to_proc_input f).in_hwcap = hwcap_rv64gcv →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (((∀ enX enY, valid_entry O1 enX (to_proc_input f) → valid_entry P1 enY (to_proc_input f) →
              ∀ tr, (run_scfg cfg O1 source_alloc_limit enX (to_proc_input f)).bh_traces tr ↔
                (run_scfg cfg P1 source_alloc_limit enY (to_proc_input f)).bh_traces tr)
            ∧ ((∃ en, valid_entry O1 en (to_proc_input f) ∧ (run_scfg cfg O1 source_alloc_limit en (to_proc_input f)).bh_errors)
                ↔ (∃ en, valid_entry P1 en (to_proc_input f) ∧ (run_scfg cfg P1 source_alloc_limit en (to_proc_input f)).bh_errors))
            ∧ ((∃ en, valid_entry O1 en (to_proc_input f) ∧ (run_scfg cfg O1 source_alloc_limit en (to_proc_input f)).bh_all_errors)
                ↔ (∃ en, valid_entry P1 en (to_proc_input f) ∧ (run_scfg cfg P1 source_alloc_limit en (to_proc_input f)).bh_all_errors))
            ∧ ((∃ en, valid_entry O1 en (to_proc_input f) ∧ (run_scfg cfg O1 source_alloc_limit en (to_proc_input f)).bh_unmodeled)
                ↔ (∃ en, valid_entry P1 en (to_proc_input f) ∧ (run_scfg cfg P1 source_alloc_limit en (to_proc_input f)).bh_unmodeled)))
          ∧ ((∀ enX enY, valid_entry O2 enX (to_proc_input f) → valid_entry P2 enY (to_proc_input f) →
              ∀ tr, (run_scfg cfg O2 target_alloc_limit enX (to_proc_input f)).bh_traces tr ↔
                (run_scfg cfg P2 target_alloc_limit enY (to_proc_input f)).bh_traces tr)
            ∧ ((∃ en, valid_entry O2 en (to_proc_input f) ∧ (run_scfg cfg O2 target_alloc_limit en (to_proc_input f)).bh_errors)
                ↔ (∃ en, valid_entry P2 en (to_proc_input f) ∧ (run_scfg cfg P2 target_alloc_limit en (to_proc_input f)).bh_errors))
            ∧ ((∃ en, valid_entry O2 en (to_proc_input f) ∧ (run_scfg cfg O2 target_alloc_limit en (to_proc_input f)).bh_all_errors)
                ↔ (∃ en, valid_entry P2 en (to_proc_input f) ∧ (run_scfg cfg P2 target_alloc_limit en (to_proc_input f)).bh_all_errors))
            ∧ ((∃ en, valid_entry O2 en (to_proc_input f) ∧ (run_scfg cfg O2 target_alloc_limit en (to_proc_input f)).bh_unmodeled)
                ↔ (∃ en, valid_entry P2 en (to_proc_input f) ∧ (run_scfg cfg P2 target_alloc_limit en (to_proc_input f)).bh_unmodeled)))))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- The forced-only classifier decides configured error-freedom and trace equality. The input declares RV64GC.
model: `classifies_good_inputs_T_s_hwcap_rv64gc` expanded into configured behaviors and verdicts. -/
theorem classifies_good_inputs_T_s_hwcap_rv64gc_iff (cfg : SpuriousCfg) (O1 O2 C : Image) :
    classifies_good_inputs_T_s_hwcap_rv64gc cfg O1 O2 C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      (to_proc_input f).in_hwcap = hwcap_rv64gc →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (∀ en1 en2, valid_entry O1 en1 (to_proc_input f) → valid_entry O2 en2 (to_proc_input f) →
              (¬ (run_scfg cfg O1 source_alloc_limit en1 (to_proc_input f)).bh_errors)
              ∧ (¬ (run_scfg cfg O2 target_alloc_limit en2 (to_proc_input f)).bh_errors)
              ∧ (∀ tr, (run_scfg cfg O1 source_alloc_limit en1 (to_proc_input f)).bh_traces tr ↔
                  (run_scfg cfg O2 target_alloc_limit en2 (to_proc_input f)).bh_traces tr)))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- The forced-only classifier decides configured error-freedom and trace equality. The input declares RV64GCV.
model: `classifies_good_inputs_T_s_hwcap_rv64gcv` expanded into configured behaviors and verdicts. -/
theorem classifies_good_inputs_T_s_hwcap_rv64gcv_iff (cfg : SpuriousCfg) (O1 O2 C : Image) :
    classifies_good_inputs_T_s_hwcap_rv64gcv cfg O1 O2 C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      (to_proc_input f).in_hwcap = hwcap_rv64gcv →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (∀ en1 en2, valid_entry O1 en1 (to_proc_input f) → valid_entry O2 en2 (to_proc_input f) →
              (¬ (run_scfg cfg O1 source_alloc_limit en1 (to_proc_input f)).bh_errors)
              ∧ (¬ (run_scfg cfg O2 target_alloc_limit en2 (to_proc_input f)).bh_errors)
              ∧ (∀ tr, (run_scfg cfg O1 source_alloc_limit en1 (to_proc_input f)).bh_traces tr ↔
                  (run_scfg cfg O2 target_alloc_limit en2 (to_proc_input f)).bh_traces tr)))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- Forced-only acceptance requires exit zero at every valid entry.
model: `accepts_fo` expanded into entry quantifiers and verdicts. -/
theorem accepts_fo_iff (C : Image) (f : FinProcInput) :
    accepts_fo C f ↔
    ∀ en, valid_entry C en (to_proc_input f) →
      must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) := Iff.rfl

/-- Forced-only rejection is validity together with failure of universal acceptance.
model: `rejects_fo` expanded into entry quantifiers and verdicts. -/
theorem rejects_fo_iff (C : Image) (f : FinProcInput) :
    rejects_fo C f ↔ valid_fin_input f ∧
      ¬ (∀ en, valid_entry C en (to_proc_input f) →
        must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- Classifier decidability asks the filter question on each valid finite input and entry.
model: `classifier_decided` and `classifier_alloc_limit`. -/
theorem classifier_decided_iff (C : Image) :
    classifier_decided C ↔
    ∀ f en, valid_fin_input f → valid_entry C en (to_proc_input f) →
      run_decided forced_only_cfg C target_alloc_limit en (to_proc_input f) := Iff.rfl

/-- Configured error-freedom excludes source errors at every valid entry.
model: `error_free_input_s` expanded into configured behaviors and verdicts. -/
theorem error_free_input_s_iff (cfg : SpuriousCfg) (O : Image) (inp : ProcInput) :
    error_free_input_s cfg O inp ↔
    ∀ enO, valid_entry O enO inp → ¬ (run_scfg cfg O source_alloc_limit enO inp).bh_errors := Iff.rfl

/-- The forced-only classifier decides source error-freedom at every valid entry.
model: `classifies_error_free_inputs_T_s` expanded into configured behaviors and verdicts. -/
theorem classifies_error_free_inputs_T_s_iff (cfg : SpuriousCfg) (O C : Image) :
    classifies_error_free_inputs_T_s cfg O C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (∀ enO, valid_entry O enO (to_proc_input f) → ¬ (run_scfg cfg O source_alloc_limit enO (to_proc_input f)).bh_errors))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- The forced-only classifier decides source error-freedom at every valid entry.
model: `classifies_error_free_inputs_T_fo` expanded into entry quantifiers and verdicts. -/
theorem classifies_error_free_inputs_T_fo_iff (O C : Image) :
    classifies_error_free_inputs_T_fo O C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (∀ enO, valid_entry O enO (to_proc_input f) → ¬ (run O source_alloc_limit enO (to_proc_input f)).bh_errors))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- The forced-only classifier decides source error-freedom at every valid entry. The input declares RV64GC.
model: `classifies_error_free_inputs_T_s_hwcap_rv64gc` expanded into configured behaviors and verdicts. -/
theorem classifies_error_free_inputs_T_s_hwcap_rv64gc_iff (cfg : SpuriousCfg) (O C : Image) :
    classifies_error_free_inputs_T_s_hwcap_rv64gc cfg O C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      (to_proc_input f).in_hwcap = hwcap_rv64gc →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (∀ enO, valid_entry O enO (to_proc_input f) → ¬ (run_scfg cfg O source_alloc_limit enO (to_proc_input f)).bh_errors))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- The forced-only classifier decides source error-freedom at every valid entry. The input declares RV64GCV.
model: `classifies_error_free_inputs_T_s_hwcap_rv64gcv` expanded into configured behaviors and verdicts. -/
theorem classifies_error_free_inputs_T_s_hwcap_rv64gcv_iff (cfg : SpuriousCfg) (O C : Image) :
    classifies_error_free_inputs_T_s_hwcap_rv64gcv cfg O C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      (to_proc_input f).in_hwcap = hwcap_rv64gcv →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (∀ enO, valid_entry O enO (to_proc_input f) → ¬ (run_scfg cfg O source_alloc_limit enO (to_proc_input f)).bh_errors))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- The forced-only classifier decides source error-freedom at every valid entry. The input declares RV64GC.
model: `classifies_error_free_inputs_T_fo_hwcap_rv64gc` expanded into entry quantifiers and verdicts. -/
theorem classifies_error_free_inputs_T_fo_hwcap_rv64gc_iff (O C : Image) :
    classifies_error_free_inputs_T_fo_hwcap_rv64gc O C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      (to_proc_input f).in_hwcap = hwcap_rv64gc →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (∀ enO, valid_entry O enO (to_proc_input f) → ¬ (run O source_alloc_limit enO (to_proc_input f)).bh_errors))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- The forced-only classifier decides source error-freedom at every valid entry. The input declares RV64GCV.
model: `classifies_error_free_inputs_T_fo_hwcap_rv64gcv` expanded into entry quantifiers and verdicts. -/
theorem classifies_error_free_inputs_T_fo_hwcap_rv64gcv_iff (O C : Image) :
    classifies_error_free_inputs_T_fo_hwcap_rv64gcv O C ↔
    ∀ f : FinProcInput, valid_fin_input f →
      (to_proc_input f).in_hwcap = hwcap_rv64gcv →
      ∀ en, valid_entry C en (to_proc_input f) →
        (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f) ↔
          (∀ enO, valid_entry O enO (to_proc_input f) → ¬ (run O source_alloc_limit enO (to_proc_input f)).bh_errors))
        ∧ (must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) C target_alloc_limit en (to_proc_input f)
          ∨ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) C target_alloc_limit en (to_proc_input f)) := Iff.rfl

/-- The concrete launch declares RV64GC in its capability field.
model: `launch`, `FinProcInput.fin_hwcap`, and `hwcap_rv64gc`. -/
def classifier_launch_rv64gc : FinProcInput :=
  { launch with fin_hwcap := hwcap_rv64gc }

/-- The RV64GC launch satisfies every finite-input clause.
model: `valid_fin_input`, `valid_input`, and `stream_of_list_then_infinite`. -/
theorem classifier_launch_rv64gc_valid : valid_fin_input classifier_launch_rv64gc := by
  unfold valid_fin_input valid_input
  repeat' with_reducible apply And.intro
  all_goals first
    | (simp only [valid_argv, valid_envp, Fs.valid_fs, valid_creds, valid_id,
        valid_nofile, valid_sigmask, valid_hwcap]
       set_option maxRecDepth 32768 in decide)
    | rfl
    | -- `Fs.fs_keys_relative` on the fixture's empty image; a bounded ∀ over
      -- a `match`-defined Prop, so `decide` finds no instance for it.
      (unfold Fs.fs_keys_relative; intro pf hpf; cases hpf)
    | exact stream_of_list_then_infinite _ _ default_urandom_infinite
    | fail "valid_fin_input: a clause matched none of the shapes"

/-- The undecodable image has a valid entry at the RV64GC launch.
model: `undecodable_entry_valid` and `classifier_launch_rv64gc_valid`. -/
theorem classifier_launch_rv64gc_entry :
    valid_entry undecodable_image demo_entry (to_proc_input classifier_launch_rv64gc) := undecodable_entry_valid _
      (valid_input_va_size _ classifier_launch_rv64gc_valid)
      (valid_input_argv _ classifier_launch_rv64gc_valid) (valid_input_envp _ classifier_launch_rv64gc_valid)

/-- The denoted input preserves the RV64GC capability declaration.
model: `to_proc_input` and `classifier_launch_rv64gc`. -/
theorem classifier_launch_rv64gc_hwcap :
    (to_proc_input classifier_launch_rv64gc).in_hwcap = hwcap_rv64gc := rfl

/-- The concrete launch declares RV64GCV in its capability field.
model: `launch`, `FinProcInput.fin_hwcap`, and `hwcap_rv64gcv`. -/
def classifier_launch_rv64gcv : FinProcInput :=
  { launch with fin_hwcap := hwcap_rv64gcv }

/-- The RV64GCV launch satisfies every finite-input clause.
model: `valid_fin_input`, `valid_input`, and `stream_of_list_then_infinite`. -/
theorem classifier_launch_rv64gcv_valid : valid_fin_input classifier_launch_rv64gcv := by
  unfold valid_fin_input valid_input
  repeat' with_reducible apply And.intro
  all_goals first
    | (simp only [valid_argv, valid_envp, Fs.valid_fs, valid_creds, valid_id,
        valid_nofile, valid_sigmask, valid_hwcap]
       set_option maxRecDepth 32768 in decide)
    | rfl
    | -- `Fs.fs_keys_relative` on the fixture's empty image; a bounded ∀ over
      -- a `match`-defined Prop, so `decide` finds no instance for it.
      (unfold Fs.fs_keys_relative; intro pf hpf; cases hpf)
    | exact stream_of_list_then_infinite _ _ default_urandom_infinite
    | fail "valid_fin_input: a clause matched none of the shapes"

/-- The undecodable image has a valid entry at the RV64GCV launch.
model: `undecodable_entry_valid` and `classifier_launch_rv64gcv_valid`. -/
theorem classifier_launch_rv64gcv_entry :
    valid_entry undecodable_image demo_entry (to_proc_input classifier_launch_rv64gcv) := undecodable_entry_valid _
      (valid_input_va_size _ classifier_launch_rv64gcv_valid)
      (valid_input_argv _ classifier_launch_rv64gcv_valid) (valid_input_envp _ classifier_launch_rv64gcv_valid)

/-- The denoted input preserves the RV64GCV capability declaration.
model: `to_proc_input` and `classifier_launch_rv64gcv`. -/
theorem classifier_launch_rv64gcv_hwcap :
    (to_proc_input classifier_launch_rv64gcv).in_hwcap = hwcap_rv64gcv := rfl

/-- Two entry-less images agree under forced-only on the concrete launch.
model: `agree_s` and `brk_unplaceable_image_has_no_entry`. -/
theorem agree_s_accept :
    agree_s forced_only_cfg brk_unplaceable_image brk_unplaceable_image
      source_alloc_limit (to_proc_input launch) := by
  have hn := fun en => brk_unplaceable_image_has_no_entry en (to_proc_input launch)
  refine ⟨fun ex _ hx _ => (hn ex hx).elim, ?_, ?_, ?_⟩
  all_goals exact ⟨fun ⟨en, hen, _⟩ => (hn en hen).elim,
    fun ⟨en, hen, _⟩ => (hn en hen).elim⟩

/-- The undecodable configured run disagrees with the entry-less image on coverage.
model: `agree_s`, `classifier_launch_entry`, and `undecodable_run_scfg_unmodeled`. -/
theorem agree_s_refute :
    ¬ agree_s forced_only_cfg undecodable_image brk_unplaceable_image
      source_alloc_limit (to_proc_input launch) := by
  intro h
  obtain ⟨en, hen, _⟩ := h.2.2.2.mp
    ⟨demo_entry, classifier_launch_entry, undecodable_run_scfg_unmodeled _ _ _⟩
  exact brk_unplaceable_image_has_no_entry en _ hen

/-- An entry-less second image makes the concrete input good under forced-only.
model: `good_input_s` and `brk_unplaceable_image_has_no_entry`. -/
theorem good_input_s_accept :
    good_input_s forced_only_cfg undecodable_image brk_unplaceable_image (to_proc_input launch) := fun _ en _ hen => (brk_unplaceable_image_has_no_entry en _ hen).elim

/-- The undecodable original is not good against itself under forced-only.
model: `good_input_s_refuted_by_source_error`, `run_scfg_unmodeled_errors`, and `undecodable_run_scfg_unmodeled`. -/
theorem good_input_s_refute :
    ¬ good_input_s forced_only_cfg undecodable_image undecodable_image (to_proc_input launch) := good_input_s_refuted_by_source_error _ _ _ _ demo_entry demo_entry
      classifier_launch_entry classifier_launch_entry
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _))

/-- The entry-less original is error-free under forced-only at the concrete launch.
model: `error_free_input_s_vacuous_no_entries` and `brk_unplaceable_image_has_no_entry`. -/
theorem error_free_input_s_accept :
    error_free_input_s forced_only_cfg brk_unplaceable_image (to_proc_input launch) := error_free_input_s_vacuous_no_entries _ _ _ (fun en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable original is not error-free under forced-only at the concrete launch.
model: `error_free_input_s_refuted_by_error`, `run_scfg_unmodeled_errors`, and `undecodable_run_scfg_unmodeled`. -/
theorem error_free_input_s_refute :
    ¬ error_free_input_s forced_only_cfg undecodable_image (to_proc_input launch) := error_free_input_s_refuted_by_error _ _ _ demo_entry classifier_launch_entry
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _))

/-- The entry-less classifier accepts the launch under forced-only.
model: `accepts_fo_vacuous_no_entries` and `brk_unplaceable_image_has_no_entry`. -/
theorem accepts_fo_accept : accepts_fo brk_unplaceable_image launch := accepts_fo_vacuous_no_entries _ _ (fun en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable classifier does not accept the concrete launch under forced-only.
model: `accepts_fo_refuted_by_entry`, `must_exit_with_scfg_refuted_by_error`, and `undecodable_run_scfg_unmodeled`. -/
theorem accepts_fo_refute : ¬ accepts_fo undecodable_image launch := accepts_fo_refuted_by_entry _ _ demo_entry classifier_launch_entry
    (must_exit_with_scfg_refuted_by_error _ _ _ _ _ _
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _)))

/-- The undecodable classifier rejects the valid concrete launch under forced-only.
model: `launch_is_valid` and `accepts_fo_refute`. -/
theorem rejects_fo_accept : rejects_fo undecodable_image launch := ⟨launch_is_valid, accepts_fo_refute⟩

/-- The entry-less classifier does not reject the concrete launch under forced-only.
model: `rejects_fo` and `accepts_fo_accept`. -/
theorem rejects_fo_refute : ¬ rejects_fo brk_unplaceable_image launch := fun h => h.2 accepts_fo_accept

/-- The entry-less classifier satisfies forced-only totality.
model: `classifier_total_T_fo_vacuous_no_entries` and `brk_unplaceable_image_has_no_entry`. -/
theorem classifier_total_T_fo_accept : classifier_total_T_fo brk_unplaceable_image := classifier_total_T_fo_vacuous_no_entries _ (fun _ en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable classifier fails forced-only totality on the concrete launch.
model: `classifier_total_T_fo_refuted_by_undecided`, `must_exit_with_scfg_refuted_by_error`, and `undecodable_run_scfg_unmodeled`. -/
theorem classifier_total_T_fo_refute : ¬ classifier_total_T_fo undecodable_image := classifier_total_T_fo_refuted_by_undecided _ launch demo_entry launch_is_valid
    classifier_launch_entry
    (must_exit_with_scfg_refuted_by_error _ _ _ _ _ _
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _)))
    (must_exit_with_scfg_refuted_by_error _ _ _ _ _ _
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _)))

/-- The entry-less classifier satisfies this obligation for the concrete originals.
model: `decides_fo`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem decides_fo_accept :
    decides_fo brk_unplaceable_image (fun _ => False) := decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable classifier fails this obligation at the concrete launch.
model: `decides_fo_implies_total` and `classifier_total_T_fo_refute`. -/
theorem decides_fo_refute :
    ¬ decides_fo undecodable_image (fun _ => False) := fun h => classifier_total_T_fo_refute (decides_fo_implies_total _ _ h)

/-- The entry-less classifier satisfies this declared obligation for the concrete originals.
model: `decides_fo_hwcap_rv64gc`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem decides_fo_hwcap_rv64gc_accept :
    decides_fo_hwcap_rv64gc brk_unplaceable_image (fun _ => False) := decides_fo_hwcap_rv64gc_of_decides_fo _ _ (decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _))

/-- The undecodable classifier fails this obligation at the concrete RV64GC launch.
model: `classifier_launch_rv64gc_valid`, `classifier_launch_rv64gc_hwcap`, `classifier_launch_rv64gc_entry`, and `undecodable_run_scfg_unmodeled`. -/
theorem decides_fo_hwcap_rv64gc_refute :
    ¬ decides_fo_hwcap_rv64gc undecodable_image (fun _ => False) := by
  intro h
  have ht := (h classifier_launch_rv64gc classifier_launch_rv64gc_valid classifier_launch_rv64gc_hwcap demo_entry classifier_launch_rv64gc_entry).2
  have hn (code : word) :
      ¬ must_exit_with_scfg forced_only_cfg code undecodable_image classifier_alloc_limit
        demo_entry (to_proc_input classifier_launch_rv64gc) :=
    must_exit_with_scfg_refuted_by_error _ _ _ _ _ _
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _))
  exact ht.elim (hn verdict_accept) (hn verdict_reject)

/-- The entry-less classifier satisfies this declared obligation for the concrete originals.
model: `decides_fo_hwcap_rv64gcv`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem decides_fo_hwcap_rv64gcv_accept :
    decides_fo_hwcap_rv64gcv brk_unplaceable_image (fun _ => False) := decides_fo_hwcap_rv64gcv_of_decides_fo _ _ (decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _))

/-- The undecodable classifier fails this obligation at the concrete RV64GCV launch.
model: `classifier_launch_rv64gcv_valid`, `classifier_launch_rv64gcv_hwcap`, `classifier_launch_rv64gcv_entry`, and `undecodable_run_scfg_unmodeled`. -/
theorem decides_fo_hwcap_rv64gcv_refute :
    ¬ decides_fo_hwcap_rv64gcv undecodable_image (fun _ => False) := by
  intro h
  have ht := (h classifier_launch_rv64gcv classifier_launch_rv64gcv_valid classifier_launch_rv64gcv_hwcap demo_entry classifier_launch_rv64gcv_entry).2
  have hn (code : word) :
      ¬ must_exit_with_scfg forced_only_cfg code undecodable_image classifier_alloc_limit
        demo_entry (to_proc_input classifier_launch_rv64gcv) :=
    must_exit_with_scfg_refuted_by_error _ _ _ _ _ _
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _))
  exact ht.elim (hn verdict_accept) (hn verdict_reject)

/-- The entry-less classifier satisfies this obligation for the concrete originals.
model: `classifies_patch_diff_T_s`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_patch_diff_T_s_accept :
    classifies_patch_diff_T_s forced_only_cfg brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image := decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable classifier fails this obligation at the concrete launch.
model: `decides_fo_implies_total` and `classifier_total_T_fo_refute`. -/
theorem classifies_patch_diff_T_s_refute :
    ¬ classifies_patch_diff_T_s forced_only_cfg brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image undecodable_image := fun h => classifier_total_T_fo_refute (decides_fo_implies_total _ _ h)

/-- The entry-less classifier satisfies this declared obligation for the concrete originals.
model: `classifies_patch_diff_T_s_hwcap_rv64gc`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_patch_diff_T_s_hwcap_rv64gc_accept :
    classifies_patch_diff_T_s_hwcap_rv64gc forced_only_cfg brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image := decides_fo_hwcap_rv64gc_of_decides_fo _ _ (decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _))

/-- The undecodable classifier fails this obligation at the concrete RV64GC launch.
model: `classifier_launch_rv64gc_valid`, `classifier_launch_rv64gc_hwcap`, `classifier_launch_rv64gc_entry`, and `undecodable_run_scfg_unmodeled`. -/
theorem classifies_patch_diff_T_s_hwcap_rv64gc_refute :
    ¬ classifies_patch_diff_T_s_hwcap_rv64gc forced_only_cfg brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image undecodable_image := by
  intro h
  have ht := (h classifier_launch_rv64gc classifier_launch_rv64gc_valid classifier_launch_rv64gc_hwcap demo_entry classifier_launch_rv64gc_entry).2
  have hn (code : word) :
      ¬ must_exit_with_scfg forced_only_cfg code undecodable_image classifier_alloc_limit
        demo_entry (to_proc_input classifier_launch_rv64gc) :=
    must_exit_with_scfg_refuted_by_error _ _ _ _ _ _
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _))
  exact ht.elim (hn verdict_accept) (hn verdict_reject)

/-- The entry-less classifier satisfies this declared obligation for the concrete originals.
model: `classifies_patch_diff_T_s_hwcap_rv64gcv`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_patch_diff_T_s_hwcap_rv64gcv_accept :
    classifies_patch_diff_T_s_hwcap_rv64gcv forced_only_cfg brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image := decides_fo_hwcap_rv64gcv_of_decides_fo _ _ (decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _))

/-- The undecodable classifier fails this obligation at the concrete RV64GCV launch.
model: `classifier_launch_rv64gcv_valid`, `classifier_launch_rv64gcv_hwcap`, `classifier_launch_rv64gcv_entry`, and `undecodable_run_scfg_unmodeled`. -/
theorem classifies_patch_diff_T_s_hwcap_rv64gcv_refute :
    ¬ classifies_patch_diff_T_s_hwcap_rv64gcv forced_only_cfg brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image undecodable_image := by
  intro h
  have ht := (h classifier_launch_rv64gcv classifier_launch_rv64gcv_valid classifier_launch_rv64gcv_hwcap demo_entry classifier_launch_rv64gcv_entry).2
  have hn (code : word) :
      ¬ must_exit_with_scfg forced_only_cfg code undecodable_image classifier_alloc_limit
        demo_entry (to_proc_input classifier_launch_rv64gcv) :=
    must_exit_with_scfg_refuted_by_error _ _ _ _ _ _
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _))
  exact ht.elim (hn verdict_accept) (hn verdict_reject)

/-- The entry-less classifier satisfies this obligation for the concrete originals.
model: `classifies_good_inputs_T_s`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_good_inputs_T_s_accept :
    classifies_good_inputs_T_s forced_only_cfg brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image := decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable classifier fails this obligation at the concrete launch.
model: `decides_fo_implies_total` and `classifier_total_T_fo_refute`. -/
theorem classifies_good_inputs_T_s_refute :
    ¬ classifies_good_inputs_T_s forced_only_cfg brk_unplaceable_image brk_unplaceable_image undecodable_image := fun h => classifier_total_T_fo_refute (decides_fo_implies_total _ _ h)

/-- The entry-less classifier satisfies this declared obligation for the concrete originals.
model: `classifies_good_inputs_T_s_hwcap_rv64gc`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_good_inputs_T_s_hwcap_rv64gc_accept :
    classifies_good_inputs_T_s_hwcap_rv64gc forced_only_cfg brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image := decides_fo_hwcap_rv64gc_of_decides_fo _ _ (decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _))

/-- The undecodable classifier fails this obligation at the concrete RV64GC launch.
model: `classifier_launch_rv64gc_valid`, `classifier_launch_rv64gc_hwcap`, `classifier_launch_rv64gc_entry`, and `undecodable_run_scfg_unmodeled`. -/
theorem classifies_good_inputs_T_s_hwcap_rv64gc_refute :
    ¬ classifies_good_inputs_T_s_hwcap_rv64gc forced_only_cfg brk_unplaceable_image brk_unplaceable_image undecodable_image := by
  intro h
  have ht := (h classifier_launch_rv64gc classifier_launch_rv64gc_valid classifier_launch_rv64gc_hwcap demo_entry classifier_launch_rv64gc_entry).2
  have hn (code : word) :
      ¬ must_exit_with_scfg forced_only_cfg code undecodable_image classifier_alloc_limit
        demo_entry (to_proc_input classifier_launch_rv64gc) :=
    must_exit_with_scfg_refuted_by_error _ _ _ _ _ _
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _))
  exact ht.elim (hn verdict_accept) (hn verdict_reject)

/-- The entry-less classifier satisfies this declared obligation for the concrete originals.
model: `classifies_good_inputs_T_s_hwcap_rv64gcv`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_good_inputs_T_s_hwcap_rv64gcv_accept :
    classifies_good_inputs_T_s_hwcap_rv64gcv forced_only_cfg brk_unplaceable_image brk_unplaceable_image brk_unplaceable_image := decides_fo_hwcap_rv64gcv_of_decides_fo _ _ (decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _))

/-- The undecodable classifier fails this obligation at the concrete RV64GCV launch.
model: `classifier_launch_rv64gcv_valid`, `classifier_launch_rv64gcv_hwcap`, `classifier_launch_rv64gcv_entry`, and `undecodable_run_scfg_unmodeled`. -/
theorem classifies_good_inputs_T_s_hwcap_rv64gcv_refute :
    ¬ classifies_good_inputs_T_s_hwcap_rv64gcv forced_only_cfg brk_unplaceable_image brk_unplaceable_image undecodable_image := by
  intro h
  have ht := (h classifier_launch_rv64gcv classifier_launch_rv64gcv_valid classifier_launch_rv64gcv_hwcap demo_entry classifier_launch_rv64gcv_entry).2
  have hn (code : word) :
      ¬ must_exit_with_scfg forced_only_cfg code undecodable_image classifier_alloc_limit
        demo_entry (to_proc_input classifier_launch_rv64gcv) :=
    must_exit_with_scfg_refuted_by_error _ _ _ _ _ _
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _))
  exact ht.elim (hn verdict_accept) (hn verdict_reject)

/-- The entry-less classifier satisfies this obligation for the concrete originals.
model: `classifies_error_free_inputs_T_s`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_error_free_inputs_T_s_accept :
    classifies_error_free_inputs_T_s forced_only_cfg brk_unplaceable_image brk_unplaceable_image := decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable classifier fails this obligation at the concrete launch.
model: `decides_fo_implies_total` and `classifier_total_T_fo_refute`. -/
theorem classifies_error_free_inputs_T_s_refute :
    ¬ classifies_error_free_inputs_T_s forced_only_cfg brk_unplaceable_image undecodable_image := fun h => classifier_total_T_fo_refute (decides_fo_implies_total _ _ h)

/-- The entry-less classifier satisfies this declared obligation for the concrete originals.
model: `classifies_error_free_inputs_T_s_hwcap_rv64gc`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_error_free_inputs_T_s_hwcap_rv64gc_accept :
    classifies_error_free_inputs_T_s_hwcap_rv64gc forced_only_cfg brk_unplaceable_image brk_unplaceable_image := decides_fo_hwcap_rv64gc_of_decides_fo _ _ (decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _))

/-- The undecodable classifier fails this obligation at the concrete RV64GC launch.
model: `classifier_launch_rv64gc_valid`, `classifier_launch_rv64gc_hwcap`, `classifier_launch_rv64gc_entry`, and `undecodable_run_scfg_unmodeled`. -/
theorem classifies_error_free_inputs_T_s_hwcap_rv64gc_refute :
    ¬ classifies_error_free_inputs_T_s_hwcap_rv64gc forced_only_cfg brk_unplaceable_image undecodable_image := by
  intro h
  have ht := (h classifier_launch_rv64gc classifier_launch_rv64gc_valid classifier_launch_rv64gc_hwcap demo_entry classifier_launch_rv64gc_entry).2
  have hn (code : word) :
      ¬ must_exit_with_scfg forced_only_cfg code undecodable_image classifier_alloc_limit
        demo_entry (to_proc_input classifier_launch_rv64gc) :=
    must_exit_with_scfg_refuted_by_error _ _ _ _ _ _
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _))
  exact ht.elim (hn verdict_accept) (hn verdict_reject)

/-- The entry-less classifier satisfies this declared obligation for the concrete originals.
model: `classifies_error_free_inputs_T_s_hwcap_rv64gcv`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_error_free_inputs_T_s_hwcap_rv64gcv_accept :
    classifies_error_free_inputs_T_s_hwcap_rv64gcv forced_only_cfg brk_unplaceable_image brk_unplaceable_image := decides_fo_hwcap_rv64gcv_of_decides_fo _ _ (decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _))

/-- The undecodable classifier fails this obligation at the concrete RV64GCV launch.
model: `classifier_launch_rv64gcv_valid`, `classifier_launch_rv64gcv_hwcap`, `classifier_launch_rv64gcv_entry`, and `undecodable_run_scfg_unmodeled`. -/
theorem classifies_error_free_inputs_T_s_hwcap_rv64gcv_refute :
    ¬ classifies_error_free_inputs_T_s_hwcap_rv64gcv forced_only_cfg brk_unplaceable_image undecodable_image := by
  intro h
  have ht := (h classifier_launch_rv64gcv classifier_launch_rv64gcv_valid classifier_launch_rv64gcv_hwcap demo_entry classifier_launch_rv64gcv_entry).2
  have hn (code : word) :
      ¬ must_exit_with_scfg forced_only_cfg code undecodable_image classifier_alloc_limit
        demo_entry (to_proc_input classifier_launch_rv64gcv) :=
    must_exit_with_scfg_refuted_by_error _ _ _ _ _ _
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _))
  exact ht.elim (hn verdict_accept) (hn verdict_reject)

/-- The entry-less classifier satisfies this obligation for the concrete originals.
model: `classifies_error_free_inputs_T_fo`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_error_free_inputs_T_fo_accept :
    classifies_error_free_inputs_T_fo brk_unplaceable_image brk_unplaceable_image := decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _)

/-- The undecodable classifier fails this obligation at the concrete launch.
model: `decides_fo_implies_total` and `classifier_total_T_fo_refute`. -/
theorem classifies_error_free_inputs_T_fo_refute :
    ¬ classifies_error_free_inputs_T_fo brk_unplaceable_image undecodable_image := fun h => classifier_total_T_fo_refute (decides_fo_implies_total _ _ h)

/-- The entry-less classifier satisfies this declared obligation for the concrete originals.
model: `classifies_error_free_inputs_T_fo_hwcap_rv64gc`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_error_free_inputs_T_fo_hwcap_rv64gc_accept :
    classifies_error_free_inputs_T_fo_hwcap_rv64gc brk_unplaceable_image brk_unplaceable_image := decides_fo_hwcap_rv64gc_of_decides_fo _ _ (decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _))

/-- The undecodable classifier fails this obligation at the concrete RV64GC launch.
model: `classifier_launch_rv64gc_valid`, `classifier_launch_rv64gc_hwcap`, `classifier_launch_rv64gc_entry`, and `undecodable_run_scfg_unmodeled`. -/
theorem classifies_error_free_inputs_T_fo_hwcap_rv64gc_refute :
    ¬ classifies_error_free_inputs_T_fo_hwcap_rv64gc brk_unplaceable_image undecodable_image := by
  intro h
  have ht := (h classifier_launch_rv64gc classifier_launch_rv64gc_valid classifier_launch_rv64gc_hwcap demo_entry classifier_launch_rv64gc_entry).2
  have hn (code : word) :
      ¬ must_exit_with_scfg forced_only_cfg code undecodable_image classifier_alloc_limit
        demo_entry (to_proc_input classifier_launch_rv64gc) :=
    must_exit_with_scfg_refuted_by_error _ _ _ _ _ _
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _))
  exact ht.elim (hn verdict_accept) (hn verdict_reject)

/-- The entry-less classifier satisfies this declared obligation for the concrete originals.
model: `classifies_error_free_inputs_T_fo_hwcap_rv64gcv`, `decides_fo_vacuous_no_entries`, and `brk_unplaceable_image_has_no_entry`. -/
theorem classifies_error_free_inputs_T_fo_hwcap_rv64gcv_accept :
    classifies_error_free_inputs_T_fo_hwcap_rv64gcv brk_unplaceable_image brk_unplaceable_image := decides_fo_hwcap_rv64gcv_of_decides_fo _ _ (decides_fo_vacuous_no_entries _ _ (fun _ en => brk_unplaceable_image_has_no_entry en _))

/-- The undecodable classifier fails this obligation at the concrete RV64GCV launch.
model: `classifier_launch_rv64gcv_valid`, `classifier_launch_rv64gcv_hwcap`, `classifier_launch_rv64gcv_entry`, and `undecodable_run_scfg_unmodeled`. -/
theorem classifies_error_free_inputs_T_fo_hwcap_rv64gcv_refute :
    ¬ classifies_error_free_inputs_T_fo_hwcap_rv64gcv brk_unplaceable_image undecodable_image := by
  intro h
  have ht := (h classifier_launch_rv64gcv classifier_launch_rv64gcv_valid classifier_launch_rv64gcv_hwcap demo_entry classifier_launch_rv64gcv_entry).2
  have hn (code : word) :
      ¬ must_exit_with_scfg forced_only_cfg code undecodable_image classifier_alloc_limit
        demo_entry (to_proc_input classifier_launch_rv64gcv) :=
    must_exit_with_scfg_refuted_by_error _ _ _ _ _ _
      (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _))
  exact ht.elim (hn verdict_accept) (hn verdict_reject)

/-- The filter question is answered even for the undecodable classifier.
model: `classifier_decided`, `run_decided`, `decided_from`, and `refusal_decided_classical`. -/
theorem classifier_decided_accept : classifier_decided undecodable_image := fun _ _ _ _ => fun _ _ _ _ _ =>
    LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Run.refusal_decided_classical _ _ _

/-- Filter decidability alone does not make the concrete undecodable classifier terminate.
model: `classifier_decided_accept` and `classifier_total_T_fo_refute`; `refusal_decided_classical` rules out a negated decidability instance. -/
theorem classifier_decided_refute :
    ¬ (classifier_decided undecodable_image → classifier_total_T_fo undecodable_image) := fun h => classifier_total_T_fo_refute (h classifier_decided_accept)

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Classifier
