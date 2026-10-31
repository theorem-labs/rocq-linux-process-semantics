import LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed
import LinuxProcessSemantics.LinuxProcessSem.Checks.Omni
import LinuxProcessSemantics.LinuxProcessSem.Checks.SpuriousCfg
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Equivalence

/-! # Checks.Cases.EquivalenceDefinition.HaltsAllowed — allowed-exit statements

Not part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.HaltsAllowed

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.Classifier
open LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Equivalence
  (undecodable_entry_valid undecodable_run_unmodeled undecodable_run_scfg_unmodeled
   undecodable_within_budget_scfg)

/-! ## A-HaltsAllowed: the allowed-exit statements -/

/-- The singleton statement quantifies the single-code judgment over valid launches.
model: `MustExit.must_exit_in_singleton` identifies the two judgments at each launch.
-/
theorem halts_allowed_T_singleton_iff (code : word) (img : Image) :
    halts_allowed_T [code] img ↔
      ∀ en inp, valid_entry img en inp → valid_input inp →
        must_exit_with code img source_alloc_limit en inp :=
  ⟨fun h en inp he hi => (must_exit_in_singleton _ _ _ _ _).1 (h en inp he hi),
   fun h en inp he hi => (must_exit_in_singleton _ _ _ _ _).2 (h en inp he hi)⟩

/-- The configured singleton quantifies the configured single-code judgment.
model: `MustExit.must_exit_in_scfg_singleton` identifies the configured judgments.
-/
theorem halts_allowed_T_scfg_singleton_iff (cfg : SpuriousCfg) (code : word) (img : Image) :
    halts_allowed_T_scfg cfg [code] img ↔
      ∀ en inp, valid_entry img en inp → valid_input inp →
        must_exit_with_scfg cfg code img source_alloc_limit en inp :=
  ⟨fun h en inp he hi => (must_exit_in_scfg_singleton _ _ _ _ _ _).1 (h en inp he hi),
   fun h en inp he hi => (must_exit_in_scfg_singleton _ _ _ _ _ _).2 (h en inp he hi)⟩

/-- The budget singleton retains the configured budget premise at the declared limit.
model: `MustExit.must_exit_in_scfg_singleton` identifies the judgments under `source_within_budget_scfg`.
-/
theorem halts_allowed_T_scfg_budgets_singleton_iff (cfg : SpuriousCfg) (lim : Int)
    (code : word) (img : Image) :
    halts_allowed_T_scfg_budgets cfg lim [code] img ↔
      ∀ en inp, valid_entry img en inp → valid_input inp →
        source_within_budget_scfg cfg lim img en inp →
        must_exit_with_scfg cfg code img lim en inp :=
  ⟨fun h en inp he hi hb => (must_exit_in_scfg_singleton _ _ _ _ _ _).1 (h en inp he hi hb),
   fun h en inp he hi hb => (must_exit_in_scfg_singleton _ _ _ _ _ _).2 (h en inp he hi hb)⟩

/-- The exit-0 fixture exits at the supplied placement, budget and input.
model: `Checks.Examples.exits_c_must_exit_at` consumes `Checks.Omni.exit0_exits_c`.
-/
theorem exit0_must_exit_at_anywhere (sp brk0 mbase : word) (rnd : EntryDraw)
    (lim : Int) (inp : ProcInput) :
    must_exit_at exit0_segments verdict_accept
      (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp) :=
  exits_c_must_exit_at _ _ 8 _ _ rfl rfl (Checks.Omni.exit0_exits_c _ _ _ _ _ _)

/-- ACCEPT: the exit-0 image meets the singleton statement.
model: `MustExit.must_exit_at_in` lifts `exit0_must_exit_at_anywhere` to the allowed set.
-/
theorem exit0_halts_allowed_zero : halts_allowed_T [verdict_accept] exit0_image :=
  fun en inp _ _ => must_exit_at_in _ _ _ _
    (exit0_must_exit_at_anywhere en.en_sp en.en_brk en.en_mmap_base en.en_draw _ inp)
    (List.mem_singleton.mpr rfl)

/-- ACCEPT: widening the allowed set to byte statuses preserves this statement.
model: `HaltsAllowed.halts_allowed_T_mono` uses `status_allowed_In` at `verdict_accept`.
-/
theorem exit0_halts_allowed_any_exit : halts_allowed_T byte_codes exit0_image := by
  apply halts_allowed_T_mono [verdict_accept] byte_codes exit0_image
  · intro code hin
    rw [List.mem_singleton] at hin
    rw [hin]
    exact status_allowed_In _ _ (by decide)
  · exact exit0_halts_allowed_zero

/-- ACCEPT: the exit-0 image meets the forced-only singleton statement.
model: `Checks.SpuriousCfg.exits_c_must_exit_at_cfg` and `MustExit.must_exit_in_at_cfg_singleton` lift `Checks.Omni.exit0_exits_c`.
-/
theorem exit0_halts_allowed_forced_only :
    halts_allowed_T_scfg forced_only_cfg [verdict_accept] exit0_image := by
  intro en inp _ _
  apply (must_exit_in_at_cfg_singleton _ _ _ _).2
  exact Checks.SpuriousCfg.exits_c_must_exit_at_cfg _ _ _ 8 _ _ rfl rfl
    (Checks.Omni.exit0_exits_c _ _ _ _ _ _)

/-- ACCEPT: the exit-0 judgment also holds with the source-budget premise.
model: `exit0_halts_allowed_forced_only` supplies the conclusion of `halts_allowed_T_scfg_budgets`.
-/
theorem exit0_halts_allowed_budgets :
    halts_allowed_T_scfg_budgets forced_only_cfg source_alloc_limit
      [verdict_accept] exit0_image :=
  fun en inp he hi _ => exit0_halts_allowed_forced_only en inp he hi

/-- The configured-to-budget bridge applies to the exit-0 fixture.
model: `HaltsAllowed.halts_allowed_T_scfg_budgets_of_scfg` consumes `exit0_halts_allowed_forced_only`.
-/
theorem exit0_budgets_from_scfg :
    halts_allowed_T_scfg_budgets forced_only_cfg source_alloc_limit
      [verdict_accept] exit0_image :=
  halts_allowed_T_scfg_budgets_of_scfg _ _ _ exit0_halts_allowed_forced_only

/-- The singleton bridge at the exit-0 demo entry preserves the input parameter.
model: an instance of `MustExit.must_exit_in_singleton`.
-/
theorem exit0_singleton_is_must_exit_with (inp : ProcInput) :
    must_exit_in [verdict_accept] exit0_image source_alloc_limit demo_entry inp ↔
      must_exit_with verdict_accept exit0_image source_alloc_limit demo_entry inp :=
  must_exit_in_singleton _ _ _ _ _

/-- Masking 0x1ff produces a member of the byte-status set.
model: `HaltsAllowed.byte_codes` contains the result of `bv_and` with 255.
-/
theorem truncated_status_in_any_exit :
    bv_and (Z_to_bv 64 0x1ff) (Z_to_bv 64 255) ∈ byte_codes := by decide

/-- The classifier's accept and reject statuses belong to the byte-status set.
model: `HaltsAllowed.byte_codes` contains `Classifier.verdict_accept` and `Classifier.verdict_reject`.
-/
theorem verdicts_in_any_exit : verdict_accept ∈ byte_codes ∧ verdict_reject ∈ byte_codes := by
  decide

set_option maxRecDepth 4096 in
/-- The membership computation refuses the word 256.
model: `HaltsAllowed.status_allowed` computes membership in `byte_codes`.
-/
theorem non_byte_not_in_any_exit : status_allowed byte_codes (Z_to_bv 64 256) = false := by
  decide

/-- REFUTE: the undecodable image fails the unconfigured statement for each allowed set.
model: `HaltsAllowed.halts_allowed_T_refuted_by_error` uses `Run.reaches_unmodeled_reaches_error` on `Equivalence.undecodable_run_unmodeled`.
-/
theorem undecodable_image_refutes_halts_allowed (S : List word) :
    ¬ halts_allowed_T S undecodable_image :=
  halts_allowed_T_refuted_by_error _ _ demo_entry demo_proc_input
    (undecodable_entry_valid _ rfl (by unfold valid_argv; decide) (by unfold valid_envp; decide))
    Checks.Omni.demo_input_valid
    (reaches_unmodeled_reaches_error _ _ (undecodable_run_unmodeled _ _))

/-- REFUTE: the first undecodable fetch also refutes the forced-only statement.
model: `MustExit.must_exit_in_scfg_refuted_by_error` and `Run.run_scfg_unmodeled_errors` consume `Equivalence.undecodable_run_scfg_unmodeled`.
-/
theorem undecodable_image_refutes_halts_allowed_forced_only (S : List word) :
    ¬ halts_allowed_T_scfg forced_only_cfg S undecodable_image := by
  intro h
  exact must_exit_in_scfg_refuted_by_error _ _ _ _ demo_entry demo_proc_input
    (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _))
    (h demo_entry demo_proc_input
      (undecodable_entry_valid _ rfl (by unfold valid_argv; decide) (by unfold valid_envp; decide))
      Checks.Omni.demo_input_valid)

/-- REFUTE: the undecodable run meets the budget premise and still errors.
model: `Equivalence.undecodable_within_budget_scfg` excludes budget reachability; `MustExit.must_exit_in_scfg_refuted_by_error` refutes the conclusion.
-/
theorem undecodable_image_refutes_halts_allowed_budgets (S : List word) :
    ¬ halts_allowed_T_scfg_budgets forced_only_cfg source_alloc_limit S undecodable_image := by
  intro h
  exact must_exit_in_scfg_refuted_by_error _ _ _ _ demo_entry demo_proc_input
    (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_run_scfg_unmodeled _ _ _))
    (h demo_entry demo_proc_input
      (undecodable_entry_valid _ rfl (by unfold valid_argv; decide) (by unfold valid_envp; decide))
      Checks.Omni.demo_input_valid (undecodable_within_budget_scfg _ _ _))

/-- A valid break suffices for the demo entry and input.
model: `Run.valid_entry_sv48` reuses the placement from `Equivalence.undecodable_entry_valid`.
-/
theorem demo_entry_valid_of_brk (img : Image)
    (hb : valid_brk img.img_segments demo_entry.en_brk) :
    valid_entry img demo_entry demo_proc_input := by
  rw [valid_entry_sv48 _ _ _ rfl]
  have he := (valid_entry_sv48 _ _ _ rfl).1
    (undecodable_entry_valid demo_proc_input rfl
      (by unfold valid_argv; decide) (by unfold valid_envp; decide))
  exact ⟨he.1, hb, he.2.2⟩

/-- REFUTE: the exit-0 image's realized status is outside the empty allowed set.
model: `MustExit.must_exit_at_realizes` supplies the star consumed by `HaltsAllowed.halts_allowed_T_refuted_by_wrong_status`.
-/
theorem exit0_refutes_halts_allowed_empty : ¬ halts_allowed_T [] exit0_image := by
  obtain ⟨tr, fs, c', hs, hh⟩ := must_exit_at_realizes _ _ _
    (exit0_must_exit_at_anywhere demo_entry.en_sp demo_entry.en_brk
      demo_entry.en_mmap_base demo_entry.en_draw source_alloc_limit demo_proc_input) rfl
  apply halts_allowed_T_refuted_by_wrong_status _ _ demo_entry demo_proc_input
    (tr ++ [ExitEv verdict_accept fs]) c' verdict_accept
  · exact demo_entry_valid_of_brk _ (by unfold valid_brk; decide)
  · exact Checks.Omni.demo_input_valid
  · exact hs
  · exact hh
  · exact List.not_mem_nil

/-- The set form over two codes follows from either single-code claim; the converse is not stated.
model: `MustExit.must_exit_with_in` at each disjunct.
-/
theorem must_exit_in_pair_from_either (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) :
    must_exit_with verdict_accept img lim en inp ∨ must_exit_with verdict_reject img lim en inp →
      must_exit_in [verdict_accept, verdict_reject] img lim en inp := by
  intro h
  rcases h with h | h
  · exact must_exit_with_in _ verdict_accept _ _ _ _ h (by decide)
  · exact must_exit_with_in _ verdict_reject _ _ _ _ h (by decide)

/-- The singleton allowed-set claim implies the claim allowing both verdicts.
model: `MustExit.must_exit_in_mono` widens the singleton to the pair.
-/
theorem must_exit_in_mono_fired (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) :
    must_exit_in [verdict_accept] img lim en inp →
      must_exit_in [verdict_accept, verdict_reject] img lim en inp := by
  apply must_exit_in_mono
  intro code hin
  rw [List.mem_singleton] at hin
  rw [hin]
  decide

/-- REFUTE: the exit-0 image's realized status is outside a non-empty set that omits it.
model: `MustExit.must_exit_at_realizes` supplies the star consumed by `HaltsAllowed.halts_allowed_T_refuted_by_wrong_status`.
-/
theorem exit0_refutes_halts_allowed_reject : ¬ halts_allowed_T [verdict_reject] exit0_image := by
  obtain ⟨tr, fs, c', hs, hh⟩ := must_exit_at_realizes _ _ _
    (exit0_must_exit_at_anywhere demo_entry.en_sp demo_entry.en_brk
      demo_entry.en_mmap_base demo_entry.en_draw source_alloc_limit demo_proc_input) rfl
  apply halts_allowed_T_refuted_by_wrong_status _ _ demo_entry demo_proc_input
    (tr ++ [ExitEv verdict_accept fs]) c' verdict_accept
  · exact demo_entry_valid_of_brk _ (by unfold valid_brk; decide)
  · exact Checks.Omni.demo_input_valid
  · exact hs
  · exact hh
  · decide

/-- The exit-1 image exits with the reject status at every allocation limit.
model: `Checks.Examples.exits_c_must_exit_at` lifts the computed `exits_c` witness.
-/
theorem exit1_must_exit_reject (lim : Int) :
    must_exit_with verdict_reject exit1_image lim demo_entry demo_proc_input := by
  unfold must_exit_with init_config
  apply exits_c_must_exit_at _ _ 8
  · rfl
  · rfl
  · decide +kernel

/-- REFUTE: the image halts cleanly with status 1, outside the allowed set {0}.
model: `MustExit.must_exit_at_realizes` realizes `exit1_must_exit_reject`; `HaltsAllowed.halts_allowed_T_refuted_by_wrong_status` uses `demo_entry_valid_of_brk` and `Checks.Omni.demo_input_valid`.
-/
theorem exit1_refutes_halts_allowed_zero : ¬ halts_allowed_T [verdict_accept] exit1_image := by
  obtain ⟨tr, fs, c', hs, hh⟩ := must_exit_at_realizes _ _ _
    (exit1_must_exit_reject source_alloc_limit) rfl
  apply halts_allowed_T_refuted_by_wrong_status _ _ demo_entry demo_proc_input
    (tr ++ [ExitEv verdict_reject fs]) c' verdict_reject
  · exact demo_entry_valid_of_brk _ (by unfold valid_brk; decide)
  · exact Checks.Omni.demo_input_valid
  · exact hs
  · exact hh
  · decide

/-- ACCEPT: the same image meets the demo-entry judgment at a set admitting its status.
model: `MustExit.must_exit_in_singleton` lifts `exit1_must_exit_reject`.
-/
theorem exit1_halts_allowed_at_reject :
    must_exit_in [verdict_reject] exit1_image source_alloc_limit demo_entry demo_proc_input :=
  (must_exit_in_singleton _ _ _ _ _).2 (exit1_must_exit_reject _)

/-- The unconfigured structure seals precisely its allowed-exit predicate.
model: `HaltsAllowed.SPEC_HALTS_ALLOWED.halts_allowed` and `SPEC_HALTS_ALLOWED.mk` expose and seal the field.
-/
theorem spec_halts_allowed_iff (S : List word) (img : Image) :
    SPEC_HALTS_ALLOWED S img ↔ halts_allowed_T S img :=
  ⟨fun h => h.halts_allowed, fun h => ⟨h⟩⟩

/-- The configured structure seals its configured allowed-exit predicate.
model: `HaltsAllowed.SPEC_HALTS_ALLOWED_SCFG.halts_allowed` and `SPEC_HALTS_ALLOWED_SCFG.mk` expose and seal the field.
-/
theorem spec_halts_allowed_scfg_iff (cfg : SpuriousCfg) (S : List word) (img : Image) :
    SPEC_HALTS_ALLOWED_SCFG cfg S img ↔ halts_allowed_T_scfg cfg S img :=
  ⟨fun h => h.halts_allowed, fun h => ⟨h⟩⟩

/-- The budget structure seals the predicate at the supplied configuration and limit.
model: `HaltsAllowed.SPEC_HALTS_ALLOWED_SCFG_BUDGETS.halts_allowed` and `SPEC_HALTS_ALLOWED_SCFG_BUDGETS.mk` expose and seal the field.
-/
theorem spec_halts_allowed_scfg_budgets_iff (cfg : SpuriousCfg) (lim : Int)
    (S : List word) (img : Image) :
    SPEC_HALTS_ALLOWED_SCFG_BUDGETS cfg lim S img ↔ halts_allowed_T_scfg_budgets cfg lim S img :=
  ⟨fun h => h.halts_allowed, fun h => ⟨h⟩⟩

/-- ACCEPT: the exit-0 singleton statement inhabits the unconfigured structure.
model: `spec_halts_allowed_iff` seals `exit0_halts_allowed_zero`.
-/
theorem exit0_spec_halts_allowed : SPEC_HALTS_ALLOWED [verdict_accept] exit0_image :=
  (spec_halts_allowed_iff _ _).2 exit0_halts_allowed_zero

/-- ACCEPT: the forced-only exit-0 statement inhabits the configured structure.
model: `spec_halts_allowed_scfg_iff` seals `exit0_halts_allowed_forced_only`.
-/
theorem exit0_spec_halts_allowed_scfg :
    SPEC_HALTS_ALLOWED_SCFG forced_only_cfg [verdict_accept] exit0_image :=
  (spec_halts_allowed_scfg_iff _ _ _).2 exit0_halts_allowed_forced_only

/-- ACCEPT: the exit-0 statement inhabits the structure at the shipped source budget.
model: `spec_halts_allowed_scfg_budgets_iff` seals `exit0_halts_allowed_budgets`.
-/
theorem exit0_spec_halts_allowed_scfg_budgets :
    SPEC_HALTS_ALLOWED_SCFG_BUDGETS forced_only_cfg source_alloc_limit [verdict_accept] exit0_image :=
  (spec_halts_allowed_scfg_budgets_iff _ _ _ _).2 exit0_halts_allowed_budgets

/-- ACCEPT: Lean form of Rocq's ascription `Exit0HaltsAllowedChecked`, sealed at AnyExit (`byte_codes`).
model: `spec_halts_allowed_iff` seals `exit0_halts_allowed_any_exit`.
-/
theorem Exit0HaltsAllowedChecked : SPEC_HALTS_ALLOWED byte_codes exit0_image :=
  (spec_halts_allowed_iff _ _).2 exit0_halts_allowed_any_exit

/-- ACCEPT: Lean form of Rocq's ascription `Exit0HaltsAllowedScfgChecked`, sealed at AnyExit (`byte_codes`) and MayFailCfg (`may_fail_cfg`).
model: `spec_halts_allowed_scfg_iff` seals `exit0_halts_allowed_any_exit` via `halts_allowed_T_scfg_may_fail`.
-/
theorem Exit0HaltsAllowedScfgChecked : SPEC_HALTS_ALLOWED_SCFG may_fail_cfg byte_codes exit0_image :=
  (spec_halts_allowed_scfg_iff _ _ _).2
    ((halts_allowed_T_scfg_may_fail _ _).2 exit0_halts_allowed_any_exit)

/-- ACCEPT: Lean form of Rocq's ascription `Exit0HaltsAllowedBudgetsChecked`, sealed at AnyExit (`byte_codes`) and MayFailCfg (`may_fail_cfg`); Rocq's `ShippedBudgets.lim_source` is `source_alloc_limit`.
model: `spec_halts_allowed_scfg_budgets_iff` seals `exit0_halts_allowed_any_exit` via `halts_allowed_T_scfg_may_fail` and `halts_allowed_T_scfg_budgets_of_scfg`.
-/
theorem Exit0HaltsAllowedBudgetsChecked :
    SPEC_HALTS_ALLOWED_SCFG_BUDGETS may_fail_cfg source_alloc_limit byte_codes exit0_image :=
  (spec_halts_allowed_scfg_budgets_iff _ _ _ _).2
    (halts_allowed_T_scfg_budgets_of_scfg _ _ _
      ((halts_allowed_T_scfg_may_fail _ _).2 exit0_halts_allowed_any_exit))

/-- REFUTE: the undecodable image fails the unconfigured sealed statement.
model: `undecodable_image_refutes_halts_allowed` refutes the field exposed by `spec_halts_allowed_iff`.
-/
theorem undecodable_refutes_spec_halts_allowed (S : List word) :
    ¬ SPEC_HALTS_ALLOWED S undecodable_image :=
  fun h => undecodable_image_refutes_halts_allowed S ((spec_halts_allowed_iff _ _).1 h)

/-- REFUTE: the undecodable image fails the forced-only sealed statement.
model: `undecodable_image_refutes_halts_allowed_forced_only` refutes the field exposed by `spec_halts_allowed_scfg_iff`.
-/
theorem undecodable_refutes_spec_halts_allowed_scfg (S : List word) :
    ¬ SPEC_HALTS_ALLOWED_SCFG forced_only_cfg S undecodable_image :=
  fun h => undecodable_image_refutes_halts_allowed_forced_only S
    ((spec_halts_allowed_scfg_iff _ _ _).1 h)

/-- REFUTE: the undecodable image fails the sealed statement at the shipped source budget.
model: `undecodable_image_refutes_halts_allowed_budgets` refutes the field exposed by `spec_halts_allowed_scfg_budgets_iff`.
-/
theorem undecodable_refutes_spec_halts_allowed_scfg_budgets (S : List word) :
    ¬ SPEC_HALTS_ALLOWED_SCFG_BUDGETS forced_only_cfg source_alloc_limit S undecodable_image :=
  fun h => undecodable_image_refutes_halts_allowed_budgets S
    ((spec_halts_allowed_scfg_budgets_iff _ _ _ _).1 h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.HaltsAllowed
