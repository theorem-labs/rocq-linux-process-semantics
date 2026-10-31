import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Base
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ErrorFree

/-! rocq-baseline: 1807c1e25ce12708f5cc85213f2df4bf03d978da -/

/-! Spurious-failure configurations are task parameters: a classifier may
need a forced-refusal reading to reason about a successful input read.
The bridges `strong_universal_T_scfg_may_fail` and
`strong_universal_error_free_T_scfg_may_fail` recover the baseline contracts
propositionally, since the configured step relation is a separate relation.

`error_free_scfg_of_error_free` and `modeled_scfg_of_modeled` carry safety and
coverage to filtered runs. Trace-set comparison and the universal-error
escape need separate reasoning when changing configurations; these contracts
therefore keep the task's configuration explicit. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.Equivalence

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run

/-- The configuration belongs to the task, while entries and allocation
budgets retain their source and target roles. -/
def strong_equiv_scfg (cfg : SpuriousCfg) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  modeled (run_scfg cfg source_image source_alloc_limit en_source inp) ∧
  equiv (run_scfg cfg source_image source_alloc_limit en_source inp)
    (run_scfg cfg target_image target_alloc_limit en_target inp)

/-- Keeping the configuration outside the input quantifier fixes the task's
refusal policy independently of the launch. -/
def strong_universal_T_scfg (cfg : SpuriousCfg) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input inp → strong_equiv_scfg cfg source_image target_image en_source en_target inp

/-- Safety strengthens the comparison without relying on the source-error escape. -/
def strong_equiv_error_free_scfg (cfg : SpuriousCfg) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free (run_scfg cfg source_image source_alloc_limit en_source inp) ∧
  error_free (run_scfg cfg target_image target_alloc_limit en_target inp) ∧
  trace_equiv (run_scfg cfg source_image source_alloc_limit en_source inp).bh_traces
    (run_scfg cfg target_image target_alloc_limit en_target inp).bh_traces

/-- The stronger body still needs inhabited entry premises when used as a task contract. -/
def strong_universal_error_free_T_scfg (cfg : SpuriousCfg) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input inp → strong_equiv_error_free_scfg cfg source_image target_image en_source en_target inp

theorem strong_equiv_error_free_scfg_implies (cfg : SpuriousCfg) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (h : strong_equiv_error_free_scfg cfg source_image target_image en_source en_target inp) :
    strong_equiv_scfg cfg source_image target_image en_source en_target inp :=
  ⟨(fun hu => h.1 (run_scfg_unmodeled_errors cfg _ _ _ _ hu)), Or.inr ⟨h.2.2, h.2.1⟩⟩

theorem strong_universal_error_free_T_scfg_implies (cfg : SpuriousCfg) (source_image target_image : Image)
    (h : strong_universal_error_free_T_scfg cfg source_image target_image) :
    strong_universal_T_scfg cfg source_image target_image :=
  fun es et inp hs ht hi => strong_equiv_error_free_scfg_implies cfg _ _ _ _ _ (h es et inp hs ht hi)

/-- Refusal policy and abort stance are independent task choices. -/
def strong_universal_T_scfg_abort (cfg : SpuriousCfg) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort inp → strong_equiv_scfg cfg source_image target_image en_source en_target inp

/-- An unspecified abort stance holds the task to both readings. -/
def strong_universal_T_scfg_either (cfg : SpuriousCfg) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_either inp → strong_equiv_scfg cfg source_image target_image en_source en_target inp

theorem strong_universal_T_scfg_either_splits (cfg : SpuriousCfg) (source_image target_image : Image) :
    strong_universal_T_scfg_either cfg source_image target_image ↔
      strong_universal_T_scfg cfg source_image target_image ∧ strong_universal_T_scfg_abort cfg source_image target_image := by
  constructor
  · intro h
    exact ⟨fun es et inp hs ht hi => h es et inp hs ht (valid_input_either_of_valid_input inp hi),
      fun es et inp hs ht hi => h es et inp hs ht (valid_input_either_of_valid_input_abort inp hi)⟩
  · rintro ⟨hoff, hon⟩ es et inp hs ht hi
    rcases valid_input_either_splits inp hi with hi | hi
    · exact hoff es et inp hs ht hi
    · exact hon es et inp hs ht hi

theorem strong_universal_T_scfg_either_implies (cfg : SpuriousCfg) (source_image target_image : Image)
    (h : strong_universal_T_scfg_either cfg source_image target_image) :
    strong_universal_T_scfg cfg source_image target_image :=
  ((strong_universal_T_scfg_either_splits cfg _ _).1 h).1

theorem strong_universal_T_scfg_either_implies_abort (cfg : SpuriousCfg) (source_image target_image : Image)
    (h : strong_universal_T_scfg_either cfg source_image target_image) :
    strong_universal_T_scfg_abort cfg source_image target_image :=
  ((strong_universal_T_scfg_either_splits cfg _ _).1 h).2

/-- A followed abort need not error, so safety also excludes signal death. -/
def strong_equiv_error_free_scfg_abort (cfg : SpuriousCfg) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free_unkilled (run_scfg cfg source_image source_alloc_limit en_source inp) ∧
  error_free_unkilled (run_scfg cfg target_image target_alloc_limit en_target inp) ∧
  trace_equiv (run_scfg cfg source_image source_alloc_limit en_source inp).bh_traces
    (run_scfg cfg target_image target_alloc_limit en_target inp).bh_traces

/-- The abort-declared input family retains the no-death safety obligation. -/
def strong_universal_error_free_T_scfg_abort (cfg : SpuriousCfg) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort inp → strong_equiv_error_free_scfg_abort cfg source_image target_image en_source en_target inp

/-- The two stances use different safety predicates, which motivates a conjunction. -/
def strong_universal_error_free_T_scfg_either (cfg : SpuriousCfg) (source_image target_image : Image) : Prop :=
  strong_universal_error_free_T_scfg cfg source_image target_image ∧
  strong_universal_error_free_T_scfg_abort cfg source_image target_image

theorem strong_equiv_error_free_scfg_abort_implies (cfg : SpuriousCfg) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (h : strong_equiv_error_free_scfg_abort cfg source_image target_image en_source en_target inp) :
    strong_equiv_scfg cfg source_image target_image en_source en_target inp :=
  ⟨(fun hu => h.1.1 (run_scfg_unmodeled_errors cfg _ _ _ _ hu)), Or.inr ⟨h.2.2, h.2.1.1⟩⟩

theorem strong_universal_error_free_T_scfg_abort_implies (cfg : SpuriousCfg) (source_image target_image : Image)
    (h : strong_universal_error_free_T_scfg_abort cfg source_image target_image) :
    strong_universal_T_scfg_abort cfg source_image target_image :=
  fun es et inp hs ht hi => strong_equiv_error_free_scfg_abort_implies cfg _ _ _ _ _ (h es et inp hs ht hi)

theorem strong_universal_error_free_T_scfg_either_splits (cfg : SpuriousCfg) (source_image target_image : Image) :
    strong_universal_error_free_T_scfg_either cfg source_image target_image ↔
      strong_universal_error_free_T_scfg cfg source_image target_image ∧
      strong_universal_error_free_T_scfg_abort cfg source_image target_image := Iff.rfl

theorem strong_universal_error_free_T_scfg_either_implies (cfg : SpuriousCfg) (source_image target_image : Image)
    (h : strong_universal_error_free_T_scfg_either cfg source_image target_image) :
    strong_universal_error_free_T_scfg cfg source_image target_image := h.1

theorem strong_universal_error_free_T_scfg_either_implies_abort (cfg : SpuriousCfg) (source_image target_image : Image)
    (h : strong_universal_error_free_T_scfg_either cfg source_image target_image) :
    strong_universal_error_free_T_scfg_abort cfg source_image target_image := h.2

/-- A run witness is needed here; a synthetic behavior alone does not refute a task. -/
theorem strong_universal_error_free_T_scfg_abort_refuted_by_abort (cfg : SpuriousCfg) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (hs : valid_entry source_image en_source inp) (ht : valid_entry target_image en_target inp)
    (hi : valid_input_abort inp) (hd : dies_by_signal (run_scfg cfg source_image source_alloc_limit en_source inp)) :
    ¬ strong_universal_error_free_T_scfg_abort cfg source_image target_image :=
  fun h => (h en_source en_target inp hs ht hi).1.2 hd

/-- A valid triple makes the source error a non-vacuous counterexample. -/
theorem strong_universal_error_free_scfg_refuted_by_source_error (cfg : SpuriousCfg) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (hs : valid_entry source_image en_source inp) (ht : valid_entry target_image en_target inp)
    (hi : valid_input inp) (he : (run_scfg cfg source_image source_alloc_limit en_source inp).bh_errors) :
    ¬ strong_universal_error_free_T_scfg cfg source_image target_image :=
  fun h => (h en_source en_target inp hs ht hi).1 he

/-- Transport through behavior equivalence avoids identifying the two step relations by conversion. -/
theorem strong_equiv_scfg_may_fail (s t : Image) (en_s en_t : ExecEntry) (inp : ProcInput) :
    strong_equiv_scfg may_fail_cfg s t en_s en_t inp ↔ strong_equiv s t en_s en_t inp := by
  have hs := run_scfg_may_fail s source_alloc_limit en_s inp
  have ht := run_scfg_may_fail t target_alloc_limit en_t inp
  exact and_congr (modeled_behavior_equiv _ _ hs) (equiv_behavior_equiv _ _ _ _ hs ht)

/-- Transport through behavior equivalence avoids identifying the two step relations by conversion. -/
theorem strong_equiv_error_free_scfg_may_fail (s t : Image) (en_s en_t : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_scfg may_fail_cfg s t en_s en_t inp ↔ strong_equiv_error_free s t en_s en_t inp := by
  have hs := run_scfg_may_fail s source_alloc_limit en_s inp
  have ht := run_scfg_may_fail t target_alloc_limit en_t inp
  exact and_congr (error_free_behavior_equiv _ _ hs)
    (and_congr (error_free_behavior_equiv _ _ ht) (trace_equiv_behavior_equiv _ _ _ _ hs ht))

/-- Transport through behavior equivalence avoids identifying the two step relations by conversion. -/
theorem strong_equiv_error_free_scfg_abort_may_fail (s t : Image) (en_s en_t : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_scfg_abort may_fail_cfg s t en_s en_t inp ↔ strong_equiv_error_free_abort s t en_s en_t inp := by
  have hs := run_scfg_may_fail s source_alloc_limit en_s inp
  have ht := run_scfg_may_fail t target_alloc_limit en_t inp
  exact and_congr (error_free_unkilled_behavior_equiv _ _ hs)
    (and_congr (error_free_unkilled_behavior_equiv _ _ ht) (trace_equiv_behavior_equiv _ _ _ _ hs ht))

theorem strong_universal_T_scfg_may_fail (s t : Image) :
    strong_universal_T_scfg may_fail_cfg s t ↔ strong_universal_T s t :=
  ⟨fun h es et inp hs ht hi => (strong_equiv_scfg_may_fail s t es et inp).1 (h es et inp hs ht hi),
   fun h es et inp hs ht hi => (strong_equiv_scfg_may_fail s t es et inp).2 (h es et inp hs ht hi)⟩

theorem strong_universal_error_free_T_scfg_may_fail (s t : Image) :
    strong_universal_error_free_T_scfg may_fail_cfg s t ↔ strong_universal_error_free_T s t :=
  ⟨fun h es et inp hs ht hi => (strong_equiv_error_free_scfg_may_fail s t es et inp).1 (h es et inp hs ht hi),
   fun h es et inp hs ht hi => (strong_equiv_error_free_scfg_may_fail s t es et inp).2 (h es et inp hs ht hi)⟩

theorem strong_universal_T_scfg_abort_may_fail (s t : Image) :
    strong_universal_T_scfg_abort may_fail_cfg s t ↔ strong_universal_T_abort s t :=
  ⟨fun h es et inp hs ht hi => (strong_equiv_scfg_may_fail s t es et inp).1 (h es et inp hs ht hi),
   fun h es et inp hs ht hi => (strong_equiv_scfg_may_fail s t es et inp).2 (h es et inp hs ht hi)⟩

theorem strong_universal_T_scfg_either_may_fail (s t : Image) :
    strong_universal_T_scfg_either may_fail_cfg s t ↔ strong_universal_T_either s t :=
  ⟨fun h es et inp hs ht hi => (strong_equiv_scfg_may_fail s t es et inp).1 (h es et inp hs ht hi),
   fun h es et inp hs ht hi => (strong_equiv_scfg_may_fail s t es et inp).2 (h es et inp hs ht hi)⟩

theorem strong_universal_error_free_T_scfg_abort_may_fail (s t : Image) :
    strong_universal_error_free_T_scfg_abort may_fail_cfg s t ↔ strong_universal_error_free_T_abort s t :=
  ⟨fun h es et inp hs ht hi => (strong_equiv_error_free_scfg_abort_may_fail s t es et inp).1 (h es et inp hs ht hi),
   fun h es et inp hs ht hi => (strong_equiv_error_free_scfg_abort_may_fail s t es et inp).2 (h es et inp hs ht hi)⟩

theorem strong_universal_error_free_T_scfg_either_may_fail (s t : Image) :
    strong_universal_error_free_T_scfg_either may_fail_cfg s t ↔
      strong_universal_error_free_T_either s t :=
  and_congr (strong_universal_error_free_T_scfg_may_fail s t)
    (strong_universal_error_free_T_scfg_abort_may_fail s t)

/-- Filtering executions lets a baseline safety proof discharge configured safety. -/
theorem error_free_scfg_of_error_free (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) (h : error_free (run img lim en inp)) :
    error_free (run_scfg cfg img lim en inp) :=
  fun he => h (run_scfg_sub_errors cfg img lim en inp he)

/-- Filtering executions lets a baseline coverage proof discharge configured coverage. -/
theorem modeled_scfg_of_modeled (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) (h : modeled (run img lim en inp)) :
    modeled (run_scfg cfg img lim en inp) :=
  fun hu => h (run_scfg_sub_unmodeled cfg img lim en inp hu)

/-- The allocation-only switch retains the earlier task interface. -/
def strong_universal_T_cfg (alloc_may_fail : Bool) (s t : Image) : Prop :=
  strong_universal_T_scfg (alloc_only_cfg alloc_may_fail) s t

/-- The allocation-only switch also supports the stronger safety contract. -/
def strong_universal_error_free_T_cfg (alloc_may_fail : Bool) (s t : Image) : Prop :=
  strong_universal_error_free_T_scfg (alloc_only_cfg alloc_may_fail) s t

theorem strong_universal_T_cfg_true (s t : Image) :
    strong_universal_T_cfg true s t ↔ strong_universal_T s t :=
  strong_universal_T_scfg_may_fail s t

theorem strong_universal_error_free_T_cfg_true (s t : Image) :
    strong_universal_error_free_T_cfg true s t ↔ strong_universal_error_free_T s t :=
  strong_universal_error_free_T_scfg_may_fail s t

end LinuxProcessSemantics.EquivalenceDefinition.Equivalence
