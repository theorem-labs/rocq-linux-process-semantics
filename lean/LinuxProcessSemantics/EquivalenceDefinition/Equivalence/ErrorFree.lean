-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/Equivalence.v
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Base

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! Error-free and declared-input contracts. Rocq section parameters are
explicit leading image arguments, as in `Base.lean`. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.Equivalence

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run

/-- Signal death is an observation in the trace set, rather than a new
behavior field, so trace comparison already observes it. -/
def dies_by_signal (b : behavior) : Prop :=
  ∃ tr sig fs, b.bh_traces tr ∧ KillEv sig fs ∈ tr

/-- A followed abort need not error. The abort-declared error-free contract
must also exclude signal death to retain its safety obligation. -/
def error_free_unkilled (b : behavior) : Prop :=
  error_free b ∧ ¬ dies_by_signal b

theorem error_free_unkilled_error_free (b : behavior) :
    error_free_unkilled b → error_free b := fun h => h.1

/-- A synthetic behavior separates the predicates; it is not a run witness. -/
theorem error_free_unkilled_bites : ∃ b, error_free b ∧ ¬ error_free_unkilled b := by
  refine ⟨{ bh_traces := fun tr => tr = [] ∨ tr = [KillEv (Z_to_bv 64 6) []]
            bh_errors := False, bh_all_errors := False, bh_unmodeled := False },
    fun h => h, ?_⟩
  intro h
  exact h.2 ⟨[KillEv (Z_to_bv 64 6) []], Z_to_bv 64 6, [], Or.inr rfl,
    List.mem_cons_self⟩

/-- Coverage failure implies error for constructed runs, not for arbitrary
records of propositions. This bridge makes error-freedom imply coverage. -/
theorem run_unmodeled_errors (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (h : (run img lim en inp).bh_unmodeled) : (run img lim en inp).bh_errors :=
  reaches_unmodeled_reaches_error img.img_segments _ h

/-- The all-error escape implies a reachable error for constructed runs. -/
theorem run_all_errors_errors (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (h : (run img lim en inp).bh_all_errors) : (run img lim en inp).bh_errors :=
  all_traces_error_reaches_error img.img_segments _ h

/-- Error-freedom inherits the coverage conjunct's anti-vacuity role. -/
theorem run_error_free_modeled (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (h : error_free (run img lim en inp)) : modeled (run img lim en inp) :=
  fun hu => h (run_unmodeled_errors img lim en inp hu)

/-- A synthetic quiet behavior pins predicates independently of `run`;
behavior records impose no coherence conditions between their fields. -/
def quiet_behavior : behavior :=
  { bh_traces := fun tr => tr = [], bh_errors := False,
    bh_all_errors := False, bh_unmodeled := False }

/-- A modeled crash is tolerated by baseline equivalence but excluded by
error-freedom; this synthetic record isolates that distinction. -/
def crashing_behavior : behavior :=
  { bh_traces := fun tr => tr = [], bh_errors := True,
    bh_all_errors := True, bh_unmodeled := False }

theorem error_free_bites : error_free quiet_behavior ∧ ¬ error_free crashing_behavior :=
  ⟨fun h => h, fun h => h True.intro⟩

theorem modeled_not_error_free_bites : ¬ (∀ b, modeled b → error_free b) :=
  fun h => h crashing_behavior (fun hu => hu) True.intro

/-- The basic tiers use argc = 1 with an empty argv[0]. -/
def basic_argv : List (List byte) := [[]]

/-- Both runs must be safe and equally productive, including exit prefixes.
Entries are independent and each run uses its role's allocation budget. -/
def strong_equiv_error_free (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free (run source_image source_alloc_limit en_source inp) ∧
  error_free (run target_image target_alloc_limit en_target inp) ∧
  trace_equiv (run source_image source_alloc_limit en_source inp).bh_traces
    (run target_image target_alloc_limit en_target inp).bh_traces

/-- The usual valid-entry shell with a stronger per-triple obligation.
An image with no valid entry still satisfies it vacuously: consumers still
need `IMAGE_WF`, since strengthening the body cannot inhabit the range. -/
def strong_universal_error_free_T (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input inp → strong_equiv_error_free source_image target_image en_source en_target inp

theorem strong_equiv_error_free_implies (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (h : strong_equiv_error_free source_image target_image en_source en_target inp) :
    strong_equiv source_image target_image en_source en_target inp :=
  ⟨run_error_free_modeled _ _ _ _ h.1, Or.inr ⟨h.2.2, h.2.1⟩⟩

theorem strong_universal_error_free_implies (source_image target_image : Image)
    (h : strong_universal_error_free_T source_image target_image) :
    strong_universal_T source_image target_image :=
  fun es et inp hs ht hi => strong_equiv_error_free_implies _ _ _ _ _ (h es et inp hs ht hi)

theorem strong_equiv_error_free_no_all_errors_escape (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (h : (run source_image source_alloc_limit en_source inp).bh_all_errors) :
    ¬ strong_equiv_error_free source_image target_image en_source en_target inp :=
  fun he => he.1 (run_all_errors_errors _ _ _ _ h)

theorem strong_universal_error_free_refuted_by_source_error (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (hs : valid_entry source_image en_source inp) (ht : valid_entry target_image en_target inp)
    (hi : valid_input inp) (he : (run source_image source_alloc_limit en_source inp).bh_errors) :
    ¬ strong_universal_error_free_T source_image target_image :=
  fun h => (h en_source en_target inp hs ht hi).1 he

/-- Only the input family changes: signal death becomes an observation the
target must reproduce, while the per-triple baseline contract stays fixed. -/
def strong_universal_T_abort (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort inp → strong_equiv source_image target_image en_source en_target inp

/-- Leaving the stance open requires both readings; it does not let a proof
choose whichever reading is easier. -/
def strong_universal_T_either (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_either inp → strong_equiv source_image target_image en_source en_target inp

theorem strong_universal_T_either_splits (source_image target_image : Image) :
    strong_universal_T_either source_image target_image ↔
      strong_universal_T source_image target_image ∧ strong_universal_T_abort source_image target_image := by
  constructor
  · intro h
    exact ⟨fun es et inp hs ht hi => h es et inp hs ht (valid_input_either_of_valid_input inp hi),
      fun es et inp hs ht hi => h es et inp hs ht (valid_input_either_of_valid_input_abort inp hi)⟩
  · rintro ⟨hoff, hon⟩ es et inp hs ht hi
    rcases valid_input_either_splits inp hi with hi | hi
    · exact hoff es et inp hs ht hi
    · exact hon es et inp hs ht hi

theorem strong_universal_T_either_implies (source_image target_image : Image)
    (h : strong_universal_T_either source_image target_image) :
    strong_universal_T source_image target_image :=
  ((strong_universal_T_either_splits _ _).1 h).1

theorem strong_universal_T_either_implies_abort (source_image target_image : Image)
    (h : strong_universal_T_either source_image target_image) :
    strong_universal_T_abort source_image target_image :=
  ((strong_universal_T_either_splits _ _).1 h).2

/-- Both runs must also be unkilled: under the abort declaration a followed
abort no longer errors, so plain error-freedom would miss it. -/
def strong_equiv_error_free_abort (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free_unkilled (run source_image source_alloc_limit en_source inp) ∧
  error_free_unkilled (run target_image target_alloc_limit en_target inp) ∧
  trace_equiv (run source_image source_alloc_limit en_source inp).bh_traces
    (run target_image target_alloc_limit en_target inp).bh_traces

/-- The abort-declared shell retains the no-death safety requirement. -/
def strong_universal_error_free_T_abort (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort inp → strong_equiv_error_free_abort source_image target_image en_source en_target inp

theorem strong_equiv_error_free_abort_implies (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (h : strong_equiv_error_free_abort source_image target_image en_source en_target inp) :
    strong_equiv source_image target_image en_source en_target inp :=
  ⟨run_error_free_modeled _ _ _ _ h.1.1, Or.inr ⟨h.2.2, h.2.1.1⟩⟩

theorem strong_universal_error_free_T_abort_implies (source_image target_image : Image)
    (h : strong_universal_error_free_T_abort source_image target_image) :
    strong_universal_T_abort source_image target_image :=
  fun es et inp hs ht hi => strong_equiv_error_free_abort_implies _ _ _ _ _ (h es et inp hs ht hi)

/-- The stances have different per-triple obligations. Their conjunction
expresses leaving the stance open without strengthening the off reading. -/
def strong_universal_error_free_T_either (source_image target_image : Image) : Prop :=
  strong_universal_error_free_T source_image target_image ∧
  strong_universal_error_free_T_abort source_image target_image

theorem strong_universal_error_free_T_either_splits (source_image target_image : Image) :
    strong_universal_error_free_T_either source_image target_image ↔
      strong_universal_error_free_T source_image target_image ∧
      strong_universal_error_free_T_abort source_image target_image := Iff.rfl

theorem strong_universal_error_free_T_either_implies (source_image target_image : Image)
    (h : strong_universal_error_free_T_either source_image target_image) :
    strong_universal_error_free_T source_image target_image := h.1

theorem strong_universal_error_free_T_either_implies_abort (source_image target_image : Image)
    (h : strong_universal_error_free_T_either source_image target_image) :
    strong_universal_error_free_T_abort source_image target_image := h.2

/-- A source death at one valid triple refutes the abort-declared contract.
The hypothesis needs a run witness; a synthetic behavior does not supply it. -/
theorem strong_universal_error_free_T_abort_refuted_by_abort (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (hs : valid_entry source_image en_source inp) (ht : valid_entry target_image en_target inp)
    (hi : valid_input_abort inp) (hd : dies_by_signal (run source_image source_alloc_limit en_source inp)) :
    ¬ strong_universal_error_free_T_abort source_image target_image :=
  fun h => (h en_source en_target inp hs ht hi).1.2 hd

/-- The baseline obligation under the declared RV64GC word.
Only the input family narrows; the per-triple obligation has no size gate. -/
def strong_universal_T_hwcap_rv64gc (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_hwcap_rv64gc inp → strong_equiv source_image target_image en_source en_target inp

/-- The baseline obligation under the declared RV64GCV word.
Only the input family narrows; the per-triple obligation has no size gate. -/
def strong_universal_T_hwcap_rv64gcv (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_hwcap_rv64gcv inp → strong_equiv source_image target_image en_source en_target inp

/-- The permissive default requires both hardware-capability readings. -/
theorem strong_universal_T_hwcap_splits (source_image target_image : Image) :
    strong_universal_T source_image target_image ↔
      strong_universal_T_hwcap_rv64gc source_image target_image ∧
      strong_universal_T_hwcap_rv64gcv source_image target_image := by
  constructor
  · intro h
    exact ⟨fun es et inp hs ht hi => h es et inp hs ht (valid_input_of_valid_input_hwcap_rv64gc inp hi),
      fun es et inp hs ht hi => h es et inp hs ht (valid_input_of_valid_input_hwcap_rv64gcv inp hi)⟩
  · rintro ⟨hgc, hgcv⟩ es et inp hs ht hi
    rcases valid_input_hwcap_splits inp hi with hi | hi
    · exact hgc es et inp hs ht hi
    · exact hgcv es et inp hs ht hi

/-- The error-free obligation under the declared RV64GC word.
Only the input family narrows; the per-triple obligation has no size gate. -/
def strong_universal_error_free_T_hwcap_rv64gc (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_hwcap_rv64gc inp → strong_equiv_error_free source_image target_image en_source en_target inp

/-- The error-free obligation under the declared RV64GCV word.
Only the input family narrows; the per-triple obligation has no size gate. -/
def strong_universal_error_free_T_hwcap_rv64gcv (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_hwcap_rv64gcv inp → strong_equiv_error_free source_image target_image en_source en_target inp

/-- The permissive default requires both hardware-capability readings. -/
theorem strong_universal_error_free_T_hwcap_splits (source_image target_image : Image) :
    strong_universal_error_free_T source_image target_image ↔
      strong_universal_error_free_T_hwcap_rv64gc source_image target_image ∧
      strong_universal_error_free_T_hwcap_rv64gcv source_image target_image := by
  constructor
  · intro h
    exact ⟨fun es et inp hs ht hi => h es et inp hs ht (valid_input_of_valid_input_hwcap_rv64gc inp hi),
      fun es et inp hs ht hi => h es et inp hs ht (valid_input_of_valid_input_hwcap_rv64gcv inp hi)⟩
  · rintro ⟨hgc, hgcv⟩ es et inp hs ht hi
    rcases valid_input_hwcap_splits inp hi with hi | hi
    · exact hgc es et inp hs ht hi
    · exact hgcv es et inp hs ht hi

/-- Opt-in error-freedom still needs IMAGE_WF to exclude an empty entry range. -/
structure SPEC_ERROR_FREE (source target : Image) : Prop where
  strong_universal_error_free : strong_universal_error_free_T source target

/-- The sealed abort declaration keeps the stance explicit in the obligation. -/
structure SPEC_ABORT (source target : Image) : Prop where
  strong_universal : strong_universal_T_abort source target

/-- Leaving the stance open seals an obligation under both readings. -/
structure SPEC_EITHER (source target : Image) : Prop where
  strong_universal : strong_universal_T_either source target

/-- Abort-declared safety excludes signal death as well as error. -/
structure SPEC_ERROR_FREE_ABORT (source target : Image) : Prop where
  strong_universal_error_free : strong_universal_error_free_T_abort source target

/-- Error-free sealing with no stance chosen requires both readings. -/
structure SPEC_ERROR_FREE_EITHER (source target : Image) : Prop where
  strong_universal_error_free : strong_universal_error_free_T_either source target

/-- The RV64GC declaration is sealed in the input family, not inferred from the binary. -/
structure SPEC_HWCAP_RV64GC (source target : Image) : Prop where
  strong_universal : strong_universal_T_hwcap_rv64gc source target

/-- The RV64GCV declaration is sealed in the input family, not inferred from the binary. -/
structure SPEC_HWCAP_RV64GCV (source target : Image) : Prop where
  strong_universal : strong_universal_T_hwcap_rv64gcv source target

/-- The RV64GC declaration is sealed in the input family, not inferred from the binary. -/
structure SPEC_ERROR_FREE_HWCAP_RV64GC (source target : Image) : Prop where
  strong_universal_error_free : strong_universal_error_free_T_hwcap_rv64gc source target

/-- The RV64GCV declaration is sealed in the input family, not inferred from the binary. -/
structure SPEC_ERROR_FREE_HWCAP_RV64GCV (source target : Image) : Prop where
  strong_universal_error_free : strong_universal_error_free_T_hwcap_rv64gcv source target

/-- Trace-set comparison transports along behavior equivalence. -/
theorem trace_equiv_behavior_equiv (s s' t t' : behavior)
    (hs : behavior_equiv s s') (ht : behavior_equiv t t') :
    trace_equiv s.bh_traces t.bh_traces ↔ trace_equiv s'.bh_traces t'.bh_traces :=
  ⟨fun h tr => (hs.1 tr).symm.trans ((h tr).trans (ht.1 tr)),
   fun h tr => (hs.1 tr).trans ((h tr).trans (ht.1 tr).symm)⟩

theorem equiv_behavior_equiv (s s' t t' : behavior)
    (hs : behavior_equiv s s') (ht : behavior_equiv t t') : equiv s t ↔ equiv s' t' :=
  or_congr hs.2.2.1 (and_congr (trace_equiv_behavior_equiv s s' t t' hs ht) (not_congr ht.2.1))

theorem modeled_behavior_equiv (b b' : behavior) (h : behavior_equiv b b') :
    modeled b ↔ modeled b' := not_congr h.2.2.2

theorem error_free_behavior_equiv (b b' : behavior) (h : behavior_equiv b b') :
    error_free b ↔ error_free b' := not_congr h.2.1

/-- Signal death transports because it reads only the trace set. -/
theorem dies_by_signal_behavior_equiv (b b' : behavior) (h : behavior_equiv b b') :
    dies_by_signal b ↔ dies_by_signal b' := by
  constructor
  · rintro ⟨tr, sig, fs, ht, hk⟩
    exact ⟨tr, sig, fs, (h.1 tr).1 ht, hk⟩
  · rintro ⟨tr, sig, fs, ht, hk⟩
    exact ⟨tr, sig, fs, (h.1 tr).2 ht, hk⟩

theorem error_free_unkilled_behavior_equiv (b b' : behavior) (h : behavior_equiv b b') :
    error_free_unkilled b ↔ error_free_unkilled b' :=
  and_congr (error_free_behavior_equiv b b' h) (not_congr (dies_by_signal_behavior_equiv b b' h))

end LinuxProcessSemantics.EquivalenceDefinition.Equivalence
