-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/Equivalence.v
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Base
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ErrorFree
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Scfg

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! The source budget premise restricts the input domain; it makes no target-budget
claim. The 9/8 factor and 261 MiB charge are runtime measurements outside the
model, not an allocation relation between the two programs.

The `BUDGETS` structure at the end of this file holds the two limits and the
proof of `budget_headroom_ok lim_source lim_target = true` in one value. Before
it, Lean passed the limits as two separate `Int` arguments with no check beside
them, so a one-image statement that reads only `lim_source`, such as
`SPEC_HALTS_ALLOWED_SCFG_BUDGETS`, was not held to the same checked pair as a
two-image statement such as `SPEC_BUDGETS`. A value of `BUDGETS` keeps the two
limits and the check together, which is what Rocq's module type `BUDGETS` does. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.Equivalence

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run

/-- The premise excludes inputs whose source reaches the budget mark. -/
def source_within_budget (lim_source : Int) (source_image : Image)
    (en_source : ExecEntry) (inp : ProcInput) : Prop :=
  ¬ run_budget_refused source_image lim_source en_source inp

def strong_equiv_budgets (lim_source lim_target : Int) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  modeled (run source_image lim_source en_source inp) ∧
  equiv (run source_image lim_source en_source inp) (run target_image lim_target en_target inp)

def strong_equiv_error_free_budgets (lim_source lim_target : Int) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free (run source_image lim_source en_source inp) ∧
  error_free (run target_image lim_target en_target inp) ∧
  trace_equiv (run source_image lim_source en_source inp).bh_traces (run target_image lim_target en_target inp).bh_traces

theorem strong_equiv_error_free_budgets_implies (lim_source lim_target : Int) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) (h : strong_equiv_error_free_budgets lim_source lim_target source_image target_image en_source en_target inp) :
    strong_equiv_budgets lim_source lim_target source_image target_image en_source en_target inp :=
  ⟨run_error_free_modeled _ _ _ _ h.1, Or.inr ⟨h.2.2, h.2.1⟩⟩

def strong_equiv_error_free_budgets_abort (lim_source lim_target : Int) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free_unkilled (run source_image lim_source en_source inp) ∧
  error_free_unkilled (run target_image lim_target en_target inp) ∧
  trace_equiv (run source_image lim_source en_source inp).bh_traces (run target_image lim_target en_target inp).bh_traces

theorem strong_equiv_error_free_budgets_abort_implies (lim_source lim_target : Int) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) (h : strong_equiv_error_free_budgets_abort lim_source lim_target source_image target_image en_source en_target inp) :
    strong_equiv_budgets lim_source lim_target source_image target_image en_source en_target inp :=
  ⟨run_error_free_modeled _ _ _ _ h.1.1, Or.inr ⟨h.2.2, h.2.1.1⟩⟩

def strong_universal_T_budgets (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input inp → source_within_budget lim_source source_image en_source inp →
    strong_equiv_budgets lim_source lim_target source_image target_image en_source en_target inp

def strong_universal_error_free_T_budgets (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input inp → source_within_budget lim_source source_image en_source inp →
    strong_equiv_error_free_budgets lim_source lim_target source_image target_image en_source en_target inp

theorem strong_universal_error_free_T_budgets_implies (lim_source lim_target : Int) (source_image target_image : Image)
    (h : strong_universal_error_free_T_budgets lim_source lim_target source_image target_image) : strong_universal_T_budgets lim_source lim_target source_image target_image :=
  fun es et inp hs ht hi hb => strong_equiv_error_free_budgets_implies lim_source lim_target source_image target_image es et inp (h es et inp hs ht hi hb)

def strong_universal_T_budgets_hwcap_rv64gc (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_hwcap_rv64gc inp → source_within_budget lim_source source_image en_source inp →
    strong_equiv_budgets lim_source lim_target source_image target_image en_source en_target inp

def strong_universal_error_free_T_budgets_hwcap_rv64gc (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_hwcap_rv64gc inp → source_within_budget lim_source source_image en_source inp →
    strong_equiv_error_free_budgets lim_source lim_target source_image target_image en_source en_target inp

theorem strong_universal_error_free_T_budgets_hwcap_rv64gc_implies (lim_source lim_target : Int) (source_image target_image : Image)
    (h : strong_universal_error_free_T_budgets_hwcap_rv64gc lim_source lim_target source_image target_image) : strong_universal_T_budgets_hwcap_rv64gc lim_source lim_target source_image target_image :=
  fun es et inp hs ht hi hb => strong_equiv_error_free_budgets_implies lim_source lim_target source_image target_image es et inp (h es et inp hs ht hi hb)

def strong_universal_T_budgets_hwcap_rv64gcv (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_hwcap_rv64gcv inp → source_within_budget lim_source source_image en_source inp →
    strong_equiv_budgets lim_source lim_target source_image target_image en_source en_target inp

def strong_universal_error_free_T_budgets_hwcap_rv64gcv (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_hwcap_rv64gcv inp → source_within_budget lim_source source_image en_source inp →
    strong_equiv_error_free_budgets lim_source lim_target source_image target_image en_source en_target inp

theorem strong_universal_error_free_T_budgets_hwcap_rv64gcv_implies (lim_source lim_target : Int) (source_image target_image : Image)
    (h : strong_universal_error_free_T_budgets_hwcap_rv64gcv lim_source lim_target source_image target_image) : strong_universal_T_budgets_hwcap_rv64gcv lim_source lim_target source_image target_image :=
  fun es et inp hs ht hi hb => strong_equiv_error_free_budgets_implies lim_source lim_target source_image target_image es et inp (h es et inp hs ht hi hb)

theorem strong_universal_T_budgets_hwcap_splits (lim_source lim_target : Int) (source_image target_image : Image) :
    strong_universal_T_budgets lim_source lim_target source_image target_image ↔
      strong_universal_T_budgets_hwcap_rv64gc lim_source lim_target source_image target_image ∧ strong_universal_T_budgets_hwcap_rv64gcv lim_source lim_target source_image target_image := by
  constructor
  · intro h
    exact ⟨fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_of_valid_input_hwcap_rv64gc inp hi) hb,
      fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_of_valid_input_hwcap_rv64gcv inp hi) hb⟩
  · rintro ⟨hgc, hgcv⟩ es et inp hs ht hi hb
    rcases valid_input_hwcap_splits inp hi with hi | hi
    · exact hgc es et inp hs ht hi hb
    · exact hgcv es et inp hs ht hi hb

theorem strong_universal_error_free_T_budgets_hwcap_splits (lim_source lim_target : Int) (source_image target_image : Image) :
    strong_universal_error_free_T_budgets lim_source lim_target source_image target_image ↔
      strong_universal_error_free_T_budgets_hwcap_rv64gc lim_source lim_target source_image target_image ∧ strong_universal_error_free_T_budgets_hwcap_rv64gcv lim_source lim_target source_image target_image := by
  constructor
  · intro h
    exact ⟨fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_of_valid_input_hwcap_rv64gc inp hi) hb,
      fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_of_valid_input_hwcap_rv64gcv inp hi) hb⟩
  · rintro ⟨hgc, hgcv⟩ es et inp hs ht hi hb
    rcases valid_input_hwcap_splits inp hi with hi | hi
    · exact hgc es et inp hs ht hi hb
    · exact hgcv es et inp hs ht hi hb

theorem strong_universal_error_free_T_budgets_refuted_by_source_error (lim_source lim_target : Int) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (hs : valid_entry source_image en_source inp) (ht : valid_entry target_image en_target inp)
    (hi : valid_input inp) (hb : source_within_budget lim_source source_image en_source inp)
    (he : (run source_image lim_source en_source inp).bh_errors) : ¬ strong_universal_error_free_T_budgets lim_source lim_target source_image target_image :=
  fun h => (h en_source en_target inp hs ht hi hb).1 he

def strong_universal_T_budgets_abort (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort inp → source_within_budget lim_source source_image en_source inp →
    strong_equiv_budgets lim_source lim_target source_image target_image en_source en_target inp

def strong_universal_error_free_T_budgets_abort (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort inp → source_within_budget lim_source source_image en_source inp →
    strong_equiv_error_free_budgets_abort lim_source lim_target source_image target_image en_source en_target inp

theorem strong_universal_error_free_T_budgets_abort_implies (lim_source lim_target : Int) (source_image target_image : Image)
    (h : strong_universal_error_free_T_budgets_abort lim_source lim_target source_image target_image) : strong_universal_T_budgets_abort lim_source lim_target source_image target_image :=
  fun es et inp hs ht hi hb => strong_equiv_error_free_budgets_abort_implies lim_source lim_target source_image target_image es et inp (h es et inp hs ht hi hb)

def strong_universal_T_budgets_abort_hwcap_rv64gc (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort_hwcap_rv64gc inp → source_within_budget lim_source source_image en_source inp →
    strong_equiv_budgets lim_source lim_target source_image target_image en_source en_target inp

def strong_universal_error_free_T_budgets_abort_hwcap_rv64gc (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort_hwcap_rv64gc inp → source_within_budget lim_source source_image en_source inp →
    strong_equiv_error_free_budgets_abort lim_source lim_target source_image target_image en_source en_target inp

theorem strong_universal_error_free_T_budgets_abort_hwcap_rv64gc_implies (lim_source lim_target : Int) (source_image target_image : Image)
    (h : strong_universal_error_free_T_budgets_abort_hwcap_rv64gc lim_source lim_target source_image target_image) : strong_universal_T_budgets_abort_hwcap_rv64gc lim_source lim_target source_image target_image :=
  fun es et inp hs ht hi hb => strong_equiv_error_free_budgets_abort_implies lim_source lim_target source_image target_image es et inp (h es et inp hs ht hi hb)

def strong_universal_T_budgets_abort_hwcap_rv64gcv (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort_hwcap_rv64gcv inp → source_within_budget lim_source source_image en_source inp →
    strong_equiv_budgets lim_source lim_target source_image target_image en_source en_target inp

def strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort_hwcap_rv64gcv inp → source_within_budget lim_source source_image en_source inp →
    strong_equiv_error_free_budgets_abort lim_source lim_target source_image target_image en_source en_target inp

theorem strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv_implies (lim_source lim_target : Int) (source_image target_image : Image)
    (h : strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv lim_source lim_target source_image target_image) : strong_universal_T_budgets_abort_hwcap_rv64gcv lim_source lim_target source_image target_image :=
  fun es et inp hs ht hi hb => strong_equiv_error_free_budgets_abort_implies lim_source lim_target source_image target_image es et inp (h es et inp hs ht hi hb)

theorem strong_universal_T_budgets_abort_hwcap_splits (lim_source lim_target : Int) (source_image target_image : Image) :
    strong_universal_T_budgets_abort lim_source lim_target source_image target_image ↔
      strong_universal_T_budgets_abort_hwcap_rv64gc lim_source lim_target source_image target_image ∧ strong_universal_T_budgets_abort_hwcap_rv64gcv lim_source lim_target source_image target_image := by
  constructor
  · intro h
    exact ⟨fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_abort_of_valid_input_abort_hwcap_rv64gc inp hi) hb,
      fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_abort_of_valid_input_abort_hwcap_rv64gcv inp hi) hb⟩
  · rintro ⟨hgc, hgcv⟩ es et inp hs ht hi hb
    rcases valid_input_abort_hwcap_splits inp hi with hi | hi
    · exact hgc es et inp hs ht hi hb
    · exact hgcv es et inp hs ht hi hb

theorem strong_universal_error_free_T_budgets_abort_hwcap_splits (lim_source lim_target : Int) (source_image target_image : Image) :
    strong_universal_error_free_T_budgets_abort lim_source lim_target source_image target_image ↔
      strong_universal_error_free_T_budgets_abort_hwcap_rv64gc lim_source lim_target source_image target_image ∧ strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv lim_source lim_target source_image target_image := by
  constructor
  · intro h
    exact ⟨fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_abort_of_valid_input_abort_hwcap_rv64gc inp hi) hb,
      fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_abort_of_valid_input_abort_hwcap_rv64gcv inp hi) hb⟩
  · rintro ⟨hgc, hgcv⟩ es et inp hs ht hi hb
    rcases valid_input_abort_hwcap_splits inp hi with hi | hi
    · exact hgc es et inp hs ht hi hb
    · exact hgcv es et inp hs ht hi hb

/-- The premise excludes inputs whose source reaches the budget mark. -/
def source_within_budget_scfg (cfg : SpuriousCfg) (lim_source : Int) (source_image : Image)
    (en_source : ExecEntry) (inp : ProcInput) : Prop :=
  ¬ run_scfg_budget_refused cfg source_image lim_source en_source inp

theorem source_within_budget_scfg_of_source_within_budget (cfg : SpuriousCfg)
    (lim_source : Int) (source_image : Image) (en_source : ExecEntry) (inp : ProcInput)
    (h : source_within_budget lim_source source_image en_source inp) :
    source_within_budget_scfg cfg lim_source source_image en_source inp :=
  fun hc => h (run_scfg_budget_refused_sub cfg _ _ _ _ hc)

def strong_equiv_budgets_scfg (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  modeled (run_scfg cfg source_image lim_source en_source inp) ∧
  equiv (run_scfg cfg source_image lim_source en_source inp) (run_scfg cfg target_image lim_target en_target inp)

def strong_equiv_error_free_budgets_scfg (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free (run_scfg cfg source_image lim_source en_source inp) ∧
  error_free (run_scfg cfg target_image lim_target en_target inp) ∧
  trace_equiv (run_scfg cfg source_image lim_source en_source inp).bh_traces (run_scfg cfg target_image lim_target en_target inp).bh_traces

theorem strong_equiv_error_free_budgets_scfg_implies (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) (h : strong_equiv_error_free_budgets_scfg cfg lim_source lim_target source_image target_image en_source en_target inp) :
    strong_equiv_budgets_scfg cfg lim_source lim_target source_image target_image en_source en_target inp :=
  ⟨(fun hu => h.1 (run_scfg_unmodeled_errors cfg _ _ _ _ hu)), Or.inr ⟨h.2.2, h.2.1⟩⟩

def strong_equiv_error_free_budgets_scfg_abort (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free_unkilled (run_scfg cfg source_image lim_source en_source inp) ∧
  error_free_unkilled (run_scfg cfg target_image lim_target en_target inp) ∧
  trace_equiv (run_scfg cfg source_image lim_source en_source inp).bh_traces (run_scfg cfg target_image lim_target en_target inp).bh_traces

theorem strong_equiv_error_free_budgets_scfg_abort_implies (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) (h : strong_equiv_error_free_budgets_scfg_abort cfg lim_source lim_target source_image target_image en_source en_target inp) :
    strong_equiv_budgets_scfg cfg lim_source lim_target source_image target_image en_source en_target inp :=
  ⟨(fun hu => h.1.1 (run_scfg_unmodeled_errors cfg _ _ _ _ hu)), Or.inr ⟨h.2.2, h.2.1.1⟩⟩

def strong_universal_T_scfg_budgets (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input inp → source_within_budget_scfg cfg lim_source source_image en_source inp →
    strong_equiv_budgets_scfg cfg lim_source lim_target source_image target_image en_source en_target inp

def strong_universal_error_free_T_scfg_budgets (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input inp → source_within_budget_scfg cfg lim_source source_image en_source inp →
    strong_equiv_error_free_budgets_scfg cfg lim_source lim_target source_image target_image en_source en_target inp

theorem strong_universal_error_free_T_scfg_budgets_implies (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image)
    (h : strong_universal_error_free_T_scfg_budgets cfg lim_source lim_target source_image target_image) : strong_universal_T_scfg_budgets cfg lim_source lim_target source_image target_image :=
  fun es et inp hs ht hi hb => strong_equiv_error_free_budgets_scfg_implies cfg lim_source lim_target source_image target_image es et inp (h es et inp hs ht hi hb)

def strong_universal_T_scfg_budgets_hwcap_rv64gc (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_hwcap_rv64gc inp → source_within_budget_scfg cfg lim_source source_image en_source inp →
    strong_equiv_budgets_scfg cfg lim_source lim_target source_image target_image en_source en_target inp

def strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_hwcap_rv64gc inp → source_within_budget_scfg cfg lim_source source_image en_source inp →
    strong_equiv_error_free_budgets_scfg cfg lim_source lim_target source_image target_image en_source en_target inp

theorem strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc_implies (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image)
    (h : strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc cfg lim_source lim_target source_image target_image) : strong_universal_T_scfg_budgets_hwcap_rv64gc cfg lim_source lim_target source_image target_image :=
  fun es et inp hs ht hi hb => strong_equiv_error_free_budgets_scfg_implies cfg lim_source lim_target source_image target_image es et inp (h es et inp hs ht hi hb)

def strong_universal_T_scfg_budgets_hwcap_rv64gcv (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_hwcap_rv64gcv inp → source_within_budget_scfg cfg lim_source source_image en_source inp →
    strong_equiv_budgets_scfg cfg lim_source lim_target source_image target_image en_source en_target inp

def strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_hwcap_rv64gcv inp → source_within_budget_scfg cfg lim_source source_image en_source inp →
    strong_equiv_error_free_budgets_scfg cfg lim_source lim_target source_image target_image en_source en_target inp

theorem strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv_implies (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image)
    (h : strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv cfg lim_source lim_target source_image target_image) : strong_universal_T_scfg_budgets_hwcap_rv64gcv cfg lim_source lim_target source_image target_image :=
  fun es et inp hs ht hi hb => strong_equiv_error_free_budgets_scfg_implies cfg lim_source lim_target source_image target_image es et inp (h es et inp hs ht hi hb)

theorem strong_universal_T_scfg_budgets_hwcap_splits (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) :
    strong_universal_T_scfg_budgets cfg lim_source lim_target source_image target_image ↔
      strong_universal_T_scfg_budgets_hwcap_rv64gc cfg lim_source lim_target source_image target_image ∧ strong_universal_T_scfg_budgets_hwcap_rv64gcv cfg lim_source lim_target source_image target_image := by
  constructor
  · intro h
    exact ⟨fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_of_valid_input_hwcap_rv64gc inp hi) hb,
      fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_of_valid_input_hwcap_rv64gcv inp hi) hb⟩
  · rintro ⟨hgc, hgcv⟩ es et inp hs ht hi hb
    rcases valid_input_hwcap_splits inp hi with hi | hi
    · exact hgc es et inp hs ht hi hb
    · exact hgcv es et inp hs ht hi hb

theorem strong_universal_error_free_T_scfg_budgets_hwcap_splits (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) :
    strong_universal_error_free_T_scfg_budgets cfg lim_source lim_target source_image target_image ↔
      strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc cfg lim_source lim_target source_image target_image ∧ strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv cfg lim_source lim_target source_image target_image := by
  constructor
  · intro h
    exact ⟨fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_of_valid_input_hwcap_rv64gc inp hi) hb,
      fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_of_valid_input_hwcap_rv64gcv inp hi) hb⟩
  · rintro ⟨hgc, hgcv⟩ es et inp hs ht hi hb
    rcases valid_input_hwcap_splits inp hi with hi | hi
    · exact hgc es et inp hs ht hi hb
    · exact hgcv es et inp hs ht hi hb

theorem strong_universal_error_free_T_scfg_budgets_refuted_by_source_error (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (hs : valid_entry source_image en_source inp) (ht : valid_entry target_image en_target inp)
    (hi : valid_input inp) (hb : source_within_budget_scfg cfg lim_source source_image en_source inp)
    (he : (run_scfg cfg source_image lim_source en_source inp).bh_errors) : ¬ strong_universal_error_free_T_scfg_budgets cfg lim_source lim_target source_image target_image :=
  fun h => (h en_source en_target inp hs ht hi hb).1 he

def strong_universal_T_scfg_budgets_abort (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort inp → source_within_budget_scfg cfg lim_source source_image en_source inp →
    strong_equiv_budgets_scfg cfg lim_source lim_target source_image target_image en_source en_target inp

def strong_universal_error_free_T_scfg_budgets_abort (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort inp → source_within_budget_scfg cfg lim_source source_image en_source inp →
    strong_equiv_error_free_budgets_scfg_abort cfg lim_source lim_target source_image target_image en_source en_target inp

theorem strong_universal_error_free_T_scfg_budgets_abort_implies (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image)
    (h : strong_universal_error_free_T_scfg_budgets_abort cfg lim_source lim_target source_image target_image) : strong_universal_T_scfg_budgets_abort cfg lim_source lim_target source_image target_image :=
  fun es et inp hs ht hi hb => strong_equiv_error_free_budgets_scfg_abort_implies cfg lim_source lim_target source_image target_image es et inp (h es et inp hs ht hi hb)

def strong_universal_T_scfg_budgets_abort_hwcap_rv64gc (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort_hwcap_rv64gc inp → source_within_budget_scfg cfg lim_source source_image en_source inp →
    strong_equiv_budgets_scfg cfg lim_source lim_target source_image target_image en_source en_target inp

def strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort_hwcap_rv64gc inp → source_within_budget_scfg cfg lim_source source_image en_source inp →
    strong_equiv_error_free_budgets_scfg_abort cfg lim_source lim_target source_image target_image en_source en_target inp

theorem strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc_implies (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image)
    (h : strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc cfg lim_source lim_target source_image target_image) : strong_universal_T_scfg_budgets_abort_hwcap_rv64gc cfg lim_source lim_target source_image target_image :=
  fun es et inp hs ht hi hb => strong_equiv_error_free_budgets_scfg_abort_implies cfg lim_source lim_target source_image target_image es et inp (h es et inp hs ht hi hb)

def strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort_hwcap_rv64gcv inp → source_within_budget_scfg cfg lim_source source_image en_source inp →
    strong_equiv_budgets_scfg cfg lim_source lim_target source_image target_image en_source en_target inp

def strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp →
    valid_input_abort_hwcap_rv64gcv inp → source_within_budget_scfg cfg lim_source source_image en_source inp →
    strong_equiv_error_free_budgets_scfg_abort cfg lim_source lim_target source_image target_image en_source en_target inp

theorem strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv_implies (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image)
    (h : strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv cfg lim_source lim_target source_image target_image) : strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv cfg lim_source lim_target source_image target_image :=
  fun es et inp hs ht hi hb => strong_equiv_error_free_budgets_scfg_abort_implies cfg lim_source lim_target source_image target_image es et inp (h es et inp hs ht hi hb)

theorem strong_universal_T_scfg_budgets_abort_hwcap_splits (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) :
    strong_universal_T_scfg_budgets_abort cfg lim_source lim_target source_image target_image ↔
      strong_universal_T_scfg_budgets_abort_hwcap_rv64gc cfg lim_source lim_target source_image target_image ∧ strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv cfg lim_source lim_target source_image target_image := by
  constructor
  · intro h
    exact ⟨fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_abort_of_valid_input_abort_hwcap_rv64gc inp hi) hb,
      fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_abort_of_valid_input_abort_hwcap_rv64gcv inp hi) hb⟩
  · rintro ⟨hgc, hgcv⟩ es et inp hs ht hi hb
    rcases valid_input_abort_hwcap_splits inp hi with hi | hi
    · exact hgc es et inp hs ht hi hb
    · exact hgcv es et inp hs ht hi hb

theorem strong_universal_error_free_T_scfg_budgets_abort_hwcap_splits (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image) :
    strong_universal_error_free_T_scfg_budgets_abort cfg lim_source lim_target source_image target_image ↔
      strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc cfg lim_source lim_target source_image target_image ∧ strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv cfg lim_source lim_target source_image target_image := by
  constructor
  · intro h
    exact ⟨fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_abort_of_valid_input_abort_hwcap_rv64gc inp hi) hb,
      fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_abort_of_valid_input_abort_hwcap_rv64gcv inp hi) hb⟩
  · rintro ⟨hgc, hgcv⟩ es et inp hs ht hi hb
    rcases valid_input_abort_hwcap_splits inp hi with hi | hi
    · exact hgc es et inp hs ht hi hb
    · exact hgcv es et inp hs ht hi hb

theorem strong_universal_error_free_T_scfg_budgets_abort_refuted_by_source_error (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (hs : valid_entry source_image en_source inp) (ht : valid_entry target_image en_target inp)
    (hi : valid_input_abort inp) (hb : source_within_budget_scfg cfg lim_source source_image en_source inp)
    (he : (run_scfg cfg source_image lim_source en_source inp).bh_errors) : ¬ strong_universal_error_free_T_scfg_budgets_abort cfg lim_source lim_target source_image target_image :=
  fun h => (h en_source en_target inp hs ht hi hb).1.1 he

theorem strong_universal_error_free_T_scfg_budgets_abort_refuted_by_abort (cfg : SpuriousCfg) (lim_source lim_target : Int) (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (hs : valid_entry source_image en_source inp) (ht : valid_entry target_image en_target inp)
    (hi : valid_input_abort inp) (hb : source_within_budget_scfg cfg lim_source source_image en_source inp)
    (he : dies_by_signal (run_scfg cfg source_image lim_source en_source inp)) : ¬ strong_universal_error_free_T_scfg_budgets_abort cfg lim_source lim_target source_image target_image :=
  fun h => (h en_source en_target inp hs ht hi hb).1.2 he

theorem strong_equiv_budgets_pinned (s t : Image) (en_s en_t : ExecEntry) (inp : ProcInput) :
    strong_equiv_budgets source_alloc_limit target_alloc_limit s t en_s en_t inp ↔
      strong_equiv s t en_s en_t inp := Iff.rfl

theorem strong_equiv_error_free_budgets_pinned (s t : Image) (en_s en_t : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_budgets source_alloc_limit target_alloc_limit s t en_s en_t inp ↔
      strong_equiv_error_free s t en_s en_t inp := Iff.rfl

theorem strong_equiv_error_free_budgets_abort_pinned (s t : Image) (en_s en_t : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_budgets_abort source_alloc_limit target_alloc_limit s t en_s en_t inp ↔
      strong_equiv_error_free_abort s t en_s en_t inp := Iff.rfl

/-- Dropping the premise gives this direction at the shipped limits. -/
theorem strong_universal_T_budgets_of_pinned (s t : Image)
    (h : strong_universal_T s t) :
    strong_universal_T_budgets source_alloc_limit target_alloc_limit s t :=
  fun es et inp hs ht hi _ => h es et inp hs ht hi

/-- Dropping the premise gives this direction at the shipped limits. -/
theorem strong_universal_T_budgets_abort_of_pinned (s t : Image)
    (h : strong_universal_T_abort s t) :
    strong_universal_T_budgets_abort source_alloc_limit target_alloc_limit s t :=
  fun es et inp hs ht hi _ => h es et inp hs ht hi

/-- Dropping the premise gives this direction at the shipped limits. -/
theorem strong_universal_error_free_T_budgets_of_pinned (s t : Image)
    (h : strong_universal_error_free_T s t) :
    strong_universal_error_free_T_budgets source_alloc_limit target_alloc_limit s t :=
  fun es et inp hs ht hi _ => h es et inp hs ht hi

/-- Dropping the premise gives this direction at the shipped limits. -/
theorem strong_universal_error_free_T_budgets_abort_of_pinned (s t : Image)
    (h : strong_universal_error_free_T_abort s t) :
    strong_universal_error_free_T_budgets_abort source_alloc_limit target_alloc_limit s t :=
  fun es et inp hs ht hi _ => h es et inp hs ht hi

theorem strong_equiv_budgets_scfg_pinned (cfg : SpuriousCfg) (s t : Image) (en_s en_t : ExecEntry) (inp : ProcInput) :
    strong_equiv_budgets_scfg cfg source_alloc_limit target_alloc_limit s t en_s en_t inp ↔
      strong_equiv_scfg cfg s t en_s en_t inp := Iff.rfl

theorem strong_equiv_error_free_budgets_scfg_pinned (cfg : SpuriousCfg) (s t : Image) (en_s en_t : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_budgets_scfg cfg source_alloc_limit target_alloc_limit s t en_s en_t inp ↔
      strong_equiv_error_free_scfg cfg s t en_s en_t inp := Iff.rfl

theorem strong_equiv_error_free_budgets_scfg_abort_pinned (cfg : SpuriousCfg) (s t : Image) (en_s en_t : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_budgets_scfg_abort cfg source_alloc_limit target_alloc_limit s t en_s en_t inp ↔
      strong_equiv_error_free_scfg_abort cfg s t en_s en_t inp := Iff.rfl

/-- Dropping the premise gives this direction at the shipped limits. -/
theorem strong_universal_T_scfg_budgets_of_scfg (cfg : SpuriousCfg) (s t : Image)
    (h : strong_universal_T_scfg cfg s t) :
    strong_universal_T_scfg_budgets cfg source_alloc_limit target_alloc_limit s t :=
  fun es et inp hs ht hi _ => h es et inp hs ht hi

/-- Dropping the premise gives this direction at the shipped limits. -/
theorem strong_universal_T_scfg_budgets_abort_of_scfg (cfg : SpuriousCfg) (s t : Image)
    (h : strong_universal_T_scfg_abort cfg s t) :
    strong_universal_T_scfg_budgets_abort cfg source_alloc_limit target_alloc_limit s t :=
  fun es et inp hs ht hi _ => h es et inp hs ht hi

/-- Dropping the premise gives this direction at the shipped limits. -/
theorem strong_universal_error_free_T_scfg_budgets_of_scfg (cfg : SpuriousCfg) (s t : Image)
    (h : strong_universal_error_free_T_scfg cfg s t) :
    strong_universal_error_free_T_scfg_budgets cfg source_alloc_limit target_alloc_limit s t :=
  fun es et inp hs ht hi _ => h es et inp hs ht hi

/-- Dropping the premise gives this direction at the shipped limits. -/
theorem strong_universal_error_free_T_scfg_budgets_abort_of_scfg (cfg : SpuriousCfg) (s t : Image)
    (h : strong_universal_error_free_T_scfg_abort cfg s t) :
    strong_universal_error_free_T_scfg_budgets_abort cfg source_alloc_limit target_alloc_limit s t :=
  fun es et inp hs ht hi _ => h es et inp hs ht hi

theorem source_within_budget_scfg_may_fail (ls : Int) (s : Image) (en : ExecEntry) (inp : ProcInput) :
    source_within_budget_scfg may_fail_cfg ls s en inp ↔ source_within_budget ls s en inp :=
  not_congr (run_scfg_budget_refused_may_fail s ls en inp).symm

theorem dies_by_signal_scfg_may_fail (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    dies_by_signal (run_scfg may_fail_cfg img lim en inp) ↔ dies_by_signal (run img lim en inp) :=
  dies_by_signal_behavior_equiv _ _ (run_scfg_may_fail img lim en inp)

theorem error_free_unkilled_scfg_may_fail (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    error_free_unkilled (run_scfg may_fail_cfg img lim en inp) ↔ error_free_unkilled (run img lim en inp) :=
  and_congr (error_free_behavior_equiv _ _ (run_scfg_may_fail img lim en inp))
    (not_congr (dies_by_signal_scfg_may_fail img lim en inp))

theorem strong_equiv_budgets_scfg_may_fail (ls lt : Int) (s t : Image) (en_s en_t : ExecEntry) (inp : ProcInput) :
    strong_equiv_budgets_scfg may_fail_cfg ls lt s t en_s en_t inp ↔ strong_equiv_budgets ls lt s t en_s en_t inp := by
  have hs := run_scfg_may_fail s ls en_s inp
  have ht := run_scfg_may_fail t lt en_t inp
  exact and_congr (modeled_behavior_equiv _ _ hs) (equiv_behavior_equiv _ _ _ _ hs ht)

theorem strong_equiv_error_free_budgets_scfg_may_fail (ls lt : Int) (s t : Image) (en_s en_t : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_budgets_scfg may_fail_cfg ls lt s t en_s en_t inp ↔ strong_equiv_error_free_budgets ls lt s t en_s en_t inp := by
  have hs := run_scfg_may_fail s ls en_s inp
  have ht := run_scfg_may_fail t lt en_t inp
  exact and_congr (error_free_behavior_equiv _ _ hs)
    (and_congr (error_free_behavior_equiv _ _ ht) (trace_equiv_behavior_equiv _ _ _ _ hs ht))

theorem strong_equiv_error_free_budgets_scfg_abort_may_fail (ls lt : Int) (s t : Image) (en_s en_t : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_budgets_scfg_abort may_fail_cfg ls lt s t en_s en_t inp ↔ strong_equiv_error_free_budgets_abort ls lt s t en_s en_t inp := by
  have hs := run_scfg_may_fail s ls en_s inp
  have ht := run_scfg_may_fail t lt en_t inp
  exact and_congr (error_free_unkilled_scfg_may_fail s ls en_s inp)
    (and_congr (error_free_unkilled_scfg_may_fail t lt en_t inp) (trace_equiv_behavior_equiv _ _ _ _ hs ht))

theorem strong_universal_T_scfg_budgets_may_fail (ls lt : Int) (s t : Image) :
    strong_universal_T_scfg_budgets may_fail_cfg ls lt s t ↔ strong_universal_T_budgets ls lt s t :=
  ⟨fun h es et inp hs ht hi hb => (strong_equiv_budgets_scfg_may_fail ls lt s t es et inp).1
    (h es et inp hs ht hi ((source_within_budget_scfg_may_fail ls s es inp).2 hb)),
   fun h es et inp hs ht hi hb => (strong_equiv_budgets_scfg_may_fail ls lt s t es et inp).2
    (h es et inp hs ht hi ((source_within_budget_scfg_may_fail ls s es inp).1 hb))⟩

theorem strong_universal_T_scfg_budgets_abort_may_fail (ls lt : Int) (s t : Image) :
    strong_universal_T_scfg_budgets_abort may_fail_cfg ls lt s t ↔ strong_universal_T_budgets_abort ls lt s t :=
  ⟨fun h es et inp hs ht hi hb => (strong_equiv_budgets_scfg_may_fail ls lt s t es et inp).1
    (h es et inp hs ht hi ((source_within_budget_scfg_may_fail ls s es inp).2 hb)),
   fun h es et inp hs ht hi hb => (strong_equiv_budgets_scfg_may_fail ls lt s t es et inp).2
    (h es et inp hs ht hi ((source_within_budget_scfg_may_fail ls s es inp).1 hb))⟩

theorem strong_universal_error_free_T_scfg_budgets_may_fail (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_scfg_budgets may_fail_cfg ls lt s t ↔ strong_universal_error_free_T_budgets ls lt s t :=
  ⟨fun h es et inp hs ht hi hb => (strong_equiv_error_free_budgets_scfg_may_fail ls lt s t es et inp).1
    (h es et inp hs ht hi ((source_within_budget_scfg_may_fail ls s es inp).2 hb)),
   fun h es et inp hs ht hi hb => (strong_equiv_error_free_budgets_scfg_may_fail ls lt s t es et inp).2
    (h es et inp hs ht hi ((source_within_budget_scfg_may_fail ls s es inp).1 hb))⟩

theorem strong_universal_error_free_T_scfg_budgets_abort_may_fail (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_scfg_budgets_abort may_fail_cfg ls lt s t ↔ strong_universal_error_free_T_budgets_abort ls lt s t :=
  ⟨fun h es et inp hs ht hi hb => (strong_equiv_error_free_budgets_scfg_abort_may_fail ls lt s t es et inp).1
    (h es et inp hs ht hi ((source_within_budget_scfg_may_fail ls s es inp).2 hb)),
   fun h es et inp hs ht hi hb => (strong_equiv_error_free_budgets_scfg_abort_may_fail ls lt s t es et inp).2
    (h es et inp hs ht hi ((source_within_budget_scfg_may_fail ls s es inp).1 hb))⟩

/-- The conjunction keeps both input stances as obligations. -/
def strong_universal_T_budgets_either (ls lt : Int) (s t : Image) : Prop :=
  strong_universal_T_budgets ls lt s t ∧ strong_universal_T_budgets_abort ls lt s t

theorem strong_universal_T_budgets_either_off (ls lt : Int) (s t : Image)
    (h : strong_universal_T_budgets_either ls lt s t) : strong_universal_T_budgets ls lt s t := h.1

theorem strong_universal_T_budgets_either_abort (ls lt : Int) (s t : Image)
    (h : strong_universal_T_budgets_either ls lt s t) : strong_universal_T_budgets_abort ls lt s t := h.2

/-- The conjunction retains the stance-specific conclusion. -/
def strong_universal_error_free_T_budgets_either (ls lt : Int) (s t : Image) : Prop :=
  strong_universal_error_free_T_budgets ls lt s t ∧ strong_universal_error_free_T_budgets_abort ls lt s t

theorem strong_universal_error_free_T_budgets_either_off (ls lt : Int) (s t : Image)
    (h : strong_universal_error_free_T_budgets_either ls lt s t) : strong_universal_error_free_T_budgets ls lt s t := h.1

theorem strong_universal_error_free_T_budgets_either_abort (ls lt : Int) (s t : Image)
    (h : strong_universal_error_free_T_budgets_either ls lt s t) : strong_universal_error_free_T_budgets_abort ls lt s t := h.2

theorem strong_universal_T_budgets_either_splits (ls lt : Int) (s t : Image) :
    strong_universal_T_budgets_either ls lt s t ↔
      (∀ es et inp, valid_entry s es inp → valid_entry t et inp → valid_input_either inp →
        source_within_budget ls s es inp → strong_equiv_budgets ls lt s t es et inp) := by
  constructor
  · rintro ⟨hoff, hon⟩ es et inp hs ht hi hb
    rcases valid_input_either_splits inp hi with hi | hi
    · exact hoff es et inp hs ht hi hb
    · exact hon es et inp hs ht hi hb
  · intro h
    exact ⟨fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_either_of_valid_input inp hi) hb,
      fun es et inp hs ht hi hb => h es et inp hs ht (valid_input_either_of_valid_input_abort inp hi) hb⟩

theorem strong_universal_error_free_T_budgets_either_is_conj (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_budgets_either ls lt s t ↔
      strong_universal_error_free_T_budgets ls lt s t ∧ strong_universal_error_free_T_budgets_abort ls lt s t := Iff.rfl

theorem strong_universal_error_free_T_budgets_either_implies (ls lt : Int) (s t : Image)
    (h : strong_universal_error_free_T_budgets_either ls lt s t) :
    strong_universal_T_budgets_either ls lt s t :=
  ⟨strong_universal_error_free_T_budgets_implies ls lt s t h.1,
    strong_universal_error_free_T_budgets_abort_implies ls lt s t h.2⟩

/-- The fixed charge above 9/8 of the live heap is a runtime measurement
outside the model: start-up mappings, size-class metadata and quarantine. -/
def asan_fixed_overhead : Int := 261 * 1048576

/-- The sanitizer source limit reflects an external allocator-size-class
constraint and the roughly 2.5 GiB OSS-Fuzz RSS limit; it is not derived from runs. -/
def sanitizer_source_limit : Int := 0x80000000

/-- The 9/8 factor and the fixed charge are measurements, not a theorem
relating the two programs' allocations. -/
def budget_headroom_ok (lim_source lim_target : Int) : Bool :=
  decide (page_size ≤ lim_source) &&
    decide (9 * lim_source + 8 * asan_fixed_overhead ≤ 8 * lim_target)

theorem budget_headroom_ok_spec (lim_source lim_target : Int) :
    budget_headroom_ok lim_source lim_target = true ↔
      page_size ≤ lim_source ∧ 9 * lim_source + 8 * asan_fixed_overhead ≤ 8 * lim_target := by
  simp only [budget_headroom_ok, Bool.and_eq_true, decide_eq_true_eq]

theorem shipped_budgets_headroom :
    budget_headroom_ok source_alloc_limit target_alloc_limit = true := by decide

theorem sanitizer_budgets_headroom :
    budget_headroom_ok sanitizer_source_limit target_alloc_limit = true := by decide

theorem equal_budgets_fail_headroom :
    budget_headroom_ok source_alloc_limit source_alloc_limit = false := by decide

theorem zero_source_budget_fails_headroom :
    budget_headroom_ok 0 target_alloc_limit = false := by decide

theorem one_page_source_budget_passes_headroom :
    budget_headroom_ok page_size target_alloc_limit = true := by decide

/-- The budget pair a task states its claim under, with the side condition as a
field: no value of this structure exists for a pair that fails
`budget_headroom_ok`. Rocq declares it as the module type `BUDGETS`, a functor
argument of each sealing surface below; Lean passes the structure instead. -/
structure BUDGETS where
  /-- The limit the source run is seeded with. -/
  lim_source : Int
  /-- The limit the target run is seeded with. -/
  lim_target : Int
  /-- The side condition on the pair, closed by computation for concrete limits. -/
  headroom : budget_headroom_ok lim_source lim_target = true

/-- The shipped pair: the 16 GiB source limit and the 512 GiB target limit. -/
def ShippedBudgets : BUDGETS where
  lim_source := source_alloc_limit
  lim_target := target_alloc_limit
  headroom := shipped_budgets_headroom

/-- The sanitizer pair: the 2 GiB source limit against the unchanged target
limit. A claim proved at this pair is not implied by one proved at
`ShippedBudgets`, because the smaller source limit removes more inputs from the
premise. -/
def SanitizerBudgets : BUDGETS where
  lim_source := sanitizer_source_limit
  lim_target := target_alloc_limit
  headroom := sanitizer_budgets_headroom

/-- The two instances carry the same target limit. -/
theorem sanitizer_budgets_target_is_shipped :
    SanitizerBudgets.lim_target = ShippedBudgets.lim_target := rfl

/-- The sanitizer source limit is below the shipped source limit. -/
theorem sanitizer_source_budget_is_below_shipped :
    SanitizerBudgets.lim_source < ShippedBudgets.lim_source := by decide

/-- The unconfigured budget surface: the baseline statement at the pair's two
limits, abort stance off. -/
structure SPEC_BUDGETS (b : BUDGETS) (source target : Image) : Prop where
  strong_universal : strong_universal_T_budgets b.lim_source b.lim_target source target

/-- The unconfigured budget surface with the abort path declared. -/
structure SPEC_BUDGETS_ABORT (b : BUDGETS) (source target : Image) : Prop where
  strong_universal : strong_universal_T_budgets_abort b.lim_source b.lim_target source target

/-- The error-free unconfigured budget surface, abort stance off. -/
structure SPEC_ERROR_FREE_BUDGETS (b : BUDGETS) (source target : Image) : Prop where
  strong_universal_error_free :
    strong_universal_error_free_T_budgets b.lim_source b.lim_target source target

/-- The error-free unconfigured budget surface with the abort path declared. -/
structure SPEC_ERROR_FREE_BUDGETS_ABORT (b : BUDGETS) (source target : Image) : Prop where
  strong_universal_error_free :
    strong_universal_error_free_T_budgets_abort b.lim_source b.lim_target source target

/-- The unconfigured budget surface for inputs that declare the rv64gc
capability word, abort stance off. -/
structure SPEC_BUDGETS_HWCAP_RV64GC (b : BUDGETS) (source target : Image) : Prop where
  strong_universal :
    strong_universal_T_budgets_hwcap_rv64gc b.lim_source b.lim_target source target

/-- The unconfigured budget surface for inputs that declare the rv64gcv
capability word, abort stance off. -/
structure SPEC_BUDGETS_HWCAP_RV64GCV (b : BUDGETS) (source target : Image) : Prop where
  strong_universal :
    strong_universal_T_budgets_hwcap_rv64gcv b.lim_source b.lim_target source target

/-- The error-free unconfigured budget surface for inputs that declare the
rv64gc capability word, abort stance off. -/
structure SPEC_ERROR_FREE_BUDGETS_HWCAP_RV64GC (b : BUDGETS) (source target : Image) : Prop where
  strong_universal_error_free :
    strong_universal_error_free_T_budgets_hwcap_rv64gc b.lim_source b.lim_target source target

/-- The error-free unconfigured budget surface for inputs that declare the
rv64gcv capability word, abort stance off. -/
structure SPEC_ERROR_FREE_BUDGETS_HWCAP_RV64GCV (b : BUDGETS) (source target : Image) : Prop where
  strong_universal_error_free :
    strong_universal_error_free_T_budgets_hwcap_rv64gcv b.lim_source b.lim_target source target

/-- The unconfigured budget surface for inputs that declare the rv64gc
capability word, with the abort path declared. -/
structure SPEC_BUDGETS_ABORT_HWCAP_RV64GC (b : BUDGETS) (source target : Image) : Prop where
  strong_universal :
    strong_universal_T_budgets_abort_hwcap_rv64gc b.lim_source b.lim_target source target

/-- The unconfigured budget surface for inputs that declare the rv64gcv
capability word, with the abort path declared. -/
structure SPEC_BUDGETS_ABORT_HWCAP_RV64GCV (b : BUDGETS) (source target : Image) : Prop where
  strong_universal :
    strong_universal_T_budgets_abort_hwcap_rv64gcv b.lim_source b.lim_target source target

/-- The error-free unconfigured budget surface for inputs that declare the
rv64gc capability word, with the abort path declared. -/
structure SPEC_ERROR_FREE_BUDGETS_ABORT_HWCAP_RV64GC (b : BUDGETS) (source target : Image) : Prop where
  strong_universal_error_free :
    strong_universal_error_free_T_budgets_abort_hwcap_rv64gc b.lim_source b.lim_target source target

/-- The error-free unconfigured budget surface for inputs that declare the
rv64gcv capability word, with the abort path declared. -/
structure SPEC_ERROR_FREE_BUDGETS_ABORT_HWCAP_RV64GCV (b : BUDGETS) (source target : Image) : Prop where
  strong_universal_error_free :
    strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv b.lim_source b.lim_target source target

/-- The configured budget surface: the baseline statement under a
spurious-failure configuration at the pair's two limits, abort stance off. -/
structure SPEC_SCFG_BUDGETS (cfg : SpuriousCfg) (b : BUDGETS) (source target : Image) : Prop where
  strong_universal :
    strong_universal_T_scfg_budgets cfg b.lim_source b.lim_target source target

/-- The error-free configured budget surface, abort stance off. -/
structure SPEC_ERROR_FREE_SCFG_BUDGETS (cfg : SpuriousCfg) (b : BUDGETS) (source target : Image) : Prop where
  strong_universal_error_free :
    strong_universal_error_free_T_scfg_budgets cfg b.lim_source b.lim_target source target

/-- The configured budget surface for inputs that declare the rv64gc capability
word, abort stance off. -/
structure SPEC_SCFG_BUDGETS_HWCAP_RV64GC (cfg : SpuriousCfg) (b : BUDGETS) (source target : Image) : Prop where
  strong_universal :
    strong_universal_T_scfg_budgets_hwcap_rv64gc cfg b.lim_source b.lim_target source target

/-- The configured budget surface for inputs that declare the rv64gcv capability
word, abort stance off. -/
structure SPEC_SCFG_BUDGETS_HWCAP_RV64GCV (cfg : SpuriousCfg) (b : BUDGETS) (source target : Image) : Prop where
  strong_universal :
    strong_universal_T_scfg_budgets_hwcap_rv64gcv cfg b.lim_source b.lim_target source target

/-- The error-free configured budget surface for inputs that declare the rv64gc
capability word, abort stance off. -/
structure SPEC_ERROR_FREE_SCFG_BUDGETS_HWCAP_RV64GC (cfg : SpuriousCfg) (b : BUDGETS) (source target : Image) : Prop where
  strong_universal_error_free :
    strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc cfg b.lim_source b.lim_target source target

/-- The error-free configured budget surface for inputs that declare the rv64gcv
capability word, abort stance off. -/
structure SPEC_ERROR_FREE_SCFG_BUDGETS_HWCAP_RV64GCV (cfg : SpuriousCfg) (b : BUDGETS) (source target : Image) : Prop where
  strong_universal_error_free :
    strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv cfg b.lim_source b.lim_target source target

/-- The configured budget surface with the abort path declared. -/
structure SPEC_SCFG_BUDGETS_ABORT (cfg : SpuriousCfg) (b : BUDGETS) (source target : Image) : Prop where
  strong_universal :
    strong_universal_T_scfg_budgets_abort cfg b.lim_source b.lim_target source target

/-- The error-free configured budget surface with the abort path declared. -/
structure SPEC_ERROR_FREE_SCFG_BUDGETS_ABORT (cfg : SpuriousCfg) (b : BUDGETS) (source target : Image) : Prop where
  strong_universal_error_free :
    strong_universal_error_free_T_scfg_budgets_abort cfg b.lim_source b.lim_target source target

/-- The configured budget surface for inputs that declare the rv64gc capability
word, with the abort path declared. -/
structure SPEC_SCFG_BUDGETS_ABORT_HWCAP_RV64GC (cfg : SpuriousCfg) (b : BUDGETS) (source target : Image) : Prop where
  strong_universal :
    strong_universal_T_scfg_budgets_abort_hwcap_rv64gc cfg b.lim_source b.lim_target source target

/-- The configured budget surface for inputs that declare the rv64gcv capability
word, with the abort path declared. -/
structure SPEC_SCFG_BUDGETS_ABORT_HWCAP_RV64GCV (cfg : SpuriousCfg) (b : BUDGETS) (source target : Image) : Prop where
  strong_universal :
    strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv cfg b.lim_source b.lim_target source target

/-- The error-free configured budget surface for inputs that declare the rv64gc
capability word, with the abort path declared. -/
structure SPEC_ERROR_FREE_SCFG_BUDGETS_ABORT_HWCAP_RV64GC (cfg : SpuriousCfg) (b : BUDGETS) (source target : Image) : Prop where
  strong_universal_error_free :
    strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc cfg b.lim_source b.lim_target source target

/-- The error-free configured budget surface for inputs that declare the rv64gcv
capability word, with the abort path declared. -/
structure SPEC_ERROR_FREE_SCFG_BUDGETS_ABORT_HWCAP_RV64GCV (cfg : SpuriousCfg) (b : BUDGETS) (source target : Image) : Prop where
  strong_universal_error_free :
    strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv cfg b.lim_source b.lim_target source target

/-- The unconfigured budget surface with neither stance pinned: both readings are
obligations. -/
structure SPEC_BUDGETS_EITHER (b : BUDGETS) (source target : Image) : Prop where
  strong_universal :
    strong_universal_T_budgets_either b.lim_source b.lim_target source target

/-- The error-free unconfigured budget surface with neither stance pinned. -/
structure SPEC_ERROR_FREE_BUDGETS_EITHER (b : BUDGETS) (source target : Image) : Prop where
  strong_universal_error_free :
    strong_universal_error_free_T_budgets_either b.lim_source b.lim_target source target

end LinuxProcessSemantics.EquivalenceDefinition.Equivalence
