import LinuxProcessSemantics.EquivalenceDefinition.Equivalence
import LinuxProcessSemantics.EquivalenceDefinition.MustExit
import LinuxProcessSemantics.EquivalenceDefinition.FinInput
import LinuxProcessSemantics.LinuxProcessSem.StackLayout

/-! rocq-baseline: 1807c1e25ce12708f5cc85213f2df4bf03d978da -/

/-! # EquivalenceDefinition.Classifier — total deciders over finite inputs

Mirrors `theories/EquivalenceDefinition/Classifier.v`. The arguments for
finite inputs, per-entry verdicts, totality and the vacuity route stay in
that file's header, so there is one place to correct them.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.Classifier

open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.EquivalenceDefinition.FinInput

/-! ## The budget a classifier runs under -/

/-- The allocation budget every classifier run is seeded with: an alias
of the target role's budget, for the reason Rocq's `classifier_alloc_limit`
gives (bugs/vm-limit-environment-obligation.md records the environment
obligation it inherits). -/
def classifier_alloc_limit : Int := target_alloc_limit

/-! ## The classified properties -/

/-- Per-input agreement of two images run at one shared budget: trace
sets at all pairs of valid entries, and each of the three error facts as
an iff of existentials over valid entries. -/
def agree (X Y : Image) (lim : Int) (inp : ProcInput) : Prop :=
  (∀ enX enY,
     valid_entry X enX inp → valid_entry Y enY inp →
     trace_equiv (run X lim enX inp).bh_traces (run Y lim enY inp).bh_traces)
  ∧ ((∃ en, valid_entry X en inp ∧ (run X lim en inp).bh_errors)
      ↔ (∃ en, valid_entry Y en inp ∧ (run Y lim en inp).bh_errors))
  ∧ ((∃ en, valid_entry X en inp ∧ (run X lim en inp).bh_all_errors)
      ↔ (∃ en, valid_entry Y en inp ∧ (run Y lim en inp).bh_all_errors))
  ∧ ((∃ en, valid_entry X en inp ∧ (run X lim en inp).bh_unmodeled)
      ↔ (∃ en, valid_entry Y en inp ∧ (run Y lim en inp).bh_unmodeled))

/-- The inputs on which the two originals are already error-free
equivalent, at every pair of valid entries. -/
def good_input (O1 O2 : Image) (inp : ProcInput) : Prop :=
  ∀ en1 en2,
    valid_entry O1 en1 inp → valid_entry O2 en2 inp →
    strong_equiv_error_free O1 O2 en1 en2 inp

/-- The inputs on which one original is error-free at every valid entry,
at the source role's budget. -/
def error_free_input (O : Image) (inp : ProcInput) : Prop :=
  ∀ en, valid_entry O en inp → error_free (run O source_alloc_limit en inp)

/-! ## The two verdicts -/

def verdict_accept : word := Z_to_bv 64 0
def verdict_reject : word := Z_to_bv 64 1

/-! ## The classifier obligation -/

/-- `C` decides `spec` on every valid finite input, at every valid entry
of its own: exit 0 exactly on `spec`, and exit 0 or exit 1 always. -/
def decides (C : Image) (spec : ProcInput → Prop) : Prop :=
  ∀ f : FinProcInput,
    valid_fin_input f →
    ∀ en,
      valid_entry C en (to_proc_input f) →
      (must_exit_with verdict_accept C classifier_alloc_limit en (to_proc_input f)
         ↔ spec (to_proc_input f))
      ∧ (must_exit_with verdict_accept C classifier_alloc_limit en (to_proc_input f)
         ∨ must_exit_with verdict_reject C classifier_alloc_limit en (to_proc_input f))

/-- The totality conjunct of `decides`, on its own. -/
def classifier_total_T (Cl : Image) : Prop :=
  ∀ f : FinProcInput,
    valid_fin_input f →
    ∀ en,
      valid_entry Cl en (to_proc_input f) →
      must_exit_with verdict_accept Cl classifier_alloc_limit en (to_proc_input f)
      ∨ must_exit_with verdict_reject Cl classifier_alloc_limit en (to_proc_input f)

/-- `C` accepts exactly the inputs on which both original/patched pairs
agree, each pair at its own role's budget. -/
def classifies_patch_diff_T (O1 P1 O2 P2 C : Image) : Prop :=
  decides C (fun inp => agree O1 P1 source_alloc_limit inp
                        ∧ agree O2 P2 target_alloc_limit inp)

def classifies_good_inputs_T (O1 O2 C : Image) : Prop :=
  decides C (good_input O1 O2)

def classifies_error_free_inputs_T (O C : Image) : Prop :=
  decides C (error_free_input O)

/-! ## Acceptance and rejection of one finite input -/

/-- `C` exits 0 on `f` at every valid entry of its own. -/
def accepts (C : Image) (f : FinProcInput) : Prop :=
  ∀ en,
    valid_entry C en (to_proc_input f) →
    must_exit_with verdict_accept C classifier_alloc_limit en (to_proc_input f)

/-- A valid finite input `C` does not accept. -/
def rejects (C : Image) (f : FinProcInput) : Prop :=
  valid_fin_input f ∧ ¬ accepts C f

/-- An error at a valid entry disagrees with an image whose valid entries are error-free. -/
theorem agree_refuted_by_error_mismatch (X Y : Image) (lim : Int) (inp : ProcInput)
    (enX : ExecEntry) :
    valid_entry X enX inp → (run X lim enX inp).bh_errors →
    (∀ en, valid_entry Y en inp → ¬ (run Y lim en inp).bh_errors) →
    ¬ agree X Y lim inp := by
  intro hx herr hy h
  obtain ⟨en, hen, he⟩ := h.2.1.mp ⟨enX, hx, herr⟩
  exact hy en hen he

/-- A trace present at one valid entry and absent at another refutes self-agreement. -/
theorem agree_self_refuted_by_entry_leak (X : Image) (lim : Int) (inp : ProcInput)
    (en1 en2 : ExecEntry) (tr : List event) :
    valid_entry X en1 inp → valid_entry X en2 inp →
    (run X lim en1 inp).bh_traces tr → ¬ (run X lim en2 inp).bh_traces tr →
    ¬ agree X X lim inp := by
  intro h1 h2 hin hout h
  exact hout ((h.1 en1 en2 h1 h2 tr).mp hin)

/-- Agreement is symmetric in its two images. -/
theorem agree_sym (X Y : Image) (lim : Int) (inp : ProcInput) :
    agree X Y lim inp → agree Y X lim inp := by
  intro h
  exact ⟨fun ey ex hy hx tr => (h.1 ex ey hx hy tr).symm,
    h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

/-- An entry-less second image agrees with a first image lacking the three error facts. -/
theorem agree_vacuous_no_second_entries (X Y : Image) (lim : Int) (inp : ProcInput) :
    (∀ en, ¬ valid_entry Y en inp) →
    (∀ en, valid_entry X en inp → ¬ (run X lim en inp).bh_errors) →
    (∀ en, valid_entry X en inp → ¬ (run X lim en inp).bh_all_errors) →
    (∀ en, valid_entry X en inp → ¬ (run X lim en inp).bh_unmodeled) →
    agree X Y lim inp := by
  intro hy herr hall hun
  refine ⟨fun _ ey _ hey => (hy ey hey).elim, ?_, ?_, ?_⟩
  · exact ⟨fun ⟨en, hen, hb⟩ => (herr en hen hb).elim,
      fun ⟨en, hen, _⟩ => (hy en hen).elim⟩
  · exact ⟨fun ⟨en, hen, hb⟩ => (hall en hen hb).elim,
      fun ⟨en, hen, _⟩ => (hy en hen).elim⟩
  · exact ⟨fun ⟨en, hen, hb⟩ => (hun en hen hb).elim,
      fun ⟨en, hen, _⟩ => (hy en hen).elim⟩

/-- An entry-less first image agrees with a second image lacking the three error facts. -/
theorem agree_vacuous_no_first_entries (X Y : Image) (lim : Int) (inp : ProcInput) :
    (∀ en, ¬ valid_entry X en inp) →
    (∀ en, valid_entry Y en inp → ¬ (run Y lim en inp).bh_errors) →
    (∀ en, valid_entry Y en inp → ¬ (run Y lim en inp).bh_all_errors) →
    (∀ en, valid_entry Y en inp → ¬ (run Y lim en inp).bh_unmodeled) →
    agree X Y lim inp := by
  intro hx herr hall hun
  exact agree_sym Y X lim inp (agree_vacuous_no_second_entries Y X lim inp hx herr hall hun)

/-- Two images with no valid entries agree at the input. -/
theorem agree_vacuous_no_entries (X Y : Image) (lim : Int) (inp : ProcInput) :
    (∀ en, ¬ valid_entry X en inp) → (∀ en, ¬ valid_entry Y en inp) →
    agree X Y lim inp := by
  intro hx hy
  exact agree_vacuous_no_second_entries X Y lim inp hy
    (fun en hen => (hx en hen).elim) (fun en hen => (hx en hen).elim)
    (fun en hen => (hx en hen).elim)

/-- A source error at a valid entry pair refutes goodness of the input. -/
theorem good_input_refuted_by_source_error (O1 O2 : Image) (inp : ProcInput)
    (en1 en2 : ExecEntry) :
    valid_entry O1 en1 inp → valid_entry O2 en2 inp →
    (run O1 source_alloc_limit en1 inp).bh_errors → ¬ good_input O1 O2 inp := by
  intro h1 h2 herr hg
  exact (hg en1 en2 h1 h2).1 herr

/-- With no valid entry for the first image, the input is good vacuously. -/
theorem good_input_vacuous_no_first_entries (O1 O2 : Image) (inp : ProcInput) :
    (∀ en, ¬ valid_entry O1 en inp) → good_input O1 O2 inp := by
  intro h en1 _ h1 _
  exact (h en1 h1).elim

/-- With no valid entry for the second image, the input is good vacuously. -/
theorem good_input_vacuous_no_second_entries (O1 O2 : Image) (inp : ProcInput) :
    (∀ en, ¬ valid_entry O2 en inp) → good_input O1 O2 inp := by
  intro h _ en2 _ h2
  exact (h en2 h2).elim

/-- An error-free input gives modeled runs at its valid entries. -/
theorem error_free_input_modeled (O : Image) (inp : ProcInput) (en : ExecEntry) :
    error_free_input O inp → valid_entry O en inp → modeled (run O source_alloc_limit en inp) := by
  intro hef hen
  exact run_error_free_modeled _ _ _ _ (hef en hen)

/-- An error at a valid entry refutes error-freedom of the input. -/
theorem error_free_input_refuted_by_error (O : Image) (inp : ProcInput) (en : ExecEntry) :
    valid_entry O en inp → (run O source_alloc_limit en inp).bh_errors →
    ¬ error_free_input O inp := by
  intro hen herr hef
  exact hef en hen herr

/-- With no valid entries, the input is error-free vacuously. -/
theorem error_free_input_vacuous_no_entries (O : Image) (inp : ProcInput) :
    (∀ en, ¬ valid_entry O en inp) → error_free_input O inp := by
  intro h en hen
  exact (h en hen).elim

/-- Goodness of an image against itself implies error-freedom of the input. -/
theorem good_input_self_error_free_input (O : Image) (inp : ProcInput) :
    good_input O O inp → error_free_input O inp := by
  intro hg en hen
  exact (hg en en hen hen).1

/-- Goodness implies source error-freedom when the second image has a valid entry. -/
theorem good_input_error_free_input (O1 O2 : Image) (inp : ProcInput) (en2 : ExecEntry) :
    valid_entry O2 en2 inp → good_input O1 O2 inp → error_free_input O1 inp := by
  intro h2 hg en1 h1
  exact (hg en1 en2 h1 h2).1

/-- A missing second entry permits goodness alongside a source error. -/
theorem good_input_not_error_free_input (O1 O2 : Image) (inp : ProcInput) (en1 : ExecEntry) :
    (∀ en, ¬ valid_entry O2 en inp) → valid_entry O1 en1 inp →
    (run O1 source_alloc_limit en1 inp).bh_errors →
    good_input O1 O2 inp ∧ ¬ error_free_input O1 inp := by
  intro hno h1 herr
  exact ⟨good_input_vacuous_no_second_entries O1 O2 inp hno,
    error_free_input_refuted_by_error O1 inp en1 h1 herr⟩

/-- The two verdicts are different words. -/
theorem verdict_accept_neq_reject : verdict_accept ≠ verdict_reject := by decide

/-- A decision procedure satisfies the classifier totality obligation. -/
theorem decides_implies_total (C : Image) (spec : ProcInput → Prop) :
    decides C spec → classifier_total_T C := by
  intro h f hf en hen
  exact (h f hf en hen).2

/-- Acceptance at a valid entry produces a finite trace ending with the accepting exit. -/
theorem accepts_realizes (C : Image) (f : FinProcInput) (en : ExecEntry) :
    valid_entry C en (to_proc_input f) → accepts C f →
    ∃ tr fs, (run C classifier_alloc_limit en (to_proc_input f)).bh_traces
      (tr ++ [ExitEv verdict_accept fs]) := by
  intro hen ha
  exact must_exit_with_realizes _ _ _ _ _ (ha en hen)

/-- A valid entry without an accepting exit refutes acceptance. -/
theorem accepts_refuted_by_entry (C : Image) (f : FinProcInput) (en : ExecEntry) :
    valid_entry C en (to_proc_input f) →
    ¬ must_exit_with verdict_accept C classifier_alloc_limit en (to_proc_input f) →
    ¬ accepts C f := by
  intro hen hno ha
  exact hno (ha en hen)

/-- A rejecting exit at one valid entry establishes rejection of a valid finite input. -/
theorem rejects_by_exit1 (C : Image) (f : FinProcInput) (en : ExecEntry) :
    valid_fin_input f → valid_entry C en (to_proc_input f) →
    must_exit_with verdict_reject C classifier_alloc_limit en (to_proc_input f) → rejects C f := by
  intro hf hen h1
  exact ⟨hf, fun ha => verdict_accept_neq_reject
    (must_exit_with_exclusive _ _ _ _ _ _ (ha en hen) h1)⟩

/-- With no valid entries, the classifier accepts the input vacuously. -/
theorem accepts_vacuous_no_entries (C : Image) (f : FinProcInput) :
    (∀ en, ¬ valid_entry C en (to_proc_input f)) → accepts C f := by
  intro h en hen
  exact (h en hen).elim

/-- For a decider at a valid input and entry, exit 1 is equivalent to the property's negation. -/
theorem decides_exit1_iff (C : Image) (spec : ProcInput → Prop)
    (hdec : decides C spec) (f : FinProcInput) (en : ExecEntry) :
    valid_fin_input f → valid_entry C en (to_proc_input f) →
    (must_exit_with verdict_reject C classifier_alloc_limit en (to_proc_input f)
      ↔ ¬ spec (to_proc_input f)) := by
  intro hf hen
  obtain ⟨hiff, htot⟩ := hdec f hf en hen
  constructor
  · intro h1 hs
    exact verdict_accept_neq_reject
      (must_exit_with_exclusive _ _ _ _ _ _ (hiff.mpr hs) h1)
  · intro hns
    rcases htot with h0 | h1
    · exact (hns (hiff.mp h0)).elim
    · exact h1

/-- A decider's accepting verdict transfers between valid entries of a valid finite input. -/
theorem decides_verdict_entry_uniform (C : Image) (spec : ProcInput → Prop)
    (f : FinProcInput) (en1 en2 : ExecEntry) :
    decides C spec → valid_fin_input f →
    valid_entry C en1 (to_proc_input f) → valid_entry C en2 (to_proc_input f) →
    must_exit_with verdict_accept C classifier_alloc_limit en1 (to_proc_input f) →
    must_exit_with verdict_accept C classifier_alloc_limit en2 (to_proc_input f) := by
  intro hdec hf h1 h2 ha
  exact (hdec f hf en2 h2).1.mpr ((hdec f hf en1 h1).1.mp ha)

/-- For a decider with inhabited valid entries, acceptance is the classified property. -/
theorem decides_accepts_iff (C : Image) (spec : ProcInput → Prop)
    (hdec : decides C spec)
    (hinh : ∀ g, valid_fin_input g → ∃ en, valid_entry C en (to_proc_input g))
    (f : FinProcInput) : valid_fin_input f → (accepts C f ↔ spec (to_proc_input f)) := by
  intro hf
  obtain ⟨en, hen⟩ := hinh f hf
  exact ⟨fun ha => (hdec f hf en hen).1.mp (ha en hen),
    fun hs en' hen' => (hdec f hf en' hen').1.mpr hs⟩

/-- For a decider with inhabited valid entries, rejection is validity and the property's negation. -/
theorem decides_rejects_iff (C : Image) (spec : ProcInput → Prop)
    (hdec : decides C spec)
    (hinh : ∀ g, valid_fin_input g → ∃ en, valid_entry C en (to_proc_input g))
    (f : FinProcInput) :
    valid_fin_input f → (rejects C f ↔ valid_fin_input f ∧ ¬ spec (to_proc_input f)) := by
  intro hf
  have hacc := decides_accepts_iff C spec hdec hinh f hf
  exact ⟨fun ⟨hf', hna⟩ => ⟨hf', fun hs => hna (hacc.mpr hs)⟩,
    fun ⟨hf', hns⟩ => ⟨hf', fun ha => hns (hacc.mp ha)⟩⟩

/-- A decider with inhabited valid entries accepts or rejects each valid finite input. -/
theorem decides_accepts_or_rejects (C : Image) (spec : ProcInput → Prop) (f : FinProcInput) :
    decides C spec →
    (∀ g, valid_fin_input g → ∃ en, valid_entry C en (to_proc_input g)) →
    valid_fin_input f → accepts C f ∨ rejects C f := by
  intro hdec hinh hf
  obtain ⟨en, hen⟩ := hinh f hf
  rcases (hdec f hf en hen).2 with h0 | h1
  · exact Or.inl ((decides_accepts_iff C spec hdec hinh f hf).mpr
      ((hdec f hf en hen).1.mp h0))
  · exact Or.inr (rejects_by_exit1 C f en hf hen h1)

/-- A valid finite input and entry reaching neither verdict refutes classifier totality. -/
theorem classifier_total_T_refuted_by_undecided (Cl : Image) (f : FinProcInput) (en : ExecEntry) :
    valid_fin_input f → valid_entry Cl en (to_proc_input f) →
    ¬ must_exit_with verdict_accept Cl classifier_alloc_limit en (to_proc_input f) →
    ¬ must_exit_with verdict_reject Cl classifier_alloc_limit en (to_proc_input f) →
    ¬ classifier_total_T Cl := by
  intro hf hen h0 h1 htot
  exact (htot f hf en hen).elim h0 h1

/-- A classifier with no valid entries satisfies totality vacuously. -/
theorem classifier_total_T_vacuous_no_entries (Cl : Image) :
    (∀ f en, ¬ valid_entry Cl en (to_proc_input f)) → classifier_total_T Cl := by
  intro h f _ en hen
  exact (h f en hen).elim

/-- A valid finite input and entry reaching neither verdict refutes deciding the property. -/
theorem decides_refuted_by_undecided (C : Image) (spec : ProcInput → Prop)
    (f : FinProcInput) (en : ExecEntry) :
    valid_fin_input f → valid_entry C en (to_proc_input f) →
    ¬ must_exit_with verdict_accept C classifier_alloc_limit en (to_proc_input f) →
    ¬ must_exit_with verdict_reject C classifier_alloc_limit en (to_proc_input f) →
    ¬ decides C spec := by
  intro hf hen h0 h1 hdec
  exact classifier_total_T_refuted_by_undecided C f en hf hen h0 h1
    (decides_implies_total C spec hdec)

/-- Accepting a valid finite input outside the property refutes deciding it. -/
theorem decides_refuted_by_wrong_verdict (C : Image) (spec : ProcInput → Prop)
    (f : FinProcInput) (en : ExecEntry) :
    valid_fin_input f → valid_entry C en (to_proc_input f) →
    must_exit_with verdict_accept C classifier_alloc_limit en (to_proc_input f) →
    ¬ spec (to_proc_input f) → ¬ decides C spec := by
  intro hf hen h0 hns hdec
  exact hns ((hdec f hf en hen).1.mp h0)

/-- A classifier with no valid entries decides the property vacuously. -/
theorem decides_vacuous_no_entries (C : Image) (spec : ProcInput → Prop) :
    (∀ f en, ¬ valid_entry C en (to_proc_input f)) → decides C spec := by
  intro h f _ en hen
  exact (h f en hen).elim

/-- A classifier of error-free inputs exits 1 when the original has a valid erroring run. -/
theorem classifies_error_free_inputs_T_rejects_error (O C : Image) (f : FinProcInput)
    (en enC : ExecEntry) :
    classifies_error_free_inputs_T O C → valid_fin_input f →
    valid_entry O en (to_proc_input f) → (run O source_alloc_limit en (to_proc_input f)).bh_errors →
    valid_entry C enC (to_proc_input f) →
    must_exit_with verdict_reject C classifier_alloc_limit enC (to_proc_input f) := by
  intro hdec hf hen herr henC
  exact (decides_exit1_iff C (error_free_input O) hdec f enC hf henC).mpr
    (error_free_input_refuted_by_error O (to_proc_input f) en hen herr)

/-- A valid erroring original run places the input in its classifier's reject set. -/
theorem classifies_error_free_inputs_T_refutes_acceptance (O C : Image) (f : FinProcInput)
    (en enC : ExecEntry) :
    classifies_error_free_inputs_T O C → valid_fin_input f →
    valid_entry O en (to_proc_input f) → (run O source_alloc_limit en (to_proc_input f)).bh_errors →
    valid_entry C enC (to_proc_input f) → rejects C f := by
  intro hdec hf hen herr henC
  exact rejects_by_exit1 C f enC hf henC
    (classifies_error_free_inputs_T_rejects_error O C f en enC hdec hf hen herr henC)

/-- A classifier of error-free inputs accepts a valid finite error-free input. -/
theorem classifies_error_free_inputs_T_accepts_error_free (O C : Image) (f : FinProcInput) :
    classifies_error_free_inputs_T O C → valid_fin_input f →
    error_free_input O (to_proc_input f) → accepts C f := by
  intro hdec hf hef en hen
  exact (hdec f hf en hen).1.mpr hef

/-- Classifying an original with no valid entries accepts every valid finite input. -/
theorem classifies_error_free_inputs_T_vacuous_accepts_everything (O C : Image)
    (hdec : classifies_error_free_inputs_T O C)
    (hno : ∀ f en, ¬ valid_entry O en (to_proc_input f)) (f : FinProcInput) :
    valid_fin_input f → accepts C f := by
  intro hf
  exact classifies_error_free_inputs_T_accepts_error_free O C f hdec hf
    (error_free_input_vacuous_no_entries O (to_proc_input f) (hno f))

/-! ## The classified properties, under a configuration

The classifier runs under `forced_only_cfg`; the property it classifies uses
the task's configuration. At `may_fail_cfg` the configured properties recover
the unconfigured ones. Finite inputs, per-entry robustness, totality, and the
vacuity route through an entry-less image remain unchanged. -/

/-- Agreement under the task configuration compares traces at every valid entry pair and the three existential error facts. -/
def agree_s (cfg : SpuriousCfg) (X Y : Image) (lim : Int) (inp : ProcInput) : Prop :=
  (∀ enX enY,
     valid_entry X enX inp → valid_entry Y enY inp →
     trace_equiv (run_scfg cfg X lim enX inp).bh_traces (run_scfg cfg Y lim enY inp).bh_traces)
  ∧ ((∃ en, valid_entry X en inp ∧ (run_scfg cfg X lim en inp).bh_errors)
      ↔ (∃ en, valid_entry Y en inp ∧ (run_scfg cfg Y lim en inp).bh_errors))
  ∧ ((∃ en, valid_entry X en inp ∧ (run_scfg cfg X lim en inp).bh_all_errors)
      ↔ (∃ en, valid_entry Y en inp ∧ (run_scfg cfg Y lim en inp).bh_all_errors))
  ∧ ((∃ en, valid_entry X en inp ∧ (run_scfg cfg X lim en inp).bh_unmodeled)
      ↔ (∃ en, valid_entry Y en inp ∧ (run_scfg cfg Y lim en inp).bh_unmodeled))

/-- Good inputs make the originals error-free equivalent under the task configuration at every valid entry pair. -/
def good_input_s (cfg : SpuriousCfg) (O1 O2 : Image) (inp : ProcInput) : Prop :=
  ∀ en1 en2,
    valid_entry O1 en1 inp → valid_entry O2 en2 inp →
    strong_equiv_error_free_scfg cfg O1 O2 en1 en2 inp

/-- Allowing every spurious failure recovers unconfigured agreement. -/
theorem agree_s_may_fail (X Y : Image) (lim : Int) (inp : ProcInput) :
    agree_s may_fail_cfg X Y lim inp ↔ agree X Y lim inp := by
  have hf (P : behavior → Prop) (Z : Image)
      (hp : ∀ b b', behavior_equiv b b' → (P b ↔ P b')) :
      (∃ en, valid_entry Z en inp ∧ P (run_scfg may_fail_cfg Z lim en inp)) ↔
      (∃ en, valid_entry Z en inp ∧ P (run Z lim en inp)) :=
    ⟨fun ⟨en, hen, hb⟩ => ⟨en, hen, (hp _ _ (run_scfg_may_fail _ _ _ _)).mp hb⟩,
     fun ⟨en, hen, hb⟩ => ⟨en, hen, (hp _ _ (run_scfg_may_fail _ _ _ _)).mpr hb⟩⟩
  unfold agree_s agree
  apply and_congr
  · exact forall_congr' fun ex => forall_congr' fun ey =>
      imp_congr_right fun _ => imp_congr_right fun _ =>
        trace_equiv_behavior_equiv _ _ _ _ (run_scfg_may_fail X lim ex inp)
          (run_scfg_may_fail Y lim ey inp)
  · exact and_congr
      (iff_congr (hf behavior.bh_errors X (fun _ _ h => h.2.1))
        (hf behavior.bh_errors Y (fun _ _ h => h.2.1)))
      (and_congr
        (iff_congr (hf behavior.bh_all_errors X (fun _ _ h => h.2.2.1))
          (hf behavior.bh_all_errors Y (fun _ _ h => h.2.2.1)))
        (iff_congr (hf behavior.bh_unmodeled X (fun _ _ h => h.2.2.2))
          (hf behavior.bh_unmodeled Y (fun _ _ h => h.2.2.2))))

/-- Allowing every spurious failure recovers unconfigured goodness. -/
theorem good_input_s_may_fail (O1 O2 : Image) (inp : ProcInput) :
    good_input_s may_fail_cfg O1 O2 inp ↔ good_input O1 O2 inp :=
  ⟨fun h en1 en2 h1 h2 => (strong_equiv_error_free_scfg_may_fail _ _ _ _ _).mp
      (h en1 en2 h1 h2),
   fun h en1 en2 h1 h2 => (strong_equiv_error_free_scfg_may_fail _ _ _ _ _).mpr
      (h en1 en2 h1 h2)⟩

/-- Configured agreement is symmetric in its two images. -/
theorem agree_s_sym (cfg : SpuriousCfg) (X Y : Image) (lim : Int) (inp : ProcInput) :
    agree_s cfg X Y lim inp → agree_s cfg Y X lim inp := by
  intro h
  exact ⟨fun ey ex hy hx tr => (h.1 ex ey hx hy tr).symm,
    h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

/-- `good_input_s` bites under every configuration, for the reason
`good_input` does: one erroring resolution of the first original
under `cfg`, at one valid entry pair, refutes it. -/
theorem good_input_s_refuted_by_source_error (cfg : SpuriousCfg) (O1 O2 : Image) (inp : ProcInput)
    (en1 en2 : ExecEntry) :
    valid_entry O1 en1 inp → valid_entry O2 en2 inp →
    (run_scfg cfg O1 source_alloc_limit en1 inp).bh_errors → ¬ good_input_s cfg O1 O2 inp := by
  intro h1 h2 herr hg
  exact (hg en1 en2 h1 h2).1 herr

/-- `decides` with the classifier's own run under `Run.forced_only_cfg`:
the same two conjuncts, the same quantifiers, the verdict predicate
`MustExit.must_exit_with_scfg forced_only_cfg` in place of
`MustExit.must_exit_with`.  `spec` is still a predicate on
`State.ProcInput`, and still evaluated wherever the task says —
`classifies_patch_diff_T_s` and `classifies_good_inputs_T_s` pass it
a property under the task's configuration. -/
def decides_fo (C : Image) (spec : ProcInput → Prop) : Prop :=
  ∀ f : FinProcInput,
    valid_fin_input f →
    ∀ en,
      valid_entry C en (to_proc_input f) →
      (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
         ↔ spec (to_proc_input f))
      ∧ (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
         ∨ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f))

/-- The forced-only classifier terminates with exit zero or one at every valid finite input and entry. -/
def classifier_total_T_fo (Cl : Image) : Prop :=
  ∀ f : FinProcInput,
    valid_fin_input f →
    ∀ en,
      valid_entry Cl en (to_proc_input f) →
      must_exit_with_scfg forced_only_cfg verdict_accept Cl classifier_alloc_limit en (to_proc_input f)
      ∨ must_exit_with_scfg forced_only_cfg verdict_reject Cl classifier_alloc_limit en (to_proc_input f)

/-- A forced-only decider satisfies the forced-only totality obligation. -/
theorem decides_fo_implies_total (C : Image) (spec : ProcInput → Prop) :
    decides_fo C spec → classifier_total_T_fo C := by
  intro h f hf en hen
  exact (h f hf en hen).2

/-- The two task-facing obligations: the property under the task's
configuration `cfg`, the classifier under forced-only. -/
def classifies_patch_diff_T_s (cfg : SpuriousCfg) (O1 P1 O2 P2 C : Image) : Prop :=
  decides_fo C (fun inp => agree_s cfg O1 P1 source_alloc_limit inp
                        ∧ agree_s cfg O2 P2 target_alloc_limit inp)

/-- The forced-only classifier decides goodness under the task configuration. -/
def classifies_good_inputs_T_s (cfg : SpuriousCfg) (O1 O2 C : Image) : Prop :=
  decides_fo C (good_input_s cfg O1 O2)

/-- `decides_fo` with the task's AT_HWCAP declaration as a hypothesis on
the input, in the shape `Run.valid_input_hwcap_rv64gc` gives the
equivalence layer.  THE CLASSIFIER BINARIES TAKE THE SAME PROBE as
the binaries they classify: a classifier that reads `vlenb` to learn
whether it has a vector unit executes, under an advertised V, a word
the model declines (`Run.valid_input_hwcap_rv64gc`'s comment and
`Checks.Cases.Hwcap` carry the mechanism), so its run is
`Run.MachineUnmodeled`, no `MustExit.must_exit_with_scfg` holds of it
and the undeclared obligation is FALSE.  Declaring is how such a task
states what it can prove.

THE HYPOTHESIS IS ON `to_proc_input f`, not on a new `FinProcInput`
field predicate, and deliberately: `FinInput.to_proc_input` carries
`fin_hwcap` into `in_hwcap` unchanged, so the equation here is the
same claim `Run.valid_input_hwcap_rv64gc` makes about the input the
equivalence layer quantifies over, and a task whose classifier
statement and equivalence statement both declare is declaring one
thing rather than two that happen to agree.

`decides` -- the unconfigured obligation -- gets NO declared twin.
Every task that needs one is stated under a configuration
(`decides_fo_of_decides` carries a proof of the stronger one into
this shape), so a twin there would be a definition nothing
quantifies over. -/
def decides_fo_hwcap_rv64gc (C : Image) (spec : ProcInput → Prop) : Prop :=
  ∀ f : FinProcInput,
    valid_fin_input f →
    (to_proc_input f).in_hwcap = hwcap_rv64gc →
    ∀ en,
      valid_entry C en (to_proc_input f) →
      (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
         ↔ spec (to_proc_input f))
      ∧ (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
         ∨ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f))

/-- The forced-only decision obligation restricted to inputs declaring RV64GCV; the declaration is on the denoted input. -/
def decides_fo_hwcap_rv64gcv (C : Image) (spec : ProcInput → Prop) : Prop :=
  ∀ f : FinProcInput,
    valid_fin_input f →
    (to_proc_input f).in_hwcap = hwcap_rv64gcv →
    ∀ en,
      valid_entry C en (to_proc_input f) →
      (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
         ↔ spec (to_proc_input f))
      ∧ (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
         ∨ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f))

/-- Each declaration is a NARROWING: the undeclared obligation answers
every input either declared one does. -/
theorem decides_fo_hwcap_rv64gc_of_decides_fo (C : Image) (spec : ProcInput → Prop) :
    decides_fo C spec → decides_fo_hwcap_rv64gc C spec :=
  fun h f hf _ en hen => h f hf en hen

/-- An undeclared forced-only decider also decides on the RV64GCV inputs. -/
theorem decides_fo_hwcap_rv64gcv_of_decides_fo (C : Image) (spec : ProcInput → Prop) :
    decides_fo C spec → decides_fo_hwcap_rv64gcv C spec :=
  fun h f hf _ en hen => h f hf en hen

/-- …and the two are EXACTLY the undeclared obligation, because
`valid_fin_input` IS `Run.valid_input` of the denoted input
(`FinInput.valid_fin_input`) and its capability clause is the
two-word disjunction.  This is what makes declaring a restriction on
the task rather than a weakening of the grader: proving both
declared obligations proves the undeclared one, so a task that says
nothing about its hart is held to both readings. -/
theorem decides_fo_hwcap_splits (C : Image) (spec : ProcInput → Prop) :
    decides_fo C spec ↔ (decides_fo_hwcap_rv64gc C spec ∧ decides_fo_hwcap_rv64gcv C spec) := by
  constructor
  · exact fun h => ⟨decides_fo_hwcap_rv64gc_of_decides_fo C spec h,
      decides_fo_hwcap_rv64gcv_of_decides_fo C spec h⟩
  · intro h f hf en hen
    rcases valid_input_hwcap (to_proc_input f) hf with hw | hw
    · exact h.1 f hf hw en hen
    · exact h.2 f hf hw en hen

/-- The declared obligation still implies totality on the inputs it
speaks about, which is the half a consumer reads first. -/
theorem decides_fo_hwcap_rv64gc_total (C : Image) (spec : ProcInput → Prop)
    (f : FinProcInput) (en : ExecEntry) :
    decides_fo_hwcap_rv64gc C spec → valid_fin_input f →
    (to_proc_input f).in_hwcap = hwcap_rv64gc → valid_entry C en (to_proc_input f) →
    must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
    ∨ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f) :=
  fun h hf hw hen => (h f hf hw en hen).2

/-- The RV64GCV obligation requires totality at valid inputs carrying that declaration. -/
theorem decides_fo_hwcap_rv64gcv_total (C : Image) (spec : ProcInput → Prop)
    (f : FinProcInput) (en : ExecEntry) :
    decides_fo_hwcap_rv64gcv C spec → valid_fin_input f →
    (to_proc_input f).in_hwcap = hwcap_rv64gcv → valid_entry C en (to_proc_input f) →
    must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
    ∨ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f) :=
  fun h hf hw hen => (h f hf hw en hen).2

/-- The two task-facing obligations of this section, declared.  Same
substitution as the undeclared pair above, so a task reads down the
column its declaration names. -/
def classifies_patch_diff_T_s_hwcap_rv64gc (cfg : SpuriousCfg) (O1 P1 O2 P2 C : Image) : Prop :=
  decides_fo_hwcap_rv64gc C (fun inp => agree_s cfg O1 P1 source_alloc_limit inp
                        ∧ agree_s cfg O2 P2 target_alloc_limit inp)

/-- The forced-only classifier decides both configured agreements on inputs declaring RV64GCV. -/
def classifies_patch_diff_T_s_hwcap_rv64gcv (cfg : SpuriousCfg) (O1 P1 O2 P2 C : Image) : Prop :=
  decides_fo_hwcap_rv64gcv C (fun inp => agree_s cfg O1 P1 source_alloc_limit inp
                        ∧ agree_s cfg O2 P2 target_alloc_limit inp)

/-- The forced-only classifier decides configured goodness on inputs declaring RV64GC. -/
def classifies_good_inputs_T_s_hwcap_rv64gc (cfg : SpuriousCfg) (O1 O2 C : Image) : Prop :=
  decides_fo_hwcap_rv64gc C (good_input_s cfg O1 O2)

/-- The forced-only classifier decides configured goodness on inputs declaring RV64GCV. -/
def classifies_good_inputs_T_s_hwcap_rv64gcv (cfg : SpuriousCfg) (O1 O2 C : Image) : Prop :=
  decides_fo_hwcap_rv64gcv C (good_input_s cfg O1 O2)

/-- Configured patch classification is exactly the conjunction of its two capability declarations. -/
theorem classifies_patch_diff_T_s_hwcap_splits (cfg : SpuriousCfg) (O1 P1 O2 P2 C : Image) :
    classifies_patch_diff_T_s cfg O1 P1 O2 P2 C ↔
    (classifies_patch_diff_T_s_hwcap_rv64gc cfg O1 P1 O2 P2 C ∧ classifies_patch_diff_T_s_hwcap_rv64gcv cfg O1 P1 O2 P2 C) :=
  decides_fo_hwcap_splits _ _

/-- Configured good-input classification is exactly the conjunction of its two capability declarations. -/
theorem classifies_good_inputs_T_s_hwcap_splits (cfg : SpuriousCfg) (O1 O2 C : Image) :
    classifies_good_inputs_T_s cfg O1 O2 C ↔
    (classifies_good_inputs_T_s_hwcap_rv64gc cfg O1 O2 C ∧ classifies_good_inputs_T_s_hwcap_rv64gcv cfg O1 O2 C) :=
  decides_fo_hwcap_splits _ _

/-- The classifier exits zero under forced-only at every valid entry of the finite input. -/
def accepts_fo (C : Image) (f : FinProcInput) : Prop :=
  ∀ en,
    valid_entry C en (to_proc_input f) →
    must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)

/-- A valid finite input the forced-only classifier does not accept. -/
def rejects_fo (C : Image) (f : FinProcInput) : Prop :=
  valid_fin_input f ∧ ¬ accepts_fo C f

/-- Acceptance under the pin is still a claim about the REAL program:
the accepting run emits `State.ExitEv` carrying `verdict_accept` in
the UNFILTERED run, by `MustExit.must_exit_with_scfg_realizes_run`.
The filter removed resolutions; it did not invent the verdict. -/
theorem accepts_fo_realizes (C : Image) (f : FinProcInput) (en : ExecEntry) :
    valid_entry C en (to_proc_input f) → accepts_fo C f →
    ∃ tr fs, (run C classifier_alloc_limit en (to_proc_input f)).bh_traces
      (tr ++ [ExitEv verdict_accept fs]) := by
  intro hen ha
  exact must_exit_with_scfg_realizes_run _ _ _ _ _ _ (ha en hen)

/-- One valid entry without a forced-only accepting exit refutes acceptance. -/
theorem accepts_fo_refuted_by_entry (C : Image) (f : FinProcInput) (en : ExecEntry) :
    valid_entry C en (to_proc_input f) →
    ¬ must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f) →
    ¬ accepts_fo C f := by
  intro hen hno ha
  exact hno (ha en hen)

/-- A forced-only rejecting exit at one valid entry establishes rejection of a valid finite input. -/
theorem rejects_fo_by_exit1 (C : Image) (f : FinProcInput) (en : ExecEntry) :
    valid_fin_input f → valid_entry C en (to_proc_input f) →
    must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f) → rejects_fo C f := by
  intro hf hen h1
  exact ⟨hf, fun ha => verdict_accept_neq_reject
    (must_exit_with_scfg_exclusive _ _ _ _ _ _ _ (ha en hen) h1)⟩

/-- With no valid entries, forced-only acceptance holds vacuously. -/
theorem accepts_fo_vacuous_no_entries (C : Image) (f : FinProcInput) :
    (∀ en, ¬ valid_entry C en (to_proc_input f)) → accepts_fo C f := by
  intro h en hen
  exact (h en hen).elim

/-- At a valid input and entry, a forced-only decider exits one exactly when the property fails. -/
theorem decides_fo_exit1_iff (C : Image) (spec : ProcInput → Prop)
    (hdec : decides_fo C spec) (f : FinProcInput) (en : ExecEntry) :
    valid_fin_input f → valid_entry C en (to_proc_input f) →
    (must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f)
      ↔ ¬ spec (to_proc_input f)) := by
  intro hf hen
  obtain ⟨hiff, htot⟩ := hdec f hf en hen
  constructor
  · intro h1 hs
    exact verdict_accept_neq_reject
      (must_exit_with_scfg_exclusive _ _ _ _ _ _ _ (hiff.mpr hs) h1)
  · intro hns
    rcases htot with h0 | h1
    · exact (hns (hiff.mp h0)).elim
    · exact h1

/-- A forced-only decider gives the same accepting verdict at all valid entries of a valid finite input. -/
theorem decides_fo_verdict_entry_uniform (C : Image) (spec : ProcInput → Prop)
    (f : FinProcInput) (en1 en2 : ExecEntry) :
    decides_fo C spec → valid_fin_input f →
    valid_entry C en1 (to_proc_input f) → valid_entry C en2 (to_proc_input f) →
    must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en1 (to_proc_input f) →
    must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en2 (to_proc_input f) := by
  intro hdec hf h1 h2 ha
  exact (hdec f hf en2 h2).1.mpr ((hdec f hf en1 h1).1.mp ha)

/-- The `_fo` twins of the three transfer lemmas, and the
inhabited-entry hypothesis is stated AT THE VALID INPUTS here for
the reason `decides_accepts_iff` gives at length: the unrestricted
`forall g, exists en, valid_entry C en (to_proc_input g)` is false
for every image
(`Checks.EntryStackFits.no_image_has_an_entry_for_every_input`), so
a lemma taking it would typecheck and never be applicable.  Each
proof instantiates the hypothesis only at an `f` it already holds
`FinInput.valid_fin_input` for. -/
theorem decides_fo_accepts_iff (C : Image) (spec : ProcInput → Prop)
    (hdec : decides_fo C spec)
    (hinh : ∀ g, valid_fin_input g → ∃ en, valid_entry C en (to_proc_input g))
    (f : FinProcInput) : valid_fin_input f → (accepts_fo C f ↔ spec (to_proc_input f)) := by
  intro hf
  obtain ⟨en, hen⟩ := hinh f hf
  exact ⟨fun ha => (hdec f hf en hen).1.mp (ha en hen),
    fun hs en' hen' => (hdec f hf en' hen').1.mpr hs⟩

/-- With inhabited entries at valid inputs, forced-only rejection is validity and the classified property’s negation. -/
theorem decides_fo_rejects_iff (C : Image) (spec : ProcInput → Prop)
    (hdec : decides_fo C spec)
    (hinh : ∀ g, valid_fin_input g → ∃ en, valid_entry C en (to_proc_input g))
    (f : FinProcInput) :
    valid_fin_input f → (rejects_fo C f ↔ valid_fin_input f ∧ ¬ spec (to_proc_input f)) := by
  intro hf
  have hacc := decides_fo_accepts_iff C spec hdec hinh f hf
  exact ⟨fun ⟨hf', hna⟩ => ⟨hf', fun hs => hna (hacc.mpr hs)⟩,
    fun ⟨hf', hns⟩ => ⟨hf', fun ha => hns (hacc.mp ha)⟩⟩

/-- With inhabited entries at valid inputs, a forced-only decider accepts or rejects every valid finite input. -/
theorem decides_fo_accepts_or_rejects (C : Image) (spec : ProcInput → Prop) (f : FinProcInput) :
    decides_fo C spec →
    (∀ g, valid_fin_input g → ∃ en, valid_entry C en (to_proc_input g)) →
    valid_fin_input f → accepts_fo C f ∨ rejects_fo C f := by
  intro hdec hinh hf
  obtain ⟨en, hen⟩ := hinh f hf
  rcases (hdec f hf en hen).2 with h0 | h1
  · exact Or.inl ((decides_fo_accepts_iff C spec hdec hinh f hf).mpr
      ((hdec f hf en hen).1.mp h0))
  · exact Or.inr (rejects_fo_by_exit1 C f en hf hen h1)

/-- A valid finite input and entry reaching neither forced-only verdict refutes totality. -/
theorem classifier_total_T_fo_refuted_by_undecided (Cl : Image) (f : FinProcInput) (en : ExecEntry) :
    valid_fin_input f → valid_entry Cl en (to_proc_input f) →
    ¬ must_exit_with_scfg forced_only_cfg verdict_accept Cl classifier_alloc_limit en (to_proc_input f) →
    ¬ must_exit_with_scfg forced_only_cfg verdict_reject Cl classifier_alloc_limit en (to_proc_input f) →
    ¬ classifier_total_T_fo Cl := by
  intro hf hen h0 h1 htot
  exact (htot f hf en hen).elim h0 h1

/-- A classifier without valid entries satisfies forced-only totality vacuously. -/
theorem classifier_total_T_fo_vacuous_no_entries (Cl : Image) :
    (∀ f en, ¬ valid_entry Cl en (to_proc_input f)) → classifier_total_T_fo Cl := by
  intro h f _ en hen
  exact (h f en hen).elim

/-- A valid finite input and entry reaching neither forced-only verdict refutes deciding any property. -/
theorem decides_fo_refuted_by_undecided (C : Image) (spec : ProcInput → Prop)
    (f : FinProcInput) (en : ExecEntry) :
    valid_fin_input f → valid_entry C en (to_proc_input f) →
    ¬ must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f) →
    ¬ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f) →
    ¬ decides_fo C spec := by
  intro hf hen h0 h1 hdec
  exact classifier_total_T_fo_refuted_by_undecided C f en hf hen h0 h1
    (decides_fo_implies_total C spec hdec)

/-- A forced-only accepting exit outside the property refutes deciding it. -/
theorem decides_fo_refuted_by_wrong_verdict (C : Image) (spec : ProcInput → Prop)
    (f : FinProcInput) (en : ExecEntry) :
    valid_fin_input f → valid_entry C en (to_proc_input f) →
    must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f) →
    ¬ spec (to_proc_input f) → ¬ decides_fo C spec := by
  intro hf hen h0 hns hdec
  exact hns ((hdec f hf en hen).1.mp h0)

/-- A classifier without valid entries decides every property vacuously under forced-only. -/
theorem decides_fo_vacuous_no_entries (C : Image) (spec : ProcInput → Prop) :
    (∀ f en, ¬ valid_entry C en (to_proc_input f)) → decides_fo C spec := by
  intro h f _ en hen
  exact (h f en hen).elim

/-- The filter's question is answered on every run of `C` the
obligations quantify over: every valid finite input, every valid
entry.  This is `MustExit.run_decided` at the classifier's own
budget, and it is the premise under which the three lemmas below
say that what `decides` certifies, `decides_fo` certifies too — so
pinning the classifier to forced-only asks for LESS, never for
something else.  See the KNOWN GAP in `Run.v`'s spurious-failure
section for why it is a premise. -/
def classifier_decided (C : Image) : Prop :=
  ∀ f en, valid_fin_input f → valid_entry C en (to_proc_input f) →
    run_decided forced_only_cfg C classifier_alloc_limit en (to_proc_input f)

/-- When the filter question is answered, unconfigured acceptance implies forced-only acceptance. -/
theorem accepts_fo_of_accepts (C : Image) (f : FinProcInput) :
    classifier_decided C → valid_fin_input f → accepts C f → accepts_fo C f :=
  fun hd hf ha en hen => must_exit_with_scfg_of_must_exit_with _ _ _ _ _ _
    (hd f en hf hen) (ha en hen)

/-- When the filter question is answered, forced-only rejection implies unconfigured rejection. -/
theorem rejects_of_rejects_fo (C : Image) (f : FinProcInput) :
    classifier_decided C → rejects_fo C f → rejects C f :=
  fun hd ⟨hf, hna⟩ => ⟨hf, fun ha => hna (accepts_fo_of_accepts C f hd hf ha)⟩

/-- When the filter question is answered, an unconfigured decider is also a forced-only decider. -/
theorem decides_fo_of_decides (C : Image) (spec : ProcInput → Prop) :
    classifier_decided C → decides C spec → decides_fo C spec := by
  intro hd h f hf en hen
  obtain ⟨hi, ht⟩ := h f hf en hen
  have ha := must_exit_with_scfg_of_must_exit_with forced_only_cfg verdict_accept
    C classifier_alloc_limit en (to_proc_input f) (hd f en hf hen)
  have hr := must_exit_with_scfg_of_must_exit_with forced_only_cfg verdict_reject
    C classifier_alloc_limit en (to_proc_input f) (hd f en hf hen)
  refine ⟨⟨?_, fun hs => ha (hi.mpr hs)⟩, ht.imp ha hr⟩
  intro hfo
  rcases ht with h0 | h1
  · exact hi.mp h0
  · exact (verdict_accept_neq_reject
      (must_exit_with_scfg_exclusive _ _ _ _ _ _ _ hfo (hr h1))).elim

/-- The `_s` twin of `error_free_input`, and it is the same edit the two
properties above take: `Run.run_scfg cfg` in place of `Run.run`,
nothing else moved.  It stays, conjunct for conjunct, the SOURCE
SIDE of `Equivalence.strong_equiv_error_free_scfg` with the entry
universally quantified — the relation this variant's two slice
programs are judged by under the task's configuration — exactly as
the unparameterized form is that of
`Equivalence.strong_equiv_error_free`.

Which configuration this is evaluated under is the task's, not the
gate's, for the reason this section's header gives: an original
judged under may-fail must be sorted by may-fail error-freedom, or
the regions would be carved by a different notion of "buggy" from
the one the slice obligations are stated under. -/
def error_free_input_s (cfg : SpuriousCfg) (O : Image) (inp : ProcInput) : Prop :=
  ∀ en, valid_entry O en inp → error_free (run_scfg cfg O source_alloc_limit en inp)

/-- At `Run.may_fail_cfg` it is the property above, which is what lets
the unparameterized statements keep their text.  Through
`Run.run_scfg_may_fail`, the same route `agree_s_may_fail` and
`good_input_s_may_fail` take. -/
theorem error_free_input_s_may_fail (O : Image) (inp : ProcInput) :
    error_free_input_s may_fail_cfg O inp ↔ error_free_input O inp :=
  ⟨fun h en hen herr => h en hen ((run_scfg_may_fail _ _ _ _).2.1.mpr herr),
   fun h en hen herr => h en hen ((run_scfg_may_fail _ _ _ _).2.1.mp herr)⟩

/-- Turning a family OFF cannot make an original buggy: fewer executions
cannot add an error, so error-freedom is inherited downward from
the may-fail reading, `Equivalence.error_free_scfg_of_error_free`
under the entry quantifier.  The converse fails, and that is the
point of parameterising rather than fixing a configuration — an
original that only faults on a refused `openat` is not-buggy under
forced-only and buggy under may-fail, and the two configurations
therefore draw the region boundary in different places. -/
theorem error_free_input_s_of_error_free_input (cfg : SpuriousCfg) (O : Image) (inp : ProcInput) :
    error_free_input O inp → error_free_input_s cfg O inp :=
  fun h en hen => error_free_scfg_of_error_free _ _ _ _ _ (h en hen)

/-- ... and it BITES under every configuration, exactly as the
unparameterized form does: one erroring resolution, at one valid
entry, of the run `cfg` permits.  Which resolutions those are is what
`cfg` decides, and that is the whole content of parameterising —
the refutation is the same shape at every configuration and lands on
a different set of inputs at each. -/
theorem error_free_input_s_refuted_by_error (cfg : SpuriousCfg) (O : Image) (inp : ProcInput) (en : ExecEntry) :
    valid_entry O en inp → (run_scfg cfg O source_alloc_limit en inp).bh_errors →
    ¬ error_free_input_s cfg O inp := by
  intro hen herr hef
  exact hef en hen herr

/-- The vacuity route survives the parameterisation untouched, because
it runs through the ENTRY quantifier and not through the run: an
original with no valid entry is error-free under every `cfg`, having
executed nothing.  Turning families off cannot repair an empty
range any more than strengthening what sits under it can. -/
theorem error_free_input_s_vacuous_no_entries (cfg : SpuriousCfg) (O : Image) (inp : ProcInput) :
    (∀ en, ¬ valid_entry O en inp) → error_free_input_s cfg O inp := by
  intro h en hen
  exact (h en hen).elim

/-- Coverage, under a configuration: `Run.run_scfg_unmodeled_errors` is
the `_scfg` image of `Equivalence.run_unmodeled_errors`, so
error-freedom subsumes `Equivalence.modeled` here for the reason it
does there, and `Equivalence.strong_equiv_error_free_scfg` carries
no `Equivalence.modeled` conjunct for the same reason. -/
theorem error_free_input_s_modeled (cfg : SpuriousCfg) (O : Image) (inp : ProcInput)
    (en : ExecEntry) :
    error_free_input_s cfg O inp → valid_entry O en inp →
    modeled (run_scfg cfg O source_alloc_limit en inp) :=
  fun hef hen hun => hef en hen (run_scfg_unmodeled_errors _ _ _ _ _ hun)

/-- The positive relation to `good_input_s`, the `_s` twin of
`good_input_self_error_free_input` and the same one-line argument:
instantiate both entry quantifiers at the same entry and take the
first conjunct of `Equivalence.strong_equiv_error_free_scfg`.  So
the two gates of the family agree where they overlap under EVERY
configuration, not only under may-fail. -/
theorem good_input_s_self_error_free_input_s (cfg : SpuriousCfg) (O : Image) (inp : ProcInput) :
    good_input_s cfg O O inp → error_free_input_s cfg O inp := by
  intro hg en hen
  exact (hg en en hen hen).1

/-- The task-facing obligation: the property under the task's
configuration `cfg`, the gate itself under
`Run.forced_only_cfg`.  Same split as
`classifies_patch_diff_T_s` and `classifies_good_inputs_T_s`, and
for the same reason — a gate is asked to DECIDE, so its own reads
must not be refusable without cause, while what it decides is the
task's question. -/
def classifies_error_free_inputs_T_s (cfg : SpuriousCfg) (O C : Image) : Prop :=
  decides_fo C (error_free_input_s cfg O)

/-- THE FORCED-ONLY TWIN, with the unparameterized property: the gate's
own run pinned to `Run.forced_only_cfg` through `decides_fo`, the
property left at `error_free_input`.  This is the name a grader
emits when it states the gate obligation without carrying the task's
configuration into it.

It is NOT a third reading.  `classifies_error_free_inputs_T_fo_iff_s_may_fail`
below shows it is exactly `classifies_error_free_inputs_T_s` at
`Run.may_fail_cfg` — the two differ only in how the property is
spelled, and `error_free_input_s_may_fail` identifies those.  The
name exists because a consumer that has no configuration to pass
should not have to pass `Run.may_fail_cfg` and then rewrite.

ONE ASYMMETRY IS WORTH NAMING because a reader will look for it.
Neither `classifies_patch_diff_T` nor `classifies_good_inputs_T` has
a `_fo` name; those two kinds carry the plain and the `_s cfg` forms
only.  Nothing here argues they should not have one — this file
simply does not add names to definitions it is not changing. -/
def classifies_error_free_inputs_T_fo (O C : Image) : Prop :=
  decides_fo C (error_free_input O)

/-- The declared twins of the two gate obligations, in the shape the
section above gives the patch-classifier ones.  Same reason: a gate
binary that probes for a vector unit is unmodeled under an advertised
V, so the undeclared obligation is false for it and the declared one
is what such a task can prove. -/
def classifies_error_free_inputs_T_s_hwcap_rv64gc (cfg : SpuriousCfg) (O C : Image) : Prop :=
  decides_fo_hwcap_rv64gc C (error_free_input_s cfg O)

/-- The forced-only gate decides configured source error-freedom on inputs declaring RV64GCV. -/
def classifies_error_free_inputs_T_s_hwcap_rv64gcv (cfg : SpuriousCfg) (O C : Image) : Prop :=
  decides_fo_hwcap_rv64gcv C (error_free_input_s cfg O)

/-- The forced-only gate decides unconfigured source error-freedom on inputs declaring RV64GC. -/
def classifies_error_free_inputs_T_fo_hwcap_rv64gc (O C : Image) : Prop :=
  decides_fo_hwcap_rv64gc C (error_free_input O)

/-- The forced-only gate decides unconfigured source error-freedom on inputs declaring RV64GCV. -/
def classifies_error_free_inputs_T_fo_hwcap_rv64gcv (O C : Image) : Prop :=
  decides_fo_hwcap_rv64gcv C (error_free_input O)

/-- Configured error-free-input classification is exactly the conjunction of its two capability declarations. -/
theorem classifies_error_free_inputs_T_s_hwcap_splits (cfg : SpuriousCfg) (O C : Image) :
    classifies_error_free_inputs_T_s cfg O C ↔ (classifies_error_free_inputs_T_s_hwcap_rv64gc cfg O C ∧ classifies_error_free_inputs_T_s_hwcap_rv64gcv cfg O C) :=
  decides_fo_hwcap_splits _ _

/-- Forced-only error-free-input classification is exactly the conjunction of its two capability declarations. -/
theorem classifies_error_free_inputs_T_fo_hwcap_splits (O C : Image) :
    classifies_error_free_inputs_T_fo O C ↔ (classifies_error_free_inputs_T_fo_hwcap_rv64gc O C ∧ classifies_error_free_inputs_T_fo_hwcap_rv64gcv O C) :=
  decides_fo_hwcap_splits _ _

/-- The identification just claimed, and it is a clean `iff` rather than
an implication: both sides are `decides_fo` of the SAME classifier
at the SAME budget, differing only in the property, and
`error_free_input_s_may_fail` is itself an `iff`.  Nothing about the
gate's own run has to move, which is why no `classifier_decided`
premise appears here and does appear below. -/
theorem classifies_error_free_inputs_T_fo_iff_s_may_fail (O C : Image) :
    classifies_error_free_inputs_T_fo O C ↔ classifies_error_free_inputs_T_s may_fail_cfg O C :=
  ⟨fun h f hf en hen => ⟨(h f hf en hen).1.trans (error_free_input_s_may_fail O _).symm,
      (h f hf en hen).2⟩,
   fun h f hf en hen => ⟨(h f hf en hen).1.trans (error_free_input_s_may_fail O _),
      (h f hf en hen).2⟩⟩

/-- The pin is a WEAKENING, which is the property the whole `_fo` layer
is built to have: a gate that decides under may-fail decides under
forced-only, given the filter's question answered on every run the
obligation quantifies over.  `decides_fo_of_decides` carries it
unchanged — the property does not move, only the gate's own run —
and the `classifier_decided` premise is the same one
`accepts_fo_of_accepts` and `rejects_of_rejects_fo` need.  The KNOWN
GAP in `Run.v`'s spurious-failure section says why it is a premise
rather than a theorem. -/
theorem classifies_error_free_inputs_T_fo_of_unparameterized (O C : Image) :
    classifier_decided C → classifies_error_free_inputs_T O C →
    classifies_error_free_inputs_T_fo O C :=
  decides_fo_of_decides C (error_free_input O)

/-- ... and the `_s` form at `Run.may_fail_cfg` is that composed with
the identification above, rather than a second case analysis.
Stated separately because it is the shape a consumer holding a
configuration reaches for. -/
theorem classifies_error_free_inputs_T_s_may_fail_of_unparameterized (O C : Image) :
    classifier_decided C → classifies_error_free_inputs_T O C →
    classifies_error_free_inputs_T_s may_fail_cfg O C :=
  fun hd h => (classifies_error_free_inputs_T_fo_iff_s_may_fail O C).mp
    (classifies_error_free_inputs_T_fo_of_unparameterized O C hd h)

/-- THE REFUTATION BITE, at the task-facing obligation.  An input the
original faults on UNDER `cfg` is an input the gate must exit 1 on,
at every valid entry of its own.  The `_s` twin of
`classifies_error_free_inputs_T_rejects_error`, through
`decides_fo_exit1_iff`, and the same place the totality conjunct is
spent.

Read the two configurations in the statement: the erroring run is
the ORIGINAL's, under `cfg`, at `State.source_alloc_limit`; the
verdict is the GATE's, under `Run.forced_only_cfg`, at
`classifier_alloc_limit`.  They are different runs of different
images under different configurations, and the obligation is exactly
the claim that the second tracks the first. -/
theorem classifies_error_free_inputs_T_s_rejects_error (cfg : SpuriousCfg) (O C : Image) (f : FinProcInput)
    (en enC : ExecEntry) :
    classifies_error_free_inputs_T_s cfg O C → valid_fin_input f →
    valid_entry O en (to_proc_input f) → (run_scfg cfg O source_alloc_limit en (to_proc_input f)).bh_errors →
    valid_entry C enC (to_proc_input f) →
    must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit enC (to_proc_input f) := by
  intro hdec hf hen herr henC
  exact (decides_fo_exit1_iff C (error_free_input_s cfg O) hdec f enC hf henC).mpr
    (error_free_input_s_refuted_by_error cfg O (to_proc_input f) en hen herr)

/-- ... and as a refutation of acceptance, which is the reading the
measure layer sums over: `rejects_fo` is `FinInput.valid_fin_input`
with the negation of `accepts_fo`.  One valid entry of the gate is
needed and cannot be dropped, for `accepts_fo_vacuous_no_entries`'s
reason. -/
theorem classifies_error_free_inputs_T_s_refutes_acceptance (cfg : SpuriousCfg) (O C : Image) (f : FinProcInput)
    (en enC : ExecEntry) :
    classifies_error_free_inputs_T_s cfg O C → valid_fin_input f →
    valid_entry O en (to_proc_input f) → (run_scfg cfg O source_alloc_limit en (to_proc_input f)).bh_errors →
    valid_entry C enC (to_proc_input f) → rejects_fo C f := by
  intro hdec hf hen herr henC
  exact rejects_fo_by_exit1 C f enC hf henC
    (classifies_error_free_inputs_T_s_rejects_error cfg O C f en enC hdec hf hen herr henC)

/-- The accepting direction.  Together with the two above this is what
makes the configured gate's exit code a reading of the original's
behavior UNDER THAT CONFIGURATION rather than a choice the
submission makes. -/
theorem classifies_error_free_inputs_T_s_accepts_error_free (cfg : SpuriousCfg) (O C : Image) (f : FinProcInput) :
    classifies_error_free_inputs_T_s cfg O C → valid_fin_input f →
    error_free_input_s cfg O (to_proc_input f) → accepts_fo C f := by
  intro hdec hf hef en hen
  exact (hdec f hf en hen).1.mpr hef

/-- THE VACUITY ROUTE'S PRICE, under a configuration, and the answer is
the same at every `cfg` because the route runs through the entry
quantifier: an ORIGINAL that does not load is error-free everywhere,
so a gate that decides correctly about it accepts the whole input
space, the second program of the split is never asked anything, and
the submission is charged for one program while proving nothing
about the other.

The hole is in the ORIGINAL, not the gate, which is what
`decides_fo_vacuous_no_entries` and `accepts_fo_vacuous_no_entries`
are about; this survives a perfectly well-formed gate doing its job
correctly. -/
theorem classifies_error_free_inputs_T_s_vacuous_accepts_everything (cfg : SpuriousCfg) (O C : Image)
    (hdec : classifies_error_free_inputs_T_s cfg O C)
    (hno : ∀ f en, ¬ valid_entry O en (to_proc_input f)) (f : FinProcInput) :
    valid_fin_input f → accepts_fo C f := by
  intro hf
  exact classifies_error_free_inputs_T_s_accepts_error_free cfg O C f hdec hf
    (error_free_input_s_vacuous_no_entries cfg O (to_proc_input f) (hno f))

/-- The four bites at the `_fo` name, each the `Run.may_fail_cfg`
instance of the one above it through
`classifies_error_free_inputs_T_fo_iff_s_may_fail`.  They are stated
rather than left to the reader because the `_fo` form is a name a
grader emits, and a definition a consumer is asked to pin should
carry its own refutations under that name instead of through a
rewrite the consumer has to find. -/
theorem classifies_error_free_inputs_T_fo_rejects_error (O C : Image) (f : FinProcInput)
    (en enC : ExecEntry) :
    classifies_error_free_inputs_T_fo O C → valid_fin_input f →
    valid_entry O en (to_proc_input f) → (run O source_alloc_limit en (to_proc_input f)).bh_errors →
    valid_entry C enC (to_proc_input f) →
    must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit enC (to_proc_input f) := by
  intro hdec hf hen herr henC
  exact (decides_fo_exit1_iff C (error_free_input O) hdec f enC hf henC).mpr
    (error_free_input_refuted_by_error O (to_proc_input f) en hen herr)

/-- An erroring original run at a valid entry forces rejection, provided the gate has a valid entry. -/
theorem classifies_error_free_inputs_T_fo_refutes_acceptance (O C : Image) (f : FinProcInput)
    (en enC : ExecEntry) :
    classifies_error_free_inputs_T_fo O C → valid_fin_input f →
    valid_entry O en (to_proc_input f) → (run O source_alloc_limit en (to_proc_input f)).bh_errors →
    valid_entry C enC (to_proc_input f) → rejects_fo C f := by
  intro hdec hf hen herr henC
  exact rejects_fo_by_exit1 C f enC hf henC
    (classifies_error_free_inputs_T_fo_rejects_error O C f en enC hdec hf hen herr henC)

/-- A forced-only gate accepts every valid finite input at which the original is error-free. -/
theorem classifies_error_free_inputs_T_fo_accepts_error_free (O C : Image) (f : FinProcInput) :
    classifies_error_free_inputs_T_fo O C → valid_fin_input f →
    error_free_input O (to_proc_input f) → accepts_fo C f := by
  intro hdec hf hef en hen
  exact (hdec f hf en hen).1.mpr hef

/-- An original without valid entries makes a correct forced-only gate accept every valid finite input. -/
theorem classifies_error_free_inputs_T_fo_vacuous_accepts_everything (O C : Image)
    (hdec : classifies_error_free_inputs_T_fo O C)
    (hno : ∀ f en, ¬ valid_entry O en (to_proc_input f)) (f : FinProcInput) :
    valid_fin_input f → accepts_fo C f := by
  intro hf
  exact classifies_error_free_inputs_T_fo_accepts_error_free O C f hdec hf
    (error_free_input_vacuous_no_entries O (to_proc_input f) (hno f))

end LinuxProcessSemantics.EquivalenceDefinition.Classifier
