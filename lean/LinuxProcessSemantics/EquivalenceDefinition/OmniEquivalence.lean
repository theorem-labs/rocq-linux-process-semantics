-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/OmniEquivalence.v
import LinuxProcessSemantics.LinuxProcessSem.OmniRun
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence
import LinuxProcessSemantics.EquivalenceDefinition.MustExit
import LinuxProcessSemantics.EquivalenceDefinition.FinInput
import LinuxProcessSemantics.EquivalenceDefinition.Classifier

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058
unported: omni_strong_universal -- Rocq declares it twice as a functor field, in OMNI_SPEC and in the body of OmniOfSpec; Lean carries it as the field of structure OMNI_SPEC and as the argument of the anonymous constructor OmniOfSpec builds, so there is no top-level definition of that name.
unported: strong_universal -- the same, for SpecOfOmni and the field of Equivalence.SPEC; Lean has it as that structure's field and as SpecOfOmni's constructor argument.
unported: omni_strong_universal_error_free -- the same, for OMNI_SPEC_ERROR_FREE and OmniOfSpecErrorFree.
unported: strong_universal_error_free -- the same, for SpecErrorFreeOfOmni and the field of Equivalence.SPEC_ERROR_FREE. -/

/-! # The omni form of the baseline equivalence contract

Mirrors the baseline definitions and compatibility statements of
`theories/EquivalenceDefinition/OmniEquivalence.v`, the shape with `m_killed`
(ticket A12). The equivalence
below is an iff between the actual judgments, rather than a redefinition of
one public contract as the other.
-/

namespace LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.EquivalenceDefinition.Classifier

theorem exec_exits_must_exit_at (segs : List Segment) (code : word) (c : config) (Q : post)
    (h : exec segs c Q) (himp : ∀ tr o, Q tr o → exits_with code tr o) :
    must_exit_at segs code c := by
  induction h with
  | exec_halt c Q _ hq =>
    obtain ⟨hex, hk⟩ := himp _ _ hq
    exact must_exit_at.must_exit_at_halted _ hex hk
  | exec_step c Q hh hp herr hn ih =>
    apply must_exit_at.must_exit_at_running c hh hp
    · intro evs hs; exact himp _ _ (herr evs hs)
    · intro evs c' hs
      exact ih evs c' hs (fun tr o hq => himp (evs ++ tr) o hq)

theorem must_exit_at_iff (segs : List Segment) (code : word) (c : config) :
    must_exit_at segs code c ↔ exec segs c (exits_with code) := by
  constructor
  · intro h
    induction h with
    | must_exit_at_halted c hh hk =>
      exact exec.exec_halt _ _ (by rw [hh]; nofun) ⟨hh, hk⟩
    | must_exit_at_running c hh hp hno hn ih =>
      exact exec.exec_step c _ hh hp (fun evs hs => False.elim (hno evs hs))
        (fun evs c' hs => ih evs c' hs)
  · intro h; exact exec_exits_must_exit_at _ _ _ _ h (fun _ _ h => h)

theorem must_exit_with_iff (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_with code img lim en inp ↔ omni_run img lim en inp (exits_with code) :=
  must_exit_at_iff _ _ _

theorem error_free_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    error_free (run img lim en inp) ↔ omni_corun img lim en inp never_errors :=
  never_errors_iff _ _

theorem modeled_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    modeled (run img lim en inp) ↔ omni_corun img lim en inp (covered img.img_segments) :=
  covered_iff _ _

def omni_trace_equiv (img1 : Image) (lim1 : Int) (en1 : ExecEntry)
    (img2 : Image) (lim2 : Int) (en2 : ExecEntry) (inp : ProcInput) : Prop :=
  ∀ P, prefix_closed P → (omni_cosafe img1 lim1 en1 inp P ↔ omni_cosafe img2 lim2 en2 inp P)

theorem trace_equiv_iff_omni (img1 : Image) (lim1 : Int) (en1 : ExecEntry)
    (img2 : Image) (lim2 : Int) (en2 : ExecEntry) (inp : ProcInput) :
    trace_equiv (run img1 lim1 en1 inp).bh_traces (run img2 lim2 en2 inp).bh_traces ↔
    omni_trace_equiv img1 lim1 en1 img2 lim2 en2 inp :=
  obs_equiv_iff_cosafe _ _ _ _

/-- The introduction rule for trace agreement: each run's trace set is a
prefix-closed postcondition the other run satisfies, that is, a refinement in
each direction. -/
theorem omni_trace_equiv_refinement (img1 : Image) (lim1 : Int) (en1 : ExecEntry)
    (img2 : Image) (lim2 : Int) (en2 : ExecEntry) (inp : ProcInput) :
    omni_trace_equiv img1 lim1 en1 img2 lim2 en2 inp ↔
    (omni_cosafe img1 lim1 en1 inp (run img2 lim2 en2 inp).bh_traces ∧
      omni_cosafe img2 lim2 en2 inp (run img1 lim1 en1 inp).bh_traces) := by
  constructor
  · intro h
    exact (obs_equiv_iff_refinement _ _ _ _).1 ((trace_equiv_iff_omni _ _ _ _ _ _ _).2 h)
  · intro h
    exact (trace_equiv_iff_omni _ _ _ _ _ _ _).1 ((obs_equiv_iff_refinement _ _ _ _).2 h)

def omni_equiv (imgS : Image) (limS : Int) (enS : ExecEntry)
    (imgT : Image) (limT : Int) (enT : ExecEntry) (inp : ProcInput) : Prop :=
  omni_run imgS limS enS inp errors ∨
    (omni_trace_equiv imgS limS enS imgT limT enT inp ∧
      omni_corun imgT limT enT inp never_errors)

theorem equiv_iff (imgS : Image) (limS : Int) (enS : ExecEntry)
    (imgT : Image) (limT : Int) (enT : ExecEntry) (inp : ProcInput) :
    equiv (run imgS limS enS inp) (run imgT limT enT inp) ↔
    omni_equiv imgS limS enS imgT limT enT inp := by
  change (_ ∨ (_ ∧ _)) ↔ (_ ∨ (_ ∧ _))
  exact or_congr (all_traces_error_iff _ _)
    (and_congr (trace_equiv_iff_omni _ _ _ _ _ _ _) (never_errors_iff _ _))

/-- The all-error escape alone establishes the omni equivalence, whatever the
target does. -/
theorem omni_all_errors_equiv_any (imgS : Image) (limS : Int) (enS : ExecEntry)
    (imgT : Image) (limT : Int) (enT : ExecEntry) (inp : ProcInput)
    (h : omni_run imgS limS enS inp errors) :
    omni_equiv imgS limS enS imgT limT enT inp := Or.inl h

/-- Without the escape, the omni equivalence forces a target that never errors
on any maximal execution. -/
theorem omni_equiv_target_never_errors (imgS : Image) (limS : Int) (enS : ExecEntry)
    (imgT : Image) (limT : Int) (enT : ExecEntry) (inp : ProcInput)
    (h : omni_equiv imgS limS enS imgT limT enT inp)
    (hn : ¬ omni_run imgS limS enS inp errors) :
    omni_corun imgT limT enT inp never_errors := by
  rcases h with hall | ⟨_, hne⟩
  · exact absurd hall hn
  · exact hne

def omni_strong_equiv (source target : Image) (es et : ExecEntry) (inp : ProcInput) : Prop :=
  omni_corun source source_alloc_limit es inp (covered source.img_segments) ∧
    omni_equiv source source_alloc_limit es target target_alloc_limit et inp

theorem strong_equiv_iff (source target : Image) (es et : ExecEntry) (inp : ProcInput) :
    strong_equiv source target es et inp ↔ omni_strong_equiv source target es et inp :=
  and_congr (modeled_iff _ _ _ _) (equiv_iff _ _ _ _ _ _ _)

def omni_strong_universal_T (source target : Image) : Prop :=
  ∀ es et inp, valid_entry source es inp → valid_entry target et inp → valid_input inp →
    omni_strong_equiv source target es et inp

theorem strong_universal_iff (source target : Image) :
    strong_universal_T source target ↔ omni_strong_universal_T source target := by
  constructor
  · intro h es et inp hs ht hi
    exact (strong_equiv_iff _ _ _ _ _).1 (h es et inp hs ht hi)
  · intro h es et inp hs ht hi
    exact (strong_equiv_iff _ _ _ _ _).2 (h es et inp hs ht hi)

/-- `Equivalence.strong_equiv_error_free` in omni form: no maximal execution of
either run ends in an error, and the two runs agree on every prefix-closed
postcondition. -/
def omni_strong_equiv_error_free (source target : Image) (es et : ExecEntry)
    (inp : ProcInput) : Prop :=
  omni_corun source source_alloc_limit es inp never_errors ∧
    omni_corun target target_alloc_limit et inp never_errors ∧
      omni_trace_equiv source source_alloc_limit es target target_alloc_limit et inp

/-- The per-triple error-free contract and its omni form are the same statement. -/
theorem strong_equiv_error_free_iff (source target : Image) (es et : ExecEntry)
    (inp : ProcInput) :
    strong_equiv_error_free source target es et inp ↔
    omni_strong_equiv_error_free source target es et inp :=
  and_congr (error_free_iff _ _ _ _)
    (and_congr (error_free_iff _ _ _ _) (trace_equiv_iff_omni _ _ _ _ _ _ _))

/-- The error-free universal contract in omni form, with the quantifier shell of
`omni_strong_universal_T` unchanged. -/
def omni_strong_universal_error_free_T (source target : Image) : Prop :=
  ∀ es et inp, valid_entry source es inp → valid_entry target et inp → valid_input inp →
    omni_strong_equiv_error_free source target es et inp

/-- The error-free universal contract and its omni form are the same statement. -/
theorem strong_universal_error_free_iff (source target : Image) :
    strong_universal_error_free_T source target ↔
    omni_strong_universal_error_free_T source target := by
  constructor
  · intro h es et inp hs ht hi
    exact (strong_equiv_error_free_iff _ _ _ _ _).1 (h es et inp hs ht hi)
  · intro h es et inp hs ht hi
    exact (strong_equiv_error_free_iff _ _ _ _ _).2 (h es et inp hs ht hi)

/-- The error-free shape is the stronger one, in omni terms: `never_errors`
entails `covered`, and the last two conjuncts are the right disjunct of
`omni_equiv`. -/
theorem omni_strong_equiv_error_free_implies (source target : Image) (es et : ExecEntry)
    (inp : ProcInput) (h : omni_strong_equiv_error_free source target es et inp) :
    omni_strong_equiv source target es et inp :=
  ⟨coexec_conseq _ _ _ _ h.1 (never_errors_covered _), Or.inr ⟨h.2.2, h.2.1⟩⟩

/-- The same implication at the universal shape. -/
theorem omni_strong_universal_error_free_implies (source target : Image)
    (h : omni_strong_universal_error_free_T source target) :
    omni_strong_universal_T source target :=
  fun es et inp hs ht hi => omni_strong_equiv_error_free_implies _ _ _ _ _ (h es et inp hs ht hi)

/-- Where the two shapes diverge, as a refutation: an `exec … errors` judgment is
realised by some maximal execution, which ends in an error, and
`coexec … never_errors` forbids exactly that. The escape is therefore
inconsistent with the error-free shape, not merely unused by it. -/
theorem omni_strong_equiv_error_free_no_all_errors_escape (source target : Image)
    (es et : ExecEntry) (inp : ProcInput)
    (hall : omni_run source source_alloc_limit es inp errors) :
    ¬ omni_strong_equiv_error_free source target es et inp := by
  intro h
  obtain ⟨tr, o, hm, herr⟩ := exec_realizes _ _ _ hall
  exact coexec_sound _ _ _ _ hm _ h.1 herr

/-- One erroring maximal execution at one valid triple refutes the whole
error-free universal statement. -/
theorem omni_strong_universal_error_free_refuted_by_source_error (source target : Image)
    (es et : ExecEntry) (inp : ProcInput) (hs : valid_entry source es inp)
    (ht : valid_entry target et inp) (hi : valid_input inp)
    (hmay : omni_may source source_alloc_limit es inp errors) :
    ¬ omni_strong_universal_error_free_T source target := by
  intro h
  obtain ⟨tr, o, hm, herr⟩ := hmay
  exact coexec_sound _ _ _ _ hm _ (h es et inp hs ht hi).1 herr

structure OMNI_SPEC (source target : Image) : Prop where
  omni_strong_universal : omni_strong_universal_T source target

/-- The obligation of the reference `OMNI_SPEC_ERROR_FREE` module type. -/
structure OMNI_SPEC_ERROR_FREE (source target : Image) : Prop where
  omni_strong_universal_error_free : omni_strong_universal_error_free_T source target

/-- The bridge Rocq writes as the functor `OmniOfSpec`: a proof of the sealed
baseline obligation is a proof of the omni one. -/
theorem OmniOfSpec (source target : Image) (S : SPEC source target) :
    OMNI_SPEC source target :=
  ⟨(strong_universal_iff source target).1 S.strong_universal⟩

/-- The converse bridge, Rocq's functor `SpecOfOmni`: a proof written against
`omni_strong_universal_T` discharges `Equivalence.SPEC`, so a consumer's pinned
checker need not change. -/
theorem SpecOfOmni (source target : Image) (O : OMNI_SPEC source target) :
    SPEC source target :=
  ⟨(strong_universal_iff source target).2 O.omni_strong_universal⟩

/-- The same bridge for the error-free pair, Rocq's functor
`OmniOfSpecErrorFree`. -/
theorem OmniOfSpecErrorFree (source target : Image) (S : SPEC_ERROR_FREE source target) :
    OMNI_SPEC_ERROR_FREE source target :=
  ⟨(strong_universal_error_free_iff source target).1 S.strong_universal_error_free⟩

/-- The converse for the error-free pair, Rocq's functor
`SpecErrorFreeOfOmni`. -/
theorem SpecErrorFreeOfOmni (source target : Image) (O : OMNI_SPEC_ERROR_FREE source target) :
    SPEC_ERROR_FREE source target :=
  ⟨(strong_universal_error_free_iff source target).2 O.omni_strong_universal_error_free⟩

/-! ## Compat: the classifier families -/

/-- A logic helper: an existential whose body is a side condition and a
predicate respects an iff of that predicate. -/
theorem ex_and_iff (A : Type) (V P P' : A → Prop) (h : ∀ x, P x ↔ P' x) :
    (∃ x, V x ∧ P x) ↔ (∃ x, V x ∧ P' x) := by
  constructor
  · rintro ⟨x, hv, hp⟩
    exact ⟨x, hv, (h x).1 hp⟩
  · rintro ⟨x, hv, hp⟩
    exact ⟨x, hv, (h x).2 hp⟩

/-- `Classifier.agree` in omni form: trace agreement at every valid entry pair,
and the three per-entry existential facts — may-error, must-error,
may-leave-the-model — matched across the two images. -/
def omni_agree (X Y : Image) (lim : Int) (inp : ProcInput) : Prop :=
  (∀ enX enY,
     valid_entry X enX inp → valid_entry Y enY inp →
     omni_trace_equiv X lim enX Y lim enY inp)
  ∧ ((∃ en, valid_entry X en inp ∧ omni_may X lim en inp errors)
      ↔ (∃ en, valid_entry Y en inp ∧ omni_may Y lim en inp errors))
  ∧ ((∃ en, valid_entry X en inp ∧ omni_run X lim en inp errors)
      ↔ (∃ en, valid_entry Y en inp ∧ omni_run Y lim en inp errors))
  ∧ ((∃ en, valid_entry X en inp ∧ omni_may X lim en inp (uncovered X.img_segments))
      ↔ (∃ en, valid_entry Y en inp ∧ omni_may Y lim en inp (uncovered Y.img_segments)))

/-- Per-input agreement and its omni form are the same statement. -/
theorem agree_iff (X Y : Image) (lim : Int) (inp : ProcInput) :
    agree X Y lim inp ↔ omni_agree X Y lim inp := by
  unfold agree omni_agree
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · constructor
    · intro h enX enY hx hy
      exact (trace_equiv_iff_omni _ _ _ _ _ _ _).1 (h enX enY hx hy)
    · intro h enX enY hx hy
      exact (trace_equiv_iff_omni _ _ _ _ _ _ _).2 (h enX enY hx hy)
  · exact iff_congr (ex_and_iff _ _ _ _ fun en => bh_errors_may_iff X lim en inp)
      (ex_and_iff _ _ _ _ fun en => bh_errors_may_iff Y lim en inp)
  · exact iff_congr (ex_and_iff _ _ _ _ fun en => bh_all_errors_iff X lim en inp)
      (ex_and_iff _ _ _ _ fun en => bh_all_errors_iff Y lim en inp)
  · exact iff_congr (ex_and_iff _ _ _ _ fun en => bh_unmodeled_may_iff X lim en inp)
      (ex_and_iff _ _ _ _ fun en => bh_unmodeled_may_iff Y lim en inp)

/-- `Classifier.good_input` in omni form: the two images are error-free
equivalent at every pair of valid entries. -/
def omni_good_input (O1 O2 : Image) (inp : ProcInput) : Prop :=
  ∀ en1 en2,
    valid_entry O1 en1 inp → valid_entry O2 en2 inp →
    omni_strong_equiv_error_free O1 O2 en1 en2 inp

/-- The good-input property and its omni form are the same statement. -/
theorem good_input_iff (O1 O2 : Image) (inp : ProcInput) :
    good_input O1 O2 inp ↔ omni_good_input O1 O2 inp := by
  constructor
  · intro h en1 en2 h1 h2
    exact (strong_equiv_error_free_iff _ _ _ _ _).1 (h en1 en2 h1 h2)
  · intro h en1 en2 h1 h2
    exact (strong_equiv_error_free_iff _ _ _ _ _).2 (h en1 en2 h1 h2)

/-- `Classifier.decides` with `MustExit.must_exit_with` read as
`omni_run … (exits_with verdict)`. -/
def omni_decides (C : Image) (spec : ProcInput → Prop) : Prop :=
  ∀ f : FinProcInput,
    valid_fin_input f →
    ∀ en,
      valid_entry C en (to_proc_input f) →
      (omni_run C classifier_alloc_limit en (to_proc_input f) (exits_with verdict_accept)
         ↔ spec (to_proc_input f))
      ∧ (omni_run C classifier_alloc_limit en (to_proc_input f) (exits_with verdict_accept)
         ∨ omni_run C classifier_alloc_limit en (to_proc_input f) (exits_with verdict_reject))

/-- The classifier obligation and its omni form are the same statement. -/
theorem decides_iff (C : Image) (spec : ProcInput → Prop) :
    decides C spec ↔ omni_decides C spec := by
  constructor
  · intro h f hf en hen
    obtain ⟨hspec, htot⟩ := h f hf en hen
    refine ⟨(must_exit_with_iff _ _ _ _ _).symm.trans hspec, ?_⟩
    rcases htot with ha | hr
    · exact Or.inl ((must_exit_with_iff _ _ _ _ _).1 ha)
    · exact Or.inr ((must_exit_with_iff _ _ _ _ _).1 hr)
  · intro h f hf en hen
    obtain ⟨hspec, htot⟩ := h f hf en hen
    refine ⟨(must_exit_with_iff _ _ _ _ _).trans hspec, ?_⟩
    rcases htot with ha | hr
    · exact Or.inl ((must_exit_with_iff _ _ _ _ _).2 ha)
    · exact Or.inr ((must_exit_with_iff _ _ _ _ _).2 hr)

/-- The spec side of `omni_decides` is respected up to iff, which is what lets
the two classifier obligations below be restated in omni form. -/
theorem omni_decides_spec_iff (C : Image) (spec spec' : ProcInput → Prop)
    (hs : ∀ inp, spec inp ↔ spec' inp) :
    omni_decides C spec ↔ omni_decides C spec' := by
  constructor
  · intro h f hf en hen
    obtain ⟨hspec, htot⟩ := h f hf en hen
    exact ⟨hspec.trans (hs _), htot⟩
  · intro h f hf en hen
    obtain ⟨hspec, htot⟩ := h f hf en hen
    exact ⟨hspec.trans (hs _).symm, htot⟩

/-- The totality conjunct of `omni_decides`, on its own. -/
def omni_classifier_total_T (Cl : Image) : Prop :=
  ∀ f : FinProcInput,
    valid_fin_input f →
    ∀ en,
      valid_entry Cl en (to_proc_input f) →
      omni_run Cl classifier_alloc_limit en (to_proc_input f) (exits_with verdict_accept)
      ∨ omni_run Cl classifier_alloc_limit en (to_proc_input f) (exits_with verdict_reject)

/-- Classifier totality and its omni form are the same statement. -/
theorem classifier_total_iff (Cl : Image) :
    classifier_total_T Cl ↔ omni_classifier_total_T Cl := by
  constructor
  · intro h f hf en hen
    rcases h f hf en hen with ha | hr
    · exact Or.inl ((must_exit_with_iff _ _ _ _ _).1 ha)
    · exact Or.inr ((must_exit_with_iff _ _ _ _ _).1 hr)
  · intro h f hf en hen
    rcases h f hf en hen with ha | hr
    · exact Or.inl ((must_exit_with_iff _ _ _ _ _).2 ha)
    · exact Or.inr ((must_exit_with_iff _ _ _ _ _).2 hr)

/-- Deciding any spec in omni form gives omni totality. -/
theorem omni_decides_implies_total (C : Image) (spec : ProcInput → Prop)
    (h : omni_decides C spec) : omni_classifier_total_T C :=
  fun f hf en hen => (h f hf en hen).2

/-- The patch-difference obligation in omni form: accept exactly the inputs on
which both original/patched pairs agree, each pair at its own role's budget. -/
def omni_classifies_patch_diff_T (O1 P1 O2 P2 C : Image) : Prop :=
  omni_decides C (fun inp => omni_agree O1 P1 source_alloc_limit inp
                             ∧ omni_agree O2 P2 target_alloc_limit inp)

/-- The patch-difference obligation and its omni form are the same statement. -/
theorem classifies_patch_diff_iff (O1 P1 O2 P2 C : Image) :
    classifies_patch_diff_T O1 P1 O2 P2 C ↔ omni_classifies_patch_diff_T O1 P1 O2 P2 C :=
  (decides_iff _ _).trans (omni_decides_spec_iff C _ _ fun inp =>
    and_congr (agree_iff O1 P1 source_alloc_limit inp) (agree_iff O2 P2 target_alloc_limit inp))

/-- The good-input obligation in omni form. -/
def omni_classifies_good_inputs_T (O1 O2 C : Image) : Prop :=
  omni_decides C (omni_good_input O1 O2)

/-- The good-input obligation and its omni form are the same statement. -/
theorem classifies_good_inputs_iff (O1 O2 C : Image) :
    classifies_good_inputs_T O1 O2 C ↔ omni_classifies_good_inputs_T O1 O2 C :=
  (decides_iff _ _).trans (omni_decides_spec_iff C _ _ (good_input_iff O1 O2))

end LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
