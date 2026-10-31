import LinuxProcessSemantics.LinuxProcessSem.OmniRun
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence
import LinuxProcessSemantics.EquivalenceDefinition.MustExit

/-! rocq-baseline: 1807c1e25ce12708f5cc85213f2df4bf03d978da
unported: omni_strong_equiv_error_free -- Waits on Equivalence.strong_equiv_error_free (A-Equiv-error-free); no plan ticket owns this omni port yet.
unported: omni_strong_universal_error_free_T -- Waits on omni_strong_equiv_error_free and Equivalence.strong_universal_error_free_T (A-Equiv-error-free); no plan ticket owns this omni port yet.
unported: omni_strong_universal -- Waits on SPEC/OMNI_SPEC module-type sealing bridges; no plan ticket owns this port yet.
unported: strong_universal -- Waits on SPEC/OMNI_SPEC module-type sealing bridges; no plan ticket owns this port yet.
unported: omni_strong_universal_error_free -- Waits on SPEC_ERROR_FREE/OMNI_SPEC_ERROR_FREE module-type sealing bridges and A-Equiv-error-free; no plan ticket owns this port yet.
unported: strong_universal_error_free -- Waits on SPEC_ERROR_FREE/OMNI_SPEC_ERROR_FREE module-type sealing bridges and A-Equiv-error-free; no plan ticket owns this port yet.
unported: omni_agree -- Waits on Classifier.agree (A-Classifier); no plan ticket owns this omni port yet.
unported: omni_good_input -- Waits on omni_strong_equiv_error_free (A-Equiv-error-free) and Classifier.good_input (A-Classifier); no plan ticket owns this omni port yet.
unported: omni_decides -- Waits on Classifier.decides, classifier_alloc_limit (A-Classifier), and FinInput's FinProcInput/valid_fin_input/to_proc_input (A-FinInput); no plan ticket owns this omni port yet.
unported: omni_classifier_total_T -- Waits on Classifier.classifier_total_T, classifier_alloc_limit (A-Classifier), and FinInput's FinProcInput/valid_fin_input/to_proc_input (A-FinInput); no plan ticket owns this omni port yet.
unported: omni_classifies_patch_diff_T -- Waits on omni_agree/omni_decides, A-Classifier, and FinInput's FinProcInput/valid_fin_input/to_proc_input (A-FinInput); no plan ticket owns this omni port yet.
unported: omni_classifies_good_inputs_T -- Waits on omni_decides, omni_good_input (A-Classifier, A-Equiv-error-free), and FinInput's FinProcInput/valid_fin_input/to_proc_input (A-FinInput); no plan ticket owns this omni port yet. -/

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

structure OMNI_SPEC (source target : Image) : Prop where
  omni_strong_universal : omni_strong_universal_T source target

end LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
