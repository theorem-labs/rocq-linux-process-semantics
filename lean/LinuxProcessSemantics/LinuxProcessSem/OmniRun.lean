import LinuxProcessSemantics.LinuxProcessSem.Run

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570
unported: coexec_progress -- the progress-carrying reading of coexec, ported by ticket K8 as Checks.Omni.coexec_progress and kept out of this file so that coexec stays the one judgment every reader takes; Checks.Omni.coexec_progress_iff proves the two coincide under the table-agreement hypothesis Checks/Progress.lean carries, and this line retires only when the reading is defined in this file or an OmniRun/ part, which the parity reader reads for the name — a complete checked table removes the hypothesis, not this line -/

/-! # Universal execution judgments

Mirrors `theories/LinuxProcessSem/OmniRun.v` at the header's baseline, name
for name; the register above names the one definition left out, and the two
lemmas about it, `coexec_progress_implies` and `stuck_not_coexec_progress`,
stand beside it in `Checks/Omni.lean`.  The
coinductive judgments are Lean's own `coinductive` (lean/README.md,
"Translation decisions").  The killed terminal rule and the kill conjunct
of `exits_with` are ticket A12's.  No execution fuel appears in these
judgments.

Why it is not here: `coexec_progress` is the reading Rocq keeps so that
dropping the progress premise stays a local reversal, and ticket K8 ported
it as `Checks.Omni.coexec_progress` beside the theorem that the two
readings coincide on this tree (`Checks/Omni.lean`'s `coexec_progress_iff`,
under the table-agreement hypothesis that file inherits), leaving this file
the one judgment every reader takes. -/

namespace LinuxProcessSemantics.LinuxProcessSem.OmniRun

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run

inductive outcome where
  | OHalt (c : config)
  | OError (c : config)

export outcome (OHalt OError)
abbrev post := List event → outcome → Prop

def is_error : outcome → Prop
  | OHalt _ => False
  | OError _ => True

def errors : post := fun _ o => is_error o
def never_errors : post := fun _ o => ¬ is_error o
def covered (segs : List Segment) : post := fun _ o =>
  match o with
  | OHalt _ => True
  | OError c => ¬ unmodeled_at segs c
def uncovered (segs : List Segment) : post := fun _ o =>
  match o with
  | OHalt _ => False
  | OError c => unmodeled_at segs c
/-- `MustExit.must_exit_at`'s postcondition.  A DEATH BY SIGNAL IS NOT AN
EXIT, and the second conjunct is what says so: a process killed by
SIGABRT carries the signal number in `State.m_halted` — that field is the
"process is over" marker, and `State.m_killed` is what says which of the
two ways it got there — so without the conjunct this postcondition would
read an abort as a verdict of 6.  The same conjunct sits on
`MustExit.must_exit_at_halted` for the same reason.  (Rocq:
`OmniRun.exits_with`.) -/
def exits_with (code : word) : post := fun _ o =>
  match o with
  | OHalt c => m_halted c.cfg_model = some code ∧ m_killed c.cfg_model = none
  | OError _ => False

theorem never_errors_covered (segs : List Segment) (tr : List event) (o : outcome) :
    never_errors tr o → covered segs tr o := by
  cases o <;> simp [never_errors, is_error, covered]

theorem exits_with_never_errors (code : word) (tr : List event) (o : outcome) :
    exits_with code tr o → never_errors tr o := by
  cases o <;> simp [exits_with, never_errors, is_error]

theorem sstep_from_running (segs : List Segment) (c : config) (evs : List event)
    (st : step_to) : sstep segs c evs st → m_halted c.cfg_model = none := by
  intro h
  cases h <;> assumption

inductive mexec (segs : List Segment) : config → List event → outcome → Prop
  | mexec_halt : ∀ c, m_halted c.cfg_model ≠ none → mexec segs c [] (OHalt c)
  | mexec_error : ∀ c evs, sstep segs c evs SError → mexec segs c evs (OError c)
  | mexec_next : ∀ c evs c' tr o,
      sstep segs c evs (SNext c') → mexec segs c' tr o → mexec segs c (evs ++ tr) o

theorem star_mexec (segs : List Segment) (c : config) (tr : List event) (c' : config)
    (tr' : List event) (o : outcome) :
    star segs c tr c' → mexec segs c' tr' o → mexec segs c (tr ++ tr') o := by
  intro hs
  induction hs with
  | star_refl _ => exact fun h => h
  | star_step c evs c1 tr c2 hstep _ ih =>
    intro h
    rw [List.append_assoc]
    exact mexec.mexec_next _ _ _ _ _ hstep (ih h)

theorem mexec_halt_star (segs : List Segment) (c : config) (tr : List event)
    (o : outcome) (h : mexec segs c tr o) :
    ∀ c', o = OHalt c' → star segs c tr c' ∧ m_halted c'.cfg_model ≠ none := by
  induction h with
  | mexec_halt c hh =>
    intro c' heq
    cases heq
    exact ⟨star.star_refl _, hh⟩
  | mexec_error c evs hs => intro c' heq; cases heq
  | mexec_next c evs c1 tr o hs _ ih =>
    intro c' heq
    obtain ⟨hstar, hh⟩ := ih c' heq
    exact ⟨star.star_step _ _ _ _ _ hs hstar, hh⟩

theorem mexec_error_star (segs : List Segment) (c : config) (tr : List event)
    (o : outcome) (h : mexec segs c tr o) :
    ∀ c', o = OError c' →
    ∃ tr1 evs, tr = tr1 ++ evs ∧ star segs c tr1 c' ∧ sstep segs c' evs SError := by
  induction h with
  | mexec_halt c hh => intro c' heq; cases heq
  | mexec_error c evs hs =>
    intro c' heq
    cases heq
    exact ⟨[], evs, rfl, star.star_refl _, hs⟩
  | mexec_next c evs c1 tr o hs _ ih =>
    intro c' heq
    obtain ⟨tr1, evs', rfl, hstar, hss'⟩ := ih c' heq
    exact ⟨evs ++ tr1, evs', (List.append_assoc _ _ _).symm,
      star.star_step _ _ _ _ _ hs hstar, hss'⟩

/-- `Run.reaches_error` is "some maximal execution errors". -/
theorem reaches_error_iff_may (segs : List Segment) (c : config) :
    reaches_error segs c ↔ ∃ tr o, mexec segs c tr o ∧ errors tr o := by
  constructor
  · rintro ⟨tr, c2, evs, hstar, hss⟩
    exact ⟨tr ++ evs, OError c2,
      star_mexec _ _ _ _ _ _ hstar (mexec.mexec_error _ _ hss), trivial⟩
  · rintro ⟨tr, o, hm, he⟩
    cases o with
    | OHalt _ => exact False.elim he
    | OError c' =>
      obtain ⟨tr1, evs, _, hstar, hss⟩ := mexec_error_star _ _ _ _ hm c' rfl
      exact ⟨tr1, c', evs, hstar, hss⟩

/-- `Run.reaches_unmodeled` is "some maximal execution errors from an
uncovered configuration". -/
theorem reaches_unmodeled_iff_may (segs : List Segment) (c : config) :
    reaches_unmodeled segs c ↔ ∃ tr o, mexec segs c tr o ∧ uncovered segs tr o := by
  constructor
  · rintro ⟨tr, c', hstar, hun⟩
    obtain ⟨evs, hss⟩ := unmodeled_at_sstep_error _ _ hun
    exact ⟨tr ++ evs, OError c',
      star_mexec _ _ _ _ _ _ hstar (mexec.mexec_error _ _ hss), hun⟩
  · rintro ⟨tr, o, hm, hun⟩
    cases o with
    | OHalt _ => exact False.elim hun
    | OError c' =>
      obtain ⟨tr1, evs, _, hstar, _⟩ := mexec_error_star _ _ _ _ hm c' rfl
      exact ⟨tr1, c', hstar, hun⟩

inductive exec (segs : List Segment) : config → post → Prop
  | exec_halt : ∀ c Q, m_halted c.cfg_model ≠ none → Q [] (OHalt c) → exec segs c Q
  | exec_step : ∀ c Q,
      m_halted c.cfg_model = none →
      (∃ evs st, sstep segs c evs st) →
      (∀ evs, sstep segs c evs SError → Q evs (OError c)) →
      (∀ evs c', sstep segs c evs (SNext c') →
        exec segs c' (fun tr o => Q (evs ++ tr) o)) → exec segs c Q

theorem exec_conseq (segs : List Segment) (c : config) (Q Q' : post)
    (h : exec segs c Q) (himp : ∀ tr o, Q tr o → Q' tr o) : exec segs c Q' := by
  induction h generalizing Q' with
  | exec_halt c Q hh hq => exact exec.exec_halt _ _ hh (himp _ _ hq)
  | exec_step c Q hh hp herr hn ih =>
    apply exec.exec_step c Q' hh hp
    · intro evs hs; exact himp _ _ (herr evs hs)
    · intro evs c' hs
      exact ih evs c' hs _ (fun tr o hq => himp _ _ hq)

/-- Halted configuration: the base case, as a lemma. -/
theorem exec_halted (segs : List Segment) (c : config) (Q : post)
    (hh : m_halted c.cfg_model ≠ none) (hq : Q [] (OHalt c)) : exec segs c Q :=
  exec.exec_halt c Q hh hq

theorem exec_step_only (segs : List Segment) (c : config) (Q : post)
    (evs1 : List event) (c1 : config)
    (hs : sstep segs c evs1 (SNext c1))
    (honly : ∀ evs st, sstep segs c evs st → evs = evs1 ∧ st = SNext c1)
    (hex : exec segs c1 (fun tr o => Q (evs1 ++ tr) o)) : exec segs c Q := by
  apply exec.exec_step c Q (sstep_from_running _ _ _ _ hs) ⟨evs1, SNext c1, hs⟩
  · intro evs he
    obtain ⟨_, hbad⟩ := honly _ _ he
    cases hbad
  · intro evs c' hn
    obtain ⟨rfl, heq⟩ := honly _ _ hn
    cases heq
    exact hex

theorem exec_star (segs : List Segment) (c : config) (Q : post) (tr : List event)
    (c' : config) (hex : exec segs c Q) (hs : star segs c tr c') :
    exec segs c' (fun tr' o => Q (tr ++ tr') o) := by
  induction hs generalizing Q with
  | star_refl _ => exact hex
  | star_step c evs c1 tr c2 hstep _ ih =>
    cases hex with
    | exec_halt _ _ hh _ => exact False.elim (hh (sstep_from_running _ _ _ _ hstep))
    | exec_step _ _ _ _ _ hn =>
      apply exec_conseq _ _ _ _ (ih _ (hn evs c1 hstep))
      intro tr' o hq
      simpa only [List.append_assoc] using hq

theorem exec_sound (segs : List Segment) (c : config) (Q : post) (hex : exec segs c Q) :
    ∀ tr o, mexec segs c tr o → Q tr o := by
  induction hex with
  | exec_halt c Q hh hq =>
    intro tr o hm
    cases hm with
    | mexec_halt _ _ => exact hq
    | mexec_error _ _ hs => exact False.elim (hh (sstep_from_running _ _ _ _ hs))
    | mexec_next _ _ _ _ _ hs _ => exact False.elim (hh (sstep_from_running _ _ _ _ hs))
  | exec_step c Q hh hp herr hn ih =>
    intro tr o hm
    cases hm with
    | mexec_halt _ hhalt => exact False.elim (hhalt hh)
    | mexec_error _ _ hs => exact herr _ hs
    | mexec_next _ evs c' tr' o hs hm => exact ih evs c' hs tr' o hm

theorem exec_realizes (segs : List Segment) (c : config) (Q : post) (hex : exec segs c Q) :
    ∃ tr o, mexec segs c tr o ∧ Q tr o := by
  induction hex with
  | exec_halt c Q hh hq => exact ⟨[], OHalt c, mexec.mexec_halt _ hh, hq⟩
  | exec_step c Q hh hp herr hn ih =>
    obtain ⟨evs, st, hs⟩ := hp
    cases st with
    | SError => exact ⟨evs, OError c, mexec.mexec_error _ _ hs, herr _ hs⟩
    | SNext c' =>
      obtain ⟨tr, o, hm, hq⟩ := ih evs c' hs
      exact ⟨evs ++ tr, o, mexec.mexec_next _ _ _ _ _ hs hm, hq⟩

theorem exec_no_error (segs : List Segment) (c : config)
    (hex : exec segs c never_errors) : ¬ reaches_error segs c := by
  rintro ⟨tr, c2, evs, hs, he⟩
  exact exec_sound _ _ _ hex _ _
    (star_mexec _ _ _ _ _ _ hs (mexec.mexec_error _ _ he)) True.intro

theorem exec_obs_iff (segs : List Segment) (c : config) (full : List event)
    (hex : exec segs c (fun tr o => tr = full ∧ ¬ is_error o)) (tr : List event) :
    obs_trace segs c tr ↔ is_prefix tr full := by
  constructor
  · rintro ⟨tr', c', hs, hp⟩
    obtain ⟨tr'', o, _, heq, _⟩ := exec_realizes _ _ _ (exec_star _ _ _ _ _ hex hs)
    rw [← heq]
    exact is_prefix_trans _ _ _ hp (is_prefix_app _ _)
  · intro hp
    obtain ⟨tr', o, hm, heq, hno⟩ := exec_realizes _ _ _ hex
    cases o with
    | OError c' => exact False.elim (hno True.intro)
    | OHalt c' =>
      subst tr'
      exact ⟨full, c', (mexec_halt_star _ _ _ _ hm _ rfl).1, hp⟩

theorem exec_errors_all_traces_error (segs : List Segment) (c : config) (Q : post)
    (h : exec segs c Q) (himp : ∀ tr o, Q tr o → is_error o) : all_traces_error segs c := by
  induction h with
  | exec_halt c Q _ hq => exact False.elim (himp _ _ hq)
  | exec_step c Q _ hp _ hn ih =>
    apply all_traces_error.all_traces_error_intro c hp
    intro evs c' hs
    exact ih evs c' hs (fun tr o hq => himp (evs ++ tr) o hq)

theorem all_traces_error_iff (segs : List Segment) (c : config) :
    all_traces_error segs c ↔ exec segs c errors := by
  constructor
  · intro h
    induction h with
    | all_traces_error_intro c hp hn ih =>
      obtain ⟨evs, st, hs⟩ := hp
      exact exec.exec_step c errors (sstep_from_running _ _ _ _ hs) ⟨evs, st, hs⟩
        (fun _ _ => True.intro) (fun evs c' hs => ih evs c' hs)
  · intro h
    exact exec_errors_all_traces_error _ _ _ h (fun _ _ h => h)

coinductive coexec (segs : List Segment) : config → post → Prop where
  | coexec_halt : ∀ c Q, m_halted c.cfg_model ≠ none → Q [] (OHalt c) → coexec segs c Q
  | coexec_step : ∀ c Q,
      m_halted c.cfg_model = none →
      (∀ evs, sstep segs c evs SError → Q evs (OError c)) →
      (∀ evs c', sstep segs c evs (SNext c') →
        coexec segs c' (fun tr o => Q (evs ++ tr) o)) → coexec segs c Q

theorem exec_coexec (segs : List Segment) (c : config) (Q : post)
    (h : exec segs c Q) : coexec segs c Q := by
  induction h with
  | exec_halt c Q hh hq => exact coexec.coexec_halt segs c Q hh hq
  | exec_step c Q hh _ herr _ ih =>
    exact coexec.coexec_step segs c Q hh herr (fun evs c' hs => ih evs c' hs)

theorem coexec_conseq (segs : List Segment) (c : config) (Q Q' : post)
    (h : coexec segs c Q) (himp : ∀ tr o, Q tr o → Q' tr o) : coexec segs c Q' := by
  apply coexec.coinduct segs
    (fun c Q' => ∃ Q, coexec segs c Q ∧ ∀ tr o, Q tr o → Q' tr o)
  · intro c Q' h
    obtain ⟨Q, h, himp⟩ := h
    cases h with
    | coexec_halt c Q hh hq => exact Or.inl ⟨hh, himp _ _ hq⟩
    | coexec_step c Q hh herr hn =>
      exact Or.inr ⟨hh, fun evs hs => himp _ _ (herr evs hs),
        fun evs c' hs => ⟨_, hn evs c' hs, fun tr o hq => himp _ _ hq⟩⟩
  · exact ⟨Q, h, himp⟩

/-- The single-transition rule, as for `exec_step_only`. -/
theorem coexec_step_only (segs : List Segment) (c : config) (Q : post)
    (evs1 : List event) (c1 : config)
    (hs : sstep segs c evs1 (SNext c1))
    (honly : ∀ evs st, sstep segs c evs st → evs = evs1 ∧ st = SNext c1)
    (hco : coexec segs c1 (fun tr o => Q (evs1 ++ tr) o)) : coexec segs c Q := by
  apply coexec.coexec_step segs c Q (sstep_from_running _ _ _ _ hs)
  · intro evs he
    obtain ⟨_, hbad⟩ := honly _ _ he
    cases hbad
  · intro evs c' hn
    obtain ⟨rfl, heq⟩ := honly _ _ hn
    cases heq
    exact hco

theorem coexec_star (segs : List Segment) (c : config) (Q : post) (tr : List event)
    (c' : config) (hex : coexec segs c Q) (hs : star segs c tr c') :
    coexec segs c' (fun tr' o => Q (tr ++ tr') o) := by
  induction hs generalizing Q with
  | star_refl _ => exact hex
  | star_step c evs c1 tr c2 hstep _ ih =>
    cases hex with
    | coexec_halt _ _ hh _ => exact False.elim (hh (sstep_from_running _ _ _ _ hstep))
    | coexec_step _ _ _ _ hn =>
      apply coexec_conseq _ _ _ _ (ih _ (hn evs c1 hstep))
      intro tr' o hq
      simpa only [List.append_assoc] using hq

theorem coexec_sound (segs : List Segment) (c : config) (tr : List event) (o : outcome)
    (hm : mexec segs c tr o) (Q : post) (hco : coexec segs c Q) : Q tr o := by
  induction hm generalizing Q with
  | mexec_halt c hh =>
    cases hco with
    | coexec_halt _ _ _ hq => exact hq
    | coexec_step _ _ hn _ _ => exact False.elim (hh hn)
  | mexec_error c evs hs =>
    cases hco with
    | coexec_halt _ _ hh _ => exact False.elim (hh (sstep_from_running _ _ _ _ hs))
    | coexec_step _ _ _ herr _ => exact herr evs hs
  | mexec_next c evs c' tr o hs _ ih =>
    cases hco with
    | coexec_halt _ _ hh _ => exact False.elim (hh (sstep_from_running _ _ _ _ hs))
    | coexec_step _ _ _ _ hn => exact ih _ (hn evs c' hs)

/-- The silent reading of a stuck configuration: it satisfies every
`coexec`, whatever the postcondition.  A stuck configuration is where this
reading and the progress-carrying one differ
(`Checks.Omni.stuck_not_coexec_progress`). -/
theorem stuck_coexec_any (segs : List Segment) (c : config)
    (hh : m_halted c.cfg_model = none) (hstuck : ∀ evs st, ¬ sstep segs c evs st)
    (Q : post) : coexec segs c Q :=
  coexec.coexec_step segs c Q hh (fun _ hs => False.elim (hstuck _ _ hs))
    (fun _ _ hs => False.elim (hstuck _ _ hs))

theorem coexec_no_error (segs : List Segment) (c : config)
    (hco : coexec segs c never_errors) : ¬ reaches_error segs c := by
  rintro ⟨tr, c2, evs, hs, he⟩
  exact coexec_sound _ _ _ _ (star_mexec _ _ _ _ _ _ hs (mexec.mexec_error _ _ he)) _ hco
    True.intro

theorem coexec_covered (segs : List Segment) (c : config)
    (hco : coexec segs c (covered segs)) : ¬ reaches_unmodeled segs c := by
  rintro ⟨tr, c', hs, hu⟩
  obtain ⟨evs, he⟩ := unmodeled_at_sstep_error _ _ hu
  exact coexec_sound _ _ _ _ (star_mexec _ _ _ _ _ _ hs (mexec.mexec_error _ _ he)) _ hco hu

theorem no_error_coexec (segs : List Segment) (c : config)
    (hno : ¬ reaches_error segs c) : coexec segs c never_errors := by
  classical
  apply coexec.coinduct segs
    (fun c Q => (¬ reaches_error segs c) ∧ ∀ tr o, never_errors tr o → Q tr o)
  · intro c Q h
    obtain ⟨hno, hq⟩ := h
    by_cases hh : m_halted c.cfg_model = none
    · refine Or.inr ⟨hh, ?_, ?_⟩
      · intro evs hs
        exact False.elim (hno ⟨[], c, evs, star.star_refl c, hs⟩)
      · intro evs c' hs
        refine ⟨?_, fun tr o hn => hq (evs ++ tr) o hn⟩
        rintro ⟨tr, c2, evs2, ht, he⟩
        exact hno ⟨evs ++ tr, c2, evs2, star.star_step _ _ _ _ _ hs ht, he⟩
    · exact Or.inl ⟨hh, hq [] (OHalt c) (fun h => h)⟩
  · exact ⟨hno, fun _ _ h => h⟩

theorem never_errors_iff (segs : List Segment) (c : config) :
    (¬ reaches_error segs c) ↔ coexec segs c never_errors :=
  ⟨no_error_coexec segs c, coexec_no_error segs c⟩

theorem no_unmodeled_coexec (segs : List Segment) (c : config)
    (hno : ¬ reaches_unmodeled segs c) : coexec segs c (covered segs) := by
  classical
  apply coexec.coinduct segs
    (fun c Q => (¬ reaches_unmodeled segs c) ∧ ∀ tr o, covered segs tr o → Q tr o)
  · intro c Q h
    obtain ⟨hno, hq⟩ := h
    by_cases hh : m_halted c.cfg_model = none
    · refine Or.inr ⟨hh, ?_, ?_⟩
      · intro evs _
        apply hq evs (OError c)
        intro hu
        exact hno ⟨[], c, star.star_refl c, hu⟩
      · intro evs c' hs
        refine ⟨?_, fun tr o hn => hq (evs ++ tr) o hn⟩
        rintro ⟨tr, c2, ht, hu⟩
        exact hno ⟨evs ++ tr, c2, star.star_step _ _ _ _ _ hs ht, hu⟩
    · exact Or.inl ⟨hh, hq [] (OHalt c) True.intro⟩
  · exact ⟨hno, fun _ _ h => h⟩

theorem covered_iff (segs : List Segment) (c : config) :
    (¬ reaches_unmodeled segs c) ↔ coexec segs c (covered segs) :=
  ⟨no_unmodeled_coexec segs c, coexec_covered segs c⟩

coinductive cosafe (segs : List Segment) : config → (List event → Prop) → Prop where
  | cosafe_intro : ∀ c P, P [] →
      (∀ evs c', sstep segs c evs (SNext c') → cosafe segs c' (fun tr => P (evs ++ tr))) →
      cosafe segs c P

theorem cosafe_star (segs : List Segment) (c : config) (P : List event → Prop)
    (tr : List event) (c' : config) (hco : cosafe segs c P) (hs : star segs c tr c') : P tr := by
  induction hs generalizing P with
  | star_refl c => cases hco with | cosafe_intro _ _ hnil _ => exact hnil
  | star_step c evs c1 tr c2 hstep _ ih =>
    cases hco with | cosafe_intro _ _ _ hn => exact ih _ (hn evs c1 hstep)

theorem star_cosafe (segs : List Segment) (c : config) (P : List event → Prop)
    (hall : ∀ tr c', star segs c tr c' → P tr) : cosafe segs c P := by
  apply cosafe.coinduct segs (fun c P => ∀ tr c', star segs c tr c' → P tr)
  · intro c P h
    refine ⟨h [] c (star.star_refl c), ?_⟩
    intro evs c' hs tr c'' ht
    exact h (evs ++ tr) c'' (star.star_step _ _ _ _ _ hs ht)
  · exact hall

def prefix_closed (P : List event → Prop) : Prop :=
  ∀ tr tr', P tr → is_prefix tr' tr → P tr'

theorem obs_trace_is_prefix_closed (segs : List Segment) (c : config) :
    prefix_closed (obs_trace segs c) :=
  fun _ _ ht hp => obs_trace_prefix_closed _ _ _ _ ht hp

theorem cosafe_obs_iff (segs : List Segment) (c : config) (P : List event → Prop)
    (hpc : prefix_closed P) : cosafe segs c P ↔ ∀ tr, obs_trace segs c tr → P tr := by
  constructor
  · intro hc tr ht
    obtain ⟨tr', c', hs, hp⟩ := ht
    exact hpc _ _ (cosafe_star _ _ _ _ _ hc hs) hp
  · intro hall
    apply star_cosafe
    intro tr c' hs
    exact hall tr ⟨tr, c', hs, is_prefix_refl _⟩

/-- The refinement pair: each side's trace set is a prefix postcondition
the other side satisfies.  Stated for two images, since the two runs of an
equivalence load different segments. -/
theorem obs_equiv_iff_refinement (segs1 : List Segment) (c1 : config)
    (segs2 : List Segment) (c2 : config) :
    (∀ tr, obs_trace segs1 c1 tr ↔ obs_trace segs2 c2 tr) ↔
    (cosafe segs1 c1 (obs_trace segs2 c2) ∧ cosafe segs2 c2 (obs_trace segs1 c1)) := by
  rw [cosafe_obs_iff segs1 c1 _ (obs_trace_is_prefix_closed segs2 c2),
    cosafe_obs_iff segs2 c2 _ (obs_trace_is_prefix_closed segs1 c1)]
  exact ⟨fun he => ⟨fun tr ht => (he tr).1 ht, fun tr ht => (he tr).2 ht⟩,
    fun ⟨h12, h21⟩ tr => ⟨h12 tr, h21 tr⟩⟩

theorem obs_equiv_iff_cosafe (segs1 : List Segment) (c1 : config)
    (segs2 : List Segment) (c2 : config) :
    (∀ tr, obs_trace segs1 c1 tr ↔ obs_trace segs2 c2 tr) ↔
    (∀ P, prefix_closed P → (cosafe segs1 c1 P ↔ cosafe segs2 c2 P)) := by
  constructor
  · intro he P hpc
    rw [cosafe_obs_iff _ _ _ hpc, cosafe_obs_iff _ _ _ hpc]
    exact ⟨fun h tr ht => h tr ((he tr).2 ht), fun h tr ht => h tr ((he tr).1 ht)⟩
  · intro he tr
    have hself (segs : List Segment) (c : config) : cosafe segs c (obs_trace segs c) := by
      apply star_cosafe
      intro tr c' hs
      exact ⟨tr, c', hs, is_prefix_refl _⟩
    have h12 := (he _ (obs_trace_is_prefix_closed segs2 c2)).2 (hself segs2 c2)
    have h21 := (he _ (obs_trace_is_prefix_closed segs1 c1)).1 (hself segs1 c1)
    exact ⟨fun h => (cosafe_obs_iff _ _ _ (obs_trace_is_prefix_closed _ _)).1 h12 tr h,
      fun h => (cosafe_obs_iff _ _ _ (obs_trace_is_prefix_closed _ _)).1 h21 tr h⟩

def omni_run (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) (Q : post) : Prop :=
  exec img.img_segments (init_config img.img_segments img.img_init_pc img.img_phdrs
    en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp) Q

def omni_corun (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) (Q : post) : Prop :=
  coexec img.img_segments (init_config img.img_segments img.img_init_pc img.img_phdrs
    en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp) Q

def omni_cosafe (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (P : List event → Prop) : Prop :=
  cosafe img.img_segments (init_config img.img_segments img.img_init_pc img.img_phdrs
    en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp) P

/-- SOME maximal execution satisfies `Q`: the existential twin. -/
def omni_may (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) (Q : post) : Prop :=
  ∃ tr o, mexec img.img_segments (init_config img.img_segments img.img_init_pc img.img_phdrs
    en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp) tr o ∧ Q tr o

/-- The progress premise excludes vacuity even when the postcondition is true. -/
theorem stuck_no_exec (segs : List Segment) (c : config)
    (hh : m_halted c.cfg_model = none)
    (hstuck : ∀ evs st, ¬ sstep segs c evs st) (Q : post) : ¬ exec segs c Q := by
  intro h
  cases h with
  | exec_halt _ _ hn _ => exact hn hh
  | exec_step _ _ _ hp _ _ =>
    obtain ⟨evs, st, hs⟩ := hp
    exact hstuck evs st hs

/-- At a halted configuration `exec` is the postcondition alone: the trivial
one is met…  Lean-only, with `halted_rejects_false`; `OmniRun.v` has
neither. -/
theorem halted_accepts_true (segs : List Segment) (c : config)
    (hh : m_halted c.cfg_model ≠ none) : exec segs c (fun _ _ => True) :=
  exec.exec_halt _ _ hh True.intro

/-- …and the empty one is not, since a halted configuration takes no step
for `exec` to go on through.  Lean-only. -/
theorem halted_rejects_false (segs : List Segment) (c : config)
    (hh : m_halted c.cfg_model ≠ none) : ¬ exec segs c (fun _ _ => False) := by
  intro h
  cases h with
  | exec_halt _ _ _ hq => exact hq
  | exec_step _ _ hn _ _ _ => exact hh hn

/-! ## Compat: the four fields of `Run.run`, each unconditional -/

theorem bh_all_errors_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (run img lim en inp).bh_all_errors ↔ omni_run img lim en inp errors :=
  all_traces_error_iff _ _

theorem bh_errors_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ (run img lim en inp).bh_errors ↔ omni_corun img lim en inp never_errors :=
  never_errors_iff _ _

theorem bh_errors_may_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (run img lim en inp).bh_errors ↔ omni_may img lim en inp errors :=
  reaches_error_iff_may _ _

theorem bh_unmodeled_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ (run img lim en inp).bh_unmodeled ↔ omni_corun img lim en inp (covered img.img_segments) :=
  covered_iff _ _

theorem bh_unmodeled_may_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (run img lim en inp).bh_unmodeled ↔ omni_may img lim en inp (uncovered img.img_segments) :=
  reaches_unmodeled_iff_may _ _

/-- Trace-set equality of two runs is agreement on every prefix-closed
postcondition; `OmniEquivalence.trace_equiv_iff_omni` restates it through
`Equivalence.trace_equiv`. -/
theorem bh_traces_iff (img1 : Image) (lim1 : Int) (en1 : ExecEntry) (img2 : Image) (lim2 : Int)
    (en2 : ExecEntry) (inp : ProcInput) :
    (∀ tr, (run img1 lim1 en1 inp).bh_traces tr ↔ (run img2 lim2 en2 inp).bh_traces tr)
    ↔ (∀ P, prefix_closed P →
         (omni_cosafe img1 lim1 en1 inp P ↔ omni_cosafe img2 lim2 en2 inp P)) :=
  obs_equiv_iff_cosafe _ _ _ _

end LinuxProcessSemantics.LinuxProcessSem.OmniRun
