import LinuxProcessSemantics.LinuxProcessSem.Run

/-! rocq-baseline: 1807c1e25ce12708f5cc85213f2df4bf03d978da -/

/-! # EquivalenceDefinition.MustExit — every maximal execution exits with one code

Mirrors `theories/EquivalenceDefinition/MustExit.v`.

TRUST BOUNDARY: this file is part of the trusted specification.

`must_exit_at` is an accessibility predicate over the `Run.SNext`
transitions, following `Run.all_traces_error`'s shape, with three
premises each buying one property: INDUCTIVE for termination (a
configuration with an infinite `SNext` execution cannot construct the
proof), PROGRESS against stuck configurations, and `SError`-REFUTATION
against faulting ones — plus the `∀`-over-successors premise so that one
exiting resolution cannot hide a sibling that does something else.  The
exit code is compared DIRECTLY, not masked here: `Sys.Kernel.Exit.exit_spec`
is the one place the low byte is defined.  A DEATH BY SIGNAL IS NOT AN
EXIT: the halted case carries `m_killed = none`, so a process killed by
SIGABRT — whose `m_halted` holds the signal number — does not satisfy
the predicate at code 6 (ticket A12; the same conjunct sits on
`OmniRun.exits_with`).  The full argument, and the non-vacuity guard,
are on the Rocq file. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.MustExit

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Run

/-! ## Three facts about `Run.sstep` that the lemmas below rely on -/

/-- Nothing steps out of a halted configuration. -/
theorem sstep_not_halted (segs : List Segment) (c : config) (evs : List event) (st : step_to) :
    sstep segs c evs st → m_halted c.cfg_model = none := by
  intro hss
  cases hss <;> assumption

/-- A `Run.star` out of a halted configuration is the empty one. -/
theorem star_from_halted (segs : List Segment) (c : config) (tr : List event) (c' : config) :
    star segs c tr c' → m_halted c.cfg_model ≠ none → tr = [] ∧ c' = c := by
  intro hstar hh
  cases hstar with
  | star_refl _ => exact ⟨rfl, rfl⟩
  | star_step _ evs c1 tr1 _ hss _ => exact absurd (sstep_not_halted _ _ _ _ hss) hh

/-- The step that HALTS a configuration is one of the two terminal steps:
the exit step, which emits the `ExitEv` carrying the stored code and
leaves the kill flag clear, or the kill step, which emits the `KillEv`
carrying the signal; every other successor transition leaves `m_halted`
alone.  `must_exit_at_realizes` needs exactly this, and the kill flag is
what lets it tell the two apart. -/
theorem sstep_next_halts_by_exit (segs : List Segment) (c : config) (evs : List event) (c' : config) :
    sstep segs c evs (SNext c') →
    m_halted c'.cfg_model = none
    ∨ (∃ evs0 code,
         evs = evs0 ++ [ExitEv code (m_fs c'.cfg_model)]
         ∧ m_halted c'.cfg_model = some code
         ∧ m_killed c'.cfg_model = none)
    ∨ (∃ evs0 sig,
         evs = evs0 ++ [KillEv sig (m_fs c'.cfg_model)]
         ∧ m_killed c'.cfg_model = some sig) := by
  intro hss
  cases hss with
  | sstep_instr ms model ms' model' hh _ hacc =>
    left
    obtain ⟨_, _, _, _, _, hproc, _⟩ := mi_account_step_model_frame segs _ _ _ _ hacc
    show m_halted model' = none
    unfold m_halted at hh ⊢
    rw [hproc]
    exact hh
  | sstep_syscall ms model x8 eff model' model'' evs1 hh hsvc hspec hh' hmat =>
    left
    obtain ⟨_, _, _, _, _, hproc, _⟩ := materialize_model_accesses_frame _ _ _ hmat
    show m_halted model'' = none
    unfold m_halted at hh' ⊢
    rw [hproc]
    exact hh'
  | sstep_exit ms model x8 eff model' evs1 code hh hsvc hspec hh' hk =>
    right; left
    exact ⟨evs1, code, rfl, hh', hk⟩
  | sstep_killed ms model x8 eff model' evs1 sig hh hsvc hspec hk =>
    right; right
    exact ⟨evs1, sig, rfl, hk⟩

/-! ## The predicate -/

/-- Every maximal execution from `c` halts, after finitely many steps,
with `m_halted` equal to `some code` — by an EXIT, not by a signal: the
halted case requires `m_killed` to be `none`. -/
inductive must_exit_at (segs : List Segment) (code : word) : config → Prop
  | must_exit_at_halted : ∀ c,
      m_halted c.cfg_model = some code →
      m_killed c.cfg_model = none →
      must_exit_at segs code c
  | must_exit_at_running : ∀ c,
      m_halted c.cfg_model = none →
      (∃ evs st, sstep segs c evs st) →
      (∀ evs, ¬ sstep segs c evs SError) →
      (∀ evs c', sstep segs c evs (SNext c') → must_exit_at segs code c') →
      must_exit_at segs code c

/-- The run-level statement: every execution of `img` from the `execve`
choices `en` on inputs `inp`, under the memory budget `lim`, exits with
`code`.  Consumes the image and the entry exactly as `Run.run` does, so
the two always speak about the SAME configuration. -/
def must_exit_with (code : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  must_exit_at img.img_segments code
    (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

/-! ## What the predicate rules out: errors, and hence unmodeled behavior -/

theorem must_exit_at_no_error (segs : List Segment) (code : word) (c : config) :
    must_exit_at segs code c → ¬ reaches_error segs c := by
  intro hme
  induction hme with
  | must_exit_at_halted c hh _ =>
    rintro ⟨tr, c2, evs, hstar, hsserr⟩
    have hne : m_halted c.cfg_model ≠ none := by rw [hh]; nofun
    obtain ⟨_, rfl⟩ := star_from_halted _ _ _ _ hstar hne
    have := sstep_not_halted _ _ _ _ hsserr
    rw [hh] at this
    exact absurd this nofun
  | must_exit_at_running c _ _ hnoerr _ ih =>
    rintro ⟨tr, c2, evs, hstar, hsserr⟩
    cases hstar with
    | star_refl _ => exact hnoerr evs hsserr
    | star_step _ evs0 c1 tr1 _ hss hstar1 =>
      exact ih evs0 c1 hss ⟨tr1, c2, evs, hstar1, hsserr⟩

theorem must_exit_with_no_error (code : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with code img lim en inp → ¬ (run img lim en inp).bh_errors :=
  fun hme => must_exit_at_no_error _ _ _ hme

theorem must_exit_with_modeled (code : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with code img lim en inp → ¬ (run img lim en inp).bh_unmodeled :=
  fun hme => no_error_no_unmodeled _ _ (must_exit_with_no_error _ _ _ _ _ hme)

/-! ## The code is unique -/

theorem must_exit_at_exclusive (segs : List Segment) (code1 code2 : word) (c : config) :
    must_exit_at segs code1 c → must_exit_at segs code2 c → code1 = code2 := by
  intro h1
  induction h1 with
  | must_exit_at_halted c hh _ =>
    intro h2
    cases h2 with
    | must_exit_at_halted _ hh2 _ => rw [hh] at hh2; exact Option.some.inj hh2
    | must_exit_at_running _ hnone _ _ _ => rw [hh] at hnone; exact absurd hnone nofun
  | must_exit_at_running c hnone hprog hnoerr _ ih =>
    intro h2
    cases h2 with
    | must_exit_at_halted _ hh2 _ => rw [hh2] at hnone; exact absurd hnone nofun
    | must_exit_at_running _ _ _ _ hnext2 =>
      obtain ⟨evs, st, hss⟩ := hprog
      cases st with
      | SNext c' => exact ih evs c' hss (hnext2 evs c' hss)
      | SError => exact absurd hss (hnoerr evs)

theorem must_exit_with_exclusive (code1 code2 : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with code1 img lim en inp →
    must_exit_with code2 img lim en inp →
    code1 = code2 :=
  fun h1 h2 => must_exit_at_exclusive _ _ _ _ h1 h2

/-! ## Non-vacuity: the predicate really produces an exit event -/

theorem must_exit_at_realizes (segs : List Segment) (code : word) (c : config) :
    must_exit_at segs code c →
    m_halted c.cfg_model = none →
    ∃ tr fs c',
      star segs c (tr ++ [ExitEv code fs]) c'
      ∧ m_halted c'.cfg_model = some code := by
  intro hme
  induction hme with
  | must_exit_at_halted c hh _ =>
    intro hrun; rw [hh] at hrun; exact absurd hrun nofun
  | must_exit_at_running c _ hprog hnoerr hnext ih =>
    intro _
    obtain ⟨evs, st, hss⟩ := hprog
    cases st with
    | SError => exact absurd hss (hnoerr evs)
    | SNext c1 =>
      have hme1 := hnext evs c1 hss
      cases hh1 : m_halted c1.cfg_model with
      | some k =>
        have hk : k = code := by
          cases hme1 with
          | must_exit_at_halted _ hh _ => rw [hh] at hh1; exact (Option.some.inj hh1).symm
          | must_exit_at_running _ hn _ _ _ => rw [hn] at hh1; exact absurd hh1 nofun
        subst hk
        -- The successor is halted and satisfies the predicate, so by the
        -- base case it is NOT killed — which rules the kill transition out
        -- and leaves `Run.sstep_exit` as the only way in.
        have hnk : m_killed c1.cfg_model = none := by
          cases hme1 with
          | must_exit_at_halted _ _ hk => exact hk
          | must_exit_at_running _ hn _ _ _ => rw [hn] at hh1; exact absurd hh1 nofun
        rcases sstep_next_halts_by_exit _ _ _ _ hss with
          hnone1 | ⟨evs0, code0, hevs, hcode0, _⟩ | ⟨_, sig, _, hsig⟩
        · rw [hnone1] at hh1; exact absurd hh1 nofun
        · have hcc : code0 = k := by rw [hcode0] at hh1; exact Option.some.inj hh1
          subst hcc
          exact ⟨evs0, m_fs c1.cfg_model, c1, hevs ▸ star_one _ _ _ _ hss, hh1⟩
        · rw [hnk] at hsig; exact absurd hsig nofun
      | none =>
        obtain ⟨tr, fs, c', hstar, hh'⟩ := ih evs c1 hss hh1
        exact ⟨evs ++ tr, fs, c', by
          rw [List.append_assoc]; exact star.star_step _ _ _ _ _ hss hstar, hh'⟩

/-- The guard, at run level: a run that must exit with `code` has an
observable trace ending in `ExitEv code fs`. -/
theorem must_exit_with_realizes (code : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with code img lim en inp →
    ∃ tr fs, (run img lim en inp).bh_traces (tr ++ [ExitEv code fs]) := by
  intro hme
  have hnone : m_halted (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp).cfg_model = none := rfl
  obtain ⟨tr, fs, c', hstar, _⟩ := must_exit_at_realizes _ _ _ hme hnone
  exact ⟨tr, fs, tr ++ [ExitEv code fs], c', hstar, is_prefix_refl _⟩

/-! ## The predicate bites: it can be established, and it can be refuted -/

/-- POSITIVE, one step: a configuration whose every successor is already
halted with `code`, and not killed, must exit with `code`. -/
theorem must_exit_at_exit_now (segs : List Segment) (code : word) (c : config) :
    m_halted c.cfg_model = none →
    (∃ evs st, sstep segs c evs st) →
    (∀ evs, ¬ sstep segs c evs SError) →
    (∀ evs c', sstep segs c evs (SNext c') →
       m_halted c'.cfg_model = some code ∧ m_killed c'.cfg_model = none) →
    must_exit_at segs code c :=
  fun hnone hprog hnoerr hhalt =>
    must_exit_at.must_exit_at_running c hnone hprog hnoerr
      (fun evs c' hss =>
        must_exit_at.must_exit_at_halted c' (hhalt evs c' hss).1 (hhalt evs c' hss).2)

/-- NEGATIVE, the error route: a running configuration that can take the
error transition refutes the predicate for EVERY code. -/
theorem must_exit_at_refuted_by_error (segs : List Segment) (code : word) (c : config) (evs : List event) :
    m_halted c.cfg_model = none →
    sstep segs c evs SError →
    ¬ must_exit_at segs code c := by
  intro hnone hsserr hme
  cases hme with
  | must_exit_at_halted _ hh _ => rw [hh] at hnone; exact absurd hnone nofun
  | must_exit_at_running _ _ _ hnoerr _ => exact hnoerr evs hsserr

/-- NEGATIVE, the wrong-code route. -/
theorem must_exit_at_wrong_code (segs : List Segment) (code code' : word) (c : config) :
    m_halted c.cfg_model = some code →
    code ≠ code' →
    ¬ must_exit_at segs code' c := by
  intro hh hne hme
  cases hme with
  | must_exit_at_halted _ hh' _ => rw [hh] at hh'; exact hne (Option.some.inj hh')
  | must_exit_at_running _ hn _ _ _ => rw [hh] at hn; exact absurd hn nofun

/-- The run-level refutation, packaged for the example side. -/
theorem must_exit_with_refuted_by_error (code : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (run img lim en inp).bh_errors → ¬ must_exit_with code img lim en inp :=
  fun herr hme => must_exit_with_no_error _ _ _ _ _ hme herr

/-! ## The verdict predicate under a spurious-failure configuration:
`must_exit_at_cfg`, `must_exit_with_scfg`

`Run.run_scfg cfg` walks `Run.sstep_cfg cfg`, the step relation with
every avoidable refusal of a forced-only family removed.  The verdict
predicate follows: `must_exit_at_cfg cfg` is `must_exit_at` over that
relation, premise for premise, and `must_exit_with_scfg cfg` is its
run-level form.  At `Run.may_fail_cfg` it is `must_exit_with` itself
(`must_exit_with_scfg_may_fail`).

This is the predicate the classifier layer pins its verdicts to, at
`Run.forced_only_cfg`, and the reason is
issue #583: a classifier that reads its input cannot decide anything
under a reading where the open may be refused without cause, since
the refused run reaches neither verdict.  Under forced-only the
refusal is gone wherever the open could have succeeded, and what
remains of the obligation is what a decision procedure should be
asked — every execution the environment can FORCE ends in the right
verdict.

What the pin costs, stated once: the progress premise of
`must_exit_at_cfg_running` is over the FILTERED relation, and
filtering can only make it harder to meet.  It cannot make it
impossible where the filter's question is answered — `Run.sstep_cfg_progress`
— and that is what `must_exit_at_cfg_mono` below turns into the
statement that a verdict under may-fail is a verdict under every
configuration: the pin is a WEAKENING of the obligation, never a
different one. -/

inductive must_exit_at_cfg (cfg : SpuriousCfg) (segs : List Segment) (code : word) : config → Prop
  | must_exit_at_cfg_halted : ∀ c,
      m_halted c.cfg_model = some code →
      m_killed c.cfg_model = none →
      must_exit_at_cfg cfg segs code c
  | must_exit_at_cfg_running : ∀ c,
      m_halted c.cfg_model = none →
      (∃ evs st, sstep_cfg segs cfg c evs st) →
      (∀ evs, ¬ sstep_cfg segs cfg c evs SError) →
      (∀ evs c', sstep_cfg segs cfg c evs (SNext c') → must_exit_at_cfg cfg segs code c') →
      must_exit_at_cfg cfg segs code c

/-- The three facts about `Run.sstep` used above carry to the filtered
relation through `Run.sstep_cfg_sub`. -/
theorem sstep_cfg_not_halted (segs : List Segment) (cfg : SpuriousCfg)
    (c : config) (evs : List event) (st : step_to) :
    sstep_cfg segs cfg c evs st → m_halted c.cfg_model = none :=
  fun hss => sstep_not_halted _ _ _ _ (sstep_cfg_sub _ _ _ _ _ hss)

theorem star_cfg_from_halted (segs : List Segment) (cfg : SpuriousCfg) (c : config) (tr : List event) (c' : config) :
    star_cfg segs cfg c tr c' → m_halted c.cfg_model ≠ none → tr = [] ∧ c' = c := by
  intro hstar hh
  cases hstar with
  | star_cfg_refl _ => exact ⟨rfl, rfl⟩
  | star_cfg_step _ evs c1 tr1 _ hss _ => exact absurd (sstep_cfg_not_halted _ _ _ _ _ hss) hh

theorem sstep_cfg_next_halts_by_exit (segs : List Segment) (cfg : SpuriousCfg) (c : config) (evs : List event) (c' : config) :
    sstep_cfg segs cfg c evs (SNext c') →
    m_halted c'.cfg_model = none
    ∨ (∃ evs0 code,
         evs = evs0 ++ [ExitEv code (m_fs c'.cfg_model)]
         ∧ m_halted c'.cfg_model = some code
         ∧ m_killed c'.cfg_model = none)
    ∨ (∃ evs0 sig,
         evs = evs0 ++ [KillEv sig (m_fs c'.cfg_model)]
         ∧ m_killed c'.cfg_model = some sig) :=
  fun hss => sstep_next_halts_by_exit _ _ _ _ (sstep_cfg_sub _ _ _ _ _ hss)

/-! ### The same five facts, for the filtered predicate -/

theorem must_exit_at_cfg_no_error (cfg : SpuriousCfg) (segs : List Segment) (code : word) (c : config) :
    must_exit_at_cfg cfg segs code c → ¬ reaches_error_cfg segs cfg c := by
  intro hme
  induction hme with
  | must_exit_at_cfg_halted c hh _ =>
    rintro ⟨tr, c2, evs, hstar, hsserr⟩
    have hne : m_halted c.cfg_model ≠ none := by rw [hh]; nofun
    obtain ⟨_, rfl⟩ := star_cfg_from_halted _ _ _ _ _ hstar hne
    have := sstep_cfg_not_halted _ _ _ _ _ hsserr
    rw [hh] at this
    exact absurd this nofun
  | must_exit_at_cfg_running c _ _ hnoerr _ ih =>
    rintro ⟨tr, c2, evs, hstar, hsserr⟩
    cases hstar with
    | star_cfg_refl _ => exact hnoerr evs hsserr
    | star_cfg_step _ evs0 c1 tr1 _ hss hstar1 =>
      exact ih evs0 c1 hss ⟨tr1, c2, evs, hstar1, hsserr⟩

theorem must_exit_at_cfg_exclusive (cfg : SpuriousCfg) (segs : List Segment) (code1 code2 : word) (c : config) :
    must_exit_at_cfg cfg segs code1 c → must_exit_at_cfg cfg segs code2 c → code1 = code2 := by
  intro h1
  induction h1 with
  | must_exit_at_cfg_halted c hh _ =>
    intro h2
    cases h2 with
    | must_exit_at_cfg_halted _ hh2 _ => rw [hh] at hh2; exact Option.some.inj hh2
    | must_exit_at_cfg_running _ hnone _ _ _ => rw [hh] at hnone; exact absurd hnone nofun
  | must_exit_at_cfg_running c hnone hprog hnoerr _ ih =>
    intro h2
    cases h2 with
    | must_exit_at_cfg_halted _ hh2 _ => rw [hh2] at hnone; exact absurd hnone nofun
    | must_exit_at_cfg_running _ _ _ _ hnext2 =>
      obtain ⟨evs, st, hss⟩ := hprog
      cases st with
      | SNext c' => exact ih evs c' hss (hnext2 evs c' hss)
      | SError => exact absurd hss (hnoerr evs)

theorem must_exit_at_cfg_realizes (cfg : SpuriousCfg) (segs : List Segment) (code : word) (c : config) :
    must_exit_at_cfg cfg segs code c →
    m_halted c.cfg_model = none →
    ∃ tr fs c',
      star_cfg segs cfg c (tr ++ [ExitEv code fs]) c'
      ∧ m_halted c'.cfg_model = some code := by
  intro hme
  induction hme with
  | must_exit_at_cfg_halted c hh _ =>
    intro hrun; rw [hh] at hrun; exact absurd hrun nofun
  | must_exit_at_cfg_running c _ hprog hnoerr hnext ih =>
    intro _
    obtain ⟨evs, st, hss⟩ := hprog
    cases st with
    | SError => exact absurd hss (hnoerr evs)
    | SNext c1 =>
      have hme1 := hnext evs c1 hss
      cases hh1 : m_halted c1.cfg_model with
      | some k =>
        have hk : k = code := by
          cases hme1 with
          | must_exit_at_cfg_halted _ hh _ => rw [hh] at hh1; exact (Option.some.inj hh1).symm
          | must_exit_at_cfg_running _ hn _ _ _ => rw [hn] at hh1; exact absurd hh1 nofun
        subst hk
        -- The successor is halted and satisfies the predicate, so by the
        -- base case it is NOT killed — which rules the kill transition out
        -- and leaves `Run.sstep_exit` as the only way in.
        have hnk : m_killed c1.cfg_model = none := by
          cases hme1 with
          | must_exit_at_cfg_halted _ _ hk => exact hk
          | must_exit_at_cfg_running _ hn _ _ _ => rw [hn] at hh1; exact absurd hh1 nofun
        rcases sstep_cfg_next_halts_by_exit _ _ _ _ _ hss with
          hnone1 | ⟨evs0, code0, hevs, hcode0, _⟩ | ⟨_, sig, _, hsig⟩
        · rw [hnone1] at hh1; exact absurd hh1 nofun
        · have hcc : code0 = k := by rw [hcode0] at hh1; exact Option.some.inj hh1
          subst hcc
          exact ⟨evs0, m_fs c1.cfg_model, c1, hevs ▸ (by
            simpa only [List.append_nil] using
              (star_cfg.star_cfg_step _ _ _ _ _ hss (star_cfg.star_cfg_refl c1))), hh1⟩
        · rw [hnk] at hsig; exact absurd hsig nofun
      | none =>
        obtain ⟨tr, fs, c', hstar, hh'⟩ := ih evs c1 hss hh1
        exact ⟨evs ++ tr, fs, c', by
          rw [List.append_assoc]; exact star_cfg.star_cfg_step _ _ _ _ _ hss hstar, hh'⟩

theorem must_exit_at_cfg_refuted_by_error (cfg : SpuriousCfg) (segs : List Segment) (code : word) (c : config) (evs : List event) :
    m_halted c.cfg_model = none →
    sstep_cfg segs cfg c evs SError →
    ¬ must_exit_at_cfg cfg segs code c := by
  intro hnone hsserr hme
  cases hme with
  | must_exit_at_cfg_halted _ hh _ => rw [hh] at hnone; exact absurd hnone nofun
  | must_exit_at_cfg_running _ _ _ hnoerr _ => exact hnoerr evs hsserr

theorem must_exit_at_cfg_wrong_code (cfg : SpuriousCfg) (segs : List Segment) (code code' : word) (c : config) :
    m_halted c.cfg_model = some code →
    code ≠ code' →
    ¬ must_exit_at_cfg cfg segs code' c := by
  intro hh hne hme
  cases hme with
  | must_exit_at_cfg_halted _ hh' _ => rw [hh] at hh'; exact hne (Option.some.inj hh')
  | must_exit_at_cfg_running _ hn _ _ _ => rw [hh] at hn; exact absurd hn nofun

/-! ### Meaning at `may_fail_cfg`, and monotonicity in the configuration -/

theorem must_exit_at_cfg_may_fail (segs : List Segment) (code : word) (c : config) :
    must_exit_at_cfg may_fail_cfg segs code c ↔ must_exit_at segs code c := by
  constructor
  · intro h
    induction h with
    | must_exit_at_cfg_halted c hh hk =>
      exact must_exit_at.must_exit_at_halted c hh hk
    | must_exit_at_cfg_running c hn hp he _ ih =>
      obtain ⟨evs, st, hs⟩ := hp
      refine must_exit_at.must_exit_at_running c hn
        ⟨evs, st, (sstep_cfg_may_fail _ _ _ _).2 hs⟩ ?_ ?_
      · exact fun evs herr => he evs ((sstep_cfg_may_fail _ _ _ _).1 herr)
      · exact fun evs c' hs' => ih evs c' ((sstep_cfg_may_fail _ _ _ _).1 hs')
  · intro h
    induction h with
    | must_exit_at_halted c hh hk =>
      exact must_exit_at_cfg.must_exit_at_cfg_halted c hh hk
    | must_exit_at_running c hn hp he _ ih =>
      obtain ⟨evs, st, hs⟩ := hp
      refine must_exit_at_cfg.must_exit_at_cfg_running c hn
        ⟨evs, st, (sstep_cfg_may_fail _ _ _ _).1 hs⟩ ?_ ?_
      · exact fun evs herr => he evs ((sstep_cfg_may_fail _ _ _ _).2 herr)
      · exact fun evs c' hs' => ih evs c' ((sstep_cfg_may_fail _ _ _ _).2 hs')

/-- The filter's question is answered at every configuration reachable
from `c`, over the UNFILTERED star, which reaches everything any filtered
star does. See `Run.refusal_decided`. -/
def decided_from (cfg : SpuriousCfg) (segs : List Segment) (c : config) : Prop :=
  ∀ tr c' x8, star segs c tr c' → c'.cfg_ms.ms_svc_pending = some x8 →
    refusal_decided cfg (sys_input segs c'.cfg_ms x8) c'.cfg_model

theorem decided_from_step (cfg cfg' : SpuriousCfg) (segs : List Segment)
    (c : config) (evs : List event) (c' : config) :
    decided_from cfg segs c → sstep_cfg segs cfg' c evs (SNext c') →
    decided_from cfg segs c' := by
  intro hd hs tr c'' x8 ht hv
  exact hd (evs ++ tr) c'' x8
    (star.star_step _ _ _ _ _ (sstep_cfg_sub _ _ _ _ _ hs) ht) hv

/-- A verdict under a configuration is a verdict under every SMALLER
one wherever the filter's question is answered along the way. Progress is
`Run.sstep_cfg_progress`; the error and successor premises use
`Run.sstep_cfg_mono`, since every smaller step is also a larger step. -/
theorem must_exit_at_cfg_mono (cfg1 cfg2 : SpuriousCfg) (segs : List Segment)
    (code : word) (c : config) :
    cfg_le cfg1 cfg2 → decided_from cfg1 segs c →
    must_exit_at_cfg cfg2 segs code c → must_exit_at_cfg cfg1 segs code c := by
  intro hle hd h
  induction h with
  | must_exit_at_cfg_halted c hh hk =>
    exact must_exit_at_cfg.must_exit_at_cfg_halted c hh hk
  | must_exit_at_cfg_running c hn hp he _ ih =>
    obtain ⟨evs, st, hs⟩ := hp
    refine must_exit_at_cfg.must_exit_at_cfg_running c hn ?_ ?_ ?_
    · cases c with
      | mkCfg ms model =>
        exact sstep_cfg_progress segs cfg1 ms model evs st
          (fun x8 hv => hd [] _ x8 (star.star_refl _) hv)
          (sstep_cfg_sub _ _ _ _ _ hs)
    · exact fun evs herr => he evs (sstep_cfg_mono _ _ _ _ _ _ hle herr)
    · intro evs c' hs'
      exact ih evs c' (sstep_cfg_mono _ _ _ _ _ _ hle hs')
        (decided_from_step _ _ _ _ _ _ hd hs')

/-- A verdict under may-fail is a verdict under any configuration: the pin
weakens the obligation, with the same `decided_from` premise. -/
theorem must_exit_at_cfg_of_must_exit_at (cfg : SpuriousCfg) (segs : List Segment)
    (code : word) (c : config) :
    decided_from cfg segs c → must_exit_at segs code c →
    must_exit_at_cfg cfg segs code c :=
  fun hd h => must_exit_at_cfg_mono _ _ _ _ _ (may_fail_cfg_greatest cfg) hd
    ((must_exit_at_cfg_may_fail _ _ _).2 h)

/-! ### The run-level statement -/

/-- `must_exit_with` under a configuration: the same image and entry and
initial configuration as `Run.run_scfg cfg`, so both speak about the SAME run. -/
def must_exit_with_scfg (cfg : SpuriousCfg) (code : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  must_exit_at_cfg cfg img.img_segments code
    (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

/-- Issue #570's one-switch form: `true` IS `must_exit_with` by reduction,
so its lemmas apply unchanged; `false` is the record form at
`Run.alloc_only_cfg false`. -/
def must_exit_with_cfg (alloc_may_fail : Bool) (code : word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  if alloc_may_fail then must_exit_with code img lim en inp
  else must_exit_with_scfg (alloc_only_cfg false) code img lim en inp

theorem must_exit_with_cfg_true (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_cfg true code img lim en inp = must_exit_with code img lim en inp := rfl

theorem must_exit_with_cfg_false (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_cfg false code img lim en inp =
      must_exit_with_scfg (alloc_only_cfg false) code img lim en inp := rfl

theorem must_exit_with_scfg_may_fail (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_scfg may_fail_cfg code img lim en inp ↔ must_exit_with code img lim en inp :=
  must_exit_at_cfg_may_fail _ _ _

theorem must_exit_with_scfg_no_error (cfg : SpuriousCfg) (code : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_scfg cfg code img lim en inp → ¬ (run_scfg cfg img lim en inp).bh_errors :=
  fun hme => must_exit_at_cfg_no_error _ _ _ _ hme

theorem must_exit_with_scfg_modeled (cfg : SpuriousCfg) (code : word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_scfg cfg code img lim en inp → ¬ (run_scfg cfg img lim en inp).bh_unmodeled :=
  fun hme hun => must_exit_with_scfg_no_error _ _ _ _ _ _ hme
    (run_scfg_unmodeled_errors _ _ _ _ _ hun)

theorem must_exit_with_scfg_exclusive (cfg : SpuriousCfg) (code1 code2 : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_scfg cfg code1 img lim en inp →
    must_exit_with_scfg cfg code2 img lim en inp →
    code1 = code2 :=
  fun h1 h2 => must_exit_at_cfg_exclusive _ _ _ _ _ h1 h2

/-- Non-vacuity at the verdict's interface: a configured verdict produces
`tr ++ [ExitEv code fs]` in the filtered run and hence the unfiltered run
(`must_exit_with_scfg_realizes_run`): the event is one the real program emits,
not one invented by the filter. -/
theorem must_exit_with_scfg_realizes (cfg : SpuriousCfg) (code : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_scfg cfg code img lim en inp →
    ∃ tr fs, (run_scfg cfg img lim en inp).bh_traces (tr ++ [ExitEv code fs]) := by
  intro hme
  have hnone : m_halted (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp).cfg_model = none := rfl
  obtain ⟨tr, fs, c', hstar, _⟩ := must_exit_at_cfg_realizes _ _ _ _ hme hnone
  exact ⟨tr, fs, tr ++ [ExitEv code fs], c', hstar, is_prefix_refl _⟩

theorem must_exit_with_scfg_realizes_run (cfg : SpuriousCfg) (code : word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_scfg cfg code img lim en inp →
    ∃ tr fs, (run img lim en inp).bh_traces (tr ++ [ExitEv code fs]) := by
  intro h
  obtain ⟨tr, fs, ht⟩ := must_exit_with_scfg_realizes _ _ _ _ _ _ h
  exact ⟨tr, fs, run_scfg_sub_traces _ _ _ _ _ _ ht⟩

theorem must_exit_with_scfg_refuted_by_error (cfg : SpuriousCfg) (code : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (run_scfg cfg img lim en inp).bh_errors → ¬ must_exit_with_scfg cfg code img lim en inp :=
  fun herr hme => must_exit_with_scfg_no_error _ _ _ _ _ _ hme herr

/-- The filter's question is answered on every configuration THIS run reaches. -/
def run_decided (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  decided_from cfg img.img_segments
    (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

theorem must_exit_with_scfg_mono (cfg1 cfg2 : SpuriousCfg) (code : word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    cfg_le cfg1 cfg2 → run_decided cfg1 img lim en inp →
    must_exit_with_scfg cfg2 code img lim en inp → must_exit_with_scfg cfg1 code img lim en inp :=
  fun hle hd h => must_exit_at_cfg_mono _ _ _ _ _ hle hd h

theorem must_exit_with_scfg_of_must_exit_with (cfg : SpuriousCfg) (code : word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    run_decided cfg img lim en inp → must_exit_with code img lim en inp →
    must_exit_with_scfg cfg code img lim en inp :=
  fun hd h => must_exit_with_scfg_mono _ _ _ _ _ _ _ (may_fail_cfg_greatest cfg) hd
    ((must_exit_with_scfg_may_fail _ _ _ _ _).2 h)

/-! ## The SET form: halting with a status in an ALLOWED SET

`must_exit_at` fixes ONE code, which is the right shape for a classifier
and the wrong shape for "this binary terminates cleanly, with a status
the task allows".  A program that exits 0 on one resolution of the
nondeterminism and 1 on another satisfies `must_exit_at` at NEITHER code
(`must_exit_at_exclusive` says so) and halted through `exit_group` both
times.  So the set form replaces the equality at the halted leaf with a
MEMBERSHIP, premise for premise the same predicate otherwise.

WHAT DOES NOT CARRY OVER is uniqueness: two allowed sets can both
contain the code a run exits with, and that is the point.  What replaces
`must_exit_at_exclusive` is `must_exit_in_at_mono` (a bigger set is a
weaker claim) and `must_exit_in_at_wrong_code` (halting OUTSIDE the set
is what fails). -/

/-- Every maximal execution from `c` halts, after finitely many steps,
with `m_halted` equal to `some code` for SOME `code` in `S` — by an
EXIT, not by a signal: the halted case requires `m_killed` to be
`none`.  Different branches may exit with different members of `S`. -/
inductive must_exit_in_at (segs : List Segment) (S : List word) : config → Prop
  | must_exit_in_at_halted : ∀ c code,
      m_halted c.cfg_model = some code →
      code ∈ S →
      m_killed c.cfg_model = none →
      must_exit_in_at segs S c
  | must_exit_in_at_running : ∀ c,
      m_halted c.cfg_model = none →
      (∃ evs st, sstep segs c evs st) →
      (∀ evs, ¬ sstep segs c evs SError) →
      (∀ evs c', sstep segs c evs (SNext c') → must_exit_in_at segs S c') →
      must_exit_in_at segs S c

/-- The run-level statement, consuming the image and the entry exactly as
`Run.run` does. -/
def must_exit_in (S : List word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  must_exit_in_at img.img_segments S
    (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

/-- What a halted configuration satisfying the predicate must look like.
Stated once because three proofs below take the base case apart. -/
theorem must_exit_in_at_halted_inv (segs : List Segment) (S : List word) (c : config) (code : word) :
    must_exit_in_at segs S c →
    m_halted c.cfg_model = some code →
    code ∈ S ∧ m_killed c.cfg_model = none := by
  intro hme hh
  cases hme with
  | must_exit_in_at_halted _ code0 hh0 hin0 hk0 =>
    rw [hh0] at hh
    exact (Option.some.inj hh) ▸ ⟨hin0, hk0⟩
  | must_exit_in_at_running _ hnone _ _ _ => rw [hnone] at hh; exact absurd hh nofun

/-! ### What the set form rules out -/

theorem must_exit_in_at_no_error (segs : List Segment) (S : List word) (c : config) :
    must_exit_in_at segs S c → ¬ reaches_error segs c := by
  intro hme
  induction hme with
  | must_exit_in_at_halted c code hh _ _ =>
    rintro ⟨tr, c2, evs, hstar, hsserr⟩
    have hne : m_halted c.cfg_model ≠ none := by rw [hh]; nofun
    obtain ⟨_, rfl⟩ := star_from_halted _ _ _ _ hstar hne
    have := sstep_not_halted _ _ _ _ hsserr
    rw [hh] at this
    exact absurd this nofun
  | must_exit_in_at_running c _ _ hnoerr _ ih =>
    rintro ⟨tr, c2, evs, hstar, hsserr⟩
    cases hstar with
    | star_refl _ => exact hnoerr evs hsserr
    | star_step _ evs0 c1 tr1 _ hss hstar1 =>
      exact ih evs0 c1 hss ⟨tr1, c2, evs, hstar1, hsserr⟩

theorem must_exit_in_no_error (S : List word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_in S img lim en inp → ¬ (run img lim en inp).bh_errors :=
  fun hme => must_exit_in_at_no_error _ _ _ hme

theorem must_exit_in_modeled (S : List word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_in S img lim en inp → ¬ (run img lim en inp).bh_unmodeled :=
  fun hme => no_error_no_unmodeled _ _ (must_exit_in_no_error _ _ _ _ _ hme)

/-! ### The single-code form is the singleton set -/

/-- A run that must exit with one code must exit with a status in any set
containing it. -/
theorem must_exit_at_in (segs : List Segment) (S : List word) (code : word) (c : config) :
    must_exit_at segs code c → code ∈ S → must_exit_in_at segs S c := by
  intro hme hin
  induction hme with
  | must_exit_at_halted c hh hk => exact must_exit_in_at.must_exit_in_at_halted c code hh hin hk
  | must_exit_at_running c hnone hprog hnoerr _ ih =>
    exact must_exit_in_at.must_exit_in_at_running c hnone hprog hnoerr ih

theorem must_exit_with_in (S : List word) (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_with code img lim en inp → code ∈ S → must_exit_in S img lim en inp :=
  fun hme hin => must_exit_at_in _ _ _ _ hme hin

/-- At a ONE-ELEMENT set the two are the same statement: the set form is
a generalisation rather than a different predicate. -/
theorem must_exit_in_at_singleton (segs : List Segment) (code : word) (c : config) :
    must_exit_in_at segs [code] c ↔ must_exit_at segs code c := by
  constructor
  · intro h
    induction h with
    | must_exit_in_at_halted c code0 hh hin hk =>
      rw [List.mem_singleton] at hin
      subst hin
      exact must_exit_at.must_exit_at_halted c hh hk
    | must_exit_in_at_running c hnone hprog hnoerr _ ih =>
      exact must_exit_at.must_exit_at_running c hnone hprog hnoerr ih
  · intro h
    exact must_exit_at_in _ _ _ _ h (List.mem_singleton.mpr rfl)

theorem must_exit_in_singleton (code : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_in [code] img lim en inp ↔ must_exit_with code img lim en inp :=
  must_exit_in_at_singleton _ _ _

/-! ### Monotone in the set: a wider allowance is a weaker claim -/

/-- Widening the allowed set weakens the obligation.  Only this
direction: NARROWING it does not follow. -/
theorem must_exit_in_at_mono (segs : List Segment) (S1 S2 : List word) (c : config) :
    (∀ code, code ∈ S1 → code ∈ S2) →
    must_exit_in_at segs S1 c → must_exit_in_at segs S2 c := by
  intro hsub h
  induction h with
  | must_exit_in_at_halted c code hh hin hk =>
    exact must_exit_in_at.must_exit_in_at_halted c code hh (hsub _ hin) hk
  | must_exit_in_at_running c hnone hprog hnoerr _ ih =>
    exact must_exit_in_at.must_exit_in_at_running c hnone hprog hnoerr ih

theorem must_exit_in_mono (S1 S2 : List word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (∀ code, code ∈ S1 → code ∈ S2) →
    must_exit_in S1 img lim en inp → must_exit_in S2 img lim en inp :=
  fun hsub h => must_exit_in_at_mono _ _ _ _ hsub h

/-! ### The set form bites: three refutations -/

/-- NEGATIVE, the error route: refutes the predicate for EVERY allowed set. -/
theorem must_exit_in_at_refuted_by_error (segs : List Segment) (S : List word) (c : config) (evs : List event) :
    m_halted c.cfg_model = none →
    sstep segs c evs SError →
    ¬ must_exit_in_at segs S c := by
  intro hnone hsserr hme
  cases hme with
  | must_exit_in_at_halted _ _ hh _ _ => rw [hh] at hnone; exact absurd hnone nofun
  | must_exit_in_at_running _ _ _ hnoerr _ => exact hnoerr evs hsserr

theorem must_exit_in_refuted_by_error (S : List word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (run img lim en inp).bh_errors → ¬ must_exit_in S img lim en inp :=
  fun herr hme => must_exit_in_no_error _ _ _ _ _ hme herr

/-- NEGATIVE, the wrong-status route: halting with a code the set does
not contain is what fails. -/
theorem must_exit_in_at_wrong_code (segs : List Segment) (S : List word) (code : word) (c : config) :
    m_halted c.cfg_model = some code →
    code ∉ S →
    ¬ must_exit_in_at segs S c :=
  fun hh hnin hme => hnin (must_exit_in_at_halted_inv _ _ _ _ hme hh).1

/-- NEGATIVE, the SIGNAL route.  The base case is out by its own
`m_killed` conjunct; the step case is out by `m_killed_of_m_halted_none`,
the representation invariant that a model with no halt status has no kill
status either.  A death by signal is not an allowed exit for ANY set. -/
theorem must_exit_in_at_refuted_by_kill (segs : List Segment) (S : List word) (c : config) (sig : word) :
    m_killed c.cfg_model = some sig →
    ¬ must_exit_in_at segs S c := by
  intro hk hme
  cases hme with
  | must_exit_in_at_halted _ _ _ _ hk0 => rw [hk0] at hk; exact absurd hk nofun
  | must_exit_in_at_running _ hnone _ _ _ =>
    rw [m_killed_of_m_halted_none _ hnone] at hk; exact absurd hk nofun

/-- The predicate survives a `Run.star`: a halted configuration takes no
step at all, so the walk can only be in the step case. -/
theorem must_exit_in_at_star (segs : List Segment) (S : List word) (c : config) (tr : List event) (c' : config) :
    must_exit_in_at segs S c → star segs c tr c' → must_exit_in_at segs S c' := by
  intro hme hstar
  induction hstar with
  | star_refl _ => exact hme
  | star_step _ evs c1 tr1 _ hss _ ih =>
    refine ih ?_
    cases hme with
    | must_exit_in_at_halted _ _ hh _ _ =>
      have := sstep_not_halted _ _ _ _ hss
      rw [hh] at this
      exact absurd this nofun
    | must_exit_in_at_running _ _ _ _ hnext => exact hnext evs c1 hss

/-- A run that can REACH a killed configuration refutes it: the form a
witness image hands over. -/
theorem must_exit_in_at_refuted_by_reachable_kill (segs : List Segment) (S : List word)
    (c : config) (tr : List event) (c' : config) (sig : word) :
    star segs c tr c' →
    m_killed c'.cfg_model = some sig →
    ¬ must_exit_in_at segs S c :=
  fun hstar hk hme =>
    must_exit_in_at_refuted_by_kill _ _ _ _ hk (must_exit_in_at_star _ _ _ _ _ hme hstar)

/-- "This run can die by a signal", at run level.  DELIBERATELY not the
trace-set form: getting from a `KillEv` in a trace back to the
configuration that emitted it would need to know no other transition can
emit one, which nothing here establishes. -/
def run_reaches_killed (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  ∃ tr c' sig,
    star img.img_segments
      (init_config img.img_segments img.img_init_pc img.img_phdrs
        en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp) tr c'
    ∧ m_killed c'.cfg_model = some sig

theorem must_exit_in_refuted_by_kill (S : List word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    run_reaches_killed img lim en inp → ¬ must_exit_in S img lim en inp := by
  rintro ⟨tr, c', sig, hstar, hkill⟩
  exact must_exit_in_at_refuted_by_reachable_kill _ _ _ _ _ _ hstar hkill

/-! ### Non-vacuity: the exit event carries a status the set allows -/

/-- The guard, and it is STRONGER than "some exit event happens": the
code the emitted `ExitEv` carries is itself in `S`. -/
theorem must_exit_in_at_realizes (segs : List Segment) (S : List word) (c : config) :
    must_exit_in_at segs S c →
    m_halted c.cfg_model = none →
    ∃ tr code fs c',
      code ∈ S
      ∧ star segs c (tr ++ [ExitEv code fs]) c'
      ∧ m_halted c'.cfg_model = some code := by
  intro hme
  induction hme with
  | must_exit_in_at_halted c code hh _ _ =>
    intro hrun; rw [hh] at hrun; exact absurd hrun nofun
  | must_exit_in_at_running c _ hprog hnoerr hnext ih =>
    intro _
    obtain ⟨evs, st, hss⟩ := hprog
    cases st with
    | SError => exact absurd hss (hnoerr evs)
    | SNext c1 =>
      have hme1 := hnext evs c1 hss
      cases hh1 : m_halted c1.cfg_model with
      | some k =>
        obtain ⟨hin1, hnk⟩ := must_exit_in_at_halted_inv _ _ _ _ hme1 hh1
        rcases sstep_next_halts_by_exit _ _ _ _ hss with
          hnone1 | ⟨evs0, code0, hevs, hcode0, _⟩ | ⟨_, sig, _, hsig⟩
        · rw [hnone1] at hh1; exact absurd hh1 nofun
        · have hcc : code0 = k := by rw [hcode0] at hh1; exact Option.some.inj hh1
          subst hcc
          exact ⟨evs0, code0, m_fs c1.cfg_model, c1, hin1, hevs ▸ star_one _ _ _ _ hss, hh1⟩
        · rw [hnk] at hsig; exact absurd hsig nofun
      | none =>
        obtain ⟨tr, code, fs, c', hin', hstar, hh'⟩ := ih evs c1 hss hh1
        exact ⟨evs ++ tr, code, fs, c', hin', by
          rw [List.append_assoc]; exact star.star_step _ _ _ _ _ hss hstar, hh'⟩

theorem must_exit_in_realizes (S : List word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_in S img lim en inp →
    ∃ tr code fs,
      code ∈ S ∧ (run img lim en inp).bh_traces (tr ++ [ExitEv code fs]) := by
  intro hme
  have hnone : m_halted (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp).cfg_model = none := rfl
  obtain ⟨tr, code, fs, c', hin, hstar, _⟩ := must_exit_in_at_realizes _ _ _ hme hnone
  exact ⟨tr, code, fs, hin, tr ++ [ExitEv code fs], c', hstar, is_prefix_refl _⟩

/-! ### Not yet ported

`theories/EquivalenceDefinition/HaltsAllowed.v` in full — the
`halts_allowed_T` statement family, the `ALLOWED_EXITS` module type and
the `AnyExit` instance — because Lean has no module-type sealing
surface and the statement file is written around one; the shape a Lean
twin of a sealed surface should take is an open question this port does
not settle. -/

/-! ## The set form under a spurious-failure configuration

The same relation to `must_exit_in_at` that `must_exit_at_cfg` has to
`must_exit_at`: the predicate over `Run.sstep_cfg cfg`, premise for
premise.  It is what a task pinned to `Run.forced_only_cfg` states,
for the reason that section's header gives — a binary that reads its
input decides nothing under a reading where the open may be refused
without cause — and the pin is a WEAKENING, which is
`must_exit_in_at_cfg_mono`. -/

inductive must_exit_in_at_cfg (cfg : SpuriousCfg) (segs : List Segment) (S : List word) : config → Prop
  | must_exit_in_at_cfg_halted : ∀ c code,
      m_halted c.cfg_model = some code →
      code ∈ S →
      m_killed c.cfg_model = none →
      must_exit_in_at_cfg cfg segs S c
  | must_exit_in_at_cfg_running : ∀ c,
      m_halted c.cfg_model = none →
      (∃ evs st, sstep_cfg segs cfg c evs st) →
      (∀ evs, ¬ sstep_cfg segs cfg c evs SError) →
      (∀ evs c', sstep_cfg segs cfg c evs (SNext c') → must_exit_in_at_cfg cfg segs S c') →
      must_exit_in_at_cfg cfg segs S c

def must_exit_in_scfg (cfg : SpuriousCfg) (S : List word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  must_exit_in_at_cfg cfg img.img_segments S
    (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

theorem must_exit_in_at_cfg_halted_inv (cfg : SpuriousCfg) (segs : List Segment) (S : List word) (c : config) (code : word) :
    must_exit_in_at_cfg cfg segs S c →
    m_halted c.cfg_model = some code →
    code ∈ S ∧ m_killed c.cfg_model = none := by
  intro hme hh
  cases hme with
  | must_exit_in_at_cfg_halted _ code0 hh0 hin0 hk0 =>
    rw [hh0] at hh
    exact (Option.some.inj hh) ▸ ⟨hin0, hk0⟩
  | must_exit_in_at_cfg_running _ hnone _ _ _ => rw [hnone] at hh; exact absurd hh nofun

theorem must_exit_in_at_cfg_no_error (cfg : SpuriousCfg) (segs : List Segment) (S : List word) (c : config) :
    must_exit_in_at_cfg cfg segs S c → ¬ reaches_error_cfg segs cfg c := by
  intro hme
  induction hme with
  | must_exit_in_at_cfg_halted c code hh _ _ =>
    rintro ⟨tr, c2, evs, hstar, hsserr⟩
    have hne : m_halted c.cfg_model ≠ none := by rw [hh]; nofun
    obtain ⟨_, rfl⟩ := star_cfg_from_halted _ _ _ _ _ hstar hne
    have := sstep_cfg_not_halted _ _ _ _ _ hsserr
    rw [hh] at this
    exact absurd this nofun
  | must_exit_in_at_cfg_running c _ _ hnoerr _ ih =>
    rintro ⟨tr, c2, evs, hstar, hsserr⟩
    cases hstar with
    | star_cfg_refl _ => exact hnoerr evs hsserr
    | star_cfg_step _ evs0 c1 tr1 _ hss hstar1 =>
      exact ih evs0 c1 hss ⟨tr1, c2, evs, hstar1, hsserr⟩

theorem must_exit_in_scfg_no_error (cfg : SpuriousCfg) (S : List word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_in_scfg cfg S img lim en inp → ¬ (run_scfg cfg img lim en inp).bh_errors :=
  fun hme => must_exit_in_at_cfg_no_error _ _ _ _ hme

theorem must_exit_in_scfg_modeled (cfg : SpuriousCfg) (S : List word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_in_scfg cfg S img lim en inp → ¬ (run_scfg cfg img lim en inp).bh_unmodeled :=
  fun hme hun => must_exit_in_scfg_no_error _ _ _ _ _ _ hme
    (run_scfg_unmodeled_errors _ _ _ _ _ hun)

theorem must_exit_in_scfg_refuted_by_error (cfg : SpuriousCfg) (S : List word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (run_scfg cfg img lim en inp).bh_errors → ¬ must_exit_in_scfg cfg S img lim en inp :=
  fun herr hme => must_exit_in_scfg_no_error _ _ _ _ _ _ hme herr

theorem must_exit_in_at_cfg_refuted_by_kill (cfg : SpuriousCfg) (segs : List Segment) (S : List word) (c : config) (sig : word) :
    m_killed c.cfg_model = some sig →
    ¬ must_exit_in_at_cfg cfg segs S c := by
  intro hk hme
  cases hme with
  | must_exit_in_at_cfg_halted _ _ _ _ hk0 => rw [hk0] at hk; exact absurd hk nofun
  | must_exit_in_at_cfg_running _ hnone _ _ _ =>
    rw [m_killed_of_m_halted_none _ hnone] at hk; exact absurd hk nofun

theorem must_exit_in_at_cfg_star (cfg : SpuriousCfg) (segs : List Segment) (S : List word) (c : config) (tr : List event) (c' : config) :
    must_exit_in_at_cfg cfg segs S c → star_cfg segs cfg c tr c' → must_exit_in_at_cfg cfg segs S c' := by
  intro hme hstar
  induction hstar with
  | star_cfg_refl _ => exact hme
  | star_cfg_step _ evs c1 tr1 _ hss _ ih =>
    refine ih ?_
    cases hme with
    | must_exit_in_at_cfg_halted _ _ hh _ _ =>
      have := sstep_cfg_not_halted _ _ _ _ _ hss
      rw [hh] at this
      exact absurd this nofun
    | must_exit_in_at_cfg_running _ _ _ _ hnext => exact hnext evs c1 hss

theorem must_exit_in_at_cfg_refuted_by_reachable_kill (cfg : SpuriousCfg) (segs : List Segment) (S : List word)
    (c : config) (tr : List event) (c' : config) (sig : word) :
    star_cfg segs cfg c tr c' →
    m_killed c'.cfg_model = some sig →
    ¬ must_exit_in_at_cfg cfg segs S c :=
  fun hstar hk hme =>
    must_exit_in_at_cfg_refuted_by_kill _ _ _ _ _ hk (must_exit_in_at_cfg_star _ _ _ _ _ _ hme hstar)

/-- The configured twin, over `Run.star_cfg`. -/
def run_reaches_killed_cfg (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  ∃ tr c' sig,
    star_cfg img.img_segments cfg
      (init_config img.img_segments img.img_init_pc img.img_phdrs
        en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp) tr c'
    ∧ m_killed c'.cfg_model = some sig

theorem must_exit_in_scfg_refuted_by_kill (cfg : SpuriousCfg) (S : List word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    run_reaches_killed_cfg cfg img lim en inp → ¬ must_exit_in_scfg cfg S img lim en inp := by
  rintro ⟨tr, c', sig, hstar, hkill⟩
  exact must_exit_in_at_cfg_refuted_by_reachable_kill _ _ _ _ _ _ _ hstar hkill

theorem must_exit_in_at_cfg_wrong_code (cfg : SpuriousCfg) (segs : List Segment) (S : List word) (code : word) (c : config) :
    m_halted c.cfg_model = some code →
    code ∉ S →
    ¬ must_exit_in_at_cfg cfg segs S c :=
  fun hh hnin hme => hnin (must_exit_in_at_cfg_halted_inv _ _ _ _ _ hme hh).1

theorem must_exit_in_at_cfg_mono_set (cfg : SpuriousCfg) (segs : List Segment) (S1 S2 : List word) (c : config) :
    (∀ code, code ∈ S1 → code ∈ S2) →
    must_exit_in_at_cfg cfg segs S1 c → must_exit_in_at_cfg cfg segs S2 c := by
  intro hsub h
  induction h with
  | must_exit_in_at_cfg_halted c code hh hin hk =>
    exact must_exit_in_at_cfg.must_exit_in_at_cfg_halted c code hh (hsub _ hin) hk
  | must_exit_in_at_cfg_running c hnone hprog hnoerr _ ih =>
    exact must_exit_in_at_cfg.must_exit_in_at_cfg_running c hnone hprog hnoerr ih

theorem must_exit_in_scfg_mono_set (cfg : SpuriousCfg) (S1 S2 : List word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (∀ code, code ∈ S1 → code ∈ S2) →
    must_exit_in_scfg cfg S1 img lim en inp → must_exit_in_scfg cfg S2 img lim en inp :=
  fun hsub h => must_exit_in_at_cfg_mono_set _ _ _ _ _ hsub h

/-- Non-vacuity under the configuration, then carried to the UNFILTERED
run: the exit is an event the real program emits, not one invented by a filter. -/
theorem must_exit_in_at_cfg_realizes (cfg : SpuriousCfg) (segs : List Segment) (S : List word) (c : config) :
    must_exit_in_at_cfg cfg segs S c →
    m_halted c.cfg_model = none →
    ∃ tr code fs c',
      code ∈ S
      ∧ star_cfg segs cfg c (tr ++ [ExitEv code fs]) c'
      ∧ m_halted c'.cfg_model = some code := by
  intro hme
  induction hme with
  | must_exit_in_at_cfg_halted c code hh _ _ =>
    intro hrun; rw [hh] at hrun; exact absurd hrun nofun
  | must_exit_in_at_cfg_running c _ hprog hnoerr hnext ih =>
    intro _
    obtain ⟨evs, st, hss⟩ := hprog
    cases st with
    | SError => exact absurd hss (hnoerr evs)
    | SNext c1 =>
      have hme1 := hnext evs c1 hss
      cases hh1 : m_halted c1.cfg_model with
      | some k =>
        obtain ⟨hin1, hnk⟩ := must_exit_in_at_cfg_halted_inv _ _ _ _ _ hme1 hh1
        rcases sstep_cfg_next_halts_by_exit _ _ _ _ _ hss with
          hnone1 | ⟨evs0, code0, hevs, hcode0, _⟩ | ⟨_, sig, _, hsig⟩
        · rw [hnone1] at hh1; exact absurd hh1 nofun
        · have hcc : code0 = k := by rw [hcode0] at hh1; exact Option.some.inj hh1
          subst hcc
          exact ⟨evs0, code0, m_fs c1.cfg_model, c1, hin1, hevs ▸ (by
            simpa only [List.append_nil] using
              (star_cfg.star_cfg_step _ _ _ _ _ hss (star_cfg.star_cfg_refl c1))), hh1⟩
        · rw [hnk] at hsig; exact absurd hsig nofun
      | none =>
        obtain ⟨tr, code, fs, c', hin', hstar, hh'⟩ := ih evs c1 hss hh1
        exact ⟨evs ++ tr, code, fs, c', hin', by
          rw [List.append_assoc]; exact star_cfg.star_cfg_step _ _ _ _ _ hss hstar, hh'⟩

theorem must_exit_in_scfg_realizes (cfg : SpuriousCfg) (S : List word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_in_scfg cfg S img lim en inp →
    ∃ tr code fs,
      code ∈ S ∧ (run_scfg cfg img lim en inp).bh_traces (tr ++ [ExitEv code fs]) := by
  intro hme
  have hnone : m_halted (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp).cfg_model = none := rfl
  obtain ⟨tr, code, fs, c', hin, hstar, _⟩ := must_exit_in_at_cfg_realizes _ _ _ _ hme hnone
  exact ⟨tr, code, fs, hin, tr ++ [ExitEv code fs], c', hstar, is_prefix_refl _⟩

theorem must_exit_in_scfg_realizes_run (cfg : SpuriousCfg) (S : List word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_in_scfg cfg S img lim en inp →
    ∃ tr code fs, code ∈ S ∧ (run img lim en inp).bh_traces (tr ++ [ExitEv code fs]) := by
  intro h
  obtain ⟨tr, code, fs, hin, ht⟩ := must_exit_in_scfg_realizes _ _ _ _ _ _ h
  exact ⟨tr, code, fs, hin, run_scfg_sub_traces _ _ _ _ _ _ ht⟩

/-! ### Meaning at `may_fail_cfg`, the singleton bridge, and monotonicity
in the configuration -/

theorem must_exit_in_at_cfg_may_fail (segs : List Segment) (S : List word) (c : config) :
    must_exit_in_at_cfg may_fail_cfg segs S c ↔ must_exit_in_at segs S c := by
  constructor
  · intro h
    induction h with
    | must_exit_in_at_cfg_halted c code hh hin hk =>
      exact must_exit_in_at.must_exit_in_at_halted c code hh hin hk
    | must_exit_in_at_cfg_running c hn hp he _ ih =>
      obtain ⟨evs, st, hs⟩ := hp
      refine must_exit_in_at.must_exit_in_at_running c hn
        ⟨evs, st, (sstep_cfg_may_fail _ _ _ _).2 hs⟩ ?_ ?_
      · exact fun evs herr => he evs ((sstep_cfg_may_fail _ _ _ _).1 herr)
      · exact fun evs c' hs' => ih evs c' ((sstep_cfg_may_fail _ _ _ _).1 hs')
  · intro h
    induction h with
    | must_exit_in_at_halted c code hh hin hk =>
      exact must_exit_in_at_cfg.must_exit_in_at_cfg_halted c code hh hin hk
    | must_exit_in_at_running c hn hp he _ ih =>
      obtain ⟨evs, st, hs⟩ := hp
      refine must_exit_in_at_cfg.must_exit_in_at_cfg_running c hn
        ⟨evs, st, (sstep_cfg_may_fail _ _ _ _).1 hs⟩ ?_ ?_
      · exact fun evs herr => he evs ((sstep_cfg_may_fail _ _ _ _).2 herr)
      · exact fun evs c' hs' => ih evs c' ((sstep_cfg_may_fail _ _ _ _).2 hs')

theorem must_exit_in_scfg_may_fail (S : List word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_in_scfg may_fail_cfg S img lim en inp ↔ must_exit_in S img lim en inp :=
  must_exit_in_at_cfg_may_fail _ _ _

/-- The configured singleton is the configured single-code form, the
`_scfg` twin of `must_exit_in_at_singleton`. -/
theorem must_exit_in_at_cfg_singleton (cfg : SpuriousCfg) (segs : List Segment) (code : word) (c : config) :
    must_exit_in_at_cfg cfg segs [code] c ↔ must_exit_at_cfg cfg segs code c := by
  constructor
  · intro h
    induction h with
    | must_exit_in_at_cfg_halted c code0 hh hin hk =>
      rw [List.mem_singleton] at hin
      subst hin
      exact must_exit_at_cfg.must_exit_at_cfg_halted c hh hk
    | must_exit_in_at_cfg_running c hnone hprog hnoerr _ ih =>
      exact must_exit_at_cfg.must_exit_at_cfg_running c hnone hprog hnoerr ih
  · intro h
    induction h with
    | must_exit_at_cfg_halted c hh hk =>
      exact must_exit_in_at_cfg.must_exit_in_at_cfg_halted c code hh (List.mem_singleton.mpr rfl) hk
    | must_exit_at_cfg_running c hn hp he _ ih =>
      exact must_exit_in_at_cfg.must_exit_in_at_cfg_running c hn hp he ih

theorem must_exit_in_scfg_singleton (cfg : SpuriousCfg) (code : word) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_in_scfg cfg [code] img lim en inp ↔ must_exit_with_scfg cfg code img lim en inp :=
  must_exit_in_at_cfg_singleton _ _ _ _

/-- A verdict under a configuration is a verdict under every SMALLER
one wherever the filter's question is answered along the way. Progress is
`Run.sstep_cfg_progress`; the error and successor premises use
`Run.sstep_cfg_mono`, since every smaller step is also a larger step. -/
theorem must_exit_in_at_cfg_mono (cfg1 cfg2 : SpuriousCfg) (segs : List Segment)
    (S : List word) (c : config) :
    cfg_le cfg1 cfg2 → decided_from cfg1 segs c →
    must_exit_in_at_cfg cfg2 segs S c → must_exit_in_at_cfg cfg1 segs S c := by
  intro hle hd h
  induction h with
  | must_exit_in_at_cfg_halted c code hh hin hk =>
    exact must_exit_in_at_cfg.must_exit_in_at_cfg_halted c code hh hin hk
  | must_exit_in_at_cfg_running c hn hp he _ ih =>
    obtain ⟨evs, st, hs⟩ := hp
    refine must_exit_in_at_cfg.must_exit_in_at_cfg_running c hn ?_ ?_ ?_
    · cases c with
      | mkCfg ms model =>
        exact sstep_cfg_progress segs cfg1 ms model evs st
          (fun x8 hv => hd [] _ x8 (star.star_refl _) hv)
          (sstep_cfg_sub _ _ _ _ _ hs)
    · exact fun evs herr => he evs (sstep_cfg_mono _ _ _ _ _ _ hle herr)
    · intro evs c' hs'
      exact ih evs c' (sstep_cfg_mono _ _ _ _ _ _ hle hs')
        (decided_from_step _ _ _ _ _ _ hd hs')

/-- A verdict under may-fail is a verdict under any configuration: the pin
weakens the obligation, with the same `decided_from` premise. -/
theorem must_exit_in_at_cfg_of_must_exit_in_at (cfg : SpuriousCfg) (segs : List Segment)
    (S : List word) (c : config) :
    decided_from cfg segs c → must_exit_in_at segs S c →
    must_exit_in_at_cfg cfg segs S c :=
  fun hd h => must_exit_in_at_cfg_mono _ _ _ _ _ (may_fail_cfg_greatest cfg) hd
    ((must_exit_in_at_cfg_may_fail _ _ _).2 h)

theorem must_exit_in_scfg_mono (cfg1 cfg2 : SpuriousCfg) (S : List word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    cfg_le cfg1 cfg2 → run_decided cfg1 img lim en inp →
    must_exit_in_scfg cfg2 S img lim en inp → must_exit_in_scfg cfg1 S img lim en inp :=
  fun hle hd h => must_exit_in_at_cfg_mono _ _ _ _ _ hle hd h

theorem must_exit_in_scfg_of_must_exit_in (cfg : SpuriousCfg) (S : List word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    run_decided cfg img lim en inp → must_exit_in S img lim en inp →
    must_exit_in_scfg cfg S img lim en inp :=
  fun hd h => must_exit_in_scfg_mono _ _ _ _ _ _ _ (may_fail_cfg_greatest cfg) hd
    ((must_exit_in_scfg_may_fail _ _ _ _ _).2 h)

/-- The configured bridge from the single-code form: a binary that exits
with one code under `cfg` satisfies the set form for every set containing it. -/
theorem must_exit_with_scfg_in (cfg : SpuriousCfg) (S : List word) (code : word)
    (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_scfg cfg code img lim en inp → code ∈ S →
    must_exit_in_scfg cfg S img lim en inp := by
  intro h hin
  exact must_exit_in_scfg_mono_set cfg [code] S img lim en inp
    (fun code0 hin0 => (List.mem_singleton.mp hin0) ▸ hin)
    ((must_exit_in_scfg_singleton _ _ _ _ _ _).2 h)

end LinuxProcessSemantics.EquivalenceDefinition.MustExit
