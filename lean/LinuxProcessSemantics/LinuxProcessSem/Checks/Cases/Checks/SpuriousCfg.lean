import LinuxProcessSemantics.LinuxProcessSem.Checks.SpuriousCfg

/-! # Checks.Cases.Checks.SpuriousCfg — part 6's two witnesses, each with its other half

Pins over `Checks.SpuriousCfg`, the twin of
`theories/LinuxProcessSem/Checks/SpuriousCfg.v`.  Rocq has no Cases file
for it: its parts are checks themselves.  Part 6 states two run-level
witnesses over `MustExit.must_exit_with_scfg` at `Run.forced_only_cfg`:
the exit-0 image is accepted, and the undecodable image is refuted.  This
file restates each witness, so a change to either statement breaks a pin
here, and pins the other half of each: the exit-0 run has no guarantee
of the reject code, and the undecodable run reaches its unmodeled fetch,
which refutes every code.  That last pin holds the refuting witness's
docstring, which says "at every code" while its statement names only
`verdict_accept`.

One more pin holds the lemma behind the exit-0 witness,
`exits_c_must_exit_at_cfg`, at every configuration.  Rocq uses that
lemma at other configurations
(`theories/LinuxProcessSem/Checks/BudgetPremise.v`'s
`exit0_must_exit_at_cfg`), and no witness here does.

Not part of the trusted specification: this file is QA on the
definitions.  No pin here states a kernel answer, so each carries a
`model:` line. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.SpuriousCfg

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.EquivalenceDefinition.Classifier
  (verdict_accept verdict_reject verdict_accept_neq_reject)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude (demo_limit)
open LinuxProcessSemantics.LinuxProcessSem.Checks.SpuriousCfg

/-! ## A-MustExit-scfg: SpuriousCfg part 6, the run-level witnesses -/

/-- ACCEPT: the exit-0 image exits 0 under forced-only.
model: `Checks.SpuriousCfg.exit0_image_must_exit_zero_under_forced_only`, at the statement of Rocq's example. -/
theorem exit0_image_accepted_under_forced_only :
    must_exit_with_scfg forced_only_cfg verdict_accept exit0_image demo_limit demo_entry
      demo_proc_input := by
  exact exit0_image_must_exit_zero_under_forced_only

/-- REFUTE: the same run has no guarantee to exit with the reject code.
model: `must_exit_with_scfg_exclusive` at the accepting witness, with `verdict_accept_neq_reject`. -/
theorem exit0_image_not_rejected_under_forced_only :
    ¬ must_exit_with_scfg forced_only_cfg verdict_reject exit0_image demo_limit demo_entry
        demo_proc_input := by
  intro h
  exact verdict_accept_neq_reject
    (must_exit_with_scfg_exclusive _ _ _ _ _ _ _
      exit0_image_accepted_under_forced_only h)

/-- ACCEPT: the exit-0 image exits 0 under every configuration, the shape of Rocq's
`BudgetPremise.exit0_must_exit_at_cfg`.  The proof applies `exits_c_must_exit_at_cfg` at an
arbitrary configuration, so a narrowing of that lemma to one configuration fails here.
model: `exits_c_must_exit_at_cfg` at any `SpuriousCfg`, with the fuel of the forced-only witness. -/
theorem exit0_image_accepted_under_every_cfg (cfg : SpuriousCfg) :
    must_exit_with_scfg cfg verdict_accept exit0_image demo_limit demo_entry
      demo_proc_input := by
  unfold must_exit_with_scfg init_config
  apply exits_c_must_exit_at_cfg _ _ _ 8
  · rfl
  · rfl
  · decide +kernel

/-- ACCEPT: the undecodable image's forced-only run reaches the unmodeled fetch at its entry.
model: `Run.reaches_unmodeled_cfg` in zero steps: the initial configuration's next instruction step answers `MachineUnmodeled`. -/
theorem undecodable_image_unmodeled_under_forced_only :
    (run_scfg forced_only_cfg undecodable_image demo_limit fixture_entry
      demo_proc_input).bh_unmodeled := by
  refine ⟨[], _, star_cfg.star_cfg_refl _, ?_⟩
  refine ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
  rw [mi_account_step_no_lazy _ _ _ rfl]
  simp only [undecodable_image, init_config, fixture_entry, demo_proc_input,
    LinuxProcessSemantics.LinuxProcessSem.State.ProcInput.mkProcInput,
    undecodable_step_unmodeled]

/-- REFUTE: the undecodable image is not accepted under forced-only.
model: `Checks.SpuriousCfg.undecodable_image_refutes_must_exit_under_forced_only`, at the statement of Rocq's example. -/
theorem undecodable_image_not_accepted_under_forced_only :
    ¬ must_exit_with_scfg forced_only_cfg verdict_accept undecodable_image demo_limit
        fixture_entry demo_proc_input := by
  exact undecodable_image_refutes_must_exit_under_forced_only

/-- REFUTE: the unmodeled fetch refutes every code, the reject code included.
model: `must_exit_with_scfg_refuted_by_error` through `run_scfg_unmodeled_errors`. -/
theorem undecodable_image_refutes_every_code_under_forced_only (code : word) :
    ¬ must_exit_with_scfg forced_only_cfg code undecodable_image demo_limit fixture_entry
        demo_proc_input := by
  exact must_exit_with_scfg_refuted_by_error _ _ _ _ _ _
    (run_scfg_unmodeled_errors _ _ _ _ _
      undecodable_image_unmodeled_under_forced_only)

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.SpuriousCfg
