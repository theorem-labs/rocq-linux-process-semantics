import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.LinuxProcessSem.Checks.Examples

/-! Regression checks for the pilot's proof contracts.

These cases exercise properties of the execution judgments which no syscall
probe can establish: infinite execution versus termination, the all-error
escape versus coverage, and exact trace equality versus matching one result.
The looping and exiting fixtures use decoded instructions. They are not
axiomatized transition systems or substitutes for the pilot's actual images.
-/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.OmniPilot

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples

/-- `jal zero, 0`: the target is this instruction and no register changes. -/
def loop_segments : List Segment :=
  [{ seg_base := 0x100, seg_size := 4, seg_perms := "r-x", seg_bytes := ["6f000000"] }]

def loop_config : config :=
  init_config loop_segments 0x100 demo_phdrs demo_entry.en_sp demo_entry.en_brk
    demo_entry.en_mmap_base demo_entry.en_draw demo_limit demo_proc_input

theorem loop_instruction_returns_to_itself :
    step loop_segments loop_config.cfg_ms = MachineOk loop_config.cfg_ms := by rfl

theorem loop_takes_silent_step : sstep loop_segments loop_config [] (SNext loop_config) := by
  apply sstep.sstep_instr _ _ _ _ rfl rfl
  rw [mi_account_step_no_lazy _ _ _ rfl]
  rfl

theorem loop_steps_only_to_itself (evs : List event) (st : step_to)
    (hs : sstep loop_segments loop_config evs st) : evs = [] ∧ st = SNext loop_config :=
  sstep_instr_inv _ _ _ _ _ _ rfl rfl loop_instruction_returns_to_itself hs

/-- Coinduction must represent an actual infinite execution. A postcondition
on finite endings is vacuous here because this program has no finite ending. -/
theorem loop_coexec_false : coexec loop_segments loop_config (fun _ _ => False) := by
  apply coexec.coinduct loop_segments (fun c _ => c = loop_config)
  · intro c Q hc
    subst c
    refine Or.inr ⟨rfl, ?_, ?_⟩
    · intro evs hs
      have h := (loop_steps_only_to_itself _ _ hs).2
      cases h
    · intro evs c' hs
      have h := (loop_steps_only_to_itself _ _ hs).2
      exact step_to.SNext.inj h
  · rfl

/-- The terminating judgment must reject the same program even when the
postcondition places no constraint at all on the answer. -/
theorem loop_has_no_total_execution (Q : post) : ¬ exec loop_segments loop_config Q := by
  suffices ∀ c Q, exec loop_segments c Q → c ≠ loop_config by
    intro h
    exact this _ _ h rfl
  intro c Q hex
  induction hex with
  | exec_halt c Q hh _ =>
    intro hc
    subst c
    exact hh rfl
  | exec_step c Q _ _ _ _ ih =>
    intro hc
    subst c
    exact ih [] loop_config loop_takes_silent_step rfl

theorem loop_has_no_finite_ending (tr : List event) (o : outcome) :
    ¬ mexec loop_segments loop_config tr o :=
  fun hm => coexec_sound _ _ _ _ hm _ loop_coexec_false

theorem exit0_symbolic_derivation :
    to_exit exit0_segments (Z_to_bv 64 0)
      (init_machine_state exit0_segments 0x100 demo_phdrs demo_entry.en_sp demo_entry.en_draw
        demo_proc_input.in_argv demo_proc_input.in_envp demo_proc_input.in_uid demo_proc_input.in_hwcap) := by
  apply to_exit.te_step _ _ rfl rfl
  apply to_exit.te_step _ _ rfl rfl
  apply to_exit.te_step _ _ rfl rfl
  exact to_exit.te_here _ (Z_to_bv 64 93) (by decide +kernel)
    (Or.inl rfl) (by decide +kernel)

theorem exit0_has_exact_total_trace :
    omni_run exit0_image demo_limit demo_entry demo_proc_input
      (exit_post (Z_to_bv 64 0) demo_proc_input.in_fs) :=
  exit_omni_run_te _ _ _ _ _ _ _ _ _ _ exit0_symbolic_derivation

theorem exit0_rejects_exit1_post :
    ¬ omni_run exit0_image demo_limit demo_entry demo_proc_input
      (exit_post (Z_to_bv 64 1) demo_proc_input.in_fs) := by
  intro h
  have h1 : must_exit_with (Z_to_bv 64 1) exit0_image demo_limit demo_entry demo_proc_input := by
    apply (must_exit_with_iff _ _ _ _ _).2
    apply exec_conseq _ _ _ _ h
    intro tr o hp
    exact hp.2
  have heq := must_exit_with_exclusive _ _ _ _ _ _ exit0_image_must_exit_zero h1
  exact (by decide : (Z_to_bv 64 0) ≠ Z_to_bv 64 1) heq

theorem exit0_admits_its_full_trace :
    (run exit0_image demo_limit demo_entry demo_proc_input).bh_traces
      [ExitEv (Z_to_bv 64 0) demo_proc_input.in_fs] :=
  (exit_obs_iff_te _ _ _ _ _ exit0_has_exact_total_trace _).2 (is_prefix_refl _)

theorem exit0_rejects_repeated_exit :
    ¬ (run exit0_image demo_limit demo_entry demo_proc_input).bh_traces
      [ExitEv (Z_to_bv 64 0) demo_proc_input.in_fs,
       ExitEv (Z_to_bv 64 0) demo_proc_input.in_fs] := by
  intro h
  exact ((exit_obs_iff_te _ _ _ _ _ exit0_has_exact_total_trace _).1 h).2

def nonempty_fs_input : ProcInput :=
  { demo_proc_input with in_image_fs := [([0x66], [0x41, 0x42])] }

theorem exit0_preserves_nonempty_filesystem :
    omni_run exit0_image demo_limit demo_entry nonempty_fs_input
      (exit_post (Z_to_bv 64 0) nonempty_fs_input.in_fs) :=
  exit_omni_run_te _ _ _ _ _ _ _ _ _ _ exit0_symbolic_derivation

theorem exit0_nonempty_filesystem_trace_accepted :
    (run exit0_image demo_limit demo_entry nonempty_fs_input).bh_traces
      [ExitEv (Z_to_bv 64 0) [([0x66], [0x41, 0x42])]] :=
  (exit_obs_iff_te _ _ _ _ _ exit0_preserves_nonempty_filesystem _).2 (is_prefix_refl _)

theorem exit0_changed_filesystem_trace_rejected :
    ¬ (run exit0_image demo_limit demo_entry nonempty_fs_input).bh_traces
      [ExitEv (Z_to_bv 64 0) []] := by
  intro h
  have hp := (exit_obs_iff_te _ _ _ _ _ exit0_preserves_nonempty_filesystem _).1 h
  have hfs := (event.ExitEv.inj hp.1).2
  cases hfs

/-- A real unsupported image must fail the coverage conjunct even though its
all-error branch permits bare equivalence. -/
theorem undecodable_refutes_strong_equivalence (target : Image) (et : ExecEntry) :
    ¬ strong_equiv undecodable_image target fixture_entry et demo_proc_input := by
  apply unmodeled_source_refutes_strong_equiv
  apply reaches_unmodeled_intro
  · rfl
  · rfl
  · rw [mi_account_step_no_lazy _ _ _ rfl]
    simp only [undecodable_image, fixture_entry, demo_proc_input, ProcInput.mkProcInput,
      undecodable_step_unmodeled]

theorem undecodable_all_executions_error :
    (run undecodable_image source_alloc_limit fixture_entry demo_proc_input).bh_all_errors := by
  have hacc : mi_account_step undecodable_segments
      (init_machine_state undecodable_segments 0x100 demo_phdrs fixture_entry.en_sp fixture_entry.en_draw
        demo_proc_input.in_argv demo_proc_input.in_envp demo_proc_input.in_uid demo_proc_input.in_hwcap)
      (init_model (segments_reserved undecodable_segments) fixture_entry.en_brk
        fixture_entry.en_mmap_base fixture_entry.en_sp source_alloc_limit demo_proc_input) =
      MachineUnmodeled := by
    rw [mi_account_step_no_lazy _ _ _ rfl]
    simp only [fixture_entry, demo_proc_input, ProcInput.mkProcInput, undecodable_step_unmodeled]
  apply all_traces_error.all_traces_error_intro
  · exact ⟨[], SError, sstep.sstep_instr_unmodeled _ _ rfl rfl hacc⟩
  · intro evs c' hs
    cases hs with
    | sstep_instr _ _ _ _ _ _ hi =>
      simp only [undecodable_image] at hi
      rw [hacc] at hi
      cases hi
    | sstep_syscall _ _ _ _ _ _ _ _ hv _ _ _ => cases hv
    | sstep_exit _ _ _ _ _ _ _ _ hv _ _ _ => cases hv
    | sstep_killed _ _ _ _ _ _ _ _ hv _ _ => cases hv

theorem undecodable_still_satisfies_bare_equivalence (target : behavior) :
    equiv (run undecodable_image source_alloc_limit fixture_entry demo_proc_input) target :=
  all_source_traces_error_equiv_any _ _ undecodable_all_executions_error

theorem terminating_behavior_reflexive :
    equiv (terminating_behavior (Z_to_bv 64 5) []) (terminating_behavior (Z_to_bv 64 5) []) :=
  same_exit_equiv _ _

theorem wrong_exit_behavior_rejected :
    ¬ equiv (terminating_behavior (Z_to_bv 64 5) []) (terminating_behavior (Z_to_bv 64 6) []) :=
  different_exit_code _ _ _ (by decide)

theorem silent_divergence_rejected :
    ¬ equiv (terminating_behavior (Z_to_bv 64 5) []) silent_behavior :=
  exit_vs_divergence _ _

theorem executable_entry_is_fetchable : image_entry_fetchable exit0_segments 0x100 = true := by
  decide

theorem missing_entry_is_rejected : image_entry_fetchable exit0_segments 0x200 = false := by
  decide

theorem empty_image_is_rejected : image_entry_fetchable [] 0x100 = false := by decide

theorem readable_phdr_bytes_accepted :
    image_phdrs_readable exit0_segments (PhdrInfo.mkPhdrInfo 0x100 4 3) = true := by decide

theorem missing_phdr_bytes_rejected :
    image_phdrs_readable exit0_segments (PhdrInfo.mkPhdrInfo 0x100 4 4) = false := by decide

theorem zero_phdr_count_rejected :
    image_phdrs_readable exit0_segments (PhdrInfo.mkPhdrInfo 0x100 4 0) = false := by decide

theorem zero_phdr_size_rejected :
    image_phdrs_readable exit0_segments (PhdrInfo.mkPhdrInfo 0x100 0 3) = false := by decide

theorem ordinary_break_fits : image_brk_satisfiable exit0_segments = true := by decide

theorem overflowing_break_rejected :
    image_brk_satisfiable
      [{ seg_base := 2 ^ 64 - 4096, seg_size := 4096,
         seg_perms := "r-x", seg_bytes := [] }] = false := by decide

/-! Carrying the task declaration in the input once came with two pins here
saying the abort syscall path was NOT ported: tkill (130) and tgkill (131)
declined for every model.  Both arms are ported now (`Sys/Kernel/Signal.lean`),
so those statements are false, and the fact that still closes the window the
pilot relies on -- `valid_input` pins the INPUT's declaration `false`, the
first model reads its `m_abort_terminal` off that input, `Run.decl_off_frame`
keeps the bit clear along a run, and with it clear both arms decline for
every argument shape and never report an `Ok` -- lives beside the specs as
`Sys.Kernel.Signal.tkill_spec_off_unmodeled` and
`Sys.Kernel.Signal.tgkill_spec_off_unmodeled`, with the worked cases in
`Checks/Cases/Kernel/Signal.lean` (`tkill_off_declined`, `tgkill_off_declined`,
`tkill_off_lies_rejected`, `sysno_130_off_declined`, `sysno_131_off_declined`).
What the pilot's compatibility claim rests on is `Run.decl_off_frame`, the
named hypothesis `Run.star_off_no_kill` takes, not a decline of the two
numbers. -/

end LinuxProcessSemantics.LinuxProcessSem.Checks.OmniPilot
