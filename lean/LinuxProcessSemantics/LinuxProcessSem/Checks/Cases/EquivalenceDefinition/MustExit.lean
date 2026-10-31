import LinuxProcessSemantics.EquivalenceDefinition.MustExit
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Run
import LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.PosixTimers

/-! # Checks.Cases.EquivalenceDefinition.MustExit — configured termination

Not part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.MustExit

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Run
  (svc_ms vast_budget_model refusal_decided_classical brk_old_break_is_spurious_within_budget)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.EquivalenceDefinition.Classifier
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mmap
  (brk_reserved m_tight_brk brk_grow_within_budget_grants)
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Mm.Mmap (brk_arm)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Hrtimer (nanosleep_clock nanosleep_rem_ok_b)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.PosixTimers (ts_1s)

/-! ## A-MustExit-scfg: the configured termination judgments -/

/-- Allowing every refusal recovers the unconfigured single-code judgment.
model: an instance of `MustExit.must_exit_with_scfg_may_fail`, the Lean twin of the Rocq lemma of that name. -/
theorem single_code_may_fail_iff (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_scfg may_fail_cfg code img lim en inp ↔ must_exit_with code img lim en inp :=
  must_exit_with_scfg_may_fail _ _ _ _ _

/-- Allowing every refusal recovers the unconfigured allowed-set judgment.
model: an instance of `MustExit.must_exit_in_scfg_may_fail`, the Lean twin of the Rocq lemma of that name. -/
theorem allowed_set_may_fail_iff (S : List word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_in_scfg may_fail_cfg S img lim en inp ↔ must_exit_in S img lim en inp :=
  must_exit_in_scfg_may_fail _ _ _ _ _

/-- The enabled allocation switch selects the original single-code judgment.
model: an instance of `MustExit.must_exit_with_cfg_true`, the Lean twin of the Rocq lemma of that name. -/
theorem allocation_true_iff (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_cfg true code img lim en inp ↔ must_exit_with code img lim en inp := by
  rw [must_exit_with_cfg_true]

/-- The disabled allocation switch selects exactly the allocation-only filter.
model: an instance of `MustExit.must_exit_with_cfg_false`, the Lean twin of the Rocq lemma of that name. -/
theorem allocation_false_iff (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_cfg false code img lim en inp ↔
      must_exit_with_scfg (alloc_only_cfg false) code img lim en inp := by
  rw [must_exit_with_cfg_false]

/-- Allowing every refusal preserves reachability of a killed configuration.
model: `Run.star_cfg_may_fail` relates the filtered and unfiltered reachability judgments. -/
theorem killed_may_fail_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    run_reaches_killed_cfg may_fail_cfg img lim en inp ↔
      LinuxProcessSemantics.EquivalenceDefinition.MustExit.run_reaches_killed img lim en inp := by
  constructor
  · rintro ⟨tr, c, sig, hs, hk⟩
    exact ⟨tr, c, sig, (star_cfg_may_fail _ _ _ _).2 hs, hk⟩
  · rintro ⟨tr, c, sig, hs, hk⟩
    exact ⟨tr, c, sig, (star_cfg_may_fail _ _ _ _).1 hs, hk⟩

/-- An exited configuration, built with the existing Run fixtures.
model: `State.with_halted` stores code 6 and clears the kill flag. -/
def exited6 : config :=
  config.mkCfg (svc_ms 0 0 0 0 0 0 0) (with_halted (Z_to_bv 64 6) vast_budget_model)

/-- A killed configuration with the same numeric halt status as `exited6`.
model: `State.with_killed` stores 6 in the halt status and sets the Boolean kill flag. -/
def killed6 : config :=
  config.mkCfg (svc_ms 0 0 0 0 0 0 0) (with_killed (Z_to_bv 64 6) vast_budget_model)

/-- ACCEPT: an exited configuration satisfies the forced-only judgment at its code.
model: `must_exit_at_cfg_halted` reads `with_halted`'s status and clear kill flag. -/
theorem single_code_accepts_exit6 :
    must_exit_at_cfg forced_only_cfg [] (Z_to_bv 64 6) exited6 :=
  must_exit_at_cfg.must_exit_at_cfg_halted _ rfl rfl

/-- REFUTE: death with signal number 6 cannot count as an exit with code 6.
model: both constructors of `must_exit_at_cfg` exclude `State.with_killed 6`. -/
theorem single_code_refuses_killed6 :
    ¬ must_exit_at_cfg forced_only_cfg [] (Z_to_bv 64 6) killed6 := by
  intro h
  cases h with
  | must_exit_at_cfg_halted _ _ hk =>
    exact nomatch (hk : (some (Z_to_bv 64 6) : Option word) = none)
  | must_exit_at_cfg_running _ hn _ _ _ =>
    exact nomatch (hn : (some (Z_to_bv 64 6) : Option word) = none)

/-- REFUTE: an exit at 6 cannot satisfy the judgment at 0.
model: an instance of `MustExit.must_exit_at_cfg_wrong_code`, the Lean twin of the Rocq lemma of that name. -/
theorem single_code_refuses_wrong_code :
    ¬ must_exit_at_cfg forced_only_cfg [] (Z_to_bv 64 0) exited6 :=
  must_exit_at_cfg_wrong_code _ _ _ _ _ rfl (by decide)

/-- ACCEPT: code 6 belongs to the explicitly allowed set [0, 6].
model: `must_exit_in_at_cfg_halted` checks membership and the clear kill flag. -/
theorem allowed_set_accepts_exit6 :
    must_exit_in_at_cfg forced_only_cfg [] [Z_to_bv 64 0, Z_to_bv 64 6] exited6 :=
  must_exit_in_at_cfg.must_exit_in_at_cfg_halted _ (Z_to_bv 64 6) rfl (by decide) rfl

/-- REFUTE: the set [0] does not contain an exit's code 6.
model: an instance of `MustExit.must_exit_in_at_cfg_wrong_code`, the Lean twin of the Rocq lemma of that name. -/
theorem allowed_set_refuses_wrong_code :
    ¬ must_exit_in_at_cfg forced_only_cfg [] [Z_to_bv 64 0] exited6 :=
  must_exit_in_at_cfg_wrong_code _ _ _ _ _ rfl (by decide)

/-- REFUTE: even a set containing 6 cannot turn signal death into an exit.
model: an instance of `MustExit.must_exit_in_at_cfg_refuted_by_kill`, the Lean twin of the Rocq lemma of that name. -/
theorem allowed_set_refuses_killed6 :
    ¬ must_exit_in_at_cfg forced_only_cfg [] [Z_to_bv 64 0, Z_to_bv 64 6] killed6 :=
  must_exit_in_at_cfg_refuted_by_kill _ _ _ _ (Z_to_bv 64 6) rfl

/-- ACCEPT everywhere: no refute case exists because this predicate is total classically.
model: `decided_from` asks only `Run.refusal_decided`, proved by `refusal_decided_classical`. -/
theorem decided_from_is_total (cfg : SpuriousCfg) (segs : List Segment) (c : config) :
    decided_from cfg segs c :=
  fun _ _ _ _ _ => refusal_decided_classical _ _ _

/-- ACCEPT for every run: no refute case exists because this predicate is total classically.
model: `run_decided` is `decided_from` at the run's initial configuration. -/
theorem run_decided_is_total (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) : run_decided cfg img lim en inp :=
  decided_from_is_total _ _ _

/-- ACCEPT over an arbitrary image: an unfiltered exit-0 guarantee also holds forced-only.
model: an instance of `MustExit.must_exit_with_scfg_of_must_exit_with`, the Lean twin of the Rocq lemma of that name. -/
theorem configured_run_accepts_exit0 (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with (Z_to_bv 64 0) img lim en inp →
    must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) img lim en inp :=
  must_exit_with_scfg_of_must_exit_with _ _ _ _ _ _ (run_decided_is_total _ _ _ _ _)

/-- REFUTE over an arbitrary image: a forced-only exit-0 guarantee excludes exit 1.
model: an instance of `MustExit.must_exit_with_scfg_exclusive`, the Lean twin of the Rocq lemma of that name. -/
theorem configured_run_refuses_exit1 (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) img lim en inp →
    ¬ must_exit_with_scfg forced_only_cfg (Z_to_bv 64 1) img lim en inp := by
  intro h0 h1
  exact absurd (must_exit_with_scfg_exclusive _ _ _ _ _ _ _ h0 h1) (by decide)

/-- ACCEPT over an arbitrary image: an exit-0 guarantee survives disabling allocation refusals.
model: an instance of `MustExit.must_exit_with_scfg_of_must_exit_with`, the Lean twin of the Rocq lemma of that name. -/
theorem allocation_switch_accepts_exit0 (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with (Z_to_bv 64 0) img lim en inp →
    must_exit_with_cfg false (Z_to_bv 64 0) img lim en inp :=
  must_exit_with_scfg_of_must_exit_with _ _ _ _ _ _ (run_decided_is_total _ _ _ _ _)

/-- REFUTE over an arbitrary image: disabling allocation refusals cannot give two certain codes.
model: an instance of `MustExit.must_exit_with_scfg_exclusive`, the Lean twin of the Rocq lemma of that name. -/
theorem allocation_switch_refuses_exit1 (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_cfg false (Z_to_bv 64 0) img lim en inp →
    ¬ must_exit_with_cfg false (Z_to_bv 64 1) img lim en inp := by
  intro h0 h1
  exact absurd (must_exit_with_scfg_exclusive _ _ _ _ _ _ _ h0 h1) (by decide)

/-- ACCEPT over an arbitrary image: a forced-only exit-0 guarantee satisfies [0, 1].
model: an instance of `MustExit.must_exit_with_scfg_in`, the Lean twin of the Rocq lemma of that name. -/
theorem configured_set_accepts_exit0 (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_scfg forced_only_cfg (Z_to_bv 64 0) img lim en inp →
    must_exit_in_scfg forced_only_cfg [Z_to_bv 64 0, Z_to_bv 64 1] img lim en inp :=
  fun h => must_exit_with_scfg_in _ _ _ _ _ _ _ h (by decide)

/-- REFUTE over an arbitrary image: a reachable signal death excludes even the set [0, 6].
model: an instance of `MustExit.must_exit_in_scfg_refuted_by_kill`, the Lean twin of the Rocq lemma of that name. -/
theorem configured_set_refuses_reachable_kill (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    run_reaches_killed_cfg forced_only_cfg img lim en inp →
    ¬ must_exit_in_scfg forced_only_cfg [Z_to_bv 64 0, Z_to_bv 64 6] img lim en inp :=
  must_exit_in_scfg_refuted_by_kill _ _ _ _ _ _

/-- ACCEPT over an arbitrary image: reaching a configuration killed with signal 6 witnesses signal death.
model: `run_reaches_killed_cfg` requires a configured star and the target's kill flag. -/
theorem killed_run_accepts_reached_kill6 (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) (tr : List event) (c : config) :
    star_cfg img.img_segments forced_only_cfg
      (init_config img.img_segments img.img_init_pc img.img_phdrs
        en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp) tr c →
    m_killed c.cfg_model = some (Z_to_bv 64 6) →
    run_reaches_killed_cfg forced_only_cfg img lim en inp :=
  fun hs hk => ⟨tr, c, Z_to_bv 64 6, hs, hk⟩

/-- REFUTE over an arbitrary image: a guarantee to exit in [0, 6] rules out reachable signal death.
model: an instance of `MustExit.must_exit_in_scfg_refuted_by_kill`, the Lean twin of the Rocq lemma of that name. -/
theorem killed_run_refused_by_allowed_exits (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_in_scfg forced_only_cfg [Z_to_bv 64 0, Z_to_bv 64 6] img lim en inp →
    ¬ run_reaches_killed_cfg forced_only_cfg img lim en inp :=
  fun h hk => must_exit_in_scfg_refuted_by_kill _ _ _ _ _ _ hk h

/-- REFUTE: the stored exit code is compared in full, so 262 differs from 6 despite its low byte.
model: `MustExit.must_exit_at_cfg_wrong_code` compares the stored word directly. -/
theorem single_code_refuses_262 :
    ¬ must_exit_at_cfg forced_only_cfg [] (Z_to_bv 64 262) exited6 :=
  must_exit_at_cfg_wrong_code _ _ _ _ _ rfl (by decide)

/-- REFUTE: the allowed set contains full words, so [262] does not contain the stored code 6.
model: `MustExit.must_exit_in_at_cfg_wrong_code` checks membership without masking. -/
theorem allowed_set_refuses_262 :
    ¬ must_exit_in_at_cfg forced_only_cfg [] [Z_to_bv 64 262] exited6 :=
  must_exit_in_at_cfg_wrong_code _ _ _ _ _ rfl (by decide)

/-- ACCEPT: the concrete exit-0 image's unfiltered guarantee survives the forced-only filter.
model: `exit0_image_must_exit_zero` and `must_exit_with_scfg_of_must_exit_with`, with classical `run_decided`. -/
theorem exit0_image_forced_only_exits_zero :
    must_exit_with_scfg forced_only_cfg verdict_accept exit0_image demo_limit demo_entry demo_proc_input :=
  must_exit_with_scfg_of_must_exit_with _ _ _ _ _ _ (run_decided_is_total _ _ _ _ _)
    exit0_image_must_exit_zero

/-- ACCEPT: the concrete exit-0 image also exits zero with allocation refusals disabled.
model: `must_exit_with_cfg` at false and `must_exit_with_scfg_of_must_exit_with` preserve `exit0_image_must_exit_zero`. -/
theorem exit0_image_alloc_off_exits_zero :
    must_exit_with_cfg false verdict_accept exit0_image demo_limit demo_entry demo_proc_input :=
  must_exit_with_scfg_of_must_exit_with _ _ _ _ _ _ (run_decided_is_total _ _ _ _ _)
    exit0_image_must_exit_zero

/-- ACCEPT: the concrete image's forced-only exit code belongs to [0, 1].
model: `must_exit_with_scfg_in` lifts `exit0_image_forced_only_exits_zero` to the allowed set. -/
theorem exit0_image_forced_only_in_zero_one :
    must_exit_in_scfg forced_only_cfg [verdict_accept, verdict_reject]
      exit0_image demo_limit demo_entry demo_proc_input :=
  must_exit_with_scfg_in _ _ _ _ _ _ _ exit0_image_forced_only_exits_zero (by decide)

/-- REFUTE: the concrete image's forced-only exit-0 guarantee excludes an exit-1 guarantee.
model: `must_exit_with_scfg_exclusive` and `verdict_accept_neq_reject` separate the two verdicts. -/
theorem exit0_image_forced_only_refutes_exit_one :
    ¬ must_exit_with_scfg forced_only_cfg verdict_reject exit0_image demo_limit demo_entry demo_proc_input :=
  fun h => verdict_accept_neq_reject
    (must_exit_with_scfg_exclusive _ _ _ _ _ _ _ exit0_image_forced_only_exits_zero h)

/-! ### The filter, at a running configuration -/

/-- Code at 0x100: ecall (0x00000073), srli a0,a0,12 (0x00c55513),
addi a7,x0,93 (0x05d00893), ecall (0x00000073); the return becomes exit 17 or 16.
model: `RiscvSemantics.step` fetches these little-endian bytes from the executable segment. -/
def brk_probe_segs : List Segment :=
  [{ seg_base := 0x100, seg_size := 16, seg_perms := "r-x",
     seg_bytes := ["730000001355c5009308d00573000000"] }]

/-- The pending brk ecall has a0=69632, a7=214, and the reused one-page budget model.
model: `Run.sys_input` reads the registers; `m_tight_brk` starts with break 65536 and budget 4096. -/
def brk_probe : config :=
  config.mkCfg { svc_ms 214 69632 0 0 0 0 0 with
    ms_regs := bvmap_set (Z_to_bv 5 17) (Z_to_bv 64 214) (svc_ms 214 69632 0 0 0 0 0).ms_regs } m_tight_brk

/-- The grant effect zero-fills the new page and advances the reused fixture's break.
model: these are the grant effect and post-model in `brk_grow_within_budget_grants`. -/
private def brk_grant : SyscallEffect := mkEffect 69632 [] [(65536, 4096)]
private def brk_granted : Model :=
  fixture (VmMaps.mkVmMapsFull brk_reserved [(65536, 4096)] [] 65536 69632 4096 0 demo_sp)

/-- The syscall input reads the requested break from a0 of the running probe.
model: `sys_input`, `syscall_args`, and `ms_gpr` project register x10. -/
private theorem brk_probe_arg :
    in_arg (sys_input brk_probe_segs brk_probe.cfg_ms 214) 0 = 69632 := by
  simp +decide only [in_arg, sys_input, syscall_args, ms_gpr, brk_probe,
    svc_ms, LinuxProcessSemantics.Riscv.Sem.reg_get, bvmap_get_set, ↓reduceIte]

/-- The running probe removes the same old-break refusal as the existing within-budget pin.
model: `spurious_refusal_cfg` uses the computed refusal flags and the grant in `brk_grow_within_budget_grants`. -/
private theorem brk_probe_old_spurious :
    spurious_refusal_cfg forced_only_cfg (sys_input brk_probe_segs brk_probe.cfg_ms 214)
      m_tight_brk (mkEffect 65536 [] []) :=
  ⟨brk_old_break_is_spurious_within_budget.1, by decide +kernel,
    brk_grant, brk_granted, [], by
      rw [syscall_spec, dispatch_arm spec_table _ _ _ brk_arm rfl]
      dsimp only [brk_arm]
      rw [brk_probe_arg]
      exact (brk_grow_within_budget_grants _ _).2 (Or.inl rfl), by decide +kernel⟩

/-- The returned word is shifted by twelve and passed to exit by the actual instruction tail.
model: `exits_c_must_exit_at` checks the instruction execution and all exit successors. -/
private theorem brk_probe_tail_grant :
    must_exit_at brk_probe_segs (Z_to_bv 64 17)
      (config.mkCfg (advance_past_svc (apply_effect brk_probe.cfg_ms brk_grant)) brk_granted) := by
  apply exits_c_must_exit_at _ _ 4
  · rfl
  · rfl
  · decide +kernel

/-- The old-break path executes the same instructions and exits at sixteen.
model: `exits_c_must_exit_at` computes the tail with return word 65536. -/
private theorem brk_probe_tail_old :
    must_exit_at brk_probe_segs (Z_to_bv 64 16)
      (config.mkCfg (advance_past_svc (apply_effect brk_probe.cfg_ms (mkEffect 65536 [] []))) m_tight_brk) := by
  apply exits_c_must_exit_at _ _ 4
  · rfl
  · rfl
  · decide +kernel

/-- The grant is a retained step because returning the requested break is not a refusal.
model: `sstep_cfg_syscall` uses `brk_grow_within_budget_grants` and materializes no lazy pages. -/
private theorem brk_probe_grant_step :
    sstep_cfg brk_probe_segs forced_only_cfg brk_probe []
      (SNext (config.mkCfg (advance_past_svc (apply_effect brk_probe.cfg_ms brk_grant)) brk_granted)) := by
  refine sstep_cfg.sstep_cfg_syscall brk_probe.cfg_ms m_tight_brk 214 brk_grant brk_granted _ [] rfl rfl
    ?_ ?_ rfl (materialize_model_accesses_no_lazy _ _ rfl)
  · rw [syscall_spec, dispatch_arm spec_table _ _ _ brk_arm rfl]
    dsimp only [brk_arm]
    rw [brk_probe_arg]
    exact (brk_grow_within_budget_grants _ _).2 (Or.inl rfl)
  · intro h
    exact Bool.noConfusion ((by decide +kernel :
      refusal_b (sys_input brk_probe_segs brk_probe.cfg_ms 214) m_tight_brk brk_grant.eff_ret = false).symm.trans h.2.1)

/-- All filtered steps at the pending brk return the grant; no error or old-break step remains.
model: `brk_grow_within_budget_grants` rules out other outcomes and `brk_probe_old_spurious` removes the refusal. -/
private theorem brk_probe_forced_step (evs : List event) (st : step_to)
    (hs : sstep_cfg brk_probe_segs forced_only_cfg brk_probe evs st) :
    st = SNext (config.mkCfg (advance_past_svc (apply_effect brk_probe.cfg_ms brk_grant)) brk_granted) := by
  have outcomes (o : outcome SyscallEffect) :
      syscall_spec (sys_input brk_probe_segs brk_probe.cfg_ms 214) m_tight_brk o ↔
        o = Ok brk_grant brk_granted [] ∨ o = Ok (mkEffect 65536 [] []) m_tight_brk [] := by
    rw [syscall_spec, dispatch_arm spec_table _ _ o brk_arm rfl]
    change Sys.Mm.Mmap.brk_spec _ _ _ _ ↔ _
    rw [brk_probe_arg]
    exact brk_grow_within_budget_grants _ o
  cases hs with
  | sstep_cfg_instr _ _ _ _ _ hv _ => cases hv
  | sstep_cfg_instr_fault _ _ _ hv _ => cases hv
  | sstep_cfg_instr_unmodeled _ _ _ hv _ => cases hv
  | sstep_cfg_syscall _ _ x8 eff model' model'' evs _ hv ho hf hh hm =>
    have hx : (214 : word) = x8 := Option.some.inj hv
    subst x8
    rcases (outcomes _).1 ho with hg | hr
    · cases hg
      rw [materialize_model_accesses_no_lazy _ _ rfl] at hm
      cases hm
      rfl
    · cases hr
      exact False.elim (hf brk_probe_old_spurious)
  | sstep_cfg_syscall_materialization_fault _ _ x8 eff model' evs _ hv ho hf hh hm =>
    have hx : (214 : word) = x8 := Option.some.inj hv
    subst x8
    rcases (outcomes _).1 ho with hg | hr
    · cases hg
      rw [materialize_model_accesses_no_lazy _ _ rfl] at hm
      cases hm
    · cases hr
      exact False.elim (hf brk_probe_old_spurious)
  | sstep_cfg_exit _ _ x8 eff model' evs code _ hv ho hh hk =>
    have hx : (214 : word) = x8 := Option.some.inj hv
    subst x8
    rcases (outcomes _).1 ho with hg | hr
    · cases hg; cases hh
    · cases hr; cases hh
  | sstep_cfg_killed _ _ x8 eff model' evs sig _ hv ho hk =>
    have hx : (214 : word) = x8 := Option.some.inj hv
    subst x8
    rcases (outcomes _).1 ho with hg | hr
    · cases hg; cases hk
    · cases hr; cases hk
  | sstep_cfg_syscall_unmodeled _ _ x8 _ hv ho =>
    have hx : (214 : word) = x8 := Option.some.inj hv
    subst x8
    rcases (outcomes _).1 ho with hg | hr
    · cases hg
    · cases hr

/-- ACCEPT: removing the within-budget old-break refusal leaves only the computed exit at 17.
model: `must_exit_at_cfg_running` quantifies over `brk_probe_forced_step` and the tail exits at 17. -/
theorem forced_only_filters_the_old_break :
    must_exit_at_cfg forced_only_cfg brk_probe_segs (Z_to_bv 64 17) brk_probe := by
  apply must_exit_at_cfg.must_exit_at_cfg_running _ rfl
    ⟨[], _, brk_probe_grant_step⟩
  · intro evs hs
    cases brk_probe_forced_step evs SError hs
  · intro evs c' hs
    have hc := brk_probe_forced_step evs (SNext c') hs
    cases hc
    exact must_exit_at_cfg_of_must_exit_at _ _ _ _ (decided_from_is_total _ _ _) brk_probe_tail_grant

/-- May-fail keeps the explicit old-break successor, whose instruction tail exits at 16.
model: `sstep_cfg_may_fail` retains the refusal outcome of `brk_grow_within_budget_grants`. -/
private theorem brk_probe_old_step :
    sstep_cfg brk_probe_segs may_fail_cfg brk_probe []
      (SNext (config.mkCfg (advance_past_svc (apply_effect brk_probe.cfg_ms (mkEffect 65536 [] []))) m_tight_brk)) := by
  apply (sstep_cfg_may_fail _ _ _ _).1
  refine sstep.sstep_syscall brk_probe.cfg_ms m_tight_brk 214 _ m_tight_brk _ [] rfl rfl ?_ rfl
    (materialize_model_accesses_no_lazy _ _ rfl)
  rw [syscall_spec, dispatch_arm spec_table _ _ _ brk_arm rfl]
  dsimp only [brk_arm]
  rw [brk_probe_arg]
  exact (brk_grow_within_budget_grants _ _).2 (Or.inr rfl)

/-- REFUTE: the old-break successor exits at 16, excluding a universal exit-17 verdict at may-fail.
model: `brk_probe_old_step`, the computed `brk_probe_tail_old`, and `must_exit_at_cfg_exclusive`. -/
theorem may_fail_keeps_the_old_break :
    ¬ must_exit_at_cfg may_fail_cfg brk_probe_segs (Z_to_bv 64 17) brk_probe := by
  intro h
  cases h with
  | must_exit_at_cfg_halted _ hh _ => cases hh
  | must_exit_at_cfg_running _ _ _ _ hn =>
    exact absurd (must_exit_at_cfg_exclusive _ _ _ _ _ (hn [] _ brk_probe_old_step)
      ((must_exit_at_cfg_may_fail _ _ _).2 brk_probe_tail_old)) (by decide)

/-- ACCEPT: the allowed-set running constructor also ranges over the filtered successors.
model: `must_exit_in_at_cfg_running` sees only the grant, whose tail exits in [17]. -/
theorem allowed_set_forced_only_filters_the_old_break :
    must_exit_in_at_cfg forced_only_cfg brk_probe_segs [Z_to_bv 64 17] brk_probe := by
  apply must_exit_in_at_cfg.must_exit_in_at_cfg_running _ rfl
    ⟨[], _, brk_probe_grant_step⟩
  · intro evs hs
    cases brk_probe_forced_step evs SError hs
  · intro evs c' hs
    have hc := brk_probe_forced_step evs (SNext c') hs
    cases hc
    exact (must_exit_in_at_cfg_singleton _ _ _ _).2
      (must_exit_at_cfg_of_must_exit_at _ _ _ _ (decided_from_is_total _ _ _) brk_probe_tail_grant)

/-- REFUTE: the old-break execution exits outside the singleton allowed set [17].
model: `must_exit_in_at_cfg_singleton` transfers the explicit may-fail counterexample. -/
theorem allowed_set_may_fail_keeps_the_old_break :
    ¬ must_exit_in_at_cfg may_fail_cfg brk_probe_segs [Z_to_bv 64 17] brk_probe :=
  fun h => may_fail_keeps_the_old_break ((must_exit_in_at_cfg_singleton _ _ _ _).1 h)

/-! ### The filter, at an error step

The brk probe removes a refusal that is an `SNext` step.  The two
relations also differ at `SError`, and there only through
`sstep_syscall_materialization_fault`: a refusal whose effect needs a lazy
page the budget cannot back is an error step of `Run.sstep`, and
`Run.sstep_cfg` keeps that step only when the refusal is not spurious.
The nanosleep probe is that case, so its pins read the error premise of
both running constructors (#1907, item 2). -/

/-- Code at 0x100: ecall (0x00000073), addi a7,x0,93 (0x05d00893),
ecall (0x00000073); a completed sleep returns 0, so the tail exits 0.
model: `RiscvSemantics.step` fetches these little-endian bytes from the executable segment. -/
def nanosleep_probe_segs : List Segment :=
  [{ seg_base := 0x100, seg_size := 12, seg_perms := "r-x",
     seg_bytes := ["730000009308d00573000000"] }]

/-- The one-second request at 65536 and sixteen zero bytes at 69632, both in the overlay.
model: `Run.sys_input` reads the request and the remainder destination from `ms_mem`. -/
def nanosleep_probe_mem : word → Option byte :=
  fun a => match bytes_at 65536 ts_1s a with
    | some b => some b
    | none => bytes_at 69632 (List.replicate 16 0) a

/-- The request page spends the whole 4096-byte budget; the remainder page is lazy and not yet touched.
model: `vm_add_lazy` records 69632 as lazy, and `vm_backing_used` charges only the page at 65536. -/
def nanosleep_probe_model : Model :=
  vm_add_lazy 69632 4096
    (fixture (VmMaps.mkVmMapsFull [] [(65536, 4096), (69632, 4096)] [] 0 0 4096 0 demo_sp))

/-- The machine at the pending nanosleep ecall: a0=65536 (rqtp), a1=69632 (rmtp), a7=101.
model: `Run.sys_input` reads the registers and `nanosleep_probe_mem`. -/
def nanosleep_probe_ms : machine_state :=
  { svc_ms 101 65536 69632 0 0 0 0 with
    ms_regs := bvmap_set (Z_to_bv 5 17) (Z_to_bv 64 101) (svc_ms 101 65536 69632 0 0 0 0).ms_regs,
    ms_mem := nanosleep_probe_mem }

/-- The pending nanosleep ecall over the probe ledger.
model: a running configuration; `m_halted` is none. -/
def nanosleep_probe : config := config.mkCfg nanosleep_probe_ms nanosleep_probe_model

/-- The completed sleep's effect: return 0, the request read, nothing written.
model: the `slept` arm of `Hrtimer.nanosleep_spec`, under its `record_copyins`. -/
private def nanosleep_slept : SyscallEffect := with_copyins [(65536, 16)] (mkEffect 0 [] [])

/-- The completed sleep's post-model: the clock moves by the whole request.
model: `nanosleep_clock` with no remainder, set by the `slept` arm. -/
private def nanosleep_slept_model : Model :=
  with_clock (nanosleep_clock (m_clock nanosleep_probe_model) ts_1s []) nanosleep_probe_model

/-- An interrupted sleep's effect: -EINTR, the request read, and the remainder written at 69632.
model: the -EINTR arm of `Hrtimer.nanosleep_spec` at a writable `rmtp`. -/
private def nanosleep_eintr (rem : List byte) : SyscallEffect :=
  with_copyins [(65536, 16)] (mkEffect (errno_ret EINTR) [(69632, rem)] [])

/-- An interrupted sleep's post-model: the clock at the armed deadline less the remainder, floored at where it stood.
model: `nanosleep_clock` with the remainder, set by the -EINTR arm. -/
private def nanosleep_eintr_model (rem : List byte) : Model :=
  with_clock (nanosleep_clock (m_clock nanosleep_probe_model) ts_1s rem) nanosleep_probe_model

/-- The syscall input at the probe: the two pointers in a0 and a1, and the overlay as both views.
model: `Run.sys_input` at `nanosleep_probe_ms`, a rewrite for `sys_norm`. -/
private theorem nanosleep_probe_input :
    sys_input nanosleep_probe_segs nanosleep_probe_ms 101
      = SyscallInput.mkInput 101 [65536, 69632, 0, 0, 0, 0] (ms_read_byte nanosleep_probe_ms)
          (ms_writable_byte nanosleep_probe_segs nanosleep_probe_ms) := by
  simp +decide only [sys_input, syscall_args, ms_gpr, nanosleep_probe_ms,
    svc_ms, LinuxProcessSemantics.Riscv.Sem.reg_get, bvmap_get_set, ↓reduceIte]

/-- The request reads back whole.
model: a closed `read_bytes_map` over the probe's read view, a rewrite for `sys_norm`. -/
private theorem nanosleep_probe_reads_the_request :
    read_bytes_map (ms_read_byte nanosleep_probe_ms) 65536 (Z_to_bv 64 16) = some ts_1s := by
  decide

/-- The remainder destination is wholly writable.
model: a closed `read_bytes_map` over the probe's writable view, a rewrite for `sys_norm`. -/
private theorem nanosleep_probe_rmtp_is_writable :
    read_bytes_map (ms_writable_byte nanosleep_probe_segs nanosleep_probe_ms) 69632 (Z_to_bv 64 16)
      = some (List.replicate 16 0) := by
  decide

/-- At the probe, nanosleep admits the completed sleep and every -EINTR with an admissible remainder.
It admits nothing else, `Unmodeled` included.
The request is valid and readable, and `rmtp` is writable, so both arms of the spec's `alt` are open.
A completed sleep returns 0 and writes nothing. An interruption writes the remainder, and the riscv64
signal code turns the restart code into -EINTR.
kernel: kernel/time/time.c:get_timespec64,put_timespec64; include/linux/time64.h:timespec64_valid; kernel/time/hrtimer.c:nanosleep,hrtimer_nanosleep,do_nanosleep,nanosleep_copyout; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
private theorem nanosleep_probe_outcomes (o : outcome SyscallEffect) :
    syscall_spec (sys_input nanosleep_probe_segs nanosleep_probe_ms 101) nanosleep_probe_model o ↔
      o = Ok (with_copyins [(65536, 16)] (mkEffect 0 [] []))
            (with_clock (nanosleep_clock (m_clock nanosleep_probe_model) ts_1s [])
              nanosleep_probe_model) []
      ∨ ∃ rem : List byte,
          o = Ok (with_copyins [(65536, 16)] (mkEffect (errno_ret EINTR) [(69632, rem)] []))
                (with_clock (nanosleep_clock (m_clock nanosleep_probe_model) ts_1s rem)
                  nanosleep_probe_model) []
          ∧ nanosleep_rem_ok_b rem = true := by
  rw [nanosleep_probe_input]
  rw [syscall_spec, dispatch_arm spec_table _ _ _
    Sys.Registry.Kernel.Time.Hrtimer.nanosleep_arm rfl]
  dsimp only [Sys.Registry.Kernel.Time.Hrtimer.nanosleep_arm]
  unfold Sys.Kernel.Time.Hrtimer.nanosleep_spec
  -- `in_arg` is not in `sys_simp`. Read both pointers off the literal input here, so that the two
  -- read lemmas match before `sys_norm` unfolds the reads.
  simp only [bind_input_iff, in_arg, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some,
    nanosleep_probe_reads_the_request, nanosleep_probe_rmtp_is_writable]
  sys_norm

/-- Under forced-only every -EINTR here is spurious: FamIntr is off, -EINTR is a refusal, and the completed sleep is not one.
model: `spurious_refusal_cfg`, with `nanosleep_probe_outcomes` giving the non-refusal witness. -/
private theorem nanosleep_probe_eintr_spurious (rem : List byte) :
    spurious_refusal_cfg forced_only_cfg (sys_input nanosleep_probe_segs nanosleep_probe_ms 101)
      nanosleep_probe_model (nanosleep_eintr rem) := by
  exact ⟨by decide +kernel, by
    change refusal_b _ _ (errno_ret EINTR) = true
    decide +kernel,
    nanosleep_slept, nanosleep_slept_model, [],
    (nanosleep_probe_outcomes _).2 (Or.inl rfl), by decide +kernel⟩

/-- The completed sleep touches only the request page, which is not lazy.
model: `materialize_model_accesses` finds no new lazy page and keeps the model. -/
private theorem nanosleep_slept_materializes :
    materialize_model_accesses nanosleep_slept_model (syscall_effect_accesses nanosleep_slept)
      = some nanosleep_slept_model := by
  rfl

/-- The remainder write needs the lazy page at 69632, and the spent budget cannot back it.
model: `materialize_accesses` would charge 4096 + 4096 bytes against a 4096-byte limit. -/
private theorem nanosleep_eintr_faults :
    materialize_model_accesses (nanosleep_eintr_model ts_1s) (syscall_effect_accesses (nanosleep_eintr ts_1s))
      = none := by
  rfl

/-- `Checks.Examples.exits_c` over the ACCOUNTED step: the probe's tail runs beside a lazy page, so the
no-lazy premise of `exits_c_must_exit_at` does not hold there.
model: `Run.mi_account_step`, the step `Run.sstep_instr` takes. -/
private def exits_acct_c (segs : List Segment) (code : word) : Nat → machine_state → Model → Bool
  | 0, _, _ => false
  | fuel + 1, ms, model =>
      match ms.ms_svc_pending with
      | some x8 =>
          (decide (bv_unsigned x8 = 93) || decide (bv_unsigned x8 = 94))
          && bv_eqb (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) code
      | none =>
          match mi_account_step segs ms model with
          | MachineOk (ms', model') => exits_acct_c segs code fuel ms' model'
          | MachineFault | MachineUnmodeled => false

/-- `exits_acct_c` is sound for `MustExit.must_exit_at`, with no premise on the lazy pages.
model: the proof of `exits_c_must_exit_at`, with `mi_account_step_model_frame` keeping `m_halted`. -/
private theorem exits_acct_c_must_exit_at (segs : List Segment) (code : word) (fuel : Nat) :
    ∀ (ms : machine_state) (model : Model),
    m_halted model = none →
    exits_acct_c segs code fuel ms model = true →
    must_exit_at segs code (config.mkCfg ms model) := by
  induction fuel with
  | zero => intro ms model _ hc; simp only [exits_acct_c, Bool.false_eq_true] at hc
  | succ fuel ih =>
    intro ms model hh hc
    cases hsvc : ms.ms_svc_pending with
    | some x8 =>
      -- the terminating ecall
      simp only [exits_acct_c, hsvc, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hx8, hcode⟩ := hc
      have hcode' := (bv_eqb_eq _ _).1 hcode
      have hno : exit_sysno (sys_input segs ms x8).in_sysno := hx8
      have harg : in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 := rfl
      apply must_exit_at.must_exit_at_running
      · exact hh
      · refine ⟨[] ++ [ExitEv (bv_and (in_arg (sys_input segs ms x8) 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (in_arg (sys_input segs ms x8) 0)
                                                  (Z_to_bv 64 255)) model))],
                 SNext (config.mkCfg ms (with_halted (bv_and (in_arg (sys_input segs ms x8) 0)
                                                       (Z_to_bv 64 255)) model)), ?_⟩
        exact sstep.sstep_exit ms model x8 _ _ [] _ hh hsvc (exit_dispatch_admits _ model hno) rfl rfl
      · intro evs hss
        cases hss with
        | sstep_instr_fault _ _ _ hsvc' _ => rw [hsvc] at hsvc'; cases hsvc'
        | sstep_instr_unmodeled _ _ _ hsvc' _ => rw [hsvc] at hsvc'; cases hsvc'
        | sstep_syscall_materialization_fault _ _ x8' eff model' evs' _ hsvc' hspec hh' _ =>
          rw [hsvc] at hsvc'
          cases hsvc'
          have := exit_dispatch_halts _ _ _ _ _ hno hspec
          rw [this] at hh'
          cases hh'
        | sstep_syscall_unmodeled _ _ x8' _ hsvc' hspec =>
          rw [hsvc] at hsvc'
          cases hsvc'
          exact exit_dispatch_modeled _ _ hno hspec
      · intro evs c' hss
        cases hss with
        | sstep_instr _ _ _ _ _ hsvc' _ => rw [hsvc] at hsvc'; cases hsvc'
        | sstep_syscall _ _ x8' eff model' model'' evs' _ hsvc' hspec hh' _ =>
          rw [hsvc] at hsvc'
          cases hsvc'
          have := exit_dispatch_halts _ _ _ _ _ hno hspec
          rw [this] at hh'
          cases hh'
        | sstep_exit _ _ x8' eff model' evs' code' _ hsvc' hspec hh' _ =>
          rw [hsvc] at hsvc'
          cases hsvc'
          have hhalts := exit_dispatch_halts _ _ _ _ _ hno hspec
          apply must_exit_at.must_exit_at_halted
          · show m_halted model' = some code
            rw [hhalts, harg, hcode']
          · exact exit_dispatch_not_killed _ _ _ _ _ hno hspec
        | sstep_killed _ _ x8' eff model' evs' sig _ hsvc' hspec hk =>
          -- the kill transition: an exit's post-model is not a killed one
          rw [hsvc] at hsvc'
          cases hsvc'
          rw [exit_dispatch_not_killed _ _ _ _ _ hno hspec] at hk
          cases hk
    | none =>
      -- an ordinary instruction
      simp only [exits_acct_c, hsvc] at hc
      cases hacc : mi_account_step segs ms model with
      | MachineOk result =>
        obtain ⟨ms', model'⟩ := result
        simp only [hacc] at hc
        have hh' : m_halted model' = none := by
          have hproc := (mi_account_step_model_frame segs ms model ms' model' hacc).2.2.2.2.2.1
          change model'.m_proc.procst_halted = none
          rw [hproc]
          exact hh
        apply must_exit_at.must_exit_at_running
        · exact hh
        · exact ⟨[], SNext (config.mkCfg ms' model'), sstep.sstep_instr ms model ms' model' hh hsvc hacc⟩
        · intro evs hss
          cases hss with
          | sstep_instr_fault _ _ _ _ hacc' => rw [hacc] at hacc'; cases hacc'
          | sstep_instr_unmodeled _ _ _ _ hacc' => rw [hacc] at hacc'; cases hacc'
          | sstep_syscall_materialization_fault _ _ _ _ _ _ _ hsvc' _ _ _ => rw [hsvc] at hsvc'; cases hsvc'
          | sstep_syscall_unmodeled _ _ _ _ hsvc' _ => rw [hsvc] at hsvc'; cases hsvc'
        · intro evs c' hss
          cases hss with
          | sstep_instr _ _ ms'' model'' _ _ hacc' =>
            rw [hacc] at hacc'
            cases hacc'
            exact ih ms' model' hh' hc
          | sstep_syscall _ _ _ _ _ _ _ _ hsvc' _ _ _ => rw [hsvc] at hsvc'; cases hsvc'
          | sstep_exit _ _ _ _ _ _ _ _ hsvc' _ _ _ => rw [hsvc] at hsvc'; cases hsvc'
          | sstep_killed _ _ _ _ _ _ _ _ hsvc' _ _ => rw [hsvc] at hsvc'; cases hsvc'
      | MachineFault => simp only [hacc, Bool.false_eq_true] at hc
      | MachineUnmodeled => simp only [hacc, Bool.false_eq_true] at hc

/-- The completed sleep's tail sets a7 to 93 and exits with a0 = 0, beside the untouched lazy page.
model: `exits_acct_c_must_exit_at` runs the two tail instructions and the exit. -/
private theorem nanosleep_probe_tail :
    must_exit_at nanosleep_probe_segs (Z_to_bv 64 0)
      (config.mkCfg (advance_past_svc (apply_effect nanosleep_probe_ms nanosleep_slept))
        nanosleep_slept_model) := by
  apply exits_acct_c_must_exit_at _ _ 3
  · rfl
  · decide +kernel

/-- The completed sleep is a retained step: it is not a refusal, and its access needs no new page.
model: `sstep_cfg_syscall` with `nanosleep_probe_outcomes` and `nanosleep_slept_materializes`. -/
private theorem nanosleep_probe_slept_step :
    sstep_cfg nanosleep_probe_segs forced_only_cfg nanosleep_probe []
      (SNext (config.mkCfg (advance_past_svc (apply_effect nanosleep_probe_ms nanosleep_slept))
        nanosleep_slept_model)) := by
  refine sstep_cfg.sstep_cfg_syscall nanosleep_probe_ms nanosleep_probe_model 101
    nanosleep_slept nanosleep_slept_model nanosleep_slept_model [] rfl rfl
    ?_ ?_ rfl nanosleep_slept_materializes
  · exact (nanosleep_probe_outcomes _).2 (Or.inl rfl)
  · exact spurious_refusal_not_refusal _ _ _ _ (by decide +kernel)

/-- Every forced-only step at the probe goes to the completed sleep: each -EINTR step, faulting or not, is spurious.
model: `nanosleep_probe_outcomes` lists the outcomes, and `nanosleep_probe_eintr_spurious` removes each -EINTR. -/
private theorem nanosleep_probe_forced_step (evs : List event) (st : step_to)
    (hs : sstep_cfg nanosleep_probe_segs forced_only_cfg nanosleep_probe evs st) :
    st = SNext (config.mkCfg (advance_past_svc (apply_effect nanosleep_probe_ms nanosleep_slept))
      nanosleep_slept_model) := by
  cases hs with
  | sstep_cfg_instr _ _ _ _ _ hv _ => cases hv
  | sstep_cfg_instr_fault _ _ _ hv _ => cases hv
  | sstep_cfg_instr_unmodeled _ _ _ hv _ => cases hv
  | sstep_cfg_syscall _ _ x8 eff model' model'' evs _ hv ho hf hh hm =>
    have hx : (101 : word) = x8 := Option.some.inj hv
    subst x8
    rcases (nanosleep_probe_outcomes _).1 ho with hs | ⟨rem, hr, _⟩
    · cases hs
      change materialize_model_accesses nanosleep_slept_model
        (syscall_effect_accesses nanosleep_slept) = some model'' at hm
      rw [nanosleep_slept_materializes] at hm
      cases hm
      rfl
    · cases hr
      exact False.elim (hf (nanosleep_probe_eintr_spurious rem))
  | sstep_cfg_syscall_materialization_fault _ _ x8 eff model' evs _ hv ho hf hh hm =>
    have hx : (101 : word) = x8 := Option.some.inj hv
    subst x8
    rcases (nanosleep_probe_outcomes _).1 ho with hs | ⟨rem, hr, _⟩
    · cases hs
      change materialize_model_accesses nanosleep_slept_model
        (syscall_effect_accesses nanosleep_slept) = none at hm
      rw [nanosleep_slept_materializes] at hm
      cases hm
    · cases hr
      exact False.elim (hf (nanosleep_probe_eintr_spurious rem))
  | sstep_cfg_exit _ _ x8 eff model' evs code _ hv ho hh hk =>
    have hx : (101 : word) = x8 := Option.some.inj hv
    subst x8
    rcases (nanosleep_probe_outcomes _).1 ho with hs | ⟨rem, hr, _⟩
    · cases hs; cases hh
    · cases hr; cases hh
  | sstep_cfg_killed _ _ x8 eff model' evs sig _ hv ho hk =>
    have hx : (101 : word) = x8 := Option.some.inj hv
    subst x8
    rcases (nanosleep_probe_outcomes _).1 ho with hs | ⟨rem, hr, _⟩
    · cases hs; cases hk
    · cases hr; cases hk
  | sstep_cfg_syscall_unmodeled _ _ x8 _ hv ho =>
    have hx : (101 : word) = x8 := Option.some.inj hv
    subst x8
    rcases (nanosleep_probe_outcomes _).1 ho with hs | ⟨rem, hr, _⟩
    · cases hs
    · cases hr

/-- May-fail keeps the -EINTR that reports one second left, and its remainder write faults.
model: `sstep_syscall_materialization_fault` with `nanosleep_eintr_faults`, through `sstep_cfg_may_fail`. -/
private theorem nanosleep_probe_fault_step :
    sstep_cfg nanosleep_probe_segs may_fail_cfg nanosleep_probe [] SError := by
  apply (sstep_cfg_may_fail _ _ _ _).1
  exact sstep.sstep_syscall_materialization_fault nanosleep_probe_ms nanosleep_probe_model 101
    (nanosleep_eintr ts_1s) (nanosleep_eintr_model ts_1s) [] rfl rfl
    ((nanosleep_probe_outcomes _).2 (Or.inr ⟨ts_1s, rfl, by decide +kernel⟩))
    rfl nanosleep_eintr_faults

/-- ACCEPT: removing the spurious -EINTR also removes its materialization fault, so the completed sleep exits 0.
model: `must_exit_at_cfg_running` reads its error premise over `sstep_cfg`, where `nanosleep_probe_forced_step` leaves no error. -/
theorem forced_only_filters_the_faulting_eintr :
    must_exit_at_cfg forced_only_cfg nanosleep_probe_segs (Z_to_bv 64 0) nanosleep_probe := by
  apply must_exit_at_cfg.must_exit_at_cfg_running _ rfl
    ⟨[], _, nanosleep_probe_slept_step⟩
  · intro evs hs
    cases nanosleep_probe_forced_step evs SError hs
  · intro evs c' hs
    have hc := nanosleep_probe_forced_step evs (SNext c') hs
    cases hc
    exact must_exit_at_cfg_of_must_exit_at _ _ _ _ (decided_from_is_total _ _ _) nanosleep_probe_tail

/-- REFUTE: may-fail keeps the -EINTR whose remainder write the spent budget cannot back.
model: `nanosleep_probe_fault_step` contradicts the error premise of `must_exit_at_cfg_running`. -/
theorem may_fail_keeps_the_faulting_eintr :
    ¬ must_exit_at_cfg may_fail_cfg nanosleep_probe_segs (Z_to_bv 64 0) nanosleep_probe := by
  intro h
  cases h with
  | must_exit_at_cfg_halted _ hh _ => cases hh
  | must_exit_at_cfg_running _ _ _ hnoerr _ =>
    exact hnoerr [] nanosleep_probe_fault_step

/-- ACCEPT: the allowed-set running constructor reads the same filtered error premise.
model: `must_exit_in_at_cfg_running` sees only the completed sleep, whose tail exits in [0]. -/
theorem allowed_set_forced_only_filters_the_faulting_eintr :
    must_exit_in_at_cfg forced_only_cfg nanosleep_probe_segs [Z_to_bv 64 0] nanosleep_probe := by
  apply must_exit_in_at_cfg.must_exit_in_at_cfg_running _ rfl
    ⟨[], _, nanosleep_probe_slept_step⟩
  · intro evs hs
    cases nanosleep_probe_forced_step evs SError hs
  · intro evs c' hs
    have hc := nanosleep_probe_forced_step evs (SNext c') hs
    cases hc
    exact (must_exit_in_at_cfg_singleton _ _ _ _).2
      (must_exit_at_cfg_of_must_exit_at _ _ _ _ (decided_from_is_total _ _ _) nanosleep_probe_tail)

/-- REFUTE: the faulting -EINTR also refutes the allowed set [0] at may-fail.
model: `nanosleep_probe_fault_step` contradicts the error premise of `must_exit_in_at_cfg_running`. -/
theorem allowed_set_may_fail_keeps_the_faulting_eintr :
    ¬ must_exit_in_at_cfg may_fail_cfg nanosleep_probe_segs [Z_to_bv 64 0] nanosleep_probe := by
  intro h
  cases h with
  | must_exit_in_at_cfg_halted _ _ hh _ _ => cases hh
  | must_exit_in_at_cfg_running _ _ _ hnoerr _ =>
    exact hnoerr [] nanosleep_probe_fault_step

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.MustExit
