import LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence

/-! # Exit-only program proofs

Ports `Common/ExitSim.v`'s exit dispatch, `to_exit`, transition inversion,
and `to_exit_exec` at f44244ad6b8041aa83053d9ca91e090037ed743b, the shape
with `m_killed` (ticket A12; first read at 9a070af9).
The initialized wrapper carries the entry draws and shared hardware input
added by `7f386a77`; the abort-declared runtime is separate port work.
The `_te` entry points accept symbolic derivations directly, avoiding the
reference's optional fuel-bounded executable witness and CatSim's I/O
dependencies. They prove the baseline execution/equivalence contracts with
the current entry and shared-input parameters.
The executable witness and stack-enumeration helpers remain unported here.
-/

namespace LinuxProcessSemantics.Common.ExitSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence

def is_exit_no (no : word) : Prop := bv_unsigned no = 93 ∨ bv_unsigned no = 94

theorem syscall_spec_exit (i : SyscallInput) (m : Model)
    (o : LinuxProcessSemantics.LinuxProcessSem.Monad.outcome SyscallEffect)
    (hno : is_exit_no i.in_sysno) : syscall_spec i m o ↔ exit_spec (in_arg i 0) i m o := by
  rcases hno with h | h
  · unfold syscall_spec dispatch; rw [h]; exact Iff.rfl
  · unfold syscall_spec dispatch; rw [h]; exact Iff.rfl

theorem exit_dispatch_ok (i : SyscallInput) (m : Model) (hno : is_exit_no i.in_sysno) :
    syscall_spec i m (Ok (mkEffect (Z_to_bv 64 0) [] [])
      (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []) := by
  apply (syscall_spec_exit i m _ hno).2
  exact bind_ok _ _ i m () _ [] _ _ [] rfl rfl

theorem exit_dispatch_ok_inv (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) (hno : is_exit_no i.in_sysno)
    (hspec : syscall_spec i m (Ok eff m' evs)) :
    eff = mkEffect (Z_to_bv 64 0) [] [] ∧
      m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m ∧ evs = [] := by
  have h := (syscall_spec_exit i m _ hno).1 hspec
  obtain ⟨x, m1, evs1, evs2, h1, h2, h3⟩ := h
  have h1' : Ok x m1 evs1 = Ok () (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) [] := h1
  cases h1'
  have h2' : Ok eff m' evs2 = Ok (mkEffect (Z_to_bv 64 0) [] []) _ [] := h2
  cases h2'
  exact ⟨rfl, rfl, by simpa using h3⟩

theorem exit_dispatch_no_unmodeled (i : SyscallInput) (m : Model)
    (hno : is_exit_no i.in_sysno) : ¬ syscall_spec i m Unmodeled := by
  intro hspec
  have h := (syscall_spec_exit i m _ hno).1 hspec
  rcases h with h | ⟨x, m1, evs1, h1, h2⟩
  · have h' : (Unmodeled : LinuxProcessSemantics.LinuxProcessSem.Monad.outcome Unit) =
        Ok () (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) [] := h
    cases h'
  · have h' : (Unmodeled : LinuxProcessSemantics.LinuxProcessSem.Monad.outcome SyscallEffect) =
        Ok (mkEffect (Z_to_bv 64 0) [] []) m1 [] := h2
    cases h'

theorem in_arg0_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 := rfl

inductive to_exit (segs : List Segment) (code : word) : machine_state → Prop
  | te_here : ∀ ms x8,
      ms.ms_svc_pending = some x8 → is_exit_no x8 → ms_gpr ms 0 = code → to_exit segs code ms
  | te_step : ∀ ms ms',
      ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      to_exit segs code ms' → to_exit segs code ms

/-- Rocq's generated induction principle for `to_exit`.  Lean generates no
non-dependent `_ind`: `to_exit.rec`, and the `recOn`/`casesOn` built on it,
take a motive over the derivation, so it is stated here with the Rocq
statement. -/
theorem to_exit_ind (segs : List Segment) (code : word) (P : machine_state → Prop)
    (f : ∀ ms x8, ms.ms_svc_pending = some x8 → is_exit_no x8 → ms_gpr ms 0 = code → P ms)
    (f0 : ∀ ms ms', ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      to_exit segs code ms' → P ms' → P ms) :
    ∀ m, to_exit segs code m → P m := by
  intro m h
  induction h with
  | te_here ms x8 hs hx hc => exact f ms x8 hs hx hc
  | te_step ms ms' hs hst h ih => exact f0 ms ms' hs hst h ih

theorem sstep_instr_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (evs : List event) (st : step_to)
    (hlazy : m_vm_lazy model = []) (hsvc : ms.ms_svc_pending = none)
    (hstep : step segs ms = MachineOk ms') (hs : sstep segs (config.mkCfg ms model) evs st) :
    evs = [] ∧ st = SNext (config.mkCfg ms' model) := by
  have hacc : mi_account_step segs ms model = MachineOk (ms', model) := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, hstep]
  cases hs with
  | sstep_instr _ _ _ _ _ _ ha => rw [hacc] at ha; cases ha; exact ⟨rfl, rfl⟩
  | sstep_instr_fault _ _ _ _ ha => rw [hacc] at ha; cases ha
  | sstep_instr_unmodeled _ _ _ _ ha => rw [hacc] at ha; cases ha
  | sstep_syscall _ _ _ _ _ _ _ _ hv _ _ _ => rw [hsvc] at hv; cases hv
  | sstep_syscall_materialization_fault _ _ _ _ _ _ _ hv _ _ _ => rw [hsvc] at hv; cases hv
  | sstep_exit _ _ _ _ _ _ _ _ hv _ _ _ => rw [hsvc] at hv; cases hv
  | sstep_killed _ _ _ _ _ _ _ _ hv _ _ => rw [hsvc] at hv; cases hv
  | sstep_syscall_unmodeled _ _ _ _ hv _ => rw [hsvc] at hv; cases hv

theorem sstep_exit_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (evs : List event) (st : step_to)
    (_hh : m_halted model = none) (hsvc : ms.ms_svc_pending = some x8)
    (hno : is_exit_no x8) (hs : sstep segs (config.mkCfg ms model) evs st) :
    evs = [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)] ∧
      st = SNext (config.mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)) := by
  cases hs with
  | sstep_instr _ _ _ _ _ hv _ => rw [hsvc] at hv; cases hv
  | sstep_instr_fault _ _ _ hv _ => rw [hsvc] at hv; cases hv
  | sstep_instr_unmodeled _ _ _ hv _ => rw [hsvc] at hv; cases hv
  | sstep_syscall _ _ x8' eff m' m'' evs' _ hv hspec hn _ =>
    rw [hsvc] at hv
    cases hv
    obtain ⟨_, rfl, _⟩ := exit_dispatch_ok_inv _ _ _ _ _ hno hspec
    rw [m_halted_with_halted] at hn
    cases hn
  | sstep_syscall_materialization_fault _ _ x8' eff m' evs' _ hv hspec hn _ =>
    rw [hsvc] at hv
    cases hv
    obtain ⟨_, rfl, _⟩ := exit_dispatch_ok_inv _ _ _ _ _ hno hspec
    rw [m_halted_with_halted] at hn
    cases hn
  | sstep_exit _ _ x8' eff m' evs' code _ hv hspec hh _ =>
    rw [hsvc] at hv
    cases hv
    obtain ⟨_, rfl, rfl⟩ := exit_dispatch_ok_inv _ _ _ _ _ hno hspec
    rw [m_halted_with_halted] at hh
    cases hh
    exact ⟨rfl, rfl⟩
  | sstep_killed _ _ x8' eff m' evs' sig _ hv hspec hk =>
    -- the exit arm's post-model is `with_halted`'s, whose `m_killed` is
    -- `none` by construction
    rw [hsvc] at hv
    cases hv
    obtain ⟨_, rfl, _⟩ := exit_dispatch_ok_inv _ _ _ _ _ hno hspec
    have hk' : (none : Option word) = some sig := hk
    cases hk'
  | sstep_syscall_unmodeled _ _ x8' _ hv hspec =>
    rw [hsvc] at hv
    cases hv
    exact False.elim (exit_dispatch_no_unmodeled _ _ hno hspec)

def exit_post (code : word) (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) : post :=
  fun tr o => tr = [ExitEv (bv_and code (Z_to_bv 64 255)) fs] ∧
    exits_with (bv_and code (Z_to_bv 64 255)) tr o

theorem to_exit_exec (segs : List Segment) (code : word) (ms : machine_state) (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hte : to_exit segs code ms) :
    exec segs (config.mkCfg ms model) (exit_post code (m_fs model)) := by
  induction hte with
  | te_here ms x8 hsvc hno hg =>
    apply exec_step_only segs _ _
      [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      (config.mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))
    · exact sstep.sstep_exit ms model x8 _ _ [] _ hh hsvc
        (exit_dispatch_ok _ model hno) rfl rfl
    · intro evs st hs
      exact sstep_exit_inv _ _ _ _ _ _ hh hsvc hno hs
    · apply exec.exec_halt
      · simp [m_halted_with_halted]
      · simp only [List.append_nil, exit_post, exits_with]
        exact ⟨by rw [hg], by rw [m_halted_with_halted, hg], rfl⟩
  | te_step ms ms' hsvc hstep hte ih =>
    apply exec_step_only segs _ _ [] (config.mkCfg ms' model)
    · apply sstep.sstep_instr _ _ _ _ hh hsvc
      rw [mi_account_step_no_lazy _ _ _ hlazy, hstep]
    · intro evs st hs
      exact sstep_instr_inv _ _ _ _ _ _ hlazy hsvc hstep hs
    · exact ih

/-- Symbolic counterpart of `ExitSim.exit_omni_run`, proved from the same
`to_exit_exec` theorem without requiring concrete input or execution fuel. -/
theorem exit_omni_run_te (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (draw : EntryDraw) (lim : Int) (code : word) (inp : ProcInput)
    (hte : to_exit segs code (init_machine_state segs pc ph sp draw inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)) :
    omni_run (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb draw) inp
      (exit_post code inp.in_fs) :=
  to_exit_exec segs code _ (init_model (segments_reserved segs) brk0 mb sp lim inp) rfl rfl hte

theorem exit_obs_iff_te (img : Image) (lim : Int) (en : ExecEntry)
    (code : word) (inp : ProcInput) (h : omni_run img lim en inp (exit_post code inp.in_fs))
    (tr : List event) :
    (run img lim en inp).bh_traces tr ↔
      is_prefix tr [ExitEv (bv_and code (Z_to_bv 64 255)) inp.in_fs] := by
  apply exec_obs_iff
  apply exec_conseq _ _ _ _ h
  intro tr o hq
  exact ⟨hq.1, exits_with_never_errors _ _ _ hq.2⟩

theorem exit_no_error_te (img : Image) (lim : Int) (en : ExecEntry)
    (code : word) (inp : ProcInput) (h : omni_run img lim en inp (exit_post code inp.in_fs)) :
    ¬ (run img lim en inp).bh_errors := by
  apply exec_no_error
  apply exec_conseq _ _ _ _ h
  intro tr o hq
  exact exits_with_never_errors _ _ _ hq.2

/-- Both premises require actual termination and the same observed trace;
the conclusion is the repository's original equivalence, including coverage. -/
theorem exit_strong_equiv_of_runs (source target : Image) (es et : ExecEntry)
    (code : word) (inp : ProcInput)
    (hs : omni_run source source_alloc_limit es inp (exit_post code inp.in_fs))
    (ht : omni_run target target_alloc_limit et inp (exit_post code inp.in_fs)) :
    strong_equiv source target es et inp := by
  refine ⟨?_, Or.inr ⟨?_, exit_no_error_te _ _ _ _ _ ht⟩⟩
  · exact no_error_no_unmodeled _ _ (exit_no_error_te _ _ _ _ _ hs)
  · intro tr
    exact (exit_obs_iff_te _ _ _ _ _ hs tr).trans (exit_obs_iff_te _ _ _ _ _ ht tr).symm

theorem exit_omni_strong_equiv_of_runs (source target : Image) (es et : ExecEntry)
    (code : word) (inp : ProcInput)
    (hs : omni_run source source_alloc_limit es inp (exit_post code inp.in_fs))
    (ht : omni_run target target_alloc_limit et inp (exit_post code inp.in_fs)) :
    omni_strong_equiv source target es et inp :=
  (strong_equiv_iff _ _ _ _ _).1 (exit_strong_equiv_of_runs _ _ _ _ _ _ hs ht)

/-! ## Additions for the E proof library

Ported from `theories/Common/ExitSim.v` at
2cde689f94c086b868999970834b76a25616b94a (ticket E-proof-library): the
syscall-number decoding fact, the two trace corollaries of `to_exit_exec`,
and the on-path invariant, with the Rocq statements; Rocq's `Section
WithSegs` variables `segs` and `code` are explicit leading arguments.
Rocq's generated `to_exit_ind`, which Lean does not generate, is stated as
a theorem after `to_exit` above.

What is left of the Rocq file after this and the part ported earlier:
`star_halted_nil`, `star_on_path` and `to_exit_no_error`; Rocq's generated
SProp eliminator `to_exit_sind` (Lean has no SProp); the executable
witness (`sim_c`, `sim_c_to_exit`, `sim_step`, `sim_c_exit_now`,
`sim_ecall_exit`); the stack-enumeration helpers (`overlay_argc_bytes`
through `init_eq_enum_state`); and the seven Rocq-named whole-run
statements, each of which takes a `sim_c` witness.  Five have a stand-in
above, which takes a `to_exit` derivation (`exit_omni_run_te`) or the
`omni_run` that one gives (the other four) instead:
`exit_omni_run_te`, `exit_obs_iff_te` and
`exit_no_error_te` for `exit_omni_run`, `exit_obs_iff` and
`exit_no_error_run`; `exit_omni_strong_equiv_of_runs` for
`exit_omni_strong_equiv`; and `exit_strong_equiv_of_runs` for
`exit_strong_equiv`, though only at the two role budgets
(`source_alloc_limit`, `target_alloc_limit`), where Rocq's quantifies over
`rlim` and `alim`.  The other two, `exit_must_exit_with` and
`exit_omni_run_code_unique`, have no counterpart in lean/.  cat1024_ns
reaches none of them. -/

/-- `in_sysno (sys_input segs ms x8) = x8`. -/
theorem in_sysno_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_sysno = x8 := rfl

theorem to_exit_star_only (segs : List Segment) (code : word) (ms : machine_state)
    (model : Model) (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hte : to_exit segs code ms) :
    ∀ tr c, star segs (config.mkCfg ms model) tr c →
      tr = [] ∨ tr = [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)] := by
  intro tr c hstar
  obtain ⟨tr', o, _, hq⟩ :=
    exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_exit_exec segs code ms model hh hlazy hte) hstar)
  have heq : tr ++ tr' = [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)] := hq.1
  cases tr with
  | nil => exact Or.inl rfl
  | cons e tr1 =>
    cases tr1 with
    | nil =>
      right
      have h1 : e = ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model) :=
        (List.cons.inj heq).1
      rw [h1]
    | cons e2 tr2 =>
      have h2 : (e2 :: tr2) ++ tr' = [] := (List.cons.inj heq).2
      cases h2

theorem to_exit_star_admits (segs : List Segment) (code : word) (ms : machine_state)
    (model : Model) (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hte : to_exit segs code ms) :
    ∃ c, star segs (config.mkCfg ms model)
      [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)] c := by
  obtain ⟨tr, o, hm, heq, hx⟩ := exec_realizes _ _ _ (to_exit_exec segs code ms model hh hlazy hte)
  cases o with
  | OError c' => exact False.elim hx
  | OHalt c' =>
    subst heq
    exact ⟨c', (mexec_halt_star _ _ _ _ hm c' rfl).1⟩

/-- On-path invariant: a reachable config is either still on the straight
line (model not halted, `to_exit` holds) or already halted. -/
def on_path (segs : List Segment) (code : word) (c : config) : Prop :=
  (m_halted c.cfg_model = none ∧ m_vm_lazy c.cfg_model = [] ∧ to_exit segs code c.cfg_ms)
    ∨ m_halted c.cfg_model ≠ none

theorem on_path_step (segs : List Segment) (code : word) (c : config) (evs : List event)
    (c' : config) (hop : on_path segs code c) (hss : sstep segs c evs (SNext c')) :
    on_path segs code c' := by
  obtain ⟨ms, model⟩ := c
  obtain ⟨ms', model'⟩ := c'
  rcases hop with ⟨hh, hlazy, hte⟩ | hh
  · cases hte with
    | te_here _ x8 hsvc hx8 _ =>
      obtain ⟨_, hc'⟩ := sstep_exit_inv segs ms model x8 evs _ hh hsvc hx8 hss
      cases hc'
      right
      show m_halted (with_halted _ model) ≠ none
      rw [m_halted_with_halted]
      intro hn
      cases hn
    | te_step _ ms0' hsvc hstep hte' =>
      obtain ⟨_, hc'⟩ := sstep_instr_inv segs ms model ms0' evs _ hlazy hsvc hstep hss
      cases hc'
      exact Or.inl ⟨hh, hlazy, hte'⟩
  · exact False.elim (hh (sstep_from_running _ _ _ _ hss))

theorem on_path_no_error (segs : List Segment) (code : word) (c : config) (evs : List event)
    (hop : on_path segs code c) : ¬ sstep segs c evs SError := by
  intro hss
  obtain ⟨ms, model⟩ := c
  rcases hop with ⟨hh, hlazy, hte⟩ | hh
  · cases hte with
    | te_here _ x8 hsvc hx8 _ =>
      obtain ⟨_, hc'⟩ := sstep_exit_inv segs ms model x8 evs _ hh hsvc hx8 hss
      cases hc'
    | te_step _ ms0' hsvc hstep _ =>
      obtain ⟨_, hc'⟩ := sstep_instr_inv segs ms model ms0' evs _ hlazy hsvc hstep hss
      cases hc'
  · exact hh (sstep_from_running _ _ _ _ hss)

end LinuxProcessSemantics.Common.ExitSim
