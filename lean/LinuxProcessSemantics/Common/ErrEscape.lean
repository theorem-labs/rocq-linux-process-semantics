import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.CatSim

/-! rocq-baseline: 2cde689f94c086b868999970834b76a25616b94a -/

/-! # Common.ErrEscape — the source-error escape glue

Ported from `theories/Common/ErrEscape.v` at the baseline above, with the
Rocq names and statements: the faulting loads (`step_lbu_fault`,
`step_ld_fault`), the lemmas of the sections `WithSegs`, `OmniWithSegs`,
`AllErrorWithSegs` and `NoUnmodeledWithSegs`, and the whole-run escapes
`err_escape_*`.  Why an escape has to carry coverage as well as the error
is argued in the Rocq file's header and above its `NoUnmodeledWithSegs`
section; it is not repeated here.

An "illegal" instruction in the Rocq names (`illegal_exec`,
`illegal_all_traces_error`, `msteps_illegal_*`) is any instruction whose
step is `MachineFault`, which is what the Rocq header means by "illegal one
(e.g. a load from an unmapped address)"; the word does not mean an illegal
encoding.  The two
faulting loads reach `MachineFault` through the missed-read `ELoad` arm of
`RiscvSemantics.interp_eff_accesses`, which that function's docstring calls
the SIGSEGV analogue, not through its `EDefinedIllegal` arm.

Spellings that differ:
- Rocq Section variables become explicit leading arguments: every lemma of
  the four sections takes `segs` first.
- Rocq's `mkCfg`, `mkImage` and `mkEntry` are `config.mkCfg`,
  `Image.mkImage` and `ExecEntry.mkEntry`; `in_argv inp` and the other
  input projections are `inp.in_argv`; `ms_svc_pending ms'` is
  `ms'.ms_svc_pending`; the size `isz : Z` is an `Int`; and in the
  `err_escape_*` theorems `pc : N` is a `Nat` while `lim : Z` and
  `limT : Z` are `Int`s.

The Lean-only helpers `step_fault_of_interp` and `interp_load_none` are
used here from `PropExec`; its header explains their role in the faulting loads.

Lean-only helper named for what a Rocq tactic did inline:
- `sstep_fault_inv` is the `inversion` of an `sstep` out of a faulting
  instruction state, which Rocq repeats inline in `illegal_exec`,
  `illegal_all_traces_error` and `fault_no_unmodeled`; it is the fault twin
  of `ExitSim.sstep_instr_inv`.  `Checks.Omni.sstep_fault_only` states the
  same with the same proof and its arguments in another order; this file
  does not import `Checks.Omni`, which brings in the checker, and Rocq's
  `ErrEscape.v` does not import `Checks/Omni.v` either. -/

namespace LinuxProcessSemantics.Common.ErrEscape

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.CatSim

/-! ## Faulting loads -/

/-- A byte load from an address that both the overlay and the loaded
segments miss faults: its step is `MachineFault`, reached through the
missed-read `ELoad` arm (`interp_load_none`). -/
theorem step_lbu_fault (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (isz : Int)
    (hfetch : fetch_word segs pc = some w) (hecall : is_ecall w = false)
    (hdecode : decode_any w = some (.Load .SZ1 false rd rs imm, isz))
    (hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1 = none) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineFault := by
  refine step_fault_of_interp segs regs pc mem rom w _ isz hfetch hecall hdecode ?_
  refine interp_load_none segs 8 _ _ mem ?_
  rw [rget_mk, b_addsext, ov_rdn]
  exact hread

/-- A double load from an address that both the overlay and the loaded
segments miss faults: its step is `MachineFault`, reached through the
missed-read `ELoad` arm (`interp_load_none`). -/
theorem step_ld_fault (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (isz : Int)
    (hfetch : fetch_word segs pc = some w) (hecall : is_ecall w = false)
    (hdecode : decode_any w = some (.Load .SZ8 true rd rs imm, isz))
    (hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8 = none) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineFault := by
  refine step_fault_of_interp segs regs pc mem rom w _ isz hfetch hecall hdecode ?_
  refine interp_load_none segs 64 _ _ mem ?_
  rw [rget_mk, b_addsext, ov_rdn]
  exact hread

/-! ## msteps into a faulting step reaches the error transition -/

/-- An `msteps` run is a silent `star` (the model is untouched). -/
theorem msteps_star_nil (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hm : msteps segs ms ms') :
    star segs (config.mkCfg ms model) [] (config.mkCfg ms' model) := by
  induction hm with
  | mst_refl ms => exact star.star_refl _
  | mst_step ms ms1 ms2 hsvc hstep _ ih =>
    have hs : sstep segs (config.mkCfg ms model) [] (SNext (config.mkCfg ms1 model)) :=
      sstep.sstep_instr ms model ms1 model hh hsvc
        (by rw [mi_account_step_no_lazy _ _ _ hlazy, hstep])
    exact star.star_step _ [] _ [] _ hs ih

/-- Straight line of instructions, then one whose step is `MachineFault`:
error reached. -/
theorem msteps_illegal_error (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hm : msteps segs ms ms') (hsvc : ms'.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms' = MachineFault) :
    reaches_error segs (config.mkCfg ms model) :=
  ⟨[], config.mkCfg ms' model, [], msteps_star_nil segs ms ms' model hh hlazy hm,
    sstep.sstep_instr_fault ms' model hh hsvc
      (by rw [mi_account_step_no_lazy _ _ _ hlazy, hill])⟩

/-! ## The omni reading: one judgment for the whole escape -/

/-- Lean-only helper: out of a state whose next instruction faults, the one
transition is the silent error. -/
theorem sstep_fault_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (evs : List event) (st : step_to)
    (hlazy : m_vm_lazy model = []) (hsvc : ms.ms_svc_pending = none)
    (hfault : RiscvSemantics.step segs ms = MachineFault)
    (hs : sstep segs (config.mkCfg ms model) evs st) :
    evs = [] ∧ st = SError := by
  have hacc : mi_account_step segs ms model = MachineFault := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, hfault]
  cases hs with
  | sstep_instr _ _ _ _ _ _ ha => rw [hacc] at ha; cases ha
  | sstep_instr_fault _ _ _ _ _ => exact ⟨rfl, rfl⟩
  | sstep_instr_unmodeled _ _ _ _ ha => rw [hacc] at ha; cases ha
  | sstep_syscall _ _ _ _ _ _ _ _ hv _ _ _ => rw [hsvc] at hv; cases hv
  | sstep_syscall_materialization_fault _ _ _ _ _ _ _ hv _ _ _ => rw [hsvc] at hv; cases hv
  | sstep_exit _ _ _ _ _ _ _ _ hv _ _ _ => rw [hsvc] at hv; cases hv
  | sstep_killed _ _ _ _ _ _ _ _ hv _ _ => rw [hsvc] at hv; cases hv
  | sstep_syscall_unmodeled _ _ _ _ hv _ => rw [hsvc] at hv; cases hv

/-- The faulting state: its only transition is the error one, taken from
itself. -/
theorem illegal_exec (segs : List Segment) (ms : machine_state) (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hsvc : ms.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms = MachineFault) :
    exec segs (config.mkCfg ms model)
      (fun tr o => tr = [] ∧ o = OError (config.mkCfg ms model)) := by
  apply exec.exec_step _ _ hh
    ⟨[], SError, sstep.sstep_instr_fault ms model hh hsvc
      (by rw [mi_account_step_no_lazy _ _ _ hlazy, hill])⟩
  · intro evs hs
    exact ⟨(sstep_fault_inv segs ms model evs SError hlazy hsvc hill hs).1, rfl⟩
  · intro evs c' hs
    cases (sstep_fault_inv segs ms model evs (SNext c') hlazy hsvc hill hs).2

/-- One ordinary instruction in front of any omni judgment: the transition
is unique and silent, so the postcondition is unchanged. -/
theorem instr_exec (segs : List Segment) (ms ms' : machine_state) (model : Model) (Q : post)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hsvc : ms.ms_svc_pending = none)
    (hstep : RiscvSemantics.step segs ms = MachineOk ms')
    (hex : exec segs (config.mkCfg ms' model) Q) :
    exec segs (config.mkCfg ms model) Q := by
  apply exec_step_only segs _ _ [] (config.mkCfg ms' model)
  · exact sstep.sstep_instr ms model ms' model hh hsvc
      (by rw [mi_account_step_no_lazy _ _ _ hlazy, hstep])
  · intro evs st hs
    exact sstep_instr_inv segs ms model ms' evs st hlazy hsvc hstep hs
  · exact exec_conseq segs _ _ _ hex (fun _ _ h => h)

theorem msteps_exec (segs : List Segment) (ms ms' : machine_state) (model : Model) (Q : post)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hm : msteps segs ms ms')
    (hex : exec segs (config.mkCfg ms' model) Q) :
    exec segs (config.mkCfg ms model) Q := by
  revert hex
  induction hm with
  | mst_refl => exact id
  | mst_step ms0 ms1 _ hsvc hstep _ ih =>
    intro hex
    exact instr_exec segs ms0 ms1 model Q hh hlazy hsvc hstep (ih hex)

/-- THE judgment: a deterministic instruction path ending in an instruction
whose step is `MachineFault` errors, on every execution, from that
instruction's configuration. -/
theorem msteps_illegal_exec (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hm : msteps segs ms ms') (hsvc : ms'.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms' = MachineFault) :
    exec segs (config.mkCfg ms model)
      (fun tr o => tr = [] ∧ o = OError (config.mkCfg ms' model)) :=
  msteps_exec segs ms ms' model _ hh hlazy hm (illegal_exec segs ms' model hh hlazy hsvc hill)

/-- The faulting configuration is covered: the fault is a `MachineFault`,
not the model giving up. -/
theorem fault_covered_at (segs : List Segment) (ms : machine_state) (model : Model)
    (hlazy : m_vm_lazy model = []) (hsvc : ms.ms_svc_pending = none)
    (hfault : RiscvSemantics.step segs ms = MachineFault) :
    ¬ unmodeled_at segs (config.mkCfg ms model) := by
  rintro ⟨_, ⟨_, hum⟩ | ⟨x8, hsvc', _⟩⟩
  · have hum' : mi_account_step segs ms model = MachineUnmodeled := hum
    rw [mi_account_step_no_lazy _ _ _ hlazy, hfault] at hum'
    cases hum'
  · have hsvc'' : ms.ms_svc_pending = some x8 := hsvc'
    rw [hsvc] at hsvc''
    cases hsvc''

/-- What the one judgment yields: the escape ... -/
theorem msteps_illegal_errors (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hm : msteps segs ms ms') (hsvc : ms'.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms' = MachineFault) :
    exec segs (config.mkCfg ms model) errors :=
  exec_conseq segs _ _ _ (msteps_illegal_exec segs ms ms' model hh hlazy hm hsvc hill)
    (fun _ _ ⟨_, ho⟩ => by subst ho; exact trivial)

/-- ... and coverage, without a separate walk of the path. -/
theorem msteps_illegal_covered (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hm : msteps segs ms ms') (hsvc : ms'.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms' = MachineFault) :
    coexec segs (config.mkCfg ms model) (covered segs) :=
  exec_coexec segs _ _
    (exec_conseq segs _ _ _ (msteps_illegal_exec segs ms ms' model hh hlazy hm hsvc hill)
      (fun _ _ ⟨_, ho⟩ => by subst ho; exact fault_covered_at segs ms' model hlazy hsvc hill))

/-- Bites: the judgment NAMES the outcome, so the other readings of the same
path are refuted — it does not exit with any code. -/
theorem msteps_illegal_no_exit (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hm : msteps segs ms ms') (hsvc : ms'.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms' = MachineFault) :
    ∀ code, ¬ exec segs (config.mkCfg ms model) (exits_with code) := by
  intro code hex
  obtain ⟨tr, o, hm', _, ho⟩ :=
    exec_realizes segs _ _ (msteps_illegal_exec segs ms ms' model hh hlazy hm hsvc hill)
  subst ho
  exact exec_sound segs _ _ hex tr _ hm'

/-- The other bite on the same path: it is not error-free. -/
theorem msteps_illegal_not_never_errors (segs : List Segment) (ms ms' : machine_state)
    (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hm : msteps segs ms ms') (hsvc : ms'.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms' = MachineFault) :
    ¬ coexec segs (config.mkCfg ms model) never_errors := by
  intro hco
  obtain ⟨tr, o, hm', _, ho⟩ :=
    exec_realizes segs _ _ (msteps_illegal_exec segs ms ms' model hh hlazy hm hsvc hill)
  subst ho
  exact coexec_sound segs _ _ _ hm' _ hco trivial

/-! ## Universal error for deterministic instruction paths -/

/-- An ordinary-instruction state whose step is `MachineFault` has exactly
the error step (`sstep_fault_inv`) and therefore all of its executions
error. -/
theorem illegal_all_traces_error (segs : List Segment) (ms : machine_state) (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hsvc : ms.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms = MachineFault) :
    all_traces_error segs (config.mkCfg ms model) := by
  apply all_traces_error.all_traces_error_intro
  · exact ⟨[], SError, sstep.sstep_instr_fault ms model hh hsvc
      (by rw [mi_account_step_no_lazy _ _ _ hlazy, hill])⟩
  · intro evs c' hs
    cases (sstep_fault_inv segs ms model evs (SNext c') hlazy hsvc hill hs).2

/-- Prepending the unique ordinary instruction transition preserves the
universal error property. -/
theorem instr_all_traces_error (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hsvc : ms.ms_svc_pending = none)
    (hstep : RiscvSemantics.step segs ms = MachineOk ms')
    (hall : all_traces_error segs (config.mkCfg ms' model)) :
    all_traces_error segs (config.mkCfg ms model) := by
  apply all_traces_error.all_traces_error_intro
  · exact ⟨[], SNext (config.mkCfg ms' model), sstep.sstep_instr ms model ms' model hh hsvc
      (by rw [mi_account_step_no_lazy _ _ _ hlazy, hstep])⟩
  · intro evs c' hs
    obtain ⟨_, hto⟩ := sstep_instr_inv segs ms model ms' evs (SNext c') hlazy hsvc hstep hs
    cases hto
    exact hall

/-- Prepend any deterministic sequence of ordinary instructions to an
all-error configuration. -/
theorem msteps_all_traces_error (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hm : msteps segs ms ms')
    (hall : all_traces_error segs (config.mkCfg ms' model)) :
    all_traces_error segs (config.mkCfg ms model) := by
  revert hall
  induction hm with
  | mst_refl => exact id
  | mst_step ms0 ms1 _ hsvc hstep _ ih =>
    intro hall
    exact instr_all_traces_error segs ms0 ms1 model hh hlazy hsvc hstep (ih hall)

/-- A deterministic instruction path ending in an instruction whose step is
`MachineFault` has no alternative non-error trace. -/
theorem msteps_illegal_all_traces_error (segs : List Segment) (ms ms' : machine_state)
    (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hm : msteps segs ms ms') (hfinal_svc : ms'.ms_svc_pending = none)
    (hillegal : RiscvSemantics.step segs ms' = MachineFault) :
    all_traces_error segs (config.mkCfg ms model) :=
  (all_traces_error_iff segs _).2
    (msteps_illegal_errors segs ms ms' model hh hlazy hm hfinal_svc hillegal)

/-! ## Coverage: the deterministic fault path is MODELED -/

/-- From a configuration with no `SNext` successor, `star` reaches only that
configuration. -/
theorem star_stuck_refl (segs : List Segment) (c : config) (tr : List event) (c' : config)
    (hno : ∀ evs c2, ¬ sstep segs c evs (SNext c2))
    (hstar : star segs c tr c') : c' = c := by
  cases hstar with
  | star_refl => rfl
  | star_step _ evs c2 _ _ hs _ => exact absurd hs (hno evs c2)

/-- The faulting state itself is covered: its only transition is the error
one (`sstep_fault_inv`), and that error is a genuine fault. -/
theorem fault_no_unmodeled (segs : List Segment) (ms : machine_state) (model : Model)
    (hlazy : m_vm_lazy model = []) (hsvc : ms.ms_svc_pending = none)
    (hfault : RiscvSemantics.step segs ms = MachineFault) :
    ¬ reaches_unmodeled segs (config.mkCfg ms model) := by
  rintro ⟨tr, c, hstar, hun⟩
  have hno : ∀ evs c2, ¬ sstep segs (config.mkCfg ms model) evs (SNext c2) :=
    fun evs c2 hs => by
      cases (sstep_fault_inv segs ms model evs (SNext c2) hlazy hsvc hfault hs).2
  rw [star_stuck_refl segs _ tr c hno hstar] at hun
  exact fault_covered_at segs ms model hlazy hsvc hfault hun

/-- One ordinary instruction in front of a covered configuration. -/
theorem instr_no_unmodeled (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (hlazy : m_vm_lazy model = []) (hsvc : ms.ms_svc_pending = none)
    (hstep : RiscvSemantics.step segs ms = MachineOk ms')
    (hnext : ¬ reaches_unmodeled segs (config.mkCfg ms' model)) :
    ¬ reaches_unmodeled segs (config.mkCfg ms model) := by
  rintro ⟨tr, c, hstar, hun⟩
  cases hstar with
  | star_refl =>
    obtain ⟨_, ⟨_, hum⟩ | ⟨x8, hsvc', _⟩⟩ := hun
    · have hum' : mi_account_step segs ms model = MachineUnmodeled := hum
      rw [mi_account_step_no_lazy _ _ _ hlazy, hstep] at hum'
      cases hum'
    · have hsvc'' : ms.ms_svc_pending = some x8 := hsvc'
      rw [hsvc] at hsvc''
      cases hsvc''
  | star_step _ evs c2 tr2 _ hs hrest =>
    obtain ⟨_, hc2⟩ := sstep_instr_inv segs ms model ms' evs (SNext c2) hlazy hsvc hstep hs
    cases hc2
    exact hnext ⟨tr2, c, hrest, hun⟩

/-- A deterministic instruction path ending in a genuine fault never reaches
a configuration the model does not cover. -/
theorem msteps_fault_no_unmodeled (segs : List Segment) (ms ms' : machine_state)
    (model : Model)
    (hm : msteps segs ms ms') (hlazy : m_vm_lazy model = [])
    (hsvc : ms'.ms_svc_pending = none)
    (hfault : RiscvSemantics.step segs ms' = MachineFault) :
    ¬ reaches_unmodeled segs (config.mkCfg ms model) := by
  cases hh : m_halted model with
  | some code =>
    -- a halted model takes no transition, and a halted configuration is
    -- not one the model declined
    rintro ⟨tr, c, hstar, hun⟩
    cases hstar with
    | star_refl =>
      have hrun : m_halted model = none := hun.1
      rw [hh] at hrun
      cases hrun
    | star_step _ evs c2 _ _ hs _ =>
      have hrun : m_halted model = none := sstep_from_running segs _ _ _ hs
      rw [hh] at hrun
      cases hrun
  | none =>
    exact coexec_covered segs _ (msteps_illegal_covered segs ms ms' model hh hlazy hm hsvc hfault)

/-! ## Equivalence-level escape -/

/-- The omni escape, per run: the source's judgment at any budget ... -/
theorem err_escape_omni_run (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (ms' : machine_state)
    (hm : msteps segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap) ms')
    (hsvc : ms'.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms' = MachineFault) :
    omni_run (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp errors :=
  msteps_illegal_errors segs _ ms' (init_model (segments_reserved segs) brk0 mb sp lim inp)
    rfl rfl hm hsvc hill

/-- ... its coverage ... -/
theorem err_escape_omni_covered (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (ms' : machine_state)
    (hm : msteps segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap) ms')
    (hsvc : ms'.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms' = MachineFault) :
    omni_corun (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp
      (covered segs) :=
  msteps_illegal_covered segs _ ms' (init_model (segments_reserved segs) brk0 mb sp lim inp)
    rfl rfl hm hsvc hill

/-- ... `OmniEquivalence.omni_equiv` against ANY target run ... -/
theorem err_escape_omni_equiv (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (T : Image)
    (limT : Int) (et : ExecEntry) (ms' : machine_state)
    (hm : msteps segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap) ms')
    (hsvc : ms'.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms' = MachineFault) :
    omni_equiv (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) T limT et
      inp :=
  Or.inl (err_escape_omni_run segs pc ph sp brk0 mb rnd lim inp ms' hm hsvc hill)

/-- ... and the packaged `OmniEquivalence.omni_strong_equiv`: a source that
deterministically faults, against any target image and entry. -/
theorem err_escape_omni_strong_equiv (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (inp : ProcInput) (T : Image) (et : ExecEntry)
    (ms' : machine_state)
    (hm : msteps segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap) ms')
    (hsvc : ms'.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms' = MachineFault) :
    omni_strong_equiv (Image.mkImage segs pc ph) T (ExecEntry.mkEntry sp brk0 mb rnd) et
      inp :=
  ⟨err_escape_omni_covered segs pc ph sp brk0 mb rnd _ inp ms' hm hsvc hill,
    err_escape_omni_equiv segs pc ph sp brk0 mb rnd _ inp T _ et ms' hm hsvc hill⟩

/-- If the SOURCE deterministically runs into a faulting instruction,
`equiv` holds against ANY target behavior (the escape in
`Equivalence.equiv`): the target is freed entirely.  From the omni judgment
through `OmniRun.bh_all_errors_iff`. -/
theorem err_escape_equiv (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (target : behavior)
    (ms' : machine_state)
    (hm : msteps segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap) ms')
    (hsvc : ms'.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms' = MachineFault) :
    equiv (run (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp)
      target :=
  Or.inl ((bh_all_errors_iff _ _ _ _).2
    (err_escape_omni_run segs pc ph sp brk0 mb rnd lim inp ms' hm hsvc hill))

/-- ...and the same run is MODELED: it dies, but at a `MachineFault`, with
nothing but ordinary instructions before it.  This is what stops the escape
from being a way to launder an unmodeled source through the theorem.  From
the same omni judgment, through `OmniEquivalence.modeled_iff`. -/
theorem err_escape_modeled (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (ms' : machine_state)
    (hm : msteps segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap) ms')
    (hsvc : ms'.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms' = MachineFault) :
    modeled (run (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp) :=
  (modeled_iff _ _ _ _).2
    (err_escape_omni_covered segs pc ph sp brk0 mb rnd lim inp ms' hm hsvc hill)

/-- The packaged escape: both clauses of `Equivalence.strong_equiv` for a
source that deterministically faults, against ANY target. -/
theorem err_escape_strong_equiv (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (target : behavior)
    (ms' : machine_state)
    (hm : msteps segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap) ms')
    (hsvc : ms'.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms' = MachineFault) :
    modeled (run (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp) ∧
      equiv (run (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp)
        target :=
  ⟨err_escape_modeled segs pc ph sp brk0 mb rnd lim inp ms' hm hsvc hill,
    err_escape_equiv segs pc ph sp brk0 mb rnd lim inp target ms' hm hsvc hill⟩

end LinuxProcessSemantics.Common.ErrEscape
