import LinuxProcessSemantics.Common.FileSim.Base
import LinuxProcessSemantics.Common.ErrEscape

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-!
unported: spec_err_all_traces_error — Rocq's proof turns a spec `Ok` into `CheckOk` with `check_syscall_complete_ok`, which in `Checks/ExecutableSpecs.lean` takes the premise `lookups_agree_at (bv_unsigned i.in_sysno)`; `check_syscall_complete_unmodeled` takes none, but the proof needs both, and the statement carries no such premise.
unported: msteps_spec_err_all_traces_error — depends on spec_err_all_traces_error.
-/

/-! The outcome-tree lemmas, Rocq lines 543–986, except the omissions above.
`ErrEscape` supplies the existing instruction-path lemma `msteps_star_nil`. -/

namespace LinuxProcessSemantics.Common.FileSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.ErrEscape
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence

variable (segs : List Segment)

theorem tfo_msteps (ms ms' : machine_state) (model : Model) (U : word × Fs.Fs → Prop)
    (H : msteps segs ms ms') (Ht : to_fout segs ms' model U) :
    to_fout segs ms model U := by
  induction H with
  | mst_refl => exact Ht
  | mst_step ms ms1 ms2 Hsvc Hstep _ IH =>
    exact to_fout.tfo_step ms ms1 model U Hsvc Hstep (IH Ht)

theorem tfo_equiv (ms : machine_state) (model : Model) (U V : word × Fs.Fs → Prop)
    (Hto : to_fout segs ms model U) (HV : ∀ o, V o ↔ U o) :
    to_fout segs ms model V := by
  induction Hto generalizing V with
  | tfo_exit ms model x8 U Hsvc Hx8 HU =>
    exact to_fout.tfo_exit ms model x8 V Hsvc Hx8 (fun o => (HV o).trans (HU o))
  | tfo_step ms ms' model U Hsvc Hstep _ IH =>
    exact to_fout.tfo_step ms ms' model V Hsvc Hstep (IH V HV)
  | tfo_sys ms model x8 T U Hsvc Hne Hrec Hshape Hcont HU _ =>
    exact to_fout.tfo_sys ms model x8 T V Hsvc Hne Hrec Hshape Hcont
      (fun o => (HV o).trans (HU o))

theorem to_fout_nonempty (ms : machine_state) (model : Model) (U : word × Fs.Fs → Prop)
    (Hto : to_fout segs ms model U) : ∃ o, U o := by
  induction Hto with
  | tfo_exit ms model x8 U Hsvc Hx8 HU => exact ⟨_, (HU _).2 rfl⟩
  | tfo_step ms ms' model U Hsvc Hstep _ IH => exact IH
  | tfo_sys ms model x8 T U Hsvc Hne Hrec Hshape Hcont HU IH =>
    obtain ⟨eff, model', evs, Hspec⟩ := Hrec
    obtain ⟨o, Ho⟩ := IH eff model' evs Hspec
    exact ⟨o, (HU o).2 ⟨eff, model', evs, Hspec, Ho⟩⟩

theorem sstep_fsys_inv (ms : machine_state) (model : Model) (x8 : word)
    (evs : List event) (st : step_to) (_Hh : m_halted model = none)
    (_Hlazy : m_vm_lazy model = []) (Hsvc : ms.ms_svc_pending = some x8)
    (Hne : ¬ syscall_spec (sys_input segs ms x8) model Unmodeled)
    (Hshape : ∀ eff model' evs',
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs') →
      evs' = [] ∧ m_halted model' = none ∧ m_vm_lazy model' = [])
    (Hss : sstep segs (config.mkCfg ms model) evs st) :
    ∃ eff model', syscall_spec (sys_input segs ms x8) model (Ok eff model' []) ∧
      evs = [] ∧ st = SNext (config.mkCfg (advance_past_svc (apply_effect ms eff)) model') := by
  cases Hss with
  | sstep_instr _ _ _ _ _ hv _ => rw [Hsvc] at hv; cases hv
  | sstep_instr_fault _ _ _ hv _ => rw [Hsvc] at hv; cases hv
  | sstep_instr_unmodeled _ _ _ hv _ => rw [Hsvc] at hv; cases hv
  | sstep_syscall _ _ x eff m' m'' evs' _ hv hs _ hm =>
    rw [Hsvc] at hv
    cases hv
    obtain ⟨rfl, _, hl⟩ := Hshape eff m' _ hs
    rw [materialize_model_accesses_no_lazy _ _ hl] at hm
    cases hm
    exact ⟨eff, m', hs, rfl, rfl⟩
  | sstep_syscall_materialization_fault _ _ x eff m' evs' _ hv hs _ hm =>
    rw [Hsvc] at hv
    cases hv
    rw [materialize_model_accesses_no_lazy _ _ (Hshape eff m' evs' hs).2.2] at hm
    cases hm
  | sstep_exit _ _ x eff m' evs' code _ hv hs hh _ =>
    rw [Hsvc] at hv
    cases hv
    rw [(Hshape eff m' evs' hs).2.1] at hh
    cases hh
  | sstep_killed _ _ x eff m' evs' sig _ hv hs hk =>
    rw [Hsvc] at hv
    cases hv
    rw [m_killed_of_m_halted_none _ (Hshape eff m' evs' hs).2.1] at hk
    cases hk
  | sstep_syscall_unmodeled _ _ x _ hv hs =>
    rw [Hsvc] at hv
    cases hv
    exact False.elim (Hne hs)

def fout_post (U : word × Fs.Fs → Prop) : post :=
  fun tr o => ∃ out, U out ∧ tr = fout_trace out ∧ exits_with out.1 tr o

theorem to_fout_exec (ms : machine_state) (model : Model) (U : word × Fs.Fs → Prop)
    (Hto : to_fout segs ms model U) (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = []) : exec segs (config.mkCfg ms model) (fout_post U) := by
  induction Hto with
  | tfo_exit ms model x8 U Hsvc Hx8 HU =>
    apply exec_step_only segs _ _
      [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      (config.mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))
    · exact sstep.sstep_exit ms model x8 (mkEffect (Z_to_bv 64 0) [] []) _ [] _
        Hh Hsvc (exit_dispatch_ok _ _ Hx8) rfl (m_killed_with_halted _ _)
    · exact fun evs st hs => sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 hs
    · apply exec.exec_halt
      · rw [m_halted_with_halted]; nofun
      · exact ⟨(_, m_fs model), (HU _).2 rfl, rfl, rfl, m_killed_with_halted _ _⟩
  | tfo_step ms ms' model U Hsvc Hstep Hto IH =>
    apply exec_step_only segs _ _ [] (config.mkCfg ms' model)
    · exact sstep.sstep_instr ms model ms' model Hh Hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])
    · exact fun evs st hs => sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep hs
    · exact IH Hh Hlazy
  | tfo_sys ms model x8 T U Hsvc Hne Hrec Hshape Hcont HU IH =>
    apply exec.exec_step _ _ Hh
    · obtain ⟨eff, model', evs, Hspec⟩ := Hrec
      obtain ⟨rfl, hh, hl⟩ := Hshape eff model' evs Hspec
      exact ⟨[], _, sstep.sstep_syscall ms model x8 eff model' model' [] Hh Hsvc Hspec hh
        (materialize_model_accesses_no_lazy _ _ hl)⟩
    · intro evs hs
      obtain ⟨eff, model', _, _, habs⟩ :=
        sstep_fsys_inv segs ms model x8 evs SError Hh Hlazy Hsvc Hne Hshape hs
      cases habs
    · intro evs c' hs
      obtain ⟨eff, model', Hspec, rfl, hc⟩ :=
        sstep_fsys_inv segs ms model x8 evs (SNext c') Hh Hlazy Hsvc Hne Hshape hs
      cases hc
      obtain ⟨_, hh, hl⟩ := Hshape eff model' [] Hspec
      apply exec_conseq _ _ _ _ (IH eff model' [] Hspec hh hl)
      rintro tr o ⟨out, Hout, Heq, Hx⟩
      exact ⟨out, (HU out).2 ⟨eff, model', [], Hspec, Hout⟩, Heq, Hx⟩

theorem to_fout_star_only (ms : machine_state) (model : Model) (U : word × Fs.Fs → Prop)
    (Hto : to_fout segs ms model U) (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = []) (tr : List event) (c : config)
    (Hstar : star segs (config.mkCfg ms model) tr c) :
    ∃ o, U o ∧ is_prefix tr (fout_trace o) := by
  obtain ⟨tr', o, _, out, Hout, Heq, _⟩ := exec_realizes _ _ _
    (exec_star _ _ _ _ _ (to_fout_exec segs ms model U Hto Hh Hlazy) Hstar)
  exact ⟨out, Hout, Heq ▸ is_prefix_app tr tr'⟩

theorem to_fout_star_admits (ms : machine_state) (model : Model) (U : word × Fs.Fs → Prop)
    (Hto : to_fout segs ms model U) (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = []) (o : word × Fs.Fs) (Ho : U o) :
    ∃ c, star segs (config.mkCfg ms model) (fout_trace o) c := by
  induction Hto with
  | tfo_exit ms model x8 U Hsvc Hx8 HU =>
    obtain rfl := (HU o).1 Ho
    refine ⟨config.mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model),
      star_one segs _ _ _ ?_⟩
    exact sstep.sstep_exit ms model x8 (mkEffect (Z_to_bv 64 0) [] []) _ [] _
      Hh Hsvc (exit_dispatch_ok _ _ Hx8) rfl (m_killed_with_halted _ _)
  | tfo_step ms ms' model U Hsvc Hstep Hto IH =>
    obtain ⟨c, hs⟩ := IH Hh Hlazy Ho
    exact ⟨c, star.star_step _ [] _ _ _ (sstep.sstep_instr ms model ms' model Hh Hsvc
      (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])) hs⟩
  | tfo_sys ms model x8 T U Hsvc Hne Hrec Hshape Hcont HU IH =>
    obtain ⟨eff, model', evs, Hspec, Ht⟩ := (HU o).1 Ho
    obtain ⟨rfl, hh, hl⟩ := Hshape eff model' evs Hspec
    obtain ⟨c, hs⟩ := IH eff model' [] Hspec hh hl Ht
    exact ⟨c, star.star_step _ [] _ _ _
      (sstep.sstep_syscall ms model x8 eff model' model' [] Hh Hsvc Hspec hh
        (materialize_model_accesses_no_lazy _ _ hl)) hs⟩

theorem to_fout_progress (ms : machine_state) (model : Model) (U : word × Fs.Fs → Prop)
    (Hto : to_fout segs ms model U) (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = []) (evs : List event) (st : step_to)
    (Hss : sstep segs (config.mkCfg ms model) evs st) :
    ∃ ms' model', st = SNext (config.mkCfg ms' model') ∧
      (m_halted model' ≠ none ∨ (m_halted model' = none ∧ m_vm_lazy model' = [] ∧
        ∃ U', to_fout segs ms' model' U')) := by
  cases Hto with
  | tfo_exit ms model x8 U Hsvc Hx8 HU =>
    obtain ⟨_, rfl⟩ := sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss
    exact ⟨_, _, rfl, Or.inl (by rw [m_halted_with_halted]; nofun)⟩
  | tfo_step ms ms' model U Hsvc Hstep Hto =>
    obtain ⟨_, rfl⟩ := sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss
    exact ⟨_, _, rfl, Or.inr ⟨Hh, Hlazy, U, Hto⟩⟩
  | tfo_sys ms model x8 T U Hsvc Hne Hrec Hshape Hcont HU =>
    obtain ⟨eff, model', Hspec, _, rfl⟩ :=
      sstep_fsys_inv segs ms model x8 evs st Hh Hlazy Hsvc Hne Hshape Hss
    obtain ⟨_, hh, hl⟩ := Hshape eff model' [] Hspec
    exact ⟨_, _, rfl, Or.inr ⟨hh, hl, T eff model', Hcont eff model' [] Hspec⟩⟩

def fon_path (c : config) : Prop :=
  (m_halted c.cfg_model = none ∧ m_vm_lazy c.cfg_model = [] ∧
    ∃ U, to_fout segs c.cfg_ms c.cfg_model U) ∨ m_halted c.cfg_model ≠ none

theorem fon_path_step (c : config) (evs : List event) (c' : config)
    (Hop : fon_path segs c) (Hss : sstep segs c evs (SNext c')) : fon_path segs c' := by
  obtain ⟨ms, model⟩ := c
  rcases Hop with ⟨Hh, Hlazy, U, Hto⟩ | Hh
  · obtain ⟨ms', model', hc, hcase⟩ := to_fout_progress segs ms model U Hto Hh Hlazy evs _ Hss
    cases hc
    exact hcase.elim Or.inr Or.inl
  · exact False.elim (Hh (sstep_from_running _ _ _ _ Hss))

theorem fon_path_no_error (c : config) (evs : List event)
    (Hop : fon_path segs c) : ¬ sstep segs c evs SError := by
  intro Hss
  obtain ⟨ms, model⟩ := c
  rcases Hop with ⟨Hh, Hlazy, U, Hto⟩ | Hh
  · obtain ⟨ms', model', hc, _⟩ := to_fout_progress segs ms model U Hto Hh Hlazy evs _ Hss
    cases hc
  · exact Hh (sstep_from_running _ _ _ _ Hss)

theorem star_fon_path (c : config) (tr : List event) (c' : config)
    (Hop : fon_path segs c) (Hstar : star segs c tr c') : fon_path segs c' :=
  star_invariant segs (fon_path segs) (fon_path_step segs) c tr c' Hstar Hop

theorem to_fout_no_error (ms : machine_state) (model : Model) (U : word × Fs.Fs → Prop)
    (Hto : to_fout segs ms model U) (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = []) : ¬ reaches_error segs (config.mkCfg ms model) := by
  apply exec_no_error
  apply exec_conseq _ _ _ _ (to_fout_exec segs ms model U Hto Hh Hlazy)
  rintro tr o ⟨out, _, _, Hx⟩
  exact exits_with_never_errors _ _ _ Hx

theorem star_syscall_nil (ms : machine_state) (model : Model) (x8 : word)
    (eff : SyscallEffect) (model' : Model) (Hh : m_halted model = none)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hspec : syscall_spec (sys_input segs ms x8) model (Ok eff model' []))
    (Hh' : m_halted model' = none) (Hlazy : m_vm_lazy model' = []) :
    star segs (config.mkCfg ms model) []
      (config.mkCfg (advance_past_svc (apply_effect ms eff)) model') :=
  star_one segs _ _ _ (sstep.sstep_syscall ms model x8 eff model' model' [] Hh Hsvc Hspec Hh'
    (materialize_model_accesses_no_lazy _ _ Hlazy))

theorem reaches_error_star (c : config) (tr : List event) (c' : config)
    (Hstar : star segs c tr c') (Herr : reaches_error segs c') : reaches_error segs c := by
  obtain ⟨tr2, c2, evs, Hstar2, Hss⟩ := Herr
  exact ⟨tr ++ tr2, c2, evs, star_trans segs _ _ _ _ _ Hstar Hstar2, Hss⟩

theorem spec_err_error (ms : machine_state) (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hspec : syscall_spec (sys_input segs ms x8) model Unmodeled) :
    reaches_error segs (config.mkCfg ms model) :=
  ⟨[], _, [], star.star_refl _, sstep.sstep_syscall_unmodeled ms model x8 Hh Hsvc Hspec⟩

theorem msteps_spec_err_error (ms ms' : machine_state) (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hm : msteps segs ms ms') (Hsvc : ms'.ms_svc_pending = some x8)
    (Hspec : syscall_spec (sys_input segs ms' x8) model Unmodeled) :
    reaches_error segs (config.mkCfg ms model) :=
  reaches_error_star segs _ [] _ (msteps_star_nil segs ms ms' model Hh Hlazy Hm)
    (spec_err_error segs ms' model x8 Hh Hsvc Hspec)

end LinuxProcessSemantics.Common.FileSim
