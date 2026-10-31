import LinuxProcessSemantics.Common.FileSim.Base
import LinuxProcessSemantics.Common.FileSim.Tree
import LinuxProcessSemantics.Common.SimInv

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Run-level packaging, Rocq lines 2338–2454. `Tree` supplies the outcome
characterization; `SimInv` supplies the existing modeled-run bridge. -/

namespace LinuxProcessSemantics.Common.FileSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.Common.SimInv
open LinuxProcessSemantics.EquivalenceDefinition
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence

theorem fout_omni_run (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (U : word × Fs.Fs → Prop)
    (Hto : to_fout segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U) :
    omni_run (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp (fout_post U) :=
  to_fout_exec segs _ _ U Hto rfl rfl

theorem fout_obs_iff (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (U : word × Fs.Fs → Prop)
    (Hto : to_fout segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U) (tr : List event) :
    obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
      ∃ o, U o ∧ is_prefix tr (fout_trace o) := by
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    obtain ⟨o, Ho, Hp'⟩ := to_fout_star_only segs _ _ U Hto rfl rfl tr' c Hstar
    exact ⟨o, Ho, is_prefix_trans _ _ _ Hp Hp'⟩
  · rintro ⟨o, Ho, Hp⟩
    obtain ⟨c, Hstar⟩ := to_fout_star_admits segs _ _ U Hto rfl rfl o Ho
    exact ⟨fout_trace o, c, Hstar, Hp⟩

theorem fout_no_error_run (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (U : word × Fs.Fs → Prop)
    (Hto : to_fout segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U) :
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) :=
  to_fout_no_error segs _ _ U Hto rfl rfl

theorem fout_omni_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo) (asp abrk amb : word) (arnd : EntryDraw)
    (U : word × Fs.Fs → Prop) (inp : ProcInput)
    (Hsource : to_fout source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) U)
    (Htarget : to_fout target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) U) :
    omni_strong_equiv (Image.mkImage source_segs rpc rph) (Image.mkImage target_segs apc aph)
      (ExecEntry.mkEntry rsp rbrk rmb rrnd) (ExecEntry.mkEntry asp abrk amb arnd) inp := by
  constructor
  · apply coexec_conseq _ _ _ _ (exec_coexec _ _ _
      (fout_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource))
    rintro tr o ⟨out, _, _, Hx⟩
    exact never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)
  · apply Or.inr
    constructor
    · apply (trace_equiv_iff_omni _ _ _ _ _ _ _).1
      intro tr
      exact (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource tr).trans
        (fout_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget tr).symm
    · exact (bh_errors_iff _ _ _ _).1
        (fout_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget)

theorem fout_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (rlim : Int) (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int) (U : word × Fs.Fs → Prop) (inp : ProcInput)
    (Hsource : to_fout source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U)
    (Htarget : to_fout target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) U) :
    Equivalence.modeled (run (Image.mkImage source_segs rpc rph) rlim
      (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp) ∧
    Equivalence.equiv (run (Image.mkImage source_segs rpc rph) rlim
      (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp)
      (run (Image.mkImage target_segs apc aph) alim (ExecEntry.mkEntry asp abrk amb arnd) inp) := by
  constructor
  · exact no_error_run_modeled source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      (fout_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource)
  · apply Or.inr
    constructor
    · intro tr
      exact (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).trans
        (fout_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).symm
    · exact fout_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget

theorem spec_err_escape_equiv (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (target : behavior)
    (Hall : all_traces_error segs (init_config segs pc ph sp brk0 mb rnd lim inp)) :
    Equivalence.equiv (run (Image.mkImage segs pc ph) lim
      (ExecEntry.mkEntry sp brk0 mb rnd) inp) target :=
  Or.inl Hall

end LinuxProcessSemantics.Common.FileSim
