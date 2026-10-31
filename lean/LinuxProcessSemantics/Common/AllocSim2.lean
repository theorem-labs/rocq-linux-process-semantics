import LinuxProcessSemantics.Common.AllocSim
import LinuxProcessSemantics.Common.MmapSim
import LinuxProcessSemantics.Common.SimInv

/-! rocq-baseline: 4729ef4fb1a6de74619176699f5393f08268d5f7 -/

/-! # Common.AllocSim2 — mixed-allocator equivalence glue

PROOF-SIDE: shared proof library, not the trusted specification.
Image-independent.

Glue for the allocator-divergence examples: a SOURCE binary whose
behavior is characterized as an `AllocSim.to_outcomes` set (brk
branching) and a TARGET binary characterized as a `MmapSim.tmw`
derivation (one mmap with a failure tail and a success tail). When
the source's outcome set is exactly the two-element set
{ (bf, cf); (bs, cs) } matching the target's two tails, the two
binaries are observably equivalent: allocation emits no trace
events, so each side's trace set is the prefixes of the same two
candidate traces even though the failing/succeeding resolutions
come from different syscalls. -/

namespace LinuxProcessSemantics.Common.AllocSim2

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Common.SimInv
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.AllocSim
open LinuxProcessSemantics.Common.MmapSim

/-- The two-element outcome set of a fail/succeed allocator run. -/
def two_outcomes (bf : List (List byte)) (cf : word)
    (bs : List (List byte)) (cs : word) : (List (List byte) × word) → Prop :=
  fun o => o = (bf, cf) ∨ o = (bs, cs)

/-- `Equivalence.equiv` for a brk-allocating source whose outcome set is
`two_outcomes bf cf bs cs` and an mmap-allocating target with the
same failure tail `(bf, cf)` and success tail `(bs, cs)`. -/
theorem alloc_mmap_strong_equiv (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo) (asp abrk amb : word)
    (arnd : EntryDraw) (alim : Int)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word) (inp : ProcInput)
    (Hsource : to_outcomes source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp)
      (two_outcomes bf cf bs cs))
    (Htarget : tmw target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    modeled (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp)
    ∧ equiv (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp)
            (run (Image.mkImage target_segs apc aph) alim (ExecEntry.mkEntry asp abrk amb arnd)
              inp) := by
  constructor
  · apply no_error_run_modeled
    exact alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      (two_outcomes bf cf bs cs) Hsource
  · refine Or.inr ⟨?_, ?_⟩
    · intro tr
      change obs_trace source_segs
          (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) tr ↔
        obs_trace target_segs (init_config target_segs apc aph asp abrk amb arnd alim inp) tr
      rw [alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp
            (two_outcomes bf cf bs cs) Hsource tr,
          mmap_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp
            bf cf bs cs Htarget Hbf Hbs tr]
      unfold two_traces two_outcomes outcome_trace
      constructor
      · rintro ⟨o, (rfl | rfl), Hp⟩
        · exact Or.inl Hp
        · exact Or.inr Hp
      · rintro (Hp | Hp)
        · exact ⟨(bf, cf), Or.inl rfl, Hp⟩
        · exact ⟨(bs, cs), Or.inr rfl, Hp⟩
    · exact mmap_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp
        bf cf bs cs Htarget Hbf Hbs

/-- The omni equivalence of a brk-branching source against a mmap-branching
target with the same two outcomes, at the two role budgets. -/
theorem alloc_mmap_omni_strong_equiv (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo) (asp abrk amb : word)
    (arnd : EntryDraw)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word) (inp : ProcInput)
    (Hsource : to_outcomes source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (two_outcomes bf cf bs cs))
    (Htarget : tmw target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    omni_strong_equiv (Image.mkImage source_segs rpc rph) (Image.mkImage target_segs apc aph)
      (ExecEntry.mkEntry rsp rbrk rmb rrnd) (ExecEntry.mkEntry asp abrk amb arnd) inp := by
  apply (strong_equiv_iff _ _ _ _ _).mp
  exact alloc_mmap_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit
    target_segs apc aph asp abrk amb arnd target_alloc_limit bf cf bs cs inp
    Hsource Htarget Hbf Hbs

end LinuxProcessSemantics.Common.AllocSim2
