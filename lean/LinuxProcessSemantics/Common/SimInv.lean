import LinuxProcessSemantics.LinuxProcessSem.OmniRun
import LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence

/-! # Common.SimInv — the generic path-invariant / no-error combinator

Ported from `theories/Common/SimInv.v` at
2cde689f94c086b868999970834b76a25616b94a: the part of it `cat1024_ns`'s
`Proof.v` reaches (`Print All Dependencies` of its
`strong_universal`, ticket E-proof-library), which is `inv_coexec` alone,
with the Rocq statement.

A sim file whose run need not terminate closes its safety obligation this
way: it defines a configuration invariant, proves that it is preserved by
every `sstep` to an `SNext` successor, and proves that it excludes the
`SError` transition.  `inv_coexec` turns those two facts into the omni
safety judgment `OmniRun.coexec … never_errors`.  In this port
`StreamSim` (its `sinv`) and `DrainSim` (its `dinv`) do so: `ExitSim`
closes its obligation from its terminating derivation (`exit_no_error_te`),
and `CatSim`'s and `WallSim`'s whole-run safety theorems
(`cat_no_error_run_te`, `wall_no_error_run`) do not use `inv_coexec`.

Left unported by that ticket: the `star`-lifting pair `star_inv` and
`inv_no_reaches_error`, the bridges `no_error_run_corun` and
`no_error_run_modeled`, and the ABI-boundary normalization tactics
`norm_fd32` and `fd32_ok` (Ltac: proof automation, not constants).
cat1024_ns reaches none of them.  The four lemmas are ported since, in the
section appended at the end of this file.

Structural proof divergence: Rocq proves `inv_coexec` by `cofix`; Lean's
`coexec` is a `coinductive` predicate (`LinuxProcessSem/OmniRun.lean`), so the
proof is an application of its coinduction principle `coexec.coinduct` with
the invariant (and a postcondition implied by `never_errors`) as the
coinduction hypothesis, the pattern `OmniRun.no_error_coexec` follows. -/

namespace LinuxProcessSemantics.Common.SimInv

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun

/-- The same invariant delivers the omni safety judgment directly: an
invariant that excludes the error transition is a proof of
`OmniRun.coexec … never_errors`, by coinduction along the preservation
clause — no `Run.star` in sight. -/
theorem inv_coexec (segs : List Segment) (Inv : config → Prop)
    (Hstep : ∀ c evs c', Inv c → sstep segs c evs (SNext c') → Inv c')
    (Hnoerr : ∀ c evs, Inv c → ¬ sstep segs c evs SError) :
    ∀ c, Inv c → coexec segs c never_errors := by
  intro c HInv
  apply coexec.coinduct segs
    (fun c Q => Inv c ∧ ∀ tr o, never_errors tr o → Q tr o)
  · intro c Q h
    obtain ⟨hinv, hq⟩ := h
    cases hh : m_halted c.cfg_model with
    | some code =>
      refine Or.inl ⟨?_, hq [] (OHalt c) (fun h => h)⟩
      intro hn
      cases hn
    | none =>
      refine Or.inr ⟨rfl, ?_, ?_⟩
      · intro evs hs
        exact False.elim (Hnoerr c evs hinv hs)
      · intro evs c' hs
        exact ⟨Hstep c evs c' hinv hs, fun tr o hn => hq (evs ++ tr) o hn⟩
  · exact ⟨HInv, fun _ _ h => h⟩

/-! ## Additions for ticket E-proof-library-2c: the `star` lifting and the no-error bridges

Ported from the same Rocq file at the baseline the header names, with the
Rocq statements: the four lemmas the header says ticket E-proof-library left
out.  `no_error_run_modeled` concludes
`Equivalence.modeled` through `OmniEquivalence.modeled_iff`, which is why
this file now imports `EquivalenceDefinition.OmniEquivalence` (Rocq's file
imports `Equivalence` and `OmniEquivalence`).  The image and entry
constructors are `Image.mkImage` and `ExecEntry.mkEntry`, and Rocq's
`pc : N` and `lim : Z` are a `Nat` and an `Int`. -/

open LinuxProcessSemantics.LinuxProcessSem.StackLayout

/-- `Inv` is preserved along any `star` run, given that it is preserved by
every single `sstep` to a `SNext` successor.  This is `Run.star_invariant`
with the invariant hypothesis before the run, as Rocq orders them. -/
theorem star_inv (segs : List Segment) (Inv : config → Prop)
    (Hstep : ∀ c evs c', Inv c → sstep segs c evs (SNext c') → Inv c') :
    ∀ c tr c', Inv c → star segs c tr c' → Inv c' :=
  fun c tr c' HInv Hstar => star_invariant segs Inv Hstep c tr c' Hstar HInv

/-- If `Inv` is preserved by `sstep`-to-`SNext` and excludes the `SError`
transition, then any configuration satisfying `Inv` never reaches the
explicit error step. -/
theorem inv_no_reaches_error (segs : List Segment) (Inv : config → Prop)
    (Hstep : ∀ c evs c', Inv c → sstep segs c evs (SNext c') → Inv c')
    (Hnoerr : ∀ c evs, Inv c → ¬ sstep segs c evs SError) :
    ∀ c, Inv c → ¬ reaches_error segs c := by
  rintro c HInv ⟨tr, c', evs, Hstar, Hss⟩
  exact Hnoerr c' evs (star_inv segs Inv Hstep c tr c' HInv Hstar) Hss

/-- The bridge from the library's `¬ reaches_error` shape to the omni
safety judgment `omni_corun … never_errors`, for combinators that already
have the negative fact in hand. -/
theorem no_error_run_corun (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (H : ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp)) :
    omni_corun (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp
      never_errors :=
  no_error_coexec segs _ H

/-- Turn a source `¬ reaches_error` proof into the source-coverage conjunct
of `Equivalence.strong_equiv`: the run never errors at all, so a fortiori it
never reaches a configuration the model declined to interpret.  The
combinators whose source is EXPECTED to error need a direct proof instead,
as `ErrEscape.err_escape_modeled` gives for a deterministic `MachineFault`. -/
theorem no_error_run_modeled (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (H : ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp)) :
    EquivalenceDefinition.Equivalence.modeled
      (run (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp) :=
  (EquivalenceDefinition.OmniEquivalence.modeled_iff _ _ _ _).2
    (coexec_conseq segs _ _ _ (no_error_run_corun segs pc ph sp brk0 mb rnd lim inp H)
      (never_errors_covered segs))

end LinuxProcessSemantics.Common.SimInv
