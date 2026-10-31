import LinuxProcessSemantics.EquivalenceDefinition.MustExit
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Budgets

/-! rocq-baseline: 1807c1e25ce12708f5cc85213f2df4bf03d978da
unported: codes -- the one member of the ALLOWED_EXITS module type and of its AnyExit instance; the allowed set is the explicit `codes : List word` parameter of each SPEC_HALTS_ALLOWED structure below, and AnyExit's value is `byte_codes`. -/

/-! Rocq module surfaces excluded by the parity checker

The scanner tracks term definitions, not these module declarations or the
lemmas about their members.
unported: ALLOWED_EXITS -- a module type; the allowed set is the explicit `codes : List word` parameter of each SPEC_HALTS_ALLOWED structure below, as Equivalence/Base.lean's SPEC takes its images.
unported: AnyExit -- an instance module of ALLOWED_EXITS; its one member is `byte_codes`, which a task passes as the `codes` argument.
unported: any_exit_covers -- states `any_exit_covers_masked_status` at `AnyExit.codes`, which is `byte_codes`; with no AnyExit module the two statements are one. -/

/-! # EquivalenceDefinition.HaltsAllowed — one binary halts with an allowed status

Mirrors `theories/EquivalenceDefinition/HaltsAllowed.v`.

TRUST BOUNDARY: this file is part of the trusted specification.

For one binary, every trace the spec admits for it, at every entry
`Run.valid_entry` allows and on every input `Run.valid_input` allows,
halts through the `exit_group` path with a status in a set the task
declares: `MustExit.must_exit_in` quantified over the entries and the
inputs.  Non-termination, a stuck execution, the error transition (and
so anything unmodeled) and death by signal are what it excludes; the
argument for each, and for having no abort stance, is on the Rocq file.

THE LEAN SHAPE OF THE SEALED SURFACE.  Rocq states the task's obligation
as module types over functor arguments (`ALLOWED_EXITS`, `SPURIOUS_CFG`,
`BUDGETS`, `MemImage`).  Lean has no module types, so each
`SPEC_HALTS_ALLOWED*` here is a `Prop` structure over the same data
passed explicitly, the way `Equivalence/Base.lean`'s `SPEC` takes its
two images: the allowed set is a `List word`, the configuration a
`Run.SpuriousCfg`, and the budget the `Int` Rocq reads off
`BUDGETS.lim_source` (`Equivalence/Budgets.lean` registers `BUDGETS`
unported).  That costs one property: Rocq takes the whole `BUDGETS`
module so that a one-image statement is pinned to the same budget pair,
headroom included, as the two-image statement beside it.  A bare `Int`
accepts any limit, so nothing here ties it to the pair a two-image
statement uses; that link returns when `BUDGETS` is ported.

THE MASK IS THE KERNEL'S.  In Linux v6.18.46 (commit
1f99e9ab748fc5c32120de9c4eca31abfe54a4d5), kernel/exit.c's
`SYSCALL_DEFINE1(exit, int, error_code)` calls
`do_exit((error_code&0xff)<<8)` and
`SYSCALL_DEFINE1(exit_group, int, error_code)` calls
`do_group_exit((error_code & 0xff) << 8)`, so the seven high bytes of the
argument are discarded before any status exists.  That is why
`byte_codes` is the widest set a task can need
(`any_exit_covers_masked_status`). -/

namespace LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence

/-! ## The three readings of the statement -/

/-- The unconfigured reading: every execution the unfiltered step
relation admits, at the shipped source budget. -/
def halts_allowed_T (S : List word) (img : Image) : Prop :=
  ∀ en inp,
    valid_entry img en inp →
    valid_input inp →
    must_exit_in S img source_alloc_limit en inp

/-- The configured reading, pinned to a spurious-failure configuration
the way `Equivalence.strong_universal_T_scfg` is. -/
def halts_allowed_T_scfg (cfg : SpuriousCfg) (S : List word) (img : Image) : Prop :=
  ∀ en inp,
    valid_entry img en inp →
    valid_input inp →
    must_exit_in_scfg cfg S img source_alloc_limit en inp

/-- The budget reading, for one image: one budget and the configured
budget premise `Equivalence.source_within_budget_scfg`. -/
def halts_allowed_T_scfg_budgets (cfg : SpuriousCfg) (lim : Int)
    (S : List word) (img : Image) : Prop :=
  ∀ en inp,
    valid_entry img en inp →
    valid_input inp →
    source_within_budget_scfg cfg lim img en inp →
    must_exit_in_scfg cfg S img lim en inp

/-! ## How the three readings relate -/

theorem halts_allowed_T_scfg_may_fail (S : List word) (img : Image) :
    halts_allowed_T_scfg may_fail_cfg S img ↔ halts_allowed_T S img :=
  ⟨fun h en inp hen hinp => (must_exit_in_scfg_may_fail _ _ _ _ _).1 (h en inp hen hinp),
   fun h en inp hen hinp => (must_exit_in_scfg_may_fail _ _ _ _ _).2 (h en inp hen hinp)⟩

theorem halts_allowed_T_scfg_mono (cfg1 cfg2 : SpuriousCfg) (S : List word) (img : Image) :
    cfg_le cfg1 cfg2 →
    (∀ en inp, valid_entry img en inp → valid_input inp →
      run_decided cfg1 img source_alloc_limit en inp) →
    halts_allowed_T_scfg cfg2 S img →
    halts_allowed_T_scfg cfg1 S img :=
  fun hle hdec h en inp hen hinp =>
    must_exit_in_scfg_mono _ _ _ _ _ _ _ hle (hdec en inp hen hinp) (h en inp hen hinp)

theorem halts_allowed_T_scfg_budgets_of_scfg (cfg : SpuriousCfg) (S : List word) (img : Image) :
    halts_allowed_T_scfg cfg S img →
    halts_allowed_T_scfg_budgets cfg source_alloc_limit S img :=
  fun h en inp hen hinp _ => h en inp hen hinp

theorem halts_allowed_T_mono (S1 S2 : List word) (img : Image) :
    (∀ code, code ∈ S1 → code ∈ S2) →
    halts_allowed_T S1 img →
    halts_allowed_T S2 img :=
  fun hsub h en inp hen hinp => must_exit_in_mono _ _ _ _ _ _ hsub (h en inp hen hinp)

theorem halts_allowed_T_scfg_mono_set (cfg : SpuriousCfg) (S1 S2 : List word) (img : Image) :
    (∀ code, code ∈ S1 → code ∈ S2) →
    halts_allowed_T_scfg cfg S1 img →
    halts_allowed_T_scfg cfg S2 img :=
  fun hsub h en inp hen hinp =>
    must_exit_in_scfg_mono_set _ _ _ _ _ _ _ hsub (h en inp hen hinp)

theorem halts_allowed_T_of_must_exit_with (S : List word) (code : word) (img : Image) :
    (∀ en inp, valid_entry img en inp → valid_input inp →
      must_exit_with code img source_alloc_limit en inp) →
    code ∈ S →
    halts_allowed_T S img :=
  fun h hin en inp hen hinp => must_exit_with_in _ _ _ _ _ _ (h en inp hen hinp) hin

/-! ## What the statement buys, and how it is refuted -/

theorem halts_allowed_T_no_error (S : List word) (img : Image) (en : ExecEntry) (inp : ProcInput) :
    halts_allowed_T S img →
    valid_entry img en inp →
    valid_input inp →
    ¬ (run img source_alloc_limit en inp).bh_errors :=
  fun h hen hinp => must_exit_in_no_error _ _ _ _ _ (h en inp hen hinp)

theorem halts_allowed_T_modeled (S : List word) (img : Image) (en : ExecEntry) (inp : ProcInput) :
    halts_allowed_T S img →
    valid_entry img en inp →
    valid_input inp →
    ¬ (run img source_alloc_limit en inp).bh_unmodeled :=
  fun h hen hinp => must_exit_in_modeled _ _ _ _ _ (h en inp hen hinp)

/-- The guard: whatever satisfies `halts_allowed_T` emits an `ExitEv`
whose status is in `S`. -/
theorem halts_allowed_T_realizes (S : List word) (img : Image) (en : ExecEntry) (inp : ProcInput) :
    halts_allowed_T S img →
    valid_entry img en inp →
    valid_input inp →
    ∃ tr code fs,
      code ∈ S ∧ (run img source_alloc_limit en inp).bh_traces (tr ++ [ExitEv code fs]) :=
  fun h hen hinp => must_exit_in_realizes _ _ _ _ _ (h en inp hen hinp)

/-- NEGATIVE, the error route. -/
theorem halts_allowed_T_refuted_by_error (S : List word) (img : Image) (en : ExecEntry) (inp : ProcInput) :
    valid_entry img en inp →
    valid_input inp →
    (run img source_alloc_limit en inp).bh_errors →
    ¬ halts_allowed_T S img :=
  fun hen hinp herr h => must_exit_in_refuted_by_error _ _ _ _ _ herr (h en inp hen hinp)

/-- NEGATIVE, the signal route. -/
theorem halts_allowed_T_refuted_by_kill (S : List word) (img : Image) (en : ExecEntry) (inp : ProcInput) :
    valid_entry img en inp →
    valid_input inp →
    run_reaches_killed img source_alloc_limit en inp →
    ¬ halts_allowed_T S img :=
  fun hen hinp hk h => must_exit_in_refuted_by_kill _ _ _ _ _ hk (h en inp hen hinp)

/-- NEGATIVE, the wrong-status route: a valid pair whose run reaches a
configuration halted with a status outside the set. -/
theorem halts_allowed_T_refuted_by_wrong_status (S : List word) (img : Image) (en : ExecEntry)
    (inp : ProcInput) (tr : List event) (c' : config) (code : word) :
    valid_entry img en inp →
    valid_input inp →
    star img.img_segments
      (init_config img.img_segments img.img_init_pc img.img_phdrs
        en.en_sp en.en_brk en.en_mmap_base en.en_draw source_alloc_limit inp) tr c' →
    m_halted c'.cfg_model = some code →
    code ∉ S →
    ¬ halts_allowed_T S img :=
  fun hen hinp hstar hh hnin h =>
    must_exit_in_at_wrong_code _ _ _ _ hh hnin
      (must_exit_in_at_star _ _ _ _ _ (h en inp hen hinp) hstar)

/-! ## The allowed set, decided by computation -/

def status_allowed (S : List word) (code : word) : Bool :=
  S.any (fun c => bv_eqb c code)

theorem status_allowed_In (S : List word) (code : word) :
    status_allowed S code = true → code ∈ S := by
  intro h
  obtain ⟨c, hin, heq⟩ := List.any_eq_true.1 h
  rw [← (bv_eqb_eq c code).1 heq]
  exact hin

theorem In_status_allowed (S : List word) (code : word) :
    code ∈ S → status_allowed S code = true :=
  fun h => List.any_eq_true.2 ⟨code, h, (bv_eqb_eq code code).2 rfl⟩

/-- Every status in `0 .. 255`, as words. -/
def byte_codes : List word :=
  (List.range 256).map (fun n : Nat => Z_to_bv 64 (n : Int))

theorem in_byte_codes (z : Int) :
    0 ≤ z ∧ z < 256 → Z_to_bv 64 z ∈ byte_codes := by
  intro hz
  refine List.mem_map.2 ⟨z.toNat, List.mem_range.2 (by omega), ?_⟩
  rw [Int.toNat_of_nonneg hz.1]

/-- The status `Sys.Kernel.Exit.exit_spec` stores is the low byte of the
argument, and the low byte of anything is a byte. -/
theorem bv_and_255_range (a : word) :
    0 ≤ bv_unsigned (bv_and a (Z_to_bv 64 255)) ∧ bv_unsigned (bv_and a (Z_to_bv 64 255)) < 256 := by
  have hle : (a &&& Z_to_bv 64 255).toNat ≤ 255 := by
    rw [BitVec.toNat_and]
    exact Nat.le_trans Nat.and_le_right (by decide)
  unfold bv_unsigned bv_and
  omega

/-- The coverage claim: every value the low-byte mask can produce is in
`byte_codes`. -/
theorem any_exit_covers_masked_status (a : word) :
    bv_and a (Z_to_bv 64 255) ∈ byte_codes := by
  have h := in_byte_codes _ (bv_and_255_range a)
  have hround : Z_to_bv 64 (bv_unsigned (bv_and a (Z_to_bv 64 255))) = bv_and a (Z_to_bv 64 255) := by
    unfold bv_unsigned Z_to_bv
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hround] at h
  exact h

/-! ## The sealed surfaces -/

/-- The unconfigured surface: one image and an allowed set beside it. -/
structure SPEC_HALTS_ALLOWED (codes : List word) (target : Image) : Prop where
  halts_allowed : halts_allowed_T codes target

/-- The configured surface. -/
structure SPEC_HALTS_ALLOWED_SCFG (cfg : SpuriousCfg) (codes : List word) (target : Image) : Prop where
  halts_allowed : halts_allowed_T_scfg cfg codes target

/-- The configured, budget-abstracted surface; `lim_source` is the
member Rocq reads off its `BUDGETS` argument. -/
structure SPEC_HALTS_ALLOWED_SCFG_BUDGETS (cfg : SpuriousCfg) (lim_source : Int)
    (codes : List word) (target : Image) : Prop where
  halts_allowed : halts_allowed_T_scfg_budgets cfg lim_source codes target

end LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed
