import LinuxProcessSemantics.LinuxProcessSem.Run
import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.DPath
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Sys
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mmap
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Run
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Mm.Mmap
import LinuxProcessSemantics.LinuxProcessSem.Checks.Examples

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.SpuriousCfg — the forced-only filter, on cases chosen by hand

Mirrors parts 1 to 6 of `theories/LinuxProcessSem/Checks/SpuriousCfg.v`:
the table, which families a configuration turns off, the three families
the filter is exercised on — `getcwd` (fs, forced by no model state),
`setsid` (cred, forced by state) and anonymous `mmap` (alloc, forced by
the budget, and by the argument gate) — and the two run-level witnesses
of part 6, stated over `MustExit.must_exit_with_scfg`.

Not part of the trusted specification: this file is QA on
`Run.SpuriousCfg`, `Run.spurious_refusal_cfg` and `Run.sstep_cfg`, written
to be READ.  Every case here is one the conformance harness cannot reach,
for the reason the Rocq header gives: the harness folds the checker over
what the kernel DID, and the filter is a statement about what the kernel
COULD HAVE DONE instead — whether a refusal was avoidable — which is not an
observation of any one run.

What each family pins:

- fs, forced by no model state: `getcwd`'s -ENOMEM is spurious under
  forced-only and kept under may-fail; its -ERANGE, the answer the state
  determines, is kept under both.  At the STEP level this is the subset
  lemma's negative twin — `Run.sstep` admits the -ENOMEM step and
  `Run.sstep_cfg Run.forced_only_cfg` refuses it — with the -ERANGE step
  admitted on both sides as the positive twin.  Its -ENOENT and
  -ENAMETOOLONG are spurious under forced-only too, although Linux gives
  the first in a removed working directory and the second in one whose
  path is `PATH_MAX` bytes or longer, neither of which the model tracks
  (`getcwd_enoent_enametoolong_spurious_under_forced_only`).
- cred, keyed on state: `setsid`'s -EPERM is spurious before a success and
  FORCED after one, because `Sys.Kernel.Sys.setsid_spec` answers it
  deterministically once `State.m_setsid_succeeded` is set.  Spurious
  before one is the spec's reading, not Linux's: a caller that leads a
  session, or its own process group, gets -EPERM on its first call, and
  the model tracks neither (`setsid_eperm_spurious_before_success`).
- alloc, keyed on the budget: an anonymous `mmap` within budget has its
  -ENOMEM removed; one beyond the budget keeps it where the grant's
  `choose` has no witness and nothing else the spec admits there is not a
  refusal.  An occupied MAP_FIXED_NOREPLACE range is not keyed on the
  budget: -EEXIST stands beside its -ENOMEM, and `refusal_b` does not
  count -EEXIST as a refusal, so the filter removes that -ENOMEM on any
  budget, although a supported kernel can be forced to give it: the
  address search's length test (`generic_get_unmapped_area`,
  mm/mmap.c:697-698, Linux v6.18.46) answers -ENOMEM before the -EEXIST
  (:410-413) on requests and floors that depend on the kernel
  (bugs/mmap-fixed-misaligned-refuses-older-riscv-enomem.md).  Over bytes
  the ledger alone holds, a
  same-page brk grow in a page no VMA backs
  (bugs/brk-same-page-grow-ledgers-bytes-no-vma-backs.md),
  `find_vma_intersection` finds nothing, and `__mmap_prepare`
  (mm/vma.c:2418-2429, Linux v6.18.46) refuses for want of budget with
  -ENOMEM, at the address-space limit or at the commit charge.
  The filter removes that answer too, leaving an -EEXIST no supported
  implementation gives there: one more place of the kind `Run.lean`'s
  exactness paragraph describes
  (`mmap_noreplace_over_unbacked_brk_bytes_enomem_is_filtered`).  And an
  -ENOMEM the ARGUMENT gate
  determines is kept although it is in `Sys.Mm.Mmap.mmap_errnos`: the
  filter does not remove an answer the state determines, whatever the
  list says, as long as the spec admits no answer beside it that is not a
  refusal.  `Checks/Cases/Run.lean`, not this file, pins the filter on
  `brk`, which refuses by value and which Rocq's file does not exercise.
- the table itself: sorted, and every number in it dispatches.

The fs and cred bullets, and in the alloc bullet the address search's
-ENOMEM over an occupied range and the bytes the ledger alone holds,
name answers a supported kernel is forced to give that the filter
removes, because the spec admits an answer that is not a refusal beside
each: the filter is exact against the spec, not against Linux.
The exactness paragraph of `Run.lean`'s spurious-failure section says
what a forced-only statement therefore assumes, and names some of the
places; `Checks/Cases/Run.lean` pins two more, `dup`'s -EMFILE at the
soft RLIMIT_NOFILE (`dup_emfile_at_the_soft_limit_is_filtered`) and
`brk`'s old break on a shrink over nothing mapped
(`brk_shrink_over_nothing_mapped_is_filtered`).

An `mmap` fixture the budget mark's pins already use is not restated
here, and the `open` lines below name its file; `mmap_overflow_i`, the
Rocq file's own fixture, is defined in `Checks/Cases/Run.lean`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.SpuriousCfg

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Fs.DPath (getcwd_arm)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Kernel.Sys (setsid_arm)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.Mm.Mmap (mmap_arm)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.DPath (getcwd_spec getcwd_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sys (setsid_spec)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap (mmap_spec mmap_fd_none)
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs (check_syscall check_syscall_sound_ok)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.DPath (getcwd_size0_iff)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Sys
  (setsid_first_call_may_answer_one setsid_after_a_success_is_eperm)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mmap
  (fixed_overflowing_len_is_enomem spent_budget_model noreplace_over_live_on_a_spent_budget_iff
   noreplace_over_live_iff)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Run
  (mmap_in mmap_overflow_i mmap_noreplace_in)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Mm.Mmap
  (mmap_within_budget_grants brk_unbacked_ledger)
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.EquivalenceDefinition.Classifier (verdict_accept)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples

/-! ## Part 1 — the table -/

/-- Rocq's `strictly_ascending`, with the previous element carried as an
argument: the as-pattern Rocq recurses through (`a :: ((b :: _) as r)`)
makes Lean fall back to well-founded recursion, which `decide` failed to
unfold when this file was written, and this form recurses structurally on
the list. -/
def ascending_after : Int → List Int → Bool
  | _, [] => true
  | a, b :: r => decide (a < b) && ascending_after b r

def strictly_ascending : List Int → Bool
  | [] => true
  | a :: r => ascending_after a r

/-- Sorted by number, like `Sys.SyscallTable.spec_table`, and so with no
number twice — the property `Run.lookup_injected`'s first-match lookup
needs to be unambiguous. -/
theorem injected_table_sorted :
    strictly_ascending (injected_table.map InjectedArm.ia_no) = true := by
  decide

/-- Every injecting arm names a syscall the dispatcher answers: a number
here with no arm in `Sys.SyscallTable.spec_table` would be a filter on
nothing. -/
theorem injected_table_dispatches :
    injected_table.all
      (fun a => (arm_numbers spec_table).any (fun n => decide (a.ia_no = n))) = true := by
  decide

/-- An effect that answers errno `e` and does nothing else. -/
def errno_eff (e : Int) : SyscallEffect := mkEffect (errno_ret e) [] []

/-- The model every check below starts from: the demo process with an
empty file system and end of input. -/
def m0 : Model := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)

/-! ## Part 2 — which families a configuration turns off -/

/-- A machine state at a `getcwd` ecall: syscall number 17 pending, every
register 0 — so `size` is 0, inside the band `Sys.Fs.DPath.getcwd_spec`
answers — and no memory at all, which that spec never reads. -/
def getcwd_ms : machine_state :=
  { ms_regs := bvmap_empty, ms_fregs := bvmap_empty,
    ms_pc_val := Z_to_bv 64 0x100,
    ms_svc_pending := some (Z_to_bv 64 17),
    ms_resv := none, ms_fcsr := Z_to_bv 32 0,
    ms_mem := fun _ => none, ms_rom := fun _ => none }

def getcwd_i : SyscallInput := sys_input [] getcwd_ms (Z_to_bv 64 17)

theorem getcwd_off_under_forced_only :
    injected_family_off forced_only_cfg getcwd_i = true := by
  decide

theorem getcwd_on_under_may_fail :
    injected_family_off may_fail_cfg getcwd_i = false := by
  decide

/-- Issue #570's switch touches the allocation family and nothing else. -/
theorem getcwd_on_under_alloc_only :
    injected_family_off (alloc_only_cfg false) getcwd_i = false := by
  decide

theorem mmap_off_under_alloc_only :
    injected_family_off (alloc_only_cfg false) (mmap_in 4096) = true := by
  decide

/-- A syscall with no injecting arm belongs to no family, whatever the
configuration: `exit` is never filtered. -/
theorem exit_has_no_family (cfg : SpuriousCfg) :
    injected_family_off cfg
      (SyscallInput.mkInput 93 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) = false :=
  rfl

/-! ## Part 3 — fs: `getcwd`, forced by no model state -/

theorem getcwd_dispatch (m : Model) (o : outcome SyscallEffect) :
    syscall_spec getcwd_i m o ↔ getcwd_spec (in_arg getcwd_i 1) getcwd_i m o := by
  unfold syscall_spec
  exact dispatch_arm spec_table getcwd_i m o getcwd_arm rfl

theorem getcwd_size_in_band : decide (1 < bv_unsigned (in_arg getcwd_i 1)) = false := by
  decide

/-- Lean-only: the size this ecall hands `getcwd`, register a1 of
`getcwd_ms`, is 0.  `getcwd_admits` and `getcwd_only` rewrite with it into
`Checks/Cases/Fs/DPath.lean`'s `getcwd_size0_iff`, where Rocq's rewrite
with `getcwd_size_in_band`. -/
theorem getcwd_size_zero : in_arg getcwd_i 1 = 0 := by
  decide

/-- Every answer `getcwd` admits here: -ERANGE, or one of the injected
three; the model is untouched and nothing is emitted. -/
theorem getcwd_admits (m : Model) (e : Int) :
    e ∈ ERANGE :: getcwd_errnos → syscall_spec getcwd_i m (Ok (errno_eff e) m []) := by
  intro hin
  rw [getcwd_dispatch, getcwd_size_zero, getcwd_size0_iff]
  simp only [getcwd_errnos, List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl | rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact Or.inl (Or.inr (Or.inr rfl))

theorem getcwd_only (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event) :
    syscall_spec getcwd_i m (Ok eff m' evs) →
    m' = m ∧ evs = [] ∧ ∃ e, e ∈ ERANGE :: getcwd_errnos ∧ eff = errno_eff e := by
  intro h
  rw [getcwd_dispatch, getcwd_size_zero, getcwd_size0_iff] at h
  rcases h with (h | h | h) | h
  · cases h
    exact ⟨rfl, rfl, ENOMEM, by decide, rfl⟩
  · cases h
    exact ⟨rfl, rfl, ENOENT, by decide, rfl⟩
  · cases h
    exact ⟨rfl, rfl, ENAMETOOLONG, by decide, rfl⟩
  · cases h
    exact ⟨rfl, rfl, ERANGE, by decide, rfl⟩

/-- The -ENOMEM is spurious under forced-only: -ERANGE was available. -/
theorem getcwd_enomem_spurious_under_forced_only :
    spurious_refusal_cfg forced_only_cfg getcwd_i m0 (errno_eff ENOMEM) :=
  ⟨getcwd_off_under_forced_only, by decide, errno_eff ERANGE, m0, [],
   getcwd_admits m0 ERANGE (by decide), by decide⟩

/-- Lean-only.  So are the -ENOENT and the -ENAMETOOLONG, for the same
reason, and that is exact against the spec, not against Linux:
`SYSCALL_DEFINE2(getcwd)` (fs/d_path.c:412-448, Linux v6.18.46) answers
-ENOENT when its `d_unlinked(pwd.dentry)` test (:424-426) finds the
working directory removed, and -ENAMETOOLONG when the path it assembles
overflows (:436-438), both before its size comparison (:439-440); there
it answers one of the two, or -ENOMEM if it cannot allocate its page
(:416-419), and not -ERANGE.  The model has no working directory, so this
is one of the places the exactness paragraph of `Run.lean`'s
spurious-failure section names, where the filter removes an answer Linux
is forced to give. -/
theorem getcwd_enoent_enametoolong_spurious_under_forced_only :
    spurious_refusal_cfg forced_only_cfg getcwd_i m0 (errno_eff ENOENT)
    ∧ spurious_refusal_cfg forced_only_cfg getcwd_i m0 (errno_eff ENAMETOOLONG) :=
  ⟨⟨getcwd_off_under_forced_only, by decide, errno_eff ERANGE, m0, [],
    getcwd_admits m0 ERANGE (by decide), by decide⟩,
   ⟨getcwd_off_under_forced_only, by decide, errno_eff ERANGE, m0, [],
    getcwd_admits m0 ERANGE (by decide), by decide⟩⟩

/-- …and kept under may-fail, and under a configuration that turns only the
allocation family off. -/
theorem getcwd_enomem_kept_under_may_fail :
    ¬ spurious_refusal_cfg may_fail_cfg getcwd_i m0 (errno_eff ENOMEM) :=
  spurious_refusal_may_fail _ _ _

theorem getcwd_enomem_kept_under_alloc_only :
    ¬ spurious_refusal_cfg (alloc_only_cfg false) getcwd_i m0 (errno_eff ENOMEM) :=
  spurious_refusal_family_on _ _ _ _ getcwd_on_under_alloc_only

/-- The answer the state determines is never spurious. -/
theorem getcwd_erange_kept_under_forced_only :
    ¬ spurious_refusal_cfg forced_only_cfg getcwd_i m0 (errno_eff ERANGE) :=
  spurious_refusal_not_refusal _ _ _ _ (by decide)

/-- The filter's question is answered here, in the affirmative. -/
theorem getcwd_decided : refusal_decided forced_only_cfg getcwd_i m0 :=
  fun _ => Or.inl ⟨errno_eff ERANGE, m0, [], getcwd_admits m0 ERANGE (by decide), by decide⟩

/-! ### The step level: the subset lemma's negative twin -/

theorem getcwd_step_from (e : Int) :
    e ∈ ERANGE :: getcwd_errnos →
    sstep [] (config.mkCfg getcwd_ms m0) []
      (SNext (config.mkCfg (advance_past_svc (apply_effect getcwd_ms (errno_eff e))) m0)) :=
  fun hin =>
    sstep.sstep_syscall getcwd_ms m0 (Z_to_bv 64 17) (errno_eff e) m0 m0 []
      rfl rfl (getcwd_admits m0 e hin) rfl (materialize_model_accesses_no_lazy _ _ rfl)

/-- `Run.sstep` admits the -ENOMEM step. -/
theorem getcwd_enomem_step_admitted :
    sstep [] (config.mkCfg getcwd_ms m0) []
      (SNext (config.mkCfg (advance_past_svc (apply_effect getcwd_ms (errno_eff ENOMEM))) m0)) :=
  getcwd_step_from ENOMEM (by decide)

/-- Lean-only: the step's a0 is the effect's return, read back through the
register map's own set/get lemma: evaluating the map (`bvmap_get` over the
radix tree) does not reduce under `decide`.  Rocq's proof of
`getcwd_enomem_step_refused` compares the returns through `inversion`
instead. -/
theorem a0_after_the_call (ms : machine_state) (eff : SyscallEffect) :
    bvmap_get (10 : reg) (advance_past_svc (apply_effect ms eff)).ms_regs = some eff.eff_ret := by
  show bvmap_get (10 : reg) (set_reg ms 10 eff.eff_ret).ms_regs = some eff.eff_ret
  have hx0 : bv_eqb (10 : reg) 0 = false := by decide
  simp only [set_reg, hx0, Bool.false_eq_true, ↓reduceIte, bvmap_get_set_same]

/-- …`Run.sstep_cfg Run.forced_only_cfg` refuses it.  Any step into that
configuration is a syscall step whose outcome set a0 to -ENOMEM, and
`getcwd_only` says such an outcome is one of the injected three —
spurious, since -ERANGE was available — while the one non-spurious
outcome, -ERANGE, lands in a different configuration.  The exit and kill
steps emit an event and this step emits none; every other step starts
from a state with no syscall pending, or ends in `SError`. -/
theorem getcwd_enomem_step_refused :
    ¬ sstep_cfg [] forced_only_cfg (config.mkCfg getcwd_ms m0) []
        (SNext (config.mkCfg (advance_past_svc (apply_effect getcwd_ms (errno_eff ENOMEM))) m0)) := by
  intro h
  generalize hc : config.mkCfg getcwd_ms m0 = c at h
  generalize hev : ([] : List event) = evs0 at h
  generalize hst : SNext (config.mkCfg (advance_past_svc (apply_effect getcwd_ms
    (errno_eff ENOMEM))) m0) = st at h
  cases h with
  | sstep_cfg_instr ms model ms' model' _ hsvc _ =>
    cases hc
    exact absurd hsvc (by decide)
  | sstep_cfg_instr_fault _ _ _ _ _ => cases hst
  | sstep_cfg_instr_unmodeled _ _ _ _ _ => cases hst
  | sstep_cfg_syscall ms model x8 eff model' model'' evs _ hsvc hspec hns _ _ =>
    cases hc
    have hx8 : Z_to_bv 64 17 = x8 := Option.some.inj hsvc
    subst hx8
    obtain ⟨rfl, rfl, e, hin, rfl⟩ := getcwd_only _ _ _ _ hspec
    simp only [getcwd_errnos, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | hin
    · -- -ERANGE lands elsewhere: a0 differs
      injection hst with hst
      injection hst with hms _
      have h0 :
          bvmap_get (10 : reg) (advance_past_svc (apply_effect getcwd_ms (errno_eff ENOMEM))).ms_regs
          = bvmap_get (10 : reg) (advance_past_svc (apply_effect getcwd_ms (errno_eff ERANGE))).ms_regs := by
        rw [hms]
      rw [a0_after_the_call, a0_after_the_call] at h0
      exact absurd (Option.some.inj h0) (by decide)
    · -- an injected errno: spurious, which the step's premise refutes
      apply hns
      refine ⟨getcwd_off_under_forced_only, ?_, errno_eff ERANGE, m0, [],
              getcwd_admits m0 ERANGE (by decide), by decide⟩
      rcases hin with rfl | rfl | rfl <;> decide
  | sstep_cfg_syscall_materialization_fault _ _ _ _ _ _ _ _ _ _ _ _ => cases hst
  | sstep_cfg_exit _ _ _ _ _ evs _ _ _ _ _ _ =>
    cases evs <;> cases hev
  | sstep_cfg_killed _ _ _ _ _ evs _ _ _ _ _ =>
    cases evs <;> cases hev
  | sstep_cfg_syscall_unmodeled _ _ _ _ _ _ => cases hst

/-- The positive twin: the filtered relation still steps here, on the
answer the state determines. -/
theorem getcwd_erange_step_admitted_under_forced_only :
    sstep_cfg [] forced_only_cfg (config.mkCfg getcwd_ms m0) []
      (SNext (config.mkCfg (advance_past_svc (apply_effect getcwd_ms (errno_eff ERANGE))) m0)) :=
  sstep_cfg.sstep_cfg_syscall getcwd_ms m0 (Z_to_bv 64 17) (errno_eff ERANGE) m0 m0 []
    rfl rfl (getcwd_admits m0 ERANGE (by decide)) getcwd_erange_kept_under_forced_only rfl
    (materialize_model_accesses_no_lazy _ _ rfl)

/-! ## Part 4 — cred: `setsid`, forced by state -/

def setsid_i : SyscallInput :=
  SyscallInput.mkInput 157 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

theorem setsid_dispatch (m : Model) (o : outcome SyscallEffect) :
    syscall_spec setsid_i m o ↔ setsid_spec setsid_i m o := by
  unfold syscall_spec
  exact dispatch_arm spec_table setsid_i m o setsid_arm rfl

/-- Before any success, -EPERM is spurious against the spec, which admits a
session id beside it (`setsid_first_call_may_answer_one`).  Not against
Linux: `ksys_setsid` (kernel/sys.c:1268-1301, Linux v6.18.46) answers
-EPERM to a first call too when the caller already leads a session
(:1278-1279) or its `pid_task(sid, PIDTYPE_PGID)` test (:1284-1285) finds
a task, as it does when the caller leads its own process group.  The
model tracks neither, so this is one of the places the exactness
paragraph of `Run.lean`'s spurious-failure section names, where the
filter removes an answer Linux is forced to give. -/
theorem setsid_eperm_spurious_before_success :
    spurious_refusal_cfg forced_only_cfg setsid_i m0 (errno_eff EPERM) :=
  ⟨by decide, by decide, mkEffect 1 [] [], with_setsid_succeeded (with_tid 1 m0), [],
   (setsid_dispatch _ _).2 (setsid_first_call_may_answer_one setsid_i m0 rfl rfl), by decide⟩

/-- After one, -EPERM is the only answer and is kept: the state forces it. -/
theorem setsid_eperm_forced_after_success :
    ¬ spurious_refusal_cfg forced_only_cfg setsid_i (with_setsid_succeeded m0)
        (errno_eff EPERM) := by
  rintro ⟨_, _, eff', m', evs', hspec, hnr⟩
  have h := (setsid_after_a_success_is_eperm setsid_i (with_setsid_succeeded m0) rfl _).1
    ((setsid_dispatch _ _).1 hspec)
  cases h
  exact absurd hnr (by decide)

/-! ## Part 5 — alloc: `mmap`, forced by the budget; and the argument gate -/

theorem mmap_dispatch (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    bv_unsigned i.in_sysno = 222 →
    (syscall_spec i m o ↔
      mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)
        i m o) :=
  fun hno => by
    unfold syscall_spec
    exact dispatch_arm spec_table i m o mmap_arm (by rw [hno]; rfl)

/-- Within budget the -ENOMEM is spurious: the grant
`mmap_within_budget_grants` admits is the non-refusal answer. -/
theorem mmap_enomem_spurious_within_budget :
    spurious_refusal_cfg forced_only_cfg (mmap_in 4096) tight_model (errno_eff ENOMEM) :=
  ⟨by decide, by decide, _, _, _,
   check_syscall_sound_ok _ _ _ _ _ mmap_within_budget_grants, by decide⟩

/-- Beyond the budget the -ENOMEM is FORCED and kept: the errno arm is the
only one with an inhabitant, since the grant's `choose` carries the
budget test in its predicate and that test is false for two pages. -/
theorem mmap_enomem_forced_beyond_budget :
    ¬ spurious_refusal_cfg forced_only_cfg (mmap_in 8192) tight_model (errno_eff ENOMEM) := by
  have honly : ∀ (i : SyscallInput) (o : outcome SyscallEffect),
      mmap_spec 0 8192 3 34 mmap_fd_none 0 i tight_model o ↔
        o = Ok (mkEffect (errno_ret ENOMEM) [] []) tight_model [] := by
    intro i o
    sys_norm
  rintro ⟨_, _, eff', m', evs', hspec, hnr⟩
  have h := (honly (mmap_in 8192) _).1
    ((mmap_dispatch (mmap_in 8192) tight_model _ (by decide)).1 hspec)
  cases h
  exact absurd hnr (by decide)

/-- MAP_FIXED_NOREPLACE rw over exactly `spent_budget_model`'s live page. -/
def mmap_noreplace_live_i : SyscallInput :=
  SyscallInput.mkInput 222 [65536, 4096, 3, 1048610, mmap_fd_none, 0] (fun _ => none) (fun _ => none)

/-- Over an occupied MAP_FIXED_NOREPLACE range the -ENOMEM is spurious
beyond the budget: -EEXIST, which is not a refusal, stands beside it
(`noreplace_over_live_on_a_spent_budget_iff`)… -/
theorem mmap_noreplace_occupied_enomem_spurious_beyond_budget :
    spurious_refusal_cfg forced_only_cfg mmap_noreplace_live_i spent_budget_model
      (errno_eff ENOMEM) :=
  ⟨by decide, by decide, errno_eff EEXIST, spent_budget_model, [],
   (mmap_dispatch mmap_noreplace_live_i spent_budget_model _ (by decide)).2
     ((noreplace_over_live_on_a_spent_budget_iff mmap_noreplace_live_i _).2 (Or.inr rfl)),
   by decide⟩

/-- …and within it, on `one_map_model`'s 1 GiB: the answer is not keyed on
the budget. -/
theorem mmap_noreplace_occupied_enomem_spurious_within_budget :
    spurious_refusal_cfg forced_only_cfg mmap_noreplace_live_i one_map_model (errno_eff ENOMEM) :=
  ⟨by decide, by decide, errno_eff EEXIST, one_map_model, [],
   (mmap_dispatch mmap_noreplace_live_i one_map_model _ (by decide)).2
     ((noreplace_over_live_iff mmap_noreplace_live_i _).2 (Or.inr rfl)),
   by decide⟩

/-- `brk_unbacked_ledger` with its budget spent: the limit is the hundred
bytes the ledger holds, so no page fits. -/
def brk_unbacked_spent_ledger : Model :=
  with_vmmaps (Checks.VmMapsDisjoint.wit_vm [(67536, 100)] 65536 67636 100)
    Checks.VmMapsDisjoint.wit_s0

set_option maxRecDepth 32768 in
/-- THE KNOWN DEFECT, from
bugs/brk-same-page-grow-ledgers-bytes-no-vma-backs.md: over bytes the
ledger alone holds, the filter removes the -ENOMEM Linux is forced to
give.  `brk_unbacked_ledger` holds the hundred bytes a same-page brk grow
ledgered in a page no VMA backs.  On Linux the page at 0x10000 meets no
VMA, so `do_mmap`'s `find_vma_intersection` finds nothing
(mm/mmap.c:410-413, Linux v6.18.46), and on a spent budget
`__mmap_prepare` (mm/vma.c:2418-2429, Linux v6.18.46) refuses the grant
with -ENOMEM, at the address-space limit or at the commit charge.
The ledger calls the page occupied, so the spec admits -EEXIST beside the
-ENOMEM, and `refusal_b` does not count -EEXIST as a refusal.  Under
`forced_only_cfg` the -ENOMEM is filtered out on the spent budget, as on
the witness's own 1 GiB, leaving only an -EEXIST no supported
implementation gives there.  Stated over the literal ledgers, as
`Checks/Cases/Checks/Sys/Mm/Mmap.lean`'s
`noreplace_over_unbacked_brk_bytes_refuses_the_grant` is: the brk fix that
entry asks for flips that file's step pin,
`brk_same_page_grow_ledgers_unbacked_bytes`, and retires this one with
it. -/
theorem mmap_noreplace_over_unbacked_brk_bytes_enomem_is_filtered :
    spurious_refusal_cfg forced_only_cfg mmap_noreplace_live_i brk_unbacked_spent_ledger
        (errno_eff ENOMEM)
    ∧ spurious_refusal_cfg forced_only_cfg mmap_noreplace_live_i brk_unbacked_ledger
        (errno_eff ENOMEM) :=
  ⟨⟨by decide, by decide, errno_eff EEXIST, brk_unbacked_spent_ledger, [],
     check_syscall_sound_ok _ _ _ _ _
       (rfl : check_syscall mmap_noreplace_live_i (errno_eff EEXIST) brk_unbacked_spent_ledger
                = Checks.Sys.Prelude.check_result.CheckOk brk_unbacked_spent_ledger []),
     by decide⟩,
   ⟨by decide, by decide, errno_eff EEXIST, brk_unbacked_ledger, [],
     check_syscall_sound_ok _ _ _ _ _
       (rfl : check_syscall mmap_noreplace_live_i (errno_eff EEXIST) brk_unbacked_ledger
                = Checks.Sys.Prelude.check_result.CheckOk brk_unbacked_ledger []),
     by decide⟩⟩

/-- …and on the same ledger a free page keeps its -ENOMEM, the only answer
the spec admits there: the budget is spent, which is what makes the
-ENOMEM the pin above filters one Linux is forced to give.  A limit that
let a page fit would put the grant beside it, and this pin would fail. -/
theorem mmap_noreplace_free_page_enomem_forced_on_the_unbacked_spent_ledger :
    ¬ spurious_refusal_cfg forced_only_cfg (mmap_noreplace_in 3 4096) brk_unbacked_spent_ledger
        (errno_eff ENOMEM) := by
  have honly : ∀ (i : SyscallInput) (o : outcome SyscallEffect),
      mmap_spec 131072 4096 3 1048610 mmap_fd_none 0 i brk_unbacked_spent_ledger o ↔
        o = Ok (mkEffect (errno_ret ENOMEM) [] []) brk_unbacked_spent_ledger [] := by
    intro i o
    sys_norm
  rintro ⟨_, _, eff', m', evs', hspec, hnr⟩
  have h := (honly (mmap_noreplace_in 3 4096) _).1
    ((mmap_dispatch (mmap_noreplace_in 3 4096) brk_unbacked_spent_ledger _ (by decide)).1 hspec)
  cases h
  exact absurd hnr (by decide)

/-- A free MAP_FIXED_NOREPLACE range beyond the budget keeps its -ENOMEM,
as the NULL-hint grant does (`mmap_enomem_forced_beyond_budget`): the
grant's `choose` has no witness, and -ENOMEM is the only answer. -/
theorem mmap_noreplace_free_enomem_forced_beyond_budget :
    ¬ spurious_refusal_cfg forced_only_cfg (mmap_noreplace_in 3 8192) tight_model
        (errno_eff ENOMEM) := by
  have honly : ∀ (i : SyscallInput) (o : outcome SyscallEffect),
      mmap_spec 131072 8192 3 1048610 mmap_fd_none 0 i tight_model o ↔
        o = Ok (mkEffect (errno_ret ENOMEM) [] []) tight_model [] := by
    intro i o
    sys_norm
  rintro ⟨_, _, eff', m', evs', hspec, hnr⟩
  have h := (honly (mmap_noreplace_in 3 8192) _).1
    ((mmap_dispatch (mmap_noreplace_in 3 8192) tight_model _ (by decide)).1 hspec)
  cases h
  exact absurd hnr (by decide)

/-- An -ENOMEM the ARGUMENT GATE determines is kept although -ENOMEM is the
one member of `Sys.Mm.Mmap.mmap_errnos`: at this input the gate's
`err_ret ENOMEM` is the whole spec (`fixed_overflowing_len_is_enomem`), so
no non-refusal outcome exists and the filter has nothing to remove.  This
is the condition in the exactness claim of `Run.lean`'s spurious-failure
section — a determined answer is kept because nothing stands beside it, not
because it is off the list — fired at a place a list-driven filter would
have got it wrong. -/
theorem mmap_gate_enomem_kept_under_forced_only :
    ¬ spurious_refusal_cfg forced_only_cfg mmap_overflow_i noaccess_base (errno_eff ENOMEM) := by
  rintro ⟨_, _, eff', m', evs', hspec, hnr⟩
  have h := (fixed_overflowing_len_is_enomem mmap_overflow_i noaccess_base _).1
    ((mmap_dispatch mmap_overflow_i noaccess_base _ (by decide)).1 hspec)
  cases h
  exact absurd hnr (by decide)

/-! ## Part 6 — run level: the two witnesses, at the other reading -/

/-- `Checks.Examples.exits_c` is sound for the filtered predicate too,
under every configuration — the same proof as
`Checks.Examples.exits_c_must_exit_at`, over `Run.sstep_cfg`: the
instruction steps and the exit step carry no filter premise, and the
two syscall shapes the filter does touch are ruled out at an exit ecall
by the exit-dispatch lemmas exactly as before. -/
theorem exits_c_must_exit_at_cfg (cfg : SpuriousCfg) (segs : List Segment) (code : word)
    (fuel : Nat) :
    ∀ (ms : machine_state) (model : Model),
    m_halted model = none →
    m_vm_lazy model = [] →
    exits_c segs code fuel ms = true →
    must_exit_at_cfg cfg segs code (config.mkCfg ms model) := by
  induction fuel with
  | zero => intro ms model _ _ hc; simp only [exits_c, Bool.false_eq_true] at hc
  | succ fuel ih =>
    intro ms model hh hlazy hc
    cases hsvc : ms.ms_svc_pending with
    | some x8 =>
      -- the terminating ecall
      simp only [exits_c, hsvc, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hx8, hcode⟩ := hc
      have hcode' := (bv_eqb_eq _ _).1 hcode
      have hno : exit_sysno (sys_input segs ms x8).in_sysno := hx8
      have harg : in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 := rfl
      apply must_exit_at_cfg.must_exit_at_cfg_running
      · exact hh
      · refine ⟨[] ++ [ExitEv (bv_and (in_arg (sys_input segs ms x8) 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (in_arg (sys_input segs ms x8) 0)
                                                  (Z_to_bv 64 255)) model))],
                 SNext (config.mkCfg ms (with_halted (bv_and (in_arg (sys_input segs ms x8) 0)
                                                       (Z_to_bv 64 255)) model)), ?_⟩
        exact sstep_cfg.sstep_cfg_exit ms model x8 _ _ [] _ hh hsvc (exit_dispatch_admits _ model hno) rfl rfl
      · intro evs hss
        cases hss with
        | sstep_cfg_instr_fault _ _ _ hsvc' _ => rw [hsvc] at hsvc'; cases hsvc'
        | sstep_cfg_instr_unmodeled _ _ _ hsvc' _ => rw [hsvc] at hsvc'; cases hsvc'
        | sstep_cfg_syscall_materialization_fault _ _ x8' eff model' evs' _ hsvc' hspec _ hh' _ =>
          rw [hsvc] at hsvc'
          cases hsvc'
          have := exit_dispatch_halts _ _ _ _ _ hno hspec
          rw [this] at hh'
          cases hh'
        | sstep_cfg_syscall_unmodeled _ _ x8' _ hsvc' hspec =>
          rw [hsvc] at hsvc'
          cases hsvc'
          exact exit_dispatch_modeled _ _ hno hspec
      · intro evs c' hss
        cases hss with
        | sstep_cfg_instr _ _ _ _ _ hsvc' _ => rw [hsvc] at hsvc'; cases hsvc'
        | sstep_cfg_syscall _ _ x8' eff model' model'' evs' _ hsvc' hspec _ hh' _ =>
          rw [hsvc] at hsvc'
          cases hsvc'
          have := exit_dispatch_halts _ _ _ _ _ hno hspec
          rw [this] at hh'
          cases hh'
        | sstep_cfg_exit _ _ x8' eff model' evs' code' _ hsvc' hspec hh' _ =>
          rw [hsvc] at hsvc'
          cases hsvc'
          have hhalts := exit_dispatch_halts _ _ _ _ _ hno hspec
          apply must_exit_at_cfg.must_exit_at_cfg_halted
          · show m_halted model' = some code
            rw [hhalts, harg, hcode']
          · exact exit_dispatch_not_killed _ _ _ _ _ hno hspec
        | sstep_cfg_killed _ _ x8' eff model' evs' sig _ hsvc' hspec hk =>
          -- the kill transition: an exit's post-model is not a killed one
          rw [hsvc] at hsvc'
          cases hsvc'
          rw [exit_dispatch_not_killed _ _ _ _ _ hno hspec] at hk
          cases hk
    | none =>
      -- an ordinary instruction
      simp only [exits_c, hsvc] at hc
      cases hstep : RiscvSemantics.step segs ms with
      | MachineOk ms' =>
        simp only [hstep] at hc
        have hacc : mi_account_step segs ms model = MachineOk (ms', model) := by
          rw [mi_account_step_no_lazy segs ms model hlazy, hstep]
        apply must_exit_at_cfg.must_exit_at_cfg_running
        · exact hh
        · exact ⟨[], SNext (config.mkCfg ms' model), sstep_cfg.sstep_cfg_instr ms model ms' model hh hsvc hacc⟩
        · intro evs hss
          cases hss with
          | sstep_cfg_instr_fault _ _ _ _ hacc' => rw [hacc] at hacc'; cases hacc'
          | sstep_cfg_instr_unmodeled _ _ _ _ hacc' => rw [hacc] at hacc'; cases hacc'
          | sstep_cfg_syscall_materialization_fault _ _ _ _ _ _ _ hsvc' _ _ _ _ => rw [hsvc] at hsvc'; cases hsvc'
          | sstep_cfg_syscall_unmodeled _ _ _ _ hsvc' _ => rw [hsvc] at hsvc'; cases hsvc'
        · intro evs c' hss
          cases hss with
          | sstep_cfg_instr _ _ ms'' model'' _ _ hacc' =>
            rw [hacc] at hacc'
            cases hacc'
            exact ih ms' model hh hlazy hc
          | sstep_cfg_syscall _ _ _ _ _ _ _ _ hsvc' _ _ _ _ => rw [hsvc] at hsvc'; cases hsvc'
          | sstep_cfg_exit _ _ _ _ _ _ _ _ hsvc' _ _ _ => rw [hsvc] at hsvc'; cases hsvc'
          | sstep_cfg_killed _ _ _ _ _ _ _ _ hsvc' _ _ => rw [hsvc] at hsvc'; cases hsvc'
      | MachineFault => simp only [hstep, Bool.false_eq_true] at hc
      | MachineUnmodeled => simp only [hstep, Bool.false_eq_true] at hc

/-- The exit-0 image must-exits under forced-only: the positive witness
of `MustExit.v`'s non-vacuity paragraph
(`Checks.Examples.exit0_image_must_exit_zero`), at `Run.forced_only_cfg`.
The proof runs the image;
`Checks/Cases/EquivalenceDefinition/MustExit.lean` reaches the same
statement as `exit0_image_forced_only_exits_zero` through the classical
`run_decided_is_total` instead. -/
theorem exit0_image_must_exit_zero_under_forced_only :
    must_exit_with_scfg forced_only_cfg verdict_accept exit0_image demo_limit demo_entry
      demo_proc_input := by
  unfold must_exit_with_scfg init_config
  apply exits_c_must_exit_at_cfg _ _ _ 8
  · rfl
  · rfl
  · decide +kernel

/-- ...and the undecodable image refutes it there too, at every code:
the fetch that leaves the modeled surface is an instruction step, and
the filter touches no instruction step. -/
theorem undecodable_image_refutes_must_exit_under_forced_only :
    ¬ must_exit_with_scfg forced_only_cfg verdict_accept undecodable_image demo_limit
        fixture_entry demo_proc_input := by
  apply must_exit_with_scfg_refuted_by_error
  apply run_scfg_unmodeled_errors
  refine ⟨[], _, star_cfg.star_cfg_refl _, ?_⟩
  refine ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
  rw [mi_account_step_no_lazy _ _ _ rfl]
  simp only [undecodable_image, init_config, fixture_entry, demo_proc_input,
    ProcInput.mkProcInput, undecodable_step_unmodeled]

end LinuxProcessSemantics.LinuxProcessSem.Checks.SpuriousCfg
