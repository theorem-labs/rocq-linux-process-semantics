import LinuxProcessSemantics.LinuxProcessSem.Run
import LinuxProcessSemantics.EquivalenceDefinition.MustExit
import LinuxProcessSemantics.EquivalenceDefinition.Classifier
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Examples — what the definitions MEAN

Mirrors the parts of `theories/LinuxProcessSem/Checks/Examples.v` that
the Phase-1 Lean tree can state: the undecodable image (coverage is not
free), the acceptor's outcomes read back as `Run.sstep` transitions
(`checker_ok_is_run_step` and its two companions), the exit dispatch
lemmas, the fuel-bounded witness `exits_c` and its soundness for
`MustExit.must_exit_at`, and the two run-level witnesses — one concrete
image `must_exit_with` HOLDS of, and one it fails for at every code.  One
twin the Rocq file does not carry is added here because the Lean skeleton
is judged on it: an image that exits 1 satisfies the predicate at 1 and
therefore refutes it at 0.

Not part of the trusted specification: this file is QA on the
definitions, written to be READ.

The executable pins (`undecodable_step_unmodeled` and the `exits_c` runs)
are closed by the KERNEL — `rfl`/`decide`, never the native-code decision
tactic — so `#print axioms` at the end shows nothing beyond what the
tactic library uses; `Checks/Axioms.lean` makes that a build failure. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Examples

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.EquivalenceDefinition.Classifier
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude

/-! ## Coverage is not free: an image the model does not cover

A four-byte executable segment holding 0xffffffff, a word the decoder does
not decode.  `Run.reaches_unmodeled` holds of its run, so a
`strong_universal_T` naming it as its source is unprovable however the
target is chosen — the vacuity the `modeled` clause exists to block. -/

def undecodable_segment : Segment :=
  { seg_base := 0x100, seg_size := 4, seg_perms := "r-x", seg_bytes := ["ffffffff"] }
def undecodable_segments : List Segment := [undecodable_segment]

example : decode_any (Z_to_bv 32 0xffffffff) = none := by decide

theorem undecodable_step_unmodeled :
    RiscvSemantics.step undecodable_segments
      (init_machine_state undecodable_segments 0x100 demo_phdrs
         (Z_to_bv 64 65536) demo_draw [[]] [] demo_uid demo_hwcap)
    = MachineUnmodeled := by
  rfl

/-- The process input every statement below runs on: one empty argument,
no environment, an empty file system, end of input. -/
def demo_proc_input : ProcInput :=
  ProcInput.mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                        default_nofile (Z_to_bv 64 0) demo_hwcap false .Sv48

/-- The fixture entry the undecodable examples use: its stack pointer sits
far below `sp_window_lo`, and these examples never have to validate it. -/
def fixture_entry : ExecEntry :=
  ExecEntry.mkEntry (Z_to_bv 64 65536) (Z_to_bv 64 1048576) (Z_to_bv 64 mmap_base_max)
    demo_draw

theorem run_of_undecodable_image_is_unmodeled :
    (run (Image.mkImage undecodable_segments 0x100 demo_phdrs) demo_limit
       fixture_entry demo_proc_input).bh_unmodeled := by
  apply reaches_unmodeled_intro
  · rfl
  · rfl
  · rw [mi_account_step_no_lazy _ _ _ rfl]
    simp only [fixture_entry, demo_proc_input, ProcInput.mkProcInput, undecodable_step_unmodeled]

/-! ## The acceptor's outcomes, read back as `Run.sstep` transitions

UNIVERSALLY QUANTIFIED — a `∀` over every input the acceptor can be handed,
which no finite set of traces establishes.

`Checks/ExecutableSpecs.lean` does not import `Run`, so nothing it proves
can mention `sstep`: its theorems reach `syscall_spec` and
`syscall_post_model`, and that the accounting it applies IS the accounting
the run performs was asserted only in a comment.  These three say it in the
one place that can see both.  (Rocq: `Checks.Examples.checker_ok_is_run_step`
and its two companions.  What they buy — adding or altering a premise of a
syscall `sstep` rule breaks a proof naming `check_syscall_for_run`, where a
simulation proof could be repaired around it — is argued on the Rocq
theorems and holds here unchanged.  `SError` carries no reason, so the two
error theorems pin the run's verdict and not which rule delivered it.)

One thing is the Lean tree's own: the unmodeled companion takes the
premise `Checks/ExecutableSpecs.lean`'s header explains.  Over the partial
checked table a `CheckUnmodeled` verdict at a number the spec answers is
the checker declining what it has no arm for, not a run error, so the
theorem holds where the two lookups agree at the call's number and is
stated so.  The success and fault companions consume the premise-free
sound halves and take nothing.  The success theorem itself is Rocq's
statement verbatim, kill disjunct and `m_killed` conjunct included; it
closes here because ticket A12 ported `Run.sstep_killed`, the rule its
third disjunct is proved with, and the `m_killed = none` premise of
`Run.sstep_exit` its second disjunct carries.

`CheckReject` has no companion, for Rocq's reason: what it wants is a
NEGATIVE statement — a rejected effect admits no syscall `sstep` — which
follows from `check_syscall_complete_ok` by inversion and is not written
yet. -/

theorem checker_ok_is_run_step (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff : SyscallEffect) (model'' : Model) (evs : List event) :
    m_halted model = none →
    ms.ms_svc_pending = some x8 →
    check_syscall_for_run (sys_input segs ms x8) eff model = some (CheckOk model'' evs) →
    (m_halted model'' = none ∧
      sstep segs (config.mkCfg ms model) evs
        (SNext (config.mkCfg (advance_past_svc (apply_effect ms eff)) model'')))
    ∨ (∃ code, m_halted model'' = some code ∧ m_killed model'' = none ∧
        sstep segs (config.mkCfg ms model) (evs ++ [ExitEv code (m_fs model'')])
          (SNext (config.mkCfg ms model'')))
    ∨ (∃ sig, m_killed model'' = some sig ∧
        sstep segs (config.mkCfg ms model) (evs ++ [KillEv sig (m_fs model'')])
          (SNext (config.mkCfg ms model''))) := by
  intro hh hsvc hchk
  obtain ⟨model', hspec, hpost⟩ := check_syscall_for_run_sound_ok _ _ _ _ _ hchk
  cases hhalt : m_halted model' with
  | some code =>
    rw [syscall_post_model_halted model' eff code hhalt] at hpost
    injection hpost with hpost
    rw [← hpost]
    cases hkill : m_killed model' with
    | some sig =>
      exact Or.inr (Or.inr ⟨sig, rfl,
        sstep.sstep_killed ms model x8 eff model' evs sig hh hsvc hspec hkill⟩)
    | none =>
      exact Or.inr (Or.inl ⟨code, hhalt, rfl,
        sstep.sstep_exit ms model x8 eff model' evs code hh hsvc hspec hhalt hkill⟩)
  | none =>
    rw [syscall_post_model_running model' eff hhalt] at hpost
    obtain ⟨_, _, _, _, _, hproc, _⟩ := materialize_model_accesses_frame model' _ model'' hpost
    refine Or.inl ⟨?_,
      sstep.sstep_syscall ms model x8 eff model' model'' evs hh hsvc hspec hhalt hpost⟩
    show model''.m_proc.procst_halted = none
    rw [hproc]
    exact hhalt

theorem checker_fault_is_run_error (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff : SyscallEffect) :
    m_halted model = none →
    ms.ms_svc_pending = some x8 →
    check_syscall_for_run (sys_input segs ms x8) eff model = none →
    sstep segs (config.mkCfg ms model) [] SError := by
  intro hh hsvc hchk
  obtain ⟨model', evs, hspec, hhalt, hfault⟩ := check_syscall_for_run_sound_fault _ _ _ hchk
  exact sstep.sstep_syscall_materialization_fault ms model x8 eff model' evs
    hh hsvc hspec hhalt hfault

/-- Under the premise, for the reason the section header gives: without it
the verdict may be the checker's own decline at a number the spec answers. -/
theorem checker_unmodeled_is_run_error (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff : SyscallEffect) (hagree : lookups_agree_at (bv_unsigned x8)) :
    m_halted model = none →
    ms.ms_svc_pending = some x8 →
    check_syscall_for_run (sys_input segs ms x8) eff model = some CheckUnmodeled →
    sstep segs (config.mkCfg ms model) [] SError := by
  intro hh hsvc hchk
  exact sstep.sstep_syscall_unmodeled ms model x8 hh hsvc
    (check_syscall_for_run_sound_unmodeled _ _ _ hagree hchk)

/-! ## The modeled surface, pinned as a SET

Not as a literal: a list of the table's numbers here was a line every
port had to edit in a file every port touches, so two ports conflicted
on every merge.  What is stated instead never changes when an arm is
added -- the list and the dispatcher name the same set of numbers, for
whatever the table holds -- and which numbers those are is
`tools/check_syscall_docs.py`'s question.  `lookup_arm_in`,
`syscall_spec_number_modeled` and `syscall_spec_unmodeled_outside` are
`theories/LinuxProcessSem/Checks/DispatchSurface.v`'s direction 1 and
`modeled_sysnos_nodup` its no-repeats check, ported here ahead of that
file's twin; `Checks/DispatchSurface.lean` uses them from here and says
why they have not moved.

The declines at the end are registers L2 and L3 of
`tools/check_decline_registers.py`: each asserts that a NUMBER has no arm
in the Lean table, and the check fails the day an arm for it lands
without retiring the assertion.  They are the negative half of the
membership pins -- a table with a `write` arm would make them false, and
a table without the `exit` arms would make the positive half false. -/

/-- `Checks/DispatchSurface.v`'s `lookup_arm_in`: if the lookup finds an
arm, the number it was given is one of the table's own.  Stated for ANY
table, so no arm's arrival re-proves it. -/
theorem lookup_arm_in (t : List SpecArm) (n : Int) (a : SpecArm) :
    lookup_arm t n = some a → n ∈ arm_numbers t := by
  induction t with
  | nil => intro h; cases h
  | cons b r ih =>
    intro h
    simp only [lookup_arm] at h
    by_cases e : b.sa_no = n
    · simp only [arm_numbers, List.map_cons, List.mem_cons]
      exact Or.inl e.symm
    · simp only [e, ↓reduceIte] at h
      simp only [arm_numbers, List.map_cons, List.mem_cons]
      exact Or.inr (ih h)

/-- The converse, which `DispatchSurface.v` reaches only through
`Progress.syscall_spec_witness` (as `modeled_sysnos_dispatched`, a floor
on ANSWERS): at the list level it is plain induction.  Every number the
list names has an arm — not that the arm answers anything, which stays
the arm's own business. -/
theorem in_lookup_arm (t : List SpecArm) (n : Int) :
    n ∈ arm_numbers t → ∃ a, lookup_arm t n = some a := by
  induction t with
  | nil => intro h; simp only [arm_numbers, List.map_nil, List.not_mem_nil] at h
  | cons b r ih =>
    intro h
    simp only [arm_numbers, List.map_cons, List.mem_cons] at h
    simp only [lookup_arm]
    by_cases e : b.sa_no = n
    · exact ⟨b, by simp only [e, ↓reduceIte]⟩
    · simp only [e, ↓reduceIte]
      rcases h with h | h
      · exact absurd h.symm e
      · exact ih h

/-- The set comparison: `modeled_sysnos` and the dispatcher's lookup name
the same numbers.  This is what the old literal pin was for, minus the
literal. -/
theorem modeled_sysnos_iff_dispatched (n : Int) :
    n ∈ modeled_sysnos ↔ ∃ a, lookup_arm spec_table n = some a :=
  ⟨in_lookup_arm spec_table n, fun ⟨a, h⟩ => lookup_arm_in spec_table n a h⟩

/-- `Checks/DispatchSurface.v`'s `syscall_spec_number_modeled`: an `Ok`
outcome pins the syscall number into the list.  A number with no arm
reaches `Monad.unmodeled`, which admits no `Ok` at all. -/
theorem syscall_spec_number_modeled (i : SyscallInput) (m : Model) (x : SyscallEffect)
    (m' : Model) (evs : List event) :
    syscall_spec i m (Ok x m' evs) → bv_unsigned i.in_sysno ∈ modeled_sysnos := by
  intro h
  unfold syscall_spec dispatch at h
  cases e : lookup_arm spec_table (bv_unsigned i.in_sysno) with
  | some a => exact lookup_arm_in _ _ _ e
  | none =>
    rw [e] at h
    cases h

/-- `Checks/DispatchSurface.v`'s `syscall_spec_unmodeled_outside`: the same
fact read as fail-closed behaviour. -/
theorem syscall_spec_unmodeled_outside (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    bv_unsigned i.in_sysno ∉ modeled_sysnos → syscall_spec i m o → o = Unmodeled := by
  intro hnin h
  cases o with
  | Ok x m' evs => exact absurd (syscall_spec_number_modeled i m x m' evs h) hnin
  | Unmodeled => rfl

/-- `Checks/DispatchSurface.v`'s `modeled_sysnos_nodup`: `lookup_arm` is
first-match-wins, so a number listed twice silently shadows its second
arm, and a membership statement cannot see it.  Decided against whatever
the table currently holds, so a replayed or twice-merged arm fails here
at the build, and in `tools/check_syscall_docs.py` before it. -/
theorem modeled_sysnos_nodup : modeled_sysnos.Nodup := by decide

/-! The membership pins.  The numbers are the kernel's, read at v6.18.46
(commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5): `scripts/syscall.tbl`
rows `0 common io_setup`, `93 common exit` and `94 common exit_group`,
which `scripts/syscalltbl.sh` turns into `asm/syscall_table_64.h`,
selected by `arch/riscv/include/asm/syscall_table.h` and included by
`arch/riscv/kernel/syscall_table.c` to fill `sys_call_table`.  A port
that adds an arm adds nothing here; a port that REMOVES one of the two
exit arms fails the positive half. -/
example : (93 : Int) ∈ modeled_sysnos := by decide
example : (94 : Int) ∈ modeled_sysnos := by decide

/-- Register L3: no arm answers to io_setup (0), said at the lookup and
at the list.  Both are shapes `tools/check_decline_registers.py` reads.
The register sat on write (64) until that arm was ported; io_setup is
outside the Rocq table too (`docs/syscalls/` has no page for it), so no
port can move it again. -/
example : (lookup_arm spec_table 0).isNone = true := by decide
example : (0 : Int) ∉ modeled_sysnos := by decide

/-- Register L2: io_setup (0) stands for every number outside the table.
Were it ever ported, that change would retire this theorem and the two
examples above it; `tools/check_decline_registers.py` fails otherwise. -/
theorem io_setup_is_unmodeled (i : SyscallInput) (m : Model) :
    bv_unsigned i.in_sysno = 0 → syscall_spec i m Unmodeled := by
  intro h
  apply dispatch_unmodeled
  rw [h]
  decide

/-! ## The exit dispatch: what the run tree sees at an exit ecall -/

/-- The syscall numbers that route to `Exit.exit_spec`: exit (93) and
exit_group (94). -/
def exit_sysno (no : word) : Prop :=
  bv_unsigned no = 93 ∨ bv_unsigned no = 94

/-- At either number the dispatcher IS the exit spec. -/
theorem exit_dispatch_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    exit_sysno i.in_sysno →
    (syscall_spec i m o ↔ exit_spec (in_arg i 0) i m o) := by
  rintro (E | E)
  · unfold syscall_spec dispatch; rw [E]; exact Iff.rfl
  · unfold syscall_spec dispatch; rw [E]; exact Iff.rfl

/-- The exit spec admits an outcome — the run is not stuck at the ecall. -/
theorem exit_dispatch_admits (i : SyscallInput) (m : Model) :
    exit_sysno i.in_sysno →
    syscall_spec i m
      (Ok (mkEffect (Z_to_bv 64 0) [] [])
          (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []) := by
  intro hno
  apply (exit_dispatch_iff i m _ hno).2
  exact Monad.bind_ok _ _ i m () _ [] _ _ [] rfl rfl

/-- ... and admits NO OTHER: the exit spec is a `set_halted` followed by a
return, with no `choose` anywhere, so the post-model, the effect and the
event list are all forced. -/
theorem exit_dispatch_forced (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) :
    exit_sysno i.in_sysno →
    syscall_spec i m (Ok eff m' evs) →
    eff = mkEffect (Z_to_bv 64 0) [] [] ∧
    m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m ∧ evs = [] := by
  intro hno hspec
  have h := (exit_dispatch_iff i m _ hno).1 hspec
  obtain ⟨x, m1, evs1, evs2, h1, h2, h3⟩ := h
  have h1' : Ok x m1 evs1 = Ok () (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) [] := h1
  cases h1'
  have h2' : Ok eff m' evs2 = Ok (mkEffect (Z_to_bv 64 0) [] []) _ [] := h2
  cases h2'
  exact ⟨rfl, rfl, by simpa using h3⟩

/-- Every admissible exit outcome HALTS, with the low byte of the status. -/
theorem exit_dispatch_halts (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) :
    exit_sysno i.in_sysno →
    syscall_spec i m (Ok eff m' evs) →
    m_halted m' = some (bv_and (in_arg i 0) (Z_to_bv 64 255)) := by
  intro hno hspec
  obtain ⟨_, rfl, _⟩ := exit_dispatch_forced _ _ _ _ _ hno hspec
  exact m_halted_with_halted _ _

/-- The same, for the OTHER terminal field: an exit's post-model is
`with_halted`'s, so it is not a killed one — which is what keeps
`Run.sstep_exit` and `Run.sstep_killed` apart at an `exit` ecall.  (Rocq:
`Checks.Examples.exit_dispatch_not_killed`.) -/
theorem exit_dispatch_not_killed (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) :
    exit_sysno i.in_sysno →
    syscall_spec i m (Ok eff m' evs) →
    m_killed m' = none := by
  intro hno hspec
  obtain ⟨_, rfl, _⟩ := exit_dispatch_forced _ _ _ _ _ hno hspec
  rfl

/-- Exit is inside the modeled surface. -/
theorem exit_dispatch_modeled (i : SyscallInput) (m : Model) :
    exit_sysno i.in_sysno → ¬ syscall_spec i m Unmodeled := by
  intro hno hspec
  have h := (exit_dispatch_iff i m _ hno).1 hspec
  rcases h with h | ⟨x, m1, evs1, h1, h2⟩
  · have h' : (Unmodeled : outcome Unit) = Ok () (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) [] := h
    cases h'
  · have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0) [] []) m1 [] := h2
    cases h'

/-! ## A fuel-bounded executable witness for `MustExit.must_exit_at`

A straight-line binary that ends in exit is checked by RUNNING it:
`exits_c` walks `RiscvSemantics.step` until a syscall is pending, and then
asks whether it is an exit carrying the right code.  A `Bool` on purpose:
the machine states it passes through stay inside the computation. -/
def exits_c (segs : List Segment) (code : word) (fuel : Nat) (ms : machine_state) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
      match ms.ms_svc_pending with
      | some x8 =>
          (decide (bv_unsigned x8 = 93) || decide (bv_unsigned x8 = 94))
          && bv_eqb (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) code
      | none =>
          match RiscvSemantics.step segs ms with
          | MachineOk ms' => exits_c segs code fuel' ms'
          | MachineFault | MachineUnmodeled => false

/-- `exits_c` is sound for `MustExit.must_exit_at`: a program it accepts
really has NO other execution.  Both premises on the model are discharged
by `rfl` at an initial configuration. -/
theorem exits_c_must_exit_at (segs : List Segment) (code : word) (fuel : Nat) :
    ∀ (ms : machine_state) (model : Model),
    m_halted model = none →
    m_vm_lazy model = [] →
    exits_c segs code fuel ms = true →
    must_exit_at segs code (config.mkCfg ms model) := by
  induction fuel with
  | zero => intro ms model _ _ hc; simp [exits_c] at hc
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
      simp only [exits_c, hsvc] at hc
      cases hstep : RiscvSemantics.step segs ms with
      | MachineOk ms' =>
        simp only [hstep] at hc
        have hacc : mi_account_step segs ms model = MachineOk (ms', model) := by
          rw [mi_account_step_no_lazy segs ms model hlazy, hstep]
        apply must_exit_at.must_exit_at_running
        · exact hh
        · exact ⟨[], SNext (config.mkCfg ms' model), sstep.sstep_instr ms model ms' model hh hsvc hacc⟩
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
            exact ih ms' model hh hlazy hc
          | sstep_syscall _ _ _ _ _ _ _ _ hsvc' _ _ _ => rw [hsvc] at hsvc'; cases hsvc'
          | sstep_exit _ _ _ _ _ _ _ _ hsvc' _ _ _ => rw [hsvc] at hsvc'; cases hsvc'
          | sstep_killed _ _ _ _ _ _ _ _ hsvc' _ _ => rw [hsvc] at hsvc'; cases hsvc'
      | MachineFault => simp [hstep] at hc
      | MachineUnmodeled => simp [hstep] at hc

/-! ## The images, and the entry a real `execve` could have chosen

Three instructions at 0x100, as the hex the loader would have produced:
`addi a7, x0, 93` (0x05d00893), `addi a0, x0, 0` (0x00000513), `ecall`
(0x00000073), little-endian.  The exit-1 twin differs in one byte:
`addi a0, x0, 1` (0x00100513). -/
def exit0_segment : Segment :=
  { seg_base := 0x100, seg_size := 12, seg_perms := "r-x",
    seg_bytes := ["9308d0051305000073000000"] }
def exit0_segments : List Segment := [exit0_segment]
def exit0_image : Image := Image.mkImage exit0_segments 0x100 demo_phdrs

def exit1_segment : Segment :=
  { seg_base := 0x100, seg_size := 12, seg_perms := "r-x",
    seg_bytes := ["9308d0051305100073000000"] }
def exit1_segments : List Segment := [exit1_segment]
def exit1_image : Image := Image.mkImage exit1_segments 0x100 demo_phdrs

/-- The undecodable image from part 1, as an `Image`. -/
def undecodable_image : Image := Image.mkImage undecodable_segments 0x100 demo_phdrs

/-- An `execve` placement that really satisfies `Run.valid_entry`: the
stack pointer at the bottom of its window, the break one page up, the
mmap base at the band's cap. -/
def demo_entry : ExecEntry :=
  ExecEntry.mkEntry (Z_to_bv 64 0x7fff80000000) (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max)
    demo_draw

/-! ## The witnesses

UNIVERSALLY QUANTIFIED: every execution of this image from this entry
halts with exit code 0, which is a claim about the whole run tree.  It is
the first place a concrete image SATISFIES `MustExit.must_exit_with`. -/
theorem exit0_image_must_exit_zero :
    must_exit_with verdict_accept exit0_image demo_limit demo_entry demo_proc_input := by
  unfold must_exit_with init_config
  apply exits_c_must_exit_at _ _ 8
  · rfl
  · rfl
  · decide +kernel

/-- The exit-1 twin exits 1, by the same witness... -/
theorem exit1_image_must_exit_one :
    must_exit_with verdict_reject exit1_image demo_limit demo_entry demo_proc_input := by
  unfold must_exit_with init_config
  apply exits_c_must_exit_at _ _ 8
  · rfl
  · rfl
  · decide +kernel

/-- ... and therefore does NOT exit 0: the code is unique
(`must_exit_with_exclusive`), and the two verdicts differ. -/
theorem exit1_image_refutes_must_exit_zero :
    ¬ must_exit_with verdict_accept exit1_image demo_limit demo_entry demo_proc_input :=
  fun h => verdict_accept_neq_reject
    (must_exit_with_exclusive _ _ _ _ _ _ h exit1_image_must_exit_one)

/-- And the other side: the undecodable image errors on its first fetch,
and `must_exit_with` forbids an error anywhere in the tree, at every code
— so this refutes exit 0 and exit 1 alike.  The route is
`must_exit_with_refuted_by_error` through
`Run.reaches_unmodeled_reaches_error`: leaving the modeled surface is a
special case of erroring. -/
theorem undecodable_image_refutes_must_exit :
    ¬ must_exit_with verdict_accept undecodable_image demo_limit fixture_entry demo_proc_input :=
  must_exit_with_refuted_by_error _ _ _ _ _
    (reaches_unmodeled_reaches_error _ _ run_of_undecodable_image_is_unmodeled)

/-- The witness must not fire on a wrong code either: the exit-0 image's
run does not pass the exit-1 test.  (This pins `exits_c`'s code
comparison, the half `exit0_image_must_exit_zero` cannot see.) -/
example : exits_c exit0_segments verdict_reject 8
    (init_machine_state exit0_segments 0x100 demo_phdrs demo_entry.en_sp
       demo_entry.en_draw [[]] [] demo_uid demo_hwcap) = false := by
  decide +kernel

#print axioms checker_ok_is_run_step
#print axioms exit0_image_must_exit_zero
#print axioms exit1_image_refutes_must_exit_zero
#print axioms undecodable_image_refutes_must_exit

end LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
