-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Omni.v
import LinuxProcessSemantics.LinuxProcessSem.OmniRun
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
import LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.PropExec

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058
unported: demo_proc_input -- the process input `Omni.v` defines ahead of Part 1 for its concrete pins; `Checks/Examples.lean` defines the same term under the same name, and Parts 2, 4 and 5 here read that copy -/

/-! # LinuxProcessSem.Checks.Omni — what the omni judgments MEAN

Mirrors `theories/LinuxProcessSem/Checks/Omni.v` at the header's baseline:
Part 1, the proof kit between Parts 1 and 2, and Parts 2, 4 and 5.  Not
part of the trusted specification: QA on the definitions of `OmniRun` and
`OmniEquivalence`, in the style of `Checks/Examples.lean`, and the one
definition Part 1 adds, `coexec_progress`, is read by nothing outside
`Checks/`.  Every case is UNIVERSALLY QUANTIFIED (a `∀` over every
execution of a run, which no finite set of traces establishes) or
COMPARES TWO RUNS, the two admission reasons `Omni.v`'s header names.  A
theorem with a Rocq twin names it, and a theorem Rocq does not have says
`Lean-only`, in its own docstring or in the comment that opens the section
or the run of lemmas it belongs to.

- PART 1, the two coinductive readings agree: `sstep_receptive`,
  `coexec_coexec_progress` and `coexec_progress_iff`, with the
  progress-carrying reading of `coexec` they are about (`OmniRun.v`'s
  `coexec_progress`, `coexec_progress_implies` and
  `stuck_not_coexec_progress`).  `OmniRun.lean` registers the reading as
  unported, says it is ported here and why it stays out of that file; the
  decision is beside `coexec_progress_iff` below, and the hypothesis the
  Lean statements carry is the next section's subject.
- PART 2, the exit-0 image SATISFIES the omni statements, for every
  `execve` placement, every input and any budget:
  `exit0_omni_strong_universal` states
  `OmniEquivalence.omni_strong_universal_T` of a concrete pair.
- PART 4, a modeled crash separates the three error postconditions: an
  `ebreak` image satisfies `OmniRun.errors` and `OmniRun.covered`, refutes
  `OmniRun.never_errors`, and its escape frees any target.
- PART 5, `exec`/`coexec` agreement is STRICTLY WEAKER than trace
  equivalence: "write one byte, then loop" and "loop" satisfy the same
  `coexec` postconditions (every one) and the same `exec` postconditions
  (none), yet `OmniRun.cosafe`, and `Equivalence.equiv` through the `iff`,
  tell them apart.

## What is not here, and what it waits on

Part 3, the undecodable image's refutations, was not asked of the ticket
that ported Parts 2, 4 and 5 (K10-prereq-omni).  It defines nothing, so
the register above cannot carry it, and this paragraph is where it is
recorded; it stops being true when Part 3 lands here.

The rest of Rocq's Part 2 states the abort stances and the classifier
shapes on the exit-0 pair: `exit0_strong_universal_abort`, `_either`,
`exit0_not_dies_by_signal`, `exit0_strong_equiv_error_free_abort_any`,
the three `exit0_strong_universal_error_free` shapes, the five `_scfg`
theorems, `MayFailCfg` and the five module ascriptions after it.  Their
vocabulary has no Lean twin — `strong_universal_T_abort` and `_either`,
`dies_by_signal`, the error-free and `_scfg` families and the module
types they seal — so each waits on its definition being ported, and is
stated then, on this pair, as the anti-vacuity check Rocq makes it.
Part 4's `ebreak_omni_may_errors` waits on `Equivalence.v`'s
`run_all_errors_errors`, which its proof reads and the Lean
`Equivalence.lean` does not state.
`ebreak_refutes_omni_error_free` waits on
`OmniEquivalence.omni_strong_equiv_error_free`, which the Lean
`OmniEquivalence.lean` does not define.

## What Rocq proves and what Lean can

Rocq's `sstep_receptive` is unconditional: a running configuration always
takes some step, because Rocq's `Progress.receptive` says the dispatcher
always answers — with the found arm's witness or with the decline.  That
theorem rests on Rocq's `checked_table` covering `spec_table`.  The Lean
`checked_table` is partial while the Track C tickets land, so
`Checks/Progress.lean`'s `receptive` carries a hypothesis — the two tables
agree at the input's number — and its header says K8 inherits it.  It does:
`sstep_receptive` here asks agreement at the number the machine has
pending, and nothing else.  An instruction step needs no such hypothesis
(`sstep_receptive_instr`), and the hypothesis is discharged outright at any
number the checked table has an arm for, at any number the spec table
lacks, and everywhere once the table is complete — one theorem each below.
When the last Track C ticket lands and `Checks/Sys/Table.lean` states the
whole equation `checked_table.map ca_arm = spec_table` — which its
`checked_table_follows_spec_table`, the order half, is not — the
unconditional Rocq statements follow from the `_of_complete` forms by one
application.

THE `∀ n` FORMS HAVE NO INSTANCE WHILE THE TABLE IS PARTIAL.
`sstep_receptive_of_agree`, `coexec_coexec_progress` and
`coexec_progress_iff` ask agreement at every number, and over a partial
`checked_table` that is false at every number `spec_table` answers and
the checked table does not; `Checks/Cases/Checks/Omni.lean` pins the
refutation over the empty table and over the real one, at the number
`Checks/Cases/Invariants.lean` keeps for that purpose, so the real-table
pin fails the day the two tables coincide.  What can be used meanwhile
is the per-number `sstep_receptive` and its discharges,
`sstep_receptive_over` on a fixture table, and the invariant form
`coexec_coexec_progress_inv`, which the pins reach on a configuration
that never has a syscall pending.

Part 5's `wloop_checker` is Rocq's statement, over `check_syscall` at
the loop's write, with no table hypothesis: the write arm is a
`checked_table` row (`Checks/Arms/Fs/ReadWrite.lean`), so the two lookups
agree at 64 by `lookups_agree_at_of_found`.  Part 5's other proofs read
the write arm's own checker (`wloop_check_write`), so that they do not
rest on the table at all.

## Why the coinductive twin lives here

`coexec_progress` is `coexec` with an added premise on the running rule:
that some step exists.  Rocq keeps both readings so that dropping the
premise stays a local reversal, and proves them equivalent
(`coexec_progress_iff`).  The Lean tree took `coexec` alone as the
judgment (`OmniRun.lean`) and left the progress reading to ticket K8.
Both are here, and the equivalence is the theorem that ticket existed for:
without it the Lean `receptive` says nothing about the run relation. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Omni

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! ## The progress-carrying reading of `coexec`

Rocq's `OmniRun.coexec_progress`, constructor for constructor.  The one
difference from `OmniRun.coexec` is the second premise of the running rule:
some step exists.  Under `sstep_receptive` that premise is redundant, which
is what `coexec_progress_iff` proves; the reading is kept so that the
argument stays local to this file. -/

coinductive coexec_progress (segs : List Segment) : config → post → Prop where
  | coexec_progress_halt : ∀ c Q,
      m_halted c.cfg_model ≠ none → Q [] (OHalt c) → coexec_progress segs c Q
  | coexec_progress_step : ∀ c Q,
      m_halted c.cfg_model = none →
      (∃ evs st, sstep segs c evs st) →
      (∀ evs, sstep segs c evs SError → Q evs (OError c)) →
      (∀ evs c', sstep segs c evs (SNext c') →
        coexec_progress segs c' (fun tr o => Q (evs ++ tr) o)) →
      coexec_progress segs c Q

/-- Dropping the progress premise is sound in one direction with no
hypothesis at all.  (Rocq: `OmniRun.coexec_progress_implies`.) -/
theorem coexec_progress_implies (segs : List Segment) (c : config) (Q : post)
    (h : coexec_progress segs c Q) : coexec segs c Q := by
  apply coexec.coinduct segs (fun c Q => coexec_progress segs c Q)
  · intro c Q h
    cases h with
    | coexec_progress_halt c Q hh hq => exact Or.inl ⟨hh, hq⟩
    | coexec_progress_step c Q hh _ herr hn => exact Or.inr ⟨hh, herr, hn⟩
  · exact h

/-- A running configuration with no step satisfies the progress reading
under no postcondition.  (Rocq: `OmniRun.stuck_not_coexec_progress`.) -/
theorem stuck_not_coexec_progress (segs : List Segment) (c : config)
    (hh : m_halted c.cfg_model = none)
    (hstuck : ∀ evs st, ¬ sstep segs c evs st) (Q : post) :
    ¬ coexec_progress segs c Q := by
  intro h
  cases h with
  | coexec_progress_halt _ _ hn _ => exact hn hh
  | coexec_progress_step _ _ _ hp _ _ =>
    obtain ⟨evs, st, hs⟩ := hp
    exact hstuck evs st hs

/-- The progress premise, read back out of the reading that carries it.
Lean-only: the inversion `stuck_not_coexec_progress` refutes with, stated
positively so that a pin can use it. -/
theorem coexec_progress_steps (segs : List Segment) (c : config) (Q : post)
    (hh : m_halted c.cfg_model = none) (h : coexec_progress segs c Q) :
    ∃ evs st, sstep segs c evs st := by
  cases h with
  | coexec_progress_halt _ _ hn _ => exact absurd hh hn
  | coexec_progress_step _ _ _ hp _ _ => exact hp

/-! ## Every answer of the spec is a step

The case analysis Rocq's `sstep_receptive` runs after it has the
dispatcher's answer in hand, split out so that the answer's provenance —
`receptive`'s witness, a fixture table's, an arm's own — is the caller's
business.  `Run.sstep` has one rule for each shape the answer can take:
`Ok` with the post-model halted and killed (`sstep_killed`), halted and
not killed (`sstep_exit`), running with the accesses materializable
(`sstep_syscall`) or not (`sstep_syscall_materialization_fault`), and the
decline (`sstep_syscall_unmodeled`).  Lean-only. -/

theorem sstep_of_syscall_spec (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (o : Monad.outcome SyscallEffect)
    (hh : m_halted model = none) (hp : ms.ms_svc_pending = some x8)
    (h : syscall_spec (sys_input segs ms x8) model o) :
    ∃ evs st, sstep segs (config.mkCfg ms model) evs st := by
  cases o with
  | Ok eff model' evs =>
    cases hh' : m_halted model' with
    | some code =>
      cases hk : m_killed model' with
      | some sig => exact ⟨_, _, sstep.sstep_killed ms model x8 eff model' evs sig hh hp h hk⟩
      | none => exact ⟨_, _, sstep.sstep_exit ms model x8 eff model' evs code hh hp h hh' hk⟩
    | none =>
      cases hm : materialize_model_accesses model' (syscall_effect_accesses eff) with
      | some model'' =>
        exact ⟨_, _, sstep.sstep_syscall ms model x8 eff model' model'' evs hh hp h hh' hm⟩
      | none =>
        exact ⟨_, _,
          sstep.sstep_syscall_materialization_fault ms model x8 eff model' evs hh hp h hh' hm⟩
  | Unmodeled => exact ⟨_, _, sstep.sstep_syscall_unmodeled ms model x8 hh hp h⟩

/-- With nothing pending the machine steps by itself: `Run.sstep` has a
rule for each of the three things `mi_account_step` can say.  Lean-only;
this half of Rocq's `sstep_receptive` needs no table hypothesis. -/
theorem sstep_receptive_instr (segs : List Segment) (c : config)
    (hh : m_halted c.cfg_model = none) (hp : c.cfg_ms.ms_svc_pending = none) :
    ∃ evs st, sstep segs c evs st := by
  obtain ⟨ms, model⟩ := c
  cases ha : mi_account_step segs ms model with
  | MachineOk p =>
    obtain ⟨ms', model'⟩ := p
    exact ⟨_, _, sstep.sstep_instr ms model ms' model' hh hp ha⟩
  | MachineFault => exact ⟨_, _, sstep.sstep_instr_fault ms model hh hp ha⟩
  | MachineUnmodeled => exact ⟨_, _, sstep.sstep_instr_unmodeled ms model hh hp ha⟩

/-! ## `sstep_receptive`

Rocq: `Checks/Omni.v`'s `sstep_receptive`, with the hypothesis
`Checks/Progress.lean` inherits from the partial table: the two tables
agree at the number the machine has pending.  The hypothesis is asked only
at that number, and only when something IS pending, so that a fixture
stopped at an unlisted or checked number discharges it by the theorem
after it rather than by a claim about the whole table. -/

/-- Lean-only: the theorem below over any table `t` in place of
`checked_table`.  The general form exists so that the found-arm branch can
be reached on a fixture table, whatever arms the real table has. -/
theorem sstep_receptive_over (t : List CheckedArm) (segs : List Segment) (c : config)
    (hh : m_halted c.cfg_model = none)
    (hagree : ∀ x8, c.cfg_ms.ms_svc_pending = some x8 → lookups_agree_in t (bv_unsigned x8)) :
    ∃ evs st, sstep segs c evs st := by
  obtain ⟨ms, model⟩ := c
  cases hp : ms.ms_svc_pending with
  | some x8 =>
    exact sstep_of_syscall_spec segs ms model x8 _ hh hp
      (receptive_over t (sys_input segs ms x8) model (hagree x8 hp))
  | none => exact sstep_receptive_instr segs (config.mkCfg ms model) hh hp

/-- Rocq: `Checks/Omni.v`'s `sstep_receptive`, with the hypothesis this
section names: the theorem above at `checked_table`. -/
theorem sstep_receptive (segs : List Segment) (c : config)
    (hh : m_halted c.cfg_model = none)
    (hagree : ∀ x8, c.cfg_ms.ms_svc_pending = some x8 → lookups_agree_at (bv_unsigned x8)) :
    ∃ evs st, sstep segs c evs st :=
  sstep_receptive_over checked_table segs c hh hagree

/-- Lean-only: agreement at every number gives Rocq's statement for every
configuration at once, whatever it has pending; `coexec_coexec_progress`
is proved through it. -/
theorem sstep_receptive_of_agree (segs : List Segment)
    (hagree : ∀ n, lookups_agree_at n) (c : config)
    (hh : m_halted c.cfg_model = none) : ∃ evs st, sstep segs c evs st :=
  sstep_receptive segs c hh (fun x8 _ => hagree (bv_unsigned x8))

/-- Lean-only: a complete checked table gives Rocq's statement outright;
this is the form the tree reaches when the last Track C ticket lands. -/
theorem sstep_receptive_of_complete (segs : List Segment)
    (hall : checked_table.map CheckedArm.ca_arm = spec_table) (c : config)
    (hh : m_halted c.cfg_model = none) : ∃ evs st, sstep segs c evs st :=
  sstep_receptive_of_agree segs (lookups_agree_at_of_complete hall) c hh

/-- Lean-only: stopped at a number the checked table has an arm for, the
machine steps, since the arm's own witness is the dispatcher's answer.  It
discharges the hypothesis Rocq's statement does not carry at the numbers
the partial table already answers. -/
theorem sstep_receptive_checked (segs : List Segment) (c : config)
    (hh : m_halted c.cfg_model = none)
    (hc : ∀ x8, c.cfg_ms.ms_svc_pending = some x8 →
      ∃ a, lookup_ca checked_table (bv_unsigned x8) = some a) :
    ∃ evs st, sstep segs c evs st :=
  sstep_receptive segs c hh (fun x8 hp =>
    match hc x8 hp with
    | ⟨a, ha⟩ => lookups_agree_at_of_found (bv_unsigned x8) a ha)

/-- Lean-only: stopped at a number the spec table has no arm for, the
machine steps, since the dispatcher declines and `sstep_syscall_unmodeled`
is the step.  It discharges the hypothesis Rocq's statement does not
carry at those numbers, where neither table has an arm. -/
theorem sstep_receptive_unlisted (segs : List Segment) (c : config)
    (hh : m_halted c.cfg_model = none)
    (hn : ∀ x8, c.cfg_ms.ms_svc_pending = some x8 →
      lookup_arm spec_table (bv_unsigned x8) = none) :
    ∃ evs st, sstep segs c evs st :=
  sstep_receptive segs c hh (fun x8 hp => lookups_agree_at_of_absent (bv_unsigned x8) (hn x8 hp))

/-! ## `coexec` implies its progress reading

Rocq's `coexec_coexec_progress` is a plain cofixpoint: at every running
configuration `sstep_receptive` supplies the premise.  The Lean
`sstep_receptive` has a hypothesis at the pending number, and a
configuration reachable from `c` may have any number pending, so the
coinduction needs the hypothesis at every configuration it visits.  The
general form below takes an invariant `I` that `sstep` preserves and that
implies progress; Rocq's statement is the instance at the trivial
invariant, with agreement everywhere supplying progress. -/

/-- Lean-only: the coinduction over an invariant `I`, which the Lean
hypothesis makes necessary for the reason this section gives;
`coexec_coexec_progress` is its instance at the trivial invariant. -/
theorem coexec_coexec_progress_inv (segs : List Segment) (I : config → Prop)
    (hstep : ∀ c, I c → m_halted c.cfg_model = none → ∃ evs st, sstep segs c evs st)
    (hinv : ∀ c evs c', I c → sstep segs c evs (SNext c') → I c')
    (c : config) (Q : post) (hI : I c) (h : coexec segs c Q) : coexec_progress segs c Q := by
  apply coexec_progress.coinduct segs (fun c Q => I c ∧ coexec segs c Q)
  · intro c Q hIc
    obtain ⟨hI, h⟩ := hIc
    cases h with
    | coexec_halt c Q hh hq => exact Or.inl ⟨hh, hq⟩
    | coexec_step c Q hh herr hn =>
      exact Or.inr ⟨hh, hstep c hI hh, herr, fun evs c' hs => ⟨hinv c evs c' hI hs, hn evs c' hs⟩⟩
  · exact ⟨hI, h⟩

/-- Rocq: `Checks/Omni.v`'s `coexec_coexec_progress`, under agreement of
the two tables at every number. -/
theorem coexec_coexec_progress (segs : List Segment) (hagree : ∀ n, lookups_agree_at n)
    (c : config) (Q : post) (h : coexec segs c Q) : coexec_progress segs c Q :=
  coexec_coexec_progress_inv segs (fun _ => True)
    (fun c _ hh => sstep_receptive_of_agree segs hagree c hh)
    (fun _ _ _ _ _ => trivial) c Q trivial h

/-! ## The two readings coincide

Rocq: `Checks/Omni.v`'s `coexec_progress_iff`, under the hypothesis this
file inherits; `coexec_progress_iff_of_complete` is the same theorem with
the hypothesis in the form the tree will discharge.

THE DECISION `OmniRun.lean`'s register defers to this file: the
progress-carrying reading IS ported, as the coinductive above, and
`OmniRun.coexec` stays the judgment every other file reads.  Two readings
that provably coincide cost nothing to keep and buy the local reversal
Rocq kept them for; what would cost is a Lean judgment carrying a premise
nothing can discharge, and today that premise — some step exists — is
provable at a configuration only under this file's hypothesis.  So the
reading nothing depends on is the one that carries the premise.  This
stops being the right split when the checked table is complete: then
`coexec_progress_iff_of_complete` closes with the whole equation
`Checks/Sys/Table.lean` will state, and the hypothesis disappears from
both directions.  The register entry in `OmniRun.lean` is a separate
matter: `tools/check_lean_spec_parity.py` reads that file and its
`OmniRun/` parts for the name, so the entry retires only when
`coexec_progress` is defined there — a complete table removes the
hypothesis, not the entry. -/

/-- Rocq: `Checks/Omni.v`'s `coexec_progress_iff`, under agreement of the
two tables at every number. -/
theorem coexec_progress_iff (segs : List Segment) (hagree : ∀ n, lookups_agree_at n)
    (c : config) (Q : post) : coexec segs c Q ↔ coexec_progress segs c Q :=
  ⟨coexec_coexec_progress segs hagree c Q, coexec_progress_implies segs c Q⟩

/-- Lean-only: the theorem above with its hypothesis in the form the tree
will discharge, a complete checked table. -/
theorem coexec_progress_iff_of_complete (segs : List Segment)
    (hall : checked_table.map CheckedArm.ca_arm = spec_table)
    (c : config) (Q : post) : coexec segs c Q ↔ coexec_progress segs c Q :=
  coexec_progress_iff segs (lookups_agree_at_of_complete hall) c Q

/-! ## Machine states with the memory abstracted

Rocq: the section of `Checks/Omni.v` between Part 1 and Part 2, the proof
kit of the Parts after it.  `with_mem` replaces a state's memory by a
variable and `with_mem_eta` says nothing is lost; the rest are the
one-transition facts the concrete runs below are walked with.

THE LEAN ROUTE TO A CONCRETE STEP DIFFERS, and the reason is evaluation.
Rocq closes each step by `vm_compute` with the memory abstracted, so that
the stack image's closure is never read back.  Lean's elaborator does not
evaluate a register read off a stepped state — `rfl` fails on `wloop_fd`
below, whose left side the kernel decides at once — so each instruction
is stepped by `Common/PropExec.lean`'s `step_of_fetch` and
`decode_exec_of_interp` over an abstract `mkst r pc m rom`, the fetch and
the decode decided by `decide +kernel`, and every scalar read off a
stepped machine state — a register, a syscall argument, a byte list — is
a `decide +kernel` lemma of its own, rewritten into the goal before a
checker is evaluated.  A read off the model, which no step touches, needs
none of this: `wloop_stdout`'s descriptor lookup closes by `rfl`.  No
machine state is normalised into a goal, which is the trap `Omni.v`'s
header warns of too. -/

open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.Riscv.Sem (reg_get)
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite (write_spec)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
  (check_write check_write_sound_ok check_write_complete_ok check_write_complete_unmodeled)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude (demo_phdrs demo_limit demo_draw)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
  (demo_proc_input exits_c exit0_segments exit0_image undecodable_image demo_entry
   exit0_image_must_exit_zero exit_sysno exit_dispatch_admits exit_dispatch_forced
   exit_dispatch_halts exit_dispatch_not_killed exit_dispatch_modeled)
open LinuxProcessSemantics.EquivalenceDefinition.Classifier
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.Common.PropExec (mkst step_of_fetch decode_exec_of_interp init_mkst)
open LinuxProcessSemantics.Common.ExitSim (sstep_instr_inv)

/-- A machine state with its memory replaced.  (Rocq: `with_mem`.) -/
def with_mem (ms : machine_state) (mem : word → Option byte) : machine_state :=
  { ms_regs := ms.ms_regs, ms_fregs := ms.ms_fregs, ms_pc_val := ms.ms_pc_val,
    ms_svc_pending := ms.ms_svc_pending, ms_resv := ms.ms_resv, ms_fcsr := ms.ms_fcsr,
    ms_mem := mem, ms_rom := ms.ms_rom }

/-- Nothing is lost: a state is itself with its own memory put back.
(Rocq: `with_mem_eta`.) -/
theorem with_mem_eta (ms : machine_state) : ms = with_mem ms ms.ms_mem := rfl

/-- Erase the accounting on a model with no lazy mappings, in the goal;
the model is read off the term, so the `rfl` that discharges
`m_vm_lazy model = []` sees it.  (Rocq: the `no_lazy` tactic.) -/
scoped macro "no_lazy" : tactic =>
  `(tactic| (rw [mi_account_step_no_lazy]; rotate_left; rfl))

/-- `no_lazy` in a hypothesis.  (Rocq: `no_lazy_in`.) -/
scoped macro "no_lazy_in " h:ident : tactic =>
  `(tactic| (rw [mi_account_step_no_lazy] at $h:ident; rotate_left; rfl))

/-- The same erasure for the materialization after a syscall, in a
hypothesis.  (Rocq: `no_lazy_materialize_in`.) -/
scoped macro "no_lazy_materialize_in " h:ident : tactic =>
  `(tactic| (rw [materialize_model_accesses_no_lazy] at $h:ident; rotate_left; rfl))

/-- From a configuration whose instruction step is a function answer, the
only transition is that step, silently.  (Rocq: `sstep_instr_only`, which
restates `Common/ExitSim.v`'s `sstep_instr_inv` because `Common` is not
part of the Rocq package.  The Lean library does hold
`Common/ExitSim.lean`, so this is that theorem in Rocq's argument order.) -/
theorem sstep_instr_only (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (hlazy : m_vm_lazy model = []) (hsvc : ms.ms_svc_pending = none)
    (hstep : RiscvSemantics.step segs ms = MachineOk ms') :
    ∀ evs st, sstep segs (config.mkCfg ms model) evs st →
      evs = [] ∧ st = SNext (config.mkCfg ms' model) :=
  fun evs st hs => sstep_instr_inv segs ms model ms' evs st hlazy hsvc hstep hs

/-- …and when the answer is a fault, the only transition is the error
one.  (Rocq: `sstep_fault_only`.) -/
theorem sstep_fault_only (segs : List Segment) (ms : machine_state) (model : Model)
    (hlazy : m_vm_lazy model = []) (hsvc : ms.ms_svc_pending = none)
    (hstep : RiscvSemantics.step segs ms = MachineFault) :
    ∀ evs st, sstep segs (config.mkCfg ms model) evs st → evs = [] ∧ st = SError := by
  intro evs st hs
  have hacc : mi_account_step segs ms model = MachineFault := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, hstep]
  cases hs with
  | sstep_instr _ _ _ _ _ _ ha => rw [hacc] at ha; cases ha
  | sstep_instr_fault _ _ _ _ _ => exact ⟨rfl, rfl⟩
  | sstep_instr_unmodeled _ _ _ _ ha => rw [hacc] at ha; cases ha
  | sstep_syscall _ _ _ _ _ _ _ _ hv _ _ _ => rw [hsvc] at hv; cases hv
  | sstep_syscall_materialization_fault _ _ _ _ _ _ _ hv _ _ _ => rw [hsvc] at hv; cases hv
  | sstep_exit _ _ _ _ _ _ _ _ hv _ _ _ => rw [hsvc] at hv; cases hv
  | sstep_killed _ _ _ _ _ _ _ _ hv _ _ => rw [hsvc] at hv; cases hv
  | sstep_syscall_unmodeled _ _ _ _ hv _ => rw [hsvc] at hv; cases hv

/-- A configuration that steps to itself: silent forever.
(Rocq: `fix_coexec_any`.) -/
theorem fix_coexec_any (segs : List Segment) (c : config) (hh : m_halted c.cfg_model = none)
    (hfix : ∀ evs st, sstep segs c evs st → evs = [] ∧ st = SNext c) :
    ∀ Q, coexec segs c Q := by
  intro Q
  apply coexec.coinduct segs (fun c' _ => c' = c)
  · intro c' Q' hc
    subst hc
    refine Or.inr ⟨hh, ?_, ?_⟩
    · intro evs hs
      obtain ⟨_, habs⟩ := hfix _ _ hs
      cases habs
    · intro evs c'' hs
      obtain ⟨_, heq⟩ := hfix _ _ hs
      exact (step_to.SNext.inj heq)
  · rfl

/-- …and no terminating judgment holds of it.  (Rocq: `fix_no_exec`.) -/
theorem fix_no_exec (segs : List Segment) (c : config) (hh : m_halted c.cfg_model = none)
    (hfix : ∀ evs st, sstep segs c evs st → evs = [] ∧ st = SNext c) :
    ∀ Q, ¬ exec segs c Q := by
  intro Q hex
  have hgen : ∀ c' Q', exec segs c' Q' → c' = c → False := by
    intro c' Q' h
    induction h with
    | exec_halt c' Q' hh' _ =>
      intro heq
      subst heq
      exact hh' hh
    | exec_step c' Q' _ hprog _ _ ih =>
      intro heq
      subst heq
      obtain ⟨evs, st, hs⟩ := hprog
      obtain ⟨rfl, rfl⟩ := hfix _ _ hs
      exact ih [] c' hs rfl
  exact hgen _ _ hex rfl

/-- Every path from a self-looping configuration is silent and stays
put.  (Rocq: `fix_star_nil`.) -/
theorem fix_star_nil (segs : List Segment) (c : config)
    (hfix : ∀ evs st, sstep segs c evs st → evs = [] ∧ st = SNext c) :
    ∀ tr c', star segs c tr c' → tr = [] ∧ c' = c := by
  intro tr c' hstar
  have hgen : ∀ c0 tr c', star segs c0 tr c' → c0 = c → tr = [] ∧ c' = c := by
    intro c0 tr c' h
    induction h with
    | star_refl c1 => intro heq; exact ⟨rfl, heq⟩
    | star_step c1 evs c2 tr c3 hs _ ih =>
      intro heq
      subst heq
      obtain ⟨hevs, heq2⟩ := hfix _ _ hs
      obtain ⟨htr, hc3⟩ := ih (step_to.SNext.inj heq2)
      subst hevs htr
      exact ⟨rfl, hc3⟩
  exact hgen _ _ _ hstar rfl

/-- …so the only trace it shows is the empty one.  (Rocq: `fix_obs_nil`.) -/
theorem fix_obs_nil (segs : List Segment) (c : config)
    (hfix : ∀ evs st, sstep segs c evs st → evs = [] ∧ st = SNext c) :
    ∀ tr, obs_trace segs c tr → tr = [] := by
  rintro tr ⟨tr', c', hstar, hp⟩
  obtain ⟨rfl, _⟩ := fix_star_nil segs c hfix _ _ hstar
  cases tr with
  | nil => rfl
  | cons _ _ => exact False.elim hp

/-- "Nothing is ever emitted" is a prefix-closed property.
(Rocq: `prefix_closed_nil`.) -/
theorem prefix_closed_nil : prefix_closed (fun tr => tr = []) := by
  intro tr tr' htr hp
  subst htr
  cases tr' with
  | nil => rfl
  | cons _ _ => exact False.elim hp

/-! ## Part 2 — the exit-0 image satisfies the omni statements, universally

Rocq: `Checks/Omni.v`'s Part 2, over `Checks/Examples.lean`'s
`exit0_image` (Rocq's `Exit0Image` module is the same image as a
`MemImage`).  One omni induction, `exits_c_exec`, delivers the exact trace,
termination and error-freedom at once, which is what
`exit0_omni_strong_universal` is made of; the legacy
`Equivalence.strong_universal_T` follows through the `iff`.  Rocq's two
modules are theorems here, because Lean's `OMNI_SPEC` and
`SPEC` are structures over two images rather than module types.  The
module header lists the rest of Rocq's Part 2 and what it waits on. -/

/-- The omni form of `Checks.Examples.exits_c_must_exit_at`: the same
walk, but the postcondition now records the exact trace and the exit code
together, so trace equality below needs no second lemma.  The successor
state at an instruction is discharged by `sstep_instr_only`; at the exit
ecall the dispatch lemmas of `Checks/Examples.lean` force the one
outcome.  (Rocq: `exits_c_exec`.) -/
theorem exits_c_exec (segs : List Segment) (code : word) (fuel : Nat) :
    ∀ (ms : machine_state) (model : Model), m_halted model = none → m_vm_lazy model = [] →
      exits_c segs code fuel ms = true →
      exec segs (config.mkCfg ms model)
        (fun tr o => tr = [ExitEv code (m_fs model)] ∧ exits_with code tr o) := by
  induction fuel with
  | zero =>
    intro ms model _ _ hc
    simp only [exits_c, Bool.false_eq_true] at hc
  | succ fuel ih =>
    intro ms model hh hlazy hc
    cases hsvc : ms.ms_svc_pending with
    | some x8 =>
      simp only [exits_c, hsvc, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hx8, hcode⟩ := hc
      have hcode' := (bv_eqb_eq _ _).1 hcode
      have hno : exit_sysno (sys_input segs ms x8).in_sysno := hx8
      have harg : in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 := rfl
      have hv : bv_and (in_arg (sys_input segs ms x8) 0) (Z_to_bv 64 255) = code := by
        rw [harg]
        exact hcode'
      apply exec.exec_step
      · exact hh
      · exact ⟨_, _, sstep.sstep_exit ms model x8 _ _ [] _ hh hsvc
          (exit_dispatch_admits _ model hno) rfl rfl⟩
      · intro evs hss
        exfalso
        cases hss with
        | sstep_instr_fault _ _ _ hsvc' _ => rw [hsvc] at hsvc'; cases hsvc'
        | sstep_instr_unmodeled _ _ _ hsvc' _ => rw [hsvc] at hsvc'; cases hsvc'
        | sstep_syscall_materialization_fault _ _ x8' _ _ _ _ hsvc' hspec hh' _ =>
          rw [hsvc] at hsvc'
          cases hsvc'
          rw [exit_dispatch_halts _ _ _ _ _ hno hspec] at hh'
          cases hh'
        | sstep_syscall_unmodeled _ _ x8' _ hsvc' hspec =>
          rw [hsvc] at hsvc'
          cases hsvc'
          exact exit_dispatch_modeled _ _ hno hspec
      · intro evs c' hss
        cases hss with
        | sstep_instr _ _ _ _ _ hsvc' _ => rw [hsvc] at hsvc'; cases hsvc'
        | sstep_syscall _ _ x8' _ _ _ _ _ hsvc' hspec hh' _ =>
          rw [hsvc] at hsvc'
          cases hsvc'
          rw [exit_dispatch_halts _ _ _ _ _ hno hspec] at hh'
          cases hh'
        | sstep_exit _ _ x8' _ model' _ _ _ hsvc' hspec hh' hk =>
          rw [hsvc] at hsvc'
          cases hsvc'
          obtain ⟨_, rfl, rfl⟩ := exit_dispatch_forced _ _ _ _ _ hno hspec
          rw [m_halted_with_halted] at hh'
          cases hh'
          apply exec.exec_halt
          · show m_halted (with_halted _ model) ≠ none
            rw [m_halted_with_halted]
            intro h
            cases h
          · refine ⟨?_, ?_⟩
            · show [ExitEv _ (m_fs (with_halted _ model))] = [ExitEv code (m_fs model)]
              rw [m_fs_with_halted, hv]
            · exact ⟨(m_halted_with_halted _ _).trans (congrArg some hv), hk⟩
        | sstep_killed _ _ x8' _ _ _ _ _ hsvc' hspec hk =>
          rw [hsvc] at hsvc'
          cases hsvc'
          rw [exit_dispatch_not_killed _ _ _ _ _ hno hspec] at hk
          cases hk
    | none =>
      simp only [exits_c, hsvc] at hc
      cases hstep : RiscvSemantics.step segs ms with
      | MachineOk ms' =>
        simp only [hstep] at hc
        exact exec_step_only segs _ _ [] (config.mkCfg ms' model)
          (sstep.sstep_instr ms model ms' model hh hsvc
            (by rw [mi_account_step_no_lazy _ _ _ hlazy, hstep]))
          (sstep_instr_only segs ms model ms' hlazy hsvc hstep)
          (exec_conseq _ _ _ _ (ih ms' model hh hlazy hc) (fun _ _ h => h))
      | MachineFault => simp only [hstep, Bool.false_eq_true] at hc
      | MachineUnmodeled => simp only [hstep, Bool.false_eq_true] at hc

/-- Lean-only: the exit-0 image's three fetches, decided by the kernel.
With them and the two decodes after them each instruction steps an
abstract `mkst r pc m rom`, which is how `exit0_exits_c` never evaluates
the initial state's memory. -/
theorem exit0_fetch_100 : fetch_word exit0_segments 0x100 = some 0x05d00893 := by decide +kernel
theorem exit0_fetch_104 : fetch_word exit0_segments 0x104 = some 0x00000513 := by decide +kernel
theorem exit0_fetch_108 : fetch_word exit0_segments 0x108 = some 0x00000073 := by decide +kernel

/-- Lean-only: `addi a7, x0, 93` and `addi a0, x0, 0`, decoded. -/
theorem decode_addi_a7_93 : decode_any 0x05d00893 = some (.OpImm .ALU_ADD 17 0 0x5d, 4) := by
  decide +kernel
theorem decode_addi_a0_0 : decode_any 0x00000513 = some (.OpImm .ALU_ADD 10 0 0, 4) := by
  decide +kernel

/-- Lean-only: the exit-0 image's three instructions as steps of an
abstract state — two register writes, then the ecall, which only marks
the syscall pending. -/
theorem exit0_step_100 (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step exit0_segments (mkst r 0x100 m rom) =
      MachineOk (mkst (bvmap_set 17 93 r) 0x104 m rom) := by
  rw [step_of_fetch exit0_segments (mkst r 0x100 m rom) 0x05d00893 exit0_fetch_100]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.OpImm .ALU_ADD 17 0 0x5d)
    (by decide +kernel) decode_addi_a7_93
  rfl

theorem exit0_step_104 (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step exit0_segments (mkst r 0x104 m rom) =
      MachineOk (mkst (bvmap_set 10 0 r) 0x108 m rom) := by
  rw [step_of_fetch exit0_segments (mkst r 0x104 m rom) 0x00000513 exit0_fetch_104]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.OpImm .ALU_ADD 10 0 0)
    (by decide +kernel) decode_addi_a0_0
  rfl

theorem exit0_step_108 (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step exit0_segments (mkst r 0x108 m rom) =
      MachineOk { mkst r 0x108 m rom with ms_svc_pending := some (reg_get r 17) } := by
  rw [step_of_fetch exit0_segments (mkst r 0x108 m rom) 0x00000073 exit0_fetch_108]
  rfl

/-- Lean-only: `exits_c` spends one unit of fuel on an instruction step. -/
theorem exits_c_step (segs : List Segment) (code : word) (fuel : Nat) (ms ms' : machine_state)
    (hs : RiscvSemantics.step segs ms = MachineOk ms') (hsvc : ms.ms_svc_pending = none) :
    exits_c segs code (fuel + 1) ms = exits_c segs code fuel ms' := by
  simp only [exits_c, hsvc, hs]

/-- Lean-only: at a pending ecall `exits_c` reads a7 and a0 and nothing
else. -/
theorem exits_c_ecall (segs : List Segment) (code : word) (fuel : Nat) (r : bvmap 5 word)
    (pc : word) (m rom : word → Option byte) :
    exits_c segs code (fuel + 1) { mkst r pc m rom with ms_svc_pending := some (reg_get r 17) } =
      ((decide (bv_unsigned (reg_get r 17) = 93) || decide (bv_unsigned (reg_get r 17) = 94))
        && bv_eqb (bv_and (reg_get r (Z_to_bv 5 (10 + ((0 : Nat) : Int)))) (Z_to_bv 64 255)) code) := by
  rfl

/-- Lean-only: the walk `exit0_exits_c` asks for, over an abstract state
at the entry pc. -/
theorem exit0_exits_c_mkst (r : bvmap 5 word) (m rom : word → Option byte) :
    exits_c exit0_segments verdict_accept 8 (mkst r 0x100 m rom) = true := by
  rw [exits_c_step _ _ 7 _ _ (exit0_step_100 r m rom) rfl,
    exits_c_step _ _ 6 _ _ (exit0_step_104 _ m rom) rfl,
    exits_c_step _ _ 5 _ _ (exit0_step_108 _ m rom) rfl,
    exits_c_ecall]
  have ha0 : (Z_to_bv 5 (10 + ((0 : Nat) : Int)) : BitVec 5) = 10 := by decide
  have h1017 : (10 : BitVec 5) ≠ 17 := by decide
  rw [ha0]
  simp only [reg_get, bvmap_get_set_same, bvmap_get_set_other _ _ _ _ h1017]
  decide

/-- Lean-only: the entry pc as `init_machine_state` spells it. -/
theorem entry_pc_0x100 : (Z_to_bv 64 ((0x100 : Nat) : Int) : word) = 0x100 := by decide

/-- The exit-0 image runs the same way from EVERY `execve` placement and
on EVERY input: it makes no memory access beyond its own fetches, and the
fetch reads the segment image, which no placement touches.  Stated with
the stack memory abstracted, exactly so that evaluation never has to look
at it.  (Rocq: `exit0_exits_c`.) -/
theorem exit0_exits_c (sp : word) (rnd : EntryDraw) (argv envp : List (List byte)) (uid hw : word) :
    exits_c exit0_segments verdict_accept 8
      (init_machine_state exit0_segments 0x100 demo_phdrs sp rnd argv envp uid hw) = true := by
  rw [init_mkst, entry_pc_0x100]
  exact exit0_exits_c_mkst _ _ _

/-- One omni judgment for the whole image: every execution halts with
code 0 after emitting exactly the exit event, at any budget.
(Rocq: `exit0_exec`.) -/
theorem exit0_exec (sp brk0 mbase : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput) :
    exec exit0_segments (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp)
      (fun tr o => tr = [ExitEv verdict_accept inp.in_fs] ∧ exits_with verdict_accept tr o) :=
  exits_c_exec exit0_segments verdict_accept 8
    (init_machine_state exit0_segments 0x100 demo_phdrs sp rnd inp.in_argv inp.in_envp inp.in_uid
      inp.in_hwcap)
    (init_model (segments_reserved exit0_segments) brk0 mbase sp lim inp)
    rfl rfl (exit0_exits_c _ _ _ _ _ _)

/-- What the one judgment yields: the exact trace set…  (Rocq: `exit0_obs`.) -/
theorem exit0_obs (sp brk0 mbase : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (tr : List event) :
    obs_trace exit0_segments (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp) tr
      ↔ is_prefix tr [ExitEv verdict_accept inp.in_fs] :=
  exec_obs_iff _ _ _ (exec_conseq _ _ _ _ (exit0_exec sp brk0 mbase rnd lim inp)
    (fun _ _ h => ⟨h.1, exits_with_never_errors _ _ _ h.2⟩)) tr

/-- …and error-freedom, hence coverage.  (Rocq: `exit0_never_errors`.) -/
theorem exit0_never_errors (sp brk0 mbase : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput) :
    coexec exit0_segments (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp)
      never_errors :=
  exec_coexec _ _ _ (exec_conseq _ _ _ _ (exit0_exec sp brk0 mbase rnd lim inp)
    (fun _ _ h => exits_with_never_errors _ _ _ h.2))

/-- The per-triple obligation, at EVERY input rather than only at a valid
one.  The proof reads none of the three validity premises — the image
never touches the stack or the heap — so stating it without them is not a
strengthening anyone has to check, it is what the proof already
establishes.  Rocq splits it out because its quantifier shells differ in
the validity predicate they name — `Run.valid_input`, `valid_input_abort`
and `valid_input_either` — and one fact discharges them all.  The Lean
equivalence statements name only `valid_input`, since the other two shells
are not ported, and the split is kept so that the statement is Rocq's.
(Rocq: `exit0_omni_strong_equiv_any`.) -/
theorem exit0_omni_strong_equiv_any (en_source en_target : ExecEntry) (inp : ProcInput) :
    omni_strong_equiv exit0_image exit0_image en_source en_target inp := by
  obtain ⟨sps, brks, mbs, rnds⟩ := en_source
  obtain ⟨spt, brkt, mbt, rndt⟩ := en_target
  refine ⟨coexec_conseq _ _ _ _ (exit0_never_errors _ _ _ _ _ _) (never_errors_covered _),
    Or.inr ⟨?_, exit0_never_errors _ _ _ _ _ _⟩⟩
  intro P hpc
  show cosafe exit0_segments
      (init_config exit0_segments 0x100 demo_phdrs sps brks mbs rnds source_alloc_limit inp) P ↔
    cosafe exit0_segments
      (init_config exit0_segments 0x100 demo_phdrs spt brkt mbt rndt target_alloc_limit inp) P
  rw [cosafe_obs_iff _ _ P hpc, cosafe_obs_iff _ _ P hpc]
  simp only [exit0_obs]

/-- UNIVERSALLY QUANTIFIED and COMPARING TWO RUNS: a concrete pair on
which `OmniEquivalence.omni_strong_universal_T` HOLDS.  It is not free —
the two roles run at different budgets, and the statement ranges over
every valid placement of each side and every valid input — and it needs
none of the three validity premises, because the image never touches the
stack or the heap.  (Rocq: `exit0_omni_strong_universal`.) -/
theorem exit0_omni_strong_universal : omni_strong_universal_T exit0_image exit0_image :=
  fun es et inp _ _ _ => exit0_omni_strong_equiv_any es et inp

/-- The legacy statement, through the `iff`: this is the whole of what a
consumer does to discharge `Equivalence.strong_universal_T` from an omni
proof.  (Rocq: `exit0_strong_universal`.) -/
theorem exit0_strong_universal : strong_universal_T exit0_image exit0_image :=
  (strong_universal_iff _ _).2 exit0_omni_strong_universal

/-- The same, at the level a checker ascribes: the omni proof seals
`OmniEquivalence.OMNI_SPEC`.  (Rocq: the module `Exit0OmniChecked`, over
the module `Exit0Image`, which packages the segments, entry pc and
program headers that `Checks.Examples.exit0_image` holds as one term.) -/
theorem exit0_omni_checked : OMNI_SPEC exit0_image exit0_image := ⟨exit0_omni_strong_universal⟩

/-- …and `Equivalence.SPEC` follows without a new proof.  (Rocq: the module
`Exit0Checked`, `SpecOfOmni` applied.  That functor has no Lean twin; its
body is the one application of `strong_universal_iff` written here.) -/
theorem exit0_checked : SPEC exit0_image exit0_image :=
  ⟨(strong_universal_iff _ _).2 exit0_omni_checked.omni_strong_universal⟩

/-- The legacy per-triple statement, at every input.
(Rocq: `exit0_strong_equiv_any`, which Rocq's abort shells consume.) -/
theorem exit0_strong_equiv_any (en_source en_target : ExecEntry) (inp : ProcInput) :
    strong_equiv exit0_image exit0_image en_source en_target inp :=
  (strong_equiv_iff _ _ _ _ _).2 (exit0_omni_strong_equiv_any en_source en_target inp)

/-- The run never errors, at any budget, from any entry, on any input.
(Rocq: `exit0_error_free_run`.) -/
theorem exit0_error_free_run (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    error_free (run exit0_image lim en inp) := by
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact (error_free_iff _ _ _ _).2 (exit0_never_errors _ _ _ _ _ _)

/-- The classifier-side reading: `MustExit.must_exit_with` at the demo
entry, in both directions of `OmniEquivalence.must_exit_with_iff`.
(Rocq: `exit0_omni_exits_zero`.) -/
theorem exit0_omni_exits_zero :
    omni_run exit0_image demo_limit demo_entry demo_proc_input (exits_with verdict_accept) :=
  (must_exit_with_iff _ _ _ _ _).1 exit0_image_must_exit_zero

/-- The same reading from the omni judgment directly.
(Rocq: `exit0_omni_exits_zero_direct`.) -/
theorem exit0_omni_exits_zero_direct :
    omni_run exit0_image demo_limit demo_entry demo_proc_input (exits_with verdict_accept) :=
  exec_conseq _ _ _ _ (exit0_exec _ _ _ _ _ _) (fun _ _ h => h.2)

/-- …and back to the legacy statement.  (Rocq: `exit0_omni_exits_zero_legacy`.) -/
theorem exit0_omni_exits_zero_legacy :
    must_exit_with verdict_accept exit0_image demo_limit demo_entry demo_proc_input :=
  (must_exit_with_iff _ _ _ _ _).2 exit0_omni_exits_zero_direct

/-- The wrong code is refuted: `exits_with` is not "halts".
(Rocq: `exit0_omni_not_exits_one`.) -/
theorem exit0_omni_not_exits_one :
    ¬ omni_run exit0_image demo_limit demo_entry demo_proc_input (exits_with verdict_reject) := by
  intro h
  obtain ⟨tr, o, hm, hx⟩ := exec_realizes _ _ _ h
  have hx0 := (exec_sound _ _ _ (exit0_exec _ _ _ _ _ _) _ _ hm).2
  cases o with
  | OError c => exact hx
  | OHalt c =>
    have h1 : m_halted c.cfg_model = some verdict_reject := hx.1
    have h0 : m_halted c.cfg_model = some verdict_accept := hx0.1
    rw [h0] at h1
    exact absurd (Option.some.inj h1) (by decide)

/-! ## Part 4 — a modeled crash separates the three error postconditions

Rocq: `Checks/Omni.v`'s Part 4.  The module header says which two of its
theorems wait, and on what. -/

/-- One `ebreak` at 0x100 (0x00100073, little-endian): a fault the model
MODELS — a real process dies there too — as opposed to the undecodable
word, where the model gives up.  In the kernel a breakpoint trap from user
mode reaches `do_trap_break` and `handle_break` (arch/riscv/kernel/traps.c,
Linux v6.18.46), which send SIGTRAP with TRAP_BRKPT; this image installs no
handler, so the default action ends the process.  (Rocq: `ebreak_segment`.) -/
def ebreak_segment : Segment :=
  { seg_base := 0x100, seg_size := 4, seg_perms := "r-x", seg_bytes := ["73001000"] }

/-- (Rocq: `ebreak_segments`.) -/
def ebreak_segments : List Segment := [ebreak_segment]

/-- (Rocq: `ebreak_image`.) -/
def ebreak_image : Image := Image.mkImage ebreak_segments 0x100 demo_phdrs

/-- The image's initial machine state at the demo entry.  (Rocq: `ebreak_ms`.) -/
def ebreak_ms : machine_state :=
  init_machine_state ebreak_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000) demo_draw
    demo_proc_input.in_argv demo_proc_input.in_envp demo_proc_input.in_uid demo_proc_input.in_hwcap

/-- The image's initial model at the demo entry, at budget `lim`.
(Rocq: `ebreak_model`.) -/
def ebreak_model (lim : Int) : Model :=
  init_model (segments_reserved ebreak_segments) (Z_to_bv 64 0x1000)
    (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000) lim demo_proc_input

/-- (Rocq: `ebreak_config`.) -/
theorem ebreak_config (lim : Int) :
    init_config ebreak_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
      (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim demo_proc_input
    = config.mkCfg ebreak_ms (ebreak_model lim) := rfl

/-- The first step faults.  Rocq computes it by `vm_compute`; the Lean
elaborator evaluates it directly, since the `ebreak` reads no register.
(Rocq: `ebreak_faults`.) -/
theorem ebreak_faults : RiscvSemantics.step ebreak_segments ebreak_ms = MachineFault := by rfl

/-- (Rocq: `ebreak_only`.) -/
theorem ebreak_only (lim : Int) (evs : List event) (st : step_to)
    (hs : sstep ebreak_segments (config.mkCfg ebreak_ms (ebreak_model lim)) evs st) :
    evs = [] ∧ st = SError :=
  sstep_fault_only _ _ _ rfl rfl ebreak_faults evs st hs

/-- Every execution errors: the escape fires…  (Rocq: `ebreak_omni_errors`.) -/
theorem ebreak_omni_errors (lim : Int) :
    omni_run ebreak_image lim demo_entry demo_proc_input errors := by
  show exec ebreak_segments (init_config ebreak_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim demo_proc_input) errors
  rw [ebreak_config]
  apply exec.exec_step
  · rfl
  · refine ⟨[], SError, sstep.sstep_instr_fault _ _ rfl rfl ?_⟩
    no_lazy
    rw [ebreak_faults]
  · intro _ _
    exact True.intro
  · intro evs c' hs
    obtain ⟨_, habs⟩ := ebreak_only _ _ _ hs
    cases habs

/-- …the crash is COVERED, because the configuration it is taken from is
one the model has an answer for…  (Rocq: `ebreak_omni_covered`.) -/
theorem ebreak_omni_covered (lim : Int) :
    omni_corun ebreak_image lim demo_entry demo_proc_input (covered ebreak_segments) := by
  show coexec ebreak_segments (init_config ebreak_segments 0x100 demo_phdrs
    (Z_to_bv 64 0x7fff80000000) (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim
    demo_proc_input) (covered ebreak_segments)
  rw [ebreak_config]
  apply coexec.coexec_step
  · rfl
  · rintro evs _ ⟨_, ⟨_, hun⟩ | ⟨x8, hsvc, _⟩⟩
    · change mi_account_step ebreak_segments ebreak_ms (ebreak_model lim) = MachineUnmodeled at hun
      no_lazy_in hun
      rw [ebreak_faults] at hun
      cases hun
    · cases hsvc
  · intro evs c' hs
    obtain ⟨_, habs⟩ := ebreak_only _ _ _ hs
    cases habs

/-- …and it is NOT error-free: the three postconditions are distinct on a
real image.  (Rocq: `ebreak_omni_not_never_errors`.) -/
theorem ebreak_omni_not_never_errors (lim : Int) :
    ¬ omni_corun ebreak_image lim demo_entry demo_proc_input never_errors := by
  intro h
  change coexec ebreak_segments (init_config ebreak_segments 0x100 demo_phdrs
    (Z_to_bv 64 0x7fff80000000) (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim
    demo_proc_input) never_errors at h
  rw [ebreak_config] at h
  refine coexec_sound _ _ _ _ (mexec.mexec_error _ [] ?_) _ h True.intro
  apply sstep.sstep_instr_fault _ _ rfl rfl
  no_lazy
  rw [ebreak_faults]

/-- The escape, positively: a crashing source frees ANY target, even the
undecodable one, at this triple.  This is the per-triple shape of what the
deliberate-bug examples prove universally.
(Rocq: `ebreak_source_omni_strong_equiv_any`.) -/
theorem ebreak_source_omni_strong_equiv_any (T : Image) (et : ExecEntry) :
    omni_strong_equiv ebreak_image T demo_entry et demo_proc_input :=
  ⟨ebreak_omni_covered source_alloc_limit, Or.inl (ebreak_omni_errors source_alloc_limit)⟩

/-- (Rocq: `ebreak_frees_undecodable_target`.) -/
theorem ebreak_frees_undecodable_target :
    omni_strong_equiv ebreak_image undecodable_image demo_entry demo_entry demo_proc_input :=
  ebreak_source_omni_strong_equiv_any _ _

/-! ## Part 5 — `exec`/`coexec` agreement is strictly weaker than trace equality

Rocq: `Checks/Omni.v`'s Part 5.  Two images.  `loop`: one `jal x0, 0` at
0x100 (0x0000006f), the process spins forever and emits nothing.
`wloop`: `write(1, 0x100, 1)` — `addi a7, x0, 64; addi a0, x0, 1;
addi a1, x0, 0x100; addi a2, x0, 1; ecall` — then the same `jal x0, 0`:
one byte of its own code (0x93) reaches stdout, then the process spins
forever.

`loop` is `Checks/OmniPilot.lean`'s loop too: that file's `loop_segments`
and `loop_config` are this `loop_segments` and `loop_c demo_limit`, which
`Checks/Cases/Checks/Omni.lean` pins, so the two files run one image. -/

/-- (Rocq: `loop_segment`.) -/
def loop_segment : Segment :=
  { seg_base := 0x100, seg_size := 4, seg_perms := "r-x", seg_bytes := ["6f000000"] }

/-- (Rocq: `loop_segments`.) -/
def loop_segments : List Segment := [loop_segment]

/-- (Rocq: `loop_image`.) -/
def loop_image : Image := Image.mkImage loop_segments 0x100 demo_phdrs

/-- (Rocq: `wloop_segment`.) -/
def wloop_segment : Segment :=
  { seg_base := 0x100, seg_size := 24, seg_perms := "r-x",
    seg_bytes := ["93080004130510009305001013061000730000006f000000"] }

/-- (Rocq: `wloop_segments`.) -/
def wloop_segments : List Segment := [wloop_segment]

/-- (Rocq: `wloop_image`.) -/
def wloop_image : Image := Image.mkImage wloop_segments 0x100 demo_phdrs

/-- The byte the write delivers: the low byte of `addi a7, x0, 64`.
(Rocq: `wloop_byte`.) -/
def wloop_byte : byte := Z_to_bv 8 0x93

/-- (Rocq: `wloop_trace`.) -/
def wloop_trace : List event := [WriteEv (Z_to_bv 64 1) wloop_byte]

/-- (Rocq: `loop_ms`.) -/
def loop_ms : machine_state :=
  init_machine_state loop_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000) demo_draw
    demo_proc_input.in_argv demo_proc_input.in_envp demo_proc_input.in_uid demo_proc_input.in_hwcap

/-- (Rocq: `loop_model`.) -/
def loop_model (lim : Int) : Model :=
  init_model (segments_reserved loop_segments) (Z_to_bv 64 0x1000)
    (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000) lim demo_proc_input

/-- (Rocq: `loop_c`.) -/
def loop_c (lim : Int) : config := config.mkCfg loop_ms (loop_model lim)

/-- (Rocq: `loop_config`.) -/
theorem loop_config (lim : Int) :
    init_config loop_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
      (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim demo_proc_input
    = loop_c lim := rfl

/-- Lean-only: the loop's one fetch and its decode. -/
theorem loop_fetch_100 : fetch_word loop_segments 0x100 = some 0x0000006f := by decide +kernel
theorem decode_jal_x0_0 : decode_any 0x0000006f = some (.Jal 0 0, 4) := by decide +kernel

/-- Lean-only: `jal x0, 0` as a step of an abstract state. -/
theorem loop_step_100 (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step loop_segments (mkst r 0x100 m rom) = MachineOk (mkst r 0x100 m rom) := by
  rw [step_of_fetch loop_segments (mkst r 0x100 m rom) 0x0000006f loop_fetch_100]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.Jal 0 0) (by decide +kernel) decode_jal_x0_0
  rfl

/-- Lean-only: the loop's initial state with its memory abstracted is an
abstract state at the entry pc. -/
theorem loop_ms_with_mem (mem : word → Option byte) :
    with_mem loop_ms mem = mkst loop_ms.ms_regs 0x100 mem loop_ms.ms_rom := rfl

/-- `jal x0, 0` maps the initial state to itself: the pc gains 0 and the
write to x0 is dropped, so nothing changes.  With the memory abstracted,
both sides are the same term.  (Rocq: `loop_fix`.) -/
theorem loop_fix (mem : word → Option byte) :
    RiscvSemantics.step loop_segments (with_mem loop_ms mem) = MachineOk (with_mem loop_ms mem) := by
  rw [loop_ms_with_mem]
  exact loop_step_100 _ _ _

/-- (Rocq: `loop_only`.) -/
theorem loop_only (lim : Int) (evs : List event) (st : step_to)
    (hs : sstep loop_segments (loop_c lim) evs st) : evs = [] ∧ st = SNext (loop_c lim) :=
  sstep_instr_only loop_segments (with_mem loop_ms loop_ms.ms_mem) (loop_model lim)
    (with_mem loop_ms loop_ms.ms_mem) rfl rfl (loop_fix _) evs st hs

/-- (Rocq: `loop_coexec_any`.) -/
theorem loop_coexec_any (lim : Int) (Q : post) : coexec loop_segments (loop_c lim) Q :=
  fix_coexec_any loop_segments (loop_c lim) rfl (loop_only lim) Q

/-- (Rocq: `loop_no_exec`.) -/
theorem loop_no_exec (lim : Int) (Q : post) : ¬ exec loop_segments (loop_c lim) Q :=
  fix_no_exec loop_segments (loop_c lim) rfl (loop_only lim) Q

/-- (Rocq: `loop_obs_nil`.) -/
theorem loop_obs_nil (lim : Int) (tr : List event) (h : obs_trace loop_segments (loop_c lim) tr) :
    tr = [] :=
  fix_obs_nil loop_segments (loop_c lim) (loop_only lim) tr h

/-- The write-then-loop run, one transition at a time.  `run_steps` walks
the instruction stream; the states along it are named by their step
count, and every step lemma is stated with the memory abstracted.
(Rocq: `run_steps`.) -/
def run_steps (n : Nat) (segs : List Segment) (ms : machine_state) : Option machine_state :=
  match n with
  | 0 => some ms
  | n' + 1 =>
    match RiscvSemantics.step segs ms with
    | MachineOk ms' => run_steps n' segs ms'
    | MachineFault | MachineUnmodeled => none

/-- (Rocq: `wloop_ms0`.) -/
def wloop_ms0 : machine_state :=
  init_machine_state wloop_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000) demo_draw
    demo_proc_input.in_argv demo_proc_input.in_envp demo_proc_input.in_uid demo_proc_input.in_hwcap

/-- (Rocq: `wloop_msk`.) -/
def wloop_msk (k : Nat) : machine_state :=
  match run_steps k wloop_segments wloop_ms0 with
  | some ms => ms
  | none => wloop_ms0

/-- The state after `k` instructions, with the memory of the real initial
state — which no instruction of this image changes.  (Rocq: `wloop_s`.) -/
def wloop_s (k : Nat) : machine_state := with_mem (wloop_msk k) wloop_ms0.ms_mem

/-- (Rocq: `wloop_model`.) -/
def wloop_model (lim : Int) : Model :=
  init_model (segments_reserved wloop_segments) (Z_to_bv 64 0x1000)
    (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000) lim demo_proc_input

/-- (Rocq: `wloop_c`.) -/
def wloop_c (lim : Int) : config := config.mkCfg (wloop_s 0) (wloop_model lim)

/-- Rocq needs `with_mem_eta` for this; Lean's structure eta makes it
`rfl`.  (Rocq: `wloop_config`.) -/
theorem wloop_config (lim : Int) :
    init_config wloop_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
      (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim demo_proc_input
    = wloop_c lim := rfl

/-- The effect the write is forced to have: one byte copied in from 0x100,
one byte reported written.  (Rocq: `wloop_eff`.) -/
def wloop_eff : SyscallEffect :=
  with_copyins [(Z_to_bv 64 0x100, 1)] (mkEffect (Z_to_bv 64 1) [] [])

/-- After the syscall: the return value is in a0 and the pc sits on the
`jal`.  (Rocq: `wloop_s6`.) -/
def wloop_s6 : machine_state := advance_past_svc (apply_effect (wloop_s 5) wloop_eff)

/-- Lean-only: the write-then-loop image's six fetches. -/
theorem wloop_fetch_100 : fetch_word wloop_segments 0x100 = some 0x04000893 := by decide +kernel
theorem wloop_fetch_104 : fetch_word wloop_segments 0x104 = some 0x00100513 := by decide +kernel
theorem wloop_fetch_108 : fetch_word wloop_segments 0x108 = some 0x10000593 := by decide +kernel
theorem wloop_fetch_10c : fetch_word wloop_segments 0x10c = some 0x00100613 := by decide +kernel
theorem wloop_fetch_110 : fetch_word wloop_segments 0x110 = some 0x00000073 := by decide +kernel
theorem wloop_fetch_114 : fetch_word wloop_segments 0x114 = some 0x0000006f := by decide +kernel

/-- Lean-only: its four `addi`s, decoded. -/
theorem decode_addi_a7_64 : decode_any 0x04000893 = some (.OpImm .ALU_ADD 17 0 64, 4) := by
  decide +kernel
theorem decode_addi_a0_1 : decode_any 0x00100513 = some (.OpImm .ALU_ADD 10 0 1, 4) := by
  decide +kernel
theorem decode_addi_a1_0x100 : decode_any 0x10000593 = some (.OpImm .ALU_ADD 11 0 0x100, 4) := by
  decide +kernel
theorem decode_addi_a2_1 : decode_any 0x00100613 = some (.OpImm .ALU_ADD 12 0 1, 4) := by
  decide +kernel

/-- Lean-only: the six instructions as steps of an abstract state. -/
theorem wloop_step_100 (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step wloop_segments (mkst r 0x100 m rom)
    = MachineOk (mkst (bvmap_set 17 64 r) 0x104 m rom) := by
  rw [step_of_fetch wloop_segments (mkst r 0x100 m rom) 0x04000893 wloop_fetch_100]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.OpImm .ALU_ADD 17 0 64) (by decide +kernel)
    decode_addi_a7_64
  rfl

theorem wloop_step_104 (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step wloop_segments (mkst r 0x104 m rom)
    = MachineOk (mkst (bvmap_set 10 1 r) 0x108 m rom) := by
  rw [step_of_fetch wloop_segments (mkst r 0x104 m rom) 0x00100513 wloop_fetch_104]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.OpImm .ALU_ADD 10 0 1) (by decide +kernel)
    decode_addi_a0_1
  rfl

theorem wloop_step_108 (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step wloop_segments (mkst r 0x108 m rom)
    = MachineOk (mkst (bvmap_set 11 0x100 r) 0x10c m rom) := by
  rw [step_of_fetch wloop_segments (mkst r 0x108 m rom) 0x10000593 wloop_fetch_108]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.OpImm .ALU_ADD 11 0 0x100) (by decide +kernel)
    decode_addi_a1_0x100
  rfl

theorem wloop_step_10c (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step wloop_segments (mkst r 0x10c m rom)
    = MachineOk (mkst (bvmap_set 12 1 r) 0x110 m rom) := by
  rw [step_of_fetch wloop_segments (mkst r 0x10c m rom) 0x00100613 wloop_fetch_10c]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.OpImm .ALU_ADD 12 0 1) (by decide +kernel)
    decode_addi_a2_1
  rfl

theorem wloop_step_110 (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step wloop_segments (mkst r 0x110 m rom)
    = MachineOk { mkst r 0x110 m rom with ms_svc_pending := some (reg_get r 17) } := by
  rw [step_of_fetch wloop_segments (mkst r 0x110 m rom) 0x00000073 wloop_fetch_110]
  rfl

theorem wloop_step_114 (r : bvmap 5 word) (m rom : word → Option byte) :
    RiscvSemantics.step wloop_segments (mkst r 0x114 m rom) = MachineOk (mkst r 0x114 m rom) := by
  rw [step_of_fetch wloop_segments (mkst r 0x114 m rom) 0x0000006f wloop_fetch_114]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.Jal 0 0) (by decide +kernel) decode_jal_x0_0
  rfl

/-- Lean-only: `run_steps` past a step that answers. -/
theorem run_steps_ok (n : Nat) (segs : List Segment) (ms ms' : machine_state)
    (h : RiscvSemantics.step segs ms = MachineOk ms') :
    run_steps (n + 1) segs ms = run_steps n segs ms' := by
  simp only [run_steps, h]

/-- Lean-only: the first step from the real initial state. -/
theorem wloop_ms0_step :
    RiscvSemantics.step wloop_segments wloop_ms0
    = MachineOk (mkst (bvmap_set 17 64 wloop_ms0.ms_regs) 0x104 wloop_ms0.ms_mem
        wloop_ms0.ms_rom) :=
  wloop_step_100 wloop_ms0.ms_regs wloop_ms0.ms_mem wloop_ms0.ms_rom

/-- Lean-only: `wloop_msk k` for each `k` up to the ecall, as a register
file and a pc over the initial memory — the states Rocq's `vm_compute`
reaches, named so that a step lemma can be rewritten into them. -/
theorem wloop_msk_0 : wloop_msk 0 = mkst wloop_ms0.ms_regs 0x100 wloop_ms0.ms_mem wloop_ms0.ms_rom :=
  rfl

theorem wloop_msk_1 :
    wloop_msk 1 = mkst (bvmap_set 17 64 wloop_ms0.ms_regs) 0x104 wloop_ms0.ms_mem wloop_ms0.ms_rom := by
  unfold wloop_msk
  rw [run_steps_ok _ _ _ _ wloop_ms0_step]
  rfl

theorem wloop_msk_2 :
    wloop_msk 2 = mkst (bvmap_set 10 1 (bvmap_set 17 64 wloop_ms0.ms_regs)) 0x108 wloop_ms0.ms_mem
      wloop_ms0.ms_rom := by
  unfold wloop_msk
  rw [run_steps_ok _ _ _ _ wloop_ms0_step, run_steps_ok _ _ _ _ (wloop_step_104 _ _ _)]
  rfl

theorem wloop_msk_3 :
    wloop_msk 3 = mkst (bvmap_set 11 0x100 (bvmap_set 10 1 (bvmap_set 17 64 wloop_ms0.ms_regs)))
      0x10c wloop_ms0.ms_mem wloop_ms0.ms_rom := by
  unfold wloop_msk
  rw [run_steps_ok _ _ _ _ wloop_ms0_step, run_steps_ok _ _ _ _ (wloop_step_104 _ _ _),
    run_steps_ok _ _ _ _ (wloop_step_108 _ _ _)]
  rfl

theorem wloop_msk_4 :
    wloop_msk 4 = mkst (bvmap_set 12 1 (bvmap_set 11 0x100 (bvmap_set 10 1
      (bvmap_set 17 64 wloop_ms0.ms_regs)))) 0x110 wloop_ms0.ms_mem wloop_ms0.ms_rom := by
  unfold wloop_msk
  rw [run_steps_ok _ _ _ _ wloop_ms0_step, run_steps_ok _ _ _ _ (wloop_step_104 _ _ _),
    run_steps_ok _ _ _ _ (wloop_step_108 _ _ _), run_steps_ok _ _ _ _ (wloop_step_10c _ _ _)]
  rfl

theorem wloop_msk_5 :
    wloop_msk 5 =
      { mkst (bvmap_set 12 1 (bvmap_set 11 0x100 (bvmap_set 10 1
          (bvmap_set 17 64 wloop_ms0.ms_regs)))) 0x110 wloop_ms0.ms_mem wloop_ms0.ms_rom with
        ms_svc_pending := some (reg_get (bvmap_set 12 1 (bvmap_set 11 0x100 (bvmap_set 10 1
          (bvmap_set 17 64 wloop_ms0.ms_regs)))) 17) } := by
  unfold wloop_msk
  rw [run_steps_ok _ _ _ _ wloop_ms0_step, run_steps_ok _ _ _ _ (wloop_step_104 _ _ _),
    run_steps_ok _ _ _ _ (wloop_step_108 _ _ _), run_steps_ok _ _ _ _ (wloop_step_10c _ _ _),
    run_steps_ok _ _ _ _ (wloop_step_110 _ _ _)]
  rfl

/-- (Rocq: `wloop_step`.) -/
theorem wloop_step (k : Nat) (hk : k < 5) (mem : word → Option byte) :
    RiscvSemantics.step wloop_segments (with_mem (wloop_msk k) mem)
    = MachineOk (with_mem (wloop_msk (k + 1)) mem) := by
  match k, hk with
  | 0, _ => rw [wloop_msk_0, wloop_msk_1]; exact wloop_step_100 _ _ _
  | 1, _ => rw [wloop_msk_1, wloop_msk_2]; exact wloop_step_104 _ _ _
  | 2, _ => rw [wloop_msk_2, wloop_msk_3]; exact wloop_step_108 _ _ _
  | 3, _ => rw [wloop_msk_3, wloop_msk_4]; exact wloop_step_10c _ _ _
  | 4, _ => rw [wloop_msk_4, wloop_msk_5]; exact wloop_step_110 _ _ _
  | _ + 5, hk => exact absurd hk (by omega)

/-- (Rocq: `wloop_svc5`.) -/
theorem wloop_svc5 : (wloop_s 5).ms_svc_pending = some (Z_to_bv 64 64) := by
  unfold wloop_s
  rw [wloop_msk_5]
  decide +kernel

/-- Lean-only: the state after the syscall, as an abstract state at the
`jal`. -/
theorem wloop_s6_with_mem (mem : word → Option byte) :
    with_mem wloop_s6 mem =
      mkst (bvmap_set 10 (Z_to_bv 64 1) (bvmap_set 12 1 (bvmap_set 11 0x100 (bvmap_set 10 1
        (bvmap_set 17 64 wloop_ms0.ms_regs))))) 0x114 mem wloop_ms0.ms_rom := by
  unfold wloop_s6 wloop_s
  rw [wloop_msk_5]
  rfl

/-- (Rocq: `wloop_fix`.) -/
theorem wloop_fix (mem : word → Option byte) :
    RiscvSemantics.step wloop_segments (with_mem wloop_s6 mem) = MachineOk (with_mem wloop_s6 mem) := by
  rw [wloop_s6_with_mem]
  exact wloop_step_114 _ _ _

/-- Lean-only: nothing is pending before the ecall — the premise Rocq's
`wloop_instr_only` and `wloop_instr_sstep` discharge inline by
`vm_compute`. -/
theorem wloop_svc_none (k : Nat) (hk : k < 5) : (wloop_s k).ms_svc_pending = none := by
  unfold wloop_s
  match k, hk with
  | 0, _ => rw [wloop_msk_0]; rfl
  | 1, _ => rw [wloop_msk_1]; rfl
  | 2, _ => rw [wloop_msk_2]; rfl
  | 3, _ => rw [wloop_msk_3]; rfl
  | 4, _ => rw [wloop_msk_4]; rfl
  | _ + 5, hk => exact absurd hk (by omega)

/-- The five instruction transitions, each the only one from its
configuration.  (Rocq: `wloop_instr_only`.) -/
theorem wloop_instr_only (lim : Int) (k : Nat) (hk : k < 5) (evs : List event) (st : step_to)
    (hs : sstep wloop_segments (config.mkCfg (wloop_s k) (wloop_model lim)) evs st) :
    evs = [] ∧ st = SNext (config.mkCfg (wloop_s (k + 1)) (wloop_model lim)) :=
  sstep_instr_only wloop_segments (wloop_s k) (wloop_model lim) (wloop_s (k + 1)) rfl
    (wloop_svc_none k hk) (wloop_step k hk wloop_ms0.ms_mem) evs st hs

/-- (Rocq: `wloop_instr_sstep`.) -/
theorem wloop_instr_sstep (lim : Int) (k : Nat) (hk : k < 5) :
    sstep wloop_segments (config.mkCfg (wloop_s k) (wloop_model lim)) []
      (SNext (config.mkCfg (wloop_s (k + 1)) (wloop_model lim))) := by
  apply sstep.sstep_instr _ _ _ _ rfl (wloop_svc_none k hk)
  no_lazy
  rw [show RiscvSemantics.step wloop_segments (wloop_s k) = MachineOk (wloop_s (k + 1)) from
    wloop_step k hk _]

/-- At the ecall.  The dispatcher at number 64 IS the write spec…
(Rocq: `write_dispatch_iff`.) -/
theorem write_dispatch_iff (i : SyscallInput) (m : Model) (o : Monad.outcome SyscallEffect)
    (E : bv_unsigned i.in_sysno = 64) :
    syscall_spec i m o ↔ write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := by
  unfold syscall_spec dispatch
  rw [E]
  exact Iff.rfl

/-- Lean-only: the ecall's number, as the dispatcher reads it. -/
theorem wloop_sysno :
    bv_unsigned (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)).in_sysno = 64 := by
  decide

/-- Lean-only: the write's three arguments and its source bytes, each read
off the concrete machine state by the kernel for the reason the kit's
header gives, so that `check_write` can be evaluated with them rewritten
in. -/
theorem wloop_fd :
    fd32 (in_arg (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)) 0) = 1 := by
  decide +kernel
theorem wloop_buf : in_arg (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)) 1 = 0x100 := by
  decide +kernel
theorem wloop_count : in_arg (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)) 2 = 1 := by
  decide +kernel
theorem wloop_source :
    Sys.Uaccess.write_source (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)).in_mem 0x100 1
    = [wloop_byte] := by
  decide +kernel

/-- Lean-only: descriptor 1 of the loop's initial model is the channel
`init_model` gives standard output, which `check_write` looks up once the
arguments above are in.  A read off the model, which no step touches, so
it closes by `rfl`, as the kit's header says.  It is stated at budget 0
because the descriptor table does not depend on the budget: the two proofs
below first rewrite `m_fds (wloop_model lim)` to `m_fds (wloop_model 0)`,
which is `rfl`. -/
theorem wloop_stdout : fd_lookup (m_fds (wloop_model 0)) 1 = some (.FdChannel 1) := rfl

/-- Lean-only: the write arm's checker accepts the forced effect at the
arm's arguments — the application `Checks/Cases/Checks/Sys/Fs/ReadWrite.lean`
names `check_write_row`, and what `check_syscall` computes to once the arm
is found (`check_syscall_of_found`).  Part 5's proofs read this rather than
`wloop_checker`, so that they do not rest on the table. -/
theorem wloop_check_write (lim : Int) :
    check_write (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64))
      (fd32 (in_arg (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)) 0))
      (in_arg (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)) 1)
      (in_arg (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)) 2)
      wloop_eff (wloop_model lim)
    = CheckOk (wloop_model lim) wloop_trace := by
  have hfds : m_fds (wloop_model lim) = m_fds (wloop_model 0) := rfl
  generalize wloop_model lim = m at hfds ⊢
  unfold check_write
  rw [hfds, wloop_fd, wloop_buf, wloop_count, wloop_source, wloop_stdout]
  rfl

/-- The checker accepts the forced effect: Rocq's statement, over
`check_syscall`.  The dispatch finds the write arm at 64
(`Checks/Arms/Fs/ReadWrite.lean`'s `arm_write`), so the two lookups agree
there (`lookups_agree_at_of_found`), and the proof is the dispatch's
completeness at the answer `wloop_check_write` admits.
(Rocq: `wloop_checker`.) -/
theorem wloop_checker (lim : Int) :
    check_syscall (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)) wloop_eff
      (wloop_model lim)
    = CheckOk (wloop_model lim) wloop_trace :=
  check_syscall_complete_ok _ _ _ _ _
    (by rw [wloop_sysno]
        exact lookups_agree_at_of_found 64 arm_write lookup_ca_checked_table_write)
    ((write_dispatch_iff _ _ _ wloop_sysno).2
      (check_write_sound_ok _ _ _ _ _ _ _ _ (wloop_check_write lim)))

/-- …whose channel outcome is forced here: fd 1 is stdout, the buffer
holds one readable byte, so the delivery is that byte.  Rocq reads the
outcome off `Checks.Cases.Fs.ReadWrite.write_channel_outcome`, a lemma
over every input whose Lean twin (`channel_write_delivers_a_prefix_iff`)
is one fixture's instance and cannot be applied here.  The Lean route is
the write checker's completeness: the spec's answer is a `CheckOk` of
`check_write` at the arm's arguments (`check_write_complete_ok`), and with
this input's descriptor, buffer, count and bytes rewritten in, every
effect but `wloop_eff` evaluates to `CheckReject`.
(Rocq: `wloop_write_forced`.) -/
theorem wloop_write_forced (lim : Int) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (hspec : syscall_spec (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)) (wloop_model lim)
      (Ok eff m' evs)) :
    eff = wloop_eff ∧ m' = wloop_model lim ∧ evs = wloop_trace := by
  have h := check_write_complete_ok _ _ _ _ _ _ _ _
    ((write_dispatch_iff _ _ _ wloop_sysno).1 hspec)
  have hfds : m_fds (wloop_model lim) = m_fds (wloop_model 0) := rfl
  generalize wloop_model lim = m at hfds h ⊢
  unfold check_write at h
  rw [hfds, wloop_fd, wloop_buf, wloop_count, wloop_source, wloop_stdout] at h
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;>
    first
    | (have h2 : CheckReject = CheckOk m' evs := h; cases h2)
    | skip
  have h2 : (if (decide (1 ≤ bv_unsigned ret)
        && decide (bv_unsigned ret ≤ (([wloop_byte] : List byte).length : Int))) = true then
      if access_ranges_eqb cis [(0x100, (bv_unsigned ret).toNat)] = true
      then CheckOk m (List.map (WriteEv 1) (List.take (bv_unsigned ret).toNat [wloop_byte]))
      else CheckReject
    else CheckReject) = CheckOk m' evs := h
  split at h2
  · rename_i hr
    split at h2
    · rename_i hc
      injection h2 with hm hevs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      have hn : (ret.toNat : Int) = 1 := by
        unfold bv_unsigned at hr
        simp only [List.length_cons, List.length_nil] at hr
        omega
      have hret : ret = Z_to_bv 64 1 := by
        apply BitVec.eq_of_toNat_eq
        have h1 : ret.toNat = 1 := by exact_mod_cast hn
        rw [h1]
        decide
      subst hret
      have hcis := (access_ranges_eqb_eq _ _).1 hc
      subst hcis hm hevs
      exact ⟨rfl, rfl, rfl⟩
    · cases h2
  · cases h2

/-- The syscall transition…  (Rocq: `wloop_syscall_sstep`.) -/
theorem wloop_syscall_sstep (lim : Int) :
    sstep wloop_segments (config.mkCfg (wloop_s 5) (wloop_model lim)) wloop_trace
      (SNext (config.mkCfg wloop_s6 (wloop_model lim))) :=
  sstep.sstep_syscall _ _ _ _ _ _ _ rfl wloop_svc5
    ((write_dispatch_iff _ _ _ wloop_sysno).2
      (check_write_sound_ok _ _ _ _ _ _ _ _ (wloop_check_write lim)))
    rfl (materialize_model_accesses_no_lazy _ _ rfl)

/-- …and that it is the only one.  (Rocq: `wloop_syscall_only`.) -/
theorem wloop_syscall_only (lim : Int) (evs : List event) (st : step_to)
    (hs : sstep wloop_segments (config.mkCfg (wloop_s 5) (wloop_model lim)) evs st) :
    evs = wloop_trace ∧ st = SNext (config.mkCfg wloop_s6 (wloop_model lim)) := by
  have hsvc := wloop_svc5
  cases hs with
  | sstep_instr _ _ _ _ _ hv _ => rw [hsvc] at hv; cases hv
  | sstep_instr_fault _ _ _ hv _ => rw [hsvc] at hv; cases hv
  | sstep_instr_unmodeled _ _ _ hv _ => rw [hsvc] at hv; cases hv
  | sstep_syscall _ _ x8 eff m1 m2 evs1 _ hv hspec _ hmat =>
    rw [hsvc] at hv
    cases hv
    obtain ⟨rfl, rfl, rfl⟩ := wloop_write_forced _ _ _ _ hspec
    no_lazy_materialize_in hmat
    cases hmat
    exact ⟨rfl, rfl⟩
  | sstep_syscall_materialization_fault _ _ x8 eff m1 evs1 _ hv hspec _ hmat =>
    rw [hsvc] at hv
    cases hv
    obtain ⟨rfl, rfl, rfl⟩ := wloop_write_forced _ _ _ _ hspec
    no_lazy_materialize_in hmat
    cases hmat
  | sstep_exit _ _ x8 eff m1 evs1 code _ hv hspec hh _ =>
    rw [hsvc] at hv
    cases hv
    obtain ⟨_, rfl, _⟩ := wloop_write_forced _ _ _ _ hspec
    cases hh
  | sstep_killed _ _ x8 eff m1 evs1 sig _ hv hspec hk =>
    rw [hsvc] at hv
    cases hv
    obtain ⟨_, rfl, _⟩ := wloop_write_forced _ _ _ _ hspec
    cases hk
  | sstep_syscall_unmodeled _ _ x8 _ hv hspec =>
    rw [hsvc] at hv
    cases hv
    have hc := check_write_complete_unmodeled _ _ _ _ wloop_eff _
      ((write_dispatch_iff _ _ _ wloop_sysno).1 hspec)
    rw [wloop_check_write] at hc
    cases hc

/-- (Rocq: `wloop_s6_only`.) -/
theorem wloop_s6_only (lim : Int) (evs : List event) (st : step_to)
    (hs : sstep wloop_segments (config.mkCfg wloop_s6 (wloop_model lim)) evs st) :
    evs = [] ∧ st = SNext (config.mkCfg wloop_s6 (wloop_model lim)) :=
  sstep_instr_only wloop_segments (with_mem wloop_s6 wloop_s6.ms_mem) (wloop_model lim)
    (with_mem wloop_s6 wloop_s6.ms_mem) rfl rfl (wloop_fix _) evs st hs

/-- The one maximal-looking path: five silent steps, the write, then the
fixpoint.  (Rocq: `wloop_star`.) -/
theorem wloop_star (lim : Int) :
    star wloop_segments (wloop_c lim) wloop_trace (config.mkCfg wloop_s6 (wloop_model lim)) := by
  change star wloop_segments (config.mkCfg (wloop_s 0) (wloop_model lim))
    ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ (wloop_trace ++ [])))))) _
  refine star.star_step _ _ _ _ _ (wloop_instr_sstep lim 0 (by decide)) ?_
  refine star.star_step _ _ _ _ _ (wloop_instr_sstep lim 1 (by decide)) ?_
  refine star.star_step _ _ _ _ _ (wloop_instr_sstep lim 2 (by decide)) ?_
  refine star.star_step _ _ _ _ _ (wloop_instr_sstep lim 3 (by decide)) ?_
  refine star.star_step _ _ _ _ _ (wloop_instr_sstep lim 4 (by decide)) ?_
  refine star.star_step _ _ _ _ _ (wloop_syscall_sstep lim) ?_
  exact star.star_refl _

/-- Every `coexec` postcondition holds of the write-then-loop run: no
execution ends.  (Rocq: `wloop_coexec_any`.) -/
theorem wloop_coexec_any (lim : Int) (Q : post) : coexec wloop_segments (wloop_c lim) Q := by
  refine coexec_step_only _ _ _ _ _ (wloop_instr_sstep lim 0 (by decide))
    (wloop_instr_only lim 0 (by decide)) ?_
  refine coexec_step_only _ _ _ _ _ (wloop_instr_sstep lim 1 (by decide))
    (wloop_instr_only lim 1 (by decide)) ?_
  refine coexec_step_only _ _ _ _ _ (wloop_instr_sstep lim 2 (by decide))
    (wloop_instr_only lim 2 (by decide)) ?_
  refine coexec_step_only _ _ _ _ _ (wloop_instr_sstep lim 3 (by decide))
    (wloop_instr_only lim 3 (by decide)) ?_
  refine coexec_step_only _ _ _ _ _ (wloop_instr_sstep lim 4 (by decide))
    (wloop_instr_only lim 4 (by decide)) ?_
  refine coexec_step_only _ _ _ _ _ (wloop_syscall_sstep lim) (wloop_syscall_only lim) ?_
  exact fix_coexec_any _ _ rfl (wloop_s6_only lim) _

/-- …and no `exec` postcondition does.  (Rocq: `wloop_no_exec`.) -/
theorem wloop_no_exec (lim : Int) (Q : post) : ¬ exec wloop_segments (wloop_c lim) Q := by
  intro hex
  exact fix_no_exec wloop_segments (config.mkCfg wloop_s6 (wloop_model lim)) rfl (wloop_s6_only lim)
    _ (exec_star _ _ _ _ _ hex (wloop_star lim))

/-- (Rocq: `wloop_obs_write`.) -/
theorem wloop_obs_write (lim : Int) : obs_trace wloop_segments (wloop_c lim) wloop_trace :=
  ⟨wloop_trace, config.mkCfg wloop_s6 (wloop_model lim), wloop_star lim, is_prefix_refl _⟩

/-- The finding, pinned.  COMPARES TWO RUNS, at either budget on each
side.  The two runs satisfy exactly the same `coexec` postconditions and
exactly the same `exec` postconditions…  (Rocq: `loop_wloop_coexec_agree`.) -/
theorem loop_wloop_coexec_agree (lim1 lim2 : Int) (Q : post) :
    coexec loop_segments (loop_c lim1) Q ↔ coexec wloop_segments (wloop_c lim2) Q :=
  ⟨fun _ => wloop_coexec_any _ _, fun _ => loop_coexec_any _ _⟩

/-- (Rocq: `loop_wloop_exec_agree`.) -/
theorem loop_wloop_exec_agree (lim1 lim2 : Int) (Q : post) :
    exec loop_segments (loop_c lim1) Q ↔ exec wloop_segments (wloop_c lim2) Q :=
  ⟨fun h => absurd h (loop_no_exec _ _), fun h => absurd h (wloop_no_exec _ _)⟩

/-- …yet their trace sets differ, so `cosafe` tells them apart…
(Rocq: `loop_wloop_cosafe_disagree`.) -/
theorem loop_wloop_cosafe_disagree (lim1 lim2 : Int) :
    ¬ (∀ P, prefix_closed P →
        (cosafe loop_segments (loop_c lim1) P ↔ cosafe wloop_segments (wloop_c lim2) P)) := by
  intro H
  have hnil := (H _ prefix_closed_nil).1
    (star_cosafe _ _ _ (fun tr c' hstar => (fix_star_nil _ _ (loop_only lim1) tr c' hstar).1))
  have hw : wloop_trace = [] :=
    cosafe_star wloop_segments (wloop_c lim2) (fun tr => tr = []) wloop_trace _ hnil (wloop_star lim2)
  cases hw

/-- (Rocq: `loop_wloop_not_trace_equiv`.) -/
theorem loop_wloop_not_trace_equiv (lim1 lim2 : Int) :
    ¬ (∀ tr, obs_trace loop_segments (loop_c lim1) tr ↔ obs_trace wloop_segments (wloop_c lim2) tr) :=
  fun H => loop_wloop_cosafe_disagree lim1 lim2 ((obs_equiv_iff_cosafe _ _ _ _).1 H)

/-- …and so does the run-level equivalence, in both shapes: the omni
statement through the `iff`, the legacy one directly — this is Rocq's
`Checks.Examples.write_then_diverge_vs_diverge` on two real images.
(Rocq: `loop_wloop_not_omni_trace_equiv`.) -/
theorem loop_wloop_not_omni_trace_equiv :
    ¬ omni_trace_equiv loop_image source_alloc_limit demo_entry
        wloop_image target_alloc_limit demo_entry demo_proc_input :=
  fun H => loop_wloop_cosafe_disagree source_alloc_limit target_alloc_limit H

/-- (Rocq: `loop_wloop_not_omni_equiv`.) -/
theorem loop_wloop_not_omni_equiv :
    ¬ omni_equiv loop_image source_alloc_limit demo_entry
        wloop_image target_alloc_limit demo_entry demo_proc_input := by
  rintro (hall | ⟨htr, _⟩)
  · exact loop_no_exec source_alloc_limit errors hall
  · exact loop_wloop_not_omni_trace_equiv htr

/-- (Rocq: `loop_wloop_not_equiv`.) -/
theorem loop_wloop_not_equiv :
    ¬ equiv (run loop_image source_alloc_limit demo_entry demo_proc_input)
        (run wloop_image target_alloc_limit demo_entry demo_proc_input) :=
  fun H => loop_wloop_not_omni_equiv ((equiv_iff _ _ _ _ _ _ _).1 H)

/-- Neither image errors or leaves the model, so what separates them is
the byte and nothing else: both sides of `OmniEquivalence.omni_strong_equiv`
other than the trace conjunct hold.  (Rocq: `loop_wloop_never_errors`.) -/
theorem loop_wloop_never_errors (lim : Int) :
    omni_corun loop_image lim demo_entry demo_proc_input never_errors
    ∧ omni_corun wloop_image lim demo_entry demo_proc_input never_errors :=
  ⟨loop_coexec_any lim never_errors, wloop_coexec_any lim never_errors⟩

/-- The process input the statements below run on is a valid one — one
empty argument, no environment, an empty file system, end of input.
Needed for the same reason the entry validity is: the obligations
quantify over VALID inputs, so a refutation naming an invalid one would
refute nothing.  (Rocq: `Checks.Examples.demo_input_valid`, which
`Checks/Examples.lean` has not ported.  It is proved here, beside its one
reader, and belongs there when that file ports it.) -/
theorem demo_input_valid : valid_input demo_proc_input := by
  have hargv : valid_argv demo_proc_input.in_argv := by unfold valid_argv; decide
  have henvp : valid_envp demo_proc_input.in_envp := by unfold valid_envp; decide
  have hfs : Fs.valid_fs demo_proc_input.in_fs := by unfold Fs.valid_fs; decide
  have himg : Fs.fs_keys_relative demo_proc_input.in_image_fs := by
    intro pf hpf
    cases hpf
  have hcreds : valid_creds demo_proc_input := by unfold valid_creds valid_id; decide
  have hnofile : valid_nofile demo_proc_input.in_nofile := by unfold valid_nofile; decide
  have hsig : valid_sigmask demo_proc_input := by unfold valid_sigmask; decide
  have hhw : valid_hwcap demo_proc_input.in_hwcap := Or.inl rfl
  have habort : demo_proc_input.in_abort_terminal = false := rfl
  have hva : demo_proc_input.in_va_size = .Sv48 := rfl
  have hur : valid_urandom demo_proc_input := default_urandom_infinite
  unfold valid_input
  repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-- Both images put their only segment inside the first page, so the demo
entry is valid for either — which is what makes the universal refutation
below a refutation at a VALID triple.  (Rocq: `demo_entry_valid_loop`.) -/
theorem demo_entry_valid_loop (inp : ProcInput) (hi : valid_input inp) :
    valid_entry loop_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_va_size inp hi)]
  have hargv : valid_argv inp.in_argv := by
    unfold valid_input at hi
    (repeat obtain ⟨_, hi⟩ := (hi : _ ∧ _))
    repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  have henvp : valid_envp inp.in_envp := by
    unfold valid_input at hi
    (repeat obtain ⟨_, hi⟩ := (hi : _ ∧ _))
    repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  refine ⟨by unfold valid_sp; decide +kernel,
    by unfold valid_brk; decide +kernel,
    by unfold valid_mmap_base; decide +kernel, ?_⟩
  have hspan := (entry_stack_span_bound _ _ hargv henvp).2
  change sp_window_lo + entry_stack_span inp.in_argv inp.in_envp ≤ sp_window_hi
  have hroom : sp_window_lo + entry_stack_span_max ≤ sp_window_hi := by decide +kernel
  omega

/-- (Rocq: `demo_entry_valid_wloop`.) -/
theorem demo_entry_valid_wloop (inp : ProcInput) (hi : valid_input inp) :
    valid_entry wloop_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_va_size inp hi)]
  have hargv : valid_argv inp.in_argv := by
    unfold valid_input at hi
    (repeat obtain ⟨_, hi⟩ := (hi : _ ∧ _))
    repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  have henvp : valid_envp inp.in_envp := by
    unfold valid_input at hi
    (repeat obtain ⟨_, hi⟩ := (hi : _ ∧ _))
    repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  refine ⟨by unfold valid_sp; decide +kernel,
    by unfold valid_brk; decide +kernel,
    by unfold valid_mmap_base; decide +kernel, ?_⟩
  have hspan := (entry_stack_span_bound _ _ hargv henvp).2
  change sp_window_lo + entry_stack_span inp.in_argv inp.in_envp ≤ sp_window_hi
  have hroom : sp_window_lo + entry_stack_span_max ≤ sp_window_hi := by decide +kernel
  omega

/-- (Rocq: `loop_wloop_refutes_omni_strong_universal`.) -/
theorem loop_wloop_refutes_omni_strong_universal :
    ¬ omni_strong_universal_T loop_image wloop_image := by
  intro H
  obtain ⟨_, heq⟩ := H demo_entry demo_entry demo_proc_input
    (demo_entry_valid_loop _ demo_input_valid) (demo_entry_valid_wloop _ demo_input_valid)
    demo_input_valid
  exact loop_wloop_not_omni_equiv heq

end LinuxProcessSemantics.LinuxProcessSem.Checks.Omni
