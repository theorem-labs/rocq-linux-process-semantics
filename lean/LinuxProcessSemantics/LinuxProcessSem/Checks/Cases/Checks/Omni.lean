import LinuxProcessSemantics.LinuxProcessSem.Checks.Omni
import LinuxProcessSemantics.LinuxProcessSem.Checks.OmniPilot
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Run
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Sys

/-! # Checks.Cases.Checks.Omni — receptiveness on the run relation, exercised

Pins over `Checks.Omni`, the twin of Parts 1, 2, 4 and 5 of
`theories/LinuxProcessSem/Checks/Omni.v`.  Rocq has no check file for it:
`sstep_receptive` is a theorem there and needs no test, and Parts 2, 4
and 5 are checks themselves, each a theorem accepting or refuting a
concrete image.  What needs a pin is what the Lean twin adds — the case
analysis `sstep_of_syscall_spec` splits out of the theorem, the
hypothesis at the pending number the theorem inherits from
`Checks/Progress.lean`, the progress-carrying reading of `coexec` the file
defines rather than mirrors, and the routes Parts 2 and 5 take where
Rocq's cannot be followed.  For Part 1 this file runs each on a
configuration the reader can hold in one hand: a machine stopped at an
`ecall` (`Checks/Cases/Run.lean`'s `svc_ms`) over the demo process, for the
syscall half, and `Checks/OmniPilot.lean`'s one-instruction loop for the
reading.  The syscall configurations sit at `exit`, whose arm answers every
input and halts, at `getpid`, whose arm answers and continues, and at
`__NR_io_setup`, which no table carries, so that the answer's shapes — the
halting arm's, the continuing arm's and the decline — are shown to be a
step, and the decline is shown to be the ONLY step at its number.  The
loop shows the reading agreeing with `coexec` on a configuration that
never halts and never has a syscall pending, which is where the reading
is decided without the table hypothesis; the hypothesis itself is pinned
where it is defined, in `Checks/Cases/Checks/ExecutableSpecs.lean`, and
what this file adds about it is a pair at its `∀ n` form: agreement over
the real table through `lookups_agree_at_of_complete`, and refusal over
an empty fixture table that cannot supply the spec's `exit` arm.

Not part of the trusted specification: this file is QA on the
definitions, written to be READ.  Each decision gets an accepting and a
rejecting instance; where a kernel answer is in play the pin is stated
against the kernel and cites it, and where the claim is the twin's own —
a fixture table's run, the shape of a reading — the pin says so with a
`model:` line.  The `exit` and `getpid` pins cite `kernel/exit.c` and
`kernel/sys.c` because each states that the step the run relation takes
at that ecall is the one the arm's answer names; the numbers are cited
from the generic table, `include/uapi/asm-generic/unistd.h`.

The last three sections pin the routes, each with an accepting and a
rejecting instance: Part 2's `Equivalence.SPEC`, reached through
`strong_universal_iff` where Rocq applies a functor; Part 5's write,
through the dispatch that now finds the write arm at 64 and through that
arm's own checker;
and the one image `Checks/OmniPilot.lean` and Part 5 each define.
The pins resting on the loop's write cite the path its one byte takes,
`ksys_write` (fs/read_write.c, Linux v6.18.46) down to `anon_pipe_write`
(fs/pipe.c, Linux v6.18.46), the function the write checker's own pins on
standard output cite. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Omni

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch (lookup_arm dispatch)
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable (spec_table)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sys (getpid_spec)
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch (CheckedArm lookup_ca)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
  (checked_table arm_write ca_check_arm_write lookup_ca_checked_table_exit lookup_ca_checked_table_write)
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
  (lookups_agree_in lookups_agree_at lookups_agree_at_of_complete check_syscall check_syscall_of_found)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_result (CheckOk CheckReject)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
  (exit_dispatch_admits exit_dispatch_halts exit_dispatch_modeled syscall_spec_unmodeled_outside
    exit0_image)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.ExecutableSpecs
  (premise_fails_at_exit_over_the_empty_table)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch (fixture_arm_exit)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Sys (getpid_repeats_the_recorded_tid)
open LinuxProcessSemantics.LinuxProcessSem.Checks.OmniPilot
  (loop_segments loop_config loop_takes_silent_step loop_steps_only_to_itself loop_coexec_false)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Omni hiding loop_segments loop_config
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite (check_write check_write_sound_ok)
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence (SPEC)
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence (strong_universal_iff)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude (demo_model demo_limit)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Run (svc_ms)

/-! ## Every answer is a step

`sstep_of_syscall_spec` takes the dispatcher's answer at the pending
syscall, whatever produced it, and names the rule of `Run.sstep` that
consumes it.  Its five leaves are the five answering rules of `Run.sstep`;
the pins reach three — the halt at `exit`, the continuing answer at
`getpid`, and the decline at a number with no arm — and the killed answer
and the materialization fault wait on a fixture that produces them.  The
found-arm branch is reached twice: on the real table at `exit`, whose arm
is registered, and on a fixture table, which keeps the general
`sstep_receptive_over` exercised over a table the pin names itself. -/

/-- THE PIN: at an `exit` ecall the arm's answer is a step.  The answer is
`exit`'s own — it halts with the low byte of the status — and the rule is
`sstep_exit`; the theorem is handed the answer and finds the rule.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem the_exit_answer_is_a_step :
    ∃ evs st, sstep [] (config.mkCfg (svc_ms 93 0 0 0 0 0 0) demo_model) evs st :=
  sstep_of_syscall_spec [] _ demo_model 93 _ rfl rfl
    (exit_dispatch_admits (sys_input [] (svc_ms 93 0 0 0 0 0 0) 93) demo_model (Or.inl rfl))

/-- The decline is a step too: at `__NR_io_setup`, which neither table
carries, `sstep_receptive_unlisted` hands the dispatcher's decline to
`sstep_syscall_unmodeled`.  This is the branch the partial table takes at
every number it lacks, so it is the one exercised on the real table.
kernel: include/uapi/asm-generic/unistd.h:__NR_io_setup@v6.18.46 -/
theorem the_decline_at_io_setup_is_a_step :
    ∃ evs st, sstep [] (config.mkCfg (svc_ms 0 0 0 0 0 0 0) demo_model) evs st :=
  sstep_receptive_unlisted [] _ rfl (fun x8 hp => by
    have hx : 0 = x8 := Option.some.inj hp
    subst hx
    rfl)

/-- Rejected: at the unlisted number the ONLY step is the error, and it
carries no event.  Every other rule of `sstep` is refused: the three
instruction rules because a syscall is pending, and the four answering
rules because the dispatcher admits nothing but the decline outside the
list (`syscall_spec_unmodeled_outside`).
kernel: include/uapi/asm-generic/unistd.h:__NR_io_setup@v6.18.46 -/
theorem io_setup_steps_only_to_the_error (evs : List event) (st : step_to)
    (hs : sstep [] (config.mkCfg (svc_ms 0 0 0 0 0 0 0) demo_model) evs st) :
    evs = [] ∧ st = SError := by
  have hnin : bv_unsigned (sys_input [] (svc_ms 0 0 0 0 0 0 0) 0).in_sysno ∉ modeled_sysnos := by
    decide
  cases hs with
  | sstep_instr _ _ _ _ _ hp _ => exact absurd hp (by decide)
  | sstep_instr_fault _ _ _ hp _ => exact absurd hp (by decide)
  | sstep_instr_unmodeled _ _ _ hp _ => exact absurd hp (by decide)
  | sstep_syscall _ _ x8 _ _ _ _ _ hp hspec _ _ =>
    have hx : 0 = x8 := Option.some.inj hp
    subst hx
    cases syscall_spec_unmodeled_outside _ _ _ hnin hspec
  | sstep_syscall_materialization_fault _ _ x8 _ _ _ _ hp hspec _ _ =>
    have hx : 0 = x8 := Option.some.inj hp
    subst hx
    cases syscall_spec_unmodeled_outside _ _ _ hnin hspec
  | sstep_exit _ _ x8 _ _ _ _ _ hp hspec _ _ =>
    have hx : 0 = x8 := Option.some.inj hp
    subst hx
    cases syscall_spec_unmodeled_outside _ _ _ hnin hspec
  | sstep_killed _ _ x8 _ _ _ _ _ hp hspec _ =>
    have hx : 0 = x8 := Option.some.inj hp
    subst hx
    cases syscall_spec_unmodeled_outside _ _ _ hnin hspec
  | sstep_syscall_unmodeled _ _ _ _ _ _ => exact ⟨rfl, rfl⟩

/-- With nothing pending the machine steps by itself, under no table
hypothesis at all: the same machine with its `ecall` cleared.  What step it
takes is the fetch's business — here a fault, since the fixture has no
memory — and the theorem asks only that there is one.
model: `sstep_receptive_instr` at a configuration with no pending syscall; the step is the machine's own, and no kernel behaviour is claimed -/
theorem a_configuration_with_nothing_pending_steps :
    ∃ evs st, sstep []
      (config.mkCfg { svc_ms 0 0 0 0 0 0 0 with ms_svc_pending := none } demo_model) evs st :=
  sstep_receptive_instr [] _ rfl rfl

/-- The running fixture: the demo process with a tid recorded, which is
what `getpid` needs to answer. -/
def getpid_model : Model := with_tid (Z_to_bv 64 4242) demo_model

/-- Positive, on the continuing rule: at a `getpid` ecall over
`getpid_model` the arm answers the recorded tid with the model unchanged
and running, the effect writes nothing, so materialization is the identity
and `sstep_syscall` is the step — the leaf `the_exit_answer_is_a_step`
does not reach, an answer the run continues past.  The dispatch at 172 is
read by conversion: `syscall_spec` at that number IS `getpid_spec`.
kernel: kernel/sys.c:getpid@v6.18.46 -/
theorem the_getpid_answer_is_a_running_step :
    ∃ evs st, sstep [] (config.mkCfg (svc_ms 172 0 0 0 0 0 0) getpid_model) evs st :=
  ⟨[], _, sstep.sstep_syscall (svc_ms 172 0 0 0 0 0 0) getpid_model 172
    (mkEffect (Z_to_bv 64 4242) [] []) getpid_model getpid_model [] rfl rfl
    (by
      have E : bv_unsigned (sys_input [] (svc_ms 172 0 0 0 0 0 0) 172).in_sysno = 172 := rfl
      unfold syscall_spec dispatch
      rw [E]
      exact (getpid_repeats_the_recorded_tid _ getpid_model (Z_to_bv 64 4242) rfl _).mpr rfl)
    rfl (materialize_model_accesses_no_lazy getpid_model _ rfl)⟩

/-- The found-arm branch, on a fixture table: over `[fixture_arm_exit]` the
machine at an `exit` ecall steps by the FIXTURE's witness, with
`sstep_receptive_over` discharging the hypothesis at 93 by computation —
the two lookups agree there because the fixture's arm IS `spec_table`'s
(`Checks/Cases/Checks/ExecutableSpecs.lean`'s
`premise_holds_at_a_checked_number`).  The STATEMENT is
`the_exit_answer_is_a_step`'s to the letter; what differs is the route,
which no statement can pin — what this theorem holds is that the term
`sstep_receptive_over [fixture_arm_exit] …` elaborates with its hypothesis
discharged, so the branch is exercised.  `the_exit_arm_steps_its_ecall`
below reaches the same branch on the real table; this pin names its table
itself, so it does not move when the real one does.
model: `sstep_receptive_over` at the one-arm fixture table of `Checks/Cases/Checks/Sys/Dispatch.lean`; the kernel claim is `the_exit_answer_is_a_step`'s -/
theorem the_exit_fixture_steps_its_ecall :
    ∃ evs st, sstep [] (config.mkCfg (svc_ms 93 0 0 0 0 0 0) demo_model) evs st :=
  sstep_receptive_over [fixture_arm_exit] [] _ rfl (fun x8 hp => by
    have hx : 93 = x8 := Option.some.inj hp
    subst hx
    rfl)

/-- The found-arm branch on the real table: `checked_table` carries an arm
at 93, so `sstep_receptive_checked` discharges the hypothesis with it and
the machine steps by that arm's witness.  The fixture pin above was
written on a branch that had not taken `exit`'s and `exit_group`'s arms
(#1072), where `checked_table` was empty and `sstep_receptive_checked`'s
own premise, an arm found at the pending number, held only where nothing
was pending.  #1080 landed it after those arms were registered, so the
real table already had its arm at 93; this theorem is the first use of
`sstep_receptive_checked`.
model: `sstep_receptive_checked` at `checked_table`'s arm at 93; the statement holds whatever that arm answers, a decline included, so it claims no kernel behaviour: what `exit` answers is pinned in `Checks/Cases/Kernel/Exit.lean`, by `exit_halts_with_low_byte` and, at 93 through the dispatcher, `sysno_93_is_exit` -/
theorem the_exit_arm_steps_its_ecall :
    ∃ evs st, sstep [] (config.mkCfg (svc_ms 93 0 0 0 0 0 0) demo_model) evs st :=
  sstep_receptive_checked [] _ rfl (fun x8 hp => by
    have hx : 93 = x8 := Option.some.inj hp
    subst hx
    exact ⟨_, lookup_ca_checked_table_exit⟩)

/-- Rejected: at the `exit` ecall no step is the error, whatever events it
names — the contrast with `io_setup_steps_only_to_the_error`.  The
instruction rules are refused because a syscall is pending; the decline,
because `exit`'s arm never declines (`exit_dispatch_modeled`); and the
materialization fault, because its premise asks for a model still running
after the answer, and `exit`'s answer halts it (`exit_dispatch_halts`).
kernel: kernel/exit.c:exit,do_exit@v6.18.46 -/
theorem the_exit_ecall_steps_to_no_error (evs : List event) :
    ¬ sstep [] (config.mkCfg (svc_ms 93 0 0 0 0 0 0) demo_model) evs SError := by
  intro hs
  cases hs with
  | sstep_instr_fault _ _ _ hp _ => exact absurd hp (by decide)
  | sstep_instr_unmodeled _ _ _ hp _ => exact absurd hp (by decide)
  | sstep_syscall_materialization_fault _ _ x8 _ _ _ _ hp hspec hrun _ =>
    have hx : 93 = x8 := Option.some.inj hp
    subst hx
    have hh := exit_dispatch_halts _ _ _ _ _ (Or.inl rfl) hspec
    rw [hrun] at hh
    cases hh
  | sstep_syscall_unmodeled _ _ x8 _ hp hspec =>
    have hx : 93 = x8 := Option.some.inj hp
    subst hx
    exact exit_dispatch_modeled _ _ (Or.inl rfl) hspec

/-! ## The hypothesis the `∀ n` forms carry

`sstep_receptive_of_agree`, `coexec_coexec_progress` and
`coexec_progress_iff` ask agreement at EVERY number.  A table lacking an
arm the spec carries cannot discharge it.  The empty fixture pins that
refusal independently of registrations; the real-table pin exercises
`lookups_agree_at_of_complete`, the route that replaces the former
spec-only counterexample once both tables coincide.  Agreement everywhere
also puts an `exit` arm in the checked table, a consequence that survives
every registration.  `no_configuration_under_the_hypothesis_is_stuck` is
the positive reading: under the hypothesis Rocq's unconditional statement
holds, which is what the `_of_agree` form is for. -/

/-- Agreement at `exit`'s number needs the arm: the spec table answers at
93, so the checked side of the equation cannot be `none`.
model: the two lookups at 93 over an arbitrary table; that the spec answers at 93 is `Checks/Examples.lean`'s `exit_dispatch_admits` -/
theorem agreement_at_exit_needs_the_exit_arm (t : List CheckedArm) (h : lookups_agree_in t 93) :
    (lookup_ca t 93).isSome = true := by
  have hs : (lookup_arm spec_table 93).isSome = true := rfl
  rw [show lookup_arm spec_table 93 = (lookup_ca t 93).map CheckedArm.ca_arm from h,
    Option.isSome_map] at hs
  exact hs

/-- Rejected: agreement everywhere is FALSE over the empty table — at
`exit`'s number, which the spec answers — so `coexec_progress_iff` has no
instance over it.  Stated over the explicit `[]` so that the pin outlives
the table: every table lacking a number the spec answers fails the same
way, the real one included while it is partial.
model: the `∀ n` hypothesis over the empty table, refuted at 93; no kernel behaviour is claimed -/
theorem agreement_everywhere_fails_over_the_empty_table : ¬ ∀ n, lookups_agree_in [] n :=
  fun h => premise_fails_at_exit_over_the_empty_table (h 93)

/-- Positive: discharge the `∀ n` hypothesis through the complete-table
route.  The empty-table refusal above keeps the missing-arm mistake
observable without relying on a spec-only number in the real table.
model: `lookups_agree_at_of_complete` with the table equality proved by conversion; no kernel behaviour is claimed -/
theorem agreement_everywhere_holds_on_the_checked_table : ∀ n, lookups_agree_at n :=
  lookups_agree_at_of_complete rfl

/-- The same fact about the real table, in the form that holds at every
size: whoever discharges `coexec_progress_iff`'s hypothesis has registered
an `exit` arm.  This consequence of agreement does not depend on how the
hypothesis was discharged.
model: `lookups_agree_at` at 93 read through `agreement_at_exit_needs_the_exit_arm`; no kernel behaviour is claimed -/
theorem agreement_everywhere_needs_the_exit_arm (h : ∀ n, lookups_agree_at n) :
    (lookup_ca checked_table 93).isSome = true :=
  agreement_at_exit_needs_the_exit_arm checked_table (h 93)

/-- Positive: under the hypothesis no running configuration is stuck — the
premise `stuck_not_coexec_progress` would need, refuted before it can be
asked.  This is Rocq's `sstep_receptive` read as a negation.
model: `sstep_receptive_of_agree` against the stuckness premise; no kernel behaviour is claimed -/
theorem no_configuration_under_the_hypothesis_is_stuck (hagree : ∀ n, lookups_agree_at n)
    (segs : List Segment) (c : config) (hh : m_halted c.cfg_model = none) :
    ¬ ∀ evs st, ¬ sstep segs c evs st :=
  fun hstuck =>
    match sstep_receptive_of_agree segs hagree c hh with
    | ⟨evs, st, hs⟩ => hstuck evs st hs

/-! ## The progress reading

`coexec_progress` is `coexec` with the premise that some step exists.  On
the loop — one instruction, returning to itself, never halting, never
pending a syscall — the two readings are decided with no table hypothesis:
`coexec_coexec_progress_inv` at the invariant "this is the loop" gives the
reading from `OmniPilot.loop_coexec_false`, and `coexec_progress_implies`
gives it back.  A halted configuration refutes the reading under the
postcondition that refuses its halt and satisfies it under the one that
names it, exactly as `coexec` does. -/

/-- THE PIN: the loop satisfies the progress reading under the FALSE
postcondition, as it satisfies `coexec` — the reading admits divergence,
and adds a premise only where a step is owed.  Proved through the
invariant form with no table hypothesis: the loop never has a syscall
pending, so `loop_takes_silent_step` is the progress at every visit.
model: `coexec_coexec_progress_inv` at the loop fixture, whose only step returns to itself; no kernel behaviour is claimed -/
theorem loop_coexec_progress_false : coexec_progress loop_segments loop_config (fun _ _ => False) :=
  coexec_coexec_progress_inv loop_segments (fun c => c = loop_config)
    (fun c hc _ => by
      subst hc
      exact ⟨[], SNext loop_config, loop_takes_silent_step⟩)
    (fun c evs c' hc hs => by
      subst hc
      exact step_to.SNext.inj (loop_steps_only_to_itself evs (SNext c') hs).2)
    loop_config (fun _ _ => False) rfl loop_coexec_false

/-- …and the round trip: dropping the premise lands back on OmniPilot's
theorem's statement.
model: `coexec_progress_implies` at the loop; no kernel behaviour is claimed -/
theorem loop_coexec_false_from_progress : coexec loop_segments loop_config (fun _ _ => False) :=
  coexec_progress_implies _ _ _ loop_coexec_progress_false

/-- Positive, on the running rule's error clause: the decline at
`__NR_io_setup` satisfies the reading under the postcondition that names
the error — no event, `OError` at this configuration.  The progress
premise is `the_decline_at_io_setup_is_a_step`, the error clause is
`io_setup_steps_only_to_the_error`, and the continuing clause is vacuous,
since nothing steps to a next configuration there.  A reading whose error
clause named the halt, or whose premise asked for a continuing step, would
refuse this configuration.
kernel: include/uapi/asm-generic/unistd.h:__NR_io_setup@v6.18.46 -/
theorem the_decline_at_io_setup_progresses_to_the_error :
    coexec_progress [] (config.mkCfg (svc_ms 0 0 0 0 0 0 0) demo_model)
      (fun tr o => tr = [] ∧ o = OError (config.mkCfg (svc_ms 0 0 0 0 0 0 0) demo_model)) :=
  coexec_progress.coexec_progress_step [] _ _ rfl the_decline_at_io_setup_is_a_step
    (fun evs hs => ⟨(io_setup_steps_only_to_the_error evs SError hs).1, rfl⟩)
    (fun evs c' hs => nomatch (io_setup_steps_only_to_the_error evs (SNext c') hs).2)

/-- The premise, read back: the reading at a running configuration yields
a step, which is what `stuck_not_coexec_progress` refutes with.
model: `coexec_progress_steps` at the loop; no kernel behaviour is claimed -/
theorem the_loop_progresses : ∃ evs st, sstep loop_segments loop_config evs st :=
  coexec_progress_steps _ _ _ rfl loop_coexec_progress_false

/-- Rejected: `stuck_not_coexec_progress` does not apply to the loop — its
stuckness premise is false there, since the loop steps.
model: the stuckness premise at the loop fixture, refuted by its own step; no kernel behaviour is claimed -/
theorem the_loop_is_not_stuck : ¬ ∀ evs st, ¬ sstep loop_segments loop_config evs st :=
  fun h => h [] (SNext loop_config) loop_takes_silent_step

/-- Rejected: a HALTED configuration refutes the reading under the false
postcondition, by both rules — the halt rule asks the postcondition, and
the running rule asks for a model that is not halted.
model: `coexec_progress`'s two rules at a configuration `with_halted` stopped; no kernel behaviour is claimed -/
theorem a_halted_configuration_refutes_the_false_post (segs : List Segment) (ms : machine_state)
    (m : Model) (code : word) :
    ¬ coexec_progress segs (config.mkCfg ms (with_halted code m)) (fun _ _ => False) := by
  intro h
  cases h with
  | coexec_progress_halt _ _ _ hq => exact hq
  | coexec_progress_step _ _ hh _ _ _ => exact nomatch (hh : (some code : Option word) = none)

/-- Positive: the same halted configuration satisfies the reading under
the postcondition that names its halt — the empty trace and the halt at
this configuration — by the halt rule alone, with no step owed.
model: `coexec_progress`'s halt rule at a configuration `with_halted` stopped; no kernel behaviour is claimed -/
theorem a_halted_configuration_satisfies_its_halt_post (segs : List Segment) (ms : machine_state)
    (m : Model) (code : word) :
    coexec_progress segs (config.mkCfg ms (with_halted code m))
      (fun tr o => tr = [] ∧ o = OHalt (config.mkCfg ms (with_halted code m))) :=
  coexec_progress.coexec_progress_halt segs _ _
    (fun h => nomatch (h : (some code : Option word) = none)) ⟨rfl, rfl⟩

/-! ## Part 2's legacy statement, through the `iff`

Rocq seals `Equivalence.SPEC` on the exit-0 pair by applying the functor
`SpecOfOmni` to the omni proof.  Lean has no functors, and
`exit0_checked` is that functor's body: one application of
`OmniEquivalence.strong_universal_iff`.  The accepting pin takes that
route from Part 2's omni theorem to `SPEC`; the rejecting pin runs the
same `iff` the other way, from `SPEC` back to the omni statement, on
Part 5's pair, where the omni statement is refuted — so the route that
gives the exit-0 pair its `SPEC` is shown not to give every pair one. -/

/-- Positive: the exit-0 pair satisfies `SPEC`, by the route itself —
`strong_universal_iff` read from Part 2's omni theorem, which is the body
`exit0_checked` gives Rocq's functor.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem the_exit0_pair_meets_spec : SPEC exit0_image exit0_image :=
  ⟨(strong_universal_iff _ _).2 exit0_omni_strong_universal⟩

/-- Rejected: the loop and the write loop do not satisfy `SPEC` — Part 5's
refutation of the omni statement, carried back across the `iff`.  What
separates the two images is the byte the write delivers, so this rests on
the write's answer.
kernel: fs/read_write.c:ksys_write; fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem the_loop_pair_fails_spec : ¬ SPEC loop_image wloop_image :=
  fun h => loop_wloop_refutes_omni_strong_universal ((strong_universal_iff _ _).1 h.strong_universal)

/-! ## Part 5's write, through the dispatch and on the arm's checker

Rocq's `wloop_checker` evaluates `check_syscall` at the loop's write, and
so does the Lean one: the write arm is a `checked_table` row
(`Checks/Arms/Fs/ReadWrite.lean`).  The first two pins read the dispatch
itself — the loop's one-byte answer accepted, and an answer claiming two
bytes of the one-byte request, a lie no kernel tells, refused — so that
removing the row, or wiring it to a checker that answers differently at
this one input, fails here.  They do NOT pin the row's argument wiring:
the loop writes to fd 1, where narrowing `a0` through `fd32` and passing
it raw agree.  The high-bit fd that separates them is pinned through the
table in `Checks/Cases/Checks/Sys/Fs/ReadWrite.lean`, as
`write_fd_truncates_to_32_bits_over_the_real_table`.  `wloop_write_forced` reaches the forced outcome
through the checker's completeness where Rocq reads it off
`write_channel_outcome`; the other two pins read the same two answers back
at the spec, over `syscall_spec`, which the table does not touch. -/

/-- THE PIN: the dispatch at the loop's write finds the write arm and
accepts the one-byte delivery to standard output with the model
unchanged (`wloop_checker`, Rocq's statement, with no table hypothesis).
kernel: fs/read_write.c:ksys_write; fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem the_write_loop_dispatch_accepts_its_byte (lim : Int) :
    check_syscall (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)) wloop_eff
      (wloop_model lim) = CheckOk (wloop_model lim) wloop_trace :=
  wloop_checker lim

/-- Rejected: the dispatch refuses the same write answered with two bytes,
more than the count of 1 the loop passes, even with a ledger that agrees
with the claim.  The channel arm of `check_write` bounds the return by
the bytes the source supplies (`1 ≤ ret ≤ length bs`), and `ksys_write`
hands `vfs_write` the count unchanged (fs/read_write.c:727-744, Linux
v6.18.46), so no kernel returns more than was asked.  Evaluated at the
arm the dispatch finds, with the input's descriptor, buffer, count and
bytes rewritten in as `wloop_check_write` does.
kernel: fs/read_write.c:ksys_write@v6.18.46 -/
theorem the_write_loop_dispatch_refuses_two_bytes (lim : Int) :
    check_syscall (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64))
      (with_copyins [(Z_to_bv 64 0x100, 2)] (mkEffect (Z_to_bv 64 2) [] [])) (wloop_model lim)
    = CheckReject := by
  rw [check_syscall_of_found _ _ _ arm_write (by rw [wloop_sysno]; exact lookup_ca_checked_table_write), ca_check_arm_write]
  have hfds : m_fds (wloop_model lim) = m_fds (wloop_model 0) := rfl
  generalize wloop_model lim = m at hfds ⊢
  unfold check_write
  rw [hfds, wloop_fd, wloop_buf, wloop_count, wloop_source, wloop_stdout]
  rfl

/-- THE PIN: at the loop's write the spec admits the one-byte
delivery to standard output with the model unchanged — `wloop_check_write`
read back through `check_write_sound_ok`, the route
`wloop_syscall_sstep` takes.
kernel: fs/read_write.c:ksys_write; fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem the_write_loop_admits_its_byte (lim : Int) :
    syscall_spec (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)) (wloop_model lim)
      (Ok wloop_eff (wloop_model lim) wloop_trace) :=
  (write_dispatch_iff _ _ _ wloop_sysno).2
    (check_write_sound_ok _ _ _ _ _ _ _ _ (wloop_check_write lim))

/-- Rejected: the same write answered with two bytes, more than the count
of 1 the loop passes, is no outcome of the spec, whatever model and events
it names — even with a ledger that agrees with the claim.
`wloop_write_forced` refuses it: the only effect admitted there is
`wloop_eff`, whose return is 1.
kernel: fs/read_write.c:ksys_write; fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem the_write_loop_refuses_two_bytes (lim : Int) (m' : Model) (evs : List event) :
    ¬ syscall_spec (sys_input wloop_segments (wloop_s 5) (Z_to_bv 64 64)) (wloop_model lim)
      (Ok (with_copyins [(Z_to_bv 64 0x100, 2)] (mkEffect (Z_to_bv 64 2) [] [])) m' evs) :=
  fun h => absurd (congrArg SyscallEffect.eff_ret (wloop_write_forced lim _ _ _ h).1) (by decide)

/-! ## Part 5's loop is `Checks/OmniPilot.lean`'s

The pilot ported one image of Part 5 ahead of the rest, the
one-instruction loop, as `OmniPilot.loop_segments` and
`OmniPilot.loop_config`; Part 5 defines it again under Rocq's names, so
the two files' statements about it could drift apart.  They are one
image: the first pin states the identity, and the second carries Part 5's
refutation across it to the pilot's fixture. -/

/-- THE PIN: the pilot's fixture is Part 5's loop at the demo budget, the
same segment list and the same starting configuration.
model: the two fixture definitions compared by computation; no kernel behaviour is claimed -/
theorem the_pilot_loop_is_the_part_5_loop :
    OmniPilot.loop_segments = Omni.loop_segments ∧ OmniPilot.loop_config = loop_c demo_limit :=
  ⟨rfl, rfl⟩

/-- Rejected: the pilot's loop and the write loop are told apart by their
traces — `loop_wloop_not_trace_equiv`, read on the pilot's fixture through
the identity.  What tells them apart is the byte the write delivers.
kernel: fs/read_write.c:ksys_write; fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem the_pilot_loop_is_told_from_the_write_loop :
    ¬ ∀ tr, obs_trace OmniPilot.loop_segments OmniPilot.loop_config tr ↔
      obs_trace wloop_segments (wloop_c demo_limit) tr := by
  rw [the_pilot_loop_is_the_part_5_loop.1, the_pilot_loop_is_the_part_5_loop.2]
  exact loop_wloop_not_trace_equiv demo_limit demo_limit

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Omni
