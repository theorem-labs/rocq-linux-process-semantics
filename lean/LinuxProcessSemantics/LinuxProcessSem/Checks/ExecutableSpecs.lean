import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
import LinuxProcessSemantics.LinuxProcessSem.Specs

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.ExecutableSpecs — the verified acceptor, dispatched over the checked table

Mirrors `theories/LinuxProcessSem/Checks/ExecutableSpecs.v`: the
acceptor's definitions and the theorems that relate them to
`Specs.syscall_spec`.  The Rocq header says what the acceptor is
FOR — a runnable decision procedure for the relational specs, so that a
conformance run can fold it over the syscalls a real kernel made — and how
its three verdicts read; none of that is repeated here.  Not part of the
trusted specification: the spec stays the definition, and the proofs here
are QA on the tester.  The header's baseline is the squash of the
2026-09-11 work, where `ExecutableSpecs.v` is byte-identical to
`f44244ad6b80`, the commit the ticket brief names and this port was read
at: a twin's baseline has to be an ancestor of its branch, the rule
`tools/check_lean_spec_parity.py` holds the twins it reads to, and
`f44244ad` stopped being one when that day's work was rebase-merged.

Rocq's file also re-exports every per-syscall checker module under
`Checks/Sys/`.  The Lean tree has the scaffold (`Checks/Sys/Prelude.lean`),
the record (`Checks/Sys/Dispatch.lean`) and the table
(`Checks/Sys/Table.lean`); a per-syscall checker arrives with its C ticket
and is imported by the table block that puts it in `checked_table`, so this
file imports the table and nothing per syscall.

TWO THINGS DIFFER FROM ROCQ, both forced by the port being partial.  The
second retires the day the last arm lands; the first need not, and stays
as the handle the pins drive the dispatch through:

- THE TABLE IS A PARAMETER of `check_syscall_in` and
  `check_syscall_for_run_in`, and Rocq's `check_syscall` and
  `check_syscall_for_run` are their instances at `checked_table`,
  definitionally; the `_in` suffix reads "over the table `t`", not the
  tree's input-fixture `_in`.  Rocq never needed the parameter: its table
  is complete.
  Here `checked_table` holds the arms registered so far — `exit` and
  `exit_group` first (K6a), the rest as their V tickets land — so a
  dispatch exercised on it alone reaches only the arms of the day.  `Checks/Cases/Checks/ExecutableSpecs.lean`
  drives both functions through a one-arm fixture table for that reason,
  the reason `Checks/Cases/Checks/Sys/Dispatch.lean` gives for its own
  fixture arm.  Nothing else changes: the extracted shape a harness would
  call is the instance, with Rocq's type.

- THE THEOREMS THAT PASS THROUGH A MISSING ARM TAKE A PREMISE Rocq does
  not need.  Rocq closes
  every one of them with `checked_table_arms : map ca_arm checked_table =
  spec_table` and `lookup_ca_arm`: the two tables are one surface, so the
  checker's lookup and the dispatcher's lookup find the same arm at every
  number.  That equation is FALSE while the port is partial
  (`Checks/Sys/Table.lean`'s header says why and states the two halves
  that hold instead), and with it false the per-number agreement,
  `lookups_agree_at n`, holds at three kinds of number and fails at a fourth:
  at every checked number (`lookups_agree_at_of_found`), at every number the
  spec table does not carry (`lookups_agree_at_of_absent`), at every number
  once the tables coincide (`lookups_agree_at_of_complete`), and NOT at a
  number `spec_table` carries and `checked_table` does not yet.  At such a
  number the checker declines a call the spec answers — the fail-closed
  answer, and the right one for a harness, but not `syscall_spec i m
  Unmodeled`.  So the two soundness-of-decline and completeness-of-accept
  directions, and every `iff` built on them, take `lookups_agree_at` at the
  call's number; `check_syscall_sound_ok`, `check_syscall_complete_unmodeled`
  and `check_syscall_for_run_reject_iff` hold with no premise, exactly as
  Rocq states them.  `Checks/Examples.lean`'s run bridge consumes only the
  premise-free halves, bar the unmodeled one, and says so there.

  When `checked_table.map CheckedArm.ca_arm = spec_table` becomes provable,
  `lookups_agree_at_of_complete` discharges the premise at every number in one
  line, and this paragraph and the premise go together.

The statements are otherwise Rocq's, name for name and argument for
argument, including the two `syscall_post_model` lemmas and the split of
the run adapter's verification into the four shapes of `Option
check_result` it can take.  Where Rocq proves an `iff` in one block, the
sound and complete halves are separate theorems here, because the run
bridge needs the halves that carry no premise and only those. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

/-! ## The acceptor -/

/-- Dispatch on the unsigned syscall number through a checked table: the
arm's acceptor if the table has one, and `CheckUnmodeled` — the fail-closed
answer — if it has none.  The table is a parameter for the reason the file
header gives; the acceptor a harness calls is `check_syscall` below.
Rocq: the body of `ExecutableSpecs.check_syscall`. -/
def check_syscall_in (t : List CheckedArm) (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match lookup_ca t (bv_unsigned i.in_sysno) with
  | some c => c.ca_check i eff m
  | none => CheckUnmodeled

/-- Rocq's `check_syscall`: the dispatch over `checked_table`, whose every
arm is `spec_table`'s arm for its number (`Table.checked_table_arms`), so
the checker never answers through an arm the dispatcher does not hold.
Which numbers it answers at all is the file header's premise: while the
port is partial it declines numbers the spec answers.  Rocq:
`ExecutableSpecs.check_syscall`. -/
def check_syscall (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_syscall_in checked_table i eff m

/-- Postprocess the relational post-model exactly as the run does: a halted
model is `Run.sstep_exit`'s (or `Run.sstep_killed`'s) and stays as it is; a
running one is charged for the effect's user-memory accesses by the same
atomic materializer `Run.sstep_syscall` and
`Run.sstep_syscall_materialization_fault` apply, and `none` is that
fault.  Rocq: `ExecutableSpecs.syscall_post_model`. -/
def syscall_post_model (m : Model) (eff : SyscallEffect) : Option Model :=
  match m_halted m with
  | some _ => some m
  | none => materialize_model_accesses m (syscall_effect_accesses eff)

/-- The public conformance-checker boundary over a checked table.  The outer
`Option` is the run's error-transition boundary: `none` exposes no partially
updated model and is deliberately not conflated with either `CheckReject`
or `CheckUnmodeled`.  Rocq: the body of
`ExecutableSpecs.check_syscall_for_run`. -/
def check_syscall_for_run_in (t : List CheckedArm) (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : Option check_result :=
  match check_syscall_in t i eff m with
  | CheckOk m' evs =>
      match syscall_post_model m' eff with
      | some m'' => some (CheckOk m'' evs)
      | none => none
  | CheckReject => some CheckReject
  | CheckUnmodeled => some CheckUnmodeled

/-- Rocq's `check_syscall_for_run`: the boundary a harness calls, over
`checked_table`.  Rocq: `ExecutableSpecs.check_syscall_for_run`. -/
def check_syscall_for_run (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    : Option check_result :=
  check_syscall_for_run_in checked_table i eff m

/-! ## The two lookups agree — at which numbers

Rocq has the agreement at every number at once, from `checked_table_arms`'s
equation and `lookup_ca_arm`.  The file header says why the Lean tree has
it per number, and this section says at which numbers. -/

/-- The checker's lookup finds only a member of the table, and finds it at
its own number.  General in the table, so no arm's arrival re-proves it. -/
theorem lookup_ca_mem (t : List CheckedArm) (n : Int) (c : CheckedArm) :
    lookup_ca t n = some c → c ∈ t ∧ ca_no c = n := by
  induction t with
  | nil => intro h; cases h
  | cons b r ih =>
    intro h
    simp only [lookup_ca] at h
    by_cases e : ca_no b = n
    · simp only [e, ↓reduceIte] at h
      injection h with hbc
      subst hbc
      exact ⟨List.Mem.head _, e⟩
    · simp only [e, ↓reduceIte] at h
      obtain ⟨hmem, hno⟩ := ih h
      exact ⟨List.Mem.tail _ hmem, hno⟩

/-- At a checked number the dispatcher's arm is the checked arm's own: the
per-number reading of `Table.checked_table_arms`. -/
theorem spec_arm_of_found (n : Int) (c : CheckedArm) :
    lookup_ca checked_table n = some c → lookup_arm spec_table n = some c.ca_arm := by
  intro h
  obtain ⟨hmem, hno⟩ := lookup_ca_mem checked_table n c h
  subst hno
  exact checked_table_arms c hmem

/-- The dispatcher and the checker find the same arm at `n`, over a
checked table `t`: what Rocq's `rewrite <- checked_table_arms, lookup_ca_arm`
establishes for every `n` at once.  Stated over a table so that
`Checks/Cases/Checks/ExecutableSpecs.lean` can exhibit both the numbers it
holds at and the number it fails at on fixture tables; the premise the
theorems below take is its instance `lookups_agree_at`. -/
def lookups_agree_in (t : List CheckedArm) (n : Int) : Prop :=
  lookup_arm spec_table n = (lookup_ca t n).map CheckedArm.ca_arm

/-- The premise: the two lookups agree at `n` over `checked_table`.  The
file header says at which numbers it holds and at which it does not, and
what retires it. -/
def lookups_agree_at (n : Int) : Prop := lookups_agree_in checked_table n

/-- The premise holds at every checked number. -/
theorem lookups_agree_at_of_found (n : Int) (c : CheckedArm) :
    lookup_ca checked_table n = some c → lookups_agree_at n := by
  intro h
  unfold lookups_agree_at lookups_agree_in
  rw [h, Option.map_some]
  exact spec_arm_of_found n c h

/-- The premise holds at every number the spec table does not carry: a
checked arm there would be an arm `Table.checked_table_arms` refuses. -/
theorem lookups_agree_at_of_absent (n : Int) :
    lookup_arm spec_table n = none → lookups_agree_at n := by
  intro h
  unfold lookups_agree_at lookups_agree_in
  rw [h]
  cases hc : lookup_ca checked_table n with
  | none => rfl
  | some c =>
    have hspec := spec_arm_of_found n c hc
    rw [h] at hspec
    simp only [reduceCtorEq] at hspec

/-- The premise holds everywhere once the two tables are one surface: Rocq's
situation, reached by the last C ticket, and the line that retires the
premise then. -/
theorem lookups_agree_at_of_complete
    (hall : checked_table.map CheckedArm.ca_arm = spec_table) (n : Int) :
    lookups_agree_at n := by
  unfold lookups_agree_at lookups_agree_in
  rw [← hall]
  exact lookup_ca_arm checked_table n

/-! ## What the dispatch computes to, and what the spec says there -/

/-- With an arm found, the dispatch over any table IS that arm's acceptor. -/
theorem check_syscall_in_of_found (t : List CheckedArm) (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) (c : CheckedArm) :
    lookup_ca t (bv_unsigned i.in_sysno) = some c →
    check_syscall_in t i eff m = c.ca_check i eff m := by
  intro h
  simp only [check_syscall_in, h]

/-- With no arm found, the dispatch over any table declines, whatever effect
it is offered. -/
theorem check_syscall_in_of_none (t : List CheckedArm) (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    lookup_ca t (bv_unsigned i.in_sysno) = none →
    check_syscall_in t i eff m = CheckUnmodeled := by
  intro h
  simp only [check_syscall_in, h]

/-- The two over `checked_table`, which is what the theorems below split on. -/
theorem check_syscall_of_found (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (c : CheckedArm) :
    lookup_ca checked_table (bv_unsigned i.in_sysno) = some c →
    check_syscall i eff m = c.ca_check i eff m :=
  check_syscall_in_of_found checked_table i eff m c

theorem check_syscall_of_none (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    lookup_ca checked_table (bv_unsigned i.in_sysno) = none →
    check_syscall i eff m = CheckUnmodeled :=
  check_syscall_in_of_none checked_table i eff m

/-- With an arm found, the spec at this input is that arm's spec: the step
that lets a theorem stated over `Specs.syscall_spec` be closed by a field
of the arm the checker found. -/
theorem syscall_spec_of_found (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (c : CheckedArm) :
    lookup_ca checked_table (bv_unsigned i.in_sysno) = some c →
    (syscall_spec i m o ↔ c.ca_arm.sa_spec i m o) := by
  intro h
  unfold syscall_spec
  exact dispatch_arm spec_table i m o c.ca_arm (spec_arm_of_found _ c h)

/-- With no arm found, and the premise, the spec declines too: the one
place the premise is consumed. -/
theorem syscall_spec_of_none (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hagree : lookups_agree_at (bv_unsigned i.in_sysno)) :
    lookup_ca checked_table (bv_unsigned i.in_sysno) = none →
    (syscall_spec i m o ↔ o = Unmodeled) := by
  intro h
  unfold lookups_agree_at lookups_agree_in at hagree
  rw [h, Option.map_none] at hagree
  unfold syscall_spec dispatch
  rw [hagree]
  exact Iff.rfl

/-! ## Verification: the checker is sound and complete for the relational specs

Each theorem is one case split on the checker's lookup and one field of the
arm it finds — Rocq's argument, which does not grow when a syscall is added.
The premise, where taken, is the file header's. -/

/-- Rocq: `ExecutableSpecs.check_syscall_sound_ok`.  No premise: an accepted
effect came from an arm the table holds, and that arm is the dispatcher's. -/
theorem check_syscall_sound_ok (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) :
    check_syscall i eff m = CheckOk m' evs → syscall_spec i m (Ok eff m' evs) := by
  intro h
  cases hc : lookup_ca checked_table (bv_unsigned i.in_sysno) with
  | none =>
    rw [check_syscall_of_none i eff m hc] at h
    simp only [reduceCtorEq] at h
  | some c =>
    rw [check_syscall_of_found i eff m c hc] at h
    exact (syscall_spec_of_found i m _ c hc).2 (c.ca_sound_ok i eff m m' evs h)

/-- Rocq: `ExecutableSpecs.check_syscall_sound_unmodeled`, under the premise:
a decline with no arm behind it is the spec's decline only where the spec
table has no arm either. -/
theorem check_syscall_sound_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (hagree : lookups_agree_at (bv_unsigned i.in_sysno)) :
    check_syscall i eff m = CheckUnmodeled → syscall_spec i m Unmodeled := by
  intro h
  cases hc : lookup_ca checked_table (bv_unsigned i.in_sysno) with
  | none => exact (syscall_spec_of_none i m _ hagree hc).2 rfl
  | some c =>
    rw [check_syscall_of_found i eff m c hc] at h
    exact (syscall_spec_of_found i m _ c hc).2 (c.ca_sound_unmodeled i eff m h)

/-- Rocq: `ExecutableSpecs.check_syscall_complete_ok`, under the premise: an
admitted effect is accepted only where the checker has the arm that admits
it. -/
theorem check_syscall_complete_ok (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (hagree : lookups_agree_at (bv_unsigned i.in_sysno)) :
    syscall_spec i m (Ok eff m' evs) → check_syscall i eff m = CheckOk m' evs := by
  intro h
  cases hc : lookup_ca checked_table (bv_unsigned i.in_sysno) with
  | none =>
    have h' := (syscall_spec_of_none i m _ hagree hc).1 h
    simp only [reduceCtorEq] at h'
  | some c =>
    rw [check_syscall_of_found i eff m c hc]
    exact c.ca_complete_ok i eff m m' evs ((syscall_spec_of_found i m _ c hc).1 h)

/-- Rocq: `ExecutableSpecs.check_syscall_complete_unmodeled`.  No premise:
where the spec declines, the checker declines — through the arm's
fail-closed field if it has the arm, and by having no arm if not. -/
theorem check_syscall_complete_unmodeled (i : SyscallInput) (m : Model) (eff : SyscallEffect) :
    syscall_spec i m Unmodeled → check_syscall i eff m = CheckUnmodeled := by
  intro h
  cases hc : lookup_ca checked_table (bv_unsigned i.in_sysno) with
  | none => exact check_syscall_of_none i eff m hc
  | some c =>
    rw [check_syscall_of_found i eff m c hc]
    exact c.ca_complete_unmodeled i m eff ((syscall_spec_of_found i m _ c hc).1 h)

/-- Rocq: `ExecutableSpecs.check_syscall_ok_iff`. -/
theorem check_syscall_ok_iff (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (hagree : lookups_agree_at (bv_unsigned i.in_sysno)) :
    check_syscall i eff m = CheckOk m' evs ↔ syscall_spec i m (Ok eff m' evs) :=
  ⟨check_syscall_sound_ok i eff m m' evs, check_syscall_complete_ok i eff m m' evs hagree⟩

/-- Rocq: `ExecutableSpecs.check_syscall_err_iff`. -/
theorem check_syscall_err_iff (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (hagree : lookups_agree_at (bv_unsigned i.in_sysno)) :
    check_syscall i eff m = CheckUnmodeled ↔ syscall_spec i m Unmodeled :=
  ⟨check_syscall_sound_unmodeled i eff m hagree, check_syscall_complete_unmodeled i m eff⟩

/-! ## Verification: the public checker, against the relational spec

These cover `Option check_result` exhaustively.  They are stated against
`syscall_spec` and `syscall_post_model` rather than against `Run.sstep`,
because this file does not import `Run`;
`Checks.Examples.checker_ok_is_run_step` and its two companions close that
last step. -/

/-- Rocq: `ExecutableSpecs.syscall_post_model_running`. -/
theorem syscall_post_model_running (m : Model) (eff : SyscallEffect) :
    m_halted m = none →
    syscall_post_model m eff = materialize_model_accesses m (syscall_effect_accesses eff) := by
  intro h
  simp only [syscall_post_model, h]

/-- Rocq: `ExecutableSpecs.syscall_post_model_halted`. -/
theorem syscall_post_model_halted (m : Model) (eff : SyscallEffect) (code : word) :
    m_halted m = some code → syscall_post_model m eff = some m := by
  intro h
  simp only [syscall_post_model, h]

/-! ### What the adapter computes to, per verdict of the checker -/

/-- An accepted effect whose post-model the accounting admits. -/
theorem check_syscall_for_run_of_ok_some (i : SyscallInput) (eff : SyscallEffect)
    (m m' m'' : Model) (evs : List event) :
    check_syscall i eff m = CheckOk m' evs → syscall_post_model m' eff = some m'' →
    check_syscall_for_run i eff m = some (CheckOk m'' evs) := by
  intro h hpost
  have h' : check_syscall_in checked_table i eff m = CheckOk m' evs := h
  simp only [check_syscall_for_run, check_syscall_for_run_in, h', hpost]

/-- An accepted effect whose post-model the accounting refuses: the outer
`none`. -/
theorem check_syscall_for_run_of_ok_none (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) :
    check_syscall i eff m = CheckOk m' evs → syscall_post_model m' eff = none →
    check_syscall_for_run i eff m = none := by
  intro h hpost
  have h' : check_syscall_in checked_table i eff m = CheckOk m' evs := h
  simp only [check_syscall_for_run, check_syscall_for_run_in, h', hpost]

/-- A rejection passes through, with no accounting done. -/
theorem check_syscall_for_run_of_reject (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_syscall i eff m = CheckReject → check_syscall_for_run i eff m = some CheckReject := by
  intro h
  have h' : check_syscall_in checked_table i eff m = CheckReject := h
  simp only [check_syscall_for_run, check_syscall_for_run_in, h']

/-- A decline passes through, with no accounting done. -/
theorem check_syscall_for_run_of_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_syscall i eff m = CheckUnmodeled →
    check_syscall_for_run i eff m = some CheckUnmodeled := by
  intro h
  have h' : check_syscall_in checked_table i eff m = CheckUnmodeled := h
  simp only [check_syscall_for_run, check_syscall_for_run_in, h']

/-! ### The four shapes, sound and complete -/

/-- A public-checker success contains a relational syscall outcome followed
by the post-model premise shared with the run constructors.  The sound
half of Rocq's `check_syscall_for_run_ok_iff`; no premise. -/
theorem check_syscall_for_run_sound_ok (i : SyscallInput) (eff : SyscallEffect) (m m'' : Model)
    (evs : List event) :
    check_syscall_for_run i eff m = some (CheckOk m'' evs) →
    ∃ m', syscall_spec i m (Ok eff m' evs) ∧ syscall_post_model m' eff = some m'' := by
  intro h
  cases hchk : check_syscall i eff m with
  | CheckOk m' evs' =>
    cases hpost : syscall_post_model m' eff with
    | none =>
      rw [check_syscall_for_run_of_ok_none i eff m m' evs' hchk hpost] at h
      simp only [reduceCtorEq] at h
    | some accounted =>
      rw [check_syscall_for_run_of_ok_some i eff m m' accounted evs' hchk hpost] at h
      simp only [Option.some.injEq, check_result.CheckOk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨m', check_syscall_sound_ok i eff m m' evs' hchk, hpost⟩
  | CheckReject =>
    rw [check_syscall_for_run_of_reject i eff m hchk] at h
    simp only [Option.some.injEq, reduceCtorEq] at h
  | CheckUnmodeled =>
    rw [check_syscall_for_run_of_unmodeled i eff m hchk] at h
    simp only [Option.some.injEq, reduceCtorEq] at h

/-- The complete half, under the premise: an admitted outcome the
accounting admits is a public-checker success. -/
theorem check_syscall_for_run_complete_ok (i : SyscallInput) (eff : SyscallEffect)
    (m m'' : Model) (evs : List event) (hagree : lookups_agree_at (bv_unsigned i.in_sysno)) :
    (∃ m', syscall_spec i m (Ok eff m' evs) ∧ syscall_post_model m' eff = some m'') →
    check_syscall_for_run i eff m = some (CheckOk m'' evs) := by
  rintro ⟨m', hspec, hpost⟩
  exact check_syscall_for_run_of_ok_some i eff m m' m'' evs
    (check_syscall_complete_ok i eff m m' evs hagree hspec) hpost

/-- Rocq: `ExecutableSpecs.check_syscall_for_run_ok_iff`, under the premise. -/
theorem check_syscall_for_run_ok_iff (i : SyscallInput) (eff : SyscallEffect) (m m'' : Model)
    (evs : List event) (hagree : lookups_agree_at (bv_unsigned i.in_sysno)) :
    check_syscall_for_run i eff m = some (CheckOk m'' evs) ↔
      ∃ m', syscall_spec i m (Ok eff m' evs) ∧ syscall_post_model m' eff = some m'' :=
  ⟨check_syscall_for_run_sound_ok i eff m m'' evs,
   check_syscall_for_run_complete_ok i eff m m'' evs hagree⟩

/-- The outer `none` is exactly the non-halting materialization-fault
premise of `Run.sstep_syscall_materialization_fault`.  The sound half of
Rocq's `check_syscall_for_run_fault_iff`; no premise. -/
theorem check_syscall_for_run_sound_fault (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_syscall_for_run i eff m = none →
    ∃ m' evs, syscall_spec i m (Ok eff m' evs) ∧ m_halted m' = none ∧
      materialize_model_accesses m' (syscall_effect_accesses eff) = none := by
  intro h
  cases hchk : check_syscall i eff m with
  | CheckOk m' evs =>
    cases hpost : syscall_post_model m' eff with
    | some accounted =>
      rw [check_syscall_for_run_of_ok_some i eff m m' accounted evs hchk hpost] at h
      simp only [reduceCtorEq] at h
    | none =>
      refine ⟨m', evs, check_syscall_sound_ok i eff m m' evs hchk, ?_⟩
      cases hh : m_halted m' with
      | some code =>
        rw [syscall_post_model_halted m' eff code hh] at hpost
        simp only [reduceCtorEq] at hpost
      | none =>
        rw [syscall_post_model_running m' eff hh] at hpost
        exact ⟨rfl, hpost⟩
  | CheckReject =>
    rw [check_syscall_for_run_of_reject i eff m hchk] at h
    simp only [reduceCtorEq] at h
  | CheckUnmodeled =>
    rw [check_syscall_for_run_of_unmodeled i eff m hchk] at h
    simp only [reduceCtorEq] at h

/-- The complete half, under the premise. -/
theorem check_syscall_for_run_complete_fault (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (hagree : lookups_agree_at (bv_unsigned i.in_sysno)) :
    (∃ m' evs, syscall_spec i m (Ok eff m' evs) ∧ m_halted m' = none ∧
      materialize_model_accesses m' (syscall_effect_accesses eff) = none) →
    check_syscall_for_run i eff m = none := by
  rintro ⟨m', evs, hspec, hh, hmat⟩
  refine check_syscall_for_run_of_ok_none i eff m m' evs
    (check_syscall_complete_ok i eff m m' evs hagree hspec) ?_
  rw [syscall_post_model_running m' eff hh]
  exact hmat

/-- Rocq: `ExecutableSpecs.check_syscall_for_run_fault_iff`, under the premise. -/
theorem check_syscall_for_run_fault_iff (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (hagree : lookups_agree_at (bv_unsigned i.in_sysno)) :
    check_syscall_for_run i eff m = none ↔
      ∃ m' evs, syscall_spec i m (Ok eff m' evs) ∧ m_halted m' = none ∧
        materialize_model_accesses m' (syscall_effect_accesses eff) = none :=
  ⟨check_syscall_for_run_sound_fault i eff m,
   check_syscall_for_run_complete_fault i eff m hagree⟩

/-- Raw rejection stays raw rejection; accounting faults use the outer
`none` and cannot reach this result.  Rocq:
`ExecutableSpecs.check_syscall_for_run_reject_iff`; no premise, since
neither side mentions the spec. -/
theorem check_syscall_for_run_reject_iff (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_syscall_for_run i eff m = some CheckReject ↔ check_syscall i eff m = CheckReject := by
  cases hchk : check_syscall i eff m with
  | CheckOk m' evs =>
    cases hpost : syscall_post_model m' eff with
    | some accounted =>
      rw [check_syscall_for_run_of_ok_some i eff m m' accounted evs hchk hpost]
      simp only [Option.some.injEq, reduceCtorEq]
    | none =>
      rw [check_syscall_for_run_of_ok_none i eff m m' evs hchk hpost]
      simp only [reduceCtorEq]
  | CheckReject =>
    rw [check_syscall_for_run_of_reject i eff m hchk]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | CheckUnmodeled =>
    rw [check_syscall_for_run_of_unmodeled i eff m hchk]
    simp only [Option.some.injEq, reduceCtorEq]

/-- A fail-closed verdict came from the checker's own decline.  The sound
half of Rocq's `check_syscall_for_run_unmodeled_iff`, under the premise
`check_syscall_sound_unmodeled` needs. -/
theorem check_syscall_for_run_sound_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (hagree : lookups_agree_at (bv_unsigned i.in_sysno)) :
    check_syscall_for_run i eff m = some CheckUnmodeled → syscall_spec i m Unmodeled := by
  intro h
  cases hchk : check_syscall i eff m with
  | CheckOk m' evs =>
    cases hpost : syscall_post_model m' eff with
    | some accounted =>
      rw [check_syscall_for_run_of_ok_some i eff m m' accounted evs hchk hpost] at h
      simp only [Option.some.injEq, reduceCtorEq] at h
    | none =>
      rw [check_syscall_for_run_of_ok_none i eff m m' evs hchk hpost] at h
      simp only [reduceCtorEq] at h
  | CheckReject =>
    rw [check_syscall_for_run_of_reject i eff m hchk] at h
    simp only [Option.some.injEq, reduceCtorEq] at h
  | CheckUnmodeled => exact check_syscall_sound_unmodeled i eff m hagree hchk

/-- Fail-closed syscall outcomes pass through the run adapter unchanged.
The complete half; no premise. -/
theorem check_syscall_for_run_complete_unmodeled (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    syscall_spec i m Unmodeled → check_syscall_for_run i eff m = some CheckUnmodeled := by
  intro hspec
  exact check_syscall_for_run_of_unmodeled i eff m (check_syscall_complete_unmodeled i m eff hspec)

/-- Rocq: `ExecutableSpecs.check_syscall_for_run_unmodeled_iff`, under the premise. -/
theorem check_syscall_for_run_unmodeled_iff (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (hagree : lookups_agree_at (bv_unsigned i.in_sysno)) :
    check_syscall_for_run i eff m = some CheckUnmodeled ↔ syscall_spec i m Unmodeled :=
  ⟨check_syscall_for_run_sound_unmodeled i eff m hagree,
   check_syscall_for_run_complete_unmodeled i eff m⟩

end LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
