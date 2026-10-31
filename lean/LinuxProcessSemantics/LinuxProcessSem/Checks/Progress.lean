import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Uaccess

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Progress — receptiveness: the model is never stuck

Mirrors `theories/LinuxProcessSem/Checks/Progress.v`, at the baseline
`Checks/Sys/Dispatch.lean`'s header explains (the Rocq file is
byte-identical there to `f44244ad6b80`, the commit BRIEF.md names).  Not
part of the trusted specification.  For every syscall input and every
model state `Specs.syscall_spec` admits SOME outcome — an `Ok` effect or
an explicit `Unmodeled` — and `syscall_spec_witness` names one.  What that
certifies
and what it does not (no ARM is shown inhabited: a `choose` with an
unsatisfiable predicate to the right of an `alt` whose left branch always
answers is invisible here) is argued on the Rocq file's header and not
repeated.

The witnesses are EXPLICIT DEFINITIONS: each arm's `ca_witness` field is a
computable function from the syscall's inputs and the model to one
concrete outcome, and `receptive` states `syscall_spec i m
(syscall_spec_witness i m)`, so the chosen outcome is readable here rather
than recoverable only by stepping through a proof.

WHAT DIFFERS FROM ROCQ, and why.  Rocq's `receptive` has no hypothesis:
its proof rewrites `spec_table` into `map ca_arm checked_table` with
`checked_table_arms`, which holds there because every arm is checked.
The Lean port is partial; `Checks/Sys/Table.lean` says why that equation
is false until the last C ticket lands, and states instead two halves that
hold throughout, of which this file needs one, `arms_agree` — every checked
arm is `spec_table`'s arm for its number.  So the theorem here carries,
as a hypothesis, the one-number instance of the equation Rocq rewrites
with: that the arm the dispatcher holds for this number is the checked
one, if any.  That hypothesis is
discharged for two kinds of number — one with a checked arm
(`receptive_checked`, through `checked_table_arms`) and one no arm carries
at all (`receptive_unlisted`) — and the numbers between the two, with a
spec arm and no checked one, are exactly what the port has not reached.
Those two kinds are the whole of the hypothesis, and that is a theorem
here rather than a sentence: `receptive_over_hypothesis_iff` says that
under `arms_agree` the hypothesis holds at a number exactly when the table
has an arm there or the spec table has none, so the two corollaries cover
every number `receptive` applies to.  Which numbers those are is a fact
about `checked_table`'s contents, and no sentence here states it: over
the table K2 left, which holds no arm, the hypothesis holds only where
`spec_table` has no arm and `receptive` certifies only the dispatcher's
own declines, and each C ticket's arm moves its number across as it
lands.  That is why both corollaries are stated over any agreeing table
first and `Checks/Cases/Checks/Progress.lean` runs them on the fixture
arm, and why that file pins, over the explicit empty table, that Rocq's
unconditional statement is false at `exit` on any table that lacks the
arm — and, over `checked_table` itself, that its witness at `exit` is the
decline exactly when it lacks the arm, a pin that holds before and after
the arm lands.  K8, which lifts this theorem to `Run.sstep`, inherits the
hypothesis for as long as it stands.  The condition under which this
paragraph goes stale: when `Checks/Sys/Table.lean` states the whole
equation `checked_table.map ca_arm = spec_table`, the hypothesis is
discharged for every number and `receptive` takes Rocq's form.

`table_witness` and `receptive_over` are the same definition and the same
argument over ANY table of checked arms.  They are Lean-only, and they are
what lets `Checks/Cases/Checks/Progress.lean` run the found-arm branch on
the fixture arm `Checks/Cases/Checks/Sys/Dispatch.lean` builds over
`exit`, whatever `checked_table` holds; over an empty table that branch
is reached by nothing.

The Rocq file re-exports every witness module.  This one imports the two
the Lean tree has, and the per-syscall witness twins are reached through
`Checks/Sys/Table.lean`, whose arm blocks import them as they land. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

/-- The witness the arms of a table `t` give this input: the found arm's
own, or the decline where `t` has no arm for the number.  Lean-only: it is
the body of Rocq's `syscall_spec_witness`, which writes it in place over
`checked_table`, generalized so that `receptive_over` can be run on a
fixture table (the header says why). -/
def table_witness (t : List CheckedArm) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match lookup_ca t (bv_unsigned i.in_sysno) with
  | some c => c.ca_witness i m
  | none => Unmodeled

/-- The witness for this input's syscall, from the same table the checker
dispatches over.  A number with no checked arm has no witness and is
`Unmodeled` — which is what `receptive` then has to show, once.  Rocq:
`Progress.syscall_spec_witness`. -/
def syscall_spec_witness (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  table_witness checked_table i m

/-! ## The lookup answers with an arm of its table

Two facts about `lookup_ca` that `receptive_checked` needs in order to
reach `checked_table_arms`: the arm found is IN the table, and it carries
the number looked up.  The first is Rocq's `VmMapsDisjoint.lookup_ca_In`,
stated here under its name because this is the first Lean file that needs
it; the second is Lean-only, since Rocq's `receptive` rewrites the whole
table with `checked_table_arms` and never asks which number the arm it
found carries. -/

/-- `lookup_ca` answers with an arm OF the table it searched.  Rocq:
`VmMapsDisjoint.lookup_ca_In`. -/
theorem lookup_ca_In (t : List CheckedArm) (n : Int) (c : CheckedArm)
    (h : lookup_ca t n = some c) : c ∈ t := by
  induction t with
  | nil => simp only [lookup_ca, reduceCtorEq] at h
  | cons a r ih =>
    simp only [lookup_ca] at h
    by_cases hn : ca_no a = n
    · simp only [hn, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact List.Mem.head r
    · simp only [hn, ↓reduceIte] at h
      exact List.Mem.tail a (ih h)

/-- ...and with an arm carrying the number looked up.  Lean-only: it turns
`arms_agree`'s statement at the found arm's own number into one at the
number looked up, a step Rocq's whole-table rewrite never needs. -/
theorem lookup_ca_no (t : List CheckedArm) (n : Int) (c : CheckedArm)
    (h : lookup_ca t n = some c) : ca_no c = n := by
  induction t with
  | nil => simp only [lookup_ca, reduceCtorEq] at h
  | cons a r ih =>
    simp only [lookup_ca] at h
    by_cases hn : ca_no a = n
    · simp only [hn, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact hn
    · simp only [hn, ↓reduceIte] at h
      exact ih h

/-- The hypothesis `receptive_over` carries, characterised.  Over a table
whose arms agree with the dispatcher's, the one-number equation holds
exactly when the table has an arm at the number or the dispatcher has
none; the numbers it excludes are those with a spec arm and no checked
one, which is what the port has not reached.  Lean-only: it is the file
header's exhaustion claim as a statement, and
`Checks/Cases/Checks/Progress.lean` pins each side of it on the fixture
tables. -/
theorem receptive_over_hypothesis_iff (t : List CheckedArm) (ht : arms_agree t) (n : Int) :
    lookup_arm spec_table n = (lookup_ca t n).map CheckedArm.ca_arm
      ↔ ((lookup_ca t n).isSome = true ∨ lookup_arm spec_table n = none) := by
  cases hc : lookup_ca t n with
  | none =>
    constructor
    · intro h
      exact Or.inr h
    · intro h
      cases h with
      | inl h => exact absurd h (by decide)
      | inr h => exact h
  | some c =>
    have harm := ht c (lookup_ca_In t n c hc)
    rw [lookup_ca_no t n c hc] at harm
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      exact harm

/-! ## Receptivity -/

/-- Receptivity in one lookup, over any table of checked arms whose arm for
the number is the dispatcher's: the arm that answers is the arm whose
`ca_receptive` field is exactly this goal, and a number no arm carries is
`unmodeled` on both sides.  No case analysis over the numbers, and nothing
here grows when a syscall is added.  Lean-only; `receptive` is its instance
at `checked_table`, and the file header says what the generalization is
for. -/
theorem receptive_over (t : List CheckedArm) (i : SyscallInput) (m : Model)
    (h : lookup_arm spec_table (bv_unsigned i.in_sysno)
          = (lookup_ca t (bv_unsigned i.in_sysno)).map CheckedArm.ca_arm) :
    syscall_spec i m (table_witness t i m) := by
  unfold syscall_spec dispatch table_witness
  rw [h]
  cases lookup_ca t (bv_unsigned i.in_sysno) with
  | some c => exact c.ca_receptive i m
  | none => exact unmodeled_intro i m

/-- The dispatcher is receptive: `syscall_spec_witness i m` is an admissible
outcome for every input and model state whose number the two tables agree
on — over a table with no arms, no modeled syscall's (the header says so
and why).  The
hypothesis is the one-number instance of the equation Rocq's proof
rewrites with; `receptive_over_hypothesis_iff` says exactly which numbers
satisfy it, and the file header says when it goes.
Rocq: `Progress.receptive`. -/
theorem receptive (i : SyscallInput) (m : Model)
    (h : lookup_arm spec_table (bv_unsigned i.in_sysno)
          = (lookup_ca checked_table (bv_unsigned i.in_sysno)).map CheckedArm.ca_arm) :
    syscall_spec i m (syscall_spec_witness i m) :=
  receptive_over checked_table i m h

/-- The hypothesis discharged for a number with an arm in an agreeing table:
the arm the lookup finds is in the table and carries the number, so
`arms_agree` says it is the dispatcher's.  Stated over any such table so
that it has an instance whatever `checked_table` holds —
`Checks/Cases/Checks/Progress.lean` runs it on the `exit` fixture — since
over an empty table its hypothesis is unsatisfiable and nothing could
reach a wrong statement. -/
theorem receptive_checked_over (t : List CheckedArm) (ht : arms_agree t)
    (i : SyscallInput) (m : Model) (c : CheckedArm)
    (hc : lookup_ca t (bv_unsigned i.in_sysno) = some c) :
    syscall_spec i m (table_witness t i m) := by
  have harm := ht c (lookup_ca_In t _ c hc)
  rw [lookup_ca_no t _ c hc] at harm
  apply receptive_over t i m
  rw [hc]
  exact harm

/-- ...and at `checked_table`, through `checked_table_arms`: the corollary
the header names, an instance of the one above. -/
theorem receptive_checked (i : SyscallInput) (m : Model) (c : CheckedArm)
    (hc : lookup_ca checked_table (bv_unsigned i.in_sysno) = some c) :
    syscall_spec i m (syscall_spec_witness i m) :=
  receptive_checked_over checked_table checked_table_arms i m c hc

/-- The hypothesis discharged for a number no spec arm carries: an agreeing
table cannot hold one either (`arms_agree` would put it in `spec_table`),
so both lookups miss and the witness is the decline the dispatcher gives.
Over any agreeing table, for the same reason as `receptive_checked_over`. -/
theorem receptive_unlisted_over (t : List CheckedArm) (ht : arms_agree t)
    (i : SyscallInput) (m : Model)
    (hn : lookup_arm spec_table (bv_unsigned i.in_sysno) = none) :
    syscall_spec i m (table_witness t i m) := by
  apply receptive_over t i m
  rw [hn]
  cases hc : lookup_ca t (bv_unsigned i.in_sysno) with
  | none => rfl
  | some c =>
    have harm := ht c (lookup_ca_In t _ c hc)
    rw [lookup_ca_no t _ c hc, hn] at harm
    cases harm

/-- ...and at `checked_table`. -/
theorem receptive_unlisted (i : SyscallInput) (m : Model)
    (hn : lookup_arm spec_table (bv_unsigned i.in_sysno) = none) :
    syscall_spec i m (syscall_spec_witness i m) :=
  receptive_unlisted_over checked_table checked_table_arms i m hn

/-- Rocq's corollary, under the same hypothesis: some outcome is admitted.
Rocq: `Progress.receptive_ex`. -/
theorem receptive_ex (i : SyscallInput) (m : Model)
    (h : lookup_arm spec_table (bv_unsigned i.in_sysno)
          = (lookup_ca checked_table (bv_unsigned i.in_sysno)).map CheckedArm.ca_arm) :
    ∃ o, syscall_spec i m o :=
  ⟨_, receptive i m h⟩

end LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
