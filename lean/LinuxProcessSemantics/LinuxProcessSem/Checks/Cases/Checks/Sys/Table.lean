import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch

/-! # Checks.Cases.Checks.Sys.Table — the two table guards, made to fire

Pins over `Checks.Sys.Table`, the twin of the second part of
`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`.  Not part of the trusted
specification.

While `checked_table` was EMPTY — K6a registered its first two arms —
both of its guards held of it for the reason an empty guard always holds,
and a table of a few arms in spec order is not much harder to satisfy.
That is exactly the situation in which a guard is worth nothing and reads
as if it were worth something, so this file does the one thing that separates the
two: it builds the tables the guards are meant to refuse and requires the
refusal.

- `arms_agree` says every checked arm is `spec_table`'s arm for its
  number.  Refuted here on an arm whose number the spec table does not
  carry, and on an arm that carries a real number with the WRONG spec —
  the shape that matters, because such an arm type-checks, proves its own
  five obligations, and would have the dispatcher check `exit` against a
  spec that declines everything.
- `numbers_follow` says the checked numbers are the spec numbers
  restricted to them, in spec order.  Refuted here on a stray number, on a
  transposed pair and on a repeat.

Every theorem below is stated over the two PREDICATES the guards are
stated over, applied to a fixture table.  That is what makes this file a
test of the guards rather than of a copy of them: weaken either
definition in `Checks/Sys/Table.lean` and these refutations stop
closing.

The positive direction is here too, on a one-arm table, because a guard
that refuses everything is no better than one that refuses nothing. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Table

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch

section ArmsGuard

/-! ## `checked_table_arms`: the arm is the dispatcher's arm

An arm's five proof fields tie its checker and its witness to `ca_arm`.
Nothing in the record ties `ca_arm` to the table the dispatcher reads, so
an arm proved correct against a spec nobody dispatches is a well-formed
arm.  That is what this guard is for, and both fixtures below are proof
that it is not decoration. -/

/-- The fixture arm for `exit` satisfies the guard.  Its number is 93,
`exit`'s row in `scripts/syscall.tbl` (pinned with the numeral beside it,
and with the header that defines the value, by `ca_no_fixture_arm_exit`),
and the arm the dispatcher holds there is `exit`'s spec at argument 0 —
the one this arm was built around, so the lookup returns the arm's own.
model: a closed lookup over `Sys/SyscallTable.lean`'s table against the
fixture's own arm; the number's provenance is `ca_no_fixture_arm_exit`'s
evidence -/
theorem arms_agree_admits_the_exit_fixture : arms_agree [fixture_arm_exit] := by
  intro c hc
  cases hc with
  | head => rfl
  | tail _ hnil => cases hnil

/-- The fail-closed construction under `exit_group`'s number, 94: a second
number `spec_table` carries, so that a two-arm table in the spec's order,
and the same two arms transposed, are both expressible.
`numbers_follow` reads numbers only, so what the arm is over does not
matter to the pins that use it. -/
def fixture_arm_unmodeled_at_94 : CheckedArm := fixture_arm_unmodeled_at 94

/-- THE CASE THE GUARD EXISTS FOR.  The arm above is internally correct and
carries a number the model really dispatches, and it is still refused,
because at 93 the dispatcher holds `exit`'s spec and `exit` ANSWERS: it
halts with the low byte of `error_code`, on every input, so a spec that
declines there is not the one the table carries.  Were this arm admitted,
every `exit` in a conformance run would be declined —
`*** UNMODELED (fail closed) ***`, exit 3, on a call the spec answers —
and `check_syscall_sound_unmodeled`, which
`theories/LinuxProcessSem/Checks/ExecutableSpecs.v` states for the whole
dispatcher, would be false at 93.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem arms_agree_refuses_a_wrong_spec (i : SyscallInput) (m : Model) :
    ¬ arms_agree [fixture_arm_unmodeled_at_93] := by
  intro h
  -- The dispatcher's arm at 93, computed: the guard would equate it with the
  -- fixture's, so the two `SpecArm`s and then their two specs are equal.
  have h93 : (some (SpecArm.mkSpecArm 93 (fun i => exit_spec (in_arg i 0) i)) : Option SpecArm)
      = some (SpecArm.mkSpecArm 93 unmodeled) :=
    h fixture_arm_unmodeled_at_93 (List.Mem.head _)
  injection h93 with harm
  injection harm with _hno hspec
  have heq : exit_spec (in_arg i 0) i m
        (Ok (mkEffect (Z_to_bv 64 0) [] [])
          (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) [])
      = unmodeled i m
        (Ok (mkEffect (Z_to_bv 64 0) [] [])
          (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []) :=
    congrFun (congrFun (congrFun hspec i) m) _
  have hok : exit_spec (in_arg i 0) i m
      (Ok (mkEffect (Z_to_bv 64 0) [] [])
        (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []) :=
    (exit_halts_with_low_byte (in_arg i 0) i m _).mpr rfl
  rw [heq, unmodeled_iff] at hok
  simp only [reduceCtorEq] at hok

/-- And an arm under a number the spec table does not carry at all: 0 is
not a syscall this model dispatches, so there is nothing for it to be the
arm of.  This is the shape a typo produces.
model: `lookup_arm` over `Sys/SyscallTable.lean`'s numbers; no kernel
behaviour is claimed -/
theorem arms_agree_refuses_an_unknown_number :
    ¬ arms_agree [fixture_arm_unmodeled] := by
  intro h
  have h0 : (none : Option SpecArm) = some fixture_arm_unmodeled.ca_arm :=
    h fixture_arm_unmodeled (List.Mem.head _)
  simp only [reduceCtorEq] at h0

/-- The guard is `∀ c ∈ t`, not a check on the head: a wrong arm BEHIND a
right one is refused.  The first arm is the exit fixture the guard admits;
the second is the declining arm under 93 it refuses alone, and it is still
refused at position two.  A guard that read only the first arm would accept
this table.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem arms_agree_refuses_a_wrong_arm_behind_a_right_one (i : SyscallInput) (m : Model) :
    ¬ arms_agree [fixture_arm_exit, fixture_arm_unmodeled_at_93] := by
  intro h
  have h93 : (some (SpecArm.mkSpecArm 93 (fun i => exit_spec (in_arg i 0) i)) : Option SpecArm)
      = some (SpecArm.mkSpecArm 93 unmodeled) :=
    h fixture_arm_unmodeled_at_93 (List.Mem.tail _ (List.Mem.head _))
  injection h93 with harm
  injection harm with _hno hspec
  have heq : exit_spec (in_arg i 0) i m
        (Ok (mkEffect (Z_to_bv 64 0) [] [])
          (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) [])
      = unmodeled i m
        (Ok (mkEffect (Z_to_bv 64 0) [] [])
          (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []) :=
    congrFun (congrFun (congrFun hspec i) m) _
  have hok : exit_spec (in_arg i 0) i m
      (Ok (mkEffect (Z_to_bv 64 0) [] [])
        (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []) :=
    (exit_halts_with_low_byte (in_arg i 0) i m _).mpr rfl
  rw [heq, unmodeled_iff] at hok
  simp only [reduceCtorEq] at hok

/-- The two guards in `Checks/Sys/Table.lean` are stated about
`checked_table` itself, not about some other list: these two anchors fail
to elaborate if either theorem is restated over another table.
model: the guard theorems' own statements; no kernel behaviour is claimed -/
theorem checked_table_arms_is_about_the_table : arms_agree checked_table :=
  checked_table_arms

/-- info: LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table.checked_table_arms : arms_agree checked_table -/
#guard_msgs in
#check checked_table_arms

/-- info: LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table.checked_table_follows_spec_table : numbers_follow checked_table -/
#guard_msgs in
#check checked_table_follows_spec_table

/-- model: the guard theorems' own statements; no kernel behaviour is
claimed -/
theorem checked_table_follows_spec_table_is_about_the_table :
    numbers_follow checked_table :=
  checked_table_follows_spec_table

end ArmsGuard

section OrderGuard

/-! ## `numbers_follow`: the numbers, in the spec's order

Each theorem below applies the guard's own predicate to a one- or two-arm
table, so what is decided is the equation the table is held to.  All are
closed computations over the two tables and claim nothing about Linux.

The tables are built from the fail-closed fixture arms rather than from
bare number lists, because `numbers_follow` reads the numbers off real
arms; `fixture_arm_unmodeled` is at 0, `fixture_arm_unmodeled_at_93` at 93
and `fixture_arm_unmodeled_at_94` at 94.  Two carried numbers are what a
transposition needs: a pair with a stray number in it is refused for the
stray, whatever its order. -/

/-- A one-arm table passes: 93 is a number `spec_table` carries.
model: a closed computation over `Sys/SyscallTable.lean`'s numbers -/
theorem numbers_follow_admits_one_arm : numbers_follow [fixture_arm_unmodeled_at_93] := by
  decide

/-- A number outside the spec table is refused: the filter cannot produce
it, so the two sides differ.  0 is not a syscall this model dispatches.
model: a closed computation over `Sys/SyscallTable.lean`'s numbers -/
theorem numbers_follow_refuses_a_stray_number : ¬ numbers_follow [fixture_arm_unmodeled] := by
  decide

/-- A stray number is refused behind a carried one too: the filter yields
`[93]` for this table, and the table's own list is `[93, 0]`.  (This is a
second stray-number case, not an order case — 0 is in neither list.)
model: a closed computation over `Sys/SyscallTable.lean`'s numbers -/
theorem numbers_follow_refuses_a_stray_behind_a_carried_number :
    ¬ numbers_follow [fixture_arm_unmodeled_at_93, fixture_arm_unmodeled] := by
  decide

/-- Two arms under numbers the spec carries, in the spec's order, are
admitted: 93 precedes 94 in `spec_table`, so the filter returns `[93, 94]`
and the equation holds.  This is the positive the order half needs; every
other pin in this section is a refusal.
model: a closed computation over `Sys/SyscallTable.lean`'s numbers -/
theorem numbers_follow_admits_a_pair_in_spec_order :
    numbers_follow [fixture_arm_unmodeled_at_93, fixture_arm_unmodeled_at_94] := by
  decide

/-- The same two arms transposed are refused: the filter returns the spec's
order, `[93, 94]`, whatever order the arms were appended in, and the
table's own list is `[94, 93]`.  Both numbers are carried and neither is
repeated, so ORDER is the only thing this table gets wrong — a guard that
compared the two lists as sets, or by length, would accept it.
model: a closed computation over `Sys/SyscallTable.lean`'s numbers -/
theorem numbers_follow_refuses_a_transposed_pair :
    ¬ numbers_follow [fixture_arm_unmodeled_at_94, fixture_arm_unmodeled_at_93] := by
  decide

/-- A number appended twice is refused: the filter keeps one copy of each
spec number, so a duplicated arm cannot match.  This is what makes
`lookup_ca`'s first-match rule unreachable in `checked_table` — two arms
under one number never get there.
model: a closed computation over `Sys/SyscallTable.lean`'s numbers -/
theorem numbers_follow_refuses_a_repeat :
    ¬ numbers_follow [fixture_arm_unmodeled_at_93, fixture_arm_unmodeled_at_93] := by
  decide

end OrderGuard

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Table
