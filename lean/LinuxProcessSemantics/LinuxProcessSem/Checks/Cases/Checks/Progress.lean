import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Table

/-! # Checks.Cases.Checks.Progress — receptiveness, exercised on the tables

Pins over `Checks.Progress`, the twin of
`theories/LinuxProcessSem/Checks/Progress.v`.  The Rocq tree has no check
file for it: `receptive` is a theorem, and a theorem needs no test.  What
needs one is the SHAPE the Lean twin had to take — a hypothesis Rocq's
statement does not carry, that the arm the dispatcher holds for the number
is the checked one — and whether that hypothesis is a decoration.  So this
file mirrors nothing and does three things: it runs the argument on both
of its branches, through `receptive_over` on the fixture table
`Checks/Cases/Checks/Sys/Dispatch.lean` builds and through the two
corollaries on the one-arm `exit` table, so that the found-arm branch is
exercised whatever arms `checked_table` holds; it pins the
hypothesis itself, through `receptive_over_hypothesis_iff`, where it holds
and where it fails; and it shows the hypothesis refusing what it is there
to refuse, the witness of an arm the dispatcher does not hold.  Not part
of the trusted specification.

The kernel claims here are `exit`'s and the syscall numbers'.  The `exit`
pins cite `kernel/exit.c` because each states what the dispatcher does
with a witness for `exit` on a concrete input, or which witness `exit`'s
input gets from a table whose arms the dispatcher vouches for; the reading
of that file — `exit` answers on every input — is
`Checks/Cases/Kernel/Exit.lean`'s `exit_never_unmodeled`, which the proofs
use rather than re-derive.  The one pin that mentions neither the
dispatcher nor an agreeing table, the empty table's witness, claims no
kernel behaviour and is tagged so.  The
numbers are cited from the generic table,
`include/uapi/asm-generic/unistd.h`; riscv64 takes the same numbers from
the `asm/unistd_64.h` generated out of `scripts/syscall.tbl`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Progress

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Table

/-- The `exit` input the pins below dispatch: syscall 93 with status 256,
whose low byte is 0. -/
def exit_input : SyscallInput :=
  SyscallInput.mkInput 93 [256, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

section FoundArm

/-! ## The found-arm branch, and what the hypothesis refuses -/

/-- THE FOUND-ARM BRANCH.  At 93 the fixture table holds `fixture_arm_exit`
and `spec_table` holds `exit`, and the two are the same arm, so the witness
the fixture supplies — the halt with the low byte of the status, and a zero
return — is admitted by the dispatcher.  This is `receptive`'s argument on
a table with an arm in it, run on the fixture table so that it does not
turn on which arms `checked_table` holds.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem receptive_over_the_fixture_table_at_exit (m : Model) :
    syscall_spec exit_input m (fixture_arm_exit.ca_witness exit_input m) :=
  receptive_over fixture_table exit_input m rfl

/-- THE FOUND-ARM COROLLARY, with an instance.  `receptive_checked_over` on
the one-arm table holding `exit`'s fixture, whose agreement with the
dispatcher is K2's `arms_agree_admits_the_exit_fixture`: the same admission
as above, reached through the corollary on a table whose agreement is
proved by hand rather than through `checked_table`'s.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem receptive_checked_over_the_exit_fixture (m : Model) :
    syscall_spec exit_input m (table_witness [fixture_arm_exit] exit_input m) :=
  receptive_checked_over [fixture_arm_exit] arms_agree_admits_the_exit_fixture
    exit_input m fixture_arm_exit rfl

/-- THE HYPOTHESIS IS NOT A DECORATION.  `fixture_arm_unmodeled_at_93` is a
well-formed checked arm at 93 — its five obligations hold — and it is not
the arm the dispatcher holds there, which is `exit`'s.  The witness a table
holding it gives `exit`'s input is that arm's, the decline, and the
dispatcher refuses it: `exit` never declines.  Were the agreement not
demanded, `receptive_over` would carry this witness to the dispatcher
through that table; with it demanded, the hypothesis is false for that
table at 93 — `arms_agree_refuses_a_wrong_spec` in
`Checks/Cases/Checks/Sys/Table.lean` — and this pin is the conclusion that
refusal protects.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem a_foreign_arms_witness_is_refused (m : Model) :
    ¬ syscall_spec exit_input m (table_witness [fixture_arm_unmodeled_at_93] exit_input m) := by
  intro h
  exact exit_never_unmodeled (in_arg exit_input 0) exit_input m
    ((dispatch_arm spec_table exit_input m _ _ rfl).mp h)

/-- THE WITNESS AN EMPTY TABLE HAS: over `[]`, `table_witness` answers the
decline — the `nil` case of its no-arm branch, which no number can turn,
so this holds at every input and is stated at `exit`'s because the pin
below composes with it there.  Stated over the explicit empty table rather
than over `checked_table`, so that it does not turn on which arms
`checked_table` holds; what `checked_table`'s own witness answers at
`exit` is `the_trees_witness_at_exit_is_the_decline_iff_the_table_lacks_the_arm`,
two pins below.
model: `table_witness` over `[]` is the decline at every input, the `nil` case of the lookup; no kernel behaviour is claimed -/
theorem the_empty_tables_witness_is_the_decline (m : Model) :
    table_witness ([] : List CheckedArm) exit_input m = Unmodeled := rfl

/-- ROCQ'S UNCONDITIONAL STATEMENT IS FALSE OVER A TABLE MISSING THE ARM.
The dispatcher, holding `exit` at 93, refuses the decline — and the decline
is, by the pin above, the witness the empty table gives `exit`'s input:
`exit` never declines.  The two pins together are `receptive_over []`
without its hypothesis, refuted at one input, and 93 is a number the
hypothesis excludes on any table that lacks the arm.  Stated over
`Unmodeled` and not over `table_witness` so that this pin alone carries
the kernel claim; the pin above has none to carry.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem the_dispatcher_refuses_the_decline_at_exit (m : Model) :
    ¬ syscall_spec exit_input m Unmodeled := by
  intro h
  exact exit_never_unmodeled (in_arg exit_input 0) exit_input m
    ((dispatch_arm spec_table exit_input m _ _ rfl).mp h)

/-- THE TREE'S OWN WITNESS AT `exit`, on any day.  `syscall_spec_witness`
reads `checked_table`, and at `exit`'s input it is the decline exactly when
that table lacks the arm at 93: with no arm the lookup misses and the
no-arm branch answers `Unmodeled`; with an arm, `checked_table_arms` makes
it `exit`'s, its `ca_receptive` puts its witness in `exit`'s spec, and
`exit` never declines, so the witness is not `Unmodeled`.  This is what
the pin two above stated while it was written over `checked_table`, made
table-proof: it holds over the table K2 left, where the right-hand side is
`rfl`, and it holds the day `exit`'s arm lands, where neither side does —
and a `checked_table` whose `exit` arm answered the decline, or a
`table_witness` that ignored the arm it found, fails it.  The proof reads
no arm of `checked_table` by name, so a C ticket appends to the table and
leaves this alone.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem the_trees_witness_at_exit_is_the_decline_iff_the_table_lacks_the_arm (m : Model) :
    syscall_spec_witness exit_input m = Unmodeled
      ↔ lookup_ca checked_table (bv_unsigned exit_input.in_sysno) = none := by
  unfold syscall_spec_witness table_witness
  cases hc : lookup_ca checked_table (bv_unsigned exit_input.in_sysno) with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some c =>
    refine ⟨fun h => ?_, fun h => nomatch h⟩
    have hw : c.ca_witness exit_input m = Unmodeled := h
    have harm := checked_table_arms c (lookup_ca_In checked_table _ c hc)
    rw [lookup_ca_no checked_table _ c hc] at harm
    have hrec := c.ca_receptive exit_input m
    rw [hw] at hrec
    exact (the_dispatcher_refuses_the_decline_at_exit m
      ((dispatch_arm spec_table exit_input m Unmodeled c.ca_arm harm).mpr hrec)).elim

/-- THE WITNESS A TABLE WITH THE ARM HAS: over the one-arm `exit` table the
lookup finds the fixture and the witness is the fixture's own, which the
dispatcher admits (`receptive_checked_over_the_exit_fixture`) and which is
therefore not the decline the dispatcher refuses.  This is the side of the
pin above that `checked_table` reaches since K6a registered `exit`'s arm
(`the_trees_witness_at_exit_is_not_the_decline` in
`Checks/Cases/Checks/Sys/Kernel/Exit.lean`), given an instance here over a
one-arm table too, so that both sides are exercised on a table this file
builds.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem the_one_arm_tables_witness_at_exit_is_not_the_decline (m : Model) :
    ¬ table_witness [fixture_arm_exit] exit_input m = Unmodeled := by
  intro h
  have hadm := receptive_checked_over_the_exit_fixture m
  rw [h] at hadm
  exact the_dispatcher_refuses_the_decline_at_exit m hadm

end FoundArm

section Hypothesis

/-! ## The hypothesis, where it holds and where it fails

`receptive_over_hypothesis_iff` says the one-number equation holds over an
agreeing table exactly where the table has an arm or the dispatcher has
none.  The pins take it at `exit`'s number, spelled as `receptive` spells
it — `bv_unsigned exit_input.in_sysno`, which is 93 — on the two tables
that differ there: the one-arm `exit` table, which has the arm, and the
empty table, which has not — the kind of number `receptive_over` cannot
reach over a table that lacks the arm. -/

/-- Where the table has the arm, the hypothesis holds: the right-to-left
half, on the fact that the lookup finds `exit`'s fixture.
model: `receptive_over_hypothesis_iff` and `arms_agree_admits_the_exit_fixture`; no kernel behaviour is claimed -/
theorem the_hypothesis_holds_where_the_table_has_the_arm :
    lookup_arm spec_table (bv_unsigned exit_input.in_sysno)
      = (lookup_ca [fixture_arm_exit] (bv_unsigned exit_input.in_sysno)).map CheckedArm.ca_arm :=
  (receptive_over_hypothesis_iff [fixture_arm_exit] arms_agree_admits_the_exit_fixture
    (bv_unsigned exit_input.in_sysno)).mpr (Or.inl (by decide))

/-- Where the dispatcher has an arm and the table has none, the hypothesis
fails: the left-to-right half over the empty table, whose agreement is
vacuous, leaves two cases and refutes both — the empty lookup finds
nothing, and the dispatcher's lookup at `exit`'s number is not `none`.
model: `receptive_over_hypothesis_iff`; no kernel behaviour is claimed -/
theorem the_hypothesis_fails_where_only_the_dispatcher_has_the_arm :
    ¬ lookup_arm spec_table (bv_unsigned exit_input.in_sysno)
        = (lookup_ca ([] : List CheckedArm) (bv_unsigned exit_input.in_sysno)).map
            CheckedArm.ca_arm := by
  intro h
  rcases (receptive_over_hypothesis_iff [] (fun _ hc => nomatch hc)
    (bv_unsigned exit_input.in_sysno)).mp h with hs | hn
  · exact absurd hs (by decide)
  · have hexit : (lookup_arm spec_table (bv_unsigned exit_input.in_sysno)).isSome = true := by
      decide
    rw [hn] at hexit
    exact absurd hexit (by decide)

end Hypothesis

section NoArm

/-! ## The no-arm branch

0 is `__NR_io_setup`, which neither `spec_table` nor `checked_table`
carries.  The fixture table DOES carry an arm at 0 — `fixture_arm_unmodeled`,
the fail-closed arm — so its no-arm branch is run at 1, `__NR_io_destroy`,
which no table carries. -/

/-- On the tree's own table the witness at 0 is the decline, …
kernel: include/uapi/asm-generic/unistd.h:__NR_io_setup@v6.18.46 -/
theorem the_witness_declines_io_setup (m : Model) :
    syscall_spec_witness (SyscallInput.mkInput 0 [] (fun _ => none) (fun _ => none)) m
      = Unmodeled := by
  have hnone : lookup_ca checked_table
      (bv_unsigned (SyscallInput.mkInput 0 [] (fun _ => none) (fun _ => none)).in_sysno)
      = none := by
    apply lookup_ca_checked_table_none <;> decide
  simp only [syscall_spec_witness, table_witness, hnone]

/-- …and the dispatcher admits it: `receptive_unlisted` at 0, both lookups
missing.
kernel: include/uapi/asm-generic/unistd.h:__NR_io_setup@v6.18.46 -/
theorem receptive_unlisted_at_io_setup (m : Model) :
    syscall_spec (SyscallInput.mkInput 0 [] (fun _ => none) (fun _ => none)) m Unmodeled :=
  receptive_unlisted _ m rfl

/-- The same branch through `receptive_over` on the fixture table, at a
number neither table carries.  The fixture table is not empty, so the
lookup that misses here is a real miss and not the `nil` case.
kernel: include/uapi/asm-generic/unistd.h:__NR_io_destroy@v6.18.46 -/
theorem receptive_over_the_fixture_table_at_io_destroy (m : Model) :
    syscall_spec (SyscallInput.mkInput 1 [] (fun _ => none) (fun _ => none)) m Unmodeled :=
  receptive_over fixture_table _ m rfl

/-- The no-arm corollary with an instance: `receptive_unlisted_over` on the
one-arm `exit` table at 1, a number neither it nor the dispatcher carries.
kernel: include/uapi/asm-generic/unistd.h:__NR_io_destroy@v6.18.46 -/
theorem receptive_unlisted_over_the_exit_table_at_io_destroy (m : Model) :
    syscall_spec (SyscallInput.mkInput 1 [] (fun _ => none) (fun _ => none)) m
      (table_witness [fixture_arm_exit]
        (SyscallInput.mkInput 1 [] (fun _ => none) (fun _ => none)) m) :=
  receptive_unlisted_over [fixture_arm_exit] arms_agree_admits_the_exit_fixture _ m rfl

end NoArm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Progress
