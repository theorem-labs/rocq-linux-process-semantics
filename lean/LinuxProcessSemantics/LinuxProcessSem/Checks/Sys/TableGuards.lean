import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.TableGuards — what keeps `checked_table` honest

The second part of the `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`
twin, with `Checks/Sys/Dispatch.lean`, which holds the record and the
lookup and says why the two files are separate.  This file holds the two
predicates the table is held to; the table itself is a build product.

THE TABLE IS GENERATED, ONE FILE PER CHECKER TWIN.  A registration — a V
ticket's first step, or the K ticket that carries a worked example —
writes the arm's `CheckedArm` block, its four `arm_unfold` lemmas and
the facts the two alternations need into `Checks/Arms/<Mirror>.lean`,
the file for the checker twin `Checks/Sys/<Mirror>.lean` whose checker
the arm dispatches to, and edits no other hub.
`tools/gen_lean_checked.py` renders the module `Checks.Sys.Table` from
those files into `lean/.lake/generated` on every build: `checked_table`
in syscall-number order, which is `spec_table`'s order, and the two
guard theorems applying the two predicates below to it.  The hand-written table this replaced was one file
every registration edited — twenty `lean: port` and `lean: verify` PRs
in two days rebased over each other through it and through the two
alternations beside it — and `tools/gen_lean_checked.py`'s docstring
says what it refuses in its place.

THE ARMS ROCQ'S TABLE HAS AND THIS ONE LACKS ARE NOT REGISTERED
`unported:` ABOVE, and the omission is deliberate.  Two facts make the
register the wrong place today.  The parity sweep is
`theories/LinuxProcessSem/Sys` (`ROCQ_SUBTREE` in
`tools/check_lean_spec_parity.py`), which does not reach `Checks/`, so an
entry here is read by nothing.  And the entries would be one line per
such arm, each saying one thing — each arm waits on its syscall's executable checker and
witness (its C ticket) and arrives with its registration — whose truth is
the generated table, not a sentence.  IT STOPS BEING FREE the day the sweep
widens to `Checks/`: the reader then wants one parseable name per line (a
glob such as `arm_*` fails the line), and although a register of any
length is legal — only the block's START is held to the reader's
4096-byte window — it is read only on a file that mirrors a Rocq file,
which this one does not: the reader finds a twin's parts through the
twin's IMPORTS (BRIEF.md section 3), and here the part imports the whole,
so the reader must learn this direction or the entries (`checked_table`
and every such arm) must sit in `Checks/Sys/Dispatch.lean`'s header, the
frozen file every registration would then edit.  Whoever widens the sweep
meets this paragraph.  THE BASELINE LINE ABOVE IS READ BY NOTHING TODAY
EITHER: the parity sweep does not reach it,
`tools/check_lean_cases_parity.py` reads its `rocq-cases` coverage block under
`Checks/Cases/` only, and `tools/check_lean_test_monotonic.py` compares a
header against the merge base's, which a new file has none of; from the
next PR that edits this file it is the base that guard holds the header
to, and its ancestry was checked by hand for the PR that added it.  The
baseline is the one `Checks/Sys/Dispatch.lean` explains.

A NUMBER WITH NO ARM IS DECLINED, not checked: the dispatcher that reads
the checked table, the twin of `theories/LinuxProcessSem/Checks/ExecutableSpecs.v`,
answers `CheckUnmodeled` where `lookup_ca` finds nothing, which is the
fail-closed answer.  What a partial table costs is stated, not hidden.  Of
Rocq's four dispatcher theorems in that file, `check_syscall_sound_ok` and
`check_syscall_complete_unmodeled` follow from `arms_agree` alone and hold
at every size; `check_syscall_sound_unmodeled` and
`check_syscall_complete_ok` are FALSE at a number the spec answers and
the checked table lacks, so their Lean twins, and every `iff` built on them,
carry `ExecutableSpecs.lookups_agree_at` at the call's number — the two
lookups agree there — until the surface is complete; that premise holds
wherever the checked table has the arm and wherever neither table carries the
number, and fails only at a number the spec answers and the checked table
lacks.  No
equivalence theorem depends on the checked table — the examples are stated on
the spec through `Run` — so the cost falls on the replay: a probe reaching
an unregistered number is unjudged, never green.
`Checks/Cases/Checks/Sys/Dispatch.lean` exercises the five obligations
and the `arm_unfold` rewrite on a fixture arm over `exit_spec`, so the
scaffold is tested independently of how many trusted arms the table
holds.

WHAT KEEPS THE TWO TABLES TOGETHER.  Rocq states it as one equation,
`map ca_arm checked_table = spec_table`, closed by `reflexivity`.  That
equation is FALSE for a partial port and stays false until the last arm
is registered, so the Lean twin states the two halves that hold
throughout:

- `arms_agree` — every checked arm IS `spec_table`'s arm for its number,
  so no arm can be built around a spec the dispatcher does not hold;
- `numbers_follow` — the checked numbers are the spec numbers restricted
  to them, IN SPEC ORDER, so an arm appended out of order, or under a
  number `spec_table` does not carry, fails the build.

Together with a third fact — `spec_table`'s numbers do not repeat
(`Checks/Examples.lean`'s `modeled_sysnos_nodup`) — the two halves imply
Rocq's equation the day every spec number has an arm: same numbers in the
same order, at most one spec arm per number, agreeing arm by arm.  That
implication is ARGUED here and proved nowhere yet; the lemma, over any
table with nodup as a hypothesis, is owed by the
`Checks/ExecutableSpecs.lean` twin when it needs the full equation, and
until then the two halves are what the dispatcher theorems can use.

Both are PREDICATES on a table rather than statements about
`checked_table` alone.  That is what lets
`Checks/Cases/Checks/Sys/Table.lean` state its refusals about the same
two definitions the guards use, instead of about hand-copies of
them that a weakened guard would leave passing.  Neither is a kernel
claim. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/-- Skip one unequal row using its number fact, leaving the tail lookup
as a separate proof goal.  Generated table proofs repeat this step without
asking definitional equality or the simplifier to walk the remaining list. -/
theorem lookup_ca_cons_of_ne {c : CheckedArm} {r : List CheckedArm} {n : Int}
    {a : Option CheckedArm} (hne : ca_no c ≠ n) (h : lookup_ca r n = a) :
    lookup_ca (c :: r) n = a := by
  simp only [lookup_ca, hne, ↓reduceIte]
  exact h

/-- The matching row is the lookup's answer, independently of the tail. -/
theorem lookup_ca_cons_self {c : CheckedArm} {r : List CheckedArm} {n : Int}
    (h : ca_no c = n) : lookup_ca (c :: r) n = some c := by
  simp only [lookup_ca, h, ↓reduceIte]

/-- Every arm of `t` is the arm `spec_table` carries for its number.  This
is where an arm built around the wrong spec is caught: `ca_check` and
`ca_witness` are tied to `ca_arm` by the record's own proof fields, and
this ties `ca_arm` to the dispatcher.

`numbers_follow` is an `abbrev` because `decide` finds a `Decidable`
instance by unfolding reducible names only; behind a `def` its equation
would have no instance and the guard could not be decided.  `arms_agree`
is one for uniformity: its equation is over `Option SpecArm`, which has
no `DecidableEq` (`sa_spec` is a function), so it is never decided, and
its `intro`/`rfl` proofs would see through a `def`. -/
abbrev arms_agree (t : List CheckedArm) : Prop :=
  ∀ c ∈ t, lookup_arm spec_table (ca_no c) = some c.ca_arm

/-- `t`'s numbers are the spec numbers restricted to them, in spec order.
One decidable equation, so a table that breaks it is refused by `decide`
rather than by a `rfl` that reports nothing. -/
abbrev numbers_follow (t : List CheckedArm) : Prop :=
  t.map ca_no = (arm_numbers spec_table).filter (fun n => (t.map ca_no).contains n)

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
