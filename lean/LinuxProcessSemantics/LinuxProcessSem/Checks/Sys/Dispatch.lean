import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Dispatch — a checked syscall, and the lookup over them

Mirrors the first part of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`:
`CheckedArm`, `ca_no`, `lookup_ca` and `lookup_ca_arm`.  The header's
baseline is the squash of the 2026-09-11 work, where `Dispatch.v` is
byte-identical to `f44244ad6b80`, the commit BRIEF.md names and this port
was read at: a twin's baseline has to be an ancestor of its branch —
`tools/check_lean_spec_parity.py` verifies that for the twins it sweeps,
`Sys/` and its base twins, which this file is not, so the ancestry was
checked by hand and `Table.lean`'s register paragraph says what reads
this header and when — and `f44244ad` stopped being one when that day's
work was rebase-merged.  The table over
them, and the per-arm lemmas, are `Checks/Sys/Table.lean`; the split and
its reason are below.  Like `Checks/Sys/Prelude.lean` this file mirrors no
kernel source and is not part of the trusted specification: what it holds
is the shape a checker must have to be believed, and the trust is carried
by the proofs an arm supplies.

`Sys/Dispatch.lean` makes a syscall a value on the spec side.  This does
the same for the two things the Checks layer adds — the executable checker
and the progress witness — and carries the PROOFS relating them to that
syscall's spec as FIELDS.  The Rocq header argues both halves and is not
repeated here; what a reader of the Lean tree needs is:

- TWO RECORDS, not one, because the trust boundary runs between them.
  `SpecArm` is part of the trusted specification, so a proof about a
  checker cannot live in it.  A `CheckedArm` holds a `SpecArm` and
  everything the Checks layer knows about it.
- The five proof fields are what guard G5 means by structural.  There is
  no way to obtain a `CheckedArm` without them, so a checker that is
  more permissive than its spec, more restrictive than it, or that
  declines where the spec answers, is not a missing test but a type
  error.  `Checks/Cases/Checks/Sys/Dispatch.lean` demonstrates each of
  the five on a worked arm and shows what each one refuses.

THE SPLIT, and why this file is frozen and `Table.lean` is not: every
arm's registration — a V ticket's first step, or the K ticket that carries
a worked example — appends one arm.  Were the table here, each of
them would be editing a file on the freeze list of
`tools/check_lean_port_scope.py` — the list exists because a change to a
shared base file is infrastructure, reviewed as such — for what is
routine work.  `Table.lean` is append-only, one delimited block per arm,
and this file changes only when the record does.

The split runs the OPPOSITE way to the split twins of BRIEF.md section 3,
where a twin re-exports its parts (`Sys/Uapi.lean` and `Sys/Uapi/`) and
the parity reader follows the twin's own imports to find them.  Here the
part imports the whole: `Table.lean` needs `CheckedArm` to build an arm
with, so it cannot be a file this one imports without a cycle.  A reader
looking for `checked_table` and the 89 `arm_*` definitions of the Rocq
file will not find them through this file's imports; they are in
`Checks/Sys/Table.lean`, which imports this one.

Rocq closes its file with the `arm_dispatch` Ltac, which resolves a
dispatch by rewriting with `arm_unfold`, computing the lookup and
rewriting again.  There is no Lean twin yet: the first arms' dispatches
(`exit` and `exit_group`, ticket K6a) close by `rfl` and
`simp only [arm_unfold]` in `Checks/Cases/Checks/Sys/Kernel/Exit.lean`,
and the tactic is written the day an arm's dispatch needs more than that.  The name is taken twice in Rocq —
`DispatchCompute.v` shadows it with a per-arm `first [ erewrite … ]`,
recorded in `bugs/arm-dispatch-defined-twice.md` — so the Lean tree
should pick one name when a twin is written. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude

/-- One modeled syscall, with its checker, its witness, and the five facts
that tie them to its spec.  Holding the proofs as fields is what makes the
dispatcher's theorems constant-size: the theorem does the lookup, the field
does the work.  Rocq: `Dispatch.CheckedArm`. -/
structure CheckedArm where
  mkCheckedArm ::
  /-- The relational spec this arm's checker and witness are judged against.
  Nothing in the record ties it to the arm the dispatcher holds for the
  same number: that is `Table.arms_agree`'s job, and it constrains the
  arms in `checked_table` only. -/
  ca_arm : SpecArm
  /-- The executable acceptor: is this observed effect one the spec admits? -/
  ca_check : SyscallInput → SyscallEffect → Model → check_result
  /-- The progress witness: one outcome the spec admits, for every input. -/
  ca_witness : SyscallInput → Model → outcome SyscallEffect
  /-- Accepting is sound: an accepted effect is one the spec admits. -/
  ca_sound_ok : ∀ i eff m m' evs,
    ca_check i eff m = CheckOk m' evs → ca_arm.sa_spec i m (Ok eff m' evs)
  /-- Declining is sound: where the checker declines, the spec declines. -/
  ca_sound_unmodeled : ∀ i eff m,
    ca_check i eff m = CheckUnmodeled → ca_arm.sa_spec i m Unmodeled
  /-- Accepting is complete: every effect the spec admits is accepted, with
  the spec's own post-model and events. -/
  ca_complete_ok : ∀ i eff m m' evs,
    ca_arm.sa_spec i m (Ok eff m' evs) → ca_check i eff m = CheckOk m' evs
  /-- Declining is complete: where the spec declines, the checker declines,
  whatever effect it is offered.  This is the fail-closed direction — it is
  what forbids a checker that answers `CheckReject` on an unmodeled call and
  so reports a conformance failure where the model has simply stopped. -/
  ca_complete_unmodeled : ∀ i m eff,
    ca_arm.sa_spec i m Unmodeled → ca_check i eff m = CheckUnmodeled
  /-- The witness is admitted: the spec is inhabited at every input, which is
  what the progress argument consumes. -/
  ca_receptive : ∀ i m, ca_arm.sa_spec i m (ca_witness i m)

/-- The number a checked arm answers to, read off its spec arm so the two
tables cannot disagree about it.  Rocq: `Dispatch.ca_no`. -/
def ca_no (c : CheckedArm) : Int := c.ca_arm.sa_no

/-- The first checked arm answering to `n`, if any.  Rocq:
`Dispatch.lookup_ca`. -/
def lookup_ca (t : List CheckedArm) (n : Int) : Option CheckedArm :=
  match t with
  | [] => none
  | c :: r => if ca_no c = n then some c else lookup_ca r n

/-- The two lookups agree, which is what lets a theorem stated over
`Specs.syscall_spec` be discharged by a `CheckedArm`'s field — in Rocq
through `checked_table_arms`; in the Lean tree the same step goes through
`Table.arms_agree` until the table is the whole surface.  Proved once,
by induction on the table; it does not grow with the surface.  Rocq:
`Dispatch.lookup_ca_arm`.

`ca_no` is unfolded before the case split for the reason Rocq's proof gives:
the two tables' guards must be the SAME term before the split reaches both
of them, and `lookup_arm` tests `sa_no` where `lookup_ca` tests `ca_no`. -/
theorem lookup_ca_arm (t : List CheckedArm) (n : Int) :
    lookup_arm (t.map CheckedArm.ca_arm) n
      = (lookup_ca t n).map CheckedArm.ca_arm := by
  induction t with
  | nil => rfl
  | cons c r ih =>
    simp only [List.map_cons, lookup_arm, lookup_ca, ca_no]
    -- After `ca_no` is unfolded the two sides test the SAME guard, so one
    -- case split decides both `if`s at once; `split` would decide only the
    -- one it lands on and leave the other standing.
    by_cases h : c.ca_arm.sa_no = n
    · simp only [h, ↓reduceIte, Option.map]
    · simp only [h, ↓reduceIte, ih]

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
