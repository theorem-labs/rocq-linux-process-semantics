import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Exit

/-! # Checks.Cases.Checks.Sys.Dispatch — the checked arm, exercised

Pins over `Checks.Sys.Dispatch`, the twin of the first part of
`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`.  The Rocq tree has no
check file for it, so this file mirrors nothing: these are the Lean tree's
tests for what the twin ports, in the place every pin in this tree lives so
that `tools/check_lean_pins.py` reads them.  Not part of the trusted
specification.

WHAT IS UNDER TEST, and it is not a syscall.  `CheckedArm` is the shape a
checker must have before the dispatcher will believe it: five proofs tying
an executable acceptor and a progress witness to one relational spec.  The
claim the record makes is that those five are not documentation but
construction — that an acceptor which is too permissive, too restrictive,
or which declines where its spec answers, cannot be packaged as an arm at
all.  A claim of that kind is tested by building one and by showing what
the five fields refuse, so this file does both:

- `fixture_arm_exit` is a complete arm over `Sys.Kernel.Exit.exit_spec`,
  with all five proofs discharged.  It is a FIXTURE, not the port of
  Rocq's `arm_exit`: the trusted checker is the twin of
  `theories/LinuxProcessSem/Checks/Sys/Kernel/Exit.v` and arrives with its
  own ticket, together with the `Checks/Sys/Table.lean` block that puts it
  in `checked_table`.
  What it buys here is that the scaffold is exercised end to end before
  the first trusted arm exists, on a real syscall spec rather than on a
  shape invented to fit.
- The refutations are one per field, each stated over ANY arm whose spec
  is `exit`'s (or, for the fail-closed field, `unmodeled`), so that what
  is refused is a property of the record and not of a fixture.  The
  cheapest fake is the everywhere-declining checker: `exit` admits an
  outcome at every input, so no arm over `exit`'s spec can carry it
  (`no_lazy_checker_over_exit`), and that is a type error rather than a
  test failure.  The general form, over an arbitrary spec, is true of
  every spec and so is not a pin; that theorem's docstring says why it is
  not stated here.
- `fixture_arm_unmodeled` is the converse, and the reason the rule is
  exactly "a lazy checker needs a lazy spec": over a spec that declines
  everywhere, the everywhere-declining checker is CORRECT, and the five
  fields let it through.
- `fixture_arm_emitting` is the arm `exit` cannot stand in for: its spec
  records an event, so the events position of two fields' conclusions is
  load-bearing somewhere in this file.

The kernel claims here are `exit`'s, and they are the ones
`Checks/Cases/Kernel/Exit.lean` already reads off `kernel/exit.c`; this
file uses those pins rather than restating them, so there is one place to
correct if that reading is ever wrong. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Exit

section WorkedArm

/-! ## A worked arm over `exit` (93)

The fixture's checker is the one
`theories/LinuxProcessSem/Checks/Sys/Kernel/Exit.v` writes for `exit`: the
effect must be the bare return 0 with every ledger empty, and the
post-model is the model with the low byte of `error_code` recorded.  The
witness is `theories/LinuxProcessSem/Checks/Witness/Kernel/Exit.v`'s, with
that file's `ret_outcome` (`Checks/Witness/Prelude.v`) written out, since
the Lean tree has no `Checks/Witness` twin to take it from.  They are
defined here, rather than imported, because the Lean tree had no checker
module when this file was written.  `Checks/Sys/Kernel/Exit.lean` has one
since K6a, and the fixture stays on purpose: `fixture_arm_unmodeled` has no
trusted counterpart, and a fixture that does not import the trusted
checker keeps this file's refusals independent of it, so a change to
`check_exit` cannot move what these pins refuse.  The trusted arm's own
pins are `Checks/Cases/Checks/Sys/Kernel/Exit.lean`'s. -/

/-- `exit`'s acceptor: the bare return 0, and the halt recorded. -/
def fixture_check_exit (code : word) (eff : SyscallEffect) (m : Model) : check_result :=
  check_ret_only eff (Z_to_bv 64 0) (with_halted (bv_and code (Z_to_bv 64 255)) m) []

/-- `exit`'s witness: the one outcome the spec admits. -/
def fixture_exit_witness (code : word) (m : Model) : outcome SyscallEffect :=
  Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (bv_and code (Z_to_bv 64 255)) m) []

/-- A complete `CheckedArm` for `exit` (93).  Every one of the five proofs
is discharged from `Checks/Cases/Kernel/Exit.lean`'s reading of the spec:
`exit_halts_with_low_byte` for the three that relate an accepted effect to
an admitted outcome, `exit_never_unmodeled` for the fail-closed direction,
and `check_ret_only_no_unmodeled` for the fact that this acceptor never
declines. -/
def fixture_arm_exit : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 93 (fun i => exit_spec (in_arg i 0) i)
  ca_check := fun i eff m => fixture_check_exit (in_arg i 0) eff m
  ca_witness := fun i m => fixture_exit_witness (in_arg i 0) m
  ca_sound_ok := by
    intro i eff m m' evs h
    unfold fixture_check_exit at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨heff, hm', hevs⟩ := h
    subst heff
    subst hm'
    subst hevs
    exact (exit_halts_with_low_byte (in_arg i 0) i m _).mpr rfl
  ca_sound_unmodeled := by
    intro i eff m h
    unfold fixture_check_exit at h
    exact absurd h (check_ret_only_no_unmodeled eff (Z_to_bv 64 0) _ [])
  ca_complete_ok := by
    intro i eff m m' evs h
    have h' := (exit_halts_with_low_byte (in_arg i 0) i m (Ok eff m' evs)).mp h
    injection h' with heff hm' hevs
    subst heff
    subst hm'
    subst hevs
    unfold fixture_check_exit
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  ca_complete_unmodeled := by
    intro i m eff h
    exact absurd h (exit_never_unmodeled (in_arg i 0) i m)
  ca_receptive := by
    intro i m
    exact (exit_halts_with_low_byte (in_arg i 0) i m _).mpr rfl

/-! ### The `arm_unfold` block

The three lemmas every arm owes, plus its number, in the shape
`Checks/Sys/Table.lean` describes.  Each is `rfl`: the arm IS that
component, and the lemma is what gives `simp only [arm_unfold]` a handle on
it so that a proof written against the plain checker does not have to name
the syscall to make progress. -/

/-- The checker, recovered from the arm.
model: the record's `ca_check` projection on a structure instance; no
kernel behaviour is claimed -/
@[arm_unfold] theorem ca_check_fixture_arm_exit (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    fixture_arm_exit.ca_check i eff m = fixture_check_exit (in_arg i 0) eff m := rfl

/-- The witness, recovered from the arm.
model: the record's `ca_witness` projection on a structure instance; no
kernel behaviour is claimed -/
@[arm_unfold] theorem ca_witness_fixture_arm_exit (i : SyscallInput) (m : Model) :
    fixture_arm_exit.ca_witness i m = fixture_exit_witness (in_arg i 0) m := rfl

/-- The spec arm, recovered from the arm, WITH ITS ARGUMENT: the status is
argument 0, which is where `SYSCALL_DEFINE1(exit, int, error_code)` puts
it.  An arm reading another register would be judging a different word, and
this lemma is where that would show.

Rocq's twin is stated one projection further in, as
`sa_spec (ca_arm arm_exit) i m o = exit_spec (in_arg i 0) i m o`, and
`Checks/Sys/Table.lean`'s block template keeps that shape.  Here it is the
arm-level equality instead, because a pin naming both `sa_spec` and
`exit_spec` is a pin relating two specs, which `tools/check_lean_pins.py`
refuses for the reason its PIN-1 gives; what the outcome really is, is the
next theorem, stated against the kernel rather than against another
definition.
kernel: kernel/exit.c:exit@v6.18.46 -/
@[arm_unfold] theorem ca_arm_fixture_arm_exit :
    fixture_arm_exit.ca_arm = SpecArm.mkSpecArm 93 (fun i => exit_spec (in_arg i 0) i) := rfl

/-- What the arm's spec ADMITS, in the kernel's terms and not another
definition's: one outcome per input, the halt carrying the low byte of
`error_code` and a zero return the program never sees.  This is the statement a
checker proof of soundness has to meet.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem sa_spec_fixture_arm_exit (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    fixture_arm_exit.ca_arm.sa_spec i m o
      ↔ o = Ok (mkEffect (Z_to_bv 64 0) [] [])
              (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) [] :=
  exit_halts_with_low_byte (in_arg i 0) i m o

/-- The number, without unfolding the arm.  `__NR_exit 93`
(include/uapi/asm-generic/unistd.h:258, Linux v6.18.46) is the number's
DEFINITION but not riscv64's source of it: riscv64 builds
`asm/unistd_64.h` from scripts/syscall.tbl (line 120, `93 common exit
sys_exit`) through scripts/Makefile.asm-headers, and
arch/riscv/include/uapi/asm/unistd.h:19-20 includes the built header.
The lemma is `rfl` in both systems — the arm IS that component — and it
is registered in both for one reason: neither `autorewrite with
arm_unfold` nor `simp only [arm_unfold]` unfolds the arm, so without it a
dispatch is stuck at `ca_no arm_exit = 93`, and a proof that names the arm
to make progress is a proof the next arm breaks.
kernel: include/uapi/asm-generic/unistd.h:__NR_exit@v6.18.46 -/
@[arm_unfold] theorem ca_no_fixture_arm_exit : ca_no fixture_arm_exit = 93 := rfl

/-- What the rewrite buys: a goal about the ARM becomes a goal about the
checker, without the proof naming `exit` to get there, and the checker then
answers on a concrete effect.  This is the step every dispatcher proof
takes first.  The right-hand side is `exit`'s own outcome, which is why
the line below is a kernel line and not a model line: a fixture that
recorded the whole word would make this a claim Linux never produces.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem arm_unfold_opens_the_fixture_arm (i : SyscallInput) (m : Model) :
    fixture_arm_exit.ca_check i (mkEffect (Z_to_bv 64 0) [] []) m
      = CheckOk (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) [] := by
  simp only [arm_unfold]
  unfold fixture_check_exit
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- The other three registrations fire too.  Each of these is `rfl` on its
own; the point is the proof script, which reaches the component through
the set and nothing else, so dropping any one `@[arm_unfold]` tag above
turns the matching pin here into `simp made no progress`.  Rocq's
`arm_dispatch` computes the lookup through the number lemma, so the set
carrying a number lemma is part of what the twin has to reproduce.
model: the record's `ca_witness` projection reached through `arm_unfold`;
no kernel behaviour is claimed -/
theorem arm_unfold_opens_the_witness (i : SyscallInput) (m : Model) :
    fixture_arm_exit.ca_witness i m = fixture_exit_witness (in_arg i 0) m := by
  simp only [arm_unfold]

/-- kernel: kernel/exit.c:exit@v6.18.46 -/
theorem arm_unfold_opens_the_arm :
    fixture_arm_exit.ca_arm = SpecArm.mkSpecArm 93 (fun i => exit_spec (in_arg i 0) i) := by
  simp only [arm_unfold]

/-- kernel: include/uapi/asm-generic/unistd.h:__NR_exit@v6.18.46 -/
theorem arm_unfold_opens_the_number : ca_no fixture_arm_exit = 93 := by
  simp only [arm_unfold]

end WorkedArm

section FiveObligations

/-! ## What the five fields refuse

The cheapest fake checker is the one that declines everything: it is
executable and it is sound in the direction anyone tests first, because a
decline admits nothing.  It is not silent — under
`testing/syscall-check/main.ml` every call it sees prints
`*** UNMODELED (fail closed) ***` and the run exits 3, red on every
`conform` case — but it can never say the kernel was WRONG, and a probe
that reaches it is unjudged, never green.  `ca_complete_ok` is what
refuses it, and the refusal is not a test that could be forgotten — an arm
is a record, and the field has to be filled.  The other four fields have
their refutations below, each stated over any arm whose spec is `exit`'s
(or, for the fail-closed direction, over any arm whose spec is
`unmodeled`), so what is refused is a property of the record. -/

/-- No arm over `exit`'s spec can carry the everywhere-declining checker.
The argument is the shape `CheckedArm` imposes and nothing about `exit`
in particular: `ca_complete_ok` sends every `Ok` the spec admits to a
`CheckOk`, so a checker that answers `CheckUnmodeled` everywhere is
complete only for a spec that admits no `Ok` at all.  That general form is
quantified over the spec, so it holds of every spec and would close
against an opaque one — the vacuity `tools/check_lean_pin_vacuity.py`
names as its unbuilt opaque-spec check; its three textual rules do not
read it, and an earlier spelling tripped VAC-1 only by pairing an atom
with its negation — so this file states it on a real arm instead.  `exit`
is not such a spec: it answers at every input —
`SYSCALL_DEFINE1(exit, int, error_code)` runs `do_exit` (kernel/exit.c)
and never returns to the caller, so there is no argument on which the
kernel does something the model has to decline — and an arm that
declined it would decline every `exit` a real program makes:
`*** UNMODELED (fail closed) ***` and exit 3 at the last syscall of every
`conform` case in `testing/syscall-check/tests/exit_status.c`, where the
spec has an answer.  The `i` and `m` the theorem takes are only the
point at which `exit_spec` is asked for its outcome; the conclusion
quantifies over the checker's own arguments.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem no_lazy_checker_over_exit (c : CheckedArm)
    (harm : c.ca_arm = SpecArm.mkSpecArm 93 (fun i => exit_spec (in_arg i 0) i))
    (i : SyscallInput) (m : Model) :
    ¬ (∀ i₁ eff₁ m₁, c.ca_check i₁ eff₁ m₁ = CheckUnmodeled) := by
  intro hlazy
  have hspec : c.ca_arm.sa_spec i m
      (Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []) := by
    rw [harm]
    exact (exit_halts_with_low_byte (in_arg i 0) i m _).mpr rfl
  have hok := c.ca_complete_ok i (mkEffect (Z_to_bv 64 0) [] []) m _ _ hspec
  rw [hlazy i (mkEffect (Z_to_bv 64 0) [] []) m] at hok
  simp only [reduceCtorEq] at hok

/-- …and the fixture arm is such an arm, so the refusal is about something
this file really builds and not only about a hypothetical one.  The
hypothesis is `ca_arm_fixture_arm_exit`.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem fixture_arm_exit_has_no_lazy_checker (i : SyscallInput) (m : Model) :
    ¬ (∀ i₁ eff₁ m₁, fixture_arm_exit.ca_check i₁ eff₁ m₁ = CheckUnmodeled) :=
  no_lazy_checker_over_exit fixture_arm_exit ca_arm_fixture_arm_exit i m

/-- What `ca_sound_ok` refuses: a checker over `exit`'s spec that ACCEPTS
anything but the one outcome.  Whatever the arm's checker is, an effect it
answers `CheckOk` to is the bare return 0 with the ledgers empty, the
post-model is the halt with the low byte, and there are no events; a
checker that let `exit(1)` return 1, or move memory, or emit, cannot be
packaged.  Stated as the three equations so that each half of the
conclusion is owed separately: weakening the field in the events
position alone leaves the third one unprovable.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem no_permissive_checker_over_exit (c : CheckedArm)
    (harm : c.ca_arm = SpecArm.mkSpecArm 93 (fun i => exit_spec (in_arg i 0) i))
    (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : c.ca_check i eff m = CheckOk m' evs) :
    eff = mkEffect (Z_to_bv 64 0) [] []
      ∧ m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m
      ∧ evs = [] := by
  have hs := c.ca_sound_ok i eff m m' evs h
  rw [harm] at hs
  have ho := (exit_halts_with_low_byte (in_arg i 0) i m (Ok eff m' evs)).mp hs
  injection ho with heff hm' hevs
  exact ⟨heff, hm', hevs⟩

/-- The instance a probe would show: `exit` observed returning 1 is not an
effect any arm over `exit`'s spec accepts.  The harness's own negative for
this is `testing/syscall-check/tests/exit_status.c`'s
`reject --mutate exit:ret=1` case.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem no_checker_over_exit_accepts_return_1 (c : CheckedArm)
    (harm : c.ca_arm = SpecArm.mkSpecArm 93 (fun i => exit_spec (in_arg i 0) i))
    (i : SyscallInput) (m m' : Model) (evs : List event) :
    c.ca_check i (mkEffect (Z_to_bv 64 1) [] []) m ≠ CheckOk m' evs := by
  intro h
  have heff := (no_permissive_checker_over_exit c harm i _ m m' evs h).1
  injection heff with hret
  exact absurd hret (by decide)

/-- What `ca_sound_unmodeled` refuses: a checker over `exit`'s spec that
DECLINES anywhere — at any effect, on any model.  `exit` never fails
closed (`exit_never_unmodeled`), so a `CheckUnmodeled` would be a claim
the spec does not make.  This is stronger than `no_lazy_checker_over_exit`
below, which refuses only the checker that declines EVERYWHERE, and it is
the only theorem here that goes through this field.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem no_declining_checker_over_exit (c : CheckedArm)
    (harm : c.ca_arm = SpecArm.mkSpecArm 93 (fun i => exit_spec (in_arg i 0) i))
    (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    c.ca_check i eff m ≠ CheckUnmodeled := by
  intro h
  have hs := c.ca_sound_unmodeled i eff m h
  rw [harm] at hs
  exact exit_never_unmodeled (in_arg i 0) i m hs

/-- What `ca_complete_ok` refuses in its other direction: a checker over
`exit`'s spec that is too RESTRICTIVE, answering `CheckReject` (or a
decline) to the one effect the spec admits.  The checker's answer on that
effect is forced to be the `CheckOk` carrying the spec's own post-model and
events; `no_lazy_checker_over_exit` below is the everywhere-declining
special case.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem every_checker_over_exit_accepts_the_halt (c : CheckedArm)
    (harm : c.ca_arm = SpecArm.mkSpecArm 93 (fun i => exit_spec (in_arg i 0) i))
    (i : SyscallInput) (m : Model) :
    c.ca_check i (mkEffect (Z_to_bv 64 0) [] []) m
      = CheckOk (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) [] := by
  have hspec : c.ca_arm.sa_spec i m
      (Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []) := by
    rw [harm]
    exact (exit_halts_with_low_byte (in_arg i 0) i m _).mpr rfl
  exact c.ca_complete_ok i _ m _ _ hspec

/-- What `ca_receptive` refuses over `exit`: a witness that is not the one
outcome.  An arm whose progress witness answered `Unmodeled`, or a return
of 1, could not be built, because the field asks the spec to accept the
witness and `exit`'s spec admits exactly one outcome.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem every_witness_over_exit_is_the_halt (c : CheckedArm)
    (harm : c.ca_arm = SpecArm.mkSpecArm 93 (fun i => exit_spec (in_arg i 0) i))
    (i : SyscallInput) (m : Model) :
    c.ca_witness i m
      = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) [] := by
  have hr := c.ca_receptive i m
  rw [harm] at hr
  exact (exit_halts_with_low_byte (in_arg i 0) i m (c.ca_witness i m)).mp hr

/-- What `ca_receptive` refuses in general: there is no arm at all over a
spec that admits nothing, because no witness could be produced for it.
This is the field's reason to exist — without it the two soundness fields
and the two completeness fields are all vacuously discharged by the
empty spec — and it is why the everywhere-declining checker needs a spec
that really DECLINES (`unmodeled`, next) rather than one that says
nothing.
model: the record's `ca_receptive` field on a spec with no outcome; no
kernel behaviour is claimed -/
theorem no_arm_where_nothing_is_admitted (i : SyscallInput) (m : Model) :
    ¬ ∃ c : CheckedArm, c.ca_arm = SpecArm.mkSpecArm 0 (fun _ _ _ => False) := by
  intro ⟨c, h⟩
  have hr := c.ca_receptive i m
  rw [h] at hr
  exact hr

/-- What `ca_complete_unmodeled` forces, through the field and not by
looking at any fixture's lambda: every arm over `unmodeled`, at whatever
number, declines every effect.  This is the fail-closed direction the
field's docstring promises — an arm over a declining spec that answered
`CheckReject`, and so reported a conformance failure where the model has
only stopped, cannot be built.
model: the record's `ca_complete_unmodeled` field over `Monad.unmodeled`;
no kernel behaviour is claimed -/
theorem every_arm_over_unmodeled_declines (c : CheckedArm) (n : Int)
    (h : c.ca_arm = SpecArm.mkSpecArm n unmodeled)
    (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    c.ca_check i eff m = CheckUnmodeled := by
  apply c.ca_complete_unmodeled i m eff
  rw [h]
  exact unmodeled_intro i m

/-- The converse, and the reason the rule reads "a lazy checker needs a
lazy spec" rather than "no lazy checkers": over a spec that declines every
call, the everywhere-declining checker is the CORRECT one, and all five
fields are discharged.  A fail-closed arm is a real arm, at any number:
the five obligations do not mention it, which is what lets the same
construction be placed under a number the table carries
(`Checks/Cases/Checks/Sys/Table.lean` puts it under 93 and 94, where the
guards refuse it for reasons the record cannot see). -/
def fixture_arm_unmodeled_at (n : Int) : CheckedArm where
  ca_arm := SpecArm.mkSpecArm n unmodeled
  ca_check := fun _ _ _ => CheckUnmodeled
  ca_witness := fun _ _ => Unmodeled
  ca_sound_ok := by
    intro i eff m m' evs h
    simp only [reduceCtorEq] at h
  ca_sound_unmodeled := by
    intro i eff m _
    exact unmodeled_intro i m
  ca_complete_ok := by
    intro i eff m m' evs h
    have h' : unmodeled i m (Ok eff m' evs) := h
    rw [unmodeled_iff] at h'
    simp only [reduceCtorEq] at h'
  ca_complete_unmodeled := by
    intro i m eff _
    rfl
  ca_receptive := by
    intro i m
    exact unmodeled_intro i m

/-- The fail-closed arm at 0, a number `Sys/SyscallTable.lean` does not
carry, so `checked_table` could not hold it even if someone tried:
`Table.checked_table_follows_spec_table` is what refuses that. -/
def fixture_arm_unmodeled : CheckedArm := fixture_arm_unmodeled_at 0

/-- The construction, once more under the number `exit` really has;
`Checks/Cases/Checks/Sys/Table.lean` is where the table guard refuses it. -/
def fixture_arm_unmodeled_at_93 : CheckedArm := fixture_arm_unmodeled_at 93

/-- The fail-closed arm really does decline every effect, which is what
makes its checker's laziness sound rather than convenient — here through
the field, so it is `every_arm_over_unmodeled_declines` at the fixture.
model: the fixture's own definition; no kernel behaviour is claimed -/
theorem fixture_arm_unmodeled_declines_by_the_field (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    fixture_arm_unmodeled.ca_check i eff m = CheckUnmodeled :=
  every_arm_over_unmodeled_declines fixture_arm_unmodeled 0 rfl i eff m

/-- The fail-closed arm really does decline every effect, which is what
makes its checker's laziness sound rather than convenient.
model: the fixture's own definition; no kernel behaviour is claimed -/
theorem fixture_arm_unmodeled_declines (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    fixture_arm_unmodeled.ca_check i eff m = CheckUnmodeled := rfl

/-- An arm whose spec EMITS.  `exit` records no event, so nothing stated
over `exit` can tell the events position of `ca_sound_ok`'s or
`ca_complete_ok`'s conclusion from `[]`: a record whose fields read
`Ok eff m' []` and `CheckOk m' []` would package `fixture_arm_exit` and
prove every theorem above.  This fixture is where those two positions
are load-bearing.  Its spec admits one outcome — return 0, the model
unchanged, `ev` recorded — and its checker is `check_ret_only` demanding
that event, so under either weakened field the matching proof below
does not close: the sound direction would have to show `[ev] = []` and
the complete direction to produce `CheckOk m []` from a checker that
answers `CheckOk m [ev]`.  The spec is a lambda under no number the
table carries; its only job is to have an event. -/
def fixture_arm_emitting (ev : event) : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 0 (fun _ m o => o = Ok (mkEffect (Z_to_bv 64 0) [] []) m [ev])
  ca_check := fun _ eff m => check_ret_only eff (Z_to_bv 64 0) m [ev]
  ca_witness := fun _ m => Ok (mkEffect (Z_to_bv 64 0) [] []) m [ev]
  ca_sound_ok := by
    intro i eff m m' evs h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨heff, hm', hevs⟩ := h
    subst heff
    subst hm'
    subst hevs
    rfl
  ca_sound_unmodeled := by
    intro i eff m h
    exact absurd h (check_ret_only_no_unmodeled eff (Z_to_bv 64 0) m [ev])
  ca_complete_ok := by
    intro i eff m m' evs h
    have h' : Ok eff m' evs = Ok (mkEffect (Z_to_bv 64 0) [] []) m [ev] := h
    injection h' with heff hm' hevs
    subst heff
    subst hm'
    subst hevs
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  ca_complete_unmodeled := by
    intro i m eff h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect (Z_to_bv 64 0) [] []) m [ev] := h
    simp only [reduceCtorEq] at h'
  ca_receptive := by
    intro i m
    rfl

/-- The event is read back through the field: whatever the emitting arm's
checker accepts carries its event.
model: the events position of `ca_sound_ok`, on a fixture whose spec
records an event; no kernel behaviour is claimed -/
theorem emitting_arm_accepts_only_its_event (ev : event) (i : SyscallInput)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : (fixture_arm_emitting ev).ca_check i eff m = CheckOk m' evs) :
    evs = [ev] := by
  have hs := (fixture_arm_emitting ev).ca_sound_ok i eff m m' evs h
  have h' : Ok eff m' evs = Ok (mkEffect (Z_to_bv 64 0) [] []) m [ev] := hs
  injection h' with _ _ hevs

/-- …and the checker is made to answer with the event, through
`ca_complete_ok`, on the one effect the spec admits.
model: the events position of `ca_complete_ok`, on a fixture whose spec
records an event; no kernel behaviour is claimed -/
theorem emitting_arm_answers_with_its_event (ev : event) (i : SyscallInput) (m : Model) :
    (fixture_arm_emitting ev).ca_check i (mkEffect (Z_to_bv 64 0) [] []) m = CheckOk m [ev] :=
  (fixture_arm_emitting ev).ca_complete_ok i _ m m [ev] rfl

end FiveObligations

section Lookup

/-! ## The lookup, and its agreement with the spec table's

`lookup_ca` is `lookup_arm` over checked arms, and `lookup_ca_arm` says the
two agree.  The pins below are on a fixture table: they were written while
`checked_table` was empty, and a fixture with a fail-closed arm at 0
exercises a case the real table never carries.  The real table's lookups
at 93 and 94 are pinned in `Checks/Cases/Checks/Sys/Kernel/Exit.lean`. -/

/-- Two arms, at 93 and at 0. -/
def fixture_table : List CheckedArm := [fixture_arm_exit, fixture_arm_unmodeled]

/-- The lookup is by number, and finds the arm carrying it.
model: `Dispatch.lookup_ca` on a fixture table; no kernel behaviour is
claimed -/
theorem lookup_ca_finds_93 : lookup_ca fixture_table 93 = some fixture_arm_exit := rfl

/-- …and the second arm, which is reached only by passing the first.
model: `Dispatch.lookup_ca` on a fixture table; no kernel behaviour is
claimed -/
theorem lookup_ca_finds_0 : lookup_ca fixture_table 0 = some fixture_arm_unmodeled := rfl

/-- A number no arm carries is not found.  94 is `exit_group`, whose spec
is `exit`'s and whose arm this table does not hold: the lookup answers to
the NUMBER, so an arm is not reached by having the right spec.
model: `Dispatch.lookup_ca` on a fixture table; no kernel behaviour is
claimed -/
theorem lookup_ca_misses_94 : lookup_ca fixture_table 94 = none := rfl

/-- `lookup_ca_arm` on the fixture table, at a number it carries: the arm
the dispatcher finds is the checked arm's own.  This is the step that lets
a theorem stated over `Specs.syscall_spec` be discharged by a field of the
arm the checker found — in Rocq through `checked_table_arms`; in the Lean
tree the same step goes through `Table.arms_agree` until the table is the
whole surface.
model: `Dispatch.lookup_ca_arm` instantiated at a fixture table; no kernel
behaviour is claimed -/
theorem lookup_ca_arm_at_93 :
    lookup_arm (fixture_table.map CheckedArm.ca_arm) 93
      = (lookup_ca fixture_table 93).map CheckedArm.ca_arm :=
  lookup_ca_arm fixture_table 93

/-- …and at a number it does not, where both sides are `none`.  Without
this the agreement could hold for found arms alone, and the `none` case is
the one the dispatcher's fail-closed answer rests on.
model: `Dispatch.lookup_ca_arm` instantiated at a fixture table; no kernel
behaviour is claimed -/
theorem lookup_ca_arm_at_94 :
    lookup_arm (fixture_table.map CheckedArm.ca_arm) 94
      = (lookup_ca fixture_table 94).map CheckedArm.ca_arm :=
  lookup_ca_arm fixture_table 94

/-- The lookup takes the FIRST arm carrying the number.  On `fixture_table`
the numbers are distinct, so nothing above distinguishes first-match from
last-match; these two tables carry 93 twice and settle it in both orders.
`numbers_follow` keeps a repeat out of `checked_table`, so the rule is
unreachable there — it is pinned because `lookup_ca_arm` relates two
lookups and would hold of a last-match pair just as well.
model: `Dispatch.lookup_ca` on a table with a repeated number; no kernel
behaviour is claimed -/
theorem lookup_ca_takes_the_first_of_two_at_93 :
    lookup_ca [fixture_arm_exit, fixture_arm_unmodeled_at_93] 93 = some fixture_arm_exit := rfl

/-- …and the other order finds the other arm.
model: `Dispatch.lookup_ca` on a table with a repeated number; no kernel
behaviour is claimed -/
theorem lookup_ca_takes_the_first_of_two_at_93_reversed :
    lookup_ca [fixture_arm_unmodeled_at_93, fixture_arm_exit] 93
      = some fixture_arm_unmodeled_at_93 := rfl

end Lookup

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch
