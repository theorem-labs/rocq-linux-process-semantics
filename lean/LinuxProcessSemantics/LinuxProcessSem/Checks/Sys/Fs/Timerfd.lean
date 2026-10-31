import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Timerfd
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Fs.Timerfd — the timerfd_create (85) checker and witness, with their proofs

Mirrors two Rocq files: `theories/LinuxProcessSem/Checks/Sys/Fs/Timerfd.v`,
the checker `check_timerfd_create` with the four lemmas relating it to the
spec, and `theories/LinuxProcessSem/Checks/Witness/Fs/Timerfd.v`, the
witness `timerfd_create_witness` with `timerfd_create_witness_ok`.  Both
answer to `Sys/Fs/Timerfd.lean`, the twin of the spec they are judged
against, and through it to Linux `fs/timerfd.c`.  Not part of the trusted
specification: the checker is executable and the witness is a value, and
the lemmas are what tie either to `timerfd_create_spec`.

ONE FILE FOR TWO, and why.  Rocq keeps the checker under `Checks/Sys/`
and the witness under `Checks/Witness/`, a split older than its
`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`, which now imports both
halves and is imported by `ExecutableSpecs.v` and `Progress.v` alike.  The
Lean tree's dispatcher takes a record instead — `CheckedArm`, in
`Checks/Sys/Dispatch.lean` — carrying the checker and the witness in one
value with the five proofs between them, and the arm's registration in
`Checks/Arms/Fs/Timerfd.lean` — the conformance ticket's first step, not
this file's — builds one such arm from the five lemmas below.  So the two
halves are written where that arm reads them.  Every definition keeps its
Rocq name; the only thing the merge changes is the import line.

WHAT IS NOT HERE, and where it goes.  Rocq states
`check_timerfd_create_frame` in `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`
beside the ledger alternation it feeds — the `*_frame` alternative of
`check_syscall_preserves_vm_wf`, the shape for an arm that never writes
the ledger.  The Lean tree states a checker's frame lemma in the
checker's own file (`Checks/Sys/Fs/Select.lean`, `Checks/Sys/Fs/Sync.lean`)
and its `VmMapsDisjoint` twin derives the arm's preservation from it once
the arm is registered; this file states none, since the frame fact is
the registration's (V-Fs-Timerfd), which states it in
`Checks/Arms/Fs/Timerfd.lean` beside the arm it feeds.  So nothing in this
file names `vm_maps` or the ledger.  This file
imports the spec, the checker prelude and the witness prelude — the last
is the one piece of the checked-table chain the witness proof cannot do
without — and nothing of the dispatcher or the ledger: the dispatcher
needs this file only once an arm is registered, and the ledger is that
registration's.

SPELLINGS, said once.  The flag test is on the word, `bv_and` against the
complement of the mask, where Rocq's is `Z.ldiff` on `bv_unsigned`;
`Sys/Fs/Timerfd.lean`'s header argues the two agree, and the gate below is
spelled exactly as that file spells its `timerfd_create_einval_b`, so that
`timerfd_gate`'s six case splits name the same six terms in both. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Timerfd

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Timerfd
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## The checker -/

/-- The gate is WRITTEN OUT rather than taken from
`Sys.Fs.Timerfd.timerfd_create_einval_b`, and the four lemmas below are
what make the repetition worth its cost: they force this statement and
the spec's to coincide.  Importing the spec's predicate would leave a
wrong gate agreeing with itself, which is the reason the Rocq
`Checks/Sys/Kernel/Time/PosixTimers.v` restates its envelope bound
instead of sharing it.

Note what the repetition does NOT buy, because the difference matters
here more than usual: an identical MISTAKE made in both files still
closes every proof.  These lemmas relate the checker to the spec and
never either to Linux.  The claim that the accepted set really is
Linux's — `flags & ~TFD_CREATE_FLAGS` truthy, or a clock id off the five
of `SYSCALL_DEFINE2(timerfd_create)` (fs/timerfd.c:404-410, Linux
v6.18.46, commit 1f99e9ab748f), is the one `return -EINVAL` of the call,
decided before the `capable(CAP_WAKE_ALARM)` test at fs/timerfd.c:412-415 — is
settled outside the proofs: by the kernel lines the spec's docstring
reads, by `testing/syscall-check/tests/timerfd_create.c`, which offers the
Rocq checker concrete answers a real kernel would never give, and by the
pins of `Checks/Cases/Checks/Sys/Fs/Timerfd.lean`, which offer this one
the same.

Why `check_ret_only` and not a shape with writes: the kernel returns at
fs/timerfd.c:410 before the `kzalloc` at fs/timerfd.c:417 (Linux v6.18.46), so the
-EINVAL touches nothing.  Why `CheckUnmodeled` and never `CheckReject` on
the other half: the spec declines there, and
`check_timerfd_create_complete_unmodeled` is the direction that forbids
grading a descriptor the model cannot hold.  Rocq:
`Checks.Sys.Fs.Timerfd.check_timerfd_create`. -/
def check_timerfd_create (clkid flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if !(bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 TFD_CREATE_FLAGS))) == 0) ||
     !(bv_unsigned clkid == CLOCK_REALTIME ||
       bv_unsigned clkid == CLOCK_MONOTONIC ||
       bv_unsigned clkid == CLOCK_BOOTTIME ||
       bv_unsigned clkid == CLOCK_REALTIME_ALARM ||
       bv_unsigned clkid == CLOCK_BOOTTIME_ALARM)
  then check_ret_only eff (errno_ret EINVAL) m []
  else CheckUnmodeled

/-- Both sides of every proof below branch on the same six equalities.
Splitting all six — rather than the assembled condition — is what keeps
the tactic from depending on the two files spelling the disjunction with
the same associativity, which is exactly the coincidence the restatement
exists to avoid relying on.  Rocq: the `timerfd_gate` Ltac.

The six `cases` replace each test by its Boolean in the GOAL and record it
as an equation; the `simp only` then carries the six equations into the
hypothesis the optional location names, folds the Boolean algebra of the
two gates to a literal, reduces both `if`s, and closes any branch whose
hypothesis has become a constructor mismatch (`reduceCtorEq`).

The simp set is the UNION of what the five callers need, and the linter
cannot tell you so: `linter.unusedSimpArgs` does not read inside a macro.
Expanded by hand into each caller (scratch compile, 2026-09-19), the six
equations are spare on the goal-only witness proof — `cases` already
rewrote the goal — and `reduceCtorEq` is spare on the two `Unmodeled`
shapes and the witness, where no hypothesis becomes a constructor
mismatch; it fires on both `Ok` shapes and is load-bearing on
`check_timerfd_create_sound_ok` alone, whose 31 gate-false branches keep
`h : CheckUnmodeled = CheckOk m' evs` without it (`complete_ok`'s `first`
closes its branch by `cases` either way).  Each entry fires in some
caller, and `Bool.true_or`/`Bool.false_or` fired in none, because every
operand is a literal by the time a `||` is visited and the right-operand
lemmas cover the four cases.  Re-measure the same way before adding an
entry. -/
macro "timerfd_gate " clkid:ident flags:ident loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (
    cases hflag : (bv_unsigned (bv_and $flags (bv_not (Z_to_bv 64 TFD_CREATE_FLAGS))) == 0) <;>
    cases hrt : (bv_unsigned $clkid == CLOCK_REALTIME) <;>
    cases hmono : (bv_unsigned $clkid == CLOCK_MONOTONIC) <;>
    cases hboot : (bv_unsigned $clkid == CLOCK_BOOTTIME) <;>
    cases hrta : (bv_unsigned $clkid == CLOCK_REALTIME_ALARM) <;>
    cases hbta : (bv_unsigned $clkid == CLOCK_BOOTTIME_ALARM) <;>
    simp only [hflag, hrt, hmono, hboot, hrta, hbta, Bool.not_true, Bool.not_false,
      Bool.or_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] $[$loc]?))

/-- Accepting is sound: an accepted effect is the -EINVAL return the spec
admits, over the same model, with no event.  Rocq:
`Checks.Sys.Fs.Timerfd.check_timerfd_create_sound_ok`. -/
theorem check_timerfd_create_sound_ok (clkid flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_timerfd_create clkid flags eff m = CheckOk m' evs) :
    timerfd_create_spec clkid flags i m (Ok eff m' evs) := by
  unfold check_timerfd_create at h
  unfold timerfd_create_spec timerfd_create_einval_b
  timerfd_gate clkid flags at h ⊢
  all_goals
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _

/-- Declining is sound: the checker declines only where the spec does,
since `check_ret_only` never declines.  Rocq:
`Checks.Sys.Fs.Timerfd.check_timerfd_create_sound_unmodeled`. -/
theorem check_timerfd_create_sound_unmodeled (clkid flags : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput) (h : check_timerfd_create clkid flags eff m = CheckUnmodeled) :
    timerfd_create_spec clkid flags i m Unmodeled := by
  unfold check_timerfd_create at h
  unfold timerfd_create_spec timerfd_create_einval_b
  timerfd_gate clkid flags at h ⊢
  all_goals first
    | exact unmodeled_intro i m
    | exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Accepting is complete: the one outcome the spec admits on the -EINVAL
half is accepted, with the spec's own post-model and events.  The
hypothesis arrives as the spec applied to the outcome; the ascription
restates it as the equation `Monad.pure` unfolds to, which `injection`
then reads.  Rocq: `Checks.Sys.Fs.Timerfd.check_timerfd_create_complete_ok`. -/
theorem check_timerfd_create_complete_ok (clkid flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : timerfd_create_spec clkid flags i m (Ok eff m' evs)) :
    check_timerfd_create clkid flags eff m = CheckOk m' evs := by
  unfold timerfd_create_spec timerfd_create_einval_b at h
  unfold check_timerfd_create
  timerfd_gate clkid flags at h ⊢
  all_goals first
    | (have h' : (Ok eff m' evs : outcome SyscallEffect) = Unmodeled := h
       cases h')
    | (have h' : (Ok eff m' evs : outcome SyscallEffect)
           = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
       injection h' with heff hm hevs
       subst heff hm hevs
       exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)

/-- Declining is complete: where the spec declines, the checker declines
whatever effect it is offered.  This is the fail-closed direction — a
descriptor for `CLOCK_MONOTONIC`, or the -EPERM `capable(CAP_WAKE_ALARM)`
gives an unprivileged caller on the alarm ids (fs/timerfd.c:412-415, Linux
v6.18.46), is `CheckUnmodeled` and never `CheckReject`.  Rocq:
`Checks.Sys.Fs.Timerfd.check_timerfd_create_complete_unmodeled`. -/
theorem check_timerfd_create_complete_unmodeled (clkid flags : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect) (h : timerfd_create_spec clkid flags i m Unmodeled) :
    check_timerfd_create clkid flags eff m = CheckUnmodeled := by
  unfold timerfd_create_spec timerfd_create_einval_b at h
  unfold check_timerfd_create
  timerfd_gate clkid flags at h ⊢
  all_goals
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'

/-! ## The witness -/

/-- The gate is written out for the third time; `check_timerfd_create` says
why the three layers restate it rather than share one predicate.

`Unmodeled` IS an admissible outcome, so the declined half needs no
invented answer — the spec's own arm is `unmodeled`, and exhibiting it
is what makes this total.  Rocq's `socket_witness` takes the same shape
for the same reason.  `ret_outcome` is `Checks/Witness/Prelude.lean`'s:
the bare return over the model, no event, which is the shape
`check_ret_only` accepts.  Rocq:
`Checks.Witness.Fs.Timerfd.timerfd_create_witness`. -/
def timerfd_create_witness (clkid flags : word) (m : Model) : outcome SyscallEffect :=
  if !(bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 TFD_CREATE_FLAGS))) == 0) ||
     !(bv_unsigned clkid == CLOCK_REALTIME ||
       bv_unsigned clkid == CLOCK_MONOTONIC ||
       bv_unsigned clkid == CLOCK_BOOTTIME ||
       bv_unsigned clkid == CLOCK_REALTIME_ALARM ||
       bv_unsigned clkid == CLOCK_BOOTTIME_ALARM)
  then ret_outcome (errno_ret EINVAL) m
  else Unmodeled

/-- The witness is admitted at every input, which is what the progress
argument consumes.  Rocq:
`Checks.Witness.Fs.Timerfd.timerfd_create_witness_ok`. -/
theorem timerfd_create_witness_ok (clkid flags : word) (i : SyscallInput) (m : Model) :
    timerfd_create_spec clkid flags i m (timerfd_create_witness clkid flags m) := by
  unfold timerfd_create_spec timerfd_create_einval_b timerfd_create_witness
  timerfd_gate clkid flags
  all_goals first
    | exact pure_ok _ i m
    | exact unmodeled_intro i m

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Timerfd
