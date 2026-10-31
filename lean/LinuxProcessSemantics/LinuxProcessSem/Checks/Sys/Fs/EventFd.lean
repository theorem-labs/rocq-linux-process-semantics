-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Fs/EventFd.v
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventFd
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! # LinuxProcessSem.Checks.Sys.Fs.EventFd — the eventfd2 (19) checker, its frame lemma and its witness, with their proofs

Ports two Rocq files: `theories/LinuxProcessSem/Checks/Sys/Fs/EventFd.v`,
the checker `check_eventfd2` with the four lemmas relating it to the spec,
and `theories/LinuxProcessSem/Checks/Witness/Fs/EventFd.v`, the witness
`eventfd2_witness` with `eventfd2_witness_ok`.  Both answer to
`Sys/Fs/EventFd.lean`, the twin of the spec they are judged against, and
through it to Linux `fs/eventfd.c`.  Not part of the trusted
specification: the checker is executable and the witness is a value, and
the lemmas are what tie either to `eventfd2_spec`.  The kernel argument
for the spec's one answer and its decline is on the Rocq definition
`eventfd2_spec` and on the Lean twin's docstrings, and is not repeated
here.  Its pins are `Checks/Cases/Checks/Sys/Fs/EventFd.lean`.

ONE ANSWER AND ONE DECLINE, which is the whole shape of this file.  A
flag word with a residue outside `EFD_FLAGS_SET` is -EINVAL, decided from
the word alone; every word that passes the gate is declined.  There is no
third branch: this port has no answer the Rocq file does not have.

ONE FILE FOR TWO, and why.  Rocq keeps the checker under `Checks/Sys/`
and the witness under `Checks/Witness/`, a split older than its
`Checks/Sys/Dispatch.v`, which imports both halves and is imported by
`ExecutableSpecs.v` and `Progress.v` alike (only the second also imports
the witness tree directly).
The Lean tree's
dispatcher takes a record instead — `CheckedArm`, in
`Checks/Sys/Dispatch.lean` — carrying the checker and the witness in one
value with the five proofs between them, and the arm's registration in
`Checks/Arms/Fs/EventFd.lean` — the conformance ticket's first step, not
this file's — builds one such arm from the five theorems below.  So the
two halves are written where that arm reads them, as
`Checks/Sys/Fs/Timerfd.lean` and `Checks/Sys/Fs/Pipe.lean` write theirs.

THE FRAME LEMMA IS HERE.  Rocq states `check_eventfd2_frame` in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, beside the alternation
that consumes it; the Lean tree states each arm's frame lemma in the
checker's own file — the header of `Checks/VmMapsDisjoint.lean` counts the
per-arm frame lemmas as the checker tickets' and not its own — so it is
below, after the four lemmas, and the arm-level fact and its alternative
are the registration's, in `Checks/VmMapsDisjoint/Arms.lean`.
This file imports the spec, the checker prelude and the witness prelude —
the last is the one piece of the checked-table chain the witness proof
cannot do without — and nothing of the dispatcher, the table or the
ledger, which is what lets it land before the arm does.

SPELLINGS, said once.  The gate is on the word, `bv_and` against the
complement of the mask, where Rocq's is `Z.ldiff` on `bv_unsigned` under
`Z.eqb`; `Sys/Fs/EventFd.lean`'s header argues the two agree, and the test
below is spelled exactly as that file spells its `eventfd2_einval_b`, so
that one dichotomy on the shared term drives both sides of every proof. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.EventFd

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventFd
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## The checker -/

/-- The gate is WRITTEN OUT rather than taken from
`Sys.Fs.EventFd.eventfd2_einval_b`, and the four lemmas below are what
make the repetition worth its cost: they force this statement and the
spec's to coincide.  Importing the spec's predicate would leave a wrong
gate agreeing with itself, which is the reason `Checks/Sys/Fs/Timerfd.v`
restates its own gate instead of sharing it.

Note what the repetition does NOT buy, because the difference matters
here more than usual: an identical MISTAKE made in both files still
closes every proof.  These lemmas relate the checker to the spec and
never either to Linux.  The claim that the admitted mask really is
Linux's `EFD_FLAGS_SET` is settled outside the proofs, by
testing/syscall-check/tests/eventfd2.c, which offers the Rocq checker
concrete answers a real kernel would never give, and by the pins of
`Checks/Cases/Checks/Sys/Fs/EventFd.lean`, which offer them to this one.

`check_ret_only` carries the rest of the obligation: it rejects any
effect with a non-empty write, zero, unmap, copy or copy-in ledger,
which is what pins that a conforming run may not smuggle a store past an
arm that stores nothing.  `eventfd2` reads no user memory and writes
none: `do_eventfd` (fs/eventfd.c:390-391, Linux v6.18.46, commit
1f99e9ab748f) decides the -EINVAL from the flag word alone, above the
allocation at line 393 and the counter store at line 399, so the five
ledgers are all empty on the one answer this arm gives (Rocq's docstring
counts six, the return word among them).  A word that passes
the gate is declined, as the spec's arm declines it: Rocq's `unmodeled`,
not a decline of this port.  Rocq: `Checks.Sys.Fs.EventFd.check_eventfd2`. -/
def check_eventfd2 (flags : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if !(bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 EFD_FLAGS_SET))) == 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else CheckUnmodeled

/-- Rocq's `eventfd2_gate`.  Both sides of every proof below branch on
the same equality — the `==` under the negation, not the assembled
condition — which is what keeps the tactic from depending on the two
files spelling the gate with the same negation, exactly the coincidence
the restatement exists to avoid relying on.

`cases hg : …` replaces the test by its Boolean in the goal and records
it as an equation; the `simp only` then carries that equation into the
hypothesis the optional location names, folds the negation, reduces the
`if` and closes any branch whose hypothesis has become a constructor
mismatch (`reduceCtorEq`).  It is `Checks/Sys/Fs/Timerfd.lean`'s
`timerfd_gate` with one test instead of six, and Rocq's
`destruct …; cbn [negb] in *`.  The spec and its gate are unfolded by
each caller rather than by the macro, because the frame lemmas below
reuse it and mention neither. -/
macro "eventfd2_gate " flags:ident loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (
    cases hg : (bv_unsigned (bv_and $flags (bv_not (Z_to_bv 64 EFD_FLAGS_SET))) == 0) <;>
    simp only [hg, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq] $[$loc]?))

/-! ## The four lemmas -/

/-- Accepting is sound: an accepted effect is the -EINVAL return the spec
admits, over the same model, with no event.  Rocq:
`check_eventfd2_sound_ok`. -/
theorem check_eventfd2_sound_ok (flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_eventfd2 flags eff m = CheckOk m' evs) :
    eventfd2_spec flags i m (Ok eff m' evs) := by
  unfold check_eventfd2 at h
  unfold eventfd2_spec eventfd2_einval_b
  eventfd2_gate flags at h ⊢
  all_goals
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _

/-- Declining is sound: the checker declines only where the spec does,
since `check_ret_only` never declines.  Rocq:
`check_eventfd2_sound_unmodeled`. -/
theorem check_eventfd2_sound_unmodeled (flags : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_eventfd2 flags eff m = CheckUnmodeled) :
    eventfd2_spec flags i m Unmodeled := by
  unfold check_eventfd2 at h
  unfold eventfd2_spec eventfd2_einval_b
  eventfd2_gate flags at h ⊢
  all_goals first
    | exact unmodeled_intro i m
    | exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Accepting is complete: the one outcome the spec admits on the -EINVAL
half is accepted, with the spec's own post-model and events.  Rocq:
`check_eventfd2_complete_ok`, whose `sys_unfold; inv_ok` is the
ascription plus `injection` here: the hypothesis arrives as the spec
applied to the outcome, the ascription restates it as the equation
`Monad.pure` unfolds to, and the declined branch closes on its
constructor mismatch. -/
theorem check_eventfd2_complete_ok (flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : eventfd2_spec flags i m (Ok eff m' evs)) :
    check_eventfd2 flags eff m = CheckOk m' evs := by
  unfold eventfd2_spec eventfd2_einval_b at h
  unfold check_eventfd2
  eventfd2_gate flags at h ⊢
  all_goals first
    | (have h' : (Ok eff m' evs : outcome SyscallEffect) = Unmodeled := h
       cases h')
    | (have h' : (Ok eff m' evs : outcome SyscallEffect)
           = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
       injection h' with heff hm hevs
       subst heff hm hevs
       exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)

/-- Declining is complete: where the spec declines, the checker declines
whatever effect it is offered.  This is the fail-closed direction — the
descriptor a word past the gate would create is `CheckUnmodeled` and
never `CheckReject`.  Rocq: `check_eventfd2_complete_unmodeled`. -/
theorem check_eventfd2_complete_unmodeled (flags : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : eventfd2_spec flags i m Unmodeled) :
    check_eventfd2 flags eff m = CheckUnmodeled := by
  unfold eventfd2_spec eventfd2_einval_b at h
  unfold check_eventfd2
  eventfd2_gate flags at h ⊢
  all_goals
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'

/-! ## The frame lemma -/

/-- Rocq: `VmMapsDisjoint.check_eventfd2_frame`, stated there beside
`check_timerfd_create_frame` as its twin, for the same reason: its
refused-word answer is inert.  Linux decides the -EINVAL before the
allocation (`do_eventfd`, fs/eventfd.c:390-393, Linux v6.18.46, commit
1f99e9ab748f), so the arm touches no field of the model, `m_vmmaps`
included.  A `*_frame` rather than a `*_preserves`: nothing is written
for `vm_wf` to be re-established over.

Proved from `check_ret_only_ok_iff` rather than by the `vm_frame` tactics
of `Checks/VmMapsDisjoint.lean`.  A checker may import that file —
`Checks/Sys/Mm/Mmap.lean` does, for arms whose accepted effects rewrite
the ledger, and `Checks/Sys/Fs/Ioctl.lean` for the `vm_frame2` tactic
that closes its own frame lemma — but its chain pulls `Run` and
`Sys/Mm/*` into a file that needs neither, and this lemma needs nothing
from it: the accepted branch is `check_ret_only`, whose `_ok_iff` hands
the model back unchanged, and the declined branch never accepts.  The
arm-level fact the alternation consumes (Rocq's `arm_preserves_vm`, one
alternative per arm) is that file's `arm_preserves_of_frame` applied to
this lemma, stated beside the arm in `Checks/VmMapsDisjoint/Arms.lean` by
the registration. -/
theorem check_eventfd2_frame (flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_eventfd2 flags eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_eventfd2 at h
  eventfd2_gate flags at h
  all_goals
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl

/-! ## The witness — `Checks/Witness/Fs/EventFd.v` -/

/-- The gate is written out a third time; `check_eventfd2` above says why
the three layers restate it rather than share one predicate, and what the
restatement does not buy.

`Unmodeled` IS an admissible outcome, so the declined half needs no
invented answer: the spec's arm past the gate is `unmodeled`, and
exhibiting it is what makes the witness total without claiming a
descriptor the model cannot describe.  The answered half is the -EINVAL
`do_eventfd` returns from the flag word alone (fs/eventfd.c:390-391,
Linux v6.18.46, commit 1f99e9ab748f), with the model untouched and no
event — which is what `Checks/Witness/Prelude.lean`'s `ret_outcome`
spells, and the shape `check_ret_only` accepts.  Rocq:
`Checks.Witness.Fs.EventFd.eventfd2_witness`. -/
def eventfd2_witness (flags : word) (m : Model) : outcome SyscallEffect :=
  if !(bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 EFD_FLAGS_SET))) == 0)
  then ret_outcome (errno_ret EINVAL) m
  else Unmodeled

/-- The witness is admitted at every flag word and every model, which is
what the progress argument consumes.  Rocq:
`Checks.Witness.Fs.EventFd.eventfd2_witness_ok`. -/
theorem eventfd2_witness_ok (flags : word) (i : SyscallInput) (m : Model) :
    eventfd2_spec flags i m (eventfd2_witness flags m) := by
  unfold eventfd2_spec eventfd2_einval_b eventfd2_witness
  eventfd2_gate flags
  all_goals first
    | exact pure_ok _ i m
    | exact unmodeled_intro i m

-- lean-port sentinel: ticket V-pilot-Fs-EventFd appends below this line

/-! ## The descriptor frame the registration owes `Checks/Invariants.lean`

Lean-only: the Rocq tree registers no invariant over `m_fd`, so this has
no Rocq twin.  `Checks/Invariants.lean`'s registry does — `fd_table_unique`
and `pipes_within_capacity` both read the descriptor subsystem — and the
arm registered in `Checks/Arms/Fs/EventFd.lean` owes each of them a fact,
which that file takes from this lemma.  It is here and not there for the
rule that file's header states: a checker's frame lemma lives beside the
checker. -/

/-- `check_eventfd2` hands back the model it was handed on the one
answer it accepts, so the descriptor subsystem is the one it was
handed.  That answer is the -EINVAL `do_eventfd` returns at
fs/eventfd.c:390-391 (Linux v6.18.46, commit 1f99e9ab748f), before
`get_unused_fd_flags` at line 405 reserves a descriptor and before
`fd_install` at line 416 binds one; a flag word that passes the gate,
the only path that binds one, is declined.  The proof is
`check_eventfd2_frame`'s with the other projection at the end. -/
theorem check_eventfd2_fd_state_frame (flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_eventfd2 flags eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold check_eventfd2 at h
  eventfd2_gate flags at h
  all_goals
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.EventFd
