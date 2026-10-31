import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventFd
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Fs.EventFd — the eventfd2 (19) checker, its frame lemma and its witness, with their proofs

Mirrors two Rocq files: `theories/LinuxProcessSem/Checks/Sys/Fs/EventFd.v`,
the checker `check_eventfd2` with the four lemmas relating it to the spec,
and `theories/LinuxProcessSem/Checks/Witness/Fs/EventFd.v`, the witness
`eventfd2_witness` with `eventfd2_witness_ok`.  Both answer to
`Sys/Fs/EventFd.lean`, the twin of the spec they are judged against, and
through it to Linux `fs/eventfd.c`.  Not part of the trusted
specification: the checker is executable and the witness is a value, and
the lemmas are what tie either to `eventfd2_spec`.  The kernel argument
for the spec's two answers and its decline is on the Rocq definition
`eventfd2_spec` and on the Lean twin's docstrings, and is not repeated
here.  Its pins are `Checks/Cases/Checks/Sys/Fs/EventFd.lean`.

The baseline named above is the 09-11 integration commit, an ancestor of
the branch this file lands on.  Both Rocq files, and the spec they read,
are byte-identical there to what the ticket's `f44244ad6b80` holds, so
the header names the commit the branch can retrace.  Every definition
keeps its Rocq name.

ONE FILE FOR TWO, and why.  Rocq keeps the checker under `Checks/Sys/`
and the witness under `Checks/Witness/`, a split older than its
`Checks/Sys/Dispatch.v`, which imports both halves and is imported by
`ExecutableSpecs.v` and `Progress.v` alike (only the second also imports
the witness tree directly).
The Lean tree's
dispatcher takes a record instead — `CheckedArm`, in
`Checks/Sys/Dispatch.lean` — carrying the checker and the witness in one
value with the five proofs between them, and the arm's registration in
`Checks/Sys/Table.lean` — the conformance ticket's first step, not this
file's — builds one such arm from the five theorems below.  So the two
halves are written where that arm reads them, as
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
ledgers are all empty on either answer this arm gives (Rocq's docstring
counts six, the return word among them).  A word that passes
the gate is declined, as the spec's arm declines it: Rocq's `unmodeled`,
not a decline of this port.  Rocq: `Checks.Sys.Fs.EventFd.check_eventfd2`. -/
def check_eventfd2 (flags : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if !(bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 EFD_FLAGS_SET))) == 0)
  then if (bv_unsigned (bv_and (bv_and flags (bv_not (Z_to_bv 64 EFD_FLAGS_SET)))
                    (bv_not (Z_to_bv 64 (2 ^ 2 + 2 ^ 7 + 2 ^ 14 + 2 ^ 16 + 2 ^ 21 + 2 ^ 22)))) == 0)
       then CheckUnmodeled
       else if bv_eqb eff.eff_ret (errno_ret ENOSYS)
       then check_ret_only eff (errno_ret ENOSYS) m []
       else check_ret_only eff (errno_ret EINVAL) m []
  else CheckUnmodeled

/-- Rocq's `eventfd2_gate`.  Both sides of every proof below branch on
the same equality — the `==` under the negation, not the assembled
condition — which is what keeps the tactic from depending on the two
files spelling the gate with the same negation, exactly the coincidence
the restatement exists to avoid relying on.

The branch is `Bool.eq_false_or_eq_true` on that equality, taken apart
with `rcases`, and NOT `cases hg : …`: the spec's `if` is opened by
`simp only`, whose congruence step leaves the `Decidable` instance a cast
over the folded condition, and generalising the scrutinee out from under
that cast is "not type correct".  A dichotomy hypothesis needs no
generalisation; the `simp only` pass rewrites with it on both sides and
reads the negation and the `if` (Rocq's `destruct …; cbn [negb] in *`).
The spec and its gate are opened first with `-failIfUnchanged`, because
the frame lemma below reuses this macro and mentions neither — a choice
of this port, since Rocq's frame proof (`VmMapsDisjoint.v`) unfolds the
checker and runs `vm_frame2` without the gate tactic — and a `simp only`
that changed nothing would otherwise fail there; an unknown constant is
still reported. -/
macro "eventfd2_gate " flags:term " with " hg:ident : tactic =>
  `(tactic| (simp -failIfUnchanged only [eventfd2_spec, eventfd2_einval_b] at *
             rcases Bool.eq_false_or_eq_true
                 (bv_unsigned (bv_and $flags (bv_not (Z_to_bv 64 EFD_FLAGS_SET))) == 0)
               with $hg:ident | $hg:ident
               <;> rcases Bool.eq_false_or_eq_true
                 (bv_unsigned (bv_and (bv_and $flags (bv_not (Z_to_bv 64 EFD_FLAGS_SET)))
                    (bv_not (Z_to_bv 64 (2 ^ 2 + 2 ^ 7 + 2 ^ 14 + 2 ^ 16 + 2 ^ 21 + 2 ^ 22)))) == 0) with hs | hs
               <;> simp only [$hg:ident, hs, Bool.not_true, Bool.not_false,
                     Bool.false_eq_true, ↓reduceIte] at *))

/-! ## The four lemmas -/

/-- Rocq: `check_eventfd2_sound_ok`. -/
theorem check_eventfd2_sound_ok (flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_eventfd2 flags eff m = CheckOk m' evs) :
    eventfd2_spec flags i m (Ok eff m' evs) := by
  unfold check_eventfd2 at h
  eventfd2_gate flags with hg
  all_goals try (solve | cases h)
  all_goals
    split at h
    · rw [check_ret_only_ok_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (pure_ok _ i _)
    · rw [check_ret_only_ok_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inl (pure_ok _ i _)

/-- Rocq: `check_eventfd2_sound_unmodeled`. -/
theorem check_eventfd2_sound_unmodeled (flags : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_eventfd2 flags eff m = CheckUnmodeled) :
    eventfd2_spec flags i m Unmodeled := by
  unfold check_eventfd2 at h
  eventfd2_gate flags with hg
  all_goals first
    | exact unmodeled_intro i m
    | split at h <;> exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `check_eventfd2_complete_ok`.  Arm for arm with Rocq's proof:
`sys_unfold` opens the monad and `inv_ok` takes the outcome equation
apart, closing the declined branch on its constructor mismatch and
substituting the admitted one's components; the `check_ret_only_ok_iff`
step then applies to whatever is left, which is the admitted branch
alone. -/
theorem check_eventfd2_complete_ok (flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : eventfd2_spec flags i m (Ok eff m' evs)) :
    check_eventfd2 flags eff m = CheckOk m' evs := by
  unfold check_eventfd2
  eventfd2_gate flags with hg
  all_goals try (solve | cases h)
  all_goals
    change (Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m []) ∨
      (Ok eff m' evs = Ok (mkEffect (errno_ret ENOSYS) [] []) m []) at h
    rcases h with h | h <;> cases h <;> rfl

/-- Rocq: `check_eventfd2_complete_unmodeled`.  The declined branch is a
`CheckUnmodeled = CheckUnmodeled` the gate's pass closes; the answered
branch has a disjunction of impossible outcome equations once the monad
is opened, and `inv_ok` closes it. -/
theorem check_eventfd2_complete_unmodeled (flags : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : eventfd2_spec flags i m Unmodeled) :
    check_eventfd2 flags eff m = CheckUnmodeled := by
  unfold check_eventfd2
  eventfd2_gate flags with hg
  all_goals (sys_unfold; inv_ok)

/-! ## The frame lemma -/

/-- Rocq: `VmMapsDisjoint.check_eventfd2_frame`, stated there beside
`check_timerfd_create_frame` as its twin, for the same reason: its
refused-word answers are inert: kernel/sys_ni.c `sys_ni_syscall`
(Linux v6.18.46) returns -ENOSYS without effects, and Linux decides
-EINVAL before the allocation (`do_eventfd`, fs/eventfd.c:390-393,
Linux v6.18.46, commit 1f99e9ab748f), so the arm touches no field of
the model, `m_vmmaps` included.  A `*_frame` rather than a
`*_preserves`: nothing is written for `vm_wf` to be re-established
over.

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
  eventfd2_gate flags with hg
  all_goals try (solve | cases h)
  all_goals
    split at h <;> rw [check_ret_only_ok_iff] at h
    all_goals obtain ⟨-, rfl, -⟩ := h; rfl

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
  then if (bv_unsigned (bv_and (bv_and flags (bv_not (Z_to_bv 64 EFD_FLAGS_SET)))
                    (bv_not (Z_to_bv 64 (2 ^ 2 + 2 ^ 7 + 2 ^ 14 + 2 ^ 16 + 2 ^ 21 + 2 ^ 22)))) == 0)
       then Unmodeled
       else ret_outcome (errno_ret EINVAL) m
  else Unmodeled

/-- The witness is admitted at every flag word and every model, which is
what the progress argument consumes.  Rocq:
`Checks.Witness.Fs.EventFd.eventfd2_witness_ok`. -/
theorem eventfd2_witness_ok (flags : word) (i : SyscallInput) (m : Model) :
    eventfd2_spec flags i m (eventfd2_witness flags m) := by
  unfold eventfd2_witness
  eventfd2_gate flags with hg
  all_goals first
    | exact unmodeled_intro i m
    | exact Or.inl (pure_ok _ i m)

-- lean-port sentinel: ticket V-pilot-Fs-EventFd appends below this line

/-! ## The descriptor frame the registration owes `Checks/Invariants.lean`

Lean-only: the Rocq tree registers no invariant over `m_fd`, so this has
no Rocq twin.  `Checks/Invariants.lean`'s registry does — `fd_table_unique`
and `pipes_within_capacity` both read the descriptor subsystem — and the
arm registered in `Checks/Sys/Table.lean` owes each of them a fact, which
that file takes from this lemma.  It is here and not there for the rule
that file's header states: a checker's frame lemma lives beside the
checker. -/

/-- `check_eventfd2` hands back the model it was handed on either
answer it accepts, so the descriptor subsystem is the one it was
handed.  The -ENOSYS comes from kernel/sys_ni.c `sys_ni_syscall`
(Linux v6.18.46), which touches nothing. The other answer is the
-EINVAL `do_eventfd` returns at fs/eventfd.c:390-391 (Linux v6.18.46,
commit 1f99e9ab748f), before `get_unused_fd_flags` at line 405
reserves a descriptor and before `fd_install` at line 416 binds one; a
flag word that passes the gate, the only path that binds one, is
declined.  The proof is `check_eventfd2_frame`'s with the other
projection at the end. -/
theorem check_eventfd2_fd_state_frame (flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_eventfd2 flags eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold check_eventfd2 at h
  eventfd2_gate flags with hg
  all_goals try (solve | cases h)
  all_goals
    split at h <;> rw [check_ret_only_ok_iff] at h
    all_goals obtain ⟨-, rfl, -⟩ := h; rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.EventFd
