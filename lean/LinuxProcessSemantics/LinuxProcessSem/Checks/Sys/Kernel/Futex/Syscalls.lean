import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Futex.Syscalls

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Kernel.Futex.Syscalls — the futex (98) checker and witness, and their proofs

Mirrors `theories/LinuxProcessSem/Checks/Sys/Kernel/Futex/Syscalls.v` (the
executable checker, its two arms, and their soundness and completeness
proofs) and `theories/LinuxProcessSem/Checks/Witness/Kernel/Futex/Syscalls.v`
(the receptiveness witness and its proof), in that order, as two sections
of one module.  Both answer to Linux `kernel/futex/syscalls.c`: this file
holds the checker and the witness for the syscall defined there, and no
other.  The ticket that ports both, C-Kernel-Futex-Syscalls, names this one
file, so the witness lives here rather than under a `Checks/Witness/`
mirror path.  Not part of the trusted specification: the spec is
`Sys/Kernel/Futex/Syscalls.lean`'s, and every theorem here relates the
checker, or the witness, to it.

The Rocq checker file is split out of `Checks/ExecutableSpecs.v`, which
keeps the dispatcher and the four top-level theorems and re-exports it;
the Rocq witness file is split out of `Checks/Progress.v` the same way.

WHAT IS NOT HERE, AND WHOSE IT IS.  The arm the checker becomes — the
`CheckedArm` built from its four lemmas and the witness's `_ok`, the row
that carries 98 in the checked table, the `arm_unfold` lemmas that open
it, and the alternative the VM-ledger invariant's alternation takes for
it — is the conformance ticket's registration step, not this file's
(BRIEF.md section 5, CHECK; the ticket is V-Kernel-Futex-Syscalls).  That split is what lets this file build on
the two preludes and the spec alone, and a `lean: checks:` PR carries none
of those hunks.  Rocq's `futex_copyins_exact`, the ledger theorem its
OCaml tester consumes, is stated in this Rocq file but is already twinned
in `Checks/Cases/Kernel/Futex/Syscalls.lean` (the S ticket put it beside
the predicate it is about); it is not restated here.

The header's baseline is a71fd38a, the squash that landed the 2026-09-11
work on main; the two futex Rocq files are byte-identical there to the
port's common baseline f44244ad, from which the brief quotes them (that
commit is not an ancestor of any branch since the day's work was
rebase-merged, and the parity tool refuses a baseline that is not one),
and to 8589c1245, the `nightly/09-14-2026` tip this twin was written
against on 2026-09-19.  Both were last touched by the commit that modeled
the syscall (#612).  The frame lemma below is transcribed from
`Checks/VmMapsDisjoint.v`, which DOES differ between f44244ad and
a71fd38a — in other syscalls' frames; the futex lemma's text is the same
in both, and only its line number moved.

WHAT THE CHECKER DECIDES.  `check_futex` is `futex_spec`'s branch
structure, branch for branch, with each relational `ret_only r` replaced
by `check_ret_only eff r m []` — the executable test that the recorded
effect is exactly a return of `r` with no writes, no zero-fills, no
model change and an empty ledger — the one `record_copyins reads (err_ret
EAGAIN)` replaced by `check_ret_only_copyins reads eff (errno_ret EAGAIN)
m []`, which decides the same with the ledger CLEARED and then requires
the ledger to be exactly `reads`, and the spec's `unmodeled` replaced by
`CheckUnmodeled`.  Nothing is decided here that the spec does not decide,
and the lemmas below say so in both directions: what the checker accepts
the spec admits (`*_sound_ok`), what the checker declines the spec
declines (`*_sound_unmodeled`), and conversely (`*_complete_ok`,
`*_complete_unmodeled`).  Read `Sys/Kernel/Futex/Syscalls.lean` for the
six corrections it makes to the Rocq comments' citations; they are not
repeated here.  The kernel order the branches are in IS, next, because
it is what the proofs below split on.

THE ORDER, read at Linux v6.18.46 (commit 1f99e9ab748f).  The op word is
tested WHOLE, all 64 bits, against the two private words; a wake never
looks at `val`, `utime` or the memory, because `futex_wake`
(kernel/futex/waitwake.c:155-200, v6.18.46) reaches its `return ret` with
`ret` the 0 `get_futex_key` left at :165-167 and no waiter to count — the
private key is built at kernel/futex/core.c:624-630 (v6.18.46) before any
page is resolved, and no task shares this mm to have queued one.  A wait
is declined FIRST on a non-NULL `utime`, because `SYSCALL_DEFINE6(futex)`
(kernel/futex/syscalls.c:188-208, v6.18.46) fetches the timeout under `if
(utime && futex_cmd_has_timeout(cmd))` (:196) before `do_futex` is even
called, so its -EFAULT and -EINVAL, and the timer it arms, come ahead of
the key check; then the two `get_futex_key` gates in the kernel's order —
`if (unlikely((address % size) != 0)) return -EINVAL;`
(kernel/futex/core.c:569-570, v6.18.46), then `if (unlikely(!access_ok(uaddr,
size))) return -EFAULT;` (:573-574) — which `futex_wait_setup`
(kernel/futex/waitwake.c:591-664, v6.18.46) runs at :617-619 before it reads
the word through `futex_get_value_locked` (a `static inline` in
kernel/futex/futex.h:332-341, v6.18.46) at :627; and last the value test,
`if (uval != val) { … return -EWOULDBLOCK; }` (:642-645), where
`EWOULDBLOCK` is `EAGAIN` (include/uapi/asm-generic/errno.h:22, v6.18.46).
A word the model cannot read, and a word that matches, both decline: the
kernel would fault or sleep, and neither is an answer this model gives.
The checker answers `CheckUnmodeled` on those two branches before it
looks at the effect at all, which is what makes the ledger theorem in the
Cases file hold on every `Ok` outcome.

THE GATE IS WRITTEN OUT, not shared.  The spec tests alignment through
`futex_aligned_b`; this checker, like Rocq's, spells the test out as
`Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0` — `Int.fmod` is the
exact transcription of Rocq's `Z.modulo` (floor modulo; the divisor is
4, so the two agree with every other reading too), the spelling the spec's
header settles on for the same reason.  Rocq's checker explains the
restatement: the proofs below split on the two gate booleans one at a
time, after unfolding `futex_aligned_b` on the spec side, so that they do
not depend on the two files spelling the assembled condition the same way
— which is the coincidence a shared predicate would have them rely on.
`Bool.not_true`/`Bool.not_false` are what the `!` on each gate needs, and
`Bool.false_eq_true` is what an `if false = true` needs; both are listed
per branch rather than in one `<;>`, so that no simp argument is ever
unused.

WHAT ELSE IS HERE.  The frame lemma, Rocq's `VmMapsDisjoint.check_futex_frame`:
the checker never moves `m_vmmaps`.  Rocq states it in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, beside the alternation
that consumes it, and the C ticket's acceptance text assigns it to the
registration step; this file states it anyway, because it depends on
nothing but the checker and two prelude lemmas, and a lemma provable where
its subject is defined should not wait on a file that cannot import it.
The table the arm's row goes into exists — `Checks/Sys/Table.lean`'s
`checked_table` — and this file is not among its imports; the alternation
that consumes the frame lemmas is the VM-ledger invariant's, wherever the
tree keeps it, and V-Kernel-Futex-Syscalls's registration (BRIEF.md
section 5) is to import this file from both.  The arm-level fact the
alternation consumes is DERIVED from it at registration, not re-proved.
It is the section before the witness.

THE WITNESS spells each answering outcome as `ret_outcome r m`, the
shorthand of `Checks/Witness/Prelude.lean` (ticket K5, in the tree since
#986), the way Rocq does; it unfolds to `Ok (mkEffect r [] []) m []`.
Importing both preludes puts two `srw` macros in scope, which
`Checks/Witness/Prelude.lean`'s header says are kept identical by hand;
this file uses neither. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Futex.Syscalls

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Futex.Syscalls
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## The two arms -/

/-- `FUTEX_WAKE_PRIVATE`: -EINVAL on a misaligned address, -EFAULT on one
past the user range, and otherwise the count 0, each as a bare return.
Mirrors `Kernel.Futex.Syscalls.futex_wake_private_spec` branch for branch;
`i` is not an argument, because the wake arm reads no memory.  Rocq:
`Checks.Sys.Kernel.Futex.Syscalls.check_futex_wake_private`. -/
def check_futex_wake_private (uaddr : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if !(Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0) then
    check_ret_only eff (errno_ret EINVAL) m []
  else if !(access_okb uaddr FUTEX_WORD_SIZE) then
    check_ret_only eff (errno_ret EFAULT) m []
  else check_ret_only eff (Z_to_bv 64 0) m []

/-- `FUTEX_WAIT_PRIVATE` with a NULL timeout: the two gates as for a wake,
then the four-byte read of the word at `uaddr` from the input's memory —
`CheckUnmodeled` when the model cannot read it, `CheckUnmodeled` when it
matches `val` (the kernel would queue and sleep), and -EAGAIN carrying
exactly that one read on the ledger when it does not.  `val` arrives
already narrowed to its low 32 bits by `check_futex`, as the kernel's `u32
val` is.  Mirrors `Kernel.Futex.Syscalls.futex_wait_private_spec`.  Rocq:
`Checks.Sys.Kernel.Futex.Syscalls.check_futex_wait_private`. -/
def check_futex_wait_private (i : SyscallInput) (uaddr val : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if !(Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0) then
    check_ret_only eff (errno_ret EINVAL) m []
  else if !(access_okb uaddr FUTEX_WORD_SIZE) then
    check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map i.in_mem uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) with
    | none => CheckUnmodeled
    | some uval =>
      if bv_eqb (le_bytes_to_word uval) val then CheckUnmodeled
      else check_ret_only_copyins [(uaddr, FUTEX_WORD_SIZE_nat)] eff (errno_ret EAGAIN) m []

/-- `futex` (98): the op word whole against the two private words, a wake
to `check_futex_wake_private`, a wait with a NULL `utime` to
`check_futex_wait_private` on the low 32 bits of `val`, and everything
else — a non-NULL timeout on a wait, and every other op word —
`CheckUnmodeled`.  Mirrors `Kernel.Futex.Syscalls.futex_spec`.  Rocq:
`Checks.Sys.Kernel.Futex.Syscalls.check_futex`. -/
def check_futex (i : SyscallInput) (uaddr op val utime : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE) then check_futex_wake_private uaddr eff m
  else if bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE) then
    (if !(w_is0 utime) then CheckUnmodeled
     else check_futex_wait_private i uaddr (abi_low32 val) eff m)
  else CheckUnmodeled

/-! ## The gate branches, once

Every gate branch of every lemma below is one of three facts about a
`ret_only` against a `check_ret_only`, which Rocq closes inline with
`check_ret_only_ok_iff`, `inv_ok` and `discriminate` after its `futex_gate`
tactic.  Lean has no `try`-over-all-goals idiom that the 0-warnings bar
tolerates (an unused simp argument in one branch of a `<;>` is a lint), so
the three facts are stated once and each branch names the one it needs.
`err_ret e` is `ret_only (errno_ret e)` by unfolding, so the three apply
to it as they stand. -/

/-- A `check_ret_only` acceptance is a `ret_only` admission: the effect is
the bare return, the model came back unchanged, no event. -/
theorem ret_only_of_check_ret_only (eff : SyscallEffect) (r : word) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : check_ret_only eff r m [] = CheckOk m' evs) :
    ret_only r i m (Ok eff m' evs) := by
  rw [check_ret_only_ok_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact pure_ok _ i _

/-- …and conversely. -/
theorem check_ret_only_of_ret_only (eff : SyscallEffect) (r : word) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : ret_only r i m (Ok eff m' evs)) :
    check_ret_only eff r m [] = CheckOk m' evs := by
  rw [ret_only, pure_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- A `ret_only` never declines. -/
theorem ret_only_not_unmodeled (r : word) (i : SyscallInput) (m : Model)
    (h : ret_only r i m Unmodeled) : False := by
  rw [ret_only, pure_iff] at h
  cases h

/-! ## The wake arm -/

/-- Rocq: `Checks.Sys.Kernel.Futex.Syscalls.check_futex_wake_private_sound_ok`. -/
theorem check_futex_wake_private_sound_ok (uaddr : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_futex_wake_private uaddr eff m = CheckOk m' evs) :
    futex_wake_private_spec uaddr i m (Ok eff m' evs) := by
  unfold check_futex_wake_private at h
  unfold futex_wake_private_spec futex_key_check futex_aligned_b
  cases ha : (Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0)
  · simp only [ha, Bool.not_false, ↓reduceIte] at h ⊢
    exact ret_only_of_check_ret_only _ _ _ _ _ i h
  · simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hok : access_okb uaddr FUTEX_WORD_SIZE
    · simp only [hok, Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_of_check_ret_only _ _ _ _ _ i h
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ret_only_of_check_ret_only _ _ _ _ _ i h

/-- Rocq: `Checks.Sys.Kernel.Futex.Syscalls.check_futex_wake_private_sound_unmodeled`. -/
theorem check_futex_wake_private_sound_unmodeled (uaddr : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_futex_wake_private uaddr eff m = CheckUnmodeled) :
    futex_wake_private_spec uaddr i m Unmodeled := by
  unfold check_futex_wake_private at h
  cases ha : (Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0)
  · simp only [ha, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  · simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hok : access_okb uaddr FUTEX_WORD_SIZE
    · simp only [hok, Bool.not_false, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `Checks.Sys.Kernel.Futex.Syscalls.check_futex_wake_private_complete_ok`. -/
theorem check_futex_wake_private_complete_ok (uaddr : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : futex_wake_private_spec uaddr i m (Ok eff m' evs)) :
    check_futex_wake_private uaddr eff m = CheckOk m' evs := by
  unfold futex_wake_private_spec futex_key_check futex_aligned_b at h
  unfold check_futex_wake_private
  cases ha : (Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0)
  · simp only [ha, Bool.not_false, ↓reduceIte] at h ⊢
    exact check_ret_only_of_ret_only _ _ _ _ _ i h
  · simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hok : access_okb uaddr FUTEX_WORD_SIZE
    · simp only [hok, Bool.not_false, ↓reduceIte] at h ⊢
      exact check_ret_only_of_ret_only _ _ _ _ _ i h
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact check_ret_only_of_ret_only _ _ _ _ _ i h

/-- Rocq: `Checks.Sys.Kernel.Futex.Syscalls.check_futex_wake_private_complete_unmodeled`. -/
theorem check_futex_wake_private_complete_unmodeled (uaddr : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : futex_wake_private_spec uaddr i m Unmodeled) :
    check_futex_wake_private uaddr eff m = CheckUnmodeled := by
  unfold futex_wake_private_spec futex_key_check futex_aligned_b at h
  cases ha : (Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0)
  · simp only [ha, Bool.not_false, ↓reduceIte] at h
    exact (ret_only_not_unmodeled _ i m h).elim
  · simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hok : access_okb uaddr FUTEX_WORD_SIZE
    · simp only [hok, Bool.not_false, ↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim

/-! ## The wait arm

Past the two gates the spec is `bind input` over a `match` on the read,
with `record_copyins` around the value test.  The `*_ok` proofs step
through `input` with `bind_ok0` (soundness) or `input_bind_ok_inv`
(completeness) and open the ledger wrapper with `record_copyins_ok_empty`
or `record_copyins_ok_inv`; the `*_unmodeled` ones use `bind_unmodeled2`,
`input_bind_unmodeled_inv`, `record_copyins_unmodeled` and
`record_copyins_unmodeled_inv`.  The read is `generalize`d to an opaque
`r` before the `cases`, on both sides at once, so that the same
`Option` is split in the hypothesis and the goal. -/

/-- Rocq: `Checks.Sys.Kernel.Futex.Syscalls.check_futex_wait_private_sound_ok`. -/
theorem check_futex_wait_private_sound_ok (i : SyscallInput) (uaddr val : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_futex_wait_private i uaddr val eff m = CheckOk m' evs) :
    futex_wait_private_spec uaddr val i m (Ok eff m' evs) := by
  unfold check_futex_wait_private at h
  unfold futex_wait_private_spec futex_key_check futex_aligned_b
  cases ha : (Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0)
  · simp only [ha, Bool.not_false, ↓reduceIte] at h ⊢
    exact ret_only_of_check_ret_only _ _ _ _ _ i h
  · simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hok : access_okb uaddr FUTEX_WORD_SIZE
    · simp only [hok, Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_of_check_ret_only _ _ _ _ _ i h
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      refine bind_ok0 _ _ i m i m _ _ _ (input_ok i m) ?_
      generalize read_bytes_map i.in_mem uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) = r at h ⊢
      cases r with
      | none =>
        dsimp only at h
        cases h
      | some uval =>
        dsimp only at h ⊢
        cases hv : bv_eqb (le_bytes_to_word uval) val
        · simp only [hv, Bool.false_eq_true, ↓reduceIte] at h ⊢
          rw [check_ret_only_copyins_ok_iff] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact record_copyins_ok_empty _ _ i _ (mkEffect (errno_ret EAGAIN) [] []) _ _ rfl
            (pure_ok _ i _)
        · simp only [hv, ↓reduceIte] at h
          cases h

/-- Rocq: `Checks.Sys.Kernel.Futex.Syscalls.check_futex_wait_private_sound_unmodeled`. -/
theorem check_futex_wait_private_sound_unmodeled (i : SyscallInput) (uaddr val : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_futex_wait_private i uaddr val eff m = CheckUnmodeled) :
    futex_wait_private_spec uaddr val i m Unmodeled := by
  unfold check_futex_wait_private at h
  unfold futex_wait_private_spec futex_key_check futex_aligned_b
  cases ha : (Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0)
  · simp only [ha, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  · simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hok : access_okb uaddr FUTEX_WORD_SIZE
    · simp only [hok, Bool.not_false, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      refine bind_unmodeled2 _ _ i m i m [] (input_ok i m) ?_
      generalize read_bytes_map i.in_mem uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) = r at h ⊢
      cases r with
      | none =>
        dsimp only
        exact unmodeled_intro i m
      | some uval =>
        dsimp only at h ⊢
        cases hv : bv_eqb (le_bytes_to_word uval) val
        · simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
          exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
        · simp only [↓reduceIte]
          exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)

/-- Rocq: `Checks.Sys.Kernel.Futex.Syscalls.check_futex_wait_private_complete_ok`. -/
theorem check_futex_wait_private_complete_ok (i : SyscallInput) (uaddr val : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : futex_wait_private_spec uaddr val i m (Ok eff m' evs)) :
    check_futex_wait_private i uaddr val eff m = CheckOk m' evs := by
  unfold futex_wait_private_spec futex_key_check futex_aligned_b at h
  unfold check_futex_wait_private
  cases ha : (Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0)
  · simp only [ha, Bool.not_false, ↓reduceIte] at h ⊢
    exact check_ret_only_of_ret_only _ _ _ _ _ i h
  · simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hok : access_okb uaddr FUTEX_WORD_SIZE
    · simp only [hok, Bool.not_false, ↓reduceIte] at h ⊢
      exact check_ret_only_of_ret_only _ _ _ _ _ i h
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      have h := input_bind_ok_inv _ i m _ _ _ h
      generalize read_bytes_map i.in_mem uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) = r at h ⊢
      cases r with
      | none =>
        dsimp only at h
        exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
      | some uval =>
        dsimp only at h ⊢
        obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ _ _ h
        cases hv : bv_eqb (le_bytes_to_word uval) val
        · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hcore ⊢
          rw [err_ret, ret_only, pure_iff] at hcore
          obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj hcore
          exact check_ret_only_copyins_refl _ _ _ _
        · simp only [hv, ↓reduceIte] at hcore
          exact absurd ((unmodeled_iff i m _).mp hcore)
            (by simp only [reduceCtorEq, not_false_eq_true])

/-- Rocq: `Checks.Sys.Kernel.Futex.Syscalls.check_futex_wait_private_complete_unmodeled`. -/
theorem check_futex_wait_private_complete_unmodeled (i : SyscallInput) (uaddr val : word)
    (m : Model) (eff : SyscallEffect) (h : futex_wait_private_spec uaddr val i m Unmodeled) :
    check_futex_wait_private i uaddr val eff m = CheckUnmodeled := by
  unfold futex_wait_private_spec futex_key_check futex_aligned_b at h
  unfold check_futex_wait_private
  cases ha : (Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0)
  · simp only [ha, Bool.not_false, ↓reduceIte] at h
    exact (ret_only_not_unmodeled _ i m h).elim
  · simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hok : access_okb uaddr FUTEX_WORD_SIZE
    · simp only [hok, Bool.not_false, ↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      have h := input_bind_unmodeled_inv _ i m h
      generalize read_bytes_map i.in_mem uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) = r at h ⊢
      cases r with
      | none => rfl
      | some uval =>
        dsimp only at h ⊢
        have h := record_copyins_unmodeled_inv _ _ i m h
        cases hv : bv_eqb (le_bytes_to_word uval) val
        · simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
          exact (ret_only_not_unmodeled _ i m h).elim
        · simp only [↓reduceIte]

/-! ## The dispatcher arm

The op word is tested WHOLE, so the three arms are disjoint by
construction and each of the four lemmas is one case split over the two
equalities and the timeout test, followed by the matching arm's lemma. -/

/-- Rocq: `Checks.Sys.Kernel.Futex.Syscalls.check_futex_sound_ok`. -/
theorem check_futex_sound_ok (i : SyscallInput) (uaddr op val utime : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_futex i uaddr op val utime eff m = CheckOk m' evs) :
    futex_spec uaddr op val utime i m (Ok eff m' evs) := by
  unfold check_futex at h
  unfold futex_spec
  cases hwake : bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE)
  · simp only [hwake, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hwait : bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)
    · simp only [hwait, Bool.false_eq_true, ↓reduceIte] at h
      cases h
    · simp only [hwait, ↓reduceIte] at h ⊢
      cases hu : w_is0 utime
      · simp only [hu, Bool.not_false, ↓reduceIte] at h
        cases h
      · simp only [hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_futex_wait_private_sound_ok i uaddr (abi_low32 val) eff m m' evs h
  · simp only [hwake, ↓reduceIte] at h ⊢
    exact check_futex_wake_private_sound_ok uaddr eff m m' evs i h

/-- Rocq: `Checks.Sys.Kernel.Futex.Syscalls.check_futex_sound_unmodeled`. -/
theorem check_futex_sound_unmodeled (i : SyscallInput) (uaddr op val utime : word)
    (eff : SyscallEffect) (m : Model) (h : check_futex i uaddr op val utime eff m = CheckUnmodeled) :
    futex_spec uaddr op val utime i m Unmodeled := by
  unfold check_futex at h
  unfold futex_spec
  cases hwake : bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE)
  · simp only [hwake, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hwait : bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
    · simp only [hwait, ↓reduceIte] at h ⊢
      cases hu : w_is0 utime
      · simp only [Bool.not_false, ↓reduceIte]
        exact unmodeled_intro i m
      · simp only [hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_futex_wait_private_sound_unmodeled i uaddr (abi_low32 val) eff m h
  · simp only [hwake, ↓reduceIte] at h ⊢
    exact check_futex_wake_private_sound_unmodeled uaddr eff m i h

/-- Rocq: `Checks.Sys.Kernel.Futex.Syscalls.check_futex_complete_ok`. -/
theorem check_futex_complete_ok (i : SyscallInput) (uaddr op val utime : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : futex_spec uaddr op val utime i m (Ok eff m' evs)) :
    check_futex i uaddr op val utime eff m = CheckOk m' evs := by
  unfold futex_spec at h
  unfold check_futex
  cases hwake : bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE)
  · simp only [hwake, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hwait : bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)
    · simp only [hwait, Bool.false_eq_true, ↓reduceIte] at h
      exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
    · simp only [hwait, ↓reduceIte] at h ⊢
      cases hu : w_is0 utime
      · simp only [hu, Bool.not_false, ↓reduceIte] at h
        exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
      · simp only [hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_futex_wait_private_complete_ok i uaddr (abi_low32 val) eff m m' evs h
  · simp only [hwake, ↓reduceIte] at h ⊢
    exact check_futex_wake_private_complete_ok uaddr eff m m' evs i h

/-- Rocq: `Checks.Sys.Kernel.Futex.Syscalls.check_futex_complete_unmodeled`. -/
theorem check_futex_complete_unmodeled (i : SyscallInput) (uaddr op val utime : word) (m : Model)
    (eff : SyscallEffect) (h : futex_spec uaddr op val utime i m Unmodeled) :
    check_futex i uaddr op val utime eff m = CheckUnmodeled := by
  unfold futex_spec at h
  unfold check_futex
  cases hwake : bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE)
  · simp only [hwake, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hwait : bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [hwait, ↓reduceIte] at h ⊢
      cases hu : w_is0 utime
      · simp only [Bool.not_false, ↓reduceIte]
      · simp only [hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_futex_wait_private_complete_unmodeled i uaddr (abi_low32 val) m eff h
  · simp only [hwake, ↓reduceIte] at h ⊢
    exact check_futex_wake_private_complete_unmodeled uaddr m i eff h

/-! ## The frame lemma

Rocq keeps every arm's frame lemma inside
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, next to the alternation
that uses it; the header says why this one is here instead, and what the
registration step derives from it.

The argument is the trivial one: the checker never builds a model.  Every
accepting branch is a `check_ret_only eff r m []` or a
`check_ret_only_copyins reads eff r m []`, which accept only with the
model they were given (the middle conjunct of `check_ret_only_ok_iff` and
of `check_ret_only_copyins_ok_iff`), so `m_vmmaps m'` is `m_vmmaps m` by
substitution.  The `CheckUnmodeled` branches never reach a `CheckOk` and
are closed by the constructor mismatch.  The split follows the checker's
own order — op word, timeout, alignment, range, read, value — so that
each branch's hypothesis is the acceptor it ends in.  As Rocq's comment
says, the wait arm's copy-in ledger is a claim about what was READ; the
pages it charges are accounted by `Run.sstep_syscall` over the effect,
outside this theorem. -/

/-- The model a `check_ret_only` accepts with is the one it was given. -/
theorem check_ret_only_model (eff : SyscallEffect) (r : word) (m m' : Model)
    (evs evs1 : List event) (h : check_ret_only eff r m evs1 = CheckOk m' evs) : m' = m :=
  ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1

/-- …and so is the one a `check_ret_only_copyins` accepts with. -/
theorem check_ret_only_copyins_model (reads : List (word × Nat)) (eff : SyscallEffect) (r : word)
    (m m' : Model) (evs evs1 : List event)
    (h : check_ret_only_copyins reads eff r m evs1 = CheckOk m' evs) : m' = m :=
  ((check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h).2.1

/-- Rocq: `VmMapsDisjoint.check_futex_frame`. -/
theorem check_futex_frame (i : SyscallInput) (uaddr op val utime : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_futex i uaddr op val utime eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_futex check_futex_wake_private check_futex_wait_private at h
  cases hwake : bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE)
  · simp only [hwake, Bool.false_eq_true, ↓reduceIte] at h
    cases hwait : bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)
    · simp only [hwait, Bool.false_eq_true, ↓reduceIte] at h
      cases h
    · simp only [hwait, ↓reduceIte] at h
      cases hu : w_is0 utime
      · simp only [hu, Bool.not_false, ↓reduceIte] at h
        cases h
      · simp only [hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases ha : (Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0)
        · simp only [ha, Bool.not_false, ↓reduceIte] at h
          rw [check_ret_only_model _ _ _ _ _ _ h]
        · simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hok : access_okb uaddr FUTEX_WORD_SIZE
          · simp only [hok, Bool.not_false, ↓reduceIte] at h
            rw [check_ret_only_model _ _ _ _ _ _ h]
          · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            generalize read_bytes_map i.in_mem uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) = r at h
            cases r with
            | none =>
              dsimp only at h
              cases h
            | some uval =>
              dsimp only at h
              cases hv : bv_eqb (le_bytes_to_word uval) (abi_low32 val)
              · simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
                rw [check_ret_only_copyins_model _ _ _ _ _ _ _ h]
              · simp only [hv, ↓reduceIte] at h
                cases h
  · simp only [hwake, ↓reduceIte] at h
    cases ha : (Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0)
    · simp only [ha, Bool.not_false, ↓reduceIte] at h
      rw [check_ret_only_model _ _ _ _ _ _ h]
    · simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hok : access_okb uaddr FUTEX_WORD_SIZE
      · simp only [hok, Bool.not_false, ↓reduceIte] at h
        rw [check_ret_only_model _ _ _ _ _ _ h]
      · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        rw [check_ret_only_model _ _ _ _ _ _ h]

/-! ## The witness — `Checks/Witness/Kernel/Futex/Syscalls.v`

Mirrors `theories/LinuxProcessSem/Checks/Witness/Kernel/Futex/Syscalls.v`.
A witness exhibits one admissible outcome for a spec in the matching
`Sys` module, which is what progress is proved from: the receptiveness
field of the arm the registration step builds is the `futex_witness_ok`
lemma below, applied to the registers the arm reads.

Every arm of this spec is a single answer rather than a choice — a
`ret_only`, a `record_copyins` around an `err_ret`, or an `unmodeled` —
so the witness is the spec read back, and the `futex_witness_ok` proof is
the spec's own case split; there is no environment nondeterminism here
for it to pick a member of.  `Unmodeled` IS an admissible outcome, so the
declined halves need no invented answer: a witness of `Unmodeled` is a
witness, and exhibiting the spec's own `unmodeled` arm is what makes this
total.  The gate is written out for the third time, as it is in Rocq;
the header says why the three layers restate it rather than share one
predicate. -/

/-- Rocq: `Checks.Witness.Kernel.Futex.Syscalls.futex_witness`. -/
def futex_witness (uaddr op val utime : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE) then
    (if !(Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0) then ret_outcome (errno_ret EINVAL) m
     else if !(access_okb uaddr FUTEX_WORD_SIZE) then ret_outcome (errno_ret EFAULT) m
     else ret_outcome (Z_to_bv 64 0) m)
  else if bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE) then
    (if !(w_is0 utime) then Unmodeled
     else if !(Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0) then
       ret_outcome (errno_ret EINVAL) m
     else if !(access_okb uaddr FUTEX_WORD_SIZE) then ret_outcome (errno_ret EFAULT) m
     else
       match read_bytes_map i.in_mem uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) with
       | none => Unmodeled
       | some uval =>
         if bv_eqb (le_bytes_to_word uval) (abi_low32 val) then Unmodeled
         else Ok (with_copyins [(uaddr, FUTEX_WORD_SIZE_nat)] (mkEffect (errno_ret EAGAIN) [] [])) m [])
  else Unmodeled

/-- Rocq: `Checks.Witness.Kernel.Futex.Syscalls.futex_witness_ok`. -/
theorem futex_witness_ok (uaddr op val utime : word) (i : SyscallInput) (m : Model) :
    futex_spec uaddr op val utime i m (futex_witness uaddr op val utime i m) := by
  unfold futex_spec futex_witness futex_wake_private_spec futex_wait_private_spec futex_key_check
    futex_aligned_b
  cases hwake : bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hwait : bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
    · simp only [↓reduceIte]
      cases hu : w_is0 utime
      · simp only [Bool.not_false, ↓reduceIte]
        exact unmodeled_intro i m
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases ha : (Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0)
        · simp only [Bool.not_false, ↓reduceIte]
          exact pure_ok _ i _
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases hok : access_okb uaddr FUTEX_WORD_SIZE
          · simp only [Bool.not_false, ↓reduceIte]
            exact pure_ok _ i _
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            refine bind_step _ _ i m i m _ (input_ok i m) ?_
            generalize read_bytes_map i.in_mem uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) = r
            cases r with
            | none =>
              dsimp only
              exact unmodeled_intro i m
            | some uval =>
              dsimp only
              cases hv : bv_eqb (le_bytes_to_word uval) (abi_low32 val)
              · simp only [Bool.false_eq_true, ↓reduceIte]
                exact record_copyins_ok_empty _ _ i _ (mkEffect (errno_ret EAGAIN) [] []) _ _ rfl
                  (pure_ok _ i _)
              · simp only [↓reduceIte]
                exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
  · simp only [↓reduceIte]
    cases ha : (Int.fmod (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0)
    · simp only [Bool.not_false, ↓reduceIte]
      exact pure_ok _ i _
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hok : access_okb uaddr FUTEX_WORD_SIZE
      · simp only [Bool.not_false, ↓reduceIte]
        exact pure_ok _ i _
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact pure_ok _ i _

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Futex.Syscalls
