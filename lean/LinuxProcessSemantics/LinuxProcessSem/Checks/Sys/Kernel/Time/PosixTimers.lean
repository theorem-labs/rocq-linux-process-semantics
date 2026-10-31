import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.PosixTimers
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Kernel.Time.PosixTimers — the clock_gettime (113) checker and its witness

Mirrors `theories/LinuxProcessSem/Checks/Sys/Kernel/Time/PosixTimers.v`
(the executable checker and its four soundness and completeness proofs)
and `theories/LinuxProcessSem/Checks/Witness/Kernel/Time/PosixTimers.v`
(the receptiveness witness and its proof), in that order, as two sections
of one module.  The ticket that ports both, C-Kernel-Time-PosixTimers,
names this one file, so the witness lives here rather than under a
`Checks/Witness/` mirror path.  Moving it there is more than a rename:
`clock_gettime_witness_ok` rewrites with `bind_get_model_ite_iff` from
the checker section, which Rocq's witness file does not import, so a
`Checks/Witness/` module would either import this one or wait for the
base move below.  That move is the condition under which this paragraph
goes stale.
Both Rocq files are byte-identical at a71fd38a and at the port's common
baseline f44244ad; the header names the one the `Sys/` twins on the day
branch name.

Not part of the trusted specification.  The trusted definition is
`Sys/Kernel/Time/PosixTimers.lean`'s `clock_gettime_spec`; the proofs here
relate the executable `check_clock_gettime` and the witness to it, and
they are what let the checker's answer stand in for the relation.  The
pins on the checker are `Checks/Cases/Checks/Sys/Kernel/Time/PosixTimers.lean`.

The checker mirrors Rocq's three arms decision for decision.  Its gates on
the clock id and on the recorded clock are spelled as the `Sys` twin
spells the spec's — Lean's decidable `=`, `≠` and `<` on `Int` where Rocq
has `Z.eqb`, `negb (Z.eqb …)` and `negb (Z.ltb …)` — so that one
`by_cases` on a gate splits the checker and the spec together; the
`bv_eqb … && … && *_ok_b …` guard on the effect stays a `Bool`, as in
Rocq.  The destination `match`es are parenthesized for the reason the
`Sys` twin's header gives.

Four lemmas here belong to base files (BRIEF.md section 4), not to the
mirrored files, and wait here until a `lean: base:` PR moves them; that
move is the condition under which each leaves this file.  One has a Rocq
twin in `BvBase.v` that the Lean `BvBase.lean` does not have:
`bytes_le_to_Z_of_le_bytes`, which the witness proof needs, and which
`Sys/Uapi/Fs.lean`'s `stat_set_size_size_ok` note also waits on and
cannot reach here.  It is proved through `bytes_le_to_nat_of_le_bytes`, a
`Nat`-level lemma with no Rocq twin — Rocq's `bytes_le_to_Z` is a
`Fixpoint` on `Z` and its proof is bit-level — which goes to
`BvBase.lean` with it.  Two more have no Rocq twin, because Rocq reaches
the same facts by evaluation at the use site: `bind_get_model_ite_iff`, a `Monad.lean`-shaped companion of
`bind_get_model_iff` that keeps a decision on the read model where a
keyed rewrite can reach it, and `m_vmmaps_with_clock`, a `State/` fact
about `with_clock`.

The frame lemma `check_clock_gettime_frame` is Rocq's
`VmMapsDisjoint.check_clock_gettime_frame`.  It is stated here rather than
in the `VmMapsDisjoint` twin because the dispatcher's table imports this
module and that twin imports the table; the arm-level fact that consumes
it registers there, in the K4 ticket's file, once that ticket lands. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.PosixTimers

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.PosixTimers
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude

/-! ## The checker — `Checks/Sys/Kernel/Time/PosixTimers.v` -/

/-- Rocq: `PosixTimers.check_clock_gettime`.  Three arms that differ in
three places and nowhere else — the clock id they answer, the byte
predicate they apply, and the model they hand back — each a decision of
Linux v6.18.46 (commit 1f99e9ab748f):

- THE ID GATE.  `SYSCALL_DEFINE2(clock_gettime)`
  (kernel/time/posix-timers.c:1136-1152, v6.18.46) consults
  `clockid_to_kclock` (kernel/time/posix-timers.c:1535-1548, v6.18.46)
  before it does anything else, and that table has an entry for every
  id the spec models.  For any other id the checker answers
  `CheckUnmodeled`, as the spec does — the kernel's `-EINVAL` for an
  unknown id and its dynamic and per-thread clocks are outside the
  model, so nothing about them is ever proved.
- THE DESTINATION GATE.  `put_timespec64` (kernel/time/time.c:903-912,
  v6.18.46) is one `copy_to_user` of the 16-byte `struct __kernel_timespec`
  (include/uapi/linux/time_types.h:7-10, v6.18.46), `-EFAULT` when it
  fails.  The checker declines rather than models that errno, as Rocq
  does: the spec's `read_bytes_map` on `in_wmem` is a 16-byte
  writability probe with no partial answer to give.
- THE EFFECT.  Exactly one write, at `tp`, with return 0 and no zeros,
  unmaps, copies or copy-ins — `SYSCALL_DEFINE2(clock_gettime)` writes
  nothing else — and the bytes written must pass the arm's predicate:
  `realtime_ok_b`, `cputime_ok_b` or `timespec_ok_b`, all from the `Sys`
  twin, which carries the kernel line behind each conjunct.
- THE MODEL.  Only the `CLOCK_MONOTONIC` arm reads `m_clock m` and
  answers `CheckOk (with_clock …)`: `posix_get_monotonic_timespec`
  (kernel/time/posix-timers.c:217-222, v6.18.46) reads a clock that
  never steps back, so the reading is recorded for the next one to be
  measured against.  `posix_get_realtime_timespec`
  (kernel/time/posix-timers.c:194-198, v6.18.46) reads a settable clock
  and `process_cpu_clock_get` (kernel/time/posix-cpu-timers.c:1675-1679,
  v6.18.46) a per-process one; neither arm records anything, and both
  answer the model they were given.

The recorded-clock gate on the monotonic arm declines a model whose
clock already sits at or past `CLOCK_NS_ENVELOPE`, before the destination
is probed, in the order the spec has them. -/
def check_clock_gettime (i : SyscallInput) (clkid tp : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if bv_unsigned clkid = CLOCK_REALTIME then
    (match read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with
     | none => CheckUnmodeled
     | some _ =>
       match eff with
       | SyscallEffect.mkEffectU r [(a, bs)] [] [] [] [] =>
         if bv_eqb r (Z_to_bv 64 0) && bv_eqb a tp && realtime_ok_b bs
         then CheckOk m [] else CheckReject
       | _ => CheckReject)
  else if bv_unsigned clkid = CLOCK_PROCESS_CPUTIME_ID then
    (match read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with
     | none => CheckUnmodeled
     | some _ =>
       match eff with
       | SyscallEffect.mkEffectU r [(a, bs)] [] [] [] [] =>
         if bv_eqb r (Z_to_bv 64 0) && bv_eqb a tp && cputime_ok_b bs
         then CheckOk m [] else CheckReject
       | _ => CheckReject)
  else if bv_unsigned clkid ≠ CLOCK_MONOTONIC then CheckUnmodeled
  else if ¬ (bv_unsigned (m_clock m) < CLOCK_NS_ENVELOPE) then CheckUnmodeled
  else
    (match read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with
     | none => CheckUnmodeled
     | some _ =>
       match eff with
       | SyscallEffect.mkEffectU r [(a, bs)] [] [] [] [] =>
         if bv_eqb r (Z_to_bv 64 0) && bv_eqb a tp && timespec_ok_b bs (m_clock m)
         then CheckOk (with_clock (Z_to_bv 64 (timespec_ns bs)) m) [] else CheckReject
       | _ => CheckReject)

/-! ### Crossing the recorded-clock gate

`bv_unsigned (m_clock m) < CLOCK_NS_ENVELOPE` is decided by `Int.decLt`,
and reducing that instance against a symbolic clock sends `Int.sub` into
`Nat.sub`'s structural recursion on the literal `2 ^ 63`.  Whatever
reduces the gate's `if` to a branch by evaluation exceeds the recursion
limit: `split` or `simp` on an `if` that has become the head of a goal,
any term elaborated against such a goal (the elaborator reduces a goal
to look for a binder), and the kernel comparing
`with_clock (Z_to_bv 64 …) m` with `m` field by field.  The gates on the
clock id are harmless — their instances stop on the symbolic id at once
— and so is `simp` rewriting the gate's condition from a hypothesis,
which never evaluates the instance.  So the proofs below decide the
envelope gate by `by_cases` while the goal is still a `bind`, cross it
by `rw` alone — the first lemma of this section with
`ite_eq_left_of_eq_true` / `ite_eq_right_of_eq_false` — and read the
address space off `with_clock` through the second lemma rather than by
`rfl` at the use site.  This stops being necessary when the `Sys` twin
decides the gate by a `Bool` the way Rocq's `Z.ltb` does. -/

/-- `get_model` followed by a decision on the model it read, resolved at
once: the continuation's `if` is the outcome's `if`.  `Monad.lean`'s
`bind_get_model_iff` leaves the decision applied to the read model, where
only evaluation can reach it; this form keeps the `if` where a keyed
rewrite can.  The instance is a plain argument so the rewrite unifies it
from the term instead of synthesizing it. -/
theorem bind_get_model_ite_iff {B : Type} (c : Model → Prop)
    {inst : (m : Model) → Decidable (c m)} (A E : Model → Sys B)
    (i : SyscallInput) (m : Model) (o : outcome B) :
    bind get_model (fun m => @ite _ (c m) (inst m) (A m) (E m)) i m o
      ↔ @ite _ (c m) (inst m) (A m i m o) (E m i m o) := by
  rw [bind_get_model_iff]
  by_cases hc : c m
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true hc)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false hc)]

/-- `with_clock` rewrites the time component and nothing else, the address
space included.  Rocq's frame proof reads this off by `reflexivity` at the
use site; here the `rfl` is taken once, on an abstract clock, for the
reason the section header gives. -/
theorem m_vmmaps_with_clock (t : word) (m : Model) : m_vmmaps (with_clock t m) = m_vmmaps m := rfl

/-- Rocq: `PosixTimers.check_clock_gettime_sound_ok`.  A `CheckOk` is an
outcome the spec admits.  The proof walks the checker's gates with the
spec's, arm by arm: `by_cases` on a gate rewrites both sides, the
destination probe is generalized, the effect is taken apart by `split`,
and the surviving guard hands `choose_ok` its predicate. -/
theorem check_clock_gettime_sound_ok (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_clock_gettime i clkid tp eff m = CheckOk m' evs) :
    clock_gettime_spec clkid tp i m (Ok eff m' evs) := by
  unfold check_clock_gettime at h
  unfold clock_gettime_spec
  by_cases hrt : bv_unsigned clkid = CLOCK_REALTIME
  · simp only [hrt, ↓reduceIte] at h ⊢
    refine bind_ok0 _ _ _ _ _ _ _ _ _ (input_ok i m) ?_
    rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
    · simp only [hdst, reduceCtorEq] at h
    · simp only [hdst] at h ⊢
      split at h
      next r a bs =>
        split at h
        next hok =>
          injection h with hm hevs
          subst hm hevs
          simp only [Bool.and_eq_true, bv_eqb_eq] at hok
          obtain ⟨⟨rfl, rfl⟩, hts⟩ := hok
          exact bind_ok0 _ _ _ _ _ _ _ _ _ (choose_ok _ bs i _ hts) (pure_ok _ i _)
        next => cases h
      next => cases h
  · simp only [hrt, ↓reduceIte] at h ⊢
    by_cases hcp : bv_unsigned clkid = CLOCK_PROCESS_CPUTIME_ID
    · simp only [hcp, ↓reduceIte] at h ⊢
      refine bind_ok0 _ _ _ _ _ _ _ _ _ (input_ok i m) ?_
      rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
      · simp only [hdst, reduceCtorEq] at h
      · simp only [hdst] at h ⊢
        split at h
        next r a bs =>
          split at h
          next hok =>
            injection h with hm hevs
            subst hm hevs
            simp only [Bool.and_eq_true, bv_eqb_eq] at hok
            obtain ⟨⟨rfl, rfl⟩, hts⟩ := hok
            exact bind_ok0 _ _ _ _ _ _ _ _ _ (choose_ok _ bs i _ hts) (pure_ok _ i _)
          next => cases h
        next => cases h
    · simp only [hcp, ↓reduceIte] at h ⊢
      by_cases hid : bv_unsigned clkid = CLOCK_MONOTONIC
      · simp only [hid, ne_eq, not_true_eq_false, ↓reduceIte] at h ⊢
        by_cases henv : bv_unsigned (m_clock m) < CLOCK_NS_ENVELOPE
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro henv))] at h
          rw [bind_get_model_ite_iff,
            ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro henv))]
          refine bind_ok0 _ _ _ _ _ _ _ _ _ (input_ok i m) ?_
          rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
          · simp only [hdst, reduceCtorEq] at h
          · simp only [hdst] at h ⊢
            split at h
            next r a bs =>
              split at h
              next hok =>
                injection h with hm hevs
                subst hm hevs
                simp only [Bool.and_eq_true, bv_eqb_eq] at hok
                obtain ⟨⟨rfl, rfl⟩, hts⟩ := hok
                exact bind_ok0 _ _ _ _ _ _ _ _ _ (choose_ok _ bs i _ hts)
                  (bind_ok0 _ _ _ _ _ _ _ _ _ (modify_ok _ i _) (pure_ok _ i _))
              next => cases h
            next => cases h
        · rw [ite_eq_left_of_eq_true _ _ (eq_true henv)] at h
          cases h
      · simp only [hid, ne_eq, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `PosixTimers.check_clock_gettime_sound_unmodeled`: every
`CheckUnmodeled` the checker answers is a decline the spec makes. -/
theorem check_clock_gettime_sound_unmodeled (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_clock_gettime i clkid tp eff m = CheckUnmodeled) :
    clock_gettime_spec clkid tp i m Unmodeled := by
  unfold check_clock_gettime at h
  unfold clock_gettime_spec
  by_cases hrt : bv_unsigned clkid = CLOCK_REALTIME
  · simp only [hrt, ↓reduceIte] at h ⊢
    refine bind_unmodeled2 _ _ _ _ _ _ _ (input_ok i m) ?_
    rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
    · exact unmodeled_intro i m
    · exfalso
      simp only [hdst] at h
      split at h
      next => split at h <;> cases h
      next => cases h
  · simp only [hrt, ↓reduceIte] at h ⊢
    by_cases hcp : bv_unsigned clkid = CLOCK_PROCESS_CPUTIME_ID
    · simp only [hcp, ↓reduceIte] at h ⊢
      refine bind_unmodeled2 _ _ _ _ _ _ _ (input_ok i m) ?_
      rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
      · exact unmodeled_intro i m
      · exfalso
        simp only [hdst] at h
        split at h
        next => split at h <;> cases h
        next => cases h
    · simp only [hcp, ↓reduceIte] at h ⊢
      by_cases hid : bv_unsigned clkid = CLOCK_MONOTONIC
      · simp only [hid, ne_eq, not_true_eq_false, ↓reduceIte] at h ⊢
        by_cases henv : bv_unsigned (m_clock m) < CLOCK_NS_ENVELOPE
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro henv))] at h
          rw [bind_get_model_ite_iff,
            ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro henv))]
          refine bind_unmodeled2 _ _ _ _ _ _ _ (input_ok i m) ?_
          rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
          · exact unmodeled_intro i m
          · exfalso
            simp only [hdst] at h
            split at h
            next => split at h <;> cases h
            next => cases h
        · rw [bind_get_model_ite_iff, ite_eq_left_of_eq_true _ _ (eq_true henv)]
          exact unmodeled_intro i m
      · simp only [hid, ne_eq, not_false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m

/-- Rocq: `PosixTimers.check_clock_gettime_complete_ok`.  Every outcome the
spec admits is a `CheckOk` of the checker, with the same model and events:
the spec's binds are inverted one at a time, the chosen bytes and the
`pure` outcome are read off, and the checker's guard is discharged by the
two reflexive `bv_eqb`s and the chosen predicate. -/
theorem check_clock_gettime_complete_ok (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : clock_gettime_spec clkid tp i m (Ok eff m' evs)) :
    check_clock_gettime i clkid tp eff m = CheckOk m' evs := by
  unfold clock_gettime_spec at h
  unfold check_clock_gettime
  by_cases hrt : bv_unsigned clkid = CLOCK_REALTIME
  · simp only [hrt, ↓reduceIte] at h ⊢
    have h1 := input_bind_ok_inv _ i m eff m' evs h
    rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
    · simp only [hdst, Monad.unmodeled, reduceCtorEq] at h1
    · simp only [hdst, bind_choose_iff, pure_iff] at h1
      obtain ⟨bs, hts, hp⟩ := h1
      simp only [mkEffect, outcome.Ok.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      have hok : (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0) && bv_eqb tp tp && realtime_ok_b bs)
          = true := by
        rw [bv_eqb_refl, bv_eqb_refl, hts]
        rfl
      simp only [hok, ↓reduceIte]
  · simp only [hrt, ↓reduceIte] at h ⊢
    by_cases hcp : bv_unsigned clkid = CLOCK_PROCESS_CPUTIME_ID
    · simp only [hcp, ↓reduceIte] at h ⊢
      have h1 := input_bind_ok_inv _ i m eff m' evs h
      rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
      · simp only [hdst, Monad.unmodeled, reduceCtorEq] at h1
      · simp only [hdst, bind_choose_iff, pure_iff] at h1
        obtain ⟨bs, hts, hp⟩ := h1
        simp only [mkEffect, outcome.Ok.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        have hok : (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0) && bv_eqb tp tp && cputime_ok_b bs)
            = true := by
          rw [bv_eqb_refl, bv_eqb_refl, hts]
          rfl
        simp only [hok, ↓reduceIte]
    · simp only [hcp, ↓reduceIte] at h ⊢
      by_cases hid : bv_unsigned clkid = CLOCK_MONOTONIC
      · simp only [hid, ne_eq, not_true_eq_false, ↓reduceIte] at h ⊢
        by_cases henv : bv_unsigned (m_clock m) < CLOCK_NS_ENVELOPE
        · rw [bind_get_model_ite_iff,
            ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro henv))] at h
          rw [ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro henv))]
          have h2 := input_bind_ok_inv _ i m eff m' evs h
          rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
          · simp only [hdst, Monad.unmodeled, reduceCtorEq] at h2
          · simp only [hdst, bind_choose_iff, Monad.set_clock, bind_modify_iff, pure_iff] at h2
            obtain ⟨bs, hts, hp⟩ := h2
            simp only [mkEffect, outcome.Ok.injEq] at hp
            obtain ⟨rfl, rfl, rfl⟩ := hp
            have hok : (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0) && bv_eqb tp tp
                && timespec_ok_b bs (m_clock m)) = true := by
              rw [bv_eqb_refl, bv_eqb_refl, hts]
              rfl
            simp only [hok, ↓reduceIte]
        · rw [bind_get_model_ite_iff, ite_eq_left_of_eq_true _ _ (eq_true henv)] at h
          simp only [Monad.unmodeled, reduceCtorEq] at h
      · simp only [hid, ne_eq, not_false_eq_true, ↓reduceIte, Monad.unmodeled, reduceCtorEq] at h

/-- Rocq: `PosixTimers.check_clock_gettime_complete_unmodeled`.  Every
decline of the spec is a `CheckUnmodeled` of the checker, whatever effect
the checker is shown: the spec's `unmodeled` sites are exactly the
checker's, and none of them looks at `eff`. -/
theorem check_clock_gettime_complete_unmodeled (i : SyscallInput) (clkid tp : word)
    (m : Model) (eff : SyscallEffect)
    (h : clock_gettime_spec clkid tp i m Unmodeled) :
    check_clock_gettime i clkid tp eff m = CheckUnmodeled := by
  unfold clock_gettime_spec at h
  unfold check_clock_gettime
  by_cases hrt : bv_unsigned clkid = CLOCK_REALTIME
  · simp only [hrt, ↓reduceIte] at h ⊢
    have h1 := input_bind_unmodeled_inv _ i m h
    rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
    · rfl
    · simp only [hdst, bind_choose_iff, pure_iff] at h1
      obtain ⟨_, _, hp⟩ := h1
      cases hp
  · simp only [hrt, ↓reduceIte] at h ⊢
    by_cases hcp : bv_unsigned clkid = CLOCK_PROCESS_CPUTIME_ID
    · simp only [hcp, ↓reduceIte] at h ⊢
      have h1 := input_bind_unmodeled_inv _ i m h
      rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
      · rfl
      · simp only [hdst, bind_choose_iff, pure_iff] at h1
        obtain ⟨_, _, hp⟩ := h1
        cases hp
    · simp only [hcp, ↓reduceIte] at h ⊢
      by_cases hid : bv_unsigned clkid = CLOCK_MONOTONIC
      · simp only [hid, ne_eq, not_true_eq_false, ↓reduceIte] at h ⊢
        by_cases henv : bv_unsigned (m_clock m) < CLOCK_NS_ENVELOPE
        · rw [bind_get_model_ite_iff,
            ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro henv))] at h
          rw [ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro henv))]
          have h2 := input_bind_unmodeled_inv _ i m h
          rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
          · rfl
          · simp only [hdst, bind_choose_iff, Monad.set_clock, bind_modify_iff, pure_iff] at h2
            obtain ⟨_, _, hp⟩ := h2
            cases hp
        · rw [ite_eq_left_of_eq_true _ _ (eq_true henv)]
      · simp only [hid, ne_eq, not_false_eq_true, ↓reduceIte]

/-- Rocq: `VmMapsDisjoint.check_clock_gettime_frame`.  A `CheckOk` leaves
the address space alone: the only model the checker ever builds is
`with_clock … m`, which rewrites the time component and nothing else.
Rocq's `vm_frame2` splits every gate and closes each `CheckOk` by
`reflexivity`; here the gates are split the way the soundness proofs
split them and the monotonic `CheckOk` is closed by `m_vmmaps_with_clock`,
for the reason the section header gives. -/
theorem check_clock_gettime_frame (i : SyscallInput) (clkid tp : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_clock_gettime i clkid tp eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_clock_gettime at h
  by_cases hrt : bv_unsigned clkid = CLOCK_REALTIME
  · simp only [hrt, ↓reduceIte] at h
    rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
    · simp only [hdst, reduceCtorEq] at h
    · simp only [hdst] at h
      split at h
      next =>
        split at h
        next =>
          cases h
          rfl
        next => cases h
      next => cases h
  · simp only [hrt, ↓reduceIte] at h
    by_cases hcp : bv_unsigned clkid = CLOCK_PROCESS_CPUTIME_ID
    · simp only [hcp, ↓reduceIte] at h
      rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
      · simp only [hdst, reduceCtorEq] at h
      · simp only [hdst] at h
        split at h
        next =>
          split at h
          next =>
            cases h
            rfl
          next => cases h
        next => cases h
    · simp only [hcp, ↓reduceIte] at h
      by_cases hid : bv_unsigned clkid = CLOCK_MONOTONIC
      · simp only [hid, ne_eq, not_true_eq_false, ↓reduceIte] at h
        by_cases henv : bv_unsigned (m_clock m) < CLOCK_NS_ENVELOPE
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro henv))] at h
          rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
          · simp only [hdst, reduceCtorEq] at h
          · simp only [hdst] at h
            split at h
            next =>
              split at h
              next =>
                cases h
                exact m_vmmaps_with_clock _ _
              next => cases h
            next => cases h
        · rw [ite_eq_left_of_eq_true _ _ (eq_true henv)] at h
          cases h
      · simp only [hid, ne_eq, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-! ## The witness — `Checks/Witness/Kernel/Time/PosixTimers.v` -/

/-- `Z_to_le_bytes` keeps exactly the low `8 * k` bits of a natural: the
`Nat` half of `bytes_le_to_Z_of_le_bytes` below (Rocq's
`BvBase.bytes_le_to_Z_of_le_bytes`), with no Rocq twin of its own.  Byte `j` of the
list is bits `8j` to `8j+7`, which is what `bytes_le_to_nat`'s
`||| … <<< 8` reassembles; the step case is `Nat.mod_mul` read
right-to-left, with `Nat.two_pow_add_eq_or_of_lt` turning the low byte's
`+` into `|||`. -/
theorem bytes_le_to_nat_of_le_bytes (k n : Nat) :
    bytes_le_to_nat (Z_to_le_bytes k (n : Int)) = n % 2 ^ (8 * k) := by
  induction k generalizing n with
  | zero => exact (Nat.mod_one n).symm
  | succ k ih =>
    have hbyte : (Z_to_bv 8 (n : Int)).toNat = n % 2 ^ 8 := by
      rw [Z_to_bv, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
    have hlt : n % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt n (Nat.two_pow_pos 8)
    simp only [Z_to_le_bytes, bytes_le_to_nat]
    rw [← Int.natCast_shiftRight, ih, hbyte, Nat.shiftLeft_eq,
      Nat.mul_comm ((n >>> 8) % 2 ^ (8 * k)) (2 ^ 8),
      Nat.or_comm (n % 2 ^ 8) (2 ^ 8 * ((n >>> 8) % 2 ^ (8 * k))),
      ← Nat.two_pow_add_eq_or_of_lt hlt ((n >>> 8) % 2 ^ (8 * k)),
      Nat.shiftRight_eq_div_pow, Nat.mul_add_one, Nat.pow_add,
      Nat.mul_comm (2 ^ (8 * k)) (2 ^ 8), Nat.mod_mul]
    exact Nat.add_comm _ _

/-- Rocq: `BvBase.bytes_le_to_Z_of_le_bytes`, stated here for the reason
the header gives.  A non-negative integer written out as `k` little-endian
bytes and read back is the integer modulo `2 ^ (8 k)`. -/
theorem bytes_le_to_Z_of_le_bytes (k : Nat) (z : Int) (hz : 0 ≤ z) :
    bytes_le_to_Z (Z_to_le_bytes k z) = z % 2 ^ (8 * k) := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, z = (n : Int) := ⟨z.toNat, (Int.toNat_of_nonneg hz).symm⟩
  unfold bytes_le_to_Z
  rw [bytes_le_to_nat_of_le_bytes, Int.natCast_emod, Int.natCast_pow]
  rfl

/-- Rocq: `PosixTimers.clock_gettime_bytes`.  The 16 bytes `put_timespec64`
(kernel/time/time.c:903-912, v6.18.46) copies out for a reading of `t`
nanoseconds: `tv_sec = t / 10^9` then `tv_nsec = t mod 10^9`, each as 8
little-endian bytes — the split `ns_to_timespec64`
(kernel/time/time.c:523-542, v6.18.46) makes of a non-negative count, and
the normal form `timespec64_add_ns` (include/linux/time64.h:163-167,
v6.18.46) leaves the timekeeping readers' result in.  Meaningful for
`0 ≤ t`: Lean's `/` and `%` on `Int` are Euclidean and agree with Rocq's
`Z.div` and `Z.modulo` for this positive divisor whatever the sign of
`t`, but `Z_to_le_bytes 8` of a negative quotient wraps to two's
complement and `bytes_le_to_Z` reads it back unsigned
(`bytes_le_to_Z_of_le_bytes` asks `0 ≤ z`).  The witness applies it to
the recorded clock, a `word`, and to 0. -/
def clock_gettime_bytes (t : Int) : List byte :=
  Z_to_le_bytes 8 (t / 1000000000) ++ Z_to_le_bytes 8 (t % 1000000000)

/-- Rocq: `PosixTimers.clock_gettime_bytes_ns`.  For a reading inside the
envelope, `clock_gettime_bytes` round-trips: the timespec it encodes is
`t`, its fraction is `t mod 10^9`, and it is 16 bytes long.  Both halves
fit in 8 bytes because `t < CLOCK_NS_ENVELOPE = 2^63 < 2^64`. -/
theorem clock_gettime_bytes_ns (t : Int) (ht : 0 ≤ t ∧ t < CLOCK_NS_ENVELOPE) :
    timespec_ns (clock_gettime_bytes t) = t
    ∧ tv_frac_of (clock_gettime_bytes t) = t % 1000000000
    ∧ (clock_gettime_bytes t).length = 16 := by
  obtain ⟨h0, h1⟩ := ht
  have henv : CLOCK_NS_ENVELOPE = 9223372036854775808 := by decide
  have h64 : (2 : Int) ^ (8 * 8) = 18446744073709551616 := by decide
  rw [henv] at h1
  have hsec : bytes_le_to_Z (Z_to_le_bytes 8 (t / 1000000000)) = t / 1000000000 := by
    rw [bytes_le_to_Z_of_le_bytes 8 _ (by omega), h64]
    omega
  have hfrac : bytes_le_to_Z (Z_to_le_bytes 8 (t % 1000000000)) = t % 1000000000 := by
    rw [bytes_le_to_Z_of_le_bytes 8 _ (by omega), h64]
    omega
  have hlen : (Z_to_le_bytes 8 (t / 1000000000)).length = 8 := length_Z_to_le_bytes 8 _
  refine ⟨?_, ?_, ?_⟩
  · unfold timespec_ns tv_sec_of tv_frac_of clock_gettime_bytes
    rw [List.take_left' hlen, List.drop_left' hlen, hsec, hfrac]
    omega
  · unfold tv_frac_of clock_gettime_bytes
    rw [List.drop_left' hlen, hfrac]
  · unfold clock_gettime_bytes
    rw [List.length_append, hlen, length_Z_to_le_bytes]

/-- Rocq: `PosixTimers.clock_gettime_witness`.  For each modeled arm, one
outcome the spec admits.  The realtime and cputime arms answer a reading
of 0 — `realtime_ok_b` and `cputime_ok_b` accept it, since neither arm
measures against the recorded clock — and the monotonic arm answers the
recorded clock itself, encoded by `clock_gettime_bytes`, which
`timespec_ok_b` admits as the equal reading (`ktime_get_ts64`,
kernel/time/timekeeping.c:955, v6.18.46, may hand out the same nanosecond
twice; the `Sys` twin carries that argument).  The witness reads the
clock WITHOUT ADVANCING it: the model it hands back re-records the same
value.  Where the spec declines the witness is `Unmodeled`, so
`clock_gettime_witness_ok` is the receptiveness obligation of the
dispatcher arm. -/
def clock_gettime_witness (clkid tp : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  if bv_unsigned clkid = CLOCK_REALTIME then
    (match read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with
     | none => Unmodeled
     | some _ => Ok (mkEffect (Z_to_bv 64 0) [(tp, clock_gettime_bytes 0)] []) m [])
  else if bv_unsigned clkid = CLOCK_PROCESS_CPUTIME_ID then
    (match read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with
     | none => Unmodeled
     | some _ => Ok (mkEffect (Z_to_bv 64 0) [(tp, clock_gettime_bytes 0)] []) m [])
  else if bv_unsigned clkid ≠ CLOCK_MONOTONIC then Unmodeled
  else if ¬ (bv_unsigned (m_clock m) < CLOCK_NS_ENVELOPE) then Unmodeled
  else
    (match read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with
     | none => Unmodeled
     | some _ =>
       let bs := clock_gettime_bytes (bv_unsigned (m_clock m))
       Ok (mkEffect (Z_to_bv 64 0) [(tp, bs)] []) (with_clock (Z_to_bv 64 (timespec_ns bs)) m) [])

/-- Rocq: `PosixTimers.clock_gettime_witness_ok`.  The witness is an outcome
of the spec on every input and model.  The 0 reading is admitted by
evaluation; the monotonic reading by `clock_gettime_bytes_ns`, with
`word_unsigned_range` supplying the lower bound the round-trip needs.
Every gate is decided before the two definitions are unfolded, because
the witness's envelope gate is the outcome itself once they are (the
section header on the checker says why that matters). -/
theorem clock_gettime_witness_ok (i : SyscallInput) (clkid tp : word) (m : Model) :
    clock_gettime_spec clkid tp i m (clock_gettime_witness clkid tp i m) := by
  by_cases hrt : bv_unsigned clkid = CLOCK_REALTIME
  · unfold clock_gettime_spec clock_gettime_witness
    simp only [hrt, ↓reduceIte]
    rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
    · refine bind_unmodeled2 _ _ _ _ _ _ _ (input_ok i m) ?_
      simp only [hdst]
      exact unmodeled_intro i m
    · refine bind_ok0 _ _ _ _ _ _ _ _ _ (input_ok i m) ?_
      simp only [hdst]
      exact bind_ok0 _ _ _ _ _ _ _ _ _ (choose_ok _ (clock_gettime_bytes 0) i m (by decide))
        (pure_ok _ i m)
  · by_cases hcp : bv_unsigned clkid = CLOCK_PROCESS_CPUTIME_ID
    · unfold clock_gettime_spec clock_gettime_witness
      simp only [hrt, ↓reduceIte]
      simp only [hcp, ↓reduceIte]
      rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
      · refine bind_unmodeled2 _ _ _ _ _ _ _ (input_ok i m) ?_
        simp only [hdst]
        exact unmodeled_intro i m
      · refine bind_ok0 _ _ _ _ _ _ _ _ _ (input_ok i m) ?_
        simp only [hdst]
        exact bind_ok0 _ _ _ _ _ _ _ _ _ (choose_ok _ (clock_gettime_bytes 0) i m (by decide))
          (pure_ok _ i m)
    · by_cases hid : bv_unsigned clkid = CLOCK_MONOTONIC
      · by_cases henv : bv_unsigned (m_clock m) < CLOCK_NS_ENVELOPE
        · unfold clock_gettime_spec clock_gettime_witness
          simp only [hrt, ↓reduceIte]
          simp only [hcp, ↓reduceIte]
          simp only [hid, ne_eq, not_true_eq_false, ↓reduceIte]
          simp only [henv, not_true_eq_false, ↓reduceIte]
          rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
          · rw [bind_get_model_ite_iff,
              ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro henv))]
            refine bind_unmodeled2 _ _ _ _ _ _ _ (input_ok i m) ?_
            simp only [hdst]
            exact unmodeled_intro i m
          · obtain ⟨hns, hfrac, hlen⟩ := clock_gettime_bytes_ns (bv_unsigned (m_clock m))
              ⟨(word_unsigned_range (m_clock m)).1, henv⟩
            have hts : timespec_ok_b (clock_gettime_bytes (bv_unsigned (m_clock m))) (m_clock m)
                = true := by
              unfold timespec_ok_b
              rw [hlen, hns, hfrac]
              have e1 : (16 == 16) = true := rfl
              have e2 : decide (bv_unsigned (m_clock m) % 1000000000 < 1000000000) = true :=
                decide_eq_true (by omega)
              have e3 : decide (bv_unsigned (m_clock m) ≤ bv_unsigned (m_clock m)) = true :=
                decide_eq_true (Int.le_refl _)
              have e4 : decide (bv_unsigned (m_clock m) < CLOCK_NS_ENVELOPE) = true :=
                decide_eq_true henv
              rw [e1, e2, e3, e4]
              rfl
            rw [bind_get_model_ite_iff,
              ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro henv))]
            refine bind_ok0 _ _ _ _ _ _ _ _ _ (input_ok i m) ?_
            simp only [hdst]
            exact bind_ok0 _ _ _ _ _ _ _ _ _
              (choose_ok _ (clock_gettime_bytes (bv_unsigned (m_clock m))) i m hts)
              (bind_ok0 _ _ _ _ _ _ _ _ _ (modify_ok _ i m) (pure_ok _ i _))
        · unfold clock_gettime_spec clock_gettime_witness
          simp only [hrt, ↓reduceIte]
          simp only [hcp, ↓reduceIte]
          simp only [hid, ne_eq, not_true_eq_false, ↓reduceIte]
          simp only [henv, not_false_eq_true, ↓reduceIte]
          rw [bind_get_model_ite_iff, ite_eq_left_of_eq_true _ _ (eq_true henv)]
          exact unmodeled_intro i m
      · unfold clock_gettime_spec clock_gettime_witness
        simp only [hrt, ↓reduceIte]
        simp only [hcp, ↓reduceIte]
        simp only [hid, ne_eq, not_false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.PosixTimers
