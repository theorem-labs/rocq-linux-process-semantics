-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Kernel/Time/Hrtimer.v

import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude


/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Kernel.Time.Hrtimer — the nanosleep (101) checker, its proofs, and its witness

Twin of `theories/LinuxProcessSem/Checks/Sys/Kernel/Time/Hrtimer.v` and of
`theories/LinuxProcessSem/Checks/Witness/Kernel/Time/Hrtimer.v`, read at
the baseline above.  Both mirror `Sys/Kernel/Time/Hrtimer.v`, which
answers to Linux `kernel/time/hrtimer.c`: this file holds the checker
and the witness for the syscall defined there, and no other.  The
witness lives here rather than at its own mirror path because
`Checks/Witness/Prelude.lean` and `Checks/Sys/Prelude.lean` are both
imported anyway and a second module would carry only the one
definition and its proof; nothing else the tree reads depends on the
split.  Not part of the trusted specification: the trusted definitions
are `Sys/Kernel/Time/Hrtimer.lean`'s, and every theorem here relates an
executable to them.

Every kernel line named below was read at Linux v6.18.46 (commit
1f99e9ab748fc5c32120de9c4eca31abfe54a4d5), which is linux-process-semantics@ff0313ba4f:AGENTS.md's
citation baseline.

WHAT IS NOT HERE, AND WHOSE IT IS.  Rocq registers this checker in
`Checks/Sys/Dispatch.v`'s `checked_table` and proves its frame lemma in
`Checks/VmMapsDisjoint.v`; the Lean tree does neither here.  Since PR
#904 a checker ticket ships the checker, its theorems and its
witness, and the V ticket's registration step adds the `checked_table`
row, the `arm_unfold` lemmas, the `CheckedArm` and the frame lemma in
one change, against the shared files this ticket may not touch.  So the
theorems below stand alone against `Checks/Sys/Prelude.lean`,
`Checks/Witness/Prelude.lean` and the `Sys` twin, and are what that step
will wire in.  The pins on this checker are in
`Checks/Cases/Checks/Sys/Kernel/Time/Hrtimer.lean`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.Hrtimer

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## The checker — `Checks/Sys/Kernel/Time/Hrtimer.v`

An unreadable request declines; an invalid one is -EINVAL; and otherwise
BOTH outcomes are admissible, so the acceptor decides which arm it is
being shown from the return value.  The order is the kernel's:
`SYSCALL_DEFINE2(nanosleep)` (kernel/time/hrtimer.c:2189-2205, Linux v6.18.46) calls
`get_timespec64` (kernel/time/time.c:872-892, Linux v6.18.46) before anything else, and
its `copy_from_user` failing is the -EFAULT this model declines rather
than answers; then `timespec64_valid` (include/linux/time64.h:97-106, Linux v6.18.46)
refuses a negative `tv_sec` or a `tv_nsec` outside `[0, 10^9)` with
-EINVAL (kernel/time/hrtimer.c:2197-2198, Linux v6.18.46); only then is the
timer armed.

THE REQUEST'S SECONDS FIELD GATES NOTHING.  A `tv_sec` at or above
`KTIME_SEC_MAX` used to decline here, and `nanosleep_spec`'s header says
why it must not: the remainder the same spec may write reaches that
band, and the standard retry loop feeds the remainder back as the next
request.  The saturation `ktime_set` (include/linux/ktime.h:36-42, Linux v6.18.46)
performs lives in `Uapi.timespec_ktime` and is read by `nanosleep_clock`,
not by a guard.

- 0 with no writes is the completed sleep, and carries the whole request
  into `m_clock`, saturated at `KTIME_MAX`.
- -EINTR is the interruption (`hrtimer_nanosleep`, kernel/time/hrtimer.c:2159-2185,
  Linux v6.18.46: `-ERESTART_RESTARTBLOCK` where the restart block is set
  up, which `arch_do_signal_or_restart` (arch/riscv/kernel/signal.c:396-463,
  Linux v6.18.46) turns into -EINTR when a handler runs).  With a NULL `rmtp` it carries no write and
  moves nothing, the slept duration being unknowable; with a non-NULL one
  it MUST carry exactly one write at `rmtp` that `nanosleep_rem_ok_b`
  admits, and carries the part of the request that provably elapsed into
  `m_clock`.

That last "must" is the sharp claim: with a remainder destination, an
-EINTR and no write is REJECTED, because `do_nanosleep`
(kernel/time/hrtimer.c:2112-2145, Linux v6.18.46) returns 0 rather than the interruption when
`hrtimer_expires_remaining` is not positive (:2135-2139), and only a
positive remainder reaches `nanosleep_copyout` (:2093-2110).

AND EVERY ACCEPTED OUTCOME MUST CARRY THE COPY-IN.  The request reaches
the kernel through `get_timespec64`, so an effect that claims one of
these outcomes without the 16-byte read at `rqtp` in its ledger
describes a kernel that decided the call without looking at the request,
and is rejected.  The requirement sits on the accepting arms only: every
`CheckUnmodeled` verdict is reached before any effect is inspected and
must stay reachable whatever ledger that effect carries, or
`check_nanosleep_complete_unmodeled` would be false.

THERE IS NO GATE ON THE MODEL'S CLOCK EITHER.  A sleep whose deadline
would leave `ktime_t` is one Linux serves at a saturated deadline
(`ktime_add_safe`, kernel/time/hrtimer.c:340-352, Linux v6.18.46, called
from `__hrtimer_start_range_ns`, kernel/time/hrtimer.c:1242-1243, Linux
v6.18.46, when the relative request is made absolute, and again with the slack inside
`hrtimer_set_expires_range_ns`, which :1247 calls to record it) rather
than refusing, so `nanosleep_clock` clamps and this
acceptor reads `m` only to compute the new clock.  That is why the two
declines that remain, an unreadable request and an unwritable `rmtp`
(`put_timespec64`, kernel/time/time.c:903-912, Linux v6.18.46, is where the kernel would
fail with -EFAULT instead), are decided without it, and why they are the
only ones.

The effect is taken apart by a `match` on `SyscallEffect.mkEffectU`, as
Rocq's is, and the `Bool` gates are `bv_eqb` and the spec's own
predicates, so on a concrete effect the whole verdict is a closed
computation. -/

/-- Rocq: `Hrtimer.check_nanosleep`. -/
def check_nanosleep (i : SyscallInput) (rqtp rmtp : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match read_bytes_map i.in_mem rqtp (Z_to_bv 64 16) with
  | none => CheckUnmodeled
  | some req =>
    if !(timespec_valid_b req) then
      check_ret_only_copyins [(rqtp, 16)] eff (errno_ret EINVAL) m []
    else if w_is0 rmtp then
      check_copyins [(rqtp, 16)] eff
        (match eff with
         | SyscallEffect.mkEffectU r [] [] [] [] _ =>
           if bv_eqb r (Z_to_bv 64 0) then
             CheckOk (with_clock (nanosleep_clock (m_clock m) req []) m) []
           else if bv_eqb r (errno_ret EINTR) then CheckOk m []
           else CheckReject
         | _ => CheckReject)
    else
      match read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) with
      | none => CheckUnmodeled
      | some _ =>
        check_copyins [(rqtp, 16)] eff
          (match eff with
           | SyscallEffect.mkEffectU r [] [] [] [] _ =>
             if bv_eqb r (Z_to_bv 64 0) then
               CheckOk (with_clock (nanosleep_clock (m_clock m) req []) m) []
             else CheckReject
           | SyscallEffect.mkEffectU r [(a, rem)] [] [] [] _ =>
             if bv_eqb r (errno_ret EINTR) && bv_eqb a rmtp && nanosleep_rem_ok_b rem then
               CheckOk (with_clock (nanosleep_clock (m_clock m) req rem) m) []
             else CheckReject
           | _ => CheckReject)

/-- Rocq: `Hrtimer.check_nanosleep_ok_copyins`.  What the acceptor demands
of the ledger, read back out of an acceptance.  Soundness needs it before
it can peel `record_copyins`, because the ledger has to be known before
the effect can be split into the part the body produces and the part the
wrapper prepends. -/
theorem check_nanosleep_ok_copyins (i : SyscallInput) (rqtp rmtp : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_nanosleep i rqtp rmtp eff m = CheckOk m' evs) :
    eff.eff_copyins = [(rqtp, 16)] := by
  unfold check_nanosleep at h
  rcases hrq : read_bytes_map i.in_mem rqtp (Z_to_bv 64 16) with _ | req
  · simp only [hrq, reduceCtorEq] at h
  · simp only [hrq] at h
    cases hv : timespec_valid_b req with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at h
      obtain ⟨rfl, -, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
      rfl
    | true =>
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hrm : w_is0 rmtp with
      | true =>
        simp only [hrm, ↓reduceIte, check_copyins] at h
        cases hc : access_ranges_eqb eff.eff_copyins [(rqtp, 16)] with
        | true => exact (access_ranges_eqb_eq _ _).mp hc
        | false => simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | false =>
        simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h
        rcases hrm2 : read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) with _ | w
        · simp only [hrm2, reduceCtorEq] at h
        · simp only [hrm2, check_copyins] at h
          cases hc : access_ranges_eqb eff.eff_copyins [(rqtp, 16)] with
          | true => exact (access_ranges_eqb_eq _ _).mp hc
          | false => simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-! ### Peeling the ledger

Rocq's `nanosleep_ledger_ok` peels `record_copyins` off the spec on the
accepting side once the effect has been split into its fields and its
ledger substituted.  `Checks/Sys/Prelude.lean`'s `record_copyins_clear_ok`
is the same step stated on the effect as a whole — the ledger equation
`check_nanosleep_ok_copyins` supplies, and the body against
`clear_copyins eff` — so the soundness proof uses it and no local twin is
kept: what is left after the peel is then a `match` on the still-whole
`eff`, which `split` takes apart by substitution, where Rocq's `destruct`
chain had to name every field first.

### Splitting the request's validity before naming anything

Every proof below cases on `timespec_valid_b req` BEFORE it binds a
hypothesis whose type is a spec application, and the completeness proofs
rewrite `h` in place with the monad's `_iff` lemmas rather than naming
each inversion.  The reason is a linter, not the logic.
`Lean.Linter.constructorNameAsVariable` runs `whnf` on the type of every
named binder, and a type of the form
`(if !(timespec_valid_b req) = true then … else …) i m o` is one that
`whnf` does not bring to a head within `maxRecDepth`: the failure is
reported at the theorem's position, names no tactic, and goes away the
moment the gate is a constant.  Which reduction runs away is not pinned
here; what is pinned is that the same gate, on a closed request, is
where `rfl` runs away on every concrete case in
`Checks/Cases/Checks/Sys/Kernel/Time/Hrtimer.lean`, whose header records
the mechanism and its cure.  Once `hv` has replaced the
guard by a constant the same types are shallow, and a hypothesis
`simp only … at h` rewrites carries no binder for the linter to visit. -/

/-- Rocq: `Hrtimer.check_nanosleep_sound_ok`.  A `CheckOk` is an outcome
the spec admits.  The ledger is read off the acceptance first, the
`record_copyins` wrapper is peeled with it, and the four accepting arms
are then matched to the spec's alternatives: the completed sleep to
`alt_l` with `set_clock` and `ret_only`, the two interruptions to `alt_r`,
the reported remainder handing `choose_ok` the predicate the acceptor
tested. -/
theorem check_nanosleep_sound_ok (i : SyscallInput) (rqtp rmtp : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_nanosleep i rqtp rmtp eff m = CheckOk m' evs) :
    nanosleep_spec rqtp rmtp i m (Ok eff m' evs) := by
  have hled := check_nanosleep_ok_copyins i rqtp rmtp eff m m' evs h
  unfold check_nanosleep at h
  unfold nanosleep_spec
  refine bind_ok0 _ _ _ _ _ _ _ _ _ (input_ok i m) ?_
  rcases hrq : read_bytes_map i.in_mem rqtp (Z_to_bv 64 16) with _ | req
  · simp only [hrq, reduceCtorEq] at h
  · simp only [hrq] at h ⊢
    apply record_copyins_clear_ok _ _ _ _ _ _ _ hled
    cases hv : timespec_valid_b req with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    | true =>
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      refine bind_ok0 _ _ _ _ _ _ _ _ _ (get_model_ok i m) ?_
      simp only [check_copyins, hled, access_ranges_eqb_refl, ↓reduceIte] at h
      cases hrm : w_is0 rmtp with
      | true =>
        simp only [hrm, ↓reduceIte] at h ⊢
        split at h
        next r c =>
          split at h
          next h0 =>
            injection h with hm hevs
            subst hm hevs
            rw [bv_eqb_eq] at h0
            subst h0
            exact alt_l _ _ i m _
              (bind_ok0 _ _ _ _ _ _ _ _ _ (modify_ok _ i m) (pure_ok _ i _))
          next =>
            split at h
            next hE =>
              injection h with hm hevs
              subst hm hevs
              rw [bv_eqb_eq] at hE
              subst hE
              exact alt_r _ _ i m _ (pure_ok _ i m)
            next => cases h
        next => cases h
      | false =>
        simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
        rcases hrm2 : read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) with _ | w
        · simp only [hrm2, reduceCtorEq] at h
        · simp only [hrm2] at h ⊢
          split at h
          next r c =>
            split at h
            next h0 =>
              injection h with hm hevs
              subst hm hevs
              rw [bv_eqb_eq] at h0
              subst h0
              exact alt_l _ _ i m _
                (bind_ok0 _ _ _ _ _ _ _ _ _ (modify_ok _ i m) (pure_ok _ i _))
            next => cases h
          next r a rem c =>
            split at h
            next hok =>
              injection h with hm hevs
              subst hm hevs
              simp only [Bool.and_eq_true, bv_eqb_eq] at hok
              obtain ⟨⟨rfl, rfl⟩, hrem⟩ := hok
              exact alt_r _ _ i m _
                (bind_ok0 _ _ _ _ _ _ _ _ _ (choose_ok _ rem i m hrem)
                  (bind_ok0 _ _ _ _ _ _ _ _ _ (modify_ok _ i m) (pure_ok _ i _)))
            next => cases h
          next => cases h

/-- Rocq: `Hrtimer.check_nanosleep_sound_unmodeled`.  Every `CheckUnmodeled`
the checker answers is a decline the spec makes: an unreadable request or
an unwritable remainder destination.  The -EINVAL arm cannot decline
(`check_ret_only_copyins_no_unmodeled`), and neither accepting arm can,
which the effect's `match` shows once the ledger test is split. -/
theorem check_nanosleep_sound_unmodeled (i : SyscallInput) (rqtp rmtp : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_nanosleep i rqtp rmtp eff m = CheckUnmodeled) :
    nanosleep_spec rqtp rmtp i m Unmodeled := by
  unfold check_nanosleep at h
  unfold nanosleep_spec
  refine bind_unmodeled2 _ _ _ _ _ _ _ (input_ok i m) ?_
  rcases hrq : read_bytes_map i.in_mem rqtp (Z_to_bv 64 16) with _ | req
  · exact unmodeled_intro i m
  · simp only [hrq] at h ⊢
    apply record_copyins_unmodeled
    cases hv : timespec_valid_b req with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at h
      exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
    | true =>
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      refine bind_unmodeled2 _ _ _ _ _ _ _ (get_model_ok i m) ?_
      simp only [check_copyins] at h
      cases hrm : w_is0 rmtp with
      | true =>
        simp only [hrm, ↓reduceIte] at h
        exfalso
        cases hc : access_ranges_eqb eff.eff_copyins [(rqtp, 16)] with
        | false => simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        | true =>
          simp only [hc, ↓reduceIte] at h
          split at h
          next =>
            split at h
            next => cases h
            next => split at h <;> cases h
          next => cases h
      | false =>
        simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
        rcases hrm2 : read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) with _ | w
        · exact unmodeled_intro i m
        · exfalso
          simp only [hrm2] at h
          cases hc : access_ranges_eqb eff.eff_copyins [(rqtp, 16)] with
          | false => simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
          | true =>
            simp only [hc, ↓reduceIte] at h
            split at h
            next => split at h <;> cases h
            next => split at h <;> cases h
            next => cases h

/-- Rocq: `Hrtimer.check_nanosleep_complete_ok`.  Every outcome the spec
admits is a `CheckOk` of the checker, with the same model and events.  The
spec's `input`, `record_copyins` and `get_model` binds are inverted one at
a time; each alternative's outcome is read off its `pure`; and the
acceptor's guards are then closed computations on the effect the spec
built — the ledger by `access_ranges_eqb_refl`, the return and address by
`bv_eqb_refl`, the remainder by the predicate `choose` was handed. -/
theorem check_nanosleep_complete_ok (i : SyscallInput) (rqtp rmtp : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : nanosleep_spec rqtp rmtp i m (Ok eff m' evs)) :
    check_nanosleep i rqtp rmtp eff m = CheckOk m' evs := by
  unfold nanosleep_spec at h
  unfold check_nanosleep
  rw [bind_input_iff] at h
  rcases hrq : read_bytes_map i.in_mem rqtp (Z_to_bv 64 16) with _ | req
  · simp only [hrq, Monad.unmodeled, reduceCtorEq] at h
  · simp only [hrq] at h
    have hne : bv_eqb (errno_ret EINTR) (Z_to_bv 64 0) = false := by decide
    cases hv : timespec_valid_b req with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte] at h ⊢
      obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m eff m' evs h
      simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
      obtain ⟨rfl, rfl, rfl⟩ := hcore
      simp only [mkEffect, List.append_nil]
      exact check_ret_only_copyins_refl _ _ _ _
    | true =>
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m eff m' evs h
      rw [bind_get_model_iff] at hcore
      cases hrm : w_is0 rmtp with
      | true =>
        simp only [hrm, ↓reduceIte, alt_iff] at hcore ⊢
        rcases hcore with h2 | h2
        · simp only [Monad.set_clock, bind_modify_iff, ret_only, pure_iff, outcome.Ok.injEq] at h2
          obtain ⟨rfl, rfl, rfl⟩ := h2
          simp only [with_copyins, List.append_nil, check_copyins,
            access_ranges_eqb_refl, ↓reduceIte, bv_eqb_refl]
        · simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h2
          obtain ⟨rfl, rfl, rfl⟩ := h2
          simp only [with_copyins, List.append_nil, check_copyins,
            access_ranges_eqb_refl, ↓reduceIte, bv_eqb_refl, hne, Bool.false_eq_true]
      | false =>
        simp only [hrm, Bool.false_eq_true, ↓reduceIte] at hcore ⊢
        rcases hrm2 : read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) with _ | w
        · simp only [hrm2, Monad.unmodeled, reduceCtorEq] at hcore
        · simp only [hrm2, alt_iff] at hcore ⊢
          rcases hcore with h2 | h2
          · simp only [Monad.set_clock, bind_modify_iff, ret_only, pure_iff,
              outcome.Ok.injEq] at h2
            obtain ⟨rfl, rfl, rfl⟩ := h2
            simp only [with_copyins, List.append_nil, check_copyins,
              access_ranges_eqb_refl, ↓reduceIte, bv_eqb_refl]
          · simp only [bind_choose_iff, Monad.set_clock, bind_modify_iff, pure_iff,
              outcome.Ok.injEq] at h2
            obtain ⟨rem, hrem, rfl, rfl, rfl⟩ := h2
            simp only [with_copyins, List.append_nil, check_copyins,
              access_ranges_eqb_refl, ↓reduceIte, bv_eqb_refl, hrem, Bool.and_self]

/-- Rocq: `Hrtimer.check_nanosleep_complete_unmodeled`.  Every decline of
the spec is a `CheckUnmodeled` of the checker, whatever effect the checker
is shown: the spec's `unmodeled` sites are exactly the checker's, and
none of them looks at `eff`. -/
theorem check_nanosleep_complete_unmodeled (i : SyscallInput) (rqtp rmtp : word) (m : Model)
    (eff : SyscallEffect) (h : nanosleep_spec rqtp rmtp i m Unmodeled) :
    check_nanosleep i rqtp rmtp eff m = CheckUnmodeled := by
  unfold nanosleep_spec at h
  unfold check_nanosleep
  rw [bind_input_iff] at h
  rcases hrq : read_bytes_map i.in_mem rqtp (Z_to_bv 64 16) with _ | req
  · rfl
  · simp only [hrq] at h
    cases hv : timespec_valid_b req with
    | false =>
      simp only [hv, Bool.not_false, ↓reduceIte, record_copyins_unmodeled_iff, err_ret, ret_only,
        pure_iff, reduceCtorEq] at h
    | true =>
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, record_copyins_unmodeled_iff,
        bind_get_model_iff] at h ⊢
      cases hrm : w_is0 rmtp with
      | true =>
        simp only [hrm, ↓reduceIte, alt_iff, Monad.set_clock, bind_modify_iff, ret_only, err_ret,
          pure_iff, reduceCtorEq, or_self] at h
      | false =>
        simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
        rcases hrm2 : read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) with _ | w
        · rfl
        · simp only [hrm2, alt_iff, Monad.set_clock, bind_modify_iff, ret_only, pure_iff,
            bind_choose_iff, reduceCtorEq, and_false, exists_false, or_self] at h

/-! ## The witness — `Checks/Witness/Kernel/Time/Hrtimer.v`

The witness always takes the COMPLETED-SLEEP arm.  That arm needs nothing
chosen — no remainder is written — so it is available for every model
state the guards let through, and the interrupted arm, whose remainder
would have to be constructed, is never needed to show the spec is
receptive.

It reads the model only to compute the new clock: there is no gate on
`m_clock` to re-play, `nanosleep_clock` clamping a saturating deadline
(`ktime_add_safe`, kernel/time/hrtimer.c:340-352, Linux v6.18.46) rather than the spec
declining it, and none on the request's seconds field either — a `tv_sec`
at or above `KTIME_SEC_MAX` is a sleep toward `KTIME_MAX` (`ktime_set`,
include/linux/ktime.h:36-42, Linux v6.18.46) and the completed arm exhibits it like any
other.

Every outcome it exhibits is reached through a successful read of the
request, so every one of them carries that read in its ledger:
`nanosleep_spec` wraps the whole arm in `record_copyins`, and a witness
that left the ledger empty would no longer be an outcome the spec
admits. -/

/-- Rocq: `Hrtimer.nanosleep_witness`. -/
def nanosleep_witness (rqtp rmtp : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  match read_bytes_map i.in_mem rqtp (Z_to_bv 64 16) with
  | none => Unmodeled                          -- unreadable request
  | some req =>
    if !(timespec_valid_b req) then
      Ok (with_copyins [(rqtp, 16)] (mkEffect (errno_ret EINVAL) [] [])) m []
    else
      let done : outcome SyscallEffect :=
        Ok (with_copyins [(rqtp, 16)] (mkEffect (Z_to_bv 64 0) [] []))
          (with_clock (nanosleep_clock (m_clock m) req []) m) []
      if w_is0 rmtp then done
      else
        match read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) with
        | none => Unmodeled                    -- unwritable remainder
        | some _ => done

/-- Rocq: `Hrtimer.nanosleep_witness_ok`.  The witness is an outcome of the
spec on every input and model: the -EINVAL answer and the completed sleep
each by `record_copyins_ok_empty` over the spec's own `pure`, the two
declines by `unmodeled_intro` under the same binds.  The `cases` on each
guard generalize the goal, so the `simp only` calls that follow reduce
the constant guards and never cite the equations. -/
theorem nanosleep_witness_ok (i : SyscallInput) (rqtp rmtp : word) (m : Model) :
    nanosleep_spec rqtp rmtp i m (nanosleep_witness rqtp rmtp i m) := by
  unfold nanosleep_spec nanosleep_witness
  refine bind_step _ _ _ _ _ _ _ (input_ok i m) ?_
  rcases hrq : read_bytes_map i.in_mem rqtp (Z_to_bv 64 16) with _ | req
  · exact unmodeled_intro i m
  · dsimp only
    cases hv : timespec_valid_b req with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      refine record_copyins_ok_empty _ _ i m _ m [] ?_ ?_
      · rfl
      · exact pure_ok _ i m
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hrm : w_is0 rmtp with
      | true =>
        simp only [↓reduceIte]
        refine record_copyins_ok_empty _ _ i m _ _ [] ?_ ?_
        · rfl
        · refine bind_step _ _ _ _ _ _ _ (get_model_ok i m) ?_
          exact alt_l _ _ i m _ (bind_step _ _ _ _ _ _ _ (modify_ok _ i m) (pure_ok _ i _))
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases hrm2 : read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) with _ | w
        · dsimp only
          apply record_copyins_unmodeled
          refine bind_unmodeled2 _ _ _ _ _ _ _ (get_model_ok i m) ?_
          exact unmodeled_intro i m
        · dsimp only
          refine record_copyins_ok_empty _ _ i m _ _ [] ?_ ?_
          · rfl
          · refine bind_step _ _ _ _ _ _ _ (get_model_ok i m) ?_
            exact alt_l _ _ i m _ (bind_step _ _ _ _ _ _ _ (modify_ok _ i m) (pure_ok _ i _))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.Hrtimer
