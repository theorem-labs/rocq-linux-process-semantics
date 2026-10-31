-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Kernel/Time/Hrtimer.v
-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Kernel/Time/Hrtimer.v

import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.Hrtimer
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.Hrtimer
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress


/-! # Checks.Cases.Checks.Sys.Kernel.Time.Hrtimer — what the nanosleep checker answers, read off against Linux

Pins over `Checks.Sys.Kernel.Time.Hrtimer.check_nanosleep`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Kernel/Time/Hrtimer.v`'s checker, and
over `nanosleep_witness`, the twin of
`theories/LinuxProcessSem/Checks/Witness/Kernel/Time/Hrtimer.v`'s witness.
Not part of the trusted specification: this file is QA on the executable
definitions, written to be READ, and every claim in it is a claim about
what the kernel does, with the citation beside it.  Every kernel line
below was read at Linux v6.18.46 (commit 1f99e9ab748f), and the Rocq
cases restated here at the checker's `rocq-baseline`,
a71fd38a08571d519b9cfc5f66308db5c26da570.

WHAT THIS FILE IS.  Rocq states its worked cases for this syscall on the
CHECKER: the `Example`s of `theories/LinuxProcessSem/Checks/Cases/Kernel/Time/Hrtimer.v`
are `check_syscall … = CheckOk …` and `= CheckReject`, and its
`nanosleep_admissible_remainder_is_a_judged_request` quantifies over the
checker's arguments.  The Lean port of that file,
`Checks/Cases/Kernel/Time/Hrtimer.lean`, restated each of them on the
RELATION `nanosleep_spec`, because the Lean tree had no executable checker
when it was written; those restatements carry the `rocq-twin:` marks and
stay where they are.  This file states the same cases on the checker,
under the Rocq names, in the namespace of the checker's own Cases mirror,
and adds the ones a checker invites that a relation does not: the lies
on the return word, the ledger and the remainder that the acceptor must
REJECT rather than merely fail to accept.  There is no
`theories/…/Checks/Cases/Checks/Sys/…` file for it to twin, so nothing
here is marked `rocq-twin:` — the credit for the Rocq lemma set stays on
the spec-level restatements, whose `covers:` block is the one register
`check_lean_cases_parity.py` reads, and no tool holds THIS file to the
Rocq names; each pin cites the kernel line the Rocq
docstring argues from instead, and the argument is repeated in its own
words so the citation can be checked against it.  The universal closes
by the checker's own case analysis.

HOW THE CONCRETE CASES CLOSE.  The checker is a closed computation on
these fixtures and `Model` has no `DecidableEq`, so a concrete case would
be `rfl`.  Here `rfl` exhausts `maxRecDepth` on every case, on the
accepting shapes and the -EINVAL shape alike, and so does `rfl` on the
request's validity gate alone (`timespec_valid_b ts_1s = true`) and on
`nanosleep_clock` alone; `decide` closes the gate but is not available
for the cases, whose result type has no `Decidable` instance.  The
mechanism is the one the clock_gettime pins record in
`Checks/Cases/Checks/Sys/Kernel/Time/PosixTimers.lean`'s header, in one
sentence: `rfl`'s `whnfCore` runs under the projection
setting `backward.isDefEq.lazyWhnfCore` selects, the gate's `Int`
comparison against `2 ^ 63` meets a stuck `BitVec.toNat` under it, and
the depth goes into a `Nat.sub` on the literal.  That the cause is the
setting and not the checker is pinned at the end of this file, as it is
there: with the option off, the completed sleep closes by plain `rfl`.
So the concrete cases close by `nanosleep_check_norm`: `unfold` of the alias below,
of the checker and of the three `Checks/Sys/Prelude.lean` wrappers it calls,
then `sys_norm`, the normal form `Checks/Cases/Tactic.lean` defines and
the spec-level Cases already use for these fixtures — a `simp only` pass
under `+decide` with the `sys_simp` set, which alone does not close a
case, then the `+ground` pass, which evaluates what the first left.
The `match` on the request is reduced only when a registered read
rewrite hands it its constructor, and
`Checks/Cases/Kernel/Time/Hrtimer.lean` registers one for every request
these cases read.  On ONE fixture that is not enough: `read_request_half`
is registered, but its left side names the reader on `bytes_at 8192
ts_half`, and the first pass leaves `in_arg (nanosleep_input …) 0` folded
so the rewrite has nothing to match until the second pass — which
evaluates the read itself and stalls inside `read_bytes_acc` on a `match`
over `[].get?Internal 0`.  The pins on an unreadable request therefore
close by `conv => lhs; whnf` instead: `Meta.whnf` evaluates that read to
`none`, and the checker's first `match` reduces to `CheckUnmodeled`
before any gate, and so before any `2 ^ 63`, is reached.  (A destination
unwritable in its last byte needs no such step: `wmem_ts` is `rlim_out`,
an `if` on two comparisons with no list behind it, and `nanosleep_check_norm`
closes the 4097 pin below.)  The witness pins close the same two ways, through
`nanosleep_offer_norm`.  When the option's default changes, or `sys_norm` learns to
reduce a closed read, the macros here collapse to `rfl` and this
paragraph goes.

HOW THE CALL IS STATED.  Rocq's cases go through `check_syscall`, the
dispatcher.  The sections before the sentinel state them on the call the
`nanosleep` arm makes — `check_nanosleep` on the request register and
the remainder register — through `nanosleep_check` below, which is what
`ca_check arm_nanosleep (nanosleep_input rmtp req) eff m` unfolds to; the
section after it restates each Rocq case through `check_syscall`, over
`checked_table`, and proves it from its twin here.  `nanosleep_check`
leaves this file when the cases before the sentinel are restated in place
on `check_syscall`, which folds that section into them; the registration
appended its twins rather than rewriting these, so the alias stays until
that rewrite.

WHAT NO PROBE CAN REACH.  Where a probe case shows the same decision of
the Rocq checker it is named in prose; the kernel line stays the
evidence.  Independently of that, `m_clock` is internal state no trace
carries — a later monotonic reading is judged against it, so the `clocked` mode of
`testing/syscall-check/tests/nanosleep_spec.c` can see an advance that is
too LARGE and cannot see one that is too small — and the request CEILING and the
SATURATING deadline both need a request or a clock 292 years along, so
`testing/syscall-check/tests/nanosleep_spec.c` cannot issue them from
either side.  The remainder shapes the mutation operators cannot spell
(a chosen `tv_sec` under the envelope, a valid remainder on a completed
sleep) are the rest of what is here.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Time.Hrtimer

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.Hrtimer
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.PosixTimers
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.Hrtimer

/-! ## The call, as the arm makes it

The fixtures are the Rocq cases' own, from `Checks/Cases/Kernel/Time/Hrtimer.lean`
and the `clock_gettime` cases it opens: `nanosleep(8192, rmtp)` with
`req` readable at 8192 and `wmem_ts` as the writable view
(`nanosleep_input`), where a non-NULL `rmtp` is 4096, wholly writable,
4104, straddling into the unwritable page, or another address a pin
names for its own reason; a model whose recorded clock reads `t`
(`clock_model t`); and the byte strings `ts_*`, sixteen bytes of `struct
timespec` unless the fixture's own docstring says otherwise. -/

/-- The check the dispatcher arm performs for `nanosleep(8192, rmtp)`:
`check_nanosleep` on the request register and the remainder register, as
Rocq's `arm_nanosleep` (`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`)
applies it.  The header says when this alias goes. -/
def nanosleep_check (rmtp : word) (req : List byte) (eff : SyscallEffect) (m : Model) :
    check_result :=
  check_nanosleep (nanosleep_input rmtp req) (in_arg (nanosleep_input rmtp req) 0)
    (in_arg (nanosleep_input rmtp req) 1) eff m

/-- The witness the same arm offers for that call. -/
def nanosleep_offer (rmtp : word) (req : List byte) (m : Model) : outcome SyscallEffect :=
  nanosleep_witness (in_arg (nanosleep_input rmtp req) 0) (in_arg (nanosleep_input rmtp req) 1)
    (nanosleep_input rmtp req) m

/-- The alias reads the two registers the arm reads: the request is at
8192 and the remainder register is `rmtp` itself.
model: `nanosleep_input`'s registers read back through `in_arg` -/
example :
    in_arg (nanosleep_input 4096 ts_1s) 0 = 8192 ∧ in_arg (nanosleep_input 4096 ts_1s) 1 = 4096 := by
  decide

/-! The two closers the header describes.  `nanosleep_check_norm` opens the
alias, the checker and the Prelude wrappers and hands the result to
`sys_norm`; `nanosleep_offer_norm` does the same for the witness.  Neither
is a proof of anything on its own: a case that `sys_norm` leaves open
fails here as it would fail under `rfl`, and the pins that need
`conv => lhs; whnf` say so where they stand.  The names carry the syscall
because `macro` declarations are global: `Checks/Cases/Checks/Sys/Kernel/Groups.lean`
declares a `check_norm` with another expansion, and a module importing
both would hold two parsers for one token. -/
macro "nanosleep_check_norm" : tactic =>
  `(tactic| (unfold nanosleep_check check_nanosleep check_ret_only_copyins check_ret_only check_copyins; sys_norm))
macro "nanosleep_offer_norm" : tactic =>
  `(tactic| (unfold nanosleep_offer nanosleep_witness; sys_norm))

/-- The zero request, read back whole: one of the two requests the cases
below read that the spec-level Cases do not (`ts_minus_one_sec` is the
other), so its rewrite is registered here.
model: a closed `read_bytes_map` over a fixture map, a rewrite for `sys_norm`. -/
theorem read_request_zero :
    read_bytes_map (Checks.Cases.Prelude.bytes_at 8192 ts_zero) 8192 (Z_to_bv 64 16) = some ts_zero := by decide
attribute [sys_simp] read_request_zero

/-! ## The completed sleep and the interruption, from a clock at zero

`SYSCALL_DEFINE2(nanosleep)` (kernel/time/hrtimer.c:2189-2205, Linux v6.18.46) hands
`hrtimer_nanosleep` (kernel/time/hrtimer.c:2159-2185, Linux v6.18.46) the request as a
relative ktime_t, and `do_nanosleep` (kernel/time/hrtimer.c:2112-2145, Linux v6.18.46)
sleeps toward it: 0 when the timer fired, and otherwise the remainder to
`rmtp` through `nanosleep_copyout` (kernel/time/hrtimer.c:2093-2110, Linux v6.18.46) and
`-ERESTART_RESTARTBLOCK`, which
`arch_do_signal_or_restart` (arch/riscv/kernel/signal.c:396-463, Linux v6.18.46) turns
into the -EINTR the program sees when a handler runs. -/

/-- MODEL-INTERNAL STATE.  A completed sleep carries `m_clock` forward by
the WHOLE request: `hrtimer_nanosleep` arms the soft expiry at now plus
the request, a timer never fires early, and `do_nanosleep` returns 0 only
once it has fired, so at least that much elapsed on the clock `m_clock`
tracks.  Nothing about `m_clock` reaches a trace, so no probe sees the
advance itself; the conformance suite feels it only indirectly, through
a later `clock_gettime` the sleep must have moved (the `clocked` mode of
`testing/syscall-check/tests/nanosleep_spec.c`).  `rmtp` is NULL here, the shape a program that does not care
what was left passes.
kernel: kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep@v6.18.46 -/
theorem nanosleep_completed_sleep_advances_the_clock :
    nanosleep_check 0 ts_1s (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 0)
      = CheckOk (clock_model 1000000000) [] := by
  nanosleep_check_norm

/-- MODEL-INTERNAL STATE — the completed sleep at a WRITABLE `rmtp`, the
one accepting arm no Rocq case reaches.  `do_nanosleep` returns 0 the
moment the timer has fired, before the `restart->nanosleep.type` test and
so before any copy-out, so a non-NULL `rmtp` is left untouched and the
effect carries no write; the timer fired, so the clock moved by the whole
request exactly as at a NULL `rmtp`.  Without this pin a checker that
held the clock still on this arm alone would pass every other case and
every theorem, since both sides would still agree.
kernel: kernel/time/hrtimer.c:nanosleep,hrtimer_nanosleep,do_nanosleep@v6.18.46 -/
theorem nanosleep_completed_sleep_at_a_writable_rmtp_advances_the_clock :
    nanosleep_check 4096 ts_1s (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 0)
      = CheckOk (clock_model 1000000000) [] := by
  nanosleep_check_norm

/-- MODEL-INTERNAL STATE.  With a NULL `rmtp` the syscall records
`TT_NONE` (kernel/time/hrtimer.c:2201, Linux v6.18.46), `do_nanosleep` skips the copy-out
and returns the restart code with nothing written, and the interrupted
arm has nowhere to report the remainder: how much of the sleep elapsed is
unknowable, so the clock stays where it was.  This is the only accepted
`nanosleep` outcome that does not move `m_clock`, and the pair with the
case above is what makes the distinction non-vacuous.
kernel: kernel/time/hrtimer.c:nanosleep,do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_null_remainder_interruption_holds_the_clock :
    nanosleep_check 0 ts_1s (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] []))
      (clock_model 0) = CheckOk (clock_model 0) [] := by
  nanosleep_check_norm

/-- MODEL-INTERNAL STATE.  The interrupted arm carries `m_clock` forward by
the request LESS the reported remainder — a second requested with a
quarter second left is three quarters of a second elapsed.  `do_nanosleep`
measures the remainder against the armed expiry and `nanosleep_copyout`
writes it, so what the model records is the one-sided fact the kernel
establishes, invisible from outside for the same reason the case above is.
kernel: kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_interruption_advances_by_the_difference :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
      (clock_model 0) = CheckOk (clock_model 750000000) [] := by
  nanosleep_check_norm

/-- MODEL-INTERNAL STATE, and the sharp one.  A remainder LARGER than the
request is admissible: `hrtimer_nanosleep` sets the range with
`current->timer_slack_ns` past the soft expiry — 50 microseconds by
default, `init_task`'s `.timer_slack_ns = 50000` (init/init_task.c:146,
Linux v6.18.46) — and `do_nanosleep` measures what is left against the HARD
expiry, so a one-microsecond sleep can report 51 microseconds remaining,
and `nanosleep_rem_ok_b` deliberately does not bound the remainder by the
request.  The advance is then floored at the clock's previous value rather
than going negative: without the `max (bv_unsigned prev)` in
`nanosleep_clock` the difference would be -50000 and the clock would wrap
to within 50 microseconds of 2^64.  The reported remainder is observable;
the clock it moves is not.
kernel: kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_remainder_past_the_request_floors_at_zero :
    nanosleep_check 4096 ts_1us
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_51us)] []))
      (clock_model 0) = CheckOk (clock_model 0) [] := by
  nanosleep_check_norm

/-- The request's NANOSECONDS carry the clock, not its seconds alone.
Every case above and below whose sleep completes asks for whole seconds,
or for a request `ktime_set` saturates, or is interrupted with more left
than it asked; a `nanosleep_clock` handed the seconds field alone would
answer all of them.  One microsecond completed advances by 1000, and one
nanosecond short of a second by 999999999 — the largest `tv_nsec`
`timespec64_valid` accepts, on the accepting side of its `>= NSEC_PER_SEC`
test, whose refusing side `ts_denorm` pins below.  The interrupted arm
has its own pin, `nanosleep_interruption_advances_by_the_nanoseconds_elapsed`.
kernel: kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep; include/linux/time64.h:timespec64_valid; include/linux/ktime.h:ktime_set@v6.18.46 -/
theorem nanosleep_completed_sleep_advances_by_the_nanoseconds :
    nanosleep_check 0 ts_1us (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 0)
        = CheckOk (clock_model 1000) []
      ∧ nanosleep_check 4096 ts_1s_minus (with_copyins [(8192, 16)] (mkEffect 0 [] []))
          (clock_model 0) = CheckOk (clock_model 999999999) [] := by
  refine ⟨?_, ?_⟩ <;> nanosleep_check_norm

/-- A ZERO request is a valid sleep, not an error: `timespec64_valid`
refuses a negative `tv_sec` and a `tv_nsec` at or past `NSEC_PER_SEC`,
and `{0, 0}` is neither, so `nanosleep({0,0}, NULL)` — the yield idiom —
arms a timer at now and returns 0 with the clock where it was; and the
interruption stays admissible, since `do_nanosleep` tests `t->task`
before the signal and a signal already pending can win that race.  No
other accepting case has a request without a positive duration, so a
request gate that also demanded positivity — the remainder's rule,
which `nanosleep_rem_ok_b` states and the request must NOT inherit —
would pass every other pin here and turn this call into -EINVAL.
kernel: include/linux/time64.h:timespec64_valid; kernel/time/hrtimer.c:nanosleep,do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_zero_request_is_a_valid_sleep :
    nanosleep_check 0 ts_zero (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 0)
        = CheckOk (clock_model 0) []
      ∧ nanosleep_check 4096 ts_zero (with_copyins [(8192, 16)] (mkEffect 0 [] []))
          (clock_model 0) = CheckOk (clock_model 0) []
      ∧ nanosleep_check 0 ts_zero
          (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] [])) (clock_model 0)
        = CheckOk (clock_model 0) []
      ∧ nanosleep_check 0 ts_zero
          (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) (clock_model 0)
        = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nanosleep_check_norm

/-- MODEL-INTERNAL STATE — the remainder equal to the request.  An
interruption before any of the sleep elapsed reports the whole request
back, and the clock holds: `max prev` meets `prev + request - request`
exactly at `prev`, the point where the floor starts to bind.  Stated from
a nonzero clock so that "holds" is not "resets".
kernel: kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_interruption_with_the_whole_request_left_holds_the_clock :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_1s)] []))
      (clock_model 5000) = CheckOk (clock_model 5000) [] := by
  nanosleep_check_norm

/-- The request's NANOSECONDS carry the clock on the INTERRUPTED arm too.
`nanosleep_completed_sleep_advances_by_the_nanoseconds` pins the completed
sleep; every other interruption at a writable `rmtp` in this file asks for
whole seconds, or for a request `ktime_set` saturates, or reports back at
least what it asked, so a `nanosleep_clock` handed the request's seconds
field alone answers all of them the same — the deep review's pins-only
sweep at be12684c2 showed exactly that (its mutant S18).  A request one
nanosecond short of a second, interrupted with one microsecond left, moves
a clock at 5000 to 5000 + 999999999 - 1000: `do_nanosleep` reports
`node.expires` less the clock at wake, and `hrtimer_nanosleep` set that
expiry from the `ktime_t` `timespec64_to_ktime` built out of BOTH fields;
the -EINTR the caller sees is `arch_do_signal_or_restart`'s rewrite of
the restart word `do_nanosleep` returned.
kernel: kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; include/linux/ktime.h:timespec64_to_ktime,ktime_set; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_interruption_advances_by_the_nanoseconds_elapsed :
    nanosleep_check 4096 ts_1s_minus
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_1us)] []))
      (clock_model 5000) = CheckOk (clock_model 1000003999) [] := by
  nanosleep_check_norm

/-! ## The request at the ceiling, and the band above it

`timespec64_to_ktime` is `ktime_set` (include/linux/ktime.h:36-42, Linux v6.18.46), whose
`if (unlikely(secs >= KTIME_SEC_MAX)) return KTIME_MAX;` hands
`hrtimer_nanosleep` the end of `ktime_t` rather than a product for every
`tv_sec` from `KTIME_SEC_MAX` up.  Above that band sits
`timespec64_valid` (include/linux/time64.h:97-106, Linux v6.18.46), which reads `tv_sec`
as the `s64` it is and refuses a negative one, and `tv_nsec` as an
`unsigned long` and refuses one at or past `NSEC_PER_SEC`. -/

/-- MODEL-INTERNAL STATE, and the arm that replaced a decline.  A request
AT `KTIME_SEC_MAX` is ANSWERED, and a completed sleep carries `m_clock` to
`KTIME_MAX`: `ktime_set`'s early return hands `hrtimer_nanosleep` the end
of `ktime_t`, and the sleep that follows is an ordinary interruptible one
toward that deadline.  A probe cannot reach this from either side —
issuing the call would park the guest for 292 years, and no mutation can
put a chosen non-uniform value in a request the kernel actually read.
The decline this replaced was not conservative: `nanosleep_rem_ok_b`
admits a remainder with `tv_sec = KTIME_SEC_MAX`, and the retry loop
`while (nanosleep(&ts, &ts) == -1 && errno == EINTR);` hands the
remainder back as the next request, so one admissible environment choice
made the next call unmodeled and cost the program its `modeled` status.
kernel: include/linux/ktime.h:ktime_set; kernel/time/hrtimer.c:nanosleep@v6.18.46 -/
theorem nanosleep_request_at_the_ceiling_sleeps_to_ktime_max :
    nanosleep_check 0 ts_ceiling (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 0)
      = CheckOk (clock_model (2 ^ 63 - 1)) [] := by
  nanosleep_check_norm

/-- MODEL-INTERNAL STATE — the control, and the reason the case above is
not vacuous.  One second BELOW the ceiling `ktime_set` converts rather
than saturating, so the recorded clock is the plain product
9223372035 * 10^9 and not `KTIME_MAX`.  The two requests are one second
apart and the clocks they record are 1854775807 ns apart: that gap is
exactly the early return firing, and a `timespec_ktime` that always
converted, or always saturated, would fail one of the pair.
kernel: include/linux/ktime.h:ktime_set; kernel/time/hrtimer.c:nanosleep@v6.18.46 -/
theorem nanosleep_request_below_the_ceiling_converts :
    nanosleep_check 0 ts_below_ceiling (with_copyins [(8192, 16)] (mkEffect 0 [] []))
      (clock_model 0) = CheckOk (clock_model 9223372035000000000) [] := by
  nanosleep_check_norm

/-- MODEL-INTERNAL STATE — the band's TOP.  The band `ktime_set` saturates
over is `[KTIME_SEC_MAX, 2^63)` of whole seconds, and every other case
here sits at its BOTTOM: a spec that judged `tv_sec = KTIME_SEC_MAX` and
went on declining everything above it would satisfy all of them.  The
largest `tv_sec` `timespec64_valid` accepts is 2^63 - 1, one below the
word that reads as negative, and it sleeps to `KTIME_MAX` exactly as the
bottom of the band does, because `ktime_set` tests `secs >= KTIME_SEC_MAX`
and returns the same constant across the whole band.
kernel: include/linux/ktime.h:ktime_set; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem nanosleep_request_at_the_top_of_the_band_sleeps_to_ktime_max :
    nanosleep_check 0 ts_top_of_band (with_copyins [(8192, 16)] (mkEffect 0 [] []))
      (clock_model 0) = CheckOk (clock_model (2 ^ 63 - 1)) [] := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the same rejection at
the top of the band as at its bottom.  `do_nanosleep` returns 0, not the
restart code, when `hrtimer_expires_remaining` is not positive, so an
-EINTR reporting a remainder of exactly zero is refused wherever the
request sits; with this pair the whole band is judged in both directions
rather than merely answered in one.
kernel: kernel/time/hrtimer.c:do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_at_the_top_of_the_band_zero_remainder_rejected :
    nanosleep_check 4096 ts_top_of_band
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-- MODEL-INTERNAL STATE.  The ceiling request INTERRUPTED: the clock moves
to the deadline the kernel armed — `KTIME_MAX`, by `ktime_set` — less the
remainder `do_nanosleep` reported, exactly as at any smaller request.  A
quarter second left leaves `KTIME_MAX - 250000000`.
kernel: include/linux/ktime.h:ktime_set; kernel/time/hrtimer.c:do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_request_at_the_ceiling_interrupted :
    nanosleep_check 4096 ts_ceiling
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
      (clock_model 0) = CheckOk (clock_model 9223372036604775807) [] := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and the REJECTION the
old decline used to cost.  At the ceiling the old spec answered
`CheckUnmodeled` for EVERY effect, so it refused nothing there.  Now the
same -EINTR reporting a remainder of exactly zero is REFUSED, as it is at
every other request: `do_nanosleep` returns 0 for a non-positive remainder.
kernel: kernel/time/hrtimer.c:do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_at_the_ceiling_zero_remainder_rejected :
    nanosleep_check 4096 ts_ceiling
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the other half of the
band, and the boundary the ceiling arm must NOT have moved.  2^63 seconds
is outside `timespec64_valid`, because `tv_sec` is signed and that word
reads as negative, so `SYSCALL_DEFINE2(nanosleep)` answers -EINVAL
(kernel/time/hrtimer.c:2197-2198, Linux v6.18.46) and no sleep, and judging the ceiling
did not widen the band that answers.  Without this case a
`timespec_valid_b` weakened alongside the gate would go unnoticed.
kernel: kernel/time/hrtimer.c:nanosleep; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem nanosleep_request_at_two_to_the_63_is_einval :
    nanosleep_check 4096 ts_neg_sec (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] []))
      (clock_model 0) = CheckOk (clock_model 0) [] := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the -EINVAL arm has no
other answer.  A completed sleep on the request `timespec64_valid`
refuses describes a kernel that armed a timer it never reached: the
`-EINVAL` return precedes `hrtimer_nanosleep` in `SYSCALL_DEFINE2(nanosleep)`,
so a 0 there is rejected.
kernel: kernel/time/hrtimer.c:nanosleep; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem nanosleep_request_at_two_to_the_63_completed_sleep_rejected :
    nanosleep_check 4096 ts_neg_sec (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 0)
      = CheckReject := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — nor is an interruption
one.  -EINTR is `arch_do_signal_or_restart`'s rewrite of the restart code
`do_nanosleep` returns, and the invalid request never reaches
`do_nanosleep`; the checker's -EINVAL arm is `check_ret_only_copyins` on
that one word, so the -EINTR is refused whatever the remainder register.
kernel: kernel/time/hrtimer.c:nanosleep; include/linux/time64.h:timespec64_valid; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_request_at_two_to_the_63_interruption_rejected :
    nanosleep_check 4096 ts_neg_sec (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — `tv_nsec`'s two refusals
in `timespec64_valid`, which casts the field to `unsigned long` and
refuses anything at or past `NSEC_PER_SEC`: exactly 10^9 (the unnormalized
`ts_denorm`) and -1 (the word `ts_neg_nsec` spells, which reads as
2^64 - 1 once cast).  Both are -EINVAL from `SYSCALL_DEFINE2(nanosleep)`,
and the checker admits exactly that.
kernel: kernel/time/hrtimer.c:nanosleep; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem nanosleep_request_with_an_invalid_nsec_is_einval :
    nanosleep_check 4096 ts_denorm (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] []))
        (clock_model 0) = CheckOk (clock_model 0) []
      ∧ nanosleep_check 4096 ts_neg_nsec
          (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) (clock_model 0)
        = CheckOk (clock_model 0) [] := by
  refine ⟨?_, ?_⟩ <;> nanosleep_check_norm

/-- tv_sec = -1, tv_nsec = 0: the negative second a program actually
passes, all ones in the seconds field, which `timespec_valid_b` reads
unsigned as 2^64 - 1. -/
def ts_minus_one_sec : List byte :=
  [255, 255, 255, 255, 255, 255, 255, 255] ++ [0, 0, 0, 0, 0, 0, 0, 0]

/-- The request of minus one second, read back whole.
model: a closed `read_bytes_map` over a fixture map, a rewrite for `sys_norm`. -/
theorem read_request_minus_one_sec :
    read_bytes_map (Checks.Cases.Prelude.bytes_at 8192 ts_minus_one_sec) 8192 (Z_to_bv 64 16)
      = some ts_minus_one_sec := by decide
attribute [sys_simp] read_request_minus_one_sec

/-- The TOP of the invalid band.  `ts_neg_sec` above is `INT64_MIN`, the
first second `timespec64_valid` refuses; this is -1, the last, and the
one a program passes by mistake: `tv_sec < 0` refuses both, and the
checker answers -EINVAL with the ledger and refuses the completed sleep,
exactly as at 2^63.  Without it the band's upper end rests on a
comparison against `2 ^ 63` alone.
kernel: kernel/time/hrtimer.c:nanosleep; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem nanosleep_request_of_minus_one_second_is_einval :
    nanosleep_check 4096 ts_minus_one_sec
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) (clock_model 0)
        = CheckOk (clock_model 0) []
      ∧ nanosleep_check 4096 ts_minus_one_sec (with_copyins [(8192, 16)] (mkEffect 0 [] []))
          (clock_model 0) = CheckReject := by
  refine ⟨?_, ?_⟩ <;> nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — and a completed sleep
on either of those requests is refused, for the reason the 2^63 case
gives: `timespec64_valid`'s refusal precedes the timer.
kernel: kernel/time/hrtimer.c:nanosleep; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem nanosleep_request_with_an_invalid_nsec_completed_sleep_rejected :
    nanosleep_check 4096 ts_denorm (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 0)
        = CheckReject
      ∧ nanosleep_check 4096 ts_neg_nsec (with_copyins [(8192, 16)] (mkEffect 0 [] []))
          (clock_model 0) = CheckReject := by
  refine ⟨?_, ?_⟩ <;> nanosleep_check_norm

/-- MODEL-INTERNAL STATE — the remainder AT the ceiling, the value that
used to poison the next call.  `nanosleep_rem_ok_b` admits it:
9223372036 * 10^9 is 854775808 ns below `CLOCK_NS_ENVELOPE`, so the
envelope conjunct passes, and the other three do too.  The clock does not
move — the request was a second and the remainder is 292 years, so the
difference is negative and `max prev` holds it — which is the
`nanosleep_clock` floor doing its job at the top of the range rather than
the bottom.  Nothing in `do_nanosleep` bounds `hrtimer_expires_remaining`
by the request: the slack argument of the 51-microsecond case is the
same argument at a different scale.
kernel: kernel/time/hrtimer.c:do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_remainder_at_the_ceiling_admitted :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_ceiling)] []))
      (clock_model 0) = CheckOk (clock_model 0) [] := by
  nanosleep_check_norm

/-! ## Every admissible remainder is a judged request

The pinning test for the retry loop, stated on the checker as Rocq
states it.  The concrete cases above pin one remainder value and one
request value; this pins that no value in between them, or beyond,
reopens the hole. -/

/-- UNIVERSALLY QUANTIFIED.  EVERY remainder this checker may accept is a
request the same checker JUDGES: given the destination the loop reuses,
no `rem` that `nanosleep_rem_ok_b` admits can make the next call decline.
The two hypotheses are the loop's own —
`while (nanosleep(&ts, &ts) == -1 && errno == EINTR);` passes the
remainder back as the request through the same pointer, so the
destination it hands the second call is one the first call already found
writable; the disjunction covers the other spelling, where `rmtp` is NULL
and no remainder is reported at all.  THE STATEMENT IS A NON-DECLINE, not
an acceptance, on purpose: it holds for EVERY effect, and most effects at
a given input are rejected.  What it rules out is the third verdict, the
one that escapes through the equivalence's unmodeled arm and takes the
whole program's `modeled` status with it.  The kernel half of the claim
is that `SYSCALL_DEFINE2(nanosleep)` answers every readable request —
with -EINVAL or a sleep — and `do_nanosleep` every armed one,
so the two declines are the checker's own bounds and both are excluded
by the hypotheses.  The proof is the checker's case analysis: the
remainder's four conjuncts imply `timespec_valid_b`, and after that every
arm of the effect `match` is `CheckOk` or `CheckReject`.
kernel: kernel/time/hrtimer.c:nanosleep,do_nanosleep@v6.18.46 -/
theorem nanosleep_admissible_remainder_is_a_judged_request
    (i : SyscallInput) (rqtp rmtp : word) (eff : SyscallEffect) (m : Model) (rem : List byte)
    (hread : read_bytes_map i.in_mem rqtp (Z_to_bv 64 16) = some rem)
    (hrem : nanosleep_rem_ok_b rem = true)
    (hdest : w_is0 rmtp = true ∨ read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) ≠ none) :
    check_nanosleep i rqtp rmtp eff m ≠ CheckUnmodeled := by
  have hvalid : timespec_valid_b rem = true := by
    have h63 : (2 : Int) ^ 63 = 9223372036854775808 := by decide
    have henv : CLOCK_NS_ENVELOPE = 9223372036854775808 := by decide
    have hnn := bytes_le_to_Z_nonneg' (rem.drop 8)
    -- `decide … = true` is read to its proposition BEFORE the fields are
    -- unfolded, as the spec-level twin does it: unfolding first changes the
    -- proposition under `decide` while its instance still names the folded
    -- field, and `decide_eq_true_eq` then no longer matches.
    simp only [nanosleep_rem_ok_b, Bool.and_eq_true, decide_eq_true_eq] at hrem
    simp only [timespec_valid_b, Bool.and_eq_true, decide_eq_true_eq]
    unfold timespec_ns tv_sec_of tv_frac_of at hrem
    unfold tv_sec_of tv_frac_of
    omega
  intro h
  unfold check_nanosleep at h
  simp only [hread, hvalid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hw : w_is0 rmtp with
  | true =>
    simp only [hw, ↓reduceIte, check_copyins] at h
    split at h
    · split at h
      · split at h
        · cases h
        · split at h <;> cases h
      · cases h
    · cases h
  | false =>
    cases hr : read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) with
    | none =>
      rcases hdest with hz | hd
      · rw [hz] at hw
        cases hw
      · exact hd hr
    | some ws =>
      simp only [hw, Bool.false_eq_true, ↓reduceIte, hr, check_copyins] at h
      split at h
      · split at h
        · split at h <;> cases h
        · split at h <;> cases h
        · cases h
      · cases h

/-! ## The clock near the ceiling

`hrtimer_nanosleep` sets a RELATIVE expiry, and
`__hrtimer_start_range_ns` (kernel/time/hrtimer.c:1204-1295, at :1242-1243, Linux v6.18.46) makes it
absolute with `ktime_add_safe` (kernel/time/hrtimer.c:340-352, Linux v6.18.46), which
replaces an overflowing sum with `ktime_set(KTIME_SEC_MAX, 0)` —
`KTIME_MAX`, by `ktime_set`'s early return — and sleeps to THAT deadline
rather than reporting an error.  So `nanosleep_clock` clamps the deadline
at `KTIME_MAX` and the checker carries no gate on the model's clock. -/

/-- MODEL-INTERNAL STATE, and the whole of what replaced a decline.  A
clock already within a second of the top of `ktime_t`'s range ANSWERS a
one-second sleep, recording the saturated deadline `KTIME_MAX` rather than
a sum the type cannot hold, because that is the deadline `ktime_add_safe`
arms.  The old decline was not merely conservative: the monotonic
`clock_gettime` arm records whatever reading the environment chooses
below 2^63, so one call from the initial model could put `m_clock` here
and the next sleep of one nanosecond declined.  The recorded value is
`2^63 - 1` and not `2^63`: the saturation constant is `KTIME_MAX`, since
`ktime_set` tests `secs >= KTIME_SEC_MAX` and fires on the very value
`ktime_add_safe` passes it — the nanosecond that keeps `m_clock` inside
the band the monotonic read answers in.
kernel: kernel/time/hrtimer.c:__hrtimer_start_range_ns,ktime_add_safe; include/linux/ktime.h:ktime_set@v6.18.46 -/
theorem nanosleep_clock_near_envelope_clamps :
    nanosleep_check 0 ts_1s (with_copyins [(8192, 16)] (mkEffect 0 [] []))
      (clock_model (2 ^ 63 - 1000000000)) = CheckOk (clock_model (2 ^ 63 - 1)) [] := by
  nanosleep_check_norm

/-- MODEL-INTERNAL STATE — the control for the case above.  The same
one-second sleep against a clock two seconds below the ceiling does NOT
clamp: the sum fits, `ktime_add_safe` returns it unchanged, and the
recorded value is the plain `prev + request`.  Without this pair a
`nanosleep_clock` that clamped everything to `KTIME_MAX` would satisfy the
case above.
kernel: kernel/time/hrtimer.c:__hrtimer_start_range_ns,ktime_add_safe; include/linux/ktime.h:ktime_set@v6.18.46 -/
theorem nanosleep_clock_below_the_ceiling_does_not_clamp :
    nanosleep_check 0 ts_1s (with_copyins [(8192, 16)] (mkEffect 0 [] []))
      (clock_model (2 ^ 63 - 2000000000)) = CheckOk (clock_model (2 ^ 63 - 1000000000)) [] := by
  nanosleep_check_norm

/-- MODEL-INTERNAL STATE, and the case that pins WHERE the remainder is
subtracted.  A saturating one-second sleep interrupted with one
microsecond left records `KTIME_MAX - 1000`, not `prev + request -
remainder`: the kernel armed `node.expires` at the saturated deadline and
`hrtimer_expires_remaining` measures the remainder against THAT, so the
wake time is the saturated deadline less the remainder.  A
`nanosleep_clock` that subtracted BEFORE clamping would compute
`min (prev + 10^9 - 1000) KTIME_MAX`, which is `KTIME_MAX` outright, and
one that did not clamp at all would record `2^63 + 999997000`, above the
envelope, where the very next monotonic read declines.
kernel: kernel/time/hrtimer.c:__hrtimer_start_range_ns,ktime_add_safe,do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_saturated_deadline_less_the_remainder :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_1us)] []))
      (clock_model (2 ^ 63 - 2000)) = CheckOk (clock_model (2 ^ 63 - 1001)) [] := by
  nanosleep_check_norm

/-- MODEL-INTERNAL STATE — the `max prev` floor, in its SECOND form.  A
saturating sleep interrupted with a quarter second left leaves
`KTIME_MAX - 250000000`, which is BELOW a clock sitting 1000 ns from the
ceiling; the clock holds where it was rather than stepping back a quarter
second.  Nothing else separates `max prev` from `max 0` applied to the
subtraction: with the clock at 0 the two agree, and only a clock near the
ceiling makes `KTIME_MAX - rem` fall below `prev`.  No kernel writes
this remainder at this clock: `node.expires` is an `s64` that
`ktime_add_safe` caps at `KTIME_MAX`, and `hrtimer_expires_remaining`
subtracts a now that is at least `prev`, so a real remainder here is at
most 999 ns.  The fixture is a lying kernel's answer the spec ADMITS —
`nanosleep_rem_ok_b` judges the remainder alone, never against `prev` —
and what the pin fixes is the floor's arithmetic on it, not a trace.
kernel: kernel/time/hrtimer.c:__hrtimer_start_range_ns,ktime_add_safe,do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_saturated_deadline_never_steps_the_clock_back :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
      (clock_model (2 ^ 63 - 1000)) = CheckOk (clock_model (2 ^ 63 - 1000)) [] := by
  nanosleep_check_norm

/-- MODEL-INTERNAL STATE — the WRITABLE arm's completed sleep from a
nonzero clock, clamped and not.  The four cases above move the clock from
near the ceiling through the NULL arm and the interrupted arm; the
completed sleep at a writable `rmtp` is a third `CheckOk` with its own
`nanosleep_clock` application, and every case on it so far starts at 0,
where `nanosleep_clock prev` and `nanosleep_clock 0` agree.  From two
seconds below the ceiling a one-second sleep records the plain sum; from
one second below it records `KTIME_MAX`, as the NULL arm does.
kernel: kernel/time/hrtimer.c:nanosleep,do_nanosleep,__hrtimer_start_range_ns,ktime_add_safe@v6.18.46 -/
theorem nanosleep_completed_sleep_at_a_writable_rmtp_from_a_nonzero_clock :
    nanosleep_check 4096 ts_1s (with_copyins [(8192, 16)] (mkEffect 0 [] []))
        (clock_model (2 ^ 63 - 2000000000)) = CheckOk (clock_model (2 ^ 63 - 1000000000)) []
      ∧ nanosleep_check 4096 ts_1s (with_copyins [(8192, 16)] (mkEffect 0 [] []))
          (clock_model (2 ^ 63 - 1000000000)) = CheckOk (clock_model (2 ^ 63 - 1)) [] := by
  refine ⟨?_, ?_⟩ <;> nanosleep_check_norm

/-- MODEL-INTERNAL STATE — the two arms that HOLD the clock, from a
nonzero one.  `nanosleep_null_remainder_interruption_holds_the_clock` and
the -EINVAL cases all start at 0, where a checker that RESET the clock
is indistinguishable from one that holds it.  The NULL-`rmtp`
interruption and the -EINVAL answer both hand back the model they were
given: `do_nanosleep` under `TT_NONE` reports nothing to move it by, and
`timespec64_valid`'s refusal never arms a timer.
kernel: kernel/time/hrtimer.c:nanosleep,do_nanosleep; include/linux/time64.h:timespec64_valid; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_holding_arms_hold_a_nonzero_clock :
    nanosleep_check 0 ts_1s (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] []))
        (clock_model (2 ^ 63 - 1000)) = CheckOk (clock_model (2 ^ 63 - 1000)) []
      ∧ nanosleep_check 4096 ts_neg_sec
          (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] []))
          (clock_model (2 ^ 63 - 1000)) = CheckOk (clock_model (2 ^ 63 - 1000)) [] := by
  refine ⟨?_, ?_⟩ <;> nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and the REJECTION the
decline used to cost.  Near the ceiling the old spec answered
`CheckUnmodeled` for EVERY effect, so it refused nothing there: a lying
kernel's impossible answers were declined rather than rejected, and a
decline admits the step under the equivalence's unmodeled escape.  With
the clamp in place the same -EINTR reporting a remainder of exactly zero
is REFUSED at a clock near the ceiling as it is at a clock of 0, because
`do_nanosleep` returns 0 for a non-positive remainder wherever the clock
stands.
kernel: kernel/time/hrtimer.c:do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_near_the_ceiling_zero_remainder_rejected :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
      (clock_model (2 ^ 63 - 1000000000)) = CheckReject := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the mirror, near the
ceiling.  A completed sleep that also writes a remainder is refused there
too: `do_nanosleep` reaches `nanosleep_copyout` only on the path that
returns the restart code, never on the one that returns 0.  Together the
two pin that the band the gate used to swallow is now fully judged.
kernel: kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout@v6.18.46 -/
theorem nanosleep_near_the_ceiling_completed_sleep_with_a_remainder_rejected :
    nanosleep_check 4096 ts_1s (with_copyins [(8192, 16)] (mkEffect 0 [(4096, ts_250ms)] []))
      (clock_model (2 ^ 63 - 1000000000)) = CheckReject := by
  nanosleep_check_norm

/-! ## What the remainder must be

`do_nanosleep` computes `hrtimer_expires_remaining` (include/linux/hrtimer.h:159-162, Linux v6.18.46)
and returns 0, writing nothing, when it is not positive; a positive one
goes through `ktime_to_timespec64` (include/linux/ktime.h:75, Linux v6.18.46),
which is `ns_to_timespec64` (kernel/time/time.c:523-542, Linux v6.18.46) and
normalises `tv_nsec` into `[0, 10^9)`, then to `rmtp` whole through
`nanosleep_copyout` (kernel/time/hrtimer.c:2093-2110, Linux v6.18.46) and
`put_timespec64` (kernel/time/time.c:903-912, Linux v6.18.46).  Every conjunct of
`nanosleep_rem_ok_b` is one of those facts, and each pin below trips one
conjunct alone — except `ts_neg_nsec` as a remainder, whose `tv_nsec` of
2^64 - 1 fails the normalisation conjunct and the envelope at once; it is
kept because the normalisation conjunct is the one it is there for. -/

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  An -EINTR reporting a
remainder of exactly zero is REFUSED: `do_nanosleep` returns 0 having
written nothing when what is left is at or below zero — the deadline has
passed, so the call is a completed sleep and is reported as one.  A
remainder of `{0, 0}` is a shape no kernel produces, and
`nanosleep_rem_ok_b`'s strict positivity is what refuses it.
kernel: kernel/time/hrtimer.c:do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_zero_remainder_rejected :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-- MODEL-INTERNAL STATE — the smallest remainder the kernel can report.
One nanosecond left is a positive `hrtimer_expires_remaining`, so
`do_nanosleep` writes it, and the clock advances by the request less that
nanosecond.  This is the boundary the case above sits on the other side
of: a strict positivity spelled `<=` would refuse this one too.
kernel: kernel/time/hrtimer.c:do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_one_nanosecond_remainder_admitted :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_1ns)] []))
      (clock_model 0) = CheckOk (clock_model 999999999) [] := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the remainder's
ENVELOPE conjunct, which nothing else reaches.  A remainder of
9223372037 seconds is normalized, sixteen bytes long and strictly
positive, so it fails `nanosleep_rem_ok_b`'s fourth conjunct ALONE.  The
kernel cannot report it: `hrtimer_expires_remaining` is a `ktime_t`
difference, so a remainder is at most `KTIME_MAX` nanoseconds, under the
envelope.  No mutation can spell this — the write operators build a
prefix of the real bytes, one uniform byte, or filler, and to stay under
the envelope `tv_sec` must decode to 0, which forces all sixteen bytes to
zero and trips strict positivity instead.
kernel: kernel/time/hrtimer.c:do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_remainder_past_the_envelope_rejected :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_over_envelope)] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-- THE ENVELOPE CONJUNCT'S BOUNDARY, on the admitted side.  `KTIME_MAX`
nanoseconds — 9223372036 s and 854775807 ns — is the LARGEST remainder
`nanosleep_rem_ok_b` admits, and the largest `hrtimer_expires_remaining`
can hold.  The request here is a microsecond, so the difference is 292
years negative and `max prev` holds the clock at 0.  The probe
`testing/syscall-check/tests/nanosleep_spec.c` smuggles these bytes onto
a real interrupted sleep and asserts the same acceptance against a kernel
trace; the pin is kept here as well because the harness cannot run
without the pinned VM.
kernel: kernel/time/hrtimer.c:do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_remainder_of_exactly_ktime_max_admitted :
    nanosleep_check 4096 ts_1us
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_ktime_max)] []))
      (clock_model 0) = CheckOk (clock_model 0) [] := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — ONE NANOSECOND further.
9223372036 s and 854775808 ns is 2^63 exactly, which is `CLOCK_NS_ENVELOPE`
and not below it, and one more than any `ktime_t` holds, so the fourth
conjunct's strict `<` refuses it while the other three still pass.
Without this twin the case above would be satisfied by a bound of `≤` as
happily as by `<`.
kernel: kernel/time/hrtimer.c:do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_remainder_of_exactly_the_envelope_rejected :
    nanosleep_check 4096 ts_1us
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_at_envelope)] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the remainder's LENGTH
conjunct, on its own.  Eight bytes decoding to `tv_sec = 1`: the reading
is normalized and `timespec_ns` is 10^9, positive and far under the
envelope, so only the length is wrong.  `put_timespec64`'s `copy_to_user`
may leave a prefix of the sixteen-byte `struct __kernel_timespec` behind
when it faults partway, but that short copy is the -EFAULT of
`nanosleep_copyout`, which reaches the program in place of -EINTR and
which this checker declines at an unwritable `rmtp` before reading any
effect; at a wholly writable one the copy is whole.  So no -EINTR
carries a truncated remainder.  It is also the one a
`trunc-writes:8` mutation cannot pin, because truncating a real remainder
whose seconds are zero gives eight zero bytes, which fail strict
positivity first.
kernel: kernel/time/time.c:put_timespec64; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_half_a_remainder_rejected :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_half)] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the other side of the
width: a seventeen-byte remainder is refused as the eight-byte one is.
`put_timespec64` copies `sizeof(struct __kernel_timespec)`, sixteen
bytes, and nothing past them, so the length conjunct of
`nanosleep_rem_ok_b` is an equality and not a lower bound; this is the
pin that separates the two.
kernel: kernel/time/time.c:put_timespec64; kernel/time/hrtimer.c:nanosleep_copyout; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_seventeen_byte_remainder_rejected :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms ++ [0])] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-- The remainder's `tv_nsec` at 999999999, the accepting side of the
normalisation conjunct whose refusing side the case below pins: one
second requested with a nanosecond short of a second left is one
nanosecond elapsed.  `ns_to_timespec64` writes a `tv_nsec` strictly under
`NSEC_PER_SEC`, so this is the largest fraction a kernel remainder
carries.
kernel: kernel/time/time.c:ns_to_timespec64,put_timespec64; kernel/time/hrtimer.c:do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_remainder_one_nanosecond_short_of_a_second_admitted :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_1s_minus)] []))
      (clock_model 0) = CheckOk (clock_model 1) [] := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — a remainder with a
NEGATIVE second.  `ns_to_timespec64` of the positive `ktime_t`
`hrtimer_expires_remaining` returns never yields a negative `tv_sec`; the
remainder predicate reads the field unsigned, so `INT64_MIN` seconds is
2^63 whole seconds, past the envelope by a factor of 10^9, and the fourth
conjunct refuses it — `Uapi.timespec_ns`'s reason for reading `tv_sec`
unsigned, pinned where it bites.
kernel: kernel/time/time.c:ns_to_timespec64; kernel/time/hrtimer.c:do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_remainder_with_a_negative_second_rejected :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_neg_sec)] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the remainder's
NORMALISATION conjunct.  `ns_to_timespec64` puts the nanoseconds of a
positive remainder in `[0, 10^9)` by construction (`div_u64_rem` by
`NSEC_PER_SEC`), so a remainder whose `tv_nsec` reads 10^9 exactly
(`ts_denorm`) or 2^64 - 1 (`ts_neg_nsec`) is one `nanosleep_copyout`
never writes, and `nanosleep_rem_ok_b`'s second conjunct refuses both.
kernel: kernel/time/time.c:ns_to_timespec64; kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_unnormalised_remainder_rejected :
    nanosleep_check 4096 ts_1s
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_denorm)] []))
        (clock_model 0) = CheckReject
      ∧ nanosleep_check 4096 ts_1s
          (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_neg_nsec)] []))
          (clock_model 0) = CheckReject := by
  refine ⟨?_, ?_⟩ <;> nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the mirror.  A
completed sleep that ALSO writes a remainder is refused.  `do_nanosleep`
reaches `nanosleep_copyout` only on the interrupted path, so a return of 0
and a write at `rmtp` cannot both happen — within one `do_nanosleep`;
across a transparent restart (`arch_do_signal_or_restart` rewinding to
`restart_syscall`, `hrtimer_nanosleep_restart` then returning 0) the
program does see 0 with `rmtp` written by the first pass, the shape
`linux-process-semantics@ff0313ba4f:bugs/nanosleep-transparent-restart-rejected.md` records and one the
harness's -EINTR-gated capture never hands the checker; admitting the
pair would let a
lying kernel move `m_clock` by the whole request while claiming a
remainder against it.  The remainder written here is a PERFECTLY VALID
one, which is what makes the case attribute: the only thing wrong with
this effect is that a completed sleep carries it, and no mutation can say
that much, since the bytes it can smuggle are not a remainder
`nanosleep_rem_ok_b` would accept.
kernel: kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout@v6.18.46 -/
theorem nanosleep_completed_sleep_with_a_remainder_rejected :
    nanosleep_check 4096 ts_1s (with_copyins [(8192, 16)] (mkEffect 0 [(4096, ts_250ms)] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the interruption that
writes NOTHING at a writable destination.  With a non-NULL `rmtp` the
syscall records `TT_NATIVE`, and on the interrupted path `do_nanosleep`
either returns 0 (remainder not positive) or writes the remainder through
`nanosleep_copyout` before returning the restart code.  There is no path
on which the restart code — the program's -EINTR — comes back with
`rmtp` untouched, and the checker's `[]`-writes arm of the non-NULL case
accepts 0 alone.
kernel: kernel/time/hrtimer.c:nanosleep,do_nanosleep,nanosleep_copyout; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_interruption_without_a_remainder_rejected :
    nanosleep_check 4096 ts_1s (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the interruption that
writes at a NULL destination.  `SYSCALL_DEFINE2(nanosleep)` records
`TT_NONE` for a NULL `rmtp` (kernel/time/hrtimer.c:2201, Linux v6.18.46) and `do_nanosleep`
then skips the copy-out entirely, so an -EINTR carrying a write — at 4096
or anywhere — is a kernel writing where it was given no pointer.  The
NULL arm of the checker takes the `[]`-writes shape alone.
kernel: kernel/time/hrtimer.c:nanosleep,do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_null_rmtp_interruption_with_a_write_rejected :
    nanosleep_check 0 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the remainder at the
WRONG address.  `nanosleep_copyout` writes through
`restart->nanosleep.rmtp`, the pointer the syscall recorded, and nowhere
else; a valid remainder landed at the request's address instead is
refused by the `bv_eqb a rmtp` conjunct alone, since the bytes and the
return word are exactly the accepted interruption's.
kernel: kernel/time/hrtimer.c:nanosleep,nanosleep_copyout; kernel/time/time.c:put_timespec64; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_remainder_at_the_wrong_address_rejected :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(8192, ts_250ms)] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — two remainders.
`do_nanosleep` calls `nanosleep_copyout` once and returns, so an effect
with two writes, both of them the accepted remainder at the accepted
address, is refused by the shape of the `match` and not by any conjunct.
kernel: kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_two_remainders_rejected :
    nanosleep_check 4096 ts_1s
      (with_copyins [(8192, 16)]
        (mkEffect (errno_ret EINTR) [(4096, ts_250ms), (4096, ts_250ms)] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-! ## The return word

`SYSCALL_DEFINE2(nanosleep)` returns exactly one of: -EFAULT from
`get_timespec64`, -EINVAL from `timespec64_valid`, or what
`hrtimer_nanosleep` returns — 0, the restart code the signal path
rewrites to -EINTR, or the -EFAULT `nanosleep_copyout` hands back through
`do_nanosleep` when the remainder's `put_timespec64` fails.  That last
word the checker never judges: an unwritable `rmtp` declines before any
effect is read, so on the arms below `rmtp` is NULL or wholly writable
and -EFAULT is a word no path produces.  The checker admits each of the
others on its own arm and nothing else; these pin that no word crosses to
another arm. -/

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  `do_nanosleep` returns
0 or a negative code, and `hrtimer_nanosleep` passes that through, so a
completed sleep returning 1 is a word no path produces; the checker's
NULL-`rmtp` arm tests `bv_eqb r 0`, then `bv_eqb r (errno_ret EINTR)`,
and rejects what is neither.
kernel: kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep@v6.18.46 -/
theorem nanosleep_completed_sleep_returning_one_rejected :
    nanosleep_check 0 ts_1s (with_copyins [(8192, 16)] (mkEffect 1 [] [])) (clock_model 0)
      = CheckReject := by
  nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  -EFAULT is
`get_timespec64`'s answer to a request that cannot be copied in, and the
request here was read whole — the checker is past its first `match` — so
the word is refused on both the NULL and the writable arm.
kernel: kernel/time/hrtimer.c:nanosleep; kernel/time/time.c:get_timespec64@v6.18.46 -/
theorem nanosleep_efault_on_a_readable_request_rejected :
    nanosleep_check 0 ts_1s (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] []))
        (clock_model 0) = CheckReject
      ∧ nanosleep_check 4096 ts_1s (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] []))
          (clock_model 0) = CheckReject := by
  refine ⟨?_, ?_⟩ <;> nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  -EINVAL is
`timespec64_valid`'s refusal, and one second is a request it accepts, so
the word is refused on a valid request; and -EFAULT on an INVALID one is
refused too, since the request was readable and the -EINVAL arm is
`check_ret_only_copyins` on that one word.
kernel: kernel/time/hrtimer.c:nanosleep; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem nanosleep_wrong_errno_rejected :
    nanosleep_check 4096 ts_1s (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] []))
        (clock_model 0) = CheckReject
      ∧ nanosleep_check 0 ts_1s (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] []))
        (clock_model 0) = CheckReject
      ∧ nanosleep_check 4096 ts_neg_sec
          (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) (clock_model 0)
        = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> nanosleep_check_norm

/-- THE INTERRUPTION IS -EINTR AND NOTHING ELSE.  The word `do_nanosleep`
actually returns is `-ERESTART_RESTARTBLOCK`, 516 (include/linux/errno.h,
Linux v6.18.46: "These should never be seen by user programs"), which
`arch_do_signal_or_restart` rewrites to -EINTR when a handler runs and
turns into a re-entry through `restart_syscall` — `a0` restored to the
request pointer, `a7` to `__NR_restart_syscall` — when none does.  The
checker admits -EINTR alone: 516 itself and the restored request pointer
that a transparent restart shows at the boundary are refused, on the
NULL arm and beside a valid remainder alike.  The cases above offer other
words on the NULL arm alone (1, -EFAULT, -EINVAL); these add the two words
a restart shows, and offer them on the writable arm too, beside a
remainder the checker would otherwise accept.  The transparent restart's rejection is the case
`linux-process-semantics@ff0313ba4f:bugs/nanosleep-transparent-restart-rejected.md` records, and these are
the pins that flip when the arm it proposes lands.
kernel: kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_only_eintr_is_the_interruption :
    nanosleep_check 0 ts_1s (with_copyins [(8192, 16)] (mkEffect (errno_ret 516) [] []))
        (clock_model 0) = CheckReject
      ∧ nanosleep_check 0 ts_1s (with_copyins [(8192, 16)] (mkEffect 8192 [] []))
          (clock_model 0) = CheckReject
      ∧ nanosleep_check 4096 ts_1s
          (with_copyins [(8192, 16)] (mkEffect (errno_ret 516) [(4096, ts_250ms)] []))
          (clock_model 0) = CheckReject
      ∧ nanosleep_check 4096 ts_1s
          (with_copyins [(8192, 16)] (mkEffect 8192 [(4096, ts_250ms)] []))
          (clock_model 0) = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nanosleep_check_norm

/-- And -EAGAIN, the would-block answer of the other blocking calls and
no interruption at all, is refused on the NULL arm: no function on the
nanosleep path names it,
which is exactly why no kernel line can be cited for it — the claim is
the arm's own, that its word test compares with `errno_ret EINTR` and
nothing else, and a checker widened to accept -EAGAIN beside it passed
every pin in this file before this one.
model: the NULL-`rmtp` arm's return-word test, offered a word no function on the path produces -/
theorem nanosleep_eagain_is_not_the_interruption :
    nanosleep_check 0 ts_1s (with_copyins [(8192, 16)] (mkEffect (errno_ret EAGAIN) [] []))
      (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-! ## The ledger

`get_timespec64` (kernel/time/time.c:872-892, Linux v6.18.46) copies the sixteen bytes at
`rqtp` in before anything is decided, so every outcome `nanosleep` can
reach has already consumed them.  The spec records that read with
`record_copyins`, and the checker demands it of every accepted effect
through `check_copyins` and `check_ret_only_copyins`. -/

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the LEDGER, which every
case above carries and none of them pins.  An effect that is otherwise the
accepted completed sleep, but claims to have decided without reading the
request, describes a kernel that cannot exist, and is refused.  Without
this case the `record_copyins` in `nanosleep_spec` would be unfalsifiable
from the example side.
kernel: kernel/time/hrtimer.c:nanosleep; kernel/time/time.c:get_timespec64@v6.18.46 -/
theorem nanosleep_missing_copyin_rejected :
    nanosleep_check 0 ts_1s (mkEffect 0 [] []) (clock_model 0) = CheckReject := by
  nanosleep_check_norm

/-- And the ledger has to name the REQUEST.  Sixteen bytes recorded at
`rmtp` — the remainder destination, which `nanosleep` writes and never
reads — is the right width at the wrong address, and is refused for that
alone.  This is what separates an acceptor that compares the whole range
from one that only counts bytes.
kernel: kernel/time/hrtimer.c:nanosleep; kernel/time/time.c:get_timespec64@v6.18.46 -/
theorem nanosleep_copyin_at_the_wrong_pointer_rejected :
    nanosleep_check 4096 ts_1s (with_copyins [(4096, 16)] (mkEffect 0 [] [])) (clock_model 0)
      = CheckReject := by
  nanosleep_check_norm

/-- And the ledger has to be the WHOLE request, ONCE.  `get_timespec64`
copies `sizeof(struct __kernel_timespec)` — sixteen bytes — in one
`copy_from_user`, so eight bytes at the right address is the width of a
kernel that does not exist, and the same sixteen recorded twice is a
second read the syscall never makes.  `access_ranges_eqb` compares the
lists whole.
kernel: kernel/time/hrtimer.c:nanosleep; kernel/time/time.c:get_timespec64@v6.18.46 -/
theorem nanosleep_ledger_of_the_wrong_shape_rejected :
    nanosleep_check 0 ts_1s (with_copyins [(8192, 8)] (mkEffect 0 [] [])) (clock_model 0)
        = CheckReject
      ∧ nanosleep_check 0 ts_1s (with_copyins [(8192, 16), (8192, 16)] (mkEffect 0 [] []))
          (clock_model 0) = CheckReject := by
  refine ⟨?_, ?_⟩ <;> nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the fields the accepted
shape leaves EMPTY.  The only user memory the sleep touches is `rmtp`,
through `nanosleep_copyout`; it zeroes nothing, unmaps nothing and copies
nothing, so a completed sleep smuggling a zero-fill, an unmapping or a
copy beside its correct ledger is refused by the `match`'s shape, whatever
the return word.  Written out as `SyscallEffect.mkEffectU` because
`mkEffect` cannot spell those fields.
kernel: kernel/time/hrtimer.c:nanosleep,do_nanosleep,nanosleep_copyout@v6.18.46 -/
theorem nanosleep_smuggled_effects_rejected :
    nanosleep_check 0 ts_1s (SyscallEffect.mkEffectU 0 [] [(4096, 16)] [] [] [(8192, 16)])
        (clock_model 0) = CheckReject
      ∧ nanosleep_check 0 ts_1s (SyscallEffect.mkEffectU 0 [] [] [(4096, 4096)] [] [(8192, 16)])
          (clock_model 0) = CheckReject
      ∧ nanosleep_check 0 ts_1s
          (SyscallEffect.mkEffectU 0 [] [] [] [MemCopy.mkCopy 8192 4096 16] [(8192, 16)])
          (clock_model 0) = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the same three fields on
the two arms a writable `rmtp` selects, which are a second `match` and
so a second set of empty patterns: the completed sleep that writes
nothing, and the interruption that writes its one remainder.  The one
above pins the NULL arm's patterns; a checker that let a zero-fill, an
unmapping or a copy through on either of these two would pass it.
kernel: kernel/time/hrtimer.c:nanosleep,do_nanosleep,nanosleep_copyout; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_smuggled_effects_at_a_writable_rmtp_rejected :
    nanosleep_check 4096 ts_1s (SyscallEffect.mkEffectU 0 [] [(4096, 16)] [] [] [(8192, 16)])
        (clock_model 0) = CheckReject
      ∧ nanosleep_check 4096 ts_1s
          (SyscallEffect.mkEffectU 0 [] [] [(4096, 4096)] [] [(8192, 16)])
          (clock_model 0) = CheckReject
      ∧ nanosleep_check 4096 ts_1s
          (SyscallEffect.mkEffectU 0 [] [] [] [MemCopy.mkCopy 8192 4096 16] [(8192, 16)])
          (clock_model 0) = CheckReject
      ∧ nanosleep_check 4096 ts_1s
          (SyscallEffect.mkEffectU (errno_ret EINTR) [(4096, ts_250ms)] [(4096, 16)] [] []
            [(8192, 16)])
          (clock_model 0) = CheckReject
      ∧ nanosleep_check 4096 ts_1s
          (SyscallEffect.mkEffectU (errno_ret EINTR) [(4096, ts_250ms)] [] [(4096, 4096)] []
            [(8192, 16)])
          (clock_model 0) = CheckReject
      ∧ nanosleep_check 4096 ts_1s
          (SyscallEffect.mkEffectU (errno_ret EINTR) [(4096, ts_250ms)] [] []
            [MemCopy.mkCopy 8192 4096 16] [(8192, 16)])
          (clock_model 0) = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the ledger on the
INTERRUPTED arms.  The three cases above refuse a missing or wrong ledger
beside a completed sleep; every -EINTR case in this file carries the
right one, so a checker that demanded the copy-in of the completed sleep
alone — `check_copyins` moved inside the `bv_eqb r 0` branch — would pass
all of them.  `get_timespec64` runs before the timer is armed, so the
interrupted call read the request exactly as the completed one did: an
-EINTR with no ledger is refused at a NULL `rmtp`, and with no ledger or
the destination's address in it beside a valid remainder.
kernel: kernel/time/hrtimer.c:nanosleep,do_nanosleep; kernel/time/time.c:get_timespec64; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_interruption_without_the_copyin_rejected :
    nanosleep_check 0 ts_1s (mkEffect (errno_ret EINTR) [] []) (clock_model 0) = CheckReject
      ∧ nanosleep_check 4096 ts_1s (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] [])
          (clock_model 0) = CheckReject
      ∧ nanosleep_check 4096 ts_1s
          (with_copyins [(4096, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
          (clock_model 0) = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the NULL arm's empty
fields under BOTH words.  One `match` alternative serves the completed
sleep and the interruption at a NULL `rmtp`, so the smuggled zero-fill
above (refused beside 0) and the write at 4096 (refused beside -EINTR)
each pin the pattern under one word only; a checker with a second
alternative freeing a field under the other word would pass both.  A
completed sleep that writes at a NULL `rmtp` and an interruption that
zero-fills are refused too.
kernel: kernel/time/hrtimer.c:nanosleep,do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_null_arm_shape_holds_under_both_words :
    nanosleep_check 0 ts_1s (with_copyins [(8192, 16)] (mkEffect 0 [(4096, ts_250ms)] []))
        (clock_model 0) = CheckReject
      ∧ nanosleep_check 0 ts_1s
          (SyscallEffect.mkEffectU (errno_ret EINTR) [] [(4096, 16)] [] [] [(8192, 16)])
          (clock_model 0) = CheckReject := by
  refine ⟨?_, ?_⟩ <;> nanosleep_check_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the -EINVAL arm owes
the ledger too, and nothing else.  `timespec64_valid` runs on the struct
`get_timespec64` already copied in, so an -EINVAL that claims not to have
read the request is refused, and an -EINVAL carrying a zero-fill beside
its ledger is refused as well, and so is one carrying a WRITE at `rmtp`,
the lie with a kernel face — a remainder reported for a sleep that was
never armed: `check_ret_only_copyins` clears the ledger and demands that
nothing else remains beside the word.
kernel: kernel/time/hrtimer.c:nanosleep; kernel/time/time.c:get_timespec64@v6.18.46 -/
theorem nanosleep_einval_with_the_wrong_ledger_rejected :
    nanosleep_check 4096 ts_neg_sec (mkEffect (errno_ret EINVAL) [] []) (clock_model 0)
        = CheckReject
      ∧ nanosleep_check 4096 ts_neg_sec
          (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [(4096, 16)] [] [] [(8192, 16)])
          (clock_model 0) = CheckReject
      ∧ nanosleep_check 4096 ts_neg_sec
          (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [(4096, ts_250ms)] []))
          (clock_model 0) = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> nanosleep_check_norm

/-- ORDER IS BEHAVIOUR.  `timespec64_valid` runs before the remainder
pointer is so much as recorded, so an invalid request is -EINVAL whatever
`rmtp` is: NULL, or 4104, which straddles into the unwritable page and
would make an otherwise valid call decline.  The checker tests validity
before it reads `in_wmem`, and this pin is what a checker that read the
destination first would fail.
kernel: kernel/time/hrtimer.c:nanosleep; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem nanosleep_einval_precedes_the_destination :
    nanosleep_check 0 ts_neg_sec (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] []))
        (clock_model 0) = CheckOk (clock_model 0) []
      ∧ nanosleep_check 4104 ts_neg_sec
          (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) (clock_model 0)
        = CheckOk (clock_model 0) [] := by
  refine ⟨?_, ?_⟩ <;> nanosleep_check_norm

/-! ## The declines

Two, and both are the model's bounds rather than empty intersections:
Linux has a definite answer at each, and the checker's `CheckUnmodeled`
is the declared narrowing `nanosleep_spec`'s header argues.  Each is
reached before any effect is inspected, which is what
`check_nanosleep_complete_unmodeled` requires, so the pins here quantify
over the effect and the model. -/

/-- A request straddling into unreadable memory — eight readable bytes at
8192 and nothing past them — declines, whatever `rmtp`, the effect and
the model.  A COVERAGE GAP, NOT AN EMPTY INTERSECTION: Linux's answer is
the definite -EFAULT of `get_timespec64`, whose `copy_from_user` of the
whole struct fails when any byte of it does, with the user memory
untouched; the decline is the definition's declared narrowing.  This is
one of the pins the header says close by `conv => lhs; whnf`.
kernel: kernel/time/time.c:get_timespec64; kernel/time/hrtimer.c:nanosleep@v6.18.46 -/
theorem nanosleep_unreadable_request_declines (eff : SyscallEffect) (m : Model) :
    nanosleep_check 0 ts_half eff m = CheckUnmodeled
      ∧ nanosleep_check 4096 ts_half eff m = CheckUnmodeled :=
  ⟨by conv => lhs; whnf, by conv => lhs; whnf⟩

/-- And in particular the -EFAULT Linux really answers there declines
rather than being accepted: the coverage gap is a gap, and an acceptor
that answered `CheckOk` here would be claiming a copy-in ledger for a
failed copy that the spec never lands.
kernel: kernel/time/time.c:get_timespec64; kernel/time/hrtimer.c:nanosleep@v6.18.46 -/
theorem nanosleep_unreadable_request_efault_declines :
    nanosleep_check 0 ts_half (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] []))
      (clock_model 0) = CheckUnmodeled :=
  (nanosleep_unreadable_request_declines _ _).1

/-- Fifteen readable bytes at 8192: one second's request with its last
byte cut off, the width a fifteen-byte read gate would accept. -/
def ts_15 : List byte := [1, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0]

/-- `ts_15` misses exactly one byte of the struct; a fixture that lost a
second byte would still close the decline below while the sentence
"one byte" went silently wrong.
model: the fixture's length at a numeral. -/
example : ts_15.length = 15 := by decide

/-- The LAST byte of the request alone decides the decline.  `get_timespec64`
copies `sizeof(kts)`, sixteen bytes, in one `copy_from_user`, which fails
when any byte does; `ts_half` misses eight of them, this misses one, and
the checker declines both — a request gate one byte narrower than the
struct would accept this one.  Closes as `ts_half` does, by evaluating the
read.
kernel: kernel/time/time.c:get_timespec64; kernel/time/hrtimer.c:nanosleep@v6.18.46 -/
theorem nanosleep_request_unreadable_in_its_last_byte_declines (eff : SyscallEffect) (m : Model) :
    nanosleep_check 0 ts_15 eff m = CheckUnmodeled
      ∧ nanosleep_check 4096 ts_15 eff m = CheckUnmodeled :=
  ⟨by conv => lhs; whnf, by conv => lhs; whnf⟩

/-- A NULL request declines, whatever `rmtp`, the effect and the model:
the request REGISTER is 0 while one second stays readable at 8192, where
nothing reads it.  Linux's answer is the definite -EFAULT of
`get_timespec64`, whose `copy_from_user` of the sixteen bytes at address
0 fails whole; the checker's first `match` finds no byte at 0 and
declines before any gate — the same declared narrowing as the straddling
requests above, and stated on `check_nanosleep` itself because the alias
fixes the request at 8192.  Closes by evaluating the read, as `ts_half`
does.
kernel: kernel/time/time.c:get_timespec64; kernel/time/hrtimer.c:nanosleep@v6.18.46 -/
theorem nanosleep_null_request_declines (eff : SyscallEffect) (m : Model) :
    check_nanosleep (nanosleep_input 0 ts_1s) 0 0 eff m = CheckUnmodeled
      ∧ check_nanosleep (nanosleep_input 4096 ts_1s) 0 4096 eff m = CheckUnmodeled :=
  ⟨by conv => lhs; whnf, by conv => lhs; whnf⟩

/-- A valid request with a remainder destination that straddles into an
unwritable page declines, whatever the effect and the model.  Linux
answers here too — `put_timespec64` fails with -EFAULT inside
`nanosleep_copyout` on the interrupted path, and a completed sleep never
touches `rmtp` at all — so this is the second declared narrowing, and
the second of the two bounds the spec-level header names.
kernel: kernel/time/time.c:put_timespec64; kernel/time/hrtimer.c:nanosleep_copyout@v6.18.46 -/
theorem nanosleep_unwritable_rmtp_declines (eff : SyscallEffect) (m : Model) :
    nanosleep_check 4104 ts_1s eff m = CheckUnmodeled := by
  nanosleep_check_norm

/-- The LAST byte of the destination alone.  `rmtp` at 4097 puts bytes
4097..4112 under the sixteen-byte write, and 4112 is the first `wmem_ts`
does not cover: `put_timespec64` copies `sizeof(struct __kernel_timespec)`
in one `copy_to_user`, which fails when any byte does, so the call
declines where a fifteen-byte gate would accept it.  4104 above misses
eight bytes; this misses one.
kernel: kernel/time/time.c:put_timespec64; kernel/time/hrtimer.c:nanosleep_copyout@v6.18.46 -/
theorem nanosleep_rmtp_unwritable_in_its_last_byte_declines (eff : SyscallEffect) (m : Model) :
    nanosleep_check 4097 ts_1s eff m = CheckUnmodeled := by
  nanosleep_check_norm

/-- The destination is judged in the WRITABLE view and nowhere else.
`rmtp` at 8192 — where the request is readable and nothing is writable in
this fixture, `rlim_out` covering `[4096, 4112)` alone — declines as 4104
does.  The spelling is `nanosleep(&ts, &ts)`, the retry loop's own, but
the decline is the FIXTURE's and not the aliasing's: a real caller owns
`ts`, `put_timespec64` writes it without a fault, and the probe's `alias`
case conforms (`testing/syscall-check/tests/nanosleep_spec.c`).  What the
pin fixes is which view the destination is looked up in: a checker that
consulted `in_mem` beside `in_wmem` for it would answer this call, and
every other fixture keeps the two views disjoint, so this is the one pin
that separates that widening from the checker.
kernel: kernel/time/time.c:put_timespec64; kernel/time/hrtimer.c:nanosleep_copyout@v6.18.46 -/
theorem nanosleep_aliased_destination_declines (eff : SyscallEffect) (m : Model) :
    nanosleep_check 8192 ts_1s eff m = CheckUnmodeled := by
  nanosleep_check_norm

/-- The sharp edge of that decline: the completed sleep, which Linux
serves at an unwritable `rmtp` without a fault since `do_nanosleep`
returns 0 before any copy-out, declines all the same.  The checker reads
the destination before it looks at the effect, so an answer it could
have given is one it declines to give; this is the coverage cost the
`unmodeled` arm of `nanosleep_spec` pays for deciding the destination
once rather than per outcome.
kernel: kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep@v6.18.46 -/
theorem nanosleep_unwritable_rmtp_completed_sleep_declines :
    nanosleep_check 4104 ts_1s (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 0)
      = CheckUnmodeled :=
  nanosleep_unwritable_rmtp_declines _ _

/-! ## The witness, evaluated

`nanosleep_witness_ok` proves the witness is an outcome the spec admits
on every input and model.  These read off WHICH outcome it is on the
fixtures, so a reader can see the receptiveness obligation's content
rather than its type: the completed sleep with its ledger and the clock
carried forward, -EINVAL where the request is invalid, and a decline
exactly where the checker declines. -/

/-- On a readable, valid request the witness offers the completed sleep:
the ledger, no writes, return 0, and the clock advanced by the request.
It offers the same at a writable `rmtp`, since a completed sleep writes
no remainder.
model: `nanosleep_witness` on the one-second fixtures, NULL and writable `rmtp` -/
theorem witness_completed_sleep_advances_the_clock :
    nanosleep_offer 0 ts_1s (clock_model 0)
        = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 1000000000) []
      ∧ nanosleep_offer 4096 ts_1s (clock_model 0)
        = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 1000000000) [] := by
  refine ⟨?_, ?_⟩ <;> nanosleep_offer_norm

/-- At the ceiling the witness's completed sleep carries the clock to
`KTIME_MAX`, the deadline `ktime_set` saturates to: the offered outcome
is the one `nanosleep_request_at_the_ceiling_sleeps_to_ktime_max` accepts,
where the kernel argument stands.
model: `nanosleep_witness` on the ceiling request at a NULL `rmtp` -/
theorem witness_at_the_ceiling_sleeps_to_ktime_max :
    nanosleep_offer 0 ts_ceiling (clock_model 0)
      = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model (2 ^ 63 - 1)) [] := by
  nanosleep_offer_norm

/-- On the request `timespec64_valid` refuses the witness offers -EINVAL
with the ledger and nothing else, the model untouched — the outcome
`nanosleep_request_at_two_to_the_63_is_einval` accepts, where the kernel
argument stands.
model: `nanosleep_witness` on the invalid request at a writable `rmtp` -/
theorem witness_invalid_request_is_einval :
    nanosleep_offer 4096 ts_neg_sec (clock_model 0)
      = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) (clock_model 0) [] := by
  nanosleep_offer_norm

/-- And it offers -EINVAL BEFORE it looks at the destination: on the
invalid request at 4104, where a valid one would make it decline, the
witness exhibits the -EINVAL outcome `nanosleep_einval_precedes_the_destination`
accepts, in the order that pin argues from `SYSCALL_DEFINE2(nanosleep)`.
model: `nanosleep_witness` on the invalid request at 4104 -/
theorem witness_einval_precedes_the_destination :
    nanosleep_offer 4104 ts_neg_sec (clock_model 0)
      = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) (clock_model 0) [] := by
  nanosleep_offer_norm

/-- The witness declines exactly where the checker does: an unreadable
request, and a valid request at an unwritable `rmtp`.  The first closes
by `conv => lhs; whnf` for the reason the header gives; the second is
the same shape and closes the same way.
model: `nanosleep_witness` on the two declining fixtures -/
theorem witness_declines_where_the_checker_declines :
    nanosleep_offer 0 ts_half (clock_model 0) = Unmodeled
      ∧ nanosleep_offer 4104 ts_1s (clock_model 0) = Unmodeled :=
  ⟨by conv => lhs; whnf, by conv => lhs; whnf⟩

/-- And the checker accepts what the witness offers, on the fixture where
the witness advances the clock: the concrete face of `nanosleep_witness_ok`.
The first half is `nanosleep_completed_sleep_advances_the_clock`'s kernel
claim — a timer that fired carried the clock by the whole request —
restated beside the witness that relies on it.
kernel: kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep@v6.18.46 -/
theorem checker_accepts_the_witness :
    (nanosleep_check 0 ts_1s (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 0)
        = CheckOk (clock_model 1000000000) []
      ∧ nanosleep_offer 0 ts_1s (clock_model 0)
        = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 1000000000) [])
    ∧ (nanosleep_check 4096 ts_1s (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 0)
        = CheckOk (clock_model 1000000000) []
      ∧ nanosleep_offer 4096 ts_1s (clock_model 0)
        = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 1000000000) []) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · nanosleep_check_norm
  · nanosleep_offer_norm
  · nanosleep_check_norm
  · nanosleep_offer_norm

/-! ## The header's claim about the elaborator, pinned

The header says `rfl` exhausts `maxRecDepth` on every concrete case
because of the projection setting `backward.isDefEq.lazyWhnfCore`
selects, and points at the clock_gettime pins for the mechanism.  The
completed sleep, stated under the option that turns the setting off and
closed by plain `rfl`: when this stops elaborating, either the option or
the mechanism has changed, and that header is what to reread. -/

set_option backward.isDefEq.lazyWhnfCore false in
/-- `nanosleep_completed_sleep_advances_the_clock` by plain `rfl`, under
the option that turns the projection setting off.
model: `check_nanosleep` on the one-second fixture, elaborated without `.yesWithDeltaI` -/
example : nanosleep_check 0 ts_1s (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 0)
      = CheckOk (clock_model 1000000000) [] := rfl

-- lean-port sentinel: ticket V-Kernel-Time-Hrtimer appends below this line

section V_Kernel_Time_Hrtimer

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Kernel-Time-Hrtimer — `nanosleep` over the real table

WHAT IS TWINNED HERE.  Every `Example` of
`theories/LinuxProcessSem/Checks/Cases/Kernel/Time/Hrtimer.v` is stated
through `check_syscall`; the sections above state each on the checker,
through `nanosleep_check`.  This section restates each of them through
the Lean `check_syscall`, over `checked_table` itself, at Rocq's input
`nanosleep_input rmtp req` and Rocq's `clock_model`, under its Rocq name
with `_over_the_real_table` after it, K6b's convention for the pins at
which the real table first answers a call.  Each is proved by computing
the dispatch once (`check_syscall_nanosleep_input`) and handing the
checker-level pin above the call it now receives, so the verdicts are
the ones `nanosleep_check_norm` computed there.

WHAT A PIN HERE ADDS to its checker-level twin is the ARM's claim: that
the lookup at 101 finds `arm_nanosleep` rather than the dispatcher's own
decline, and that the arm hands the checker the input with `a0` as the
request and `a1` as the destination.  The accepting twins separate the
two registers: `nanosleep_input` makes the request readable at 8192 and
nothing else readable, so an arm reading the request from `a1` would be
declined where the one-second ones accept
(`the_checker_declines_a_request_read_from_a1`).

POLARITY: `model:` on the table's own contents and on the checker's
answer at an input no arm hands it; `kernel:` on every verdict of the
table and on the witness it offers. -/

/-- The lookup the dispatcher performs on a `nanosleep_input`, computed
once: `in_sysno` is `101` whatever the destination and the request, so
this is `rfl` for every `rmtp` and `req`.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_nanosleep_input (rmtp : word) (req : List byte) :
    lookup_ca checked_table (bv_unsigned (nanosleep_input rmtp req).in_sysno)
      = some arm_nanosleep :=
  lookup_ca_checked_table_nanosleep

/-- What the table hands the checker on a `nanosleep_input`: the call
itself, `a0` and `a1` — the call `nanosleep_check` names.
model: `check_syscall` through `arm_nanosleep`, unfolded; the table's own
contents, not a kernel claim. -/
theorem check_syscall_nanosleep_input (rmtp : word) (req : List byte) (eff : SyscallEffect)
    (m : Model) : check_syscall (nanosleep_input rmtp req) eff m = nanosleep_check rmtp req eff m :=
  check_syscall_of_found _ _ _ _ (lookup_nanosleep_input rmtp req)

/-- The checker's side of the register order: handed the destination
register as the request pointer, at both destinations the accepting
twins below use and with the one-second request, it finds no readable
request there and declines, whatever the effect.  So an arm reading the
two registers the other way round would decline the one-second calls
those twins accept.  Closed by
`conv => lhs; whnf` for the reason the header gives for an unreadable
request.
model: the checker's contract with the arm's reading; no kernel call reads its request from rmtp -/
theorem the_checker_declines_a_request_read_from_a1 (eff : SyscallEffect) (m : Model) :
    check_nanosleep (nanosleep_input 0 ts_1s) 0 8192 eff m = CheckUnmodeled
    ∧ check_nanosleep (nanosleep_input 4096 ts_1s) 4096 8192 eff m = CheckUnmodeled :=
  ⟨by conv => lhs; whnf, by conv => lhs; whnf⟩

/-! ### The Rocq examples, through `check_syscall` -/

/-- Rocq's `nanosleep_completed_sleep_advances_the_clock` through the table:
the verdict, and the kernel argument for it, are the checker-level pin
`nanosleep_completed_sleep_advances_the_clock` above.
kernel: kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep@v6.18.46 -/
theorem nanosleep_completed_sleep_advances_the_clock_over_the_real_table :
    check_syscall (nanosleep_input 0 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 0)
      = CheckOk (clock_model 1000000000) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_completed_sleep_advances_the_clock

/-- Rocq's `nanosleep_null_remainder_interruption_holds_the_clock` through
the table: the verdict, and the kernel argument for it, are the
checker-level pin
`nanosleep_null_remainder_interruption_holds_the_clock` above.
kernel: kernel/time/hrtimer.c:nanosleep,do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_null_remainder_interruption_holds_the_clock_over_the_real_table :
    check_syscall (nanosleep_input 0 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] []))
      (clock_model 0) = CheckOk (clock_model 0) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_null_remainder_interruption_holds_the_clock

/-- Rocq's `nanosleep_interruption_advances_by_the_difference` through the
table: the verdict, and the kernel argument for it, are the
checker-level pin `nanosleep_interruption_advances_by_the_difference`
above.
kernel: kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_interruption_advances_by_the_difference_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
      (clock_model 0) = CheckOk (clock_model 750000000) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_interruption_advances_by_the_difference

/-- Rocq's `nanosleep_remainder_past_the_request_floors_at_zero` through the
table: the verdict, and the kernel argument for it, are the
checker-level pin `nanosleep_remainder_past_the_request_floors_at_zero`
above.
kernel: kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_remainder_past_the_request_floors_at_zero_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_1us)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_51us)] []))
      (clock_model 0) = CheckOk (clock_model 0) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_remainder_past_the_request_floors_at_zero

/-- Rocq's `nanosleep_request_at_the_ceiling_sleeps_to_ktime_max` through
the table: the verdict, and the kernel argument for it, are the
checker-level pin `nanosleep_request_at_the_ceiling_sleeps_to_ktime_max`
above.
kernel: include/linux/ktime.h:ktime_set; kernel/time/hrtimer.c:nanosleep@v6.18.46 -/
theorem nanosleep_request_at_the_ceiling_sleeps_to_ktime_max_over_the_real_table :
    check_syscall (nanosleep_input 0 ts_ceiling)
      (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 0)
      = CheckOk (clock_model (2 ^ 63 - 1)) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_request_at_the_ceiling_sleeps_to_ktime_max

/-- Rocq's `nanosleep_request_below_the_ceiling_converts` through the table:
the verdict, and the kernel argument for it, are the checker-level pin
`nanosleep_request_below_the_ceiling_converts` above.
kernel: include/linux/ktime.h:ktime_set; kernel/time/hrtimer.c:nanosleep@v6.18.46 -/
theorem nanosleep_request_below_the_ceiling_converts_over_the_real_table :
    check_syscall (nanosleep_input 0 ts_below_ceiling)
      (with_copyins [(8192, 16)] (mkEffect 0 [] []))
      (clock_model 0) = CheckOk (clock_model 9223372035000000000) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_request_below_the_ceiling_converts

/-- Rocq's `nanosleep_request_at_the_top_of_the_band_sleeps_to_ktime_max`
through the table: the verdict, and the kernel argument for it, are the
checker-level pin
`nanosleep_request_at_the_top_of_the_band_sleeps_to_ktime_max` above.
kernel: include/linux/ktime.h:ktime_set; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem nanosleep_request_at_the_top_of_the_band_sleeps_to_ktime_max_over_the_real_table :
    check_syscall (nanosleep_input 0 ts_top_of_band) (with_copyins [(8192, 16)] (mkEffect 0 [] []))
      (clock_model 0) = CheckOk (clock_model (2 ^ 63 - 1)) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_request_at_the_top_of_the_band_sleeps_to_ktime_max

/-- Rocq's `nanosleep_at_the_top_of_the_band_zero_remainder_rejected`
through the table: the verdict, and the kernel argument for it, are the
checker-level pin
`nanosleep_at_the_top_of_the_band_zero_remainder_rejected` above.
kernel: kernel/time/hrtimer.c:do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_at_the_top_of_the_band_zero_remainder_rejected_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_top_of_band)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
      (clock_model 0) = CheckReject := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_at_the_top_of_the_band_zero_remainder_rejected

/-- Rocq's `nanosleep_request_at_the_ceiling_interrupted` through the table:
the verdict, and the kernel argument for it, are the checker-level pin
`nanosleep_request_at_the_ceiling_interrupted` above.
kernel: include/linux/ktime.h:ktime_set; kernel/time/hrtimer.c:do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_request_at_the_ceiling_interrupted_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_ceiling)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
      (clock_model 0) = CheckOk (clock_model 9223372036604775807) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_request_at_the_ceiling_interrupted

/-- Rocq's `nanosleep_at_the_ceiling_zero_remainder_rejected` through the
table: the verdict, and the kernel argument for it, are the
checker-level pin `nanosleep_at_the_ceiling_zero_remainder_rejected`
above.
kernel: kernel/time/hrtimer.c:do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_at_the_ceiling_zero_remainder_rejected_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_ceiling)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
      (clock_model 0) = CheckReject := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_at_the_ceiling_zero_remainder_rejected

/-- Rocq's `nanosleep_request_at_two_to_the_63_is_einval` through the table:
the verdict, and the kernel argument for it, are the checker-level pin
`nanosleep_request_at_two_to_the_63_is_einval` above.
kernel: kernel/time/hrtimer.c:nanosleep; include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem nanosleep_request_at_two_to_the_63_is_einval_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_neg_sec)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] []))
      (clock_model 0) = CheckOk (clock_model 0) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_request_at_two_to_the_63_is_einval

/-- Rocq's `nanosleep_remainder_at_the_ceiling_admitted` through the table:
the verdict, and the kernel argument for it, are the checker-level pin
`nanosleep_remainder_at_the_ceiling_admitted` above.
kernel: kernel/time/hrtimer.c:do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_remainder_at_the_ceiling_admitted_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_ceiling)] []))
      (clock_model 0) = CheckOk (clock_model 0) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_remainder_at_the_ceiling_admitted

/-- Rocq's `nanosleep_clock_near_envelope_clamps` through the table: the
verdict, and the kernel argument for it, are the checker-level pin
`nanosleep_clock_near_envelope_clamps` above.
kernel: kernel/time/hrtimer.c:__hrtimer_start_range_ns,ktime_add_safe; include/linux/ktime.h:ktime_set@v6.18.46 -/
theorem nanosleep_clock_near_envelope_clamps_over_the_real_table :
    check_syscall (nanosleep_input 0 ts_1s) (with_copyins [(8192, 16)] (mkEffect 0 [] []))
      (clock_model (2 ^ 63 - 1000000000)) = CheckOk (clock_model (2 ^ 63 - 1)) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_clock_near_envelope_clamps

/-- Rocq's `nanosleep_clock_below_the_ceiling_does_not_clamp` through the
table: the verdict, and the kernel argument for it, are the
checker-level pin `nanosleep_clock_below_the_ceiling_does_not_clamp`
above.
kernel: kernel/time/hrtimer.c:__hrtimer_start_range_ns,ktime_add_safe; include/linux/ktime.h:ktime_set@v6.18.46 -/
theorem nanosleep_clock_below_the_ceiling_does_not_clamp_over_the_real_table :
    check_syscall (nanosleep_input 0 ts_1s) (with_copyins [(8192, 16)] (mkEffect 0 [] []))
      (clock_model (2 ^ 63 - 2000000000)) = CheckOk (clock_model (2 ^ 63 - 1000000000)) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_clock_below_the_ceiling_does_not_clamp

/-- Rocq's `nanosleep_saturated_deadline_less_the_remainder` through the
table: the verdict, and the kernel argument for it, are the
checker-level pin `nanosleep_saturated_deadline_less_the_remainder`
above.
kernel: kernel/time/hrtimer.c:__hrtimer_start_range_ns,ktime_add_safe,do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_saturated_deadline_less_the_remainder_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_1us)] []))
      (clock_model (2 ^ 63 - 2000)) = CheckOk (clock_model (2 ^ 63 - 1001)) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_saturated_deadline_less_the_remainder

/-- Rocq's `nanosleep_saturated_deadline_never_steps_the_clock_back` through
the table: the verdict, and the kernel argument for it, are the
checker-level pin
`nanosleep_saturated_deadline_never_steps_the_clock_back` above.
kernel: kernel/time/hrtimer.c:__hrtimer_start_range_ns,ktime_add_safe,do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_saturated_deadline_never_steps_the_clock_back_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
      (clock_model (2 ^ 63 - 1000)) = CheckOk (clock_model (2 ^ 63 - 1000)) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_saturated_deadline_never_steps_the_clock_back

/-- Rocq's `nanosleep_near_the_ceiling_zero_remainder_rejected` through the
table: the verdict, and the kernel argument for it, are the
checker-level pin `nanosleep_near_the_ceiling_zero_remainder_rejected`
above.
kernel: kernel/time/hrtimer.c:do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_near_the_ceiling_zero_remainder_rejected_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
      (clock_model (2 ^ 63 - 1000000000)) = CheckReject := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_near_the_ceiling_zero_remainder_rejected

/-- Rocq's
`nanosleep_near_the_ceiling_completed_sleep_with_a_remainder_rejected`
through the table: the verdict, and the kernel argument for it, are the
checker-level pin
`nanosleep_near_the_ceiling_completed_sleep_with_a_remainder_rejected`
above.
kernel: kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout@v6.18.46 -/
theorem nanosleep_near_the_ceiling_completed_sleep_with_a_remainder_rejected_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect 0 [(4096, ts_250ms)] []))
      (clock_model (2 ^ 63 - 1000000000)) = CheckReject := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_near_the_ceiling_completed_sleep_with_a_remainder_rejected

/-- Rocq's `nanosleep_zero_remainder_rejected` through the table: the
verdict, and the kernel argument for it, are the checker-level pin
`nanosleep_zero_remainder_rejected` above.
kernel: kernel/time/hrtimer.c:do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_zero_remainder_rejected_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
      (clock_model 0) = CheckReject := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_zero_remainder_rejected

/-- Rocq's `nanosleep_remainder_past_the_envelope_rejected` through the
table: the verdict, and the kernel argument for it, are the
checker-level pin `nanosleep_remainder_past_the_envelope_rejected`
above.
kernel: kernel/time/hrtimer.c:do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_remainder_past_the_envelope_rejected_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_over_envelope)] []))
      (clock_model 0) = CheckReject := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_remainder_past_the_envelope_rejected

/-- Rocq's `nanosleep_remainder_of_exactly_ktime_max_admitted` through the
table: the verdict, and the kernel argument for it, are the
checker-level pin `nanosleep_remainder_of_exactly_ktime_max_admitted`
above.
kernel: kernel/time/hrtimer.c:do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_remainder_of_exactly_ktime_max_admitted_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_1us)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_ktime_max)] []))
      (clock_model 0) = CheckOk (clock_model 0) [] := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_remainder_of_exactly_ktime_max_admitted

/-- Rocq's `nanosleep_remainder_of_exactly_the_envelope_rejected` through
the table: the verdict, and the kernel argument for it, are the
checker-level pin `nanosleep_remainder_of_exactly_the_envelope_rejected`
above.
kernel: kernel/time/hrtimer.c:do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_remainder_of_exactly_the_envelope_rejected_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_1us)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_at_envelope)] []))
      (clock_model 0) = CheckReject := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_remainder_of_exactly_the_envelope_rejected

/-- Rocq's `nanosleep_half_a_remainder_rejected` through the table: the
verdict, and the kernel argument for it, are the checker-level pin
`nanosleep_half_a_remainder_rejected` above.
kernel: kernel/time/time.c:put_timespec64; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem nanosleep_half_a_remainder_rejected_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_half)] []))
      (clock_model 0) = CheckReject := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_half_a_remainder_rejected

/-- Rocq's `nanosleep_completed_sleep_with_a_remainder_rejected` through the
table: the verdict, and the kernel argument for it, are the
checker-level pin `nanosleep_completed_sleep_with_a_remainder_rejected`
above.
kernel: kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout@v6.18.46 -/
theorem nanosleep_completed_sleep_with_a_remainder_rejected_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect 0 [(4096, ts_250ms)] []))
      (clock_model 0) = CheckReject := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_completed_sleep_with_a_remainder_rejected

/-- Rocq's `nanosleep_missing_copyin_rejected` through the table: the
verdict, and the kernel argument for it, are the checker-level pin
`nanosleep_missing_copyin_rejected` above.
kernel: kernel/time/hrtimer.c:nanosleep; kernel/time/time.c:get_timespec64@v6.18.46 -/
theorem nanosleep_missing_copyin_rejected_over_the_real_table :
    check_syscall (nanosleep_input 0 ts_1s) (mkEffect 0 [] []) (clock_model 0) = CheckReject := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_missing_copyin_rejected

/-- Rocq's `nanosleep_copyin_at_the_wrong_pointer_rejected` through the
table: the verdict, and the kernel argument for it, are the
checker-level pin `nanosleep_copyin_at_the_wrong_pointer_rejected`
above.
kernel: kernel/time/hrtimer.c:nanosleep; kernel/time/time.c:get_timespec64@v6.18.46 -/
theorem nanosleep_copyin_at_the_wrong_pointer_rejected_over_the_real_table :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(4096, 16)] (mkEffect 0 [] [])) (clock_model 0)
      = CheckReject := by
  rw [check_syscall_nanosleep_input]
  exact nanosleep_copyin_at_the_wrong_pointer_rejected

/-! ### The witness the table hands `receptive`

`syscall_spec_witness` dispatches over the same table, so the arm's
`ca_witness` is what it answers at 101. -/

/-- `witness_completed_sleep_advances_the_clock` through the table: at a
NULL and at a writable `rmtp` the table's witness is the completed sleep
— the ledger, return 0, no write, and the clock carried by the whole
request — the answer `do_nanosleep` gives once the timer has fired
(kernel/time/hrtimer.c:2130-2131, Linux v6.18.46).
kernel: kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep@v6.18.46 -/
theorem witness_completed_sleep_advances_the_clock_over_the_real_table :
    syscall_spec_witness (nanosleep_input 0 ts_1s) (clock_model 0)
        = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 1000000000) []
      ∧ syscall_spec_witness (nanosleep_input 4096 ts_1s) (clock_model 0)
        = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 1000000000) [] := by
  have hw : ∀ rmtp req m,
      syscall_spec_witness (nanosleep_input rmtp req) m = nanosleep_offer rmtp req m := by
    intro rmtp req m
    unfold syscall_spec_witness table_witness
    rw [lookup_nanosleep_input]
    rfl
  rw [hw, hw]
  exact witness_completed_sleep_advances_the_clock

end V_Kernel_Time_Hrtimer

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Time.Hrtimer
