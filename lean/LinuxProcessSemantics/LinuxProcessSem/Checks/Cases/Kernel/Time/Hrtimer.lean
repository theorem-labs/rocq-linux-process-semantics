import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.PosixTimers

/-! rocq-cases: 2871c3b17515278b4604f59a0fae68b70265e6f0
covers: nanosleep_completed_sleep_advances_the_clock -- nanosleep_completed_sleep_advances_the_clock
covers: nanosleep_null_remainder_interruption_holds_the_clock -- nanosleep_null_remainder_interruption_holds_the_clock
covers: nanosleep_interruption_advances_by_the_difference -- nanosleep_interruption_advances_by_the_difference
covers: nanosleep_remainder_past_the_request_floors_at_zero -- nanosleep_remainder_past_the_request_floors_at_zero
covers: nanosleep_request_at_the_ceiling_sleeps_to_ktime_max -- nanosleep_request_at_the_ceiling_sleeps_to_ktime_max
covers: nanosleep_request_below_the_ceiling_converts -- nanosleep_request_below_the_ceiling_converts
covers: nanosleep_request_at_the_top_of_the_band_sleeps_to_ktime_max -- nanosleep_request_at_the_top_of_the_band_sleeps_to_ktime_max
covers: nanosleep_at_the_top_of_the_band_zero_remainder_rejected -- nanosleep_at_the_top_of_the_band_zero_remainder_rejected
covers: nanosleep_request_at_the_ceiling_interrupted -- nanosleep_request_at_the_ceiling_interrupted
covers: nanosleep_at_the_ceiling_zero_remainder_rejected -- nanosleep_at_the_ceiling_zero_remainder_rejected
covers: nanosleep_request_at_two_to_the_63_is_einval -- nanosleep_request_at_two_to_the_63_is_einval
covers: nanosleep_remainder_at_the_ceiling_admitted -- nanosleep_remainder_at_the_ceiling_admitted
covers: bytes_le_to_Z_nonneg' -- bytes_le_to_Z_nonneg'
covers: timespec_ns_nonneg -- timespec_ns_nonneg
covers: timespec_ktime_nonneg -- timespec_ktime_nonneg
covers: nanosleep_clock_at_most_the_armed_deadline -- nanosleep_clock_at_most_the_armed_deadline
covers: nanosleep_clock_under_the_envelope -- nanosleep_clock_under_the_envelope
covers: nanosleep_admissible_remainder_is_a_judged_request -- nanosleep_admissible_remainder_is_a_judged_request
covers: nanosleep_clock_near_envelope_clamps -- nanosleep_clock_near_envelope_clamps
covers: nanosleep_clock_below_the_ceiling_does_not_clamp -- nanosleep_clock_below_the_ceiling_does_not_clamp
covers: nanosleep_saturated_deadline_less_the_remainder -- nanosleep_saturated_deadline_less_the_remainder
covers: nanosleep_saturated_deadline_never_steps_the_clock_back -- nanosleep_saturated_deadline_never_steps_the_clock_back
covers: nanosleep_near_the_ceiling_zero_remainder_rejected -- nanosleep_near_the_ceiling_zero_remainder_rejected
covers: nanosleep_near_the_ceiling_completed_sleep_with_a_remainder_rejected -- nanosleep_near_the_ceiling_completed_sleep_with_a_remainder_rejected
covers: nanosleep_zero_remainder_rejected -- nanosleep_zero_remainder_rejected
covers: nanosleep_remainder_past_the_envelope_rejected -- nanosleep_remainder_past_the_envelope_rejected
covers: nanosleep_remainder_of_exactly_ktime_max_admitted -- nanosleep_remainder_of_exactly_ktime_max_admitted
covers: nanosleep_remainder_of_exactly_the_envelope_rejected -- nanosleep_remainder_of_exactly_the_envelope_rejected
covers: nanosleep_half_a_remainder_rejected -- nanosleep_half_a_remainder_rejected
covers: nanosleep_completed_sleep_with_a_remainder_rejected -- nanosleep_completed_sleep_with_a_remainder_rejected
covers: nanosleep_missing_copyin_rejected -- nanosleep_missing_copyin_rejected
covers: nanosleep_copyin_at_the_wrong_pointer_rejected -- nanosleep_copyin_at_the_wrong_pointer_rejected -/

/-! # Checks.Cases.Kernel.Time.Hrtimer — what `nanosleep` admits, read off against Linux

Worked examples over `Sys.Kernel.Time.Hrtimer.nanosleep_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Kernel/Time/Hrtimer.v`.  Not part of
the trusted specification: this file is QA on the definitions, written to
be READ, and every claim in it is a claim about what the kernel does, with
the citation beside it.  Line numbers are Linux v6.18.46 (commit
1f99e9ab748f) throughout.

WHAT IS PINNED HERE.  `testing/syscall-check/tests/nanosleep_spec.c` covers
what a real kernel can be made to show.  What is left here is the whole of
`m_clock` — how far a sleep carries the clock is model-internal state that
reaches no trace at all — plus the request CEILING and the SATURATING
deadline, both of which need a request or a clock 292 years along and so
are unreachable from either side, and the remainder shapes no mutation
operator can spell.  Every worked case of the Rocq file has a same-named
twin below; the cases with no Rocq twin are the two declines (which the
probe file covers as `fail-closed` and Rocq pins nowhere), the -EINTR
without a write on a non-NULL `rmtp`, and the boundary values of
`timespec64_valid` and `nanosleep_rem_ok_b` a mutation of one comparison
would move.

HOW THESE ARE STATED.  Each decision of the spec gets an `iff` over EVERY
outcome `o` — the positive half (what is admitted) and the negative half
(nothing else is) in one statement — and beside it the concrete mistake a
lying kernel could report, refuted on its own.  Where the admitted set is
infinite — an interruption may report ANY remainder `nanosleep_rem_ok_b`
accepts — the `iff`'s right-hand side carries the existential the spec
carries, and the concrete cases pin the values inside it.  All close by
the tactics of `Checks/Cases/Tactic.lean`, except seven hand proofs: the
three universally quantified Rocq lemmas, the twins of the three `Local
Lemma` helpers they rest on, and one Lean-only fact about the word
encoding, each proved as Rocq proves its counterpart.

FIXTURES.  `wmem_ts`, `clock_model`, `ts_1s`, `ts_1s_minus` and `ts_denorm` are
the `clock_gettime` cases' fixtures, read from
`Checks/Cases/Kernel/Time/PosixTimers.lean` as Rocq reads them from
`PosixTimers.v`; the requests and remainders below are this file's own, as
in Rocq.  Rocq's `mem_at` is the Prelude's `bytes_at`: the same map,
already defined.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins
prove is that this spec and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.Hrtimer

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.PosixTimers

/-! ## The register

What `Checks/Cases/Tactic.lean` says a spec owes the `sys_simp` set: its
unfolding at low priority.  `record_copyins` is a `bind` of the wrapped
spec into a `pure`, so its unfolding is registered the same way; no spec
before this one wrapped a copy-in, which is why the line is not in
`Tactic.lean`'s register.  The gates (`timespec_valid_b`,
`nanosleep_rem_ok_b`) are decided, never unfolded, and `nanosleep_clock` is
evaluated where closed and left folded where its remainder is symbolic, so
none of the three is registered.  Both lines are OWED to `Tactic.lean`'s
register — `record_copyins.eq_1` beside the `Sys/Syscall.lean` wrappers
`ret_only.eq_1` and `err_ret.eq_1`, `nanosleep_spec.eq_1` beside the other
specs' — and sit here until that register's next edit takes them, as
`Checks/Cases/Kernel/Exit.lean` holds `wait4_spec.eq_1`: a port PR edits no
shared file.  A later port that wraps a copy-in and registers
`record_copyins.eq_1` again does no harm in the meantime: a simp set holds
its lemmas as a set, so the second `attribute` line is silent. -/

attribute [sys_simp low] nanosleep_spec.eq_1 record_copyins.eq_1

/-! ## The errnos these checks spell out -/

/-- `EINTR` is 4.
kernel: include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46 -/
example : EINTR = 4 := by decide
/-- `EINVAL` is 22.
kernel: include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
example : EINVAL = 22 := by decide
/-- `EFAULT` is 14.
kernel: include/uapi/asm-generic/errno-base.h:EFAULT@v6.18.46 -/
example : EFAULT = 14 := by decide

/-! ## Fixtures: the input, and this file's requests and remainders

The writable page `wmem_ts`, the clock `clock_model` and the one-second
request `ts_1s` (with `ts_1s_minus` and `ts_denorm`) come from the
`clock_gettime` cases, opened above. -/

/-- `nanosleep(8192, rmtp)` with `req` readable at 8192 and nothing else
readable, and `wmem_ts` as the writable view.  A non-NULL `rmtp` is
passed as 4096, which `wmem_ts` makes wholly writable, or as 4104, which
it makes straddle into an unwritable page. -/
def nanosleep_input (rmtp : word) (req : List byte) : SyscallInput :=
  SyscallInput.mkInput 101 [8192, rmtp, 0, 0, 0, 0] (bytes_at 8192 req) wmem_ts

-- The fixtures' unfoldings, at the priority every fixture has.  `clock_model`
-- is the clock_gettime cases' and is registered there only `local`ly, so it
-- is registered here too.  `wmem_ts` and the requests stay folded: the read
-- rewrites below match them by name.
attribute [sys_simp low] nanosleep_input.eq_1 clock_model.eq_1

/-! Requests and remainders, each 16 bytes of `struct timespec`: `tv_sec`
in the first eight bytes, `tv_nsec` in the last eight, little-endian.  The
value pins after them say what each one decodes to, the three shared
fixtures included. -/

/-- tv_sec = 0, tv_nsec = 0 — no time at all. -/
def ts_zero : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]
/-- tv_sec = 0, tv_nsec = 250000000 — a quarter second. -/
def ts_250ms : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0] ++ [128, 178, 230, 14, 0, 0, 0, 0]
/-- tv_sec = 0, tv_nsec = 1000 — one microsecond. -/
def ts_1us : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0] ++ [232, 3, 0, 0, 0, 0, 0, 0]
/-- tv_sec = 0, tv_nsec = 51000 — 51 microseconds, which is one microsecond
plus the default 50us of timer slack. -/
def ts_51us : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0] ++ [56, 199, 0, 0, 0, 0, 0, 0]
/-- tv_sec = 0, tv_nsec = 1 — the smallest strictly positive remainder. -/
def ts_1ns : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0] ++ [1, 0, 0, 0, 0, 0, 0, 0]
/-- tv_sec = 0, tv_nsec = -1 as the `long long` it is: the word
`timespec64_valid` reads as 2^64 - 1 once cast to `unsigned long`. -/
def ts_neg_nsec : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0] ++ [255, 255, 255, 255, 255, 255, 255, 255]
/-- tv_sec = 9223372036 = `KTIME_SEC_MAX`, tv_nsec = 0: where `ktime_set`
stops converting. -/
def ts_ceiling : List byte :=
  [4, 125, 193, 37, 2, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]
/-- tv_sec = 9223372035, tv_nsec = 0 — one second below the ceiling. -/
def ts_below_ceiling : List byte :=
  [3, 125, 193, 37, 2, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]
/-- tv_sec = 2^63, tv_nsec = 0 — the first second `timespec64_valid`
refuses, reading the field as the `s64` it is. -/
def ts_neg_sec : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 128] ++ [0, 0, 0, 0, 0, 0, 0, 0]
/-- tv_sec = 2^63 - 1, tv_nsec = 999999999 — the largest request
`timespec64_valid` accepts, and the top of the saturating band. -/
def ts_top_of_band : List byte :=
  [255, 255, 255, 255, 255, 255, 255, 127] ++ [255, 201, 154, 59, 0, 0, 0, 0]
/-- tv_sec = 9223372037, tv_nsec = 0 — a whole second past 2^63 ns. -/
def ts_over_envelope : List byte :=
  [5, 125, 193, 37, 2, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]
/-- tv_sec = 9223372036, tv_nsec = 854775807 — exactly `KTIME_MAX` ns, the
largest remainder `nanosleep_rem_ok_b` admits. -/
def ts_ktime_max : List byte :=
  [4, 125, 193, 37, 2, 0, 0, 0] ++ [255, 215, 242, 50, 0, 0, 0, 0]
/-- tv_sec = 9223372036, tv_nsec = 854775808 — one nanosecond further: 2^63
exactly, the envelope itself. -/
def ts_at_envelope : List byte :=
  [4, 125, 193, 37, 2, 0, 0, 0] ++ [0, 216, 242, 50, 0, 0, 0, 0]
/-- Eight bytes decoding to tv_sec = 1: the width a truncating kernel would
write, and the width of a request that straddles into an unreadable page. -/
def ts_half : List byte :=
  [1, 0, 0, 0, 0, 0, 0, 0]

/-! ### What the fixtures decode to, pinned

Each is the claim the docstring above it makes, as a check rather than a
sentence; a fixture that lost the property would silently weaken every
case that relies on it. -/

/-- One second, a quarter second, a microsecond, 51 microseconds, a
nanosecond, and one nanosecond short of a second.
model: the fixtures' decoded values at numerals. -/
example :
    timespec_ns ts_1s = 1000000000 ∧ timespec_ns ts_250ms = 250000000
      ∧ timespec_ns ts_1us = 1000 ∧ timespec_ns ts_51us = 51000
      ∧ timespec_ns ts_1ns = 1 ∧ timespec_ns ts_1s_minus = 999999999 := by decide
/-- The two unnormalized nanosecond fields: exactly 10^9, and -1 read
unsigned.
model: the fixtures' decoded values at numerals. -/
example : tv_frac_of ts_denorm = 1000000000 ∧ tv_frac_of ts_neg_nsec = 18446744073709551615 := by
  decide
/-- The band's bottom, the second below it, its top, and the first word
past it.
model: the fixtures' decoded values at numerals. -/
example :
    tv_sec_of ts_ceiling = 9223372036 ∧ tv_sec_of ts_below_ceiling = 9223372035
      ∧ tv_sec_of ts_top_of_band = 9223372036854775807
      ∧ tv_sec_of ts_neg_sec = 9223372036854775808 := by decide
/-- The envelope's neighbourhood, in whole nanoseconds: one below it, on
it, and a second past it.
model: the fixtures' decoded values at numerals. -/
example :
    timespec_ns ts_ktime_max = 9223372036854775807
      ∧ timespec_ns ts_at_envelope = 9223372036854775808
      ∧ timespec_ns ts_over_envelope = 9223372037000000000 := by decide
/-- `ts_half` is eight bytes, not sixteen.
model: the fixture's length at a numeral. -/
example : ts_half.length = 8 := by decide

/-! ### The reads `sys_norm` needs

`nanosleep_spec` matches on `read_bytes_map` twice — the request, then the
remainder destination — and a `match` on a closed reader application is
reduced by nothing in `sys_norm`'s first pass unless a rewrite hands it
the constructor.  These are those rewrites, one per fixture the cases
read, each a closed computation. -/

/-- The one-second request, read back whole.
model: a closed `read_bytes_map` over a fixture map, a rewrite for `sys_norm`. -/
theorem read_request_1s :
    read_bytes_map (bytes_at 8192 ts_1s) 8192 (Z_to_bv 64 16) = some ts_1s := by decide
/-- One nanosecond short of a second, read back whole.
model: a closed `read_bytes_map` over a fixture map, a rewrite for `sys_norm`. -/
theorem read_request_1s_minus :
    read_bytes_map (bytes_at 8192 ts_1s_minus) 8192 (Z_to_bv 64 16) = some ts_1s_minus := by
  decide
/-- The unnormalized request, read back whole: the bytes are readable, the
value is what `timespec64_valid` refuses.
model: a closed `read_bytes_map` over a fixture map, a rewrite for `sys_norm`. -/
theorem read_request_denorm :
    read_bytes_map (bytes_at 8192 ts_denorm) 8192 (Z_to_bv 64 16) = some ts_denorm := by decide
/-- The negative-nanosecond request, read back whole.
model: a closed `read_bytes_map` over a fixture map, a rewrite for `sys_norm`. -/
theorem read_request_neg_nsec :
    read_bytes_map (bytes_at 8192 ts_neg_nsec) 8192 (Z_to_bv 64 16) = some ts_neg_nsec := by
  decide
/-- The one-microsecond request, read back whole.
model: a closed `read_bytes_map` over a fixture map, a rewrite for `sys_norm`. -/
theorem read_request_1us :
    read_bytes_map (bytes_at 8192 ts_1us) 8192 (Z_to_bv 64 16) = some ts_1us := by decide
/-- The request at the ceiling, read back whole.
model: a closed `read_bytes_map` over a fixture map, a rewrite for `sys_norm`. -/
theorem read_request_ceiling :
    read_bytes_map (bytes_at 8192 ts_ceiling) 8192 (Z_to_bv 64 16) = some ts_ceiling := by
  decide
/-- The request a second below the ceiling, read back whole.
model: a closed `read_bytes_map` over a fixture map, a rewrite for `sys_norm`. -/
theorem read_request_below_ceiling :
    read_bytes_map (bytes_at 8192 ts_below_ceiling) 8192 (Z_to_bv 64 16)
      = some ts_below_ceiling := by decide
/-- The request at 2^63 seconds, read back whole.
model: a closed `read_bytes_map` over a fixture map, a rewrite for `sys_norm`. -/
theorem read_request_neg_sec :
    read_bytes_map (bytes_at 8192 ts_neg_sec) 8192 (Z_to_bv 64 16) = some ts_neg_sec := by
  decide
/-- The request at the top of the band, read back whole.
model: a closed `read_bytes_map` over a fixture map, a rewrite for `sys_norm`. -/
theorem read_request_top_of_band :
    read_bytes_map (bytes_at 8192 ts_top_of_band) 8192 (Z_to_bv 64 16)
      = some ts_top_of_band := by decide
/-- Eight readable bytes at 8192 and nothing past them: a 16-byte read
straddles into unreadable memory and fails whole, as `copy_from_user`'s
nonzero return makes it fail.
model: a closed `read_bytes_map` over a fixture map, a rewrite for `sys_norm`. -/
theorem read_request_half :
    read_bytes_map (bytes_at 8192 ts_half) 8192 (Z_to_bv 64 16) = none := by decide
/-- The remainder destination at 4096 is wholly writable under `wmem_ts`.
model: a closed `read_bytes_map` over a fixture map, a rewrite for `sys_norm`. -/
theorem read_wmem_ts :
    read_bytes_map wmem_ts 4096 (Z_to_bv 64 16) = some (List.replicate 16 0) := by decide
/-- ...and at 4104 it straddles into the unwritable page at 4112.
model: a closed `read_bytes_map` over a fixture map, a rewrite for `sys_norm`. -/
theorem read_wmem_ts_straddle :
    read_bytes_map wmem_ts 4104 (Z_to_bv 64 16) = none := by decide

attribute [sys_simp]
  read_request_1s read_request_1s_minus read_request_denorm read_request_neg_nsec
  read_request_1us read_request_ceiling read_request_below_ceiling read_request_neg_sec
  read_request_top_of_band read_request_half read_wmem_ts read_wmem_ts_straddle

/-! ## Gate 1: the request is read first, and a request that cannot be read declines

`SYSCALL_DEFINE2(nanosleep, ...)` (kernel/time/hrtimer.c:2189-2205, Linux v6.18.46) opens
with `get_timespec64` (:2194-2195), one `copy_from_user` of the whole
struct (kernel/time/time.c:878) whose nonzero return is -EFAULT (:879-880)
before `timespec64_valid` or the timer is reached. -/

/-- A request straddling into unreadable memory — eight readable bytes at
8192 and nothing past them — declines, whatever `rmtp` and the model are.
A COVERAGE GAP, NOT AN EMPTY INTERSECTION: Linux's answer is the definite
-EFAULT of `get_timespec64` with the user memory untouched, and the
decline is the Rocq definition's declared narrowing (the copy-in ledger of
a failed copy is what an answering arm would have to land first).
kernel: kernel/time/time.c:get_timespec64; kernel/time/hrtimer.c:nanosleep@v6.18.46 -/
theorem nanosleep_unreadable_request_is_unmodeled (rmtp : word) (m : Model)
    (o : outcome SyscallEffect) :
    nanosleep_spec 8192 rmtp (nanosleep_input rmtp ts_half) m o ↔ o = Unmodeled := by
  sys_norm

/-- Linux's own -EFAULT is NOT given there: the decline admits no answer,
so nothing turns the gap into a guess.
kernel: kernel/time/time.c:get_timespec64@v6.18.46 -/
theorem nanosleep_unreadable_request_efault_rejected (rmtp : word) (m m' : Model)
    (evs : List event) :
    ¬ nanosleep_spec 8192 rmtp (nanosleep_input rmtp ts_half) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  intro h
  sys_refute at h

/-! ## Gate 2: `timespec64_valid`, and -EINVAL before anything is slept on

`timespec64_valid` (include/linux/time64.h:97-106, Linux v6.18.46) refuses `tv_sec < 0`
(:100-101) and `(unsigned long)tv_nsec >= NSEC_PER_SEC` (:103-104), and
`SYSCALL_DEFINE2(nanosleep, ...)` answers -EINVAL for either
(kernel/time/hrtimer.c:2197-2198) with the request already consumed and
`rmtp` never touched.  The gate holds for EVERY model, so these pins
quantify over `m`. -/

/-- 2^63 seconds reads as a negative `s64` and is -EINVAL, not a sleep:
the top of the saturating band is one below it, so judging the ceiling did
not widen the band that answers.  The request is in the ledger — it was
read before it was judged — and the model is untouched.
kernel: kernel/time/hrtimer.c:nanosleep; include/linux/time64.h:timespec64_valid; include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46
rocq-twin: nanosleep_request_at_two_to_the_63_is_einval -/
theorem nanosleep_request_at_two_to_the_63_is_einval (m : Model) (o : outcome SyscallEffect) :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_neg_sec) m o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) m [] := by
  sys_norm

/-- A `tv_nsec` of exactly 10^9 fails `(unsigned long)tv_nsec >=
NSEC_PER_SEC` (include/linux/time64.h:103-104, Linux v6.18.46): -EINVAL, not a sleep of
two seconds.  The boundary is strict on the other side — one nanosecond
less sleeps, `nanosleep_request_one_ns_short_of_a_second_sleeps` below.
kernel: kernel/time/hrtimer.c:nanosleep; include/linux/time64.h:timespec64_valid; include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
theorem nanosleep_request_with_a_denormal_nsec_is_einval (m : Model)
    (o : outcome SyscallEffect) :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_denorm) m o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) m [] := by
  sys_norm

/-- A negative `tv_nsec` is cast to `unsigned long` before the comparison
(include/linux/time64.h:103), so -1 fails the same test 10^9 does: -EINVAL.
kernel: kernel/time/hrtimer.c:nanosleep; include/linux/time64.h:timespec64_valid; include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
theorem nanosleep_request_with_a_negative_nsec_is_einval (m : Model)
    (o : outcome SyscallEffect) :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_neg_nsec) m o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) m [] := by
  sys_norm

/-- ...and the -EINVAL is answered whatever `rmtp` is — NULL, wholly
writable, or straddling into an unwritable page — because
`timespec64_valid` fires (kernel/time/hrtimer.c:2197-2198, Linux v6.18.46) before the
restart block ever looks at `rmtp` (:2201), and nothing is written.  This
is the errno pair the `rmtp` gate must not reorder: an unwritable `rmtp`
declines only past a VALID request, so a spec that consulted `rmtp` first
would fail this pin on the straddling shape.  The statement quantifies
over `rmtp` for exactly that reason.
kernel: kernel/time/hrtimer.c:nanosleep; include/linux/time64.h:timespec64_valid; include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
theorem nanosleep_invalid_request_is_einval_whatever_rmtp (rmtp : word) (m : Model)
    (o : outcome SyscallEffect) :
    nanosleep_spec 8192 rmtp (nanosleep_input rmtp ts_neg_sec) m o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) m [] := by
  sys_norm

/-- A kernel that slept on 2^63 seconds and returned 0 is lying: the
`tv_sec < 0` test (include/linux/time64.h:100-101) is reached before the
timer is.
kernel: include/linux/time64.h:timespec64_valid@v6.18.46 -/
theorem nanosleep_invalid_request_sleep_rejected (m m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_neg_sec) m
        (Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) m' evs) := by
  intro h
  sys_refute at h

/-- ...and so is one that answered -EINVAL without having read the
request: `get_timespec64` runs first (kernel/time/hrtimer.c:2194), so the
ledger carries the sixteen bytes on the -EINVAL path too.
kernel: kernel/time/hrtimer.c:nanosleep; kernel/time/time.c:get_timespec64@v6.18.46 -/
theorem nanosleep_invalid_request_einval_without_the_copyin_rejected (m m' : Model)
    (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_neg_sec) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  intro h
  sys_refute at h

/-- MODEL-INTERNAL STATE, and the strict side of the `tv_nsec` boundary:
999999999 ns passes `timespec64_valid` and a completed sleep carries
`m_clock` forward by exactly that — and nothing else is admitted at a NULL
`rmtp` but the -EINTR that holds the clock; a sleep of a whole second is
refused.
kernel: include/linux/time64.h:timespec64_valid; kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46 -/
theorem nanosleep_request_one_ns_short_of_a_second_sleeps (o : outcome SyscallEffect) :
    nanosleep_spec 8192 0 (nanosleep_input 0 ts_1s_minus) (clock_model 0) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 999999999) []
      ∨ o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] [])) (clock_model 0) [] := by
  sys_norm

/-! ## A NULL `rmtp`: both outcomes, and nothing written on either

With `rmtp == NULL` the restart block's type is `TT_NONE`
(kernel/time/hrtimer.c:2201, Linux v6.18.46), so `do_nanosleep` writes nothing on either
path (:2133-2134, :2144).  A completed sleep returns 0 (:2130-2131);
an interruption returns -ERESTART_RESTARTBLOCK, which
`arch_do_signal_or_restart` (arch/riscv/kernel/signal.c:437-444, Linux v6.18.46) turns
into -EINTR when a handler runs.  The environment chooses. -/

/-- The whole call at a NULL `rmtp`: a completed sleep that carries the
clock forward by the second requested, or an -EINTR that writes nothing
and leaves the clock where it was — and nothing else, `Unmodeled`
included.
kernel: kernel/time/hrtimer.c:nanosleep,hrtimer_nanosleep,do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46 -/
theorem nanosleep_null_rmtp_admits_both_outcomes (o : outcome SyscallEffect) :
    nanosleep_spec 8192 0 (nanosleep_input 0 ts_1s) (clock_model 0) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 1000000000) []
      ∨ o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] [])) (clock_model 0) [] := by
  sys_norm

/-- MODEL-INTERNAL STATE.  A completed sleep carries `m_clock` forward by
the WHOLE request: `hrtimer_nanosleep` arms the soft expiry at now plus
the request (kernel/time/hrtimer.c:2167 (Linux v6.18.46), :1242-1243) and a timer never
fires before its soft expiry, so returning 0 (:2130-2131) means at least
that much elapsed on the very clock `m_clock` tracks.  Nothing about
`m_clock` reaches a trace; the conformance suite feels it only through a
later `clock_gettime` being judged against a clock a second further on.
kernel: kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep; include/linux/hrtimer.h:hrtimer_set_expires_range_ns@v6.18.46
rocq-twin: nanosleep_completed_sleep_advances_the_clock -/
theorem nanosleep_completed_sleep_advances_the_clock :
    nanosleep_spec 8192 0 (nanosleep_input 0 ts_1s) (clock_model 0)
      (Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 1000000000) []) := by
  sys_norm

/-- MODEL-INTERNAL STATE.  With a NULL `rmtp` the interrupted arm has
nowhere to report the remainder (`TT_NONE`, kernel/time/hrtimer.c:2201 (Linux v6.18.46),
:2134), so how much of the sleep elapsed is unknowable and the clock
stays where it was.  This is the only accepted `nanosleep` outcome that
does not move `m_clock`, and the pair with the case above is what makes
the distinction non-vacuous.
kernel: kernel/time/hrtimer.c:nanosleep,do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46
rocq-twin: nanosleep_null_remainder_interruption_holds_the_clock -/
theorem nanosleep_null_remainder_interruption_holds_the_clock :
    nanosleep_spec 8192 0 (nanosleep_input 0 ts_1s) (clock_model 0)
      (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] [])) (clock_model 0) []) := by
  sys_norm

/-- A write at 4096 on a NULL-`rmtp` interruption is a write to an address
the kernel was never given: under `TT_NONE`, `do_nanosleep`
(kernel/time/hrtimer.c:2134, :2144) never reaches `nanosleep_copyout`.
kernel: kernel/time/hrtimer.c:do_nanosleep@v6.18.46 -/
theorem nanosleep_null_rmtp_interruption_with_a_write_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 0 (nanosleep_input 0 ts_1s) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] [])) m' evs) := by
  intro h
  sys_refute at h

/-- A completed sleep that leaves the clock where it was is refused on
the model: the timer armed at now plus a second did not fire early
(`hrtimer_nanosleep`, kernel/time/hrtimer.c:2167).
kernel: kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep@v6.18.46 -/
theorem nanosleep_null_rmtp_completed_sleep_holding_the_clock_rejected :
    ¬ nanosleep_spec 8192 0 (nanosleep_input 0 ts_1s) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 0) []) := by
  intro h
  sys_refute at h

/-! ## A writable `rmtp`: both outcomes, and the remainder written only with -EINTR

`do_nanosleep` reaches `nanosleep_copyout` only on the interrupted path
and only for a strictly positive remainder (kernel/time/hrtimer.c:2133-2142, Linux v6.18.46);
`put_timespec64` writes the sixteen bytes (kernel/time/time.c:903-912).
The remainder is measured against the HARD expiry
(`hrtimer_expires_remaining`, include/linux/hrtimer.h:159-162), which
`hrtimer_nanosleep` set `current->timer_slack_ns` past the soft one
(kernel/time/hrtimer.c:2167, Linux v6.18.46), so it is NOT bounded by the request. -/

/-- The whole call at a writable `rmtp`: a completed sleep that carries the
clock forward by the second requested and writes nothing, or an -EINTR
carrying exactly one write at `rmtp` of some remainder `nanosleep_rem_ok_b`
admits, with the clock at the armed deadline less that remainder, floored
at where it stood.  Nothing else, `Unmodeled` included.  The clock's
origin reading is spelled `Z_to_bv 64 0`, as `clock_model` spells it.
The -EINTR half fixes the SHAPE — one write at `rmtp`, the clock at the
armed deadline less the remainder, nothing `Unmodeled` — and the concrete
cases below fix the values inside it: `ts_250ms` leaves 750000000,
`ts_51us` floors at 0, `ts_1ns` leaves 999999999, `ts_zero` is refused.
kernel: kernel/time/hrtimer.c:nanosleep,hrtimer_nanosleep,do_nanosleep,nanosleep_copyout; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46 -/
theorem nanosleep_writable_rmtp_admits_both_outcomes (o : outcome SyscallEffect) :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model 0) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 1000000000) []
      ∨ ∃ rem : List byte,
          o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, rem)] []))
                (with_clock (nanosleep_clock (Z_to_bv 64 0) ts_1s rem) (clock_model 0)) []
          ∧ nanosleep_rem_ok_b rem = true := by
  sys_norm

/-- MODEL-INTERNAL STATE.  The interrupted arm carries `m_clock` forward
by the request LESS the reported remainder — a second requested with a
quarter second left is three quarters of a second elapsed
(`hrtimer_expires_remaining`, include/linux/hrtimer.h:159-162 (Linux v6.18.46), read at
kernel/time/hrtimer.c:2135).  What the model records is the one-sided fact
the kernel actually establishes, and it is invisible from outside for the
same reason the completed sleep's advance is.
kernel: kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46
rocq-twin: nanosleep_interruption_advances_by_the_difference -/
theorem nanosleep_interruption_advances_by_the_difference :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model 0)
      (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
          (clock_model 750000000) []) := by
  sys_norm

/-- ...and an interruption reporting a quarter second left that leaves the
clock at 0 is refused on the model: three quarters of a second elapsed.
kernel: kernel/time/hrtimer.c:do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining@v6.18.46 -/
theorem nanosleep_interruption_holding_the_clock_rejected :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
            (clock_model 0) []) := by
  intro h
  sys_refute at h

/-- MODEL-INTERNAL STATE, and the sharp one.  A remainder LARGER than the
request is admissible, because `do_nanosleep` measures what is left
against the HARD expiry (kernel/time/hrtimer.c:2135 (Linux v6.18.46);
include/linux/hrtimer.h:159-162) and `hrtimer_nanosleep` sets that
`current->timer_slack_ns` past the soft one (kernel/time/hrtimer.c:2167;
include/linux/hrtimer.h:109-113) — 50 microseconds by default.  So a
one-microsecond sleep can report 51 microseconds remaining, and the
advance is floored at the clock's previous value rather than going
negative: without the `max` in `nanosleep_clock` the difference would be
-50000 and the clock would wrap to within 50 microseconds of 2^64.
kernel: kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep; include/linux/hrtimer.h:hrtimer_set_expires_range_ns,hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46
rocq-twin: nanosleep_remainder_past_the_request_floors_at_zero -/
theorem nanosleep_remainder_past_the_request_floors_at_zero :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1us) (clock_model 0)
      (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_51us)] []))
          (clock_model 0) []) := by
  sys_norm

/-- The whole call for a one-microsecond request at a writable `rmtp`: the
completed sleep carries the clock to 1000 and writes nothing, or an -EINTR
writes one admitted remainder — 51 µs among them, past the request by the
default slack (init/init_task.c:146, Linux v6.18.46) — with the clock at the armed deadline
less it, floored at where it stood.  Nothing else: this `iff` is what
refuses a clock that went negative or wrapped behind the floor.
kernel: kernel/time/hrtimer.c:nanosleep,hrtimer_nanosleep,do_nanosleep,nanosleep_copyout; include/linux/hrtimer.h:hrtimer_set_expires_range_ns,hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46 -/
theorem nanosleep_microsecond_request_at_a_writable_rmtp_admits_both_outcomes
    (o : outcome SyscallEffect) :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1us) (clock_model 0) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 1000) []
      ∨ ∃ rem : List byte,
          o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, rem)] []))
                (with_clock (nanosleep_clock (Z_to_bv 64 0) ts_1us rem) (clock_model 0)) []
          ∧ nanosleep_rem_ok_b rem = true := by
  sys_norm

/-- A remainder past the request does not WRAP the clock: without the floor
the difference 1000 - 51000 would land within 50 µs of 2^64, and 584 years
did not elapse in a microsecond sleep.  CLOCK_MONOTONIC never decreases, and
`m_clock` is a lower bound on it, so the wrapped word is refused.
kernel: kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep; include/linux/hrtimer.h:hrtimer_set_expires_range_ns,hrtimer_expires_remaining@v6.18.46 -/
theorem nanosleep_remainder_past_the_request_wrapped_clock_rejected :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1us) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_51us)] []))
            (clock_model (2 ^ 64 - 50000)) []) := by
  intro h
  sys_refute at h

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  An -EINTR reporting a
remainder of exactly zero is REFUSED: `do_nanosleep` computes what is
left and, when that is at or below zero, returns 0 having written nothing
(kernel/time/hrtimer.c:2138-2139) — the deadline has passed, so the call
is a completed sleep and is reported as one.
kernel: kernel/time/hrtimer.c:do_nanosleep@v6.18.46
rocq-twin: nanosleep_zero_remainder_rejected -/
theorem nanosleep_zero_remainder_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_zero)] [])) m' evs) := by
  intro h
  sys_refute at h

/-- ...and one nanosecond IS admitted: `rem <= 0` is the test
(kernel/time/hrtimer.c:2138, Linux v6.18.46), so the smallest positive remainder is
written, and the clock lands one nanosecond short of the second.
kernel: kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46 -/
theorem nanosleep_one_nanosecond_remainder_admitted :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model 0)
      (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_1ns)] []))
          (clock_model 999999999) []) := by
  sys_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the mirror.  A completed
sleep that ALSO writes a remainder is refused: `nanosleep_copyout` is
reached only on the interrupted path (kernel/time/hrtimer.c:2130-2142, Linux v6.18.46), so
a return of 0 and a write at `rmtp` cannot both happen.  The remainder
written here is a PERFECTLY VALID one, which is what makes the case
attribute: the only thing wrong with this effect is that a completed
sleep carries it.
kernel: kernel/time/hrtimer.c:do_nanosleep@v6.18.46
rocq-twin: nanosleep_completed_sleep_with_a_remainder_rejected -/
theorem nanosleep_completed_sleep_with_a_remainder_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect 0 [(4096, ts_250ms)] [])) m' evs) := by
  intro h
  sys_refute at h

/-- An -EINTR with NO write on a non-NULL `rmtp` is refused too: with
`TT_NATIVE` set (kernel/time/hrtimer.c:2201, Linux v6.18.46) the only exit of `do_nanosleep`
that yields -ERESTART_RESTARTBLOCK, and so the program's -EINTR, is
`nanosleep_copyout`'s (:2109), after `put_timespec64` wrote the sixteen
bytes (:2103-2104); a remainder at or below zero returns 0 instead
(:2138-2139), never -EINTR.  The write is what the program reads its next
request out of.
kernel: kernel/time/hrtimer.c:nanosleep,do_nanosleep,nanosleep_copyout@v6.18.46 -/
theorem nanosleep_interruption_without_a_remainder_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] [])) m' evs) := by
  intro h
  sys_refute at h

/-- The write lands at `rmtp` and nowhere else: `put_timespec64` is handed
`restart->nanosleep.rmtp` (kernel/time/hrtimer.c:2103), the pointer the
syscall stored at :2202.
kernel: kernel/time/hrtimer.c:nanosleep,nanosleep_copyout@v6.18.46 -/
theorem nanosleep_remainder_at_the_wrong_address_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(8192, ts_250ms)] [])) m' evs) := by
  intro h
  sys_refute at h

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the remainder's LENGTH
conjunct, on its own.  Eight bytes decoding to `tv_sec = 1`: `tv_frac_of`
of the empty tail is 0, so the reading is normalized, and `timespec_ns` is
10^9, positive and far under the envelope.  Only the length is wrong:
`put_timespec64` writes `sizeof(struct __kernel_timespec)` (kernel/time/time.c:911, Linux v6.18.46).
This is the shape a truncating kernel would produce, and exactly the one
a `trunc-writes:8` mutation cannot pin, because truncating a completed
sleep's remainder gives eight ZERO bytes, which fails strict positivity
first.
kernel: kernel/time/time.c:put_timespec64@v6.18.46
rocq-twin: nanosleep_half_a_remainder_rejected -/
theorem nanosleep_half_a_remainder_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_half)] [])) m' evs) := by
  intro h
  sys_refute at h

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the remainder's
NORMALIZATION conjunct, on its own.  A `tv_nsec` of exactly 10^9 with
`tv_sec = 1`: sixteen bytes, positive, under the envelope, and not what
`ns_to_timespec64` writes, whose `div_u64_rem` by NSEC_PER_SEC leaves
`tv_nsec` below 10^9 (kernel/time/time.c:528-530).
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46 -/
theorem nanosleep_denormal_remainder_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_denorm)] [])) m' evs) := by
  intro h
  sys_refute at h

/-- ...and 999999999 ns, the largest `tv_nsec` `ns_to_timespec64` can
write, is admitted: one nanosecond of the second elapsed.
kernel: kernel/time/time.c:ns_to_timespec64; kernel/time/hrtimer.c:do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46 -/
theorem nanosleep_remainder_one_ns_short_of_a_second_admitted :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model 0)
      (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_1s_minus)] []))
          (clock_model 1) []) := by
  sys_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the remainder's ENVELOPE
conjunct, which nothing else reaches.  A remainder of 9223372037 seconds
is normalized, sixteen bytes long and strictly positive, so it fails the
fourth conjunct ALONE: a `ktime_t` is at most `KTIME_MAX`
(include/linux/time64.h:30, Linux v6.18.46), and `do_nanosleep` converts the
ktime_t remainder it computed (kernel/time/hrtimer.c:2135-2140).  No mutation can spell this: the write
operators build a prefix of the real bytes, one uniform byte, or 0x41
filler, and to stay under the envelope `tv_sec` must decode to 0, which
forces all sixteen bytes to zero, and an all-zero remainder fails strict
positivity instead.
kernel: kernel/time/hrtimer.c:do_nanosleep@v6.18.46
rocq-twin: nanosleep_remainder_past_the_envelope_rejected -/
theorem nanosleep_remainder_past_the_envelope_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_over_envelope)] []))
            m' evs) := by
  intro h
  sys_refute at h

/-- THE ENVELOPE CONJUNCT'S BOUNDARY, one nanosecond either side, and the
twin of a probe pair: `testing/syscall-check/tests/nanosleep_spec.c`
smuggles these two byte strings onto a real interrupted sleep.
`KTIME_MAX` nanoseconds — 9223372036 s and 854775807 ns — is the LARGEST
remainder `nanosleep_rem_ok_b` admits, and the request here is a
microsecond, so the difference is 292 years negative and the floor holds
the clock at 0.  The value is the TYPE's bound, not a producible trace:
`hrtimer_expires_remaining` (include/linux/hrtimer.h:159-162, Linux v6.18.46) subtracts the
clock reading at wake, positive on any running system, from an expiry
`ktime_add_safe` holds at or below `KTIME_MAX`, so a real remainder is
strictly below it.  Accepting the bound itself is one value of priority 2,
Rocq's `nanosleep_rem_ok_b`, and this twin keeps it.
kernel: kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout; kernel/time/time.c:ns_to_timespec64; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46
rocq-twin: nanosleep_remainder_of_exactly_ktime_max_admitted -/
theorem nanosleep_remainder_of_exactly_ktime_max_admitted :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1us) (clock_model 0)
      (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_ktime_max)] []))
          (clock_model 0) []) := by
  sys_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — ONE NANOSECOND further.
9223372036 s and 854775808 ns is 2^63 exactly, which no `ktime_t` holds
(`KTIME_MAX` is `~((u64)1 << 63)` as an `s64`, include/linux/time64.h:30, Linux v6.18.46),
so the fourth conjunct's strict bound refuses it and the other three
still pass.  Without this twin the case above would be satisfied by a
bound of `≤` as happily as by `<`.
kernel: kernel/time/hrtimer.c:do_nanosleep@v6.18.46
rocq-twin: nanosleep_remainder_of_exactly_the_envelope_rejected -/
theorem nanosleep_remainder_of_exactly_the_envelope_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1us) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_at_envelope)] []))
            m' evs) := by
  intro h
  sys_refute at h

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the remainder AT the
ceiling, the value that used to poison the next call.  `nanosleep_rem_ok_b`
admits it: 9223372036 * 10^9 is 854775808 ns below the envelope.  The
clock does not move — the request was a second and the remainder is 292
years, so the difference is negative and the floor holds it.  Read this
case together with `nanosleep_request_at_the_ceiling_sleeps_to_ktime_max`:
THIS is the remainder, THAT is what the next call does with it.
kernel: kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46
rocq-twin: nanosleep_remainder_at_the_ceiling_admitted -/
theorem nanosleep_remainder_at_the_ceiling_admitted :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model 0)
      (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_ceiling)] []))
          (clock_model 0) []) := by
  sys_norm

/-! ## The request's ceiling: judged, not declined

`timespec64_to_ktime` (include/linux/ktime.h:69-72, Linux v6.18.46) is `ktime_set`
(include/linux/ktime.h:36-42), which returns `KTIME_MAX` outright once
`secs >= KTIME_SEC_MAX` (the test at :38-39), and
`SYSCALL_DEFINE2(nanosleep, ...)` (kernel/time/hrtimer.c:2203-2204) hands
that to `hrtimer_nanosleep`.  A request at or
above the ceiling is an ordinary interruptible sleep toward the end of
`ktime_t`.  A probe cannot reach this from either side — issuing the call
really would park the guest for 292 years — so the whole of the arm is
here. -/

/-- MODEL-INTERNAL STATE, and the arm that replaced a decline.  A request
AT `KTIME_SEC_MAX` is ANSWERED, and a completed sleep carries `m_clock` to
`KTIME_MAX`, 2^63 - 1: `ktime_set`'s early return (include/linux/ktime.h:38-39, Linux v6.18.46)
hands `hrtimer_nanosleep` the end of `ktime_t` rather than a product.  The
`iff` carries the only other outcome at a NULL `rmtp`, the -EINTR that holds
the clock, and refuses every other value — the product 9223372036 * 10^9
among them.
kernel: include/linux/ktime.h:ktime_set,timespec64_to_ktime; kernel/time/hrtimer.c:nanosleep,hrtimer_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46
rocq-twin: nanosleep_request_at_the_ceiling_sleeps_to_ktime_max -/
theorem nanosleep_request_at_the_ceiling_sleeps_to_ktime_max (o : outcome SyscallEffect) :
    nanosleep_spec 8192 0 (nanosleep_input 0 ts_ceiling) (clock_model 0) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model (2 ^ 63 - 1)) []
      ∨ o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] [])) (clock_model 0) [] := by
  sys_norm

/-- MODEL-INTERNAL STATE — the control, and the reason the case above is
not vacuous.  One second BELOW the ceiling `ktime_set` converts rather
than saturating (`secs * NSEC_PER_SEC + nsecs`, include/linux/ktime.h:41, Linux v6.18.46),
so the recorded clock is the plain product 9223372035 * 10^9.  The two
requests are one second apart and the clocks they record are 1854775807 ns
apart: that gap is exactly the early return firing.  The `iff` refuses
every other value, `KTIME_MAX` among them: a conversion that always
saturated fails here, one that never did fails the case above.
kernel: include/linux/ktime.h:ktime_set,timespec64_to_ktime; kernel/time/hrtimer.c:hrtimer_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46
rocq-twin: nanosleep_request_below_the_ceiling_converts -/
theorem nanosleep_request_below_the_ceiling_converts (o : outcome SyscallEffect) :
    nanosleep_spec 8192 0 (nanosleep_input 0 ts_below_ceiling) (clock_model 0) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 9223372035000000000) []
      ∨ o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] [])) (clock_model 0) [] := by
  sys_norm

/-- MODEL-INTERNAL STATE — the band's TOP.  The largest `tv_sec`
`timespec64_valid` accepts is 2^63 - 1, one below the word that reads as
negative, and it sleeps to `KTIME_MAX` exactly as the bottom of the band
does: `ktime_set` tests `secs >= KTIME_SEC_MAX` (include/linux/ktime.h:38, Linux v6.18.46)
and returns the same constant across the whole band.  The `iff` refuses
every other value at the top of the band as well.
kernel: include/linux/ktime.h:ktime_set; include/linux/time64.h:timespec64_valid; kernel/time/hrtimer.c:hrtimer_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46
rocq-twin: nanosleep_request_at_the_top_of_the_band_sleeps_to_ktime_max -/
theorem nanosleep_request_at_the_top_of_the_band_sleeps_to_ktime_max (o : outcome SyscallEffect) :
    nanosleep_spec 8192 0 (nanosleep_input 0 ts_top_of_band) (clock_model 0) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model (2 ^ 63 - 1)) []
      ∨ o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] [])) (clock_model 0) [] := by
  sys_norm

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the same rejection at
the top of the band as at its bottom: an -EINTR reporting a remainder of
exactly zero is refused wherever the request sits
(kernel/time/hrtimer.c:2138-2139).
kernel: kernel/time/hrtimer.c:do_nanosleep@v6.18.46
rocq-twin: nanosleep_at_the_top_of_the_band_zero_remainder_rejected -/
theorem nanosleep_at_the_top_of_the_band_zero_remainder_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_top_of_band) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_zero)] [])) m' evs) := by
  intro h
  sys_refute at h

/-- MODEL-INTERNAL STATE.  The ceiling request INTERRUPTED: the clock moves
to the deadline the kernel armed — `KTIME_MAX` — less the reported
remainder, exactly as at any smaller request.  A quarter second left
leaves 2^63 - 1 - 250000000.
kernel: include/linux/ktime.h:ktime_set; kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46
rocq-twin: nanosleep_request_at_the_ceiling_interrupted -/
theorem nanosleep_request_at_the_ceiling_interrupted :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_ceiling) (clock_model 0)
      (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
          (clock_model 9223372036604775807) []) := by
  sys_norm

/-- The whole call for a request AT the ceiling with a writable `rmtp`: the
completed sleep carries the clock to `KTIME_MAX`, or an -EINTR writes one
admitted remainder with the clock at `KTIME_MAX` less it, floored at 0 —
the deadline `ktime_set` armed (include/linux/ktime.h:38-39, Linux v6.18.46), never the
product 9223372036 * 10^9.  Nothing else.
kernel: include/linux/ktime.h:ktime_set; kernel/time/hrtimer.c:nanosleep,hrtimer_nanosleep,do_nanosleep,nanosleep_copyout; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46 -/
theorem nanosleep_ceiling_request_at_a_writable_rmtp_admits_both_outcomes
    (o : outcome SyscallEffect) :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_ceiling) (clock_model 0) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model (2 ^ 63 - 1)) []
      ∨ ∃ rem : List byte,
          o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, rem)] []))
                (with_clock (nanosleep_clock (Z_to_bv 64 0) ts_ceiling rem) (clock_model 0)) []
          ∧ nanosleep_rem_ok_b rem = true := by
  sys_norm

/-- At the ceiling the deadline the kernel armed is `KTIME_MAX`, not the
product 9223372036 * 10^9 (`ktime_set`, include/linux/ktime.h:38-39):
the quarter second comes off `KTIME_MAX`, and taking it off the product is
refused.
kernel: include/linux/ktime.h:ktime_set; kernel/time/hrtimer.c:hrtimer_nanosleep,do_nanosleep@v6.18.46 -/
theorem nanosleep_request_at_the_ceiling_interrupted_plain_product_rejected :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_ceiling) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
            (clock_model 9223372035750000000) []) := by
  intro h
  sys_refute at h

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and the REJECTION the
old decline used to cost: at the ceiling the old spec answered
`Unmodeled` for every effect, so it refused nothing there.  Now the same
-EINTR reporting a remainder of exactly zero is refused, as it is at
every other request.
kernel: kernel/time/hrtimer.c:do_nanosleep@v6.18.46
rocq-twin: nanosleep_at_the_ceiling_zero_remainder_rejected -/
theorem nanosleep_at_the_ceiling_zero_remainder_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_ceiling) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_zero)] [])) m' evs) := by
  intro h
  sys_refute at h

/-! ## The saturating deadline: a clock near the top of ktime_t

`__hrtimer_start_range_ns` (kernel/time/hrtimer.c:1242-1243, Linux v6.18.46) turns the
relative request into an absolute expiry with `ktime_add_safe`
(kernel/time/hrtimer.c:340-352), which replaces an overflowing sum with
`ktime_set(KTIME_SEC_MAX, 0)` (:348-349)
— `KTIME_MAX` — and the sleep runs to THAT deadline rather than failing.
A clock this far along needs 292 years of uptime, or one `clock_gettime`
whose environment chose the reading; no probe reaches it. -/

/-- MODEL-INTERNAL STATE, and the whole of what replaced a decline.  A
clock already within a second of the top of `ktime_t`'s range ANSWERS a
one-second sleep, recording the saturated deadline 2^63 - 1 rather than a
sum the type cannot hold.  The recorded value is 2^63 - 1 and not 2^63:
the saturation constant is `ktime_set(KTIME_SEC_MAX, 0)`, and `ktime_set`'s
early return tests `secs >= KTIME_SEC_MAX` (include/linux/ktime.h:38, Linux v6.18.46), so
it fires on the very value `ktime_add_safe` passes it.  The `iff` carries
the -EINTR that holds the clock, the only other outcome at a NULL `rmtp`,
and refuses every other value — the unsaturated sum 2^63, which no
`ktime_t` holds, among them.
kernel: kernel/time/hrtimer.c:ktime_add_safe,__hrtimer_start_range_ns; include/linux/ktime.h:ktime_set; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46
rocq-twin: nanosleep_clock_near_envelope_clamps -/
theorem nanosleep_clock_near_envelope_clamps (o : outcome SyscallEffect) :
    nanosleep_spec 8192 0 (nanosleep_input 0 ts_1s) (clock_model (2 ^ 63 - 1000000000)) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model (2 ^ 63 - 1)) []
      ∨ o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] [])) (clock_model (2 ^ 63 - 1000000000)) [] := by
  sys_norm

/-- MODEL-INTERNAL STATE — the control for the case above.  The same
one-second sleep against a clock two seconds below the ceiling does NOT
clamp: the sum fits, `ktime_add_safe`'s test (kernel/time/hrtimer.c:348, Linux v6.18.46)
does not fire, and the recorded value is the plain `prev + request`.  The
`iff` refuses every other value, the clamp 2^63 - 1 among them.
kernel: kernel/time/hrtimer.c:ktime_add_safe,__hrtimer_start_range_ns; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46
rocq-twin: nanosleep_clock_below_the_ceiling_does_not_clamp -/
theorem nanosleep_clock_below_the_ceiling_does_not_clamp (o : outcome SyscallEffect) :
    nanosleep_spec 8192 0 (nanosleep_input 0 ts_1s) (clock_model (2 ^ 63 - 2000000000)) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model (2 ^ 63 - 1000000000)) []
      ∨ o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] [])) (clock_model (2 ^ 63 - 2000000000)) [] := by
  sys_norm

/-- MODEL-INTERNAL STATE, and the case that pins WHERE the remainder is
subtracted.  A saturating one-second sleep interrupted with one
microsecond left records 2^63 - 1 - 1000, not `prev + request -
remainder`: the kernel armed `node.expires` at the saturated deadline and
`hrtimer_expires_remaining` measures against THAT
(include/linux/hrtimer.h:159-162, Linux v6.18.46), so the wake time is the saturated
deadline less the remainder — the sleep the kernel ran was shorter than
the one asked for.
kernel: kernel/time/hrtimer.c:ktime_add_safe,do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46
rocq-twin: nanosleep_saturated_deadline_less_the_remainder -/
theorem nanosleep_saturated_deadline_less_the_remainder :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model (2 ^ 63 - 2000))
      (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_1us)] []))
          (clock_model (2 ^ 63 - 1001)) []) := by
  sys_norm

/-- The whole call for a one-second request against a clock 2000 ns below
the top of `ktime_t`, `rmtp` writable: the completed sleep carries the clock
to the saturated deadline 2^63 - 1 (`ktime_add_safe`,
kernel/time/hrtimer.c:348-349, Linux v6.18.46), or an -EINTR writes one admitted remainder
with the clock at THAT deadline less it, floored where it stood.  Nothing
else — not the unsaturated sum, which no `ktime_t` holds.
kernel: kernel/time/hrtimer.c:ktime_add_safe,__hrtimer_start_range_ns,do_nanosleep,nanosleep_copyout; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46 -/
theorem nanosleep_saturating_sleep_at_a_writable_rmtp_admits_both_outcomes
    (o : outcome SyscallEffect) :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model (2 ^ 63 - 2000)) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model (2 ^ 63 - 1)) []
      ∨ ∃ rem : List byte,
          o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, rem)] []))
                (with_clock (nanosleep_clock (Z_to_bv 64 (2 ^ 63 - 2000)) ts_1s rem)
                  (clock_model (2 ^ 63 - 2000))) []
          ∧ nanosleep_rem_ok_b rem = true := by
  sys_norm

/-- Subtracting BEFORE clamping would leave 2^63 - 1 outright and lose the
microsecond: refused.  `hrtimer_expires_remaining` measures against the
saturated `node.expires` (include/linux/hrtimer.h:159-162), so the
microsecond comes off the deadline, not off the sum.
kernel: kernel/time/hrtimer.c:ktime_add_safe,do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining@v6.18.46 -/
theorem nanosleep_saturated_deadline_subtracted_before_the_clamp_rejected :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model (2 ^ 63 - 2000))
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_1us)] []))
            (clock_model (2 ^ 63 - 1)) []) := by
  intro h
  sys_refute at h

/-- MODEL-INTERNAL STATE — the floor, in its SECOND form.  A saturating
sleep interrupted with a quarter second left leaves `KTIME_MAX - 250000000`,
which is BELOW a clock sitting 1000 ns from the ceiling; the clock holds
where it was rather than stepping back a quarter second.  Nothing else
separates the floor at `prev` from a floor at 0: with the clock at 0 the
two agree.
kernel: kernel/time/hrtimer.c:ktime_add_safe,do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46
rocq-twin: nanosleep_saturated_deadline_never_steps_the_clock_back -/
theorem nanosleep_saturated_deadline_never_steps_the_clock_back :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model (2 ^ 63 - 1000))
      (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
          (clock_model (2 ^ 63 - 1000)) []) := by
  sys_norm

/-- The whole call against a clock a microsecond below the top of `ktime_t`,
`rmtp` writable: the completed sleep records the saturated deadline, or an
-EINTR writes one admitted remainder with the clock floored where it stood
whenever `KTIME_MAX` less the remainder falls below it.  Nothing else.
kernel: kernel/time/hrtimer.c:ktime_add_safe,__hrtimer_start_range_ns,do_nanosleep,nanosleep_copyout; include/linux/hrtimer.h:hrtimer_expires_remaining; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46 -/
theorem nanosleep_sleep_a_microsecond_below_the_ceiling_admits_both_outcomes
    (o : outcome SyscallEffect) :
    nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model (2 ^ 63 - 1000)) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model (2 ^ 63 - 1)) []
      ∨ ∃ rem : List byte,
          o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, rem)] []))
                (with_clock (nanosleep_clock (Z_to_bv 64 (2 ^ 63 - 1000)) ts_1s rem)
                  (clock_model (2 ^ 63 - 1000))) []
          ∧ nanosleep_rem_ok_b rem = true := by
  sys_norm

/-- The clock does not run backwards: `KTIME_MAX - 250000000` is below a
clock a microsecond from the ceiling, and CLOCK_MONOTONIC never decreases,
so the stepped-back reading is refused.
kernel: kernel/time/hrtimer.c:do_nanosleep; include/linux/hrtimer.h:hrtimer_expires_remaining@v6.18.46 -/
theorem nanosleep_saturated_deadline_stepping_the_clock_back_rejected :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model (2 ^ 63 - 1000))
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
            (clock_model (2 ^ 63 - 1 - 250000000)) []) := by
  intro h
  sys_refute at h

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and the REJECTION the
decline used to cost: near the ceiling the old spec answered `Unmodeled`
for EVERY effect, so it refused nothing there.  With the clamp in place
the same -EINTR reporting a remainder of exactly zero is REFUSED at a
clock near the ceiling, exactly as it is at a clock of 0.
kernel: kernel/time/hrtimer.c:do_nanosleep@v6.18.46
rocq-twin: nanosleep_near_the_ceiling_zero_remainder_rejected -/
theorem nanosleep_near_the_ceiling_zero_remainder_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model (2 ^ 63 - 1000000000))
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [(4096, ts_zero)] [])) m' evs) := by
  intro h
  sys_refute at h

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the mirror of the case
above, at the ceiling.  A completed sleep that also writes a remainder is
refused near the envelope too.
kernel: kernel/time/hrtimer.c:do_nanosleep@v6.18.46
rocq-twin: nanosleep_near_the_ceiling_completed_sleep_with_a_remainder_rejected -/
theorem nanosleep_near_the_ceiling_completed_sleep_with_a_remainder_rejected (m' : Model)
    (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model (2 ^ 63 - 1000000000))
        (Ok (with_copyins [(8192, 16)] (mkEffect 0 [(4096, ts_250ms)] [])) m' evs) := by
  intro h
  sys_refute at h

/-! ## The ledger: the request is read on every path

`get_timespec64` runs before the call decides anything
(kernel/time/hrtimer.c:2194, Linux v6.18.46), so every outcome has consumed the sixteen
bytes at `rqtp`. -/

/-- An effect that is otherwise the accepted completed sleep, but claims
to have decided without reading the request, describes a kernel that
cannot exist.  Without this case the `record_copyins` in `nanosleep_spec`
would be unfalsifiable from the example side.
kernel: kernel/time/hrtimer.c:nanosleep; kernel/time/time.c:get_timespec64@v6.18.46
rocq-twin: nanosleep_missing_copyin_rejected -/
theorem nanosleep_missing_copyin_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 0 (nanosleep_input 0 ts_1s) (clock_model 0)
        (Ok (mkEffect 0 [] []) m' evs) := by
  intro h
  sys_refute at h

/-- And the ledger has to name the REQUEST.  Sixteen bytes recorded at
`rmtp` — the remainder destination, which `nanosleep` writes and never
reads — is the right width at the wrong address, and is refused for that
alone.
kernel: kernel/time/hrtimer.c:nanosleep; kernel/time/time.c:get_timespec64@v6.18.46
rocq-twin: nanosleep_copyin_at_the_wrong_pointer_rejected -/
theorem nanosleep_copyin_at_the_wrong_pointer_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 4096 (nanosleep_input 4096 ts_1s) (clock_model 0)
        (Ok (with_copyins [(4096, 16)] (mkEffect 0 [] [])) m' evs) := by
  intro h
  sys_refute at h

/-! ## A non-NULL `rmtp` that cannot be written: the one decline past a valid request

Linux answers -EFAULT there HAVING CONSUMED THE SLEEP: `put_timespec64`'s
copy to user space (kernel/time/time.c:911, Linux v6.18.46) fails in `nanosleep_copyout`
(kernel/time/hrtimer.c:2103-2104) at the end of `do_nanosleep`, after the
timer ran, and on a
destination straddling into an unwritable page the copy routine leaves
the bytes it managed written.  The model does not describe a torn struct
and declines the shape before the sleep. -/

/-- A remainder destination straddling into the unwritable page at 4112
declines, for every outcome.  A COVERAGE GAP, NOT AN EMPTY INTERSECTION,
and a declared one: a completed sleep really answers 0 there without
touching `rmtp`, and the model gives that answer up to keep the
interrupted path's torn write out of what it describes.
kernel: kernel/time/hrtimer.c:do_nanosleep,nanosleep_copyout; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem nanosleep_unwritable_remainder_is_unmodeled (o : outcome SyscallEffect) :
    nanosleep_spec 8192 4104 (nanosleep_input 4104 ts_1s) (clock_model 0) o ↔ o = Unmodeled := by
  sys_norm

/-- Linux's -EFAULT after the sleep is NOT given: the decline admits no
answer.
kernel: kernel/time/hrtimer.c:nanosleep_copyout; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem nanosleep_unwritable_remainder_efault_rejected (m' : Model) (evs : List event) :
    ¬ nanosleep_spec 8192 4104 (nanosleep_input 4104 ts_1s) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  intro h
  sys_refute at h

/-- ...and neither is the 0 a completed sleep really answers there: the
cost of the gate, named.
kernel: kernel/time/hrtimer.c:do_nanosleep@v6.18.46 -/
theorem nanosleep_unwritable_remainder_completed_sleep_rejected :
    ¬ nanosleep_spec 8192 4104 (nanosleep_input 4104 ts_1s) (clock_model 0)
        (Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 1000000000) []) := by
  intro h
  sys_refute at h

/-! ## Universally quantified: the retry loop, and the clock's bound

The three Rocq lemmas of the mirror file and the three `Local Lemma`
helpers they rest on, proved by hand as Rocq proves them, plus one
Lean-only fact about the word encoding.  The helpers rest on the decoders
never reading a negative number,
which is what turns `nanosleep_rem_ok_b`'s bound on the TOTAL into a bound
on `tv_sec` alone. -/

/-- `bytes_le_to_Z` never decodes to a negative number.
rocq-twin: bytes_le_to_Z_nonneg' -/
theorem bytes_le_to_Z_nonneg' (bs : List byte) : 0 ≤ bytes_le_to_Z bs := by
  unfold bytes_le_to_Z
  omega

/-- ...so neither does a `struct timespec` read as nanoseconds.
rocq-twin: timespec_ns_nonneg -/
theorem timespec_ns_nonneg (bs : List byte) : 0 ≤ timespec_ns bs := by
  unfold timespec_ns tv_sec_of tv_frac_of
  have h1 := bytes_le_to_Z_nonneg' (bs.take 8)
  have h2 := bytes_le_to_Z_nonneg' (bs.drop 8)
  omega

/-- ...nor the `ktime_t` `ktime_set` makes of it.
rocq-twin: timespec_ktime_nonneg -/
theorem timespec_ktime_nonneg (bs : List byte) : 0 ≤ timespec_ktime bs := by
  unfold timespec_ktime
  split
  · exact timespec_ns_nonneg bs
  · decide

/-- A 64-bit word made from an integer in range reads back as that
integer: the step every bound on `nanosleep_clock` goes through.
model: a fact about `Z_to_bv` and `bv_unsigned`, the model's own encoding. -/
theorem bv_unsigned_Z_to_bv_of_range (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    bv_unsigned (Z_to_bv 64 z) = z := by
  have h64 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  have hlt : z.toNat < 2 ^ 64 := by
    have := Int.toNat_of_nonneg h0
    have h64n : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
    omega
  unfold bv_unsigned Z_to_bv
  rw [← Int.toNat_of_nonneg h0, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- UNIVERSALLY QUANTIFIED, and the machine-checkable proxy for the one
thing `nanosleep_clock`'s docstring claims: that what it records is a
LOWER bound on the real `CLOCK_MONOTONIC`.  The real clock is not a term in
this development; what IS expressible is the model-side half, and this is
that half: the recorded clock never runs past the deadline the kernel
armed, `min (prev + timespec_ktime req) KTIME_MAX`.  It is also the step the
spec's "the FIRST saturation is not load-bearing" argument rests on:
NOTHING of the shape `min _ KTIME_MAX` exceeds `KTIME_MAX`, which is the
armed deadline throughout the saturating band.  A fact about one call,
not an invariant of the model, as the Rocq twin says.
rocq-twin: nanosleep_clock_at_most_the_armed_deadline -/
theorem nanosleep_clock_at_most_the_armed_deadline (prev : word) (req rem : List byte)
    (hprev : bv_unsigned prev ≤ KTIME_MAX) :
    bv_unsigned (nanosleep_clock prev req rem)
      ≤ min (bv_unsigned prev + timespec_ktime req) KTIME_MAX := by
  have hk := timespec_ktime_nonneg req
  have hr := timespec_ns_nonneg rem
  have hp : 0 ≤ bv_unsigned prev := by unfold bv_unsigned; omega
  have hmax : KTIME_MAX = 9223372036854775807 := by decide
  have h64 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  have hmin_right := Int.min_le_right (bv_unsigned prev + timespec_ktime req) KTIME_MAX
  have hmin_left := Int.min_le_left (bv_unsigned prev + timespec_ktime req) KTIME_MAX
  have hle_min : bv_unsigned prev ≤ min (bv_unsigned prev + timespec_ktime req) KTIME_MAX :=
    Int.le_min.mpr ⟨by omega, hprev⟩
  have hmax_le : max (bv_unsigned prev)
      (min (bv_unsigned prev + timespec_ktime req) KTIME_MAX - timespec_ns rem)
      ≤ min (bv_unsigned prev + timespec_ktime req) KTIME_MAX :=
    Int.max_le.mpr ⟨hle_min, by omega⟩
  have hmax_ge := Int.le_max_left (bv_unsigned prev)
    (min (bv_unsigned prev + timespec_ktime req) KTIME_MAX - timespec_ns rem)
  unfold nanosleep_clock
  rw [bv_unsigned_Z_to_bv_of_range _ (by omega) (by omega)]
  exact hmax_le

/-- UNIVERSALLY QUANTIFIED — the corollary `nanosleep_spec` needs to carry
no envelope gate of its own.  A clock inside the band
`Kernel.Time.PosixTimers.clock_gettime_spec` ANSWERS in is still inside
it after any sleep, whatever the request and whatever the remainder,
because the deadline is clamped at `KTIME_MAX` and that is
`CLOCK_NS_ENVELOPE - 1`.  Without this a sleep could park `m_clock` where
the very next monotonic read declines.
rocq-twin: nanosleep_clock_under_the_envelope -/
theorem nanosleep_clock_under_the_envelope (prev : word) (req rem : List byte)
    (hprev : bv_unsigned prev < CLOCK_NS_ENVELOPE) :
    bv_unsigned (nanosleep_clock prev req rem) < CLOCK_NS_ENVELOPE := by
  have hmax : KTIME_MAX = 9223372036854775807 := by decide
  have henv : CLOCK_NS_ENVELOPE = 9223372036854775808 := by decide
  have hle : bv_unsigned prev ≤ KTIME_MAX := by omega
  have h := nanosleep_clock_at_most_the_armed_deadline prev req rem hle
  have hmin := Int.min_le_right (bv_unsigned prev + timespec_ktime req) KTIME_MAX
  omega

/-- UNIVERSALLY QUANTIFIED, and the pinning test for the retry loop.
EVERY remainder this spec may write is a request the same spec JUDGES:
given the destination the loop reuses, no `rem` that `nanosleep_rem_ok_b`
admits can make the next call decline.  The two hypotheses are the
loop's own — `while (nanosleep(&ts, &ts) == -1 && errno == EINTR);`
passes the remainder back as the request through the same pointer, so
the destination it hands the second call is one the first call already
found writable; the disjunction covers the other spelling, where `rmtp`
is NULL and no remainder is reported at all.  THE STATEMENT IS A
NON-DECLINE, not an acceptance, on purpose: what it rules out is the
third verdict, the one that escapes through the equivalence's unmodeled
arm and takes the whole program's `modeled` status with it.  Rocq states
it over the executable checker; the Lean tree has none, so it is stated
on the relation.
kernel: kernel/time/hrtimer.c:nanosleep,do_nanosleep@v6.18.46
rocq-twin: nanosleep_admissible_remainder_is_a_judged_request -/
theorem nanosleep_admissible_remainder_is_a_judged_request
    (i : SyscallInput) (rqtp rmtp : word) (m : Model) (rem : List byte)
    (hread : read_bytes_map i.in_mem rqtp (Z_to_bv 64 16) = some rem)
    (hrem : nanosleep_rem_ok_b rem = true)
    (hdest : w_is0 rmtp = true ∨ read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) ≠ none) :
    ¬ nanosleep_spec rqtp rmtp i m Unmodeled := by
  have hvalid : timespec_valid_b rem = true := by
    have h63 : (2 : Int) ^ 63 = 9223372036854775808 := by decide
    have henv : CLOCK_NS_ENVELOPE = 9223372036854775808 := by decide
    have hnn := bytes_le_to_Z_nonneg' (rem.drop 8)
    -- `decide … = true` is read to its proposition BEFORE the fields are
    -- unfolded: unfolding first changes the proposition under `decide`
    -- while its `Decidable` instance still names the folded field, and
    -- `decide_eq_true_eq` then no longer matches.
    simp only [nanosleep_rem_ok_b, Bool.and_eq_true, decide_eq_true_eq] at hrem
    simp only [timespec_valid_b, Bool.and_eq_true, decide_eq_true_eq]
    unfold timespec_ns tv_sec_of tv_frac_of at hrem
    unfold tv_sec_of tv_frac_of
    omega
  intro h
  unfold nanosleep_spec at h
  simp only [bind_input_iff, hread, hvalid, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte] at h
  cases hw : w_is0 rmtp with
  | true =>
    simp only [hw, ↓reduceIte] at h
    sys_refute at h
  | false =>
    cases hr : read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) with
    | none =>
      rcases hdest with hz | hd
      · rw [hz] at hw
        cases hw
      · exact hd hr
    | some ws =>
      simp only [hw, Bool.false_eq_true, ↓reduceIte, hr] at h
      sys_refute at h

/-! ## The dispatcher

Syscall 101 reaches `nanosleep_spec` with a0 and a1 as its two pointers,
raw (`arch/riscv/kernel/syscall_table.c (Linux v6.18.46)` through `__NR_nanosleep`); a2..a5
are carried as 7 here, and the answer does not depend on them. -/

/-- Through the dispatcher, the NULL-`rmtp` call admits exactly the two
outcomes `nanosleep_null_rmtp_admits_both_outcomes` names.
kernel: include/uapi/asm-generic/unistd.h:__NR_nanosleep; kernel/time/hrtimer.c:nanosleep,do_nanosleep; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46 -/
theorem sysno_101_is_nanosleep (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 101 [8192, 0, 7, 7, 7, 7] (bytes_at 8192 ts_1s) wmem_ts)
        (clock_model 0) o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (clock_model 1000000000) []
      ∨ o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] [])) (clock_model 0) [] := by
  sys_norm

/-- ...and a1 is the remainder pointer, a0 the request: with a0 = 8192
naming 2^63 seconds and a1 = 4096, the dispatcher answers the -EINVAL of
`nanosleep_request_at_two_to_the_63_is_einval`, for every model.
kernel: include/uapi/asm-generic/unistd.h:__NR_nanosleep; kernel/time/hrtimer.c:nanosleep; include/linux/time64.h:timespec64_valid; include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
theorem sysno_101_reads_a0_as_the_request (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 101 [8192, 4096, 7, 7, 7, 7] (bytes_at 8192 ts_neg_sec) wmem_ts)
        m o ↔
      o = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) m [] := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.Hrtimer
