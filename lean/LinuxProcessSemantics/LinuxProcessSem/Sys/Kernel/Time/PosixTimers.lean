-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Sys/Kernel/Time/PosixTimers.v

import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi


-- The `rocq-baseline` below is the upstream port's own; this file's source
-- of truth is the `Ports` line at the top.
/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Kernel.Time.PosixTimers — clock_gettime (113)

Mirrors `theories/LinuxProcessSem/Sys/Kernel/Time/PosixTimers.v`.  This
file answers to Linux `kernel/time/posix-timers.c`: it holds what the
kernel defines there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Kernel/Time/PosixTimers.lean`.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
Rocq's own comments cite these functions over a v6.10-v6.15 window with no
line numbers; every line number below was read at v6.18.46 and is labelled
so, and where the v6.18.46 tree spells a function differently from that
window the docstring says what moved.

Two spellings differ from Rocq without changing a value.  Rocq's
`Z.eqb`/`Z.ltb`/`Z.leb` gates are Lean's decidable `=`, `<`, `≤` on `Int`,
coerced to `Bool` where the Rocq definition is a `bool`, and `Nat.eqb` on
the length is `==`; and Rocq's `negb (Z.ltb a b)` guard on the recorded
clock is spelled `¬ (a < b)`.  The `unmodeled` sites are Rocq's five, none
added and none removed: the id decline, the recorded-clock gate, and the
destination gate on each of the three arms.  The destination `match`es are
parenthesized because `tools/lean_mutate.py`'s reader counts `if`/`else` at
bracket depth and refuses a `match` at an `if`'s own depth inside a
then-arm — the first two sit in one; the third sits in the else-arm of the
recorded-clock `if`, which the reader accepts either way, and is
parenthesized for uniformity.  The parentheses change nothing. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.PosixTimers

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- What a `CLOCK_MONOTONIC` reading of `bs`, following a previous reading
of `prev`, must satisfy.  Defined ONCE and used by name by
`clock_gettime_spec` and by every pin, so that a later change to the
conditions cannot prove one thing and check another.  The argument in
full — why `Uapi.CLOCK_NS_ENVELOPE` bounds this clock, and why the four
conditions are kernel facts rather than caution — is on the Rocq
definition `PosixTimers.timespec_ok_b` and the header above it; what
follows is the kernel line each conjunct rests on, read at Linux v6.18.46
(commit 1f99e9ab748f).

- EXACTLY 16 BYTES: `struct __kernel_timespec` is two 8-byte fields
  (include/uapi/linux/time_types.h:7-10), and `put_timespec64`
  (kernel/time/time.c:903-912) copies `sizeof(kts)` of it.
- `tv_nsec` IS NORMALIZED, below 10^9.  `posix_get_monotonic_timespec`
  (kernel/time/posix-timers.c:217-222, v6.18.46) is `ktime_get_ts64` then
  `timens_add_monotonic`.  `ktime_get_ts64` (kernel/time/timekeeping.c:955-975, v6.18.46)
  sets `ts->tv_nsec = 0` and normalizes with `timespec64_add_ns`
  (include/linux/time64.h:163-167, v6.18.46), which carries whole seconds out of the
  nanosecond field as it adds; `timens_add_monotonic`
  (include/linux/time_namespace.h:74-79, v6.18.46, under `CONFIG_TIME_NS`, an empty
  body at :162 without it) adds the namespace offset through
  `timespec64_add` (include/linux/time64.h, v6.18.46), which normalizes through
  `set_normalized_timespec64` (kernel/time/time.c:495-514, v6.18.46).  So a kernel
  never writes a nanosecond field at or above a full second.
- THE READING DOES NOT PRECEDE `prev` — `CLOCK_MONOTONIC`'s whole
  guarantee, argued mechanism by mechanism on `clock_gettime_spec`.
  Non-strict: the clock is not required to advance between two reads.
- THE READING IS BELOW `CLOCK_NS_ENVELOPE`, so it is a time `ktime_t`
  (`typedef s64 ktime_t`, include/linux/types.h:126, v6.18.46) can represent.  The
  namespace offset cannot carry it past that: `proc_timens_set_offset`
  (kernel/time/namespace.c:383-461, v6.18.46) refuses an offset whose `tv_sec`
  exceeds `KTIME_SEC_MAX` (:418-419) and then refuses again unless the
  resulting `tv_sec` is at or below `KTIME_SEC_MAX / 2` (:427), "to be
  sure that KTIME_MAX is still unreachable". -/
def timespec_ok_b (bs : List byte) (prev : word) : Bool :=
  bs.length == 16
  && (tv_frac_of bs < 1000000000)
  && (bv_unsigned prev ≤ timespec_ns bs)
  && (timespec_ns bs < CLOCK_NS_ENVELOPE)

/-- What a `CLOCK_REALTIME` reading of `bs` must satisfy: `timespec_ok_b`
MINUS the relation to a previous reading, because the wall clock carries
no guarantee in either direction and there is nothing to relate it to.
The argument in full is on the Rocq definition `PosixTimers.realtime_ok_b`;
the two writers that settle it, read at Linux v6.18.46 (commit
1f99e9ab748f):

- `do_settimeofday64` (kernel/time/timekeeping.c:1434-1465) refuses
  nothing for setting the wall clock EARLIER.  Its only ordering check,
  `timespec64_compare(&tks->wall_to_monotonic, &ts_delta) > 0` → -EINVAL,
  is a floor at the boot instant, not a ratchet at the last reading.
- `adjtimex`'s `ADJ_SETOFFSET` reaches `__timekeeping_inject_offset`
  (kernel/time/timekeeping.c:1480-1520, v6.18.46, through `timekeeping_inject_offset`
  :1522-1533 and `do_adjtimex`), which adds a SIGNED `struct timespec64`
  straight from userspace, subject only to a normalized `tv_nsec`, the
  same `wall_to_monotonic` floor and `timespec64_valid_settod` on the
  result.  (At v6.18.46 the function is split into a core-timekeeper arm
  and an auxiliary-clock arm; the core arm is the one described, and the
  aux arm never touches `CLOCK_REALTIME`.)

What is left is what one reading must look like on its own:

- EXACTLY 16 BYTES, as on `timespec_ok_b`.
- `tv_nsec` IS NORMALIZED: `posix_get_realtime_timespec`
  (kernel/time/posix-timers.c:194-198, v6.18.46) is `ktime_get_real_ts64`
  (kernel/time/timekeeping.c:793-811), which sets `tv_nsec` to 0 and
  normalizes with `timespec64_add_ns`.
- THE READING IS BELOW `CLOCK_NS_ENVELOPE`: every writer of the wall
  clock passes `timespec64_valid_settod` (include/linux/time64.h:118-126, v6.18.46),
  which rejects a negative `tv_sec`, a `tv_nsec` outside `[0, 10^9)` (via
  `timespec64_valid`, :97-106) and a `tv_sec` at or above
  `TIME_SETTOD_SEC_MAX` (:44) — `KTIME_SEC_MAX` (:32) less thirty years
  (`TIME_UPTIME_SEC_MAX`, :43), the headroom the comment beside it says is
  there so a reasonable uptime cannot carry the clock past what
  `ktime_t` holds. -/
def realtime_ok_b (bs : List byte) : Bool :=
  bs.length == 16
  && (tv_frac_of bs < 1000000000)
  && (timespec_ns bs < CLOCK_NS_ENVELOPE)

/-- What a `CLOCK_PROCESS_CPUTIME_ID` reading of `bs` must satisfy:
`realtime_ok_b` with the envelope moved onto the SIGNED reading and made
two-sided, because this is not a clock but a `u64` count of CPU consumed,
and `ns_to_timespec64` writes a NEGATIVE `tv_sec` once that count passes
2^63.  The argument in full is on the Rocq definition
`PosixTimers.cputime_ok_b`; the path, read at Linux v6.18.46 (commit
1f99e9ab748f):

`clock_gettime` resolves id 2 through `posix_clocks`
(kernel/time/posix-timers.c:1518-1533, `[CLOCK_PROCESS_CPUTIME_ID] =
&clock_process` at :1521).  `clock_process`
(kernel/time/posix-cpu-timers.c:1719-1724) names `process_cpu_clock_get`
(:1675-1679), one line: `posix_cpu_clock_get(PROCESS_CLOCK, tp)` with
`PROCESS_CLOCK` = `make_process_cpuclock(0, CPUCLOCK_SCHED)` (:1667).
`posix_cpu_clock_get` (:358-379) takes the `!CPUCLOCK_PERTHREAD` branch to
`cpu_clock_sample_group(clkid, tsk, false)` (:374), and `store_samples`
(:214-219) fills the `CPUCLOCK_SCHED` slot with the scheduler's
`sum_exec_runtime` (`samples[CPUCLOCK_SCHED] = rtime`, :218), never the
`stime + utime` of the `CPUCLOCK_PROF` slot (:216).

IT CANNOT FAIL: the only `-EINVAL` in `posix_cpu_clock_get` is a NULL
task (:365-369), and `pid_for_clock` (:57-95) cannot return NULL for this
id — `CPUCLOCK_WHICH(PROCESS_CLOCK)` is `CPUCLOCK_SCHED`, below
`CPUCLOCK_MAX` (:63-64), and `CPUCLOCK_PID(PROCESS_CLOCK)` is 0, so the
`upid == 0` branch (:70-71) answers `task_tgid(current)` without a lookup.
The `pid_task(…, PIDTYPE_TGID)` step beside it (:365) then finds the group
leader, which stays attached to that pid until the whole group is dead:
`__unhash_process` (kernel/exit.c:134-154, v6.18.46) detaches `PIDTYPE_TGID` only
under `group_dead` (:144-145), and the calling thread is alive.

A NEGATIVE `tv_sec` IS A SHAPE THIS ID REALLY EMITS.  Nothing clamps the
sample: `thread_group_cputime` (kernel/sched/cputime.c:313-353, v6.18.46) accumulates
`read_sum_exec_runtime(t)` over `for_each_thread` (:342-346) on top of
`sig->sum_sched_runtime` (:340) in a `u64`, and `ns_to_timespec64`
(kernel/time/time.c:523-542, v6.18.46) takes an `s64` and HAS A BRANCH for bit 63:
the `nsec < 0` case (:531-539) writes `tv_sec = -div_u64_rem(-nsec - 1,
NSEC_PER_SEC, &rem) - 1` and keeps `tv_nsec = NSEC_PER_SEC - rem - 1`
positive.  `realtime_ok_b`'s unsigned reading would reject that conforming
kernel, and the other two arms may read `tv_sec` unsigned only because a
kernel writer keeps their quantity non-negative.

The four conjuncts are the same envelope read the way the kernel reads it,
and exact: `ns_to_timespec64` is a bijection from the `s64` it is handed
onto the timespecs below.

- EXACTLY 16 BYTES, as on the other arms.
- `tv_nsec` IS NORMALIZED on all three branches of `ns_to_timespec64`:
  the zero case leaves the `{ 0, 0 }` initializer, the `nsec > 0` case
  takes `div_u64_rem`'s remainder, the `nsec < 0` case computes
  `NSEC_PER_SEC - rem - 1`.
- THE SIGNED TOTAL IS AN `s64` NUMBER OF NANOSECONDS, at or above
  `-CLOCK_NS_ENVELOPE` and below it: the argument the whole `u64` sample
  fits in, two-sided because the argument is signed. -/
def cputime_ok_b (bs : List byte) : Bool :=
  bs.length == 16
  && (tv_frac_of bs < 1000000000)
  && (- CLOCK_NS_ENVELOPE ≤ timespec_ns_signed bs)
  && (timespec_ns_signed bs < CLOCK_NS_ENVELOPE)

/-- The clock ids answered PER CALL, against `realtime_ok_b` alone — no
model field read, none written, each call's reading independently
arbitrary.  `CLOCK_REALTIME` is here for `realtime_ok_b`'s reason: the
kernel guarantees NOTHING across two wall-clock readings, so there is
nothing to record.  The other four DO carry cross-call guarantees in the
kernel, and the model deliberately states NONE of them — each is a strict
over-approximation of the kind the CPU-time arm already takes: every
reading a kernel can produce is admitted, so no conforming trace is
rejected, and the price is that a program whose OUTPUT depends on the
value it read cannot be proved equivalent to anything.  The argument in
full is on the Rocq definition `PosixTimers.clockid_percall_b`
(f1006fe8, `Sys/Kernel/Time/PosixTimers.v:233-296`); per id, what is
deliberately not said:

- `CLOCK_MONOTONIC_RAW` (4): `ktime_get_raw_ts64`
  (kernel/time/timekeeping.c) — the monotonic clock WITHOUT NTP frequency
  correction.  Monotone in the kernel, but a DIFFERENT quantity from what
  `m_clock` records: NTP slews the adjusted clock both faster and slower
  than the raw one, so no inequality between a raw reading and the
  recorded `CLOCK_MONOTONIC` reading is a kernel fact in either
  direction.
- `CLOCK_REALTIME_COARSE` (5): `ktime_get_coarse_real_ts64` (same file) —
  the wall clock as of the last tick.  Everything `realtime_ok_b` says
  about the wall clock's absence of guarantees applies verbatim, with up
  to a tick of staleness on top.
- `CLOCK_MONOTONIC_COARSE` (6): `ktime_get_coarse_ts64` (same file) — the
  monotonic clock as of the last tick.  Monotone in the kernel, but a
  coarse reading may PRECEDE a fine-grained reading already recorded in
  `m_clock`, so constraining it against that field would reject
  conforming traces.
- `CLOCK_BOOTTIME` (7): `ktime_get_boottime_ts64` (same file) — the
  monotonic clock PLUS time spent suspended.  It never precedes the
  monotonic clock, but the two are read at different instants and the
  model has no suspend accounting, so the inequality it does carry
  relates nothing the model can state.

The per-reading conditions ARE `realtime_ok_b`'s, and that is a kernel
fact five times over: every one of these paths writes a 16-byte
`struct __kernel_timespec`, normalizes `tv_nsec` below 10^9
(`timespec64_add_ns` on the fine paths; the coarse pair copies a
timekeeper field that was stored normalized), and reports a
`ktime_t`-representable non-negative time.

THE SCOPE, as on the CPU-time arm: `CLOCK_BOOTTIME` is answered on both
sides of the `CONFIG_POSIX_TIMERS` gate (kernel/time/posix-stubs.c serves
REALTIME, MONOTONIC and BOOTTIME); the raw and coarse ids, like
`CLOCK_PROCESS_CPUTIME_ID`, are answered only with the option on. -/
def clockid_percall_b (clkid : word) : Bool :=
  bv_unsigned clkid == CLOCK_REALTIME
  || bv_unsigned clkid == CLOCK_MONOTONIC_RAW
  || bv_unsigned clkid == CLOCK_REALTIME_COARSE
  || bv_unsigned clkid == CLOCK_MONOTONIC_COARSE
  || bv_unsigned clkid == CLOCK_BOOTTIME

/-- `clock_gettime clkid tp` (113): read a clock into a
`struct __kernel_timespec`.  SEVEN ids are modeled, in three arms that
are not folded together — `CLOCK_MONOTONIC` (1),
`CLOCK_PROCESS_CPUTIME_ID` (2) and the five per-call ids of
`clockid_percall_b` (0, 4, 5, 6, 7) are different quantities carrying
different guarantees, and each arm says only what its own quantity
promises.  The
argument in full — why the wall clock and the CPU count get no model
field, why the raw and coarse ids share the per-call arm and state no
cross-call relation, what the model
deliberately does not say about time passing at other syscalls
(linux-process-semantics@ff0313ba4f:bugs/clock-advances-only-at-clock-gettime.md), the libc calls that arrive
here as ids 0 and 2, and the vDSO asymmetry recorded in
linux-process-semantics@ff0313ba4f:bugs/clock-gettime-served-by-vdso.md — is on the Rocq definition
`PosixTimers.clock_gettime_spec` and is not repeated here.  What follows
is the kernel line each gate rests on, read at Linux v6.18.46 (commit
1f99e9ab748f).

ORDER.  `SYSCALL_DEFINE2(clock_gettime, …)` (kernel/time/posix-timers.c:1136-1152)
resolves `which_clock` through `clockid_to_kclock` (:1535-1548) and returns
-EINVAL for an id with no `k_clock` (:1143-1144) BEFORE `tp` is touched;
`kc->clock_get_timespec` runs next (:1146), and `put_timespec64` runs only
under `!error` (:1148-1149).  So the id is decoded first here too: a bad
id beats a bad pointer, and the model's decline sits where the kernel's
-EINVAL does.  `clockid_to_kclock` sends every NEGATIVE id to
`clock_posix_dynamic` when `(id & CLOCKFD_MASK) == CLOCKFD` and to
`clock_posix_cpu` otherwise (:1539-1542), and every id at or past
`ARRAY_SIZE(posix_clocks)` to NULL (:1544-1545); ids 0..7 index
`posix_clocks` (:1518-1533).  That array is 12 entries long, 24 under
`CONFIG_POSIX_AUX_CLOCKS` (kernel/time/Kconfig:213, v6.18.46; `[CLOCK_AUX ...
CLOCK_AUX_LAST] = &clock_aux`, :1530-1532), and it has NULL holes below
its size that answer -EINVAL through the same `if (!kc)`: `CLOCK_SGI_CYCLE`
(10, include/uapi/linux/time.h:63, v6.18.46, "kept as a place holder") and, with
aux clocks, 12..15; an aux id in range answers -ENODEV until its clock is
enabled (`aux_get_timespec`, kernel/time/timekeeping.c:2907-2910, v6.18.46).  None
of that reaches the seven modeled ids, and every other id declines below.

EVERY OTHER ID IS `unmodeled`, fail closed — including the ones a real
kernel answers (`CLOCK_THREAD_CPUTIME_ID`, `CLOCK_TAI`, the alarm pair).
The `_COARSE` ids are answered on the PER-CALL arm and are NOT answered
by analogy with the monotonic arm: that arm's non-decreasing conjunct
leans on the anti-step compensation in `timekeeping_apply_adjustment`,
and the coarse getters never applied it, which is what let
`CLOCK_MONOTONIC_COARSE` step backwards.  A coarse reading is
non-decreasing at the pinned tree only through `tk->coarse_nsec`
(include/linux/timekeeper_internal.h:154, v6.18.46, which `tk_update_coarse_nsecs`
maintains from `__timekeeping_advance`, kernel/time/timekeeping.c:2308-2367, v6.18.46),
a guarantee younger than the clock.  Stating no cross-call relation for
those ids, as `clockid_percall_b` does, needs no such guarantee.

THE MONOTONIC ARM.  The reading is the environment's, constrained by
`timespec_ok_b` to be NON-DECREASING and inside `CLOCK_NS_ENVELOPE`, and
RECORDED in `m_clock` — the only reason the relation to the previous call
can be stated at all.  Non-decreasing rather than strictly increasing, and
both halves are kernel facts:

IT NEVER GOES BACKWARDS, against each mechanism that could move it.
MONOTONIC is `xtime + wall_to_monotonic`, and `do_settimeofday64`
(kernel/time/timekeeping.c:1434-1465, v6.18.46) edits the pair together —
`tk_set_wall_to_mono(tks, wall_to_monotonic - ts_delta)` against
`tk_set_xtime(tks, ts)` — so a settimeofday cancels to the nanosecond
(`ts_delta` is taken against `tk_xtime`, :202-209, which truncates the
shifted `xtime_nsec`, and `tk_set_xtime`, :234-239, drops the
sub-nanosecond fraction `timekeeping_forward_now`, :765-785, had carried;
a read straddling the publish can therefore land one nanosecond below the
pre-set timekeeper's answer at the same cycle, a deviation from the
documented non-decreasing guarantee that linux-process-semantics@ff0313ba4f:AGENTS.md's rule on
implementation bugs keeps out of the admitted set), and
`tk_set_wall_to_mono` (:249-265) touches neither `tkr_mono.mult` nor
`cycle_last`; `accumulate_nsecs_to_secs` (:2221-2259) pairs the same way
for a leap second.  NTP slewing changes the SLOPE only:
`timekeeping_apply_adjustment` (:2081-2153) does `tkr_mono.mult +=
mult_adj` (:2150) together with `tkr_mono.xtime_nsec -= offset` (:2152),
the anti-step compensation, and runs on the SHADOW timekeeper from
`timekeeping_adjust` (:2159) inside `__timekeeping_advance` (:2308-2367),
which publishes afterwards through `timekeeping_update_from_shadow`
(:708-755, `write_seqcount_begin` at :721) — shadow-then-publish, which is
what makes it invisible to a reader mid-update.  Suspend stops the clock
rather than jumping it: `__timekeeping_inject_sleeptime` (:1857-1870) adds
the sleep to xtime and subtracts it from `wall_to_monotonic`.  And a
backwards COUNTER read is clamped rather than propagated:
`timekeeping_cycles_to_ns` (:378-400) returns `xtime_nsec >> shift` when
the masked delta has the mask's MSB set — but only inside
`if (unlikely(delta > tkr->clock->max_cycles))`, so an ordinary small
delta never reaches it.  Time stalls but never steps back.

IT IS NOT REQUIRED TO ADVANCE: two reads inside one counter tick return
the identical value, and the clamp above freezes the clock while it is in
effect.  Requiring an advance would reject a conforming trace.

THE RECORDED-CLOCK GATE declines when `m_clock` has left the range
`ktime_t` can represent.  Unreachable from `init_model` — the origin is 0
and this is the only arm that writes `m_clock`, under a predicate that
holds it below the envelope — but Rocq's `Progress.receptive` quantifies over
ARBITRARY model states, and the choice below would be empty there.
Declining keeps the spec receptive without inventing a reading.

THE PER-CALL ARM (`clockid_percall_b`: ids 0, 4, 5, 6 and 7) drops the
relation to the previous reading and
is constrained per call by `realtime_ok_b` alone, leaving the model exactly
as it found it: no `get_model`, no `set_clock`.  THE CPU-TIME ARM (id 2)
has the same shape under `cputime_ok_b`; an accepted call leaves the
model unchanged because the model has no notion of work done and there is
nothing for the reading to be related to — a strict over-approximation
that admits every reading a kernel can produce.  Its scope, named rather
than assumed: a kernel built with `CONFIG_POSIX_TIMERS`.  Without it
`posix_cpu_clock_get` is not built and `do_clock_gettime`
(kernel/time/posix-stubs.c:39-58, v6.18.46) answers -EINVAL for every id but
REALTIME, MONOTONIC and BOOTTIME (:53-54).  Those three modeled ids are
answered on both sides of that gate; id 2 and the raw and coarse ids are
not.  A stubs kernel's
-EINVAL is therefore a reading those arms REFUSE rather than decline;
linux-process-semantics@ff0313ba4f:bugs/clock-gettime-served-by-vdso.md's last paragraph records that
residual against the scope rule.

TWO NAMES THE ROCQ ARGUMENT USES HAVE MOVED at v6.18.46, without moving
the argument.  The scheduler guard Rocq names as update_curr_se — the
first of the four mechanisms that keep the CPU count non-decreasing — is
`update_se` (kernel/sched/fair.c:1232-1271, the `delta_exec <= 0` guard at
:1238).  And `__cvdso_clock_gettime_common` (lib/vdso/gettimeofday.c:288-314, v6.18.46),
which answers only the ids in `VDSO_HRES | VDSO_COARSE | VDSO_RAW`, gained
an `else if (msk & VDSO_AUX)` arm (:308) for the auxiliary clocks — still
no CPU clock among them, so id 2 still reaches the kernel from hardware
while ids 0 and 1 are absorbed before the syscall is made
(linux-process-semantics@ff0313ba4f:bugs/clock-gettime-served-by-vdso.md).

THE DESTINATION GATE declines rather than answering -EFAULT, on every arm.
`put_timespec64` (kernel/time/time.c:903-912, v6.18.46) is one `copy_to_user`,
which on riscv64 reaches `__asm_copy_to_user` (arch/riscv/lib/uaccess.S:15-23, v6.18.46)
and its scalar fallback `fallback_scalar_usercopy_sum_enabled` (:56-215),
which copies forward and whose fixup at label `10:` returns bytes-not-copied
(`sub a0, t5, a0`, :212-213); a copy under `9*SZREG-1` = 71 bytes takes
`.Lbyte_copy_tail` (:76-77), byte by byte.  So a 16-byte `tp` straddling
into an unmapped page keeps its first bytes and still reports -EFAULT, and
there is
no single answer the model could commit to.  A WHOLLY unwritable `tp` is
not like that — Linux answers -EFAULT having written nothing — and is
folded into the same decline for uniformity with `getrandom_spec`'s
whole-buffer gate.  The cost is coverage on a shape the model could have
answered. -/
def clock_gettime_spec (clkid tp : word) : Sys SyscallEffect :=
  if clockid_percall_b clkid then
    -- THE PER-CALL IDS, WHICH THE MODEL DOES NOT REMEMBER.
    i <- input ;;
    (match read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with
     | none => unmodeled   -- destination not fully writable: fail closed
     | some _ =>
         bs <- choose (fun bs : List byte => realtime_ok_b bs = true) ;;
         Monad.pure (mkEffect (Z_to_bv 64 0) [(tp, bs)] []))
  else if bv_unsigned clkid = CLOCK_PROCESS_CPUTIME_ID then
    -- CPU CONSUMED, WHICH THE MODEL CANNOT HAVE AN OPINION ABOUT.
    i <- input ;;
    (match read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with
     | none => unmodeled   -- destination not fully writable: fail closed
     | some _ =>
         bs <- choose (fun bs : List byte => cputime_ok_b bs = true) ;;
         Monad.pure (mkEffect (Z_to_bv 64 0) [(tp, bs)] []))
  else if bv_unsigned clkid ≠ CLOCK_MONOTONIC then unmodeled
  else
  m <- get_model ;;
  if ¬ (bv_unsigned (m_clock m) < CLOCK_NS_ENVELOPE) then unmodeled
    -- the recorded clock has left the range `ktime_t` can represent
  else
  i <- input ;;
  (match read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with
   | none => unmodeled   -- destination not fully writable: fail closed
   | some _ =>
       bs <- choose (fun bs : List byte => timespec_ok_b bs (m_clock m) = true) ;;
       set_clock (Z_to_bv 64 (timespec_ns bs)) ;;
       Monad.pure (mkEffect (Z_to_bv 64 0) [(tp, bs)] []))

end LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.PosixTimers
