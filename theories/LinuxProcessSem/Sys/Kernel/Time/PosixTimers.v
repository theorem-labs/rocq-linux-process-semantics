(** * LinuxProcessSem.Sys.Kernel.Time.PosixTimers — clock_gettime (113), clock_getres (114)

    This file answers to Linux [kernel/time/posix-timers.c]: it holds
    what the kernel defines there, and nothing else.  Which file a spec
    belongs in is therefore not a judgement call — look up where the
    kernel defines the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi Uaccess.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** WHY [Uapi.CLOCK_NS_ENVELOPE] BOUNDS THIS CLOCK.  The envelope is a
    fact about [ktime_t]'s range; that a [CLOCK_MONOTONIC] reading stays
    inside it is a fact about the path [clock_gettime] takes, and that
    path does not materialize a [ktime_t] at all:
    [posix_get_monotonic_timespec] calls [ktime_get_ts64]
    (kernel/time/timekeeping.c), which fills the [timespec64] directly
    from [tk->xtime_sec] plus [wall_to_monotonic] via
    [timespec64_add_ns], and then [timens_add_monotonic] adds the time
    namespace's offset.  That last one is a [static inline] in
    include/linux/time_namespace.h — NOT kernel/time/namespace.c, which
    holds the offset's WRITE path instead — and is byte-identical at
    v6.10-v6.15, compiling to an empty body when CONFIG_TIME_NS is off.

    Both the clock and that offset are signed 64-bit nanosecond counts,
    and the offset is bounded where it is SET, by
    [proc_timens_set_offset] (kernel/time/namespace.c, byte-identical
    across the range): it refuses an offset whose [tv_sec] exceeds
    [KTIME_SEC_MAX], and then refuses again unless the resulting
    [tv_sec] is at or below [KTIME_SEC_MAX / 2] — the halving is
    deliberate, and the comment beside it says why, "to be sure that
    KTIME_MAX is still unreachable".  So the sum a
    [struct __kernel_timespec] can report cannot exceed 2^63
    nanoseconds — about 292 years.  The bound is a kernel fact rather
    than a modeling convenience.

    It is also what keeps [Uapi.tv_sec_of]/[Uapi.tv_frac_of] in the
    non-negative range: at [t < 2^63] both [t / 10^9] and [t mod 10^9]
    are non-negative, so neither field of the timespec is ever an [s64]
    the kernel could not have produced.

    The bound on [m_clock] is tested SEPARATELY in each of the three
    layers — here, in [Checks/Sys/Kernel/Time/PosixTimers.check_clock_gettime]
    and in [Checks/Witness/Kernel/Time/PosixTimers.clock_gettime_witness]
    — and that repetition is structural rather than an oversight.  The
    acceptor and the witness are verified AGAINST this spec, by the four
    soundness/completeness lemmas and by [clock_gettime_witness_ok];
    they may not import its reasoning, or the proofs would be circular
    and a wrong guard would agree with itself.  Each layer therefore
    restates the test and the lemmas are what force the three to
    coincide.  Contrast the per-reading conditions, which ARE shared:
    [timespec_ok_b] is one definition used by name in all three places,
    because a reading is checked against a value rather than deciding
    whether a layer runs at all. *)

(** What a [CLOCK_MONOTONIC] reading of [bs], following a previous
    reading of [prev], must satisfy.  Defined ONCE and used by name by
    [clock_gettime_spec], by the acceptor and by the witness, so that a
    later change to the conditions cannot prove one thing and execute
    another.  Four conditions:

    - EXACTLY 16 BYTES — the size of the struct the kernel writes.
    - [tv_nsec] IS NORMALIZED, below 10^9.  On this path the
      normalization is [timespec64_add_ns] (include/linux/time64.h),
      which carries whole seconds out of the nanosecond field as it
      adds, and — under CONFIG_TIME_NS — [set_normalized_timespec64]
      (kernel/time/time.c) reached from [timens_add_monotonic].  (NOT
      [ktime_to_timespec64], which is a macro alias for
      [ns_to_timespec64] and belongs to the [.clock_get_ktime] path
      [clock_gettime] never calls.)  So a kernel never writes a
      nanosecond field at or above a full second.  This is the
      condition that makes the two fields a unique reading rather than
      one of many spellings of the same instant.
    - THE READING DOES NOT PRECEDE [prev] — [CLOCK_MONOTONIC]'s whole
      guarantee.  Non-strict: the clock never runs backwards, but it is
      not required to advance between two reads, and a coarse
      clocksource really does answer two quick calls alike.
    - THE READING IS BELOW [CLOCK_NS_ENVELOPE], so it is a time
      [ktime_t] can represent. *)
Definition timespec_ok_b (bs : list byte) (prev : word) : bool :=
  Nat.eqb (length bs) 16
  && (tv_frac_of bs <? 1000000000)%Z
  && (bv_unsigned prev <=? timespec_ns bs)%Z
  && (timespec_ns bs <? CLOCK_NS_ENVELOPE)%Z.

(** What a [CLOCK_REALTIME] reading of [bs] must satisfy.  It is
    [timespec_ok_b] MINUS ONE CONJUNCT, and the missing one is the
    point of this definition: there is no [prev].

    THE WALL CLOCK CARRIES NO GUARANTEE IN EITHER DIRECTION, so there
    is nothing to relate this reading to and no model field to record
    it in.  Two writers settle that, and neither needs the modeled
    process to do anything:

    - [do_settimeofday64] (kernel/time/timekeeping.c) refuses NOTHING
      for setting the wall clock EARLIER.  Its only ordering check is
      [timespec64_compare(&tks->wall_to_monotonic, &ts_delta) > 0],
      which is -EINVAL — the wall clock may not be set below
      CLOCK_MONOTONIC — and that is a floor at the boot instant, not a
      ratchet at the last reading.  Between any two readings the clock
      may be set anywhere above that floor, backwards included.
    - [adjtimex]'s [ADJ_SETOFFSET] reaches
      [timekeeping_inject_offset] (same file), which adds a SIGNED
      [struct timespec64] straight from userspace, subject only to a
      normalized [tv_nsec], the same [wall_to_monotonic] floor, and
      [timespec64_valid_settod] on the result.  A negative offset is
      exactly how NTP steps the clock backwards.

    (Both are byte-identical at v6.13-v6.15; the v6.10-v6.12 spellings
    take the timekeeper lock by hand and hold an explicit [ret] instead
    of using [scoped_guard] and [timekeeping_restore_shadow], with the
    same two -EINVAL conditions and the same writes.  All of it holds
    on the linux-6.10.y through linux-6.15.y stable branches too.)

    A FIELD WRITTEN BY THE SPEC AND READ BY NOTHING WOULD BE WORSE
    THAN NONE: it would look like a guarantee the model does not have.
    So the reading is chosen per call, against this predicate alone,
    and [clock_gettime_spec]'s [CLOCK_REALTIME] arm leaves the model
    UNCHANGED — pinned as a [forall] in
    [Checks/Cases/Kernel/Time/PosixTimers.v].

    What is left is what one reading, on its own, must look like:

    - EXACTLY 16 BYTES, as above.
    - [tv_nsec] IS NORMALIZED, below 10^9.  [posix_get_realtime_timespec]
      is [ktime_get_real_ts64] (kernel/time/timekeeping.c,
      byte-identical at v6.10-v6.15), which sets [tv_nsec] to 0 and
      then normalizes with [timespec64_add_ns].
    - THE READING IS BELOW [CLOCK_NS_ENVELOPE].  The wall clock is
      settable, but only through writers that pass
      [timespec64_valid_settod] (include/linux/time64.h, byte-identical
      at v6.10-v6.15), which rejects a negative [tv_sec], a [tv_nsec]
      outside [[0, 10^9)], and a [tv_sec] at or above
      [TIME_SETTOD_SEC_MAX] — [KTIME_SEC_MAX] LESS thirty years, the
      headroom the comment beside it says is there so a reasonable
      uptime cannot carry the clock past what [ktime_t] holds.  So a
      settable clock reported by [ktime_get_real_ts64] still fits in
      the same 2^63 ns envelope [ktime_t] gives the monotonic one, and
      the same split argument keeps both fields non-negative. *)
Definition realtime_ok_b (bs : list byte) : bool :=
  Nat.eqb (length bs) 16
  && (tv_frac_of bs <? 1000000000)%Z
  && (timespec_ns bs <? CLOCK_NS_ENVELOPE)%Z.

(** What a [CLOCK_PROCESS_CPUTIME_ID] reading of [bs] must satisfy.  It
    is [realtime_ok_b] with the envelope moved onto the SIGNED reading
    and made TWO-SIDED, and that one change is the point of this
    definition.

    THIS IS NOT A CLOCK.  It is a count of CPU the thread group has
    CONSUMED, and every step of the path says so.  [clock_gettime]
    resolves id 2 through [posix_clocks], whose
    [[CLOCK_PROCESS_CPUTIME_ID] = &clock_process]
    (kernel/time/posix-timers.c); [clock_process]'s
    [.clock_get_timespec] is [process_cpu_clock_get], which is one
    line, [posix_cpu_clock_get(PROCESS_CLOCK, tp)], with
    [#define PROCESS_CLOCK make_process_cpuclock(0, CPUCLOCK_SCHED)];
    [posix_cpu_clock_get] takes the [!CPUCLOCK_PERTHREAD] branch to
    [cpu_clock_sample_group(CPUCLOCK_SCHED, tsk, false)]; and
    [store_samples] fills that slot with the scheduler's
    [sum_exec_runtime] — [samples[CPUCLOCK_SCHED] = rtime], where
    [samples[CPUCLOCK_PROF] = stime + utime] is the sum of user and
    system time this id never selects (kernel/time/posix-cpu-timers.c).
    Every one of those — [posix_clocks], [clock_process],
    [process_cpu_clock_get], [PROCESS_CLOCK], [posix_cpu_clock_get],
    [cpu_clock_sample_group] and [store_samples] — is byte-identical
    across mainline v6.10-v6.15 and across the 6.10.y through 6.15.y
    stable branches.

    IT CANNOT FAIL, which is why the arm below has no error path other
    than the destination gate.  [posix_cpu_clock_get]'s only [-EINVAL]
    is a NULL task, and [pid_for_clock] cannot return one for this id:
    [CPUCLOCK_WHICH(PROCESS_CLOCK)] is [CPUCLOCK_SCHED], below
    [CPUCLOCK_MAX], and [CPUCLOCK_PID(PROCESS_CLOCK)] is 0, so it takes
    the [upid == 0] branch and answers [task_tgid(current)] without
    looking anything up.

    A NEGATIVE [tv_sec] IS A SHAPE THIS ID REALLY EMITS, which is why
    the envelope has to move.  Nothing clamps the sample:
    [thread_group_cputime] (kernel/sched/cputime.c) accumulates
    [read_sum_exec_runtime(t)] over [for_each_thread] on top of
    [sig->sum_sched_runtime] in a [u64], and a thread group running on
    several CPUs burns CPU faster than any clock advances.  What
    happens when that [u64] passes 2^63 is not undefined and not an
    error: [ns_to_timespec64] (kernel/time/time.c, byte-identical at
    v6.10-v6.15 and on the matching stable branches) takes an [s64],
    and HAS A BRANCH FOR IT — the [nsec < 0] case, reached exactly when
    the sample has bit 63 set, writes a NEGATIVE [tv_sec] and keeps
    [tv_nsec] positive.  So [realtime_ok_b]'s
    [timespec_ns bs <? CLOCK_NS_ENVELOPE], which reads [tv_sec]
    UNSIGNED, would reject a conforming kernel here.  The other two
    arms may read it unsigned because a kernel writer keeps their
    quantity non-negative — [timespec64_valid_settod] for the wall
    clock, [ktime_t] itself for the monotonic one.  Nothing does that
    for a count of nanoseconds burned.

    WHAT IS LEFT IS THE SAME ENVELOPE, READ THE WAY THE KERNEL READS
    IT, and it is exact rather than cautious: [ns_to_timespec64] is a
    BIJECTION from the [s64] it is handed onto the timespecs below,
    so the four conjuncts admit every reading a kernel can produce here
    and nothing else.

    - EXACTLY 16 BYTES, the [struct __kernel_timespec] the syscall
      writes; the same argument as on the other two arms.
    - [tv_nsec] IS NORMALIZED, below 10^9, on all three branches: the
      zero case leaves the [{ 0, 0 }] initializer, the [nsec > 0] case
      takes [div_u64_rem(nsec, NSEC_PER_SEC, &rem)]'s remainder, and
      the [nsec < 0] case computes [NSEC_PER_SEC - rem - 1], which the
      comment beside it says is kept positive on purpose.
    - THE SIGNED TOTAL IS AN [s64] NUMBER OF NANOSECONDS, at or above
      [-CLOCK_NS_ENVELOPE] and below it.  That is the argument the
      whole [u64] sample fits in, and it is two-sided for the one
      reason: the argument is signed, so the bottom of its range is a
      real bound and not a formality.  It also does the work
      [timespec_ns bs <? CLOCK_NS_ENVELOPE] does on the other arms —
      an absurd [tv_sec] cannot present itself as a small admissible
      count, in either direction. *)
Definition cputime_ok_b (bs : list byte) : bool :=
  Nat.eqb (length bs) 16
  && (tv_frac_of bs <? 1000000000)%Z
  && (- CLOCK_NS_ENVELOPE <=? timespec_ns_signed bs)%Z
  && (timespec_ns_signed bs <? CLOCK_NS_ENVELOPE)%Z.

(** The clock ids answered PER CALL, against [realtime_ok_b] alone — no
    model field read, none written, each call's reading independently
    arbitrary.  [CLOCK_REALTIME] is here for [realtime_ok_b]'s reason:
    the kernel guarantees NOTHING across two wall-clock readings, so
    there is nothing to record.  The other four DO carry cross-call
    guarantees in the kernel, and the model deliberately states NONE of
    them — each is a strict over-approximation of exactly the kind the
    CPU-time arm already takes: every reading a kernel can produce is
    admitted, so no conforming trace is rejected, and the price is the
    CPU-time arm's price, that a program whose OUTPUT depends on the
    value it read cannot be proved equivalent to anything.  Per id, what
    is deliberately not said, and why saying it against [m_clock] would
    be wrong anyway:

    - [CLOCK_MONOTONIC_RAW] (4): [ktime_get_raw_ts64]
      (kernel/time/timekeeping.c) — the monotonic clock WITHOUT NTP
      frequency correction.  Monotone in the kernel, but a DIFFERENT
      quantity from what [m_clock] records: NTP slews the adjusted clock
      both faster and slower than the raw one, so no inequality between
      a raw reading and the recorded [CLOCK_MONOTONIC] reading is a
      kernel fact in either direction.
    - [CLOCK_REALTIME_COARSE] (5): [ktime_get_coarse_real_ts64] (same
      file) — the wall clock as of the last tick.  Everything
      [realtime_ok_b] says about the wall clock's absence of guarantees
      applies verbatim, with up to a tick of staleness on top.
    - [CLOCK_MONOTONIC_COARSE] (6): [ktime_get_coarse_ts64] (same file)
      — the monotonic clock as of the last tick.  Monotone in the
      kernel, but a coarse reading may PRECEDE a fine-grained reading
      already recorded in [m_clock], so constraining it against that
      field would reject conforming traces.
    - [CLOCK_BOOTTIME] (7): [ktime_get_boottime_ts64] (same file) — the
      monotonic clock PLUS time spent suspended.  It never precedes the
      monotonic clock, but the two are read at different instants and
      the model has no suspend accounting, so the inequality it does
      carry relates nothing the model can state.

    Not modeling their cross-call monotonicity is a CHOICE, not an
    oversight: recording four more clock fields would buy proofs about
    programs whose behavior depends on values this model already makes
    unprovable the moment they are consulted, at the cost of four more
    envelope gates of the kind the monotonic arm needs to stay
    receptive.  A later change that needs, say, BOOTTIME monotonicity
    can split its id out of this set the way [CLOCK_MONOTONIC] already
    is.

    The per-reading conditions ARE [realtime_ok_b]'s, and that is a
    kernel fact five times over: every one of these paths writes a
    16-byte [struct __kernel_timespec], normalizes [tv_nsec] below 10^9
    ([timespec64_add_ns] on the fine paths; the coarse pair copies a
    timekeeper field that was stored normalized), and reports a
    [ktime_t]-representable non-negative time, so the same three
    conjuncts admit every reading any of them can produce.

    THE SCOPE, as on the CPU-time arm: [CLOCK_BOOTTIME] is answered on
    both sides of the [CONFIG_POSIX_TIMERS] gate
    (kernel/time/posix-stubs.c serves REALTIME, MONOTONIC and BOOTTIME);
    the raw and coarse ids, like [CLOCK_PROCESS_CPUTIME_ID], are
    answered only with the option on. *)
Definition clockid_percall_b (clkid : word) : bool :=
  Z.eqb (bv_unsigned clkid) CLOCK_REALTIME
  || Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC_RAW
  || Z.eqb (bv_unsigned clkid) CLOCK_REALTIME_COARSE
  || Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC_COARSE
  || Z.eqb (bv_unsigned clkid) CLOCK_BOOTTIME.

(** [clock_gettime clkid tp]: read a clock into a [struct timespec].

    SEVEN IDS ARE MODELED, IN THREE ARMS THAT ARE NOT FOLDED TOGETHER.
    [CLOCK_MONOTONIC] (1), [CLOCK_REALTIME] (0) and
    [CLOCK_PROCESS_CPUTIME_ID] (2) are different quantities carrying
    different guarantees, and each arm below says only what its own
    quantity promises; [CLOCK_MONOTONIC_RAW] (4), [CLOCK_REALTIME_COARSE]
    (5), [CLOCK_MONOTONIC_COARSE] (6) and [CLOCK_BOOTTIME] (7) share the
    wall-clock arm through [clockid_percall_b], whose header carries the
    argument that the sharing attaches nothing: that arm states only
    per-reading facts every one of its five ids satisfies, and no
    cross-call relation at all.  Each arm changes exactly one thing from
    the one above it, and every change is a kernel fact:

    - a MONOTONIC reading is constrained against the previous one, by
      [timespec_ok_b], and RECORDED in [m_clock];
    - a WALL-CLOCK reading DROPS the relation to the previous reading
      and is constrained per call, by [realtime_ok_b] alone, leaving
      the model exactly as it found it.  [CLOCK_REALTIME] is settable
      and can jump in either direction under
      [settimeofday]/[clock_settime] and NTP, so it is not monotone at
      all — [realtime_ok_b] carries the two writers that settle it, and
      what they leave is a floor at the boot instant rather than a
      ratchet at the last reading;
    - a CPU-TIME reading MOVES the 2^63 ns envelope, by [cputime_ok_b],
      onto the SIGNED reading of the struct and makes it two-sided.
      The envelope is not dropped — it is the same 2^63, applied the
      way [ns_to_timespec64] applies it.  [cputime_ok_b] carries why.

    Sharing one arm — or one model field — between any two of those
    three would attach a guarantee to a quantity that does not have it.
    The per-call ids can share theirs because it attaches none.

    MODELING [CLOCK_REALTIME] IS WHAT MAKES A LIBC [gettimeofday]
    MODELED, which is why it is here rather than left with the other
    ids.  musl's [gettimeofday] (src/time/gettimeofday.c, musl 1.2.6)
    is [clock_gettime(CLOCK_REALTIME, &ts)]
    followed by a divide by 1000, and issues syscall 169 on NO
    architecture — so dropbear's three call sites (src/dbrandom.c,
    src/loginrec.c, src/dbutil.c) arrive here, at 113 with id 0.

    MODELING [CLOCK_PROCESS_CPUTIME_ID] (2) IS WHAT MAKES A LIBC
    [clock()] MODELED, and it is here for that reason, alongside the
    one above.  musl's [clock] (src/time/clock.c, musl 1.2.6) is
    [clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts)] followed by a
    convert to microseconds, so dropbear's [seedrandom]
    (src/dbrandom.c at v2026.94) arrives here, at 113 with id 2, BEFORE
    the server has accepted anything.  It is also the ONE modeled id a
    real machine cannot serve out of the vDSO —
    [__cvdso_clock_gettime_common] answers only the ids in
    [VDSO_HRES | VDSO_COARSE | VDSO_RAW] and no CPU clock is in any of
    them — so it is the only one a LIBC call reaches the kernel
    through on hardware, the other six being absorbed before the
    syscall is made.

    IT IS A DIFFERENT QUANTITY FROM BOTH OTHERS, AND IT GETS NO MODEL
    FIELD.  [m_clock] is elapsed monotonic nanoseconds; this is
    nanoseconds of CPU the thread group has burned.  Answering either
    out of the other would be a confident wrong answer of exactly the
    kind the fail-closed rule exists to forbid — and so, for the same
    reason, would answering a [CLOCK_REALTIME] read out of [m_clock].

    So the reading is chosen per call against [cputime_ok_b] alone,
    and, as on the wall-clock arm, an accepted call leaves the model
    UNCHANGED.  The reason is not the wall clock's: nothing about this
    quantity is settable.  It is that THE MODEL HAS NO NOTION OF WORK
    DONE, so there is nothing here for a reading to be related to —
    not the previous reading, and not [m_clock], which measures
    elapsed time rather than CPU consumed and is related to it by no
    inequality this model could state (a thread group on several CPUs
    burns CPU faster than the clock runs, and one that is not
    scheduled burns none at all).  Relating it to nothing is a STRICT
    OVER-APPROXIMATION: every reading a kernel can produce is
    admitted, whatever a kernel does or does not guarantee across
    calls, so no conforming trace is rejected.  It costs the same as
    the wall clock's arm costs — a program whose output depends on the
    value it read cannot be proved equivalent to anything — and it is
    of a piece with the over-approximation the monotonic arm already
    takes, where the clock does not advance for work either.

    A FIELD FOR IT WOULD BE WORSE THAN NONE, for the reason
    [realtime_ok_b] gives: it could only be written and never usefully
    read, and would look like a guarantee the model does not have.
    THE KERNEL DOES NOT MAKE THAT GUARANTEE, which is the second
    reason not to state it and the reason not to state its negation
    either.  The value IS non-decreasing in the implementation, but
    only as the conclusion of an argument over four separate
    mechanisms — the [delta_exec <= 0] guard in [update_curr_se], the
    [write_seqlock(&sig->stats_lock)] section in [__exit_signal] that
    moves a dying thread's runtime into [sig->sum_sched_runtime]
    before unhashing it, [__sched_fork] zeroing a new thread's
    counter, and [update_gt_cputime]'s per-field max when a
    process-wide timer arms and moves reads from the live walk to
    [cputimer.cputime_atomic].  Upstream states none of that as a
    contract: no comment, no [WARN_ON] and no test asserts it for this
    id, and the read path carries NO defensive filter, unlike
    [cputime_adjust], which has one for [utime]/[stime] and whose
    comment calls a non-monotonic [sum_exec_runtime] "a bug".

    A WRONG INFERENCE TO AVOID, because it is an easy one to reach.
    It is tempting to say
    the value is "NOT NON-DECREASING" and use that as a second reason
    to decline the id, on the grounds that
    [cpu_clock_sample_group] reads the live sum while
    [!pct->timers_active] and the cached [cputime_atomic] once timers
    are armed, and that the cache omits the slice running at the moment
    of the switch.  It cannot move backwards:
    [__update_gt_cputime] returns early on
    [sum_cputime <= curr_cputime] and otherwise raises the value by
    [cmpxchg], so [cputime_atomic] is a monotone max and activation can
    only lift what is reported.  What the omission produces is a STALE
    reading, not a backwards one — [thread_group_cputime]'s own comment
    says it deliberately skips the pending time of other running tasks
    on other CPUs — and a sum that omits work still only accumulates.

    Modeling it as a guarantee would be claiming more than Linux
    does; modeling its negation would be claiming a step this code
    does not take.  Claiming neither is the honest option, and it is
    free, because the model has nothing to relate the reading to
    anyway.

    That is NOT the monotonic arm's situation, though its
    non-decreasing constraint rests on a reading of five mechanisms
    below and so looks like the same move made the other way.  The
    difference is what the reading is ABOUT: [CLOCK_MONOTONIC] is
    REQUIRED to be non-decreasing, so those mechanisms are how the
    kernel KEEPS a promise it has made, where the same reading here
    would establish a property the next patch may break without
    breaking anything it owes.

    THE SCOPE, named rather than assumed: this arm describes a kernel
    built with [CONFIG_POSIX_TIMERS].  Without it [posix_cpu_clock_get]
    is not built at all and [do_clock_gettime]
    (kernel/time/posix-stubs.c, byte-identical at v6.10-v6.15) answers
    -EINVAL for every id but REALTIME, MONOTONIC and BOOTTIME.  Those
    three modeled ids are answered on BOTH sides of that gate; this one
    is not, and neither are the raw and coarse ids on the per-call arm
    ([clockid_percall_b]'s header restates the split), so which modeled
    ids answer depends on that kernel config option.

    EVERY OTHER ID IS [unmodeled], fail closed.  The [_COARSE] ids in
    particular are not answered by analogy with the MONOTONIC arm.
    That arm's non-decreasing conjunct leans below on the anti-step
    compensation in [timekeeping_apply_adjustment] — the
    [xtime_nsec -= offset] that pairs with a slope change — and the
    coarse getters never applied it, which is exactly what let
    [CLOCK_MONOTONIC_COARSE] step backwards.  A coarse reading is
    non-decreasing at the cited tree only because of b71f9804f66c
    ("timekeeping: Prevent coarse clocks going backwards", v6.15-rc6),
    which added [tk->coarse_nsec] (include/linux/timekeeper_internal.h)
    to carry that compensation for the coarse path too.  Stable
    [linux-6.12.y] has not taken that fix as of v6.12.105 and
    [linux-6.14.y] took it at v6.14.7, measured by the presence of
    [coarse_nsec] at each tag.  So a coarse arm would rest on a
    guarantee younger than the clock, and needs its own argument, read
    at the cited tree, rather than this one's.

    ORDER.  The id is decoded FIRST, as Linux does, so a bad id beats
    a bad pointer and the model's decline sits where the kernel's
    -EINVAL does.  Cited below.

    WHAT THE ENVIRONMENT CHOOSES, ON THE MONOTONIC ARM.  The reading is
    the environment's, constrained only to be NON-DECREASING and inside
    [CLOCK_NS_ENVELOPE].  Non-decreasing rather than strictly
    increasing, and BOTH halves of that are kernel facts rather than
    caution.

    IT NEVER GOES BACKWARDS, against each mechanism that could
    plausibly move it.  MONOTONIC is [xtime + wall_to_monotonic], and
    [do_settimeofday64] edits the pair together —
    [tk_set_wall_to_mono(tk, wall_to_monotonic - ts_delta)] against
    [tk_set_xtime(tk, ts)] — so a settimeofday cancels exactly, and
    [tk_set_wall_to_mono] touches neither [tkr_mono.mult] nor
    [cycle_last]; [accumulate_nsecs_to_secs] pairs the same way for a
    leap second.

    (THE SPELLING, not the behaviour, moves inside the window: the
    v6.13-v6.15 form of [do_settimeofday64] passes the shadow
    timekeeper and uses [scoped_guard] with
    [timekeeping_restore_shadow], where v6.10-v6.12 takes the timekeeper
    lock by hand and holds an explicit [ret].  The shadow variable does
    not exist before v6.13 at all.  Same two -EINVAL conditions and the
    same writes either way, so the argument above is unaffected — but
    "byte-identical across v6.10-v6.15" would be false of these
    functions, and is not claimed.)

    NTP slewing changes the SLOPE only: [timekeeping_apply_adjustment]
    does [tkr_mono.mult += mult_adj] together with
    [tkr_mono.xtime_nsec -= offset], the second line being the anti-step
    compensation.  It runs on the SHADOW timekeeper and is published
    atomically afterwards, which is what makes it invisible to a reader
    mid-update — at v6.10 [timekeeping_adjust] is called eight lines
    BEFORE [write_seqcount_begin(&tk_core.seq)] opens the section that
    then copies the shadow across, and at v6.13 its caller has no
    [write_seqcount_begin] at all, publishing through
    [timekeeping_update_from_shadow] instead.  So the guarantee is
    shadow-then-publish rather than "inside the write section".

    Suspend stops the clock rather than jumping it —
    [__timekeeping_inject_sleeptime] adds the sleep to xtime and
    subtracts it from [wall_to_monotonic], so REALTIME and BOOTTIME
    advance across a suspend and MONOTONIC does not.  And a backwards
    COUNTER read is clamped rather than propagated:
    [timekeeping_cycles_to_ns] returns [xtime_nsec >> shift] when the
    masked delta has the mask's MSB set — but only inside
    [if (unlikely(delta > tkr->clock->max_cycles))], so the MSB test is
    necessary and not sufficient, and an ordinary small delta never
    reaches it.  Time stalls but never steps back.

    IT IS NOT REQUIRED TO ADVANCE, for two separate reasons, which is
    why the model must not demand a strict increase: two reads inside
    one counter tick return the identical value — on riscv the counter
    is [rdtime], about 10 MHz under qemu-virt, so equal consecutive
    readings are ordinary rather than a corner case — and the clamp
    above freezes the clock outright while it is in effect.
    [clock_getres] answering 1 ns does not contradict this: that is
    timer-programming granularity, not a promise that two reads differ.
    Requiring an advance would reject a conforming trace.
    The chosen value is recorded in [m_clock], which is the only reason
    the constraint can be stated at all: it is a relation between this
    call and the previous one, and a per-call [choose] has nothing to
    relate to.

    NOT MODELED, deliberately: the clock does not advance at any OTHER
    syscall, so the model admits traces in which unbounded work happens
    between two readings that return the same nanosecond.  That is a
    strict over-approximation of the reachable set — every real trace
    is still admitted — and it is the honest shape while nothing else
    in the model has a notion of duration.

    ORDER, cited: [clock_gettime] resolves [which_clock] through
    [clockid_to_kclock] and returns -EINVAL for an id with no [k_clock]
    before [tp] is touched, and [put_timespec64] runs only under
    [!error] (kernel/time/posix-timers.c, v6.10-v6.15).

    THE DESTINATION GATE declines rather than answering -EFAULT, and it
    declines a WIDER band than its reason strictly covers.  The reason
    is the partial case: a 16-byte [tp] straddling into an unmapped
    page keeps its first bytes and still reports -EFAULT, because
    [put_timespec64]'s [copy_to_user] reaches riscv64's
    [__asm_copy_to_user] (arch/riscv/lib/uaccess.S), which copies
    forward and whose fixup returns bytes-not-copied — so there is no
    single answer the model could commit to.  A WHOLLY unwritable [tp]
    is not like that: Linux answers -EFAULT having written nothing, and
    [read_spec] does commit to -EFAULT in exactly that shape.  It is
    folded into the same decline anyway, for uniformity with
    [getrandom_spec]'s whole-buffer gate, which takes the same decision.
    The cost is coverage on a shape the model could have answered. *)
Definition clock_gettime_spec (clkid tp : word) : Sys SyscallEffect :=
  if clockid_percall_b clkid then
    (* THE PER-CALL IDS, WHICH THE MODEL DOES NOT REMEMBER.  No
       [get_model], no [set_clock] and no relation to any earlier
       reading: [realtime_ok_b] carries the argument that the wall
       clock has nothing to relate to, and [clockid_percall_b] the
       argument that relating the other four to nothing is a strict
       over-approximation taken on purpose.  The destination gate and
       the effect shape are the monotonic arm's, for the monotonic
       arm's reasons. *)
    i <- input ;;
    match read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) with
    | None => unmodeled   (* destination not fully writable: fail closed *)
    | Some _ =>
        bs <- choose (fun bs : list byte => realtime_ok_b bs = true) ;;
        pure (mkEffect (Z_to_bv 64 0) [(tp, bs)] [])
    end
  else if Z.eqb (bv_unsigned clkid) CLOCK_PROCESS_CPUTIME_ID then
    (* CPU CONSUMED, WHICH THE MODEL CANNOT HAVE AN OPINION ABOUT.  The
       wall-clock arm's shape exactly — no [get_model] and no
       [set_clock] — under a predicate of its own: [cputime_ok_b]
       carries both the argument that there is nothing to relate a
       count of nanoseconds burned to, and the envelope, which is
       moved rather than dropped.  The destination gate and the effect
       shape are the monotonic arm's, for the monotonic arm's
       reasons. *)
    i <- input ;;
    match read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) with
    | None => unmodeled   (* destination not fully writable: fail closed *)
    | Some _ =>
        bs <- choose (fun bs : list byte => cputime_ok_b bs = true) ;;
        pure (mkEffect (Z_to_bv 64 0) [(tp, bs)] [])
    end
  else if negb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC) then unmodeled
  else
  m <- get_model ;;
  if negb (Z.ltb (bv_unsigned (m_clock m)) CLOCK_NS_ENVELOPE) then unmodeled
    (* the recorded clock has left the range [ktime_t] can represent.
       Unreachable from [init_model] — the origin is 0 and this is the
       only arm of this spec that writes [m_clock], under a predicate
       that holds it below the envelope — but [Progress.receptive]
       quantifies over ARBITRARY model states, not reachable ones, and
       the choice below would be empty here.  Declining keeps the spec
       receptive without inventing a reading. *)
  else
  i <- input ;;
  match read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) with
  | None => unmodeled   (* destination not fully writable: fail closed *)
  | Some _ =>
      bs <- choose (fun bs : list byte => timespec_ok_b bs (m_clock m) = true) ;;
      set_clock (Z_to_bv 64 (timespec_ns bs)) ;;
      pure (mkEffect (Z_to_bv 64 0) [(tp, bs)] [])
  end.

(** Positive clock IDs handled by [clock_getres].  IDs 8 and 9 can fail
    with -EINVAL when no alarm RTC is available.  The CPU clocks (2, 3)
    have a fixed 1 ns resolution.  For the others Linux returns either
    [hrtimer_resolution] or [KTIME_LOW_RES]; QEMU forwards the host's
    [clock_getres].  A positive normalized subsecond value covers these
    configurations without fixing the host kernel's HZ.  This deliberately
    leaves the exact resolution unspecified, like other environment time
    values in this model.  Negative dynamic clock IDs and optional auxiliary
    clocks remain unmodeled. *)
Definition clock_getres_supported_b (clkid : word) : bool :=
  (bv_unsigned clkid <=? CLOCK_BOOTTIME_ALARM)%Z
  || Z.eqb (bv_unsigned clkid) CLOCK_TAI.

Definition clock_getres_alarm_b (clkid : word) : bool :=
  Z.eqb (bv_unsigned clkid) CLOCK_REALTIME_ALARM
  || Z.eqb (bv_unsigned clkid) CLOCK_BOOTTIME_ALARM.

Definition clock_getres_cpu_b (clkid : word) : bool :=
  Z.eqb (bv_unsigned clkid) CLOCK_PROCESS_CPUTIME_ID
  || Z.eqb (bv_unsigned clkid) CLOCK_THREAD_CPUTIME_ID.

Definition clock_getres_resolution_b (clkid : word) (bs : list byte) : bool :=
  Nat.eqb (length bs) 16
  && Z.eqb (tv_sec_of bs) 0
  && (if clock_getres_cpu_b clkid
      then Z.eqb (tv_frac_of bs) 1
      else (0 <? tv_frac_of bs)%Z && (tv_frac_of bs <? 1000000000)%Z).

Definition clock_getres_dst_ok_b (i : SyscallInput) (tp : word) : bool :=
  if w_is0 tp then
    match read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) with
    | Some _ => false
    | None => true
    end
  else match read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) with
       | Some _ => true
       | None => false
       end.

Definition clock_getres_result_spec (clkid tp : word) : Sys SyscallEffect :=
  if w_is0 tp then ret_only (Z_to_bv 64 0)
  else
    bs <- choose (fun bs : list byte =>
      clock_getres_resolution_b clkid bs = true) ;;
    pure (mkEffect (Z_to_bv 64 0) [(tp, bs)] []).

(** The clock is resolved before the destination is touched.  Linux skips
    the copy for NULL [tp]; QEMU attempts it but ignores the copy's return.
    If guest address zero is writable, QEMU can write there, so that input
    is declined.  A partially writable non-NULL destination is declined,
    as in [clock_gettime_spec]. *)
Definition clock_getres_spec (clkid tp : word) : Sys SyscallEffect :=
  if clock_getres_supported_b clkid then
    i <- input ;;
    if clock_getres_dst_ok_b i tp then
      if clock_getres_alarm_b clkid
      then alt (err_ret EINVAL) (clock_getres_result_spec clkid tp)
      else clock_getres_result_spec clkid tp
    else unmodeled
  else if Z.eqb (bv_unsigned clkid) CLOCK_SGI_CYCLE then err_ret EINVAL
  else unmodeled.
