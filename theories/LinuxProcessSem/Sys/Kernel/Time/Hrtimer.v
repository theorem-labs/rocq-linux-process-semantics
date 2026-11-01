(** * LinuxProcessSem.Sys.Kernel.Time.Hrtimer — nanosleep (101)

    This file answers to Linux [kernel/time/hrtimer.c]: it holds what
    the kernel defines there, and nothing else.  Which file a spec
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

(** What [timespec64_valid] (include/linux/time64.h, byte-identical at
    v6.10-v6.15) accepts, applied to the 16 bytes read out of [rqtp]:

      if (ts->tv_sec < 0) return false;
      if ((unsigned long)ts->tv_nsec >= NSEC_PER_SEC) return false;

    [tv_sec] is signed, so "not negative" is "below 2^63 read
    unsigned"; [tv_nsec] is cast to unsigned before the comparison, so
    a negative nanosecond field fails the same test a too-large one
    does.  A request failing either is -EINVAL, and the model commits
    to that: the kernel writes nothing and returns before it touches
    [rmtp].

    No length conjunct: the only caller applies this to exactly the
    bytes [copy_bytes_map] returned for a 16-byte read. *)
Definition timespec_valid_b (bs : list byte) : bool :=
  (tv_sec_of bs <? 2 ^ 63)%Z
  && (tv_frac_of bs <? 1000000000)%Z.

(** What a remainder the kernel wrote into [rmtp] must satisfy.
    Normalized and strictly positive — and NOT bounded by the request,
    which is the surprising half and is argued at [nanosleep_spec]. *)
Definition nanosleep_rem_ok_b (bs : list byte) : bool :=
  Nat.eqb (length bs) 16
  && (tv_frac_of bs <? 1000000000)%Z
  && (0 <? timespec_ns bs)%Z
  && (timespec_ns bs <? CLOCK_NS_ENVELOPE)%Z.

(** The monotonic clock after a sleep that requested [req] and reported
    remainder [rem].  [rem] is [[]] on the success path, where the whole
    request elapsed — [timespec_ns [] = 0], both fields decoding out of
    an empty byte list as 0.

    Read it as the deadline the kernel actually armed, less what was
    left of it, and never behind where the clock already stood:

      [timespec_ktime req]              the request, as [ktime_set] took it
      [Z.min (prev + that) KTIME_MAX]   the deadline, SATURATING
      [- rem]                           less the reported remainder
      [Z.max prev ...]                  and the clock never runs back

    THE REQUEST SATURATES TWICE, at two different functions, and the
    model needs both.  [hrtimer_nanosleep] is handed a [ktime_t] that
    [SYSCALL_DEFINE2(nanosleep, ...)] built with [timespec64_to_ktime]
    (kernel/time/hrtimer.c and include/linux/ktime.h at v6.18.46),
    which is [ktime_set] and which returns [KTIME_MAX] outright once
    [tv_sec >= KTIME_SEC_MAX] — that is [Uapi.timespec_ktime], and it
    is what makes a request past the ceiling a SLEEP rather than a
    shape to decline.  The absolute expiry then saturates again, at
    [ktime_add_safe], which is the [Z.min] below.

    THE TWO SATURATIONS ARE NOT LOAD-BEARING IN THE SAME WAY, and it is
    worth being exact about which one soundness needs, because getting
    the reason wrong here would license removing the other one.

    THE SECOND IS LOAD-BEARING: without the [Z.min], an ordinary sleep
    against a clock near the ceiling would record a sum [ktime_t]
    cannot hold, and the paragraph below shows the lower bound fails
    outright there.

    THE FIRST IS NOT, and the argument is the [Z.min] rather than any
    comparison between [timespec_ns] and [timespec_ktime] — those two
    do not order the convenient way.  In the band [ktime_set] saturates
    over, the deadline the kernel armed is [KTIME_MAX] exactly: the
    conversion hands [hrtimer_nanosleep] that constant and every add
    after it saturates back to it.  A model that read the request as a
    plain product and clamped afterwards would record
    [Z.min (prev + timespec_ns req) KTIME_MAX], and NO value of that
    shape exceeds [KTIME_MAX], so it would still be at or below the
    armed deadline — a sound lower bound, whichever way the two
    readings of the request happen to compare.

    What [timespec_ktime] buys is EXACTNESS, and only in one place: at
    [tv_sec = KTIME_SEC_MAX] with [tv_nsec] under 854775807 the product
    is BELOW [KTIME_MAX], so the plain-product model would record less
    time than the kernel really armed.  The [Checks/Cases] pair
    [nanosleep_request_at_the_ceiling_sleeps_to_ktime_max] and
    [nanosleep_request_below_the_ceiling_converts] is exactly that gap,
    and [Checks/Cases]'s
    [nanosleep_clock_at_most_the_armed_deadline] is the "no value of
    that shape exceeds [KTIME_MAX]" step, machine-checked.

    THE SATURATION IS THE KERNEL'S, not a modeling convenience.
    [__hrtimer_start_range_ns] (kernel/time/hrtimer.c at v6.18.46)
    turns the relative request into an absolute expiry with

      [if (mode & HRTIMER_MODE_REL)]
      [        tim = ktime_add_safe(tim, __hrtimer_cb_get_time(base->clockid));]

    and [ktime_add_safe] (same file, same tree)
    does NOT report an error when that sum leaves the type: it adds as
    [u64], tests [if (res < 0 || res < lhs || res < rhs)], and on any
    of those replaces the result with [ktime_set(KTIME_SEC_MAX, 0)] —
    which is [KTIME_MAX], for the [>=] reason [Uapi.KTIME_MAX] argues.
    Since both operands are non-negative [ktime_t]s, that test fires
    exactly when the true sum exceeds [KTIME_MAX], so the arm is a
    [Z.min] with [KTIME_MAX] and nothing else.  A sleep whose deadline
    would leave the type therefore SUCCEEDS, at a nearer deadline; it
    does not fail, and it is not a shape the model may decline.

    THE CALL SITE IS STABLE; THE FUNCTION AROUND IT IS NOT, which is
    worth recording because it is what a two-endpoint check misses.
    [__hrtimer_start_range_ns] has had three shapes across the versions
    cited here: byte-identical at v6.10-v6.13, changed for
    v6.14 by commit 2f8dea1692ee ("hrtimers: Handle CPU state correctly
    on hotplug", which adds the offline-CPU handling), and changed
    again by v6.18.46, where [hrtimer_clock_base] no longer carries a
    [get_time] pointer on this path and the reading goes through
    [__hrtimer_cb_get_time(base->clockid)] instead.  None of the three
    touches the [HRTIMER_MODE_REL] branch or the [ktime_add_safe] call
    it feeds, so the argument above holds across all of them — but the
    spec cites v6.18.46 and quotes that tree, not the window.

    WHY THIS IS A SOUND LOWER BOUND, which is the only thing [m_clock]
    claims.  Write [now] for the real monotonic clock when the call
    started and [wake] for when it returned; [prev <= now <= wake].
    Write [k] for the request as a [ktime_t], which is
    [timespec_ktime req]: the syscall converted it with
    [timespec64_to_ktime] before [hrtimer_nanosleep] ever saw it, so
    [k] and not the [timespec] product is what the timer was armed
    from.  [_softexpires] is [ktime_add_safe(now, k) = Z.min (now + k)
    KTIME_MAX].  [node.expires] is that plus a NON-NEGATIVE delta —
    [hrtimer_start_expires] (include/linux/hrtimer.h) hands
    [hrtimer_start_range_ns] the gap between the relative pair
    [hrtimer_nanosleep] set, which is the task's timer slack less
    whatever the relative add itself saturated away — and the delta is
    added with [ktime_add_safe] again.  The exact width does not matter
    to the bound; only that it is non-negative, so
    [node.expires >= _softexpires].  [do_nanosleep] computes the
    remainder as [hrtimer_expires_remaining]
    (include/linux/hrtimer.h), which is [node.expires - now_at_wake],
    so

      [wake = node.expires - rem >= _softexpires - rem]
           [ = Z.min (now + k) KTIME_MAX - rem]
           [>= Z.min (prev + k) KTIME_MAX - rem]

    the last step by [now >= prev] and [Z.min] being monotone.  Taking
    [Z.max] with [prev] keeps the other lower bound [wake >= prev], so
    the recorded value is below the real clock on both arms.

    WITHOUT THE [Z.min] THE BOUND IS FALSE, and not by a rounding
    error.  Once the deadline saturates, the sleep is SHORTER than the
    request — the kernel armed [KTIME_MAX], not [now + k] — so
    recording [prev + k] would claim time that never elapsed and
    would let a later [clock_gettime] reading be rejected for running
    backwards when it did no such thing.  That is a false REJECTION,
    the worse kind.

    [Z.max prev] is load-bearing for two separate reasons, and the
    second is new here.  A remainder may EXCEED the request, by up to
    the task's timer slack, so the subtraction goes negative on an
    ordinary interruption — [nanosleep_spec] argues that at length.
    And once the deadline saturates, [KTIME_MAX - rem] can fall below
    [prev] outright, which is the same subtraction going negative
    against a different quantity.  Both are the clock refusing to run
    backwards.

    THE RESULT STAYS UNDER [CLOCK_NS_ENVELOPE], so this spec cannot
    push [m_clock] into the band
    [Kernel.Time.PosixTimers.clock_gettime_spec] declines on: the value
    is at most [Z.max prev KTIME_MAX], and [KTIME_MAX] is
    [CLOCK_NS_ENVELOPE - 1].  So a model whose clock is below the
    envelope still has one after any sleep, which is what lets this
    file carry no envelope gate of its own. *)
Definition nanosleep_clock (prev : word) (req rem : list byte) : word :=
  Z_to_bv 64
    (Z.max (bv_unsigned prev)
       (Z.min (bv_unsigned prev + timespec_ktime req) KTIME_MAX
        - timespec_ns rem)).

(** [nanosleep rqtp rmtp]: sleep for a relative [struct timespec], and
    on interruption report what was left.

    BOTH OUTCOMES ARE ADMITTED, and that is the decision this spec
    turns on.  The tempting simplification is that the model has no
    signals, so -EINTR cannot arise and the success path is the only
    one.  It does not survive contact with the source: the model does
    not FORBID signals, it says nothing about them, and a real kernel
    running the real program delivers them.  In dropbear specifically
    it does — [sesssigchild_handler] is installed for SIGCHLD in the
    very session process that runs the anti-user-enumeration auth
    delay (src/svr-chansession.c at v2026.94), and the delay is
    [while (nanosleep(&delay, &delay) == -1 && errno == EINTR) {}]
    (src/svr-auth.c).  A model claiming [nanosleep] always succeeds
    would REJECT that conforming trace.  So the environment chooses
    which outcome occurred, exactly as it chooses a short read: an
    [alt] of a completed sleep and an interruption.

    Declining just the interrupted case is not available: whether a
    signal arrived is not a function of the arguments, so there is no
    gate to put it behind, and folding [unmodeled] into the [alt] would
    make EVERY [nanosleep] call unmodeled rather than some of them —
    the same trap [Drivers.Char.Random.getrandom_spec] spells its
    zero-byte arm out to avoid.

    ALIASING IS FINE.  dropbear passes [rqtp == rmtp], the same 16
    bytes as request and remainder.  The kernel reads the request into
    a kernel-local [struct timespec64] with [get_timespec64] before
    anything else, and only writes [rmtp] at the very end, so the write
    cannot disturb the read.  The model has the same order — [req] is
    read out of [in_mem] and the remainder is a separate write entry —
    so nothing special is needed and no gate has to notice the two
    pointers are equal.

    ORDER, following [SYSCALL_DEFINE2(nanosleep, ...)]
    (kernel/time/hrtimer.c, byte-identical at v6.10-v6.15): the
    request is read first ([get_timespec64], -EFAULT), validated
    second ([timespec64_valid], -EINVAL), and only then slept on.
    [rmtp] is NEVER validated up front — a completed sleep with an
    unwritable [rmtp] answers 0 without touching it.  The model keeps
    that for an [rmtp] that [access_ok] refuses, which is answered with
    both outcomes at the remainder's [None] arm below.  It gives the
    rest up by gating on [rmtp] before the [alt] where [access_ok]
    admits the range but it is not wholly mapped.  The cost is
    coverage on a shape the model could have answered; the reason is
    the straddle below.

    THE REQUEST'S CEILING IS JUDGED, not declined.
    [timespec64_to_ktime] is [ktime_set] (include/linux/ktime.h at
    v6.18.46), which returns [KTIME_MAX] outright when
    [secs >= KTIME_SEC_MAX] rather than converting.  A request at or
    above that ceiling is therefore a sleep toward the end of
    [ktime_t] — an ORDINARY interruptible sleep, armed by the same
    [__hrtimer_start_range_ns], waited on by the same [do_nanosleep]
    and broken by the same signal as any other, differing only in the
    deadline it carries.  Linux does not refuse it, so the model does
    not decline it: [Uapi.timespec_ktime] carries the conversion into
    [nanosleep_clock] and both arms answer.  Note where the band sits:
    a [tv_sec] at or past 2^63 reads as negative and is -EINVAL, and
    the band this paragraph is about is the valid one just below it,
    [[KTIME_SEC_MAX, 2^63)].

    WHAT THE MODEL ANSWERS THERE, since "judged" has to name an answer.
    Both arms stay admissible and the environment still chooses.  On an
    interruption [m_clock] moves to [KTIME_MAX] less the reported
    remainder, floored at [prev] — the deadline the kernel really armed
    less what was left of it, exactly as at any other request.  On a
    completed sleep [m_clock] moves to [KTIME_MAX], and the model is
    then claiming the monotonic clock reached the largest value
    [ktime_t] holds; that is what returning 0 from a timer armed at
    [KTIME_MAX] means, and it is sound for the reason every completed
    sleep is — a timer never fires before its soft expiry.  In practice
    that arm is the one no run reaches, since [KTIME_MAX] is 292 years
    of CLOCK_MONOTONIC away.  The model does not say so and does not
    need to: an admissible outcome nothing reaches costs nothing, where
    a decline costs the whole program.

    WHY IT IS NOT DECLINED, which is not a coverage argument.  The
    remainder this spec may WRITE is not bounded by the request, and
    [nanosleep_rem_ok_b] admits any normalized positive [timespec]
    under [CLOCK_NS_ENVELOPE] — [tv_sec = KTIME_SEC_MAX] among them,
    inside that envelope by 854775808 ns.  The standard retry loop
    hands the remainder straight back as the next request:
    [while (nanosleep(&ts, &ts) == -1 && errno == EINTR);], which is
    dropbear's auth delay (src/svr-auth.c) and is quoted above.  So
    with a decline, ONE
    admissible environment choice — interrupt, report
    [{KTIME_SEC_MAX, 0}] — would make the NEXT call [unmodeled].
    [Equivalence.modeled] is the negation of an existential over
    resolutions, so that single resolution would cost the whole program its
    [modeled] status, on every input on which it slept at all.

    THE OTHER FIX IS NOT AVAILABLE.  Bounding the admissible remainder
    by the request would close the loop too, and would be wrong:
    [hrtimer_expires_remaining] measures against [node.expires], which
    [hrtimer_set_expires_range_ns] puts [current->timer_slack_ns] past
    the soft expiry, and [prctl(PR_SET_TIMERSLACK)] (kernel/sys.c) sets
    that field to any nonzero [unsigned long], and an [arg2] of 0
    RESETS to [current->default_timer_slack_ns] rather than setting
    zero.  Neither restriction bounds the slack from above, and the
    value is inherited from the parent rather than derived from
    anything the model can see, so there is nothing to bound it WITH:
    the model carries no timer slack.

    THE CLOCK ADVANCES, and the bound is one-sided on purpose.
    ([hrtimer_nanosleep] and [do_nanosleep] are both in
    kernel/time/hrtimer.c; [do_nanosleep] is byte-identical at
    v6.10-v6.15, [hrtimer_nanosleep] at v6.12-v6.15.  The boundary is
    v6.12 and not v6.13: v6.10 and v6.11 carry
    [slack = current->timer_slack_ns; if (rt_task(current)) slack = 0;]
    and pass [slack], where v6.12 onwards passes
    [current->timer_slack_ns] to [hrtimer_set_expires_range_ns]
    unconditionally.  Those two earlier spellings therefore differ only
    in zeroing the slack for an RT task explicitly rather than relying
    on the scheduler having already zeroed [timer_slack_ns], and — from
    v6.15 — in the [hrtimer_init_sleeper_on_stack] to
    [hrtimer_setup_sleeper_on_stack] rename.  No behavioural difference
    for a task under a policy that is neither RT nor SCHED_DEADLINE,
    which is every task the model describes: [State.init_model] starts
    an ordinary exec, and the one arm that can change the policy at
    all, [Kernel.Sched.Syscalls.sched_setscheduler_spec], answers
    SCHED_IDLE and declines every RT and DEADLINE request.)

    - ON A COMPLETED SLEEP, by the request as [ktime_set] took it — or
      up to [Uapi.KTIME_MAX], whichever is nearer.  [hrtimer_nanosleep]
      arms a CLOCK_MONOTONIC hrtimer with [HRTIMER_MODE_REL] and a
      soft expiry of exactly now + that [ktime_t] SATURATED at the top
      of the type by [ktime_add_safe], and a timer never fires
      before its soft expiry, so returning 0 means at least that much
      elapsed on the very clock [m_clock] tracks.  THERE IS NO GATE ON
      THE SUM: a sleep whose deadline would leave the type is one
      Linux serves at a nearer deadline rather than refusing, so the
      model records the nearer deadline instead of declining.
      [nanosleep_clock] carries the saturation and the argument that
      what it records is a lower bound on the real clock.  Recording
      that is strictly more faithful than leaving the clock still: it
      makes a later [clock_gettime] have to report a time at least a
      sleep further on.  It also covers the case that LOOKS like an
      interruption and is reported as success — [do_nanosleep] returns
      0 without writing anything when the remainder it computes is at
      or below zero, and that can only happen once the deadline is
      past.
    - ON AN INTERRUPTION, by the SATURATED DEADLINE less the reported
      remainder, floored at the clock's previous value — the same
      [Z.min (prev + timespec_ktime req) KTIME_MAX] the completed sleep
      records, minus what was left of it.  The deadline is the one the kernel really
      armed, so subtracting the remainder from it subtracts from the
      sleep that RAN rather than from the one that was asked for; the
      two differ exactly when the request saturated.  The floor is
      reachable, which is the one genuinely surprising fact in this
      syscall.  [do_nanosleep]
      computes the remainder as [hrtimer_expires_remaining]
      (include/linux/hrtimer.h), which measures against the HARD
      expiry, and [hrtimer_nanosleep] sets the hard expiry to
      [current->timer_slack_ns] PAST the soft one
      ([hrtimer_set_expires_range_ns]).  So a remainder may EXCEED the
      request, by up to the task's timer slack — 50 microseconds by
      default ([init_task]'s [.timer_slack_ns = 50000] in
      init/init_task.c), inherited rather than derived, and settable by
      [prctl(PR_SET_TIMERSLACK)] — though not to ANYTHING: kernel/sys.c
      breaks out without setting when [rt_or_dl_task_policy(current)],
      and an [arg2 <= 0] RESETS to [current->default_timer_slack_ns]
      rather than setting that value.  Neither restriction bounds the
      slack from above for the non-RT, non-DEADLINE tasks this model
      describes, which is what the argument below needs.  This is why
      [nanosleep_rem_ok_b] does NOT bound the remainder by the
      request: a model that did would reject a trace a real kernel can
      produce, and the model carries no timer slack to bound it
      properly.  What survives is the one-sided fact that at least
      (deadline - remainder) elapsed, which is what gets recorded, and
      the [Z.max prev] is what makes that statable when the difference
      goes the other way: the clock stands still rather than running
      backwards.

    A REMAINDER IS WRITTEN ONLY WITH THE INTERRUPTION, and only when
    it is strictly positive: [do_nanosleep] returns 0 without writing
    when the computed remainder is at or below zero, so the completed
    sleep has no write entry at all and -EINTR with a non-NULL [rmtp]
    always has exactly one, never [{0, 0}].  With a NULL [rmtp] the
    restart block's type is [TT_NONE] and nothing is written on either
    path — and then the slept duration is unknowable, so that
    interrupted arm leaves the clock where it was.

    -EINTR NEEDS A HANDLER TO HAVE RUN, and the model does not step
    one.  [do_nanosleep] itself never returns -EINTR; it returns
    -ERESTART_RESTARTBLOCK, and riscv64's
    [arch_do_signal_or_restart] (arch/riscv/kernel/signal.c,
    byte-identical at v6.10-v6.15) rewrites that to -EINTR ONLY on the
    branch where [get_signal] handed back a signal to deliver — and it
    does so there whatever the handler's flags say, the [SA_RESTART]
    test being attached to the -ERESTARTSYS disjunct alone, which is
    why [SA_RESTART] does not make [nanosleep] restartable.  (The one
    other guard on that rewrite is [regs->epc == restart_addr], which
    fails only when a ptracer has moved the program counter, and the
    model steps no ptracer.)  So a run that observes -EINTR is a run
    in which a handler's instructions executed, and those the machine
    model does not step.  Admitting this arm therefore does not model
    signal delivery; it stops the model REJECTING the one part of a
    signal-interrupted run that is visible at the syscall boundary.
    Whether the rest of such a run is covered is a pre-existing gap
    and not one this changes.

    NOT MODELED: the transparent-restart path.  When [get_signal] has
    nothing to deliver — a job-control stop and continue — the same
    -ERESTART_RESTARTBLOCK is turned into a fresh [restart_syscall]
    (nr 128) with the program counter rewound, rather than a return to
    the program.  [rmtp] HAS ALREADY BEEN WRITTEN by then, because
    [nanosleep_copyout] runs inside [do_nanosleep], before the signal
    layer chooses.  What the model would see at that step is neither
    of the two arms, so it REJECTS rather than declining: a known
    gap.  Reaching it takes
    a stop signal from another process, and the number the run goes on
    to make is outside [Specs.modeled_sysnos] anyway.

    THE REQUEST IS A COPY-IN.  [get_timespec64] (kernel/time/time.c,
    byte-identical at v6.10-v6.15) is a single
    [copy_from_user(&kts, uts, sizeof(kts))] of the whole
    [struct __kernel_timespec] into a kernel-local [struct timespec64],
    and it runs BEFORE any other decision the call makes.  The width is
    16 because that struct is two 8-byte fields — [__kernel_time64_t
    tv_sec] and [long long tv_nsec] (include/uapi/linux/time_types.h).
    So every outcome reached through a successful read has already
    consumed those bytes — the -EINVAL, the decline that is left past
    it, the completed sleep, the interruption and the copy-out's
    -EFAULT alike — and [record_copyins] therefore wraps the whole
    [Some req] arm rather than any one branch of it.

    THE RANGE TEST COMES FIRST, through [State.copy_bytes_map], whose
    note says why the bare walk could not stand alone.  Before it, a
    [rqtp] in the last sixteen bytes of the address space read the
    request back through the wrap and the arm SLEPT on it, where
    [get_timespec64]'s [copy_from_user] refuses the range before a byte
    moves.  The [None] arm carries no ledger, because no outcome on it
    has read the request, and it splits by the rule
    [Kernel.Sys.prlimit64_spec]'s note states:

    - [access_ok] REFUSES the range: -EFAULT with nothing copied, which
      [SYSCALL_DEFINE2(nanosleep)] (kernel/time/hrtimer.c at v6.18.46)
      returns before it validates or sleeps.  The arm commits to it.
    - [access_ok] ADMITS the range and it is not wholly mapped: still
      -EFAULT with the kernel buffer untouched, but the raw copy reads
      forward up to the fault, and the model declines it for the reason
      [Kernel.Sys.prlimit64_spec] gives for its [new_rlim]: which bytes
      the kernel read is not something the ledger can state. *)
Definition nanosleep_spec (rqtp rmtp : word) : Sys SyscallEffect :=
  i <- input ;;
  match copy_bytes_map (in_mem i) rqtp 16 with
  | None =>
      if negb (access_okb rqtp 16) then err_ret EFAULT
      else unmodeled   (* admitted but not wholly readable: fail closed *)
  | Some req =>
      record_copyins [(rqtp, 16%nat)]
      (
      if negb (timespec_valid_b req) then err_ret EINVAL
      else
      m <- get_model ;;
      let slept :=
        (set_clock (nanosleep_clock (m_clock m) req []) ;;
         ret_only (Z_to_bv 64 0)) in
      if w_is0 rmtp
      then alt slept (err_ret EINTR)   (* nothing to report the remainder in *)
      else
        match copy_bytes_map (in_wmem i) rmtp 16 with
        | None =>
            (* The remainder destination, through the same
               [State.copy_bytes_map] as the request.  Before it an
               [rmtp] in the last sixteen bytes of the address space
               read back as writable through the wrap, and an
               interruption wrote its remainder there.
               [put_timespec64] (kernel/time/time.c at v6.18.46) is one
               [copy_to_user] of the whole struct, so the [None] splits
               by the same rule as the request's:

               - [access_ok] REFUSES the range, and nothing is ever
                 written.  A completed sleep never reaches the copy and
                 returns 0.  An interruption with a positive remainder
                 gets -EFAULT from [nanosleep_copyout], which
                 [do_nanosleep] and [hrtimer_nanosleep] return as it is
                 rather than as a restart (kernel/time/hrtimer.c,
                 [nanosleep_copyout] and [hrtimer_nanosleep]).  Both are
                 admitted.  The -EFAULT holds the clock, as the NULL
                 [rmtp] interruption does: the remainder was computed
                 and not reported, so how much elapsed is unknowable.
               - [access_ok] ADMITS the range and it is not wholly
                 mapped: declined.  Linux answers -EFAULT here HAVING
                 CONSUMED THE SLEEP and, on a 16-byte [rmtp] straddling
                 into an unwritable page, having torn the struct:
                 [put_timespec64]'s [copy_to_user] reaches riscv64's
                 [__asm_copy_to_user] (arch/riscv/lib/uaccess.S), which
                 copies forward and leaves the bytes it managed
                 written.  Fail closed. *)
            if negb (access_okb rmtp 16) then alt slept (err_ret EFAULT)
            else unmodeled
        | Some _ =>
            alt slept
              (rem <- choose (fun rem : list byte =>
                                nanosleep_rem_ok_b rem = true) ;;
               set_clock (nanosleep_clock (m_clock m) req rem) ;;
               pure (mkEffect (errno_ret EINTR) [(rmtp, rem)] []))
        end)
  end.
