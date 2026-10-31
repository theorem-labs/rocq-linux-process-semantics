import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Kernel.Time.Hrtimer — nanosleep (101)

Mirrors `theories/LinuxProcessSem/Sys/Kernel/Time/Hrtimer.v`.  This file
answers to Linux `kernel/time/hrtimer.c (Linux v6.18.46)`: it holds what the kernel defines
there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
The Rocq file cites its kernel side partly over the window v6.10-v6.15
and partly at v6.18.46, with no line numbers; every number here was read
at v6.18.46, and where a function changed inside that window the
docstring says what changed.

Spellings that differ from Rocq without changing a value: `Z.ltb` and
`Nat.eqb` are Lean's decidable `<` on `Int` and `==` on `Nat`, `Z.max`
and `Z.min` are `max` and `min` on `Int`, and the `negb` gate is `!`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Hrtimer

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- What `timespec64_valid` (include/linux/time64.h:97-106, Linux
v6.18.46, commit 1f99e9ab748f) accepts, applied to the 16 bytes read out
of `rqtp`: `ts->tv_sec < 0` is refused at :100-101 and
`(unsigned long)ts->tv_nsec >= NSEC_PER_SEC` at :103-104.  `tv_sec` is an
`s64`, so "not negative" is "below 2^63 read unsigned"; `tv_nsec` is cast
to unsigned before the comparison, so a negative nanosecond field fails
the same test a too-large one does.  A request failing either is -EINVAL
(`SYSCALL_DEFINE2(nanosleep, ...)`, kernel/time/hrtimer.c:2197-2198, Linux v6.18.46),
returned before `rmtp` is touched.

No length conjunct: the only caller applies this to exactly the bytes
`read_bytes_map` returned for a 16-byte read.  Rocq:
`Hrtimer.timespec_valid_b`. -/
def timespec_valid_b (bs : List byte) : Bool :=
  decide (tv_sec_of bs < 2 ^ 63) && decide (tv_frac_of bs < 1000000000)

/-- What a remainder the kernel wrote into `rmtp` must satisfy: sixteen
bytes, normalized, strictly positive and under the `ktime_t` envelope —
and NOT bounded by the request, which is the surprising half and is
argued at `nanosleep_spec`.  Each conjunct is a kernel line (Linux
v6.18.46, commit 1f99e9ab748f):

- the width: `put_timespec64` (kernel/time/time.c:903-912) is one
  `copy_to_user` of a `struct __kernel_timespec`, two 8-byte fields
  (include/uapi/linux/time_types.h:7-10);
- the normalized `tv_nsec` and the envelope: `do_nanosleep` converts the
  `ktime_t` remainder with `ktime_to_timespec64` (kernel/time/hrtimer.c:2140, Linux v6.18.46),
  which is `ns_to_timespec64` (kernel/time/time.c:523-542): the
  `div_u64_rem` by NSEC_PER_SEC leaves `tv_nsec` below 10^9, and a
  `ktime_t` is at most `KTIME_MAX` (include/linux/time64.h:30), one below
  `CLOCK_NS_ENVELOPE`;
- strict positivity: `do_nanosleep`'s `if (rem <= 0) return 0;`
  (kernel/time/hrtimer.c:2138-2139, Linux v6.18.46) turns a non-positive remainder into a
  completed sleep before anything is written.

See bugs/nanosleep-remainder-can-exceed-the-request.md for why no
conjunct compares the remainder with the request.  Rocq:
`Hrtimer.nanosleep_rem_ok_b`. -/
def nanosleep_rem_ok_b (bs : List byte) : Bool :=
  (bs.length == 16)
  && decide (tv_frac_of bs < 1000000000)
  && decide (0 < timespec_ns bs)
  && decide (timespec_ns bs < CLOCK_NS_ENVELOPE)

/-- The monotonic clock after a sleep that requested `req` and reported
remainder `rem`; `rem` is `[]` on the success path, where the whole
request elapsed (`timespec_ns [] = 0`).  Read it as the deadline the
kernel actually armed, less what was left of it, and never behind where
the clock already stood:

- `timespec_ktime req` is the request as `ktime_set` took it:
  `SYSCALL_DEFINE2(nanosleep, ...)` hands `hrtimer_nanosleep` the
  `timespec64_to_ktime` of the request (kernel/time/hrtimer.c:2203-2204, Linux v6.18.46);
  `timespec64_to_ktime` (include/linux/ktime.h:69-72) is `ktime_set`
  (include/linux/ktime.h:36-42), which returns `KTIME_MAX` outright once
  `secs >= KTIME_SEC_MAX` (the test at :38-39).  The first saturation.
- `min (prev + that) KTIME_MAX` is the deadline, SATURATING: `do_nanosleep`
  (kernel/time/hrtimer.c:2118, Linux v6.18.46) starts the sleeper through
  `hrtimer_sleeper_start_expires` (kernel/time/hrtimer.c:2031-2045) and
  `hrtimer_start_expires`
  (include/linux/hrtimer.h:265-274) into `__hrtimer_start_range_ns`
  (kernel/time/hrtimer.c:1242-1243 (Linux v6.18.46), its `HRTIMER_MODE_REL` branch), which
  adds the clock reading with `ktime_add_safe`.  `ktime_add_safe`
  (kernel/time/hrtimer.c:340-352) does not report an overflow: it tests
  `res < 0 || res < lhs || res < rhs` (:348) and on any of them replaces
  the sum with `ktime_set(KTIME_SEC_MAX, 0)` (:349), which is `KTIME_MAX`
  for the `>=` reason `Uapi.KTIME_MAX` argues.  Both operands are
  non-negative, so the test fires exactly when the true sum exceeds
  `KTIME_MAX`.  The second saturation.  A sleep whose deadline would leave
  the type therefore SUCCEEDS at a nearer deadline; it is not a shape the
  model may decline.
- `- timespec_ns rem` subtracts the reported remainder from THAT
  deadline, not from the request: `do_nanosleep` measures the remainder
  as `hrtimer_expires_remaining` (include/linux/hrtimer.h:159-162, Linux
  v6.18.46; the call is kernel/time/hrtimer.c:2135), `node.expires` less the clock at
  wake, and `node.expires` is the saturated soft expiry plus a
  non-negative slack — `hrtimer_nanosleep` sets the pair with
  `hrtimer_set_expires_range_ns(&t.timer, rqtp, current->timer_slack_ns)`
  (kernel/time/hrtimer.c:2167 (Linux v6.18.46); include/linux/hrtimer.h:109-113), and
  `__hrtimer_start_range_ns` (kernel/time/hrtimer.c:1247) re-adds the gap
  between the two through `hrtimer_set_expires_range_ns`, `ktime_add_safe`
  again.  So the wake time is at least
  `min (now + k) KTIME_MAX - rem`, and `now >= prev`.
- `max prev ...` is the clock refusing to run backwards, and it is
  reachable: a remainder may exceed the request by up to the slack, and
  once the deadline saturates `KTIME_MAX - rem` can fall below `prev`.

Which of the two saturations is load-bearing for soundness (the second),
why the first buys exactness at `tv_sec = KTIME_SEC_MAX` and nothing
else, and the version history of `__hrtimer_start_range_ns` — three
shapes since v6.10, none touching the `HRTIMER_MODE_REL` branch; at
v6.18.46 the reading goes through `__hrtimer_cb_get_time(base->clockid)`
— are argued on the Rocq definition `Hrtimer.nanosleep_clock`.  The
result stays under `CLOCK_NS_ENVELOPE`, which is what lets this file carry
no envelope gate of its own; `Checks/Cases/Kernel/Time/Hrtimer.lean`'s
`nanosleep_clock_under_the_envelope` is that fact, machine-checked. -/
def nanosleep_clock (prev : word) (req rem : List byte) : word :=
  Z_to_bv 64
    (max (bv_unsigned prev)
      (min (bv_unsigned prev + timespec_ktime req) KTIME_MAX - timespec_ns rem))

/-- `nanosleep rqtp rmtp`: sleep for a relative `struct timespec`, and on
interruption report what was left.  The argument in full — why BOTH
outcomes are admitted rather than the success path alone, why the
interrupted case cannot be declined on its own, why aliasing `rqtp ==
rmtp` needs no gate, why the request's ceiling is judged rather than
declined and what each arm answers there, and why the remainder is not
bounded by the request — is on the Rocq definition `Hrtimer.nanosleep_spec`
and is not repeated here.  What follows is the kernel line each decision
rests on, re-read at Linux v6.18.46 (commit 1f99e9ab748f).

ORDER, following `SYSCALL_DEFINE2(nanosleep, ...)`
(kernel/time/hrtimer.c:2189-2205): the request is read first
(`get_timespec64`, -EFAULT at :2194-2195), validated second
(`timespec64_valid`, -EINVAL at :2197-2198), the restart block is told
whether there is an `rmtp` (`rmtp ? TT_NATIVE : TT_NONE`, :2201), and
only then is the sleep armed (:2203-2204).  `rmtp` is NEVER validated up
front — a completed sleep with an unwritable `rmtp` answers 0 without
touching it — which the model gives up by gating on `rmtp` before the
`alt`.  The cost is coverage on a shape the model could have answered;
the reason is the straddle at the `none` arm below.

THE REQUEST IS A COPY-IN.  `get_timespec64` (kernel/time/time.c:872-892, Linux v6.18.46)
is a single `copy_from_user(&kts, uts, sizeof(kts))` (:878) of the whole
`struct __kernel_timespec` — two 8-byte fields, `tv_sec` and `tv_nsec`
(include/uapi/linux/time_types.h:7-10), hence 16 — and it runs BEFORE any
other decision the call makes, so every outcome reached through a
successful read has already consumed those bytes and `record_copyins`
wraps the whole `some req` arm.  A request that is not wholly readable is
the -EFAULT of :879-880 with the user memory untouched; the model
declines that shape rather than describing it (Rocq's declared
narrowing, not an empty intersection).

BOTH OUTCOMES ARE ADMITTED, the environment choosing.  On a completed
sleep `do_nanosleep` returns 0 (kernel/time/hrtimer.c:2130-2131 (Linux v6.18.46), and
:2138-2139 when the remainder it computes is at or below zero, the case
that LOOKS like an interruption); the clock moves by the whole request as
`ktime_set` took it, saturated (`nanosleep_clock` with `rem = []`).  On
an interruption `do_nanosleep` writes the remainder through
`nanosleep_copyout` (:2133-2142; :2093-2110, `put_timespec64` at
:2103-2104) and returns -ERESTART_RESTARTBLOCK (:2109, :2144).  That
becomes the -EINTR the program sees only in riscv64's
`arch_do_signal_or_restart` (arch/riscv/kernel/signal.c:396-463, Linux v6.18.46): the
rewrite at :437-444 runs on the branch where `get_signal` (:431) handed
back a signal to deliver, and does so whatever the handler's flags say —
the `SA_RESTART` test is attached to the -ERESTARTSYS disjunct alone
(:440-441), which is why `SA_RESTART` does not make `nanosleep`
restartable.  So a run that observes -EINTR is a run in which a handler
executed; admitting the arm stops the model REJECTING the one part of
such a run that is visible at the syscall boundary, and models no
delivery.

A REMAINDER IS WRITTEN ONLY WITH THE INTERRUPTION, and only when it is
strictly positive (:2138-2139): the completed sleep has no write entry,
and -EINTR with a non-NULL `rmtp` has exactly one, never `{0, 0}`.  With a
NULL `rmtp` the type is `TT_NONE` (:2201) and nothing is written on
either path (:2134, :2144); the slept duration is then unknowable and
that arm leaves the clock where it was.

THE REMAINDER MAY EXCEED THE REQUEST.  `hrtimer_nanosleep` sets the hard
expiry `current->timer_slack_ns` past the soft one (:2167;
include/linux/hrtimer.h:109-113, Linux v6.18.46) and `hrtimer_expires_remaining`
measures against the HARD expiry (include/linux/hrtimer.h:159-162).  The
slack is 50000 ns by default (init/init_task.c:146, the
`.timer_slack_ns` initialiser), inherited rather than derived, and
`prctl(PR_SET_TIMERSLACK)` (kernel/sys.c:2630-2638, Linux v6.18.46) sets it to any
positive `arg2` — the `rt_or_dl_task_policy` break (:2631-2632) and the
`arg2 <= 0` reset to `default_timer_slack_ns` (:2633-2635) bound it from
neither side above.  The model carries no timer slack, so
`nanosleep_rem_ok_b` does not bound the remainder by the request, and
`nanosleep_clock` floors the difference at the previous clock instead.
The Rocq file's window note: v6.10 and v6.11 zeroed the slack for an RT
task explicitly at this call, v6.12 onwards passes
`current->timer_slack_ns` unconditionally, which v6.18.46 does at :2167;
no behavioural difference for a task under a policy that is neither RT
nor DEADLINE, which is every task the model describes — `State.init_model`
starts an ordinary exec, and the one Rocq arm that can change the policy,
`Kernel.Sched.Syscalls.sched_setscheduler_spec`, answers SCHED_IDLE and
declines every RT and DEADLINE request.

NOT MODELED: the transparent-restart path.  When `get_signal` has nothing
to deliver — a job-control stop and continue — the same
-ERESTART_RESTARTBLOCK becomes a fresh `restart_syscall` with the program
counter rewound (arch/riscv/kernel/signal.c:455-456, Linux v6.18.46), and `rmtp` has
already been written by then.  What the model would see at that step is
neither arm, so it REJECTS rather than declining;
bugs/nanosleep-transparent-restart-rejected.md records it.

THE `none` ARM ON `rmtp`: Linux answers -EFAULT there HAVING CONSUMED THE
SLEEP and, on a 16-byte `rmtp` straddling into an unwritable page, having
torn the struct — `put_timespec64`'s copy to user space (kernel/time/time.c:911,
Linux v6.18.46)
reaches riscv64's copy routine in arch/riscv/lib/uaccess.S, which copies
forward and leaves the bytes it managed written.  Fail closed. -/
def nanosleep_spec (rqtp rmtp : word) : Sys SyscallEffect :=
  i <- input ;;
  match read_bytes_map i.in_mem rqtp (Z_to_bv 64 16) with
  | none => unmodeled   -- request not wholly readable: fail closed
  | some req =>
      record_copyins [(rqtp, 16)]
        (if !(timespec_valid_b req) then err_ret EINVAL
         else
           m <- get_model ;;
           let slept : Sys SyscallEffect :=
             set_clock (nanosleep_clock (m_clock m) req []) ;; ret_only (Z_to_bv 64 0)
           if w_is0 rmtp then alt slept (err_ret EINTR)   -- nothing to report the remainder in
           else
             match read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) with
             | none => unmodeled   -- remainder destination not wholly writable: fail closed
             | some _ =>
                 alt slept
                   (rem <- choose (fun rem : List byte => nanosleep_rem_ok_b rem = true) ;;
                    set_clock (nanosleep_clock (m_clock m) req rem) ;;
                    Monad.pure (mkEffect (errno_ret EINTR) [(rmtp, rem)] [])))

end LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
