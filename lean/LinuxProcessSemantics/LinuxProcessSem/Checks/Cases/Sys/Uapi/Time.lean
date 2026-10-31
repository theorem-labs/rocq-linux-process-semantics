import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! # Checks.Cases.Sys.Uapi.Time — the `Sys.Uapi.Time` constants, read off
against Linux

Pins over `Sys/Uapi/Time.lean`, clock ids, the `ktime_t` bounds and the
timespec decoders. Not part of the trusted specification: this file is QA
on the definitions, written to be READ, and every claim in it is a claim
about a header or a function of Linux v6.18.46, commit
1f99e9ab748fc5c32120de9c4eca31abfe54a4d5, with the citation beside it.

Each pin states a value the kernel really has and, beside it, refutes the
concrete mistake the constant exists to prevent — a value from another
architecture's header, an off-by-one at a bound, a decimal read of an
octal, a mask taken for its neighbour.  They are stated about the cited
headers and sources, never about the Rocq definitions of the same names.
No Rocq file sits at this file's mirror path: the Rocq tree keeps its
Uapi constants unpinned (this stops being true the day a Rocq case
file pins them), so this file is the Lean port's own evidence rather
than a twin. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Time

open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- The nine clock ids (include/uapi/linux/time.h:49-58), and the two
calls that read them cover different sets without either containing the
other: `timerfd_create` (fs/timerfd.c:394, Linux v6.18.46) refuses
`CLOCK_PROCESS_CPUTIME_ID`, which `clock_gettime` answers, and takes the
two alarm clocks, which `clock_gettime` declines.  `CLOCK_BOOTTIME` is in
both: at `f1006fe8` it is one of the five ids
`Kernel.Time.PosixTimers.clockid_percall_b` admits, beside
`CLOCK_MONOTONIC_RAW`, `CLOCK_REALTIME_COARSE` and
`CLOCK_MONOTONIC_COARSE`.  Each call's set is in its own specification. -/
theorem clock_ids :
    CLOCK_REALTIME = 0 ∧ CLOCK_MONOTONIC = 1 ∧ CLOCK_PROCESS_CPUTIME_ID = 2
    ∧ CLOCK_MONOTONIC_RAW = 4 ∧ CLOCK_REALTIME_COARSE = 5
    ∧ CLOCK_MONOTONIC_COARSE = 6
    ∧ CLOCK_BOOTTIME = 7 ∧ CLOCK_REALTIME_ALARM = 8 ∧ CLOCK_BOOTTIME_ALARM = 9
    ∧ CLOCK_PROCESS_CPUTIME_ID ∉ [CLOCK_REALTIME, CLOCK_MONOTONIC, CLOCK_BOOTTIME,
                                   CLOCK_REALTIME_ALARM, CLOCK_BOOTTIME_ALARM]
    ∧ CLOCK_BOOTTIME ∉ [CLOCK_REALTIME, CLOCK_MONOTONIC, CLOCK_PROCESS_CPUTIME_ID] := by decide

/-- The `ktime_t` bounds (include/linux/time64.h:30-32, include/linux/types.h:126,
include/vdso/time64.h:11, Linux v6.18.46).  The division is written over the literal
`10 ^ 9` rather than over `NSEC_PER_SEC` so that the divisor is positive by
construction (Lean's `Int` division is Euclidean and agrees with Rocq's
floor division only then); the conjunct before it ties the literal to the
name.  `KTIME_MAX` is NOT `KTIME_SEC_MAX * NSEC_PER_SEC`
— the value `ktime_add_safe`'s comment describes and its code does not
produce — and the gap is 854775807 ns; `NSEC_PER_SEC` is not
`USEC_PER_SEC` (include/vdso/time64.h:10, Linux v6.18.46). -/
theorem ktime_bounds :
    KTIME_MAX = 2 ^ 63 - 1 ∧ CLOCK_NS_ENVELOPE = KTIME_MAX + 1
    ∧ NSEC_PER_SEC = 10 ^ 9 ∧ KTIME_SEC_MAX = KTIME_MAX / 10 ^ 9
    ∧ KTIME_MAX ≠ KTIME_SEC_MAX * NSEC_PER_SEC
    ∧ KTIME_MAX - KTIME_SEC_MAX * NSEC_PER_SEC = 854775807
    ∧ NSEC_PER_SEC ≠ 1000000 := by decide

/-- A `struct __kernel_timespec` (include/uapi/linux/time_types.h:7-10, Linux
v6.18.46) as the kernel writes it: two little-endian 8-byte fields.  A fixture for the
pins, not a definition of the model. -/
private def timespec_fixture (sec nsec : Int) : List byte :=
  Z_to_le_bytes 8 sec ++ Z_to_le_bytes 8 nsec

/-- The decoders read the two fields back and total them in nanoseconds. -/
theorem timespec_decoders_read_the_struct :
    tv_sec_of (timespec_fixture 5 7) = 5 ∧ tv_frac_of (timespec_fixture 5 7) = 7
    ∧ timespec_ns (timespec_fixture 5 7) = 5000000007
    ∧ timespec_ktime (timespec_fixture 5 7) = 5000000007 := by decide

/-- `ktime_set` (include/linux/ktime.h:38, Linux v6.18.46) tests `secs >=
KTIME_SEC_MAX`, so exactly `KTIME_SEC_MAX` seconds converts to `KTIME_MAX`
and not to the product, while one second less converts exactly. -/
theorem timespec_ktime_saturates_at_KTIME_SEC_MAX :
    timespec_ktime (timespec_fixture KTIME_SEC_MAX 0) = KTIME_MAX
    ∧ timespec_ktime (timespec_fixture KTIME_SEC_MAX 0) ≠ KTIME_SEC_MAX * NSEC_PER_SEC
    ∧ timespec_ktime (timespec_fixture (KTIME_SEC_MAX - 1) 999999999)
        = (KTIME_SEC_MAX - 1) * NSEC_PER_SEC + 999999999 := by decide

/-- `tv_sec` is a `long long`: -1 second reads as -1 signed and as
2^64 - 1 unsigned, which the unsigned total pushes past the envelope —
the rejection the two time-reporting arms want — while the signed total
is what `CLOCK_PROCESS_CPUTIME_ID` really emits. -/
theorem negative_tv_sec_reads_two_ways :
    timespec_ns_signed (timespec_fixture (-1) 5) = -999999995
    ∧ CLOCK_NS_ENVELOPE < timespec_ns (timespec_fixture (-1) 5) := by decide

/-- On a non-negative `tv_sec` the signed and unsigned totals AGREE — the
signed reading changes nothing for a time — and the boundary between them
is bit 63 of the `long long`: `struct __kernel_timespec`'s `tv_sec` is a
`__kernel_time64_t` (include/uapi/linux/time_types.h:8, Linux v6.18.46,
commit 1f99e9ab748f), `typedef long long __kernel_time64_t`
(include/uapi/asm-generic/posix_types.h:93), and `put_timespec64`
(kernel/time/time.c:903) writes it whole.  2^63 − 1 seconds is the
largest positive `tv_sec` and totals as itself; 2^63 seconds is the most
negative, −2^63, and totals as that and not as the unsigned product.  The
one pin above sits at −1 alone, which a port that always subtracted 2^64,
or one that put the boundary anywhere between 2^63 and 2^64, both closed.
No probe reaches a negative `tv_sec`: the signed total's only consumer,
`cputime_ok_b`, is unported (`Kernel.Time.PosixTimers`).
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem timespec_ns_signed_boundary_is_bit_63 :
    timespec_ns_signed (timespec_fixture 5 7) = 5000000007
    ∧ timespec_ns_signed (timespec_fixture 5 7) = timespec_ns (timespec_fixture 5 7)
    ∧ timespec_ns_signed (timespec_fixture (2 ^ 63 - 1) 0) = (2 ^ 63 - 1) * 1000000000
    ∧ timespec_ns_signed (timespec_fixture (2 ^ 63) 0) = -(2 ^ 63) * 1000000000
    ∧ timespec_ns_signed (timespec_fixture (2 ^ 63) 0) ≠ 2 ^ 63 * 1000000000 := by decide

/-- `timespec_ns` totals in `Int`, not in 64 bits, as its docstring
promises: 18446744074 seconds is 2^64 + 290448384 nanoseconds, 584 years
past `CLOCK_NS_ENVELOPE`, and a port totalling in a 64-bit word would read
it as 290448384 ns — a small, admissible time.  No kernel reports such a
second on the clocks the total serves, since `ktime_t` is an `s64` of
nanoseconds (include/linux/types.h:126, Linux v6.18.46) and `put_timespec64`
(kernel/time/time.c:903) writes the seconds `ktime_t` was split into, so the
wrapped reading would let through an answer no kernel gives.  Rocq pins the same
wrap at the consumer (`clock_reading_wrapping_sum_rejected`,
`Checks/Cases/Kernel/Time/PosixTimers.v`); Lean has no consumer of
`timespec_ns` yet, so the decoder carries the pin.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem timespec_ns_does_not_wrap_at_2_64 :
    timespec_ns (timespec_fixture 18446744074 0) = 2 ^ 64 + 290448384
    ∧ CLOCK_NS_ENVELOPE < timespec_ns (timespec_fixture 18446744074 0)
    ∧ timespec_ns (timespec_fixture 18446744074 0) ≠ 290448384 := by decide

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Time
