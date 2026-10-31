import LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Uapi.Time — clock ids, the `ktime_t` bounds and
the timespec decoders

One part of `theories/LinuxProcessSem/Sys/Uapi.v` (see `Sys/Uapi.lean`
for the split).  WHAT GOES HERE: the POSIX clock ids some spec tests, the
three bounds `ktime_t` imposes, and the little-endian readers of a
`struct __kernel_timespec` or `__kernel_old_timeval`.

TRUST BOUNDARY: this file is part of the trusted specification.

Every line below is read at Linux v6.18.46, commit
1f99e9ab748fc5c32120de9c4eca31abfe54a4d5; where Rocq read a block at
v6.10-v6.15 it is byte-identical there. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! ## The POSIX clock ids the model interprets (include/uapi/linux/time.h)

A clock id gets a name here when some spec TESTS it, not when it exists.
The first three are `clock_gettime`'s.  The last three are
`Fs.Timerfd.timerfd_create_spec`'s, named for the OPPOSITE reason: that
spec's whole content is a five-way membership test written out of
Linux's own, so each id it admits has to be stateable.  The two families
OVERLAP but neither contains the other — `timerfd_create` takes
`CLOCK_BOOTTIME` and the two alarm clocks that `clock_gettime` declines,
and declines `CLOCK_PROCESS_CPUTIME_ID`, which `clock_gettime` answers.
Do not read either list as "the clocks the model supports". -/

/-- `#define CLOCK_REALTIME 0` (include/uapi/linux/time.h:49, Linux
v6.18.46, commit 1f99e9ab748f). -/
def CLOCK_REALTIME : Int := 0

/-- `#define CLOCK_MONOTONIC 1` (include/uapi/linux/time.h:50, Linux
v6.18.46, commit 1f99e9ab748f). -/
def CLOCK_MONOTONIC : Int := 1

/-- `#define CLOCK_PROCESS_CPUTIME_ID 2` (include/uapi/linux/time.h:51,
Linux v6.18.46, commit 1f99e9ab748f). -/
def CLOCK_PROCESS_CPUTIME_ID : Int := 2

/-- `#define CLOCK_BOOTTIME 7` (include/uapi/linux/time.h:56, Linux
v6.18.46, commit 1f99e9ab748f). -/
def CLOCK_BOOTTIME : Int := 7

/-- `#define CLOCK_REALTIME_ALARM 8` (include/uapi/linux/time.h:57, Linux
v6.18.46, commit 1f99e9ab748f). -/
def CLOCK_REALTIME_ALARM : Int := 8

/-- `#define CLOCK_BOOTTIME_ALARM 9` (include/uapi/linux/time.h:58, Linux
v6.18.46, commit 1f99e9ab748f). -/
def CLOCK_BOOTTIME_ALARM : Int := 9

/-! ## The `ktime_t` bounds -/

/-- The range `ktime_t` represents, in nanoseconds.  Linux carries kernel
time as a signed 64-bit nanosecond count — `typedef s64 ktime_t`
(include/linux/types.h:126, Linux v6.18.46, commit 1f99e9ab748f) — so
2^63 nanoseconds, about 292 years, is the first value it cannot hold.
`Kernel.Time.PosixTimers` needs it as the ceiling on a recorded
`CLOCK_MONOTONIC` reading and `Kernel.Time.Hrtimer` as the ceiling on
where a sleep may carry that reading; it is here because it is a fact
about the type, not about a syscall. -/
def CLOCK_NS_ENVELOPE : Int := 2 ^ 63

/-- The largest value `ktime_t` holds: `#define KTIME_MAX ((s64)~((u64)1
<< 63))` (include/linux/time64.h:30, Linux v6.18.46, commit
1f99e9ab748f), one nanosecond below `CLOCK_NS_ENVELOPE`.

It is the value `ktime_add_safe` (kernel/time/hrtimer.c, Linux v6.18.46)
SATURATES to, which is the one place the two constants must not be
confused.  That function's saturation arm reads `res =
ktime_set(KTIME_SEC_MAX, 0)`, and its comment says it is using "the
maximum timeout which we can return to user space in a timespec" — but
`ktime_set` (include/linux/ktime.h:38, Linux v6.18.46) opens with `if
(unlikely(secs >= KTIME_SEC_MAX)) return KTIME_MAX;`, and the test is
`>=`, so passing
exactly `KTIME_SEC_MAX` takes that early return.  The saturation value is
therefore `KTIME_MAX`, NOT `KTIME_SEC_MAX * 10^9` — the code does not do
what its own comment describes, and the difference is the 854775807 ns
between them.  `Kernel.Time.Hrtimer.nanosleep_clock` needs the value the
code produces. -/
def KTIME_MAX : Int := 2 ^ 63 - 1

/-- The largest whole second `ktime_t` can hold: `#define KTIME_SEC_MAX
(KTIME_MAX / NSEC_PER_SEC)` (include/linux/time64.h:32, Linux v6.18.46,
commit 1f99e9ab748f).  Two readers:
`Time.gettimeofday_spec` as the ceiling on a wall-clock reading, and
`timespec_ktime` below as the point where `ktime_set` stops converting a
request and starts clamping. -/
def KTIME_SEC_MAX : Int := 9223372036

/-- One second in nanoseconds: `#define NSEC_PER_SEC 1000000000L`
(include/vdso/time64.h:11, Linux v6.18.46, commit 1f99e9ab748f), the
bound `timespec64_valid` (include/linux/time64.h) holds `tv_nsec`
under. -/
def NSEC_PER_SEC : Int := 1000000000

/-! ## Two little-endian 8-byte fields, read OUT of the bytes the kernel
wrote

THE NAMES ARE STRUCT-NEUTRAL because three structs have this shape on
riscv64.  `struct __kernel_timespec { __kernel_time64_t tv_sec; long long
tv_nsec; }` (include/uapi/linux/time_types.h:7-10, Linux v6.18.46) and
`struct __kernel_old_timeval { __kernel_long_t tv_sec; __kernel_long_t
tv_usec; }` (lines 25-28) are both 16 bytes of two 8-byte fields,
differing only in the UNIT of the second one, so the decoders are shared
and only the per-struct predicates differ.  Reading the bytes, rather
than encoding a chosen count into them, is deliberate: the bytes in the
destination buffer are what the kernel actually produced and what the
harness actually observes, so every condition over them is stated about
them directly. -/

def tv_sec_of (bs : List byte) : Int := bytes_le_to_Z (bs.take 8)
def tv_frac_of (bs : List byte) : Int := bytes_le_to_Z (bs.drop 8)

/-- A whole `struct __kernel_timespec` as a nanosecond count.  Computed
in `Int`, NOT in `word`: a wrapping sum would let an absurd `tv_sec` land
back under the envelope and read as a small, admissible time. -/
def timespec_ns (bs : List byte) : Int :=
  tv_sec_of bs * 1000000000 + tv_frac_of bs

/-- The same `struct __kernel_timespec` as the `ktime_t` the kernel
converts it to, which is NOT the same number.  `timespec64_to_ktime` is
`ktime_set(ts.tv_sec, ts.tv_nsec)` (include/linux/ktime.h, Linux
v6.18.46, commit 1f99e9ab748f, where both functions are defined), and
`ktime_set` opens with `if (unlikely(secs >= KTIME_SEC_MAX)) return
KTIME_MAX;` (line 38), so the conversion STOPS at `KTIME_SEC_MAX` and
hands back `KTIME_MAX` rather than a product.  The two disagree over the
whole band [KTIME_SEC_MAX, 2^63) of seconds a `timespec64` can carry
past `timespec64_valid`, and AT the boundary: `KTIME_SEC_MAX` seconds
converts to `KTIME_MAX`, not to `KTIME_SEC_MAX * 10^9`, which is
854775807 ns lower.  `tv_sec` is read unsigned here for `timespec_ns`'s
reason, and the one caller (`Kernel.Time.Hrtimer.nanosleep_clock`) has
already applied `timespec64_valid`, which refuses a `tv_sec` at or past
2^63. -/
def timespec_ktime (bs : List byte) : Int :=
  if tv_sec_of bs < KTIME_SEC_MAX then timespec_ns bs else KTIME_MAX

/-- The same total with `tv_sec` read as the SIGNED 64-bit field it
actually is (`__kernel_time64_t` is `long long`).  `timespec_ns` reads it
unsigned, which is what the two arms that report a TIME want — a negative
second is not a time, and reading it unsigned turns it into a number far
past their envelope, which is exactly the rejection they need.
`CLOCK_PROCESS_CPUTIME_ID` does not report a time, and a negative
`tv_sec` is a shape it really emits, so
`Kernel.Time.PosixTimers.cputime_ok_b` needs the signed reading.
Computed in `Int` for `timespec_ns`'s reason. -/
def timespec_ns_signed (bs : List byte) : Int :=
  (if tv_sec_of bs < 2 ^ 63 then tv_sec_of bs else tv_sec_of bs - 2 ^ 64) * 1000000000
    + tv_frac_of bs

end LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
