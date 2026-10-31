-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Sys/Kernel/Time/Time.v

import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi


/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Kernel.Time.Time — gettimeofday (169)

Mirrors `theories/LinuxProcessSem/Sys/Kernel/Time/Time.v`, which answers to
Linux `kernel/time/time.c`: it holds what the kernel defines there, and
nothing else.

Its own definitions are cited as `Time.<ident>`, not
`Kernel.Time.Time.<ident>`, for the reason the Rocq header gives: a module
path with a repeated segment is what `tools/check_module_refs.py` reports
as malformed, and `Time` alone is the spelling that resolves.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Kernel/Time/Time.lean`.

The two definitions keep the Rocq names and shapes.  Each docstring carries
the kernel citation the decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f), every one read there — and
points at the Rocq definition for the argument in full, so there is one
place to correct it.  Rocq's own comments cite most of these functions over
a v6.10-v6.15 window with no line numbers; every number below is v6.18.46
and labelled so.  Rocq's `Z.ltb` and `Nat.eqb` are the decidable `<` and
`=` on `Int` and `Nat`; nothing else changes shape.

The Rocq file was read at f44244ad6b80 and the baseline above is the day
tip it was re-read at: both Rocq Time files are byte-identical between the
two commits (`git diff` is empty), and what moved in between is the
CLOSURE the parity checker hashes — `FdEntry` and `IoState` in `State.v`
(#712's /dev/urandom mirror) — neither of which this arm reads. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Time

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- What a `struct __kernel_old_timeval` the kernel wrote must satisfy:
three conditions on the sixteen bytes, and NOTHING relating them to any
earlier reading — `gettimeofday_spec` says why there is nothing to relate
them to.  The argument in full is on Rocq's `Time.timeval_ok_b`; the
kernel each conjunct rests on, read at Linux v6.18.46 (commit
1f99e9ab748f):

- EXACTLY 16 BYTES.  `struct __kernel_old_timeval` is `__kernel_long_t
  tv_sec` then `__kernel_long_t tv_usec` (include/uapi/linux/time_types.h,
  `__kernel_old_timeval`, :25-28), 8 bytes each on riscv64; `tv_sec_of`
  and `tv_frac_of` (`Sys/Uapi/Time.lean`) read the two fields off the
  bytes.
- `tv_usec` IS NORMALIZED, below 10^6.  The kernel stores
  `ts.tv_nsec / 1000` (kernel/time/time.c, `gettimeofday`, :148) out of
  a `timespec64` that `ktime_get_real_ts64` (kernel/time/timekeeping.c:793-811,
  v6.18.46) finishes with `timespec64_add_ns` (include/linux/time64.h:163-167,
  v6.18.46), which carries whole seconds out of `tv_nsec`; so `tv_nsec`
  is below `NSEC_PER_SEC` and the quotient below 10^6.  This is a
  DIFFERENT normalization constant from `timespec64_valid`'s 10^9
  (include/linux/time64.h:97-106, v6.18.46), which is why this predicate is not a
  `clock_gettime` one parameterized by a unit: getting the two the same
  way round is the whole content of the condition.
- `tv_sec` IS BELOW `KTIME_SEC_MAX`.  This bound is weaker-footed than a
  monotonic clock's, and the difference is worth stating:
  `ktime_get_real_ts64` (kernel/time/timekeeping.c:793-811, v6.18.46) applies NO
  clamp on the read path — it copies `xtime_sec` (:804) and adds the
  nanoseconds (:810).  What is checked is the SET path:
  `timespec64_valid_settod` (include/linux/time64.h:118-126, v6.18.46) refuses a
  `tv_sec` at or above `TIME_SETTOD_SEC_MAX` (:123), which is
  `KTIME_SEC_MAX` less `TIME_UPTIME_SEC_MAX` (:43-44), thirty years of
  headroom, and every writer of the wall clock goes through it:
  `do_settimeofday64` (kernel/time/timekeeping.c:1434-1438, v6.18.46),
  `__timekeeping_inject_offset` (:1494, the test on the RESULTING wall
  time), and `timekeeping_init` (:1811).  So the reading stays under
  `KTIME_SEC_MAX` unless the machine has been up for more than thirty
  years since the last time anything set its clock.  The model takes
  that as the envelope and declines above it, rather than admitting a
  value no kernel is built to produce.  One writer sits behind that
  argument; see linux-process-semantics@ff0313ba4f:bugs/gettimeofday-tv-sec-ceiling-behind-one-writer.md. -/
def timeval_ok_b (bs : List byte) : Bool :=
  (bs.length = 16)
  && (tv_frac_of bs < 1000000)
  && (tv_sec_of bs < KTIME_SEC_MAX)

/-- `gettimeofday tv tz`: read the WALL CLOCK into a `struct timeval`.

A DIFFERENT QUANTITY FROM `m_clock`, AND IT GETS NO MODEL FIELD.  That is
the decision this spec turns on; the argument in full is on Rocq's
`Time.gettimeofday_spec`, and the kernel it rests on, read at Linux
v6.18.46 (commit 1f99e9ab748f), is this.  `CLOCK_REALTIME` carries no
guarantee BETWEEN calls in either direction: it is settable through
`do_settimeofday64` (kernel/time/timekeeping.c:1434-1465), whose only
checks are `timespec64_valid_settod` (:1438) and a guard that stops
`CLOCK_MONOTONIC` going negative (:1449) — neither of which stops the
wall clock being set EARLIER than it currently reads — and `adjtimex`
with `ADJ_SETOFFSET` steps it by a signed `tv_sec` through
`__timekeeping_inject_offset` (:1480-1520), which rejects a `tv_nsec`
outside `[0, 10^9)` (:1485-1486), then applies `timespec64_valid_settod`
to the RESULTING wall time and the same `wall_to_monotonic` comparison
(:1492-1497): a NEGATIVE `tv_sec` passes both.  And none of that needs the
modeled process to do anything.  So there is no cross-call invariant to
record; the reading is `choose`n afresh per call, constrained only by
`timeval_ok_b`.

ORDER.  The kernel's `SYSCALL_DEFINE2(gettimeofday, ...)`
(kernel/time/time.c:140-156, v6.18.46) handles `tv` FIRST (:143-150) and `tz`
SECOND (:151-154); the spec tests `tz` first.  That is not an order
claim and costs no trace: the only answer the spec gives on a non-NULL
`tz` is a decline, and a decline admits nothing whatever `tv` would have
done, so every trace with `tz` non-NULL is declined and every trace with
`tz` NULL is decided by the `tv` block alone, which is the order the
kernel decides it in.  What each gate costs:

- A NON-NULL `tz` IS DECLINED.  The kernel copies `sys_tz`
  (kernel/time/time.c:50 at v6.18.46, a file-scope `struct timezone` with no
  initializer, eight bytes: include/uapi/linux/time.h:33-36, v6.18.46) into it
  (:152) — MUTABLE GLOBAL state whose only writer is
  `do_sys_settimeofday64` (kernel/time/time.c:169-197 at v6.18.46, the assignment
  at :186).  "Nothing ever sets it" is a fact about the deployment, not
  about the kernel, and the model has nowhere to carry the value;
  answering `{0, 0}` would be a confident guess.
- A NULL `tv` IS DECLINED, even though Linux answers 0 there having
  written nothing — the whole `if (likely(tv != NULL))` block (:143) is
  skipped and :155 returns 0.  Rocq declines it for uniformity with
  `clock_gettime`'s gate and because no program calls
  `gettimeofday(NULL, NULL)` on purpose; the Lean twin keeps that
  decline, as it keeps every Rocq arm.
- A `tv` THAT IS NOT WHOLLY WRITABLE IS DECLINED, and the reason is
  stronger than a single `copy_to_user`'s.  The kernel writes `tv` with
  TWO SEPARATE `put_user` calls, `tv_sec` then `tv_usec` (:147-148),
  and returns -EFAULT if either fails (:149).  A 16-byte `tv` straddling
  into an unmapped page therefore COMMITS `tv_sec` and then returns
  -EFAULT — a half-written struct with an error return, a shape this
  model cannot spell as one effect.  Declining is the only honest answer.

  A `tv` THE RANGE TEST REFUSES IS DECIDED BEFORE THE WALK, and which
  answer it gets turns on the same two `put_user`s.  `copy_bytes_map`
  (`State.lean`) asks `access_okb tv 16` before it walks, which is what
  stops a `tv` in the last bytes of the address space wrapping round to
  low memory and reading back as writable.  But a refused 16-byte range
  is NOT a promise that nothing was written.  Each `put_user` carries its
  OWN `access_ok` over its own 8-byte range: riscv's `put_user`
  (arch/riscv/include/asm/uaccess.h:408-415, v6.18.46) tests
  `access_ok(__p, sizeof(*__p))` (:412) — 8 bytes here — and answers
  `-EFAULT` (:414) without storing when it fails, and `__access_ok`
  (include/asm-generic/access_ok.h:31-41, v6.18.46) is
  `(size <= limit) && (addr <= (limit - size))` (:40) with `limit` the
  `TASK_SIZE_MAX` that falls back to `TASK_SIZE` (:15-16), arch/riscv
  defining no other.  So the refused range splits in two:

  - `access_okb tv 8` FALSE: the first store is refused, nothing is
    written, and the call is -EFAULT.  Every wrapping `tv` is in here,
    since a wrap needs `tv >= 2^64 - 15`.  The arm commits to that
    -EFAULT.
  - `access_okb tv 8` TRUE and `access_okb tv 16` FALSE, `tv` in
    `[TASK_SIZE - 15, TASK_SIZE - 8]`: the first store passes its own
    test and the second is refused.  Linux answers -EFAULT having stored
    `tv_sec` if that top page is mapped and nothing if it is not — the
    half-written struct of the bullet above — and the arm declines.

On the modeled path the return is the literal 0 of
kernel/time/time.c:155 (v6.18.46) and the effect is exactly one 16-byte write at
`tv`.

NOT OBSERVABLE THROUGH MUSL, and not reaching the kernel on real
hardware: musl's `gettimeofday` is a `clock_gettime(CLOCK_REALTIME, ...)`
wrapper that never issues syscall 169, and the vDSO serves the call
otherwise; linux-process-semantics@ff0313ba4f:bugs/gettimeofday-not-issued-by-musl.md and
linux-process-semantics@ff0313ba4f:bugs/gettimeofday-served-by-vdso.md carry both.  This arm buys the
raw-syscall caller alone. -/
def gettimeofday_spec (tv tz : word) : Sys SyscallEffect :=
  if !(w_is0 tz) then unmodeled        -- would report `sys_tz`: fail closed
  else if w_is0 tv then unmodeled      -- Linux writes nothing and answers 0
  else
    i <- input ;;
    match copy_bytes_map i.in_wmem tv 16 with
    | none =>
        -- 8, NOT 16: only the FIRST `put_user`'s range being refused
        -- proves nothing was written; the docstring has the bands.
        if !(access_okb tv 8) then err_ret EFAULT
        else unmodeled                 -- the torn band, or a destination not
                                       -- wholly mapped: a partial `put_user`
                                       -- then -EFAULT
    | some _ =>
        bs <- choose (fun bs : List byte => timeval_ok_b bs = true) ;;
        Monad.pure (mkEffect (Z_to_bv 64 0) [(tv, bs)] [])

end LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Time
