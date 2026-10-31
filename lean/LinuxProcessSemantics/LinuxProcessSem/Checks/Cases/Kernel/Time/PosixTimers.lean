-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Kernel/Time/PosixTimers.v

import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic


/-! # Checks.Cases.Kernel.Time.PosixTimers — what `clock_gettime` admits, read off against Linux

Worked examples over `Sys.Kernel.Time.PosixTimers.clock_gettime_spec`, the
twin of `theories/LinuxProcessSem/Checks/Cases/Kernel/Time/PosixTimers.v`
at commit a71fd38a08571d519b9cfc5f66308db5c26da570 (the squash of the 2026-09-11 work onto main; both Rocq files are byte-identical there to f44244ad6b80, where they were first read, and to 7b2d9b92449f, the day tip the port was first rebased onto): every worked case of
that file is here under its Rocq name, marked `rocq-twin:`, beside the
pins the Lean port adds.  Not part of the trusted specification: this file
is QA on the definitions, written to be READ, and every claim in it is a
claim about what the kernel does, with the citation beside it.  Every
kernel line below was read at Linux v6.18.46 (commit 1f99e9ab748f).

HOW THESE ARE STATED.  The Lean tree has no executable checker, so a check
is stated on the relation itself.  Each decision of the spec gets an `iff`
over EVERY outcome `o` — the positive half (what is admitted) and the
negative half (nothing else is) in one statement — and beside it the
concrete mistake a lying kernel could report, refuted on its own.  Where
the arm chooses a reading the admitted set is infinite, and the `iff`
names the reading's conditions explicitly — the kernel's conditions on the
sixteen bytes, not the spec's predicate; the three `*_reads_the_kernel_
conditions` lemmas tie each predicate to its conditions once, and are
what lets `sys_norm` read a guard as those conditions.  Both halves are
closed by the tactics of `Checks/Cases/Tactic.lean`: `sys_norm` reads the
call off its monad primitives and decides the closed gates, `sys_refute`
is `sys_norm` that must close the goal.

WHAT NO PROBE CAN REACH, and why these pins exist beside
`testing/syscall-check/tests/clock_gettime_spec.c`: `m_clock` is internal
state no observation reveals; no kernel can be asked to run
`CLOCK_MONOTONIC` backwards, to stand still on demand, or to report a
reading near either end of an `s64`; and for `CLOCK_REALTIME` and
`CLOCK_PROCESS_CPUTIME_ID` what is left is the ABSENCE of a cross-call
constraint, which shows up as the cases the monotonic arm rejects and
those arms allow.  Where a probe case does show a decision, the pin names
it as its evidence.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.PosixTimers

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.PosixTimers
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude

/-! The spec's unfolding, registered here as every ported Cases file
registers its own; `Checks/Cases/Tactic.lean`'s register carries only the
base's specs. -/
attribute [sys_simp low] clock_gettime_spec.eq_1

/-! ## The numbers these checks spell out -/

/-- The seven modeled ids, as the register value the program passes.
kernel: include/uapi/linux/time.h:CLOCK_REALTIME,CLOCK_MONOTONIC,CLOCK_PROCESS_CPUTIME_ID,CLOCK_MONOTONIC_RAW,CLOCK_REALTIME_COARSE,CLOCK_MONOTONIC_COARSE,CLOCK_BOOTTIME@v6.18.46 -/
example : CLOCK_REALTIME = 0 ∧ CLOCK_MONOTONIC = 1 ∧ CLOCK_PROCESS_CPUTIME_ID = 2
    ∧ CLOCK_MONOTONIC_RAW = 4 ∧ CLOCK_REALTIME_COARSE = 5 ∧ CLOCK_MONOTONIC_COARSE = 6
    ∧ CLOCK_BOOTTIME = 7 := by decide

/-! ## The fixtures

The Rocq cases' call shape, under the Rocq names: `clock_gettime(clkid,
4096)` with nothing readable and exactly sixteen bytes writable at 4096,
against a model whose recorded clock is chosen per case. -/

/-- Sixteen writable bytes at 4096, and nothing else: the landing zone
`Prelude.rlim_out` already lays out for a 16-byte out-parameter, under the
name the Rocq cases give it. -/
def wmem_ts : word → Option byte := rlim_out

/-- `clock_gettime(clkid, 4096)`: a0 is the id, a1 the destination. -/
def clock_input (clkid : word) : SyscallInput :=
  SyscallInput.mkInput 113 [clkid, 4096, 0, 0, 0, 0] (fun _ => none) wmem_ts

/-- The same call with NOTHING writable: the destination gate's shape. -/
def clock_input_unwritable (clkid : word) : SyscallInput :=
  SyscallInput.mkInput 113 [clkid, 4096, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- A model whose monotonic clock reads `t` nanoseconds, set on top of the
bare `mkModel` the Rocq cases use: no fd, no mapping, no input, the clock
at its origin before `with_clock` moves it. -/
def clock_model (t : Int) : Model :=
  with_clock (Z_to_bv 64 t) (mkModel [] demo_vm IEof [] none none none)

/-! `clock_model` enters the normal form by its unfolding, so that a
post-state spelled `clock_model (timespec_ns bs)` under a binder meets the
spec's `with_clock` in one constructor tree. -/
attribute [local sys_simp low] clock_model.eq_1

/-- One second, as the kernel would write it: tv_sec = 1, tv_nsec = 0. -/
def ts_1s : List byte := [1, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]
/-- Two seconds. -/
def ts_2s : List byte := [2, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]
/-- One nanosecond BEFORE one second: tv_sec = 0, tv_nsec = 999999999. -/
def ts_1s_minus : List byte := [0, 0, 0, 0, 0, 0, 0, 0] ++ [255, 201, 154, 59, 0, 0, 0, 0]
/-- tv_sec = 1 with an UNNORMALIZED tv_nsec of exactly 10^9. -/
def ts_denorm : List byte := [1, 0, 0, 0, 0, 0, 0, 0] ++ [0, 202, 154, 59, 0, 0, 0, 0]
/-- The zero reading: tv_sec = 0, tv_nsec = 0, what a `--mutate
poison-writes:0` delivers. -/
def ts_0 : List byte := List.replicate 16 0
/-- 2^63 - 1 ns exactly: tv_sec = 9223372036, tv_nsec = 854775807. -/
def ts_max : List byte := [4, 125, 193, 37, 2, 0, 0, 0] ++ [255, 215, 242, 50, 0, 0, 0, 0]
/-- 2^63 ns: one too many. -/
def ts_over : List byte := [4, 125, 193, 37, 2, 0, 0, 0] ++ [0, 216, 242, 50, 0, 0, 0, 0]
/-- tv_sec = 18446744073, tv_nsec = 709552616 — a reading of 2^64 + 1000
nanoseconds, whose LOW 64 BITS are 1000. -/
def ts_wrap : List byte := [9, 250, 130, 75, 4, 0, 0, 0] ++ [232, 233, 74, 42, 0, 0, 0, 0]
/-- Signed total -2^63 exactly: what `ns_to_timespec64` writes for a
sample of 2^63, `tv_sec = -9223372037`, `tv_nsec = 145224192`. -/
def ts_cpu_min : List byte :=
  [251, 130, 62, 218, 253, 255, 255, 255] ++ [0, 242, 167, 8, 0, 0, 0, 0]
/-- -2^63 - 1: one too few. -/
def ts_cpu_below : List byte :=
  [251, 130, 62, 218, 253, 255, 255, 255] ++ [255, 241, 167, 8, 0, 0, 0, 0]
/-- tv_sec = -1, tv_nsec = 10^9 - 1: the largest sample a `u64` holds,
2^64 - 1, as the `nsec < 0` branch spells it. -/
def ts_cpu_neg1 : List byte :=
  [255, 255, 255, 255, 255, 255, 255, 255] ++ [255, 201, 154, 59, 0, 0, 0, 0]

/-- The landing zone is exactly the sixteen bytes at 4096: the whole
struct fits, and one byte past it does not — `Prelude.rlim_out_is_sixteen_bytes`,
restated under the name the Rocq cases give the zone.
model: `wmem_ts` at its four boundary addresses -/
theorem wmem_ts_is_sixteen_bytes :
    wmem_ts 4095 = none ∧ wmem_ts 4096 = some 0 ∧ wmem_ts 4111 = some 0 ∧ wmem_ts 4112 = none :=
  rlim_out_is_sixteen_bytes

/-- The model records the clock it was given, and nothing else moves the
time field.
model: `m_clock` over `clock_model` -/
theorem m_clock_clock_model : m_clock (clock_model 1000000000) = 1000000000 := by decide

/-- What the fixture bytes decode to, so each case below is read against a
number and not a byte string.  The wrapping reading's low 64 bits are
1000: summed in `word` it would present as a small, admissible time.
model: the timespec decoders over the fixture bytes -/
theorem fixtures_decode :
    timespec_ns ts_1s = 1000000000 ∧ timespec_ns ts_2s = 2000000000
    ∧ timespec_ns ts_1s_minus = 999999999 ∧ timespec_ns ts_0 = 0
    ∧ tv_sec_of ts_denorm = 1 ∧ tv_frac_of ts_denorm = 1000000000
    ∧ timespec_ns ts_max = 2 ^ 63 - 1 ∧ timespec_ns ts_over = 2 ^ 63
    ∧ timespec_ns ts_wrap = 2 ^ 64 + 1000 ∧ Z_to_bv 64 (timespec_ns ts_wrap) = 1000
    ∧ timespec_ns_signed ts_cpu_min = - 2 ^ 63 ∧ timespec_ns_signed ts_cpu_below = - 2 ^ 63 - 1
    ∧ timespec_ns_signed ts_cpu_neg1 = -1 ∧ tv_frac_of ts_cpu_neg1 = 999999999 := by
  decide

/-! ## The three predicates, as the kernel's conditions

Each `*_ok_b` is a `Bool`; these three lemmas say which conditions it is,
so that every `iff` below can name the conditions and never the predicate. -/

/-- A `CLOCK_MONOTONIC` reading is sixteen bytes (`put_timespec64` copies
`sizeof(struct __kernel_timespec)`, kernel/time/time.c:903-912), has a
normalized `tv_nsec` (`ktime_get_ts64`, kernel/time/timekeeping.c:955-975,
sets it to 0 and adds through `timespec64_add_ns`,
include/linux/time64.h:163-167), does not precede the recorded reading,
and is below 2^63 ns.
kernel: kernel/time/timekeeping.c:ktime_get_ts64; include/linux/time64.h:timespec64_add_ns; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem timespec_ok_reads_the_kernel_conditions (bs : List byte) (prev : word) :
    timespec_ok_b bs prev = true ↔
      bs.length = 16 ∧ tv_frac_of bs < 1000000000
        ∧ bv_unsigned prev ≤ timespec_ns bs ∧ timespec_ns bs < 2 ^ 63 := by
  simp only [timespec_ok_b, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]
  exact Iff.rfl

/-- A `CLOCK_REALTIME` reading is the same struct with the same normalized
`tv_nsec` (`ktime_get_real_ts64`, kernel/time/timekeeping.c:793-811) and
the same 2^63 ns ceiling, and nothing relates it to any earlier reading.
kernel: kernel/time/timekeeping.c:ktime_get_real_ts64; include/linux/time64.h:timespec64_add_ns; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem realtime_ok_reads_the_kernel_conditions (bs : List byte) :
    realtime_ok_b bs = true ↔
      bs.length = 16 ∧ tv_frac_of bs < 1000000000 ∧ timespec_ns bs < 2 ^ 63 := by
  simp only [realtime_ok_b, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]
  exact Iff.rfl

/-- A `CLOCK_PROCESS_CPUTIME_ID` reading is the same struct, `tv_nsec`
normalized on all three branches of `ns_to_timespec64`
(kernel/time/time.c:523-542), and its SIGNED total is the `s64` that
function was handed: in `[-2^63, 2^63)`.
kernel: kernel/time/time.c:ns_to_timespec64,put_timespec64@v6.18.46 -/
theorem cputime_ok_reads_the_kernel_conditions (bs : List byte) :
    cputime_ok_b bs = true ↔
      bs.length = 16 ∧ tv_frac_of bs < 1000000000
        ∧ -(2 ^ 63) ≤ timespec_ns_signed bs ∧ timespec_ns_signed bs < 2 ^ 63 := by
  simp only [cputime_ok_b, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]
  exact Iff.rfl

attribute [local sys_simp]
  timespec_ok_reads_the_kernel_conditions realtime_ok_reads_the_kernel_conditions
  cputime_ok_reads_the_kernel_conditions

/-! ## The id gate: `clockid_to_kclock`, first of all

`SYSCALL_DEFINE2(clock_gettime, …)` (kernel/time/posix-timers.c:1136-1152,
Linux v6.18.46) resolves `which_clock` through `clockid_to_kclock`
(:1535-1548) and returns -EINVAL on a NULL `k_clock` (:1143-1144) before
`tp` is touched.  Ids 0..7 index `posix_clocks` (:1518-1533); the other
non-negative ids below the table's size are clocks the model does not
cover or NULL holes (`CLOCK_SGI_CYCLE`, 10, and 12..15 under
`CONFIG_POSIX_AUX_CLOCKS`), ids past it are NULL, and negative ids go to
`clock_posix_dynamic` or `clock_posix_cpu` (:1539-1542) — a live clock
family, several of whose members succeed.  The spec declines every id but
the seven, whatever the kernel answers there: a declared narrowing, not a
claim that those answers are -EINVAL. -/

/-- Every id but the seven modeled ones declines, whatever the
destination, the effect or the model, so no future arm can quietly start
answering for CLOCK_THREAD_CPUTIME_ID, CLOCK_TAI or the alarm variants
without this failing.  The id is tested before anything else,
which is why no hypothesis about `tp` or `i` is needed.  The kernel
answers several of these ids (the probe's `thrcputime` and `cpuclock`
cases succeed on Linux); the decline is the model's, not an -EINVAL.
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock@v6.18.46
rocq-twin: clock_gettime_only_the_modeled_clocks -/
theorem clock_gettime_only_the_modeled_clocks (clkid tp : word)
    (hrt : bv_unsigned clkid ≠ CLOCK_REALTIME)
    (hraw : bv_unsigned clkid ≠ CLOCK_MONOTONIC_RAW)
    (hrtc : bv_unsigned clkid ≠ CLOCK_REALTIME_COARSE)
    (hmc : bv_unsigned clkid ≠ CLOCK_MONOTONIC_COARSE)
    (hbt : bv_unsigned clkid ≠ CLOCK_BOOTTIME)
    (hcp : bv_unsigned clkid ≠ CLOCK_PROCESS_CPUTIME_ID)
    (hmono : bv_unsigned clkid ≠ CLOCK_MONOTONIC)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    clock_gettime_spec clkid tp i m o ↔ o = Unmodeled := by
  have hpc : clockid_percall_b clkid = false := by
    simp only [clockid_percall_b, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨⟨⟨hrt, hraw⟩, hrtc⟩, hmc⟩, hbt⟩
  simp only [clock_gettime_spec.eq_1, hpc, Bool.false_eq_true, ↓reduceIte, hcp, hmono,
    ne_eq, not_false_eq_true]
  sys_norm

/-- `CLOCK_THREAD_CPUTIME_ID` (3): the modeled id's nearest neighbour, the
same `CPUCLOCK_SCHED` sample per thread rather than per thread group
(`clock_thread`, kernel/time/posix-cpu-timers.c:1726-1730, v6.18.46).  It succeeds
on Linux and the model declines.
probe: testing/syscall-check/tests/clock_gettime_spec.c#fail-closed -- thrcputime -/
theorem thread_cputime_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    clock_gettime_spec 3 4096 (clock_input 3) m o ↔ o = Unmodeled := by
  sys_norm

/-- `CLOCK_MONOTONIC_RAW` (4) is answered on the PER-CALL arm, under
`realtime_ok_b` alone: a denormalized `tv_nsec` is refused there as it is
for the wall clock.
kernel: kernel/time/timekeeping.c:ktime_get_raw_ts64@v6.18.46
rocq-twin: monotonic_raw_denormalized_nsec_rejected -/
theorem monotonic_raw_denormalized_nsec_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 4 4096 (clock_input 4) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_denorm)] []) m' evs) := by
  sys_refute

/-- `CLOCK_REALTIME_COARSE` (5) is on the same arm, and its reading is
bounded by `CLOCK_NS_ENVELOPE` like every other per-call reading.
kernel: kernel/time/timekeeping.c:ktime_get_coarse_real_ts64@v6.18.46
rocq-twin: realtime_coarse_reading_at_envelope_rejected -/
theorem realtime_coarse_reading_at_envelope_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 5 4096 (clock_input 5) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_over)] []) m' evs) := by
  sys_refute

/-- `CLOCK_MONOTONIC_COARSE` (6) states no cross-call relation at all, so
it answers against a recorded clock the monotonic arm would decline, and
records nothing.
kernel: kernel/time/timekeeping.c:ktime_get_coarse_ts64@v6.18.46
rocq-twin: monotonic_coarse_ignores_the_recorded_clock -/
theorem monotonic_coarse_ignores_the_recorded_clock :
    clock_gettime_spec 6 4096 (clock_input 6) (clock_model (2 ^ 63))
      (Ok (mkEffect 0 [(4096, ts_1s)] []) (clock_model (2 ^ 63)) []) := by
  sys_norm

/-- `CLOCK_BOOTTIME` (7): advances across suspend where MONOTONIC does not
(`__timekeeping_inject_sleeptime`, kernel/time/timekeeping.c:1857-1870, v6.18.46).
It is on the per-call arm, so a reading BEFORE the recorded monotonic one
is admissible.
rocq-twin: boottime_backwards_reading_is_admissible -/
theorem boottime_backwards_reading_is_admissible :
    clock_gettime_spec 7 4096 (clock_input 7) (clock_model 1000000000)
      (Ok (mkEffect 0 [(4096, ts_1s_minus)] []) (clock_model 1000000000) []) := by
  sys_norm

/-- `CLOCK_TAI` (11): realtime plus the leap-second offset.
probe: testing/syscall-check/tests/clock_gettime_spec.c#fail-closed -- tai -/
theorem tai_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    clock_gettime_spec 11 4096 (clock_input 11) m o ↔ o = Unmodeled := by
  sys_norm

/-- ORDER: an unmodeled id declines with no delivered bytes to judge and
an unwritable destination alike — the id is decoded first, so nothing
about `tp` is consulted.  Both gates decline here, so the kernel's
-EINVAL-before-EFAULT order is not observable on the outcome; what this
pins is that the decline needs no destination at all.  The probe's own
`--mutate clock_gettime:arg0=7,drop-writes` case cannot carry this pin
any more: at `f1006fe8` id 7 is answered, so the case is stated on
`CLOCK_THREAD_CPUTIME_ID` (3), which no recorded case pairs with a
dropped write.
model: `clock_gettime_spec`'s id gate against `clock_input_unwritable` -/
theorem bad_id_with_unwritable_tp_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    clock_gettime_spec 3 4096 (clock_input_unwritable 3) m o ↔ o = Unmodeled := by
  sys_norm

/-! ## The destination gate: `put_timespec64`, after the reading

`put_timespec64` (kernel/time/time.c:903-912, Linux v6.18.46) is one
`copy_to_user` of sixteen bytes, `-EFAULT` on any byte not copied.  On
riscv64 that copy is `__asm_copy_to_user` (arch/riscv/lib/uaccess.S:15-23)
and its scalar fallback, whose fixup at label `10:` returns bytes-not-copied
(`sub a0, t5, a0`, :212-213) after copying forward: a destination whose
last byte is unwritable keeps its first fifteen and still reports -EFAULT.
The spec declines every not-fully-writable destination — the partial case
because there is no single answer, the wholly unwritable case for
uniformity with `getrandom`'s gate — rather than answering -EFAULT. -/

/-- A wholly unwritable `tp` declines on the monotonic arm.  Linux answers
-EFAULT here having written nothing; the decline is the declared
narrowing, so the -EFAULT is refused below rather than admitted.
probe: testing/syscall-check/tests/clock_gettime_spec.c#fail-closed --mutate clock_gettime:wmem-hide:a1:16 -- one -/
theorem unwritable_tp_is_unmodeled (o : outcome SyscallEffect) :
    clock_gettime_spec 1 4096 (clock_input_unwritable 1) (clock_model 0) o ↔ o = Unmodeled := by
  sys_norm

/-- The LAST byte alone unwritable — `tp` = 4097 against the zone ending
at 4112 — declines too: a 15-byte gate would wrongly allow this, and the
copy really faults on byte sixteen after writing fifteen.
probe: testing/syscall-check/tests/clock_gettime_spec.c#fail-closed --mutate clock_gettime:wmem-hide:a1+15:1 -- one -/
theorem straddling_tp_is_unmodeled (o : outcome SyscallEffect) :
    clock_gettime_spec 1 4097 (clock_input 1) (clock_model 0) o ↔ o = Unmodeled := by
  sys_norm

/-- Linux's -EFAULT for the wholly unwritable `tp` is NOT given: the
decline admits no answer at all.
probe: testing/syscall-check/tests/clock_gettime_spec.c#fail-closed --mutate clock_gettime:wmem-hide:a1:16 -- one -/
theorem unwritable_tp_efault_rejected :
    ¬ clock_gettime_spec 1 4096 (clock_input_unwritable 1) (clock_model 0)
        (Ok (mkEffect (errno_ret EFAULT) [] []) (clock_model 0) []) := by
  sys_refute

/-- …and neither is a success that still carries a good struct: the
destination is judged, not the bytes.
probe: testing/syscall-check/tests/clock_gettime_spec.c#fail-closed --mutate clock_gettime:arg1=0xfffffffffffffff8 -- one -/
theorem unwritable_tp_success_rejected :
    ¬ clock_gettime_spec 1 4096 (clock_input_unwritable 1) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_1s)] []) (clock_model 1000000000) []) := by
  sys_refute

/-- The gate reads the WRITABLE view: readable memory hidden entirely
(`in_mem` answers nothing, as every `clock_input` does) changes nothing.
probe: testing/syscall-check/tests/clock_gettime_spec.c#conform --mutate clock_gettime:mem-none -- one -/
theorem destination_gated_on_wmem_not_mem :
    clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
      (Ok (mkEffect 0 [(4096, ts_1s)] []) (clock_model 1000000000) []) := by
  sys_norm

/-! ## The recorded-clock gate, on the monotonic arm only

Before the destination is read, the monotonic arm declines when `m_clock`
has left the range `ktime_t` (`typedef s64 ktime_t`,
include/linux/types.h:126, v6.18.46) can represent.  Unreachable from `init_model` —
the origin is 0 and this arm is the only writer, under a predicate that
holds it below 2^63 — but Rocq's `Progress.receptive` quantifies over arbitrary
model states, so the arm has to be there and has to be right.  The kernel
fact behind the bound: the time-namespace offset, the one thing added to
a monotonic reading beyond the timekeeper, is refused by
`proc_timens_set_offset` (kernel/time/namespace.c:383-461, v6.18.46) past
`KTIME_SEC_MAX / 2` (:427), "to be sure that KTIME_MAX is still
unreachable". -/

/-- A clock already at the top of `ktime_t`'s range declines rather than
inventing a reading.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46
rocq-twin: clock_at_envelope_declines -/
theorem clock_at_envelope_declines (o : outcome SyscallEffect) :
    clock_gettime_spec 1 4096 (clock_input 1) (clock_model (2 ^ 63)) o ↔ o = Unmodeled := by
  sys_norm

/-- One nanosecond below, the arm still answers: the equal reading at
2^63 - 1 is admitted and re-recorded, so the gate is `<` and not `≤`.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46 -/
theorem clock_recorded_at_envelope_minus_one_answers :
    clock_gettime_spec 1 4096 (clock_input 1) (clock_model (2 ^ 63 - 1))
      (Ok (mkEffect 0 [(4096, ts_max)] []) (clock_model (2 ^ 63 - 1)) []) := by
  sys_norm

/-- At the envelope no reading is admitted, not even the one the
recorded clock would make an equal reading.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46 -/
theorem clock_at_envelope_reading_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model (2 ^ 63))
        (Ok (mkEffect 0 [(4096, ts_over)] []) m' evs) := by
  sys_refute

/-! ## `CLOCK_MONOTONIC` (1): the reading, constrained against the last one

`posix_get_monotonic_timespec` (kernel/time/posix-timers.c:217-222, Linux
v6.18.46) is `ktime_get_ts64` (kernel/time/timekeeping.c:955-975) then
`timens_add_monotonic` (include/linux/time_namespace.h:74-79).  The reading
is the environment's, and the one relation the model states is to the
reading before it, which is why `m_clock` exists: the guarantee is
non-decreasing, argued mechanism by mechanism on the Rocq definition
`PosixTimers.clock_gettime_spec`, and not strictly increasing — two reads
inside one counter tick are equal, and `timekeeping_cycles_to_ns`
(kernel/time/timekeeping.c:378-400, v6.18.46) freezes the clock outright on a
backwards counter read rather than propagating it. -/

/-- THE MONOTONIC READING, and nothing else.  From a recorded clock of one
second, every outcome is: return 0, the sixteen bytes written at `tp`, no
event, the model's clock moved to the reading — with the reading a
normalized `struct __kernel_timespec` no earlier than one second and below
2^63 ns.  No errno, no other write, no other model.
kernel: kernel/time/posix-timers.c:clock_gettime,posix_get_monotonic_timespec; kernel/time/timekeeping.c:ktime_get_ts64; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem monotonic_reading_iff (o : outcome SyscallEffect) :
    clock_gettime_spec 1 4096 (clock_input 1) (clock_model 1000000000) o ↔
      ∃ bs : List byte, o = Ok (mkEffect 0 [(4096, bs)] []) (clock_model (timespec_ns bs)) []
        ∧ bs.length = 16 ∧ tv_frac_of bs < 1000000000
        ∧ 1000000000 ≤ timespec_ns bs ∧ timespec_ns bs < 2 ^ 63 := by
  sys_norm

/-- The same from the origin: with nothing recorded, every normalized
reading below 2^63 ns is admitted and recorded, and each refutation below
at `clock_model 0` is an outcome this `iff` excludes — so a refused reading
there is refused, not declined.
kernel: kernel/time/posix-timers.c:clock_gettime,posix_get_monotonic_timespec; kernel/time/timekeeping.c:ktime_get_ts64@v6.18.46 -/
theorem monotonic_reading_from_origin_iff (o : outcome SyscallEffect) :
    clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0) o ↔
      ∃ bs : List byte, o = Ok (mkEffect 0 [(4096, bs)] []) (clock_model (timespec_ns bs)) []
        ∧ bs.length = 16 ∧ tv_frac_of bs < 1000000000
        ∧ 0 ≤ timespec_ns bs ∧ timespec_ns bs < 2 ^ 63 := by
  sys_norm

/-- Two readings that return the SAME nanosecond are admissible:
CLOCK_MONOTONIC never runs backwards, but it is not required to advance,
and a coarse clocksource really does answer two quick calls alike.  The
accepted step leaves `m_clock` where it was.
probe: testing/syscall-check/tests/clock_gettime_spec.c#conform --mutate clock_gettime#1:poison-writes:0 --mutate clock_gettime#2:poison-writes:0 -- two
rocq-twin: clock_equal_reading_is_admissible -/
theorem clock_equal_reading_is_admissible :
    clock_gettime_spec 1 4096 (clock_input 1) (clock_model 1000000000)
      (Ok (mkEffect 0 [(4096, ts_1s)] []) (clock_model 1000000000) []) := by
  sys_norm

/-- A reading of 0 ns is admissible when nothing has been recorded yet:
the origin is 0 and the relation is non-strict.
probe: testing/syscall-check/tests/clock_gettime_spec.c#conform --mutate clock_gettime#1:poison-writes:0 -- one -/
theorem clock_zero_reading_from_origin_admissible :
    clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
      (Ok (mkEffect 0 [(4096, ts_0)] []) (clock_model 0) []) := by
  sys_norm

/-- An advancing reading is admissible too, and the point of the case is
the SECOND half: the accepted step carries the new time into `m_clock`.
That the clock is updated at all is invisible from outside; the
conformance suite sees it only through a later call being judged against
it.
probe: testing/syscall-check/tests/clock_gettime_spec.c#conform -- two
rocq-twin: clock_advancing_reading_records_it -/
theorem clock_advancing_reading_records_it :
    clock_gettime_spec 1 4096 (clock_input 1) (clock_model 1000000000)
      (Ok (mkEffect 0 [(4096, ts_2s)] []) (clock_model 2000000000) []) := by
  sys_norm

/-- …and a step that delivers two seconds while leaving the recorded
clock at one is refused: the record is part of the outcome, which is what
lets the next call be judged.  The probe sees this only indirectly — its
second call's 0 ns reading rejects because the first call recorded.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime#2:poison-writes:0 -- two -/
theorem clock_advancing_reading_not_recorded_rejected :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 1000000000)
        (Ok (mkEffect 0 [(4096, ts_2s)] []) (clock_model 1000000000) []) := by
  sys_refute

/-- A reading one nanosecond EARLIER than the last is refused.  This is
the monotonicity guarantee itself, and no real kernel can be asked to
violate it; the conformance suite reaches it only through `--mutate`.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime#2:poison-writes:0 -- two
rocq-twin: clock_backwards_reading_rejected -/
theorem clock_backwards_reading_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 1000000000)
        (Ok (mkEffect 0 [(4096, ts_1s_minus)] []) m' evs) := by
  sys_refute

/-- The exact boundary of normalization: tv_nsec = 10^9 is refused even
though the total it encodes moves forward.  `timespec64_add_ns`
(include/linux/time64.h:163-167) carries whole seconds out of the
nanosecond field, so a full second never appears there, and admitting it
would make two different byte strings mean the same instant.
kernel: include/linux/time64.h:timespec64_add_ns; kernel/time/timekeeping.c:ktime_get_ts64@v6.18.46
rocq-twin: clock_denormalized_nsec_rejected -/
theorem clock_denormalized_nsec_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_denorm)] []) m' evs) := by
  sys_refute

/-- The other side of that boundary: tv_nsec = 10^9 - 1 is admitted and
recorded on this arm too.  `timespec64_add_ns` (include/linux/time64.h:163-167)
leaves exactly the remainder below `NSEC_PER_SEC` in the field, so the
last nanosecond of a second is a value the kernel really writes, and a
spec stopping one short would refuse a conforming reading.
kernel: include/linux/time64.h:timespec64_add_ns; kernel/time/timekeeping.c:ktime_get_ts64@v6.18.46 -/
theorem clock_last_nanosecond_admissible :
    clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
      (Ok (mkEffect 0 [(4096, ts_1s_minus)] []) (clock_model 999999999) []) := by
  sys_norm

/-- The largest reading `ktime_t` can hold is admissible, and recorded.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46
rocq-twin: clock_reading_at_envelope_minus_one_admissible -/
theorem clock_reading_at_envelope_minus_one_admissible :
    clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
      (Ok (mkEffect 0 [(4096, ts_max)] []) (clock_model (2 ^ 63 - 1)) []) := by
  sys_norm

/-- One nanosecond further is refused: `ktime_t` is signed 64-bit, so
2^63 ns is not a time a kernel can report.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46
rocq-twin: clock_reading_at_envelope_rejected -/
theorem clock_reading_at_envelope_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_over)] []) m' evs) := by
  sys_refute

/-- THE ONE CASE THAT PINS THE `Int` ARITHMETIC.  `timespec_ns` sums
`tv_sec * 10^9 + tv_nsec` in `Int` on purpose: summed in `word` this
reading is 1000 ns — larger than the recorded 0 and far under the
envelope — so a wrapping spelling would let an absurd `tv_sec` present
itself as a small, admissible time.  Every other case in this file passes
under both spellings; this is the only one that separates them.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46
rocq-twin: clock_reading_wrapping_sum_rejected -/
theorem clock_reading_wrapping_sum_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_wrap)] []) m' evs) := by
  sys_refute

/-- `clock_gettime` returns 0, never a count: the return is
`kc->clock_get_timespec`'s 0 (kernel/time/posix-timers.c:1146, v6.18.46) unless the
copy-out fails.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:ret=1 -- one -/
theorem clock_nonzero_return_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (mkEffect 1 [(4096, ts_1s)] []) m' evs) := by
  sys_refute

/-- CLOCK_MONOTONIC always succeeds: -EINVAL is the kernel's answer for an
id with no `k_clock` (kernel/time/posix-timers.c:1143-1144, v6.18.46), and this id
has one.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:ret=-EINVAL -- one -/
theorem clock_einval_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The struct lands at `tp`, not one byte past it.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:shift-writes:1 -- one -/
theorem clock_write_elsewhere_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (mkEffect 0 [(4097, ts_1s)] []) m' evs) := by
  sys_refute

/-- …and it lands wherever `tp` points, not at a fixed address: the same
call with `tp` = 8192, and sixteen writable bytes there, writes at 8192.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_lands_at_tp :
    clock_gettime_spec 1 8192
      (SyscallInput.mkInput 113 [1, 8192, 0, 0, 0, 0] (fun _ => none)
        (bytes_at 8192 (List.replicate 16 0)))
      (clock_model 0)
      (Ok (mkEffect 0 [(8192, ts_1s)] []) (clock_model 1000000000) []) := by
  sys_norm

/-- Only `tv_sec` delivered: a timespec is sixteen bytes.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:trunc-writes:8 -- one -/
theorem clock_short_struct_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (mkEffect 0 [(4096, [1, 0, 0, 0, 0, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- Seventeen bytes is not a timespec either.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:grow-writes:1 -- one -/
theorem clock_long_struct_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_1s ++ [0])] []) m' evs) := by
  sys_refute

/-- A successful `clock_gettime` always delivers the struct.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:drop-writes -- one -/
theorem clock_no_write_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A zero-fill ledger riding along is refused: the effect is the one
write and nothing else.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:smuggle-zeros:a1 -- one -/
theorem clock_smuggled_zeros_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_1s)] [(4096, 16)]) m' evs) := by
  sys_refute

/-- -EFAULT with a WRITABLE destination is refused: `put_timespec64`
(kernel/time/time.c:903-912) fails only when `copy_to_user` reports bytes
not copied, and the sixteen bytes at 4096 are all writable here.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_efault_with_writable_tp_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- One write entry, not two: the struct is one `copy_to_user`.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:split-writes -- one -/
theorem clock_split_write_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_1s.take 8), (4104, ts_1s.drop 8)] []) m' evs) := by
  sys_refute

/-- A smuggled unmap ledger is refused: the effect carries the one write
and nothing else.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:smuggle-unmap:a1 -- one -/
theorem clock_smuggled_unmap_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (SyscallEffect.mkEffectU 0 [(4096, ts_1s)] [] [(4096, 4096)] [] []) m' evs) := by
  sys_refute

/-- …and so is a smuggled pre-effect memory copy.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:smuggle-copy:a1:a1:8 -- one -/
theorem clock_smuggled_copy_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (SyscallEffect.mkEffectU 0 [(4096, ts_1s)] [] [] [MemCopy.mkCopy 4096 4096 8] []) m' evs) := by
  sys_refute

/-- A `tv_nsec` of 2^64 - 1 — every byte 0xff — is refused by the same
normalization conjunct: the field is read unsigned, and
`timespec64_add_ns` (include/linux/time64.h:163-167) leaves a remainder
below 10^9 there, never a full word.
kernel: include/linux/time64.h:timespec64_add_ns; kernel/time/timekeeping.c:ktime_get_ts64@v6.18.46 -/
theorem clock_full_word_nsec_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 1 4096 (clock_input 1) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_1s.take 8 ++ [255, 255, 255, 255, 255, 255, 255, 255])] []) m' evs) := by
  sys_refute

/-! ## `CLOCK_REALTIME` (0): the same struct, none of the guarantee

`posix_get_realtime_timespec` (kernel/time/posix-timers.c:194-198, Linux
v6.18.46) is `ktime_get_real_ts64` (kernel/time/timekeeping.c:793-811).
The wall clock is settable in either direction by anything on the machine
— `do_settimeofday64` (:1434-1465) refuses nothing for setting it EARLIER,
and `adjtimex`'s `ADJ_SETOFFSET` reaches `__timekeeping_inject_offset`
(:1480-1520) with a signed offset straight from userspace — so there is
nothing to relate a reading to, and no model field to record it in.  Each
case below is paired with the CLOCK_MONOTONIC case above that it
contradicts. -/

/-- THE WALL-CLOCK READING, over EVERY model: return 0, the sixteen bytes
at `tp`, no event, the model exactly as it was — with the reading a
normalized `struct __kernel_timespec` below 2^63 ns and related to nothing.
kernel: kernel/time/posix-timers.c:clock_gettime,posix_get_realtime_timespec; kernel/time/timekeeping.c:ktime_get_real_ts64,do_settimeofday64; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem realtime_reading_iff (m : Model) (o : outcome SyscallEffect) :
    clock_gettime_spec 0 4096 (clock_input 0) m o ↔
      ∃ bs : List byte, o = Ok (mkEffect 0 [(4096, bs)] []) m []
        ∧ bs.length = 16 ∧ tv_frac_of bs < 1000000000 ∧ timespec_ns bs < 2 ^ 63 := by
  sys_norm

/-- UNIVERSALLY QUANTIFIED, and the load-bearing one: an accepted call on
ANY per-call id leaves the model EXACTLY as it found it, for every
input, destination, effect and starting model.  This is what stops a
future change quietly giving the wall clock or a coarse clock an
`m_clock`-style field — a
field written by the spec and read by nothing would look like a guarantee
the kernel does not give: `do_settimeofday64` (kernel/time/timekeeping.c:1434-1465)
refuses nothing that sets the clock EARLIER, and `__timekeeping_inject_offset`
(:1480-1520) steps it by a signed value straight from userspace.
kernel: kernel/time/timekeeping.c:do_settimeofday64,__timekeeping_inject_offset@v6.18.46
rocq-twin: clock_gettime_percall_leaves_the_model_alone -/
theorem clock_gettime_percall_leaves_the_model_alone (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (hid : clockid_percall_b clkid = true)
    (h : clock_gettime_spec clkid tp i m (Ok eff m' evs)) : m' = m ∧ evs = [] := by
  rw [clock_gettime_spec.eq_1, if_pos hid] at h
  sys_simp_pass +decide at h
  rcases hr : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | bs
  · rw [hr] at h
    sys_refute at h
  · rw [hr] at h
    sys_norm at h
    obtain ⟨_, -, hm, hevs, -⟩ := h
    exact ⟨hm, hevs⟩

/-- The exact counterpart of `clock_backwards_reading_rejected`: the SAME
bytes, the SAME recorded clock, the other id.  A wall-clock reading one
nanosecond EARLIER than the last monotonic one is admissible, because
CLOCK_REALTIME carries no monotonicity at all — and the accepted step
leaves the recorded clock where it was rather than dragging it backwards.
probe: testing/syscall-check/tests/clock_gettime_spec.c#conform --mutate clock_gettime#2:poison-writes:0 -- realtime2
rocq-twin: realtime_backwards_reading_is_admissible -/
theorem realtime_backwards_reading_is_admissible :
    clock_gettime_spec 0 4096 (clock_input 0) (clock_model 1000000000)
      (Ok (mkEffect 0 [(4096, ts_1s_minus)] []) (clock_model 1000000000) []) := by
  sys_norm

/-- …and a step that drags the recorded clock along with the wall-clock
reading is refused: the arm never writes `m_clock`.
kernel: kernel/time/timekeeping.c:do_settimeofday64@v6.18.46 -/
theorem realtime_recording_rejected :
    ¬ clock_gettime_spec 0 4096 (clock_input 0) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_1s)] []) (clock_model 1000000000) []) := by
  sys_refute

/-- The counterpart of `clock_at_envelope_declines`.  A recorded clock
past what `ktime_t` holds declines a MONOTONIC read, because the choice
that read makes is relative to it and would be empty.  It does not
decline a WALL-CLOCK read: that arm never consults `m_clock`, so there is
nothing for the envelope to be empty against.  This is also the one
observable ORDER between the id gate and the recorded-clock gate: the id
is decoded first, and only id 1 reaches the gate.
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock,posix_get_realtime_timespec@v6.18.46
rocq-twin: realtime_ignores_the_recorded_clock -/
theorem realtime_ignores_the_recorded_clock :
    clock_gettime_spec 0 4096 (clock_input 0) (clock_model (2 ^ 63))
      (Ok (mkEffect 0 [(4096, ts_1s)] []) (clock_model (2 ^ 63)) []) := by
  sys_norm

/-- What the wall clock DOES have to satisfy, it satisfies on the same
terms as the monotonic one.  A tv_nsec of exactly 10^9 is refused:
`ktime_get_real_ts64` sets the field to 0 and normalizes with
`timespec64_add_ns`, so a full second never appears there.
kernel: kernel/time/timekeeping.c:ktime_get_real_ts64; include/linux/time64.h:timespec64_add_ns@v6.18.46
rocq-twin: realtime_denormalized_nsec_rejected -/
theorem realtime_denormalized_nsec_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 0 4096 (clock_input 0) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_denorm)] []) m' evs) := by
  sys_refute

/-- A reading of 2^63 ns is refused for the wall clock too.  The bound is
`timespec64_valid_settod` (include/linux/time64.h:118-126), which every
writer of the wall clock passes and which stops thirty years SHORT of
`KTIME_SEC_MAX` precisely so uptime cannot carry the clock out of
`ktime_t`.
kernel: include/linux/time64.h:timespec64_valid_settod; kernel/time/timekeeping.c:do_settimeofday64@v6.18.46
rocq-twin: realtime_reading_at_envelope_rejected -/
theorem realtime_reading_at_envelope_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 0 4096 (clock_input 0) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_over)] []) m' evs) := by
  sys_refute

/-- The largest wall-clock reading `ktime_t` can hold is admissible, and
is NOT recorded — the pair with the case above makes the boundary
non-vacuous, and the pair with
`clock_reading_at_envelope_minus_one_admissible`, which records the same
bytes, makes the difference between the arms non-vacuous.
kernel: include/linux/time64.h:timespec64_valid_settod; kernel/time/timekeeping.c:do_settimeofday64@v6.18.46
rocq-twin: realtime_reading_at_envelope_minus_one_admissible -/
theorem realtime_reading_at_envelope_minus_one_admissible :
    clock_gettime_spec 0 4096 (clock_input 0) (clock_model 0)
      (Ok (mkEffect 0 [(4096, ts_max)] []) (clock_model 0) []) := by
  sys_norm

/-- The `Int` arithmetic, pinned on this arm too: summed in `word` this
reading is 1000 ns and would be admitted; `timespec_ns` does not wrap, so
the absurd `tv_sec` is refused here as on the monotonic arm.
kernel: include/linux/time64.h:timespec64_valid_settod@v6.18.46 -/
theorem realtime_wrapping_sum_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 0 4096 (clock_input 0) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_wrap)] []) m' evs) := by
  sys_refute

/-- A NEGATIVE tv_sec is refused for the wall clock: `timespec64_valid`
(include/linux/time64.h:97-106), inside `timespec64_valid_settod`,
rejects `tv_sec < 0` for every writer, so no wall-clock reading has one.
The identical bytes are admitted on the CPU-time arm below.
kernel: include/linux/time64.h:timespec64_valid,timespec64_valid_settod@v6.18.46
rocq-twin: realtime_negative_tv_sec_rejected -/
theorem realtime_negative_tv_sec_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 0 4096 (clock_input 0) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_cpu_neg1)] []) m' evs) := by
  sys_refute

/-- CLOCK_REALTIME succeeds: -EINVAL is the answer for an id the model
declines, never for id 0.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:ret=-EINVAL -- realtime -/
theorem realtime_einval_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 0 4096 (clock_input 0) (clock_model 0)
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- Only `tv_sec` delivered on this arm: a timespec is sixteen bytes here too.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:trunc-writes:8 -- realtime -/
theorem realtime_short_struct_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 0 4096 (clock_input 0) (clock_model 0)
        (Ok (mkEffect 0 [(4096, [1, 0, 0, 0, 0, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- This arm's destination is gated like the monotonic one's: a wholly
unwritable `tp` declines.
probe: testing/syscall-check/tests/clock_gettime_spec.c#fail-closed --mutate clock_gettime:wmem-hide:a1:16 -- realtime -/
theorem realtime_unwritable_tp_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    clock_gettime_spec 0 4096 (clock_input_unwritable 0) m o ↔ o = Unmodeled := by
  sys_norm

/-- …and so does the last byte alone.
probe: testing/syscall-check/tests/clock_gettime_spec.c#fail-closed --mutate clock_gettime:wmem-hide:a1+15:1 -- realtime -/
theorem realtime_straddling_tp_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    clock_gettime_spec 0 4097 (clock_input 0) m o ↔ o = Unmodeled := by
  sys_norm

/-- `clock_gettime` returns 0 on this id too, never a count
(kernel/time/posix-timers.c:1146, the getter's 0, unless the copy-out
fails).
kernel: kernel/time/posix-timers.c:clock_gettime,posix_get_realtime_timespec@v6.18.46 -/
theorem realtime_nonzero_return_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 0 4096 (clock_input 0) (clock_model 0)
        (Ok (mkEffect 1 [(4096, ts_1s)] []) m' evs) := by
  sys_refute

/-- One write entry on this arm too.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:split-writes -- realtime -/
theorem realtime_split_write_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 0 4096 (clock_input 0) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_1s.take 8), (4104, ts_1s.drop 8)] []) m' evs) := by
  sys_refute

/-! ## `CLOCK_PROCESS_CPUTIME_ID` (2): not a clock

`clock_process` (kernel/time/posix-cpu-timers.c:1719-1724, Linux v6.18.46)
answers through `process_cpu_clock_get` (:1675-1679) and
`posix_cpu_clock_get` (:358-379): `cpu_clock_sample_group` (:339-356) reads
the thread group's `sum_exec_runtime` into the `CPUCLOCK_SCHED` slot
(`store_samples`, :214-219), a `u64` count of nanoseconds of CPU consumed,
and `ns_to_timespec64` (kernel/time/time.c:523-542, v6.18.46) writes it as an `s64`
— a NEGATIVE `tv_sec` once the count passes 2^63.  That is the whole
difference between this arm and the wall clock's, and the half no probe
can reach: no kernel can be asked for a reading near either end of an
`s64`, and `m_clock` not moving is invisible from outside. -/

/-- THE CPU-TIME READING, over EVERY model: return 0, the sixteen bytes at
`tp`, no event, the model exactly as it was — with the reading a
normalized struct whose SIGNED total is an `s64` number of nanoseconds.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/posix-cpu-timers.c:process_cpu_clock_get,posix_cpu_clock_get,cpu_clock_sample_group,store_samples; kernel/time/time.c:ns_to_timespec64,put_timespec64@v6.18.46 -/
theorem cputime_reading_iff (m : Model) (o : outcome SyscallEffect) :
    clock_gettime_spec 2 4096 (clock_input 2) m o ↔
      ∃ bs : List byte, o = Ok (mkEffect 0 [(4096, bs)] []) m []
        ∧ bs.length = 16 ∧ tv_frac_of bs < 1000000000
        ∧ -(2 ^ 63) ≤ timespec_ns_signed bs ∧ timespec_ns_signed bs < 2 ^ 63 := by
  sys_norm

/-- UNIVERSALLY QUANTIFIED, and the load-bearing one, for the reason
`clock_gettime_percall_leaves_the_model_alone` gives and one more of its
own: an accepted CLOCK_PROCESS_CPUTIME_ID call leaves the model EXACTLY as
it found it, for every input, destination, effect and starting model.
This is what stops a future change relating CPU consumed to `m_clock`.
The two are different quantities and no kernel-enforced inequality
connects them — `thread_group_cputime` (kernel/sched/cputime.c:313-353)
sums `sum_exec_runtime` over every thread, so a thread group on several
CPUs burns CPU faster than any clock advances, and one that is not
scheduled burns none — so a field here could only be written and never
read.
kernel: kernel/sched/cputime.c:thread_group_cputime; kernel/time/posix-cpu-timers.c:cpu_clock_sample_group@v6.18.46
rocq-twin: clock_gettime_cputime_leaves_the_model_alone -/
theorem clock_gettime_cputime_leaves_the_model_alone (i : SyscallInput) (tp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : clock_gettime_spec 2 tp i m (Ok eff m' evs)) : m' = m ∧ evs = [] := by
  sys_simp_pass +decide at h
  rcases hr : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | bs
  · rw [hr] at h
    sys_refute at h
  · rw [hr] at h
    sys_norm at h
    obtain ⟨_, -, hm, hevs, -⟩ := h
    exact ⟨hm, hevs⟩

/-- The counterpart of `realtime_backwards_reading_is_admissible` and
`clock_backwards_reading_rejected`: the SAME bytes, the SAME recorded
clock, a third id.  A CPU-time reading is related to no earlier reading
and to no clock, so it is admissible below the recorded one, and the
accepted step leaves that clock alone.
probe: testing/syscall-check/tests/clock_gettime_spec.c#conform --mutate clock_gettime#2:poison-writes:0 -- cputime2
rocq-twin: cputime_backwards_reading_is_admissible -/
theorem cputime_backwards_reading_is_admissible :
    clock_gettime_spec 2 4096 (clock_input 2) (clock_model 1000000000)
      (Ok (mkEffect 0 [(4096, ts_1s_minus)] []) (clock_model 1000000000) []) := by
  sys_norm

/-- …and a step that records the CPU count as the clock is refused.
kernel: kernel/sched/cputime.c:thread_group_cputime@v6.18.46 -/
theorem cputime_recording_rejected :
    ¬ clock_gettime_spec 2 4096 (clock_input 2) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_1s)] []) (clock_model 1000000000) []) := by
  sys_refute

/-- The counterpart of `clock_at_envelope_declines` and
`realtime_ignores_the_recorded_clock`: a recorded clock past what
`ktime_t` holds declines a MONOTONIC read and not this one, which never
consults `m_clock` either.
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock; kernel/time/posix-cpu-timers.c:process_cpu_clock_get@v6.18.46
rocq-twin: cputime_ignores_the_recorded_clock -/
theorem cputime_ignores_the_recorded_clock :
    clock_gettime_spec 2 4096 (clock_input 2) (clock_model (2 ^ 63))
      (Ok (mkEffect 0 [(4096, ts_1s)] []) (clock_model (2 ^ 63)) []) := by
  sys_norm

/-- The conjunct that survives on this arm still bites: a tv_nsec of
exactly 10^9 is refused, because all three branches of `ns_to_timespec64`
leave that field below 10^9 — the `nsec < 0` one by computing
`NSEC_PER_SEC - rem - 1`.
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46
rocq-twin: cputime_denormalized_nsec_rejected -/
theorem cputime_denormalized_nsec_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 2 4096 (clock_input 2) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_denorm)] []) m' evs) := by
  sys_refute

/-- THE PAIR THAT IS THE WHOLE DIFFERENCE BETWEEN THIS ARM AND THE WALL
CLOCK'S.  A reading with a NEGATIVE tv_sec is what `ns_to_timespec64`
writes once the `u64` sample passes 2^63 (the `nsec < 0` branch,
kernel/time/time.c:531-539), so this arm must allow it;
`realtime_negative_tv_sec_rejected` refuses the identical bytes.
kernel: kernel/time/time.c:ns_to_timespec64; kernel/sched/cputime.c:thread_group_cputime@v6.18.46
rocq-twin: cputime_negative_tv_sec_admissible -/
theorem cputime_negative_tv_sec_admissible :
    clock_gettime_spec 2 4096 (clock_input 2) (clock_model 0)
      (Ok (mkEffect 0 [(4096, ts_cpu_neg1)] []) (clock_model 0) []) := by
  sys_norm

/-- The bottom of the envelope, which exists only on this arm.  A SAMPLE
of exactly 2^63 is admissible: it is the smallest `u64` the `nsec < 0`
branch sees, and so the one whose READING is the most negative of any
this id can report.  (Larger samples read HIGHER, back up towards -1 —
`ts_cpu_neg1` above is the largest sample of all.)
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46
rocq-twin: cputime_at_signed_envelope_admissible -/
theorem cputime_at_signed_envelope_admissible :
    clock_gettime_spec 2 4096 (clock_input 2) (clock_model 0)
      (Ok (mkEffect 0 [(4096, ts_cpu_min)] []) (clock_model 0) []) := by
  sys_norm

/-- One nanosecond lower is refused, which is what makes the bound above
non-vacuous: the argument to `ns_to_timespec64` is an `s64`, so nothing
below -2^63 is in its image.
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46
rocq-twin: cputime_below_signed_envelope_rejected -/
theorem cputime_below_signed_envelope_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 2 4096 (clock_input 2) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_cpu_below)] []) m' evs) := by
  sys_refute

/-- The top of the envelope, where this arm agrees with the other two:
moving the bound onto the signed reading did not delete it.  2^63 - 1 ns
is the largest positive sample, admitted…
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46
rocq-twin: cputime_reading_at_envelope_minus_one_admissible -/
theorem cputime_reading_at_envelope_minus_one_admissible :
    clock_gettime_spec 2 4096 (clock_input 2) (clock_model 0)
      (Ok (mkEffect 0 [(4096, ts_max)] []) (clock_model 0) []) := by
  sys_norm

/-- …and 2^63 is refused here exactly as it is for the wall clock.
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46
rocq-twin: cputime_reading_at_envelope_rejected -/
theorem cputime_reading_at_envelope_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 2 4096 (clock_input 2) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_over)] []) m' evs) := by
  sys_refute

/-- …and the wrapping bytes on this arm: `tv_sec` = 18446744073 is below
2^63, so the signed reading is the unsigned one, 2^64 + 1000 ns, past the
envelope; a wrapping sum would have admitted it as 1000 ns.
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46 -/
theorem cputime_wrapping_sum_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 2 4096 (clock_input 2) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_wrap)] []) m' evs) := by
  sys_refute

/-- THE SCOPE, pinned rather than assumed: the arm describes a kernel
built with `CONFIG_POSIX_TIMERS`.  Without it `posix_cpu_clock_get` is
not built and `do_clock_gettime` (kernel/time/posix-stubs.c:39-58) answers
-EINVAL for every id but REALTIME, MONOTONIC and BOOTTIME (:53-54).  That
answer is NOT admitted here — the Rocq definition names the scope and
`docs/syscalls/clock_gettime.md` records it — so a stubs kernel's -EINVAL
is a reading this arm refuses, and a run under such a kernel is outside
what the arm describes; linux-process-semantics@ff0313ba4f:bugs/clock-gettime-served-by-vdso.md's last
paragraph records the residual.
kernel: kernel/time/posix-stubs.c:do_clock_gettime@v6.18.46 -/
theorem cputime_stubs_einval_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 2 4096 (clock_input 2) (clock_model 0)
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- This arm's destination is gated like the other two: a wholly
unwritable `tp` declines.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem cputime_unwritable_tp_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    clock_gettime_spec 2 4096 (clock_input_unwritable 2) m o ↔ o = Unmodeled := by
  sys_norm

/-- …and so does the last byte alone, on this arm as on the other two: the
literal sixteen of the gate is pinned per arm.
probe: testing/syscall-check/tests/clock_gettime_spec.c#fail-closed --mutate clock_gettime:wmem-hide:a1+15:1 -- cputime -/
theorem cputime_straddling_tp_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    clock_gettime_spec 2 4097 (clock_input 2) m o ↔ o = Unmodeled := by
  sys_norm

/-- Only `tv_sec` delivered: sixteen bytes on this arm too.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:trunc-writes:8 -- cputime -/
theorem cputime_short_struct_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 2 4096 (clock_input 2) (clock_model 0)
        (Ok (mkEffect 0 [(4096, [1, 0, 0, 0, 0, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- 0, never a count, on this id too.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:ret=1 -- cputime -/
theorem cputime_nonzero_return_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 2 4096 (clock_input 2) (clock_model 0)
        (Ok (mkEffect 1 [(4096, ts_1s)] []) m' evs) := by
  sys_refute

/-- One write entry on this arm too.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime:split-writes -- cputime -/
theorem cputime_split_write_rejected (m' : Model) (evs : List event) :
    ¬ clock_gettime_spec 2 4096 (clock_input 2) (clock_model 0)
        (Ok (mkEffect 0 [(4096, ts_1s.take 8), (4104, ts_1s.drop 8)] []) m' evs) := by
  sys_refute

/-! ## Through the dispatcher: syscall 113, and the `int` the id arrives as

`SYSCALL_DEFINE2(clock_gettime, const clockid_t, which_clock, …)`
(kernel/time/posix-timers.c:1136-1137, Linux v6.18.46) declares the id a
`clockid_t`, an `int`, and the riscv wrapper narrows a0 to it
(`__SYSCALL_DEFINEx`, arch/riscv/include/asm/syscall_wrapper.h:82-88,
through `__SC_CAST`, include/linux/syscalls.h:132): the table applies
`Syscall.clockid32` once, at the ABI boundary, and the spec receives an
already-truncated id. -/

/-- Syscall 113 with a0 = 0 reaches the wall-clock arm through the table.
kernel: include/uapi/asm-generic/unistd.h:__NR_clock_gettime; kernel/time/posix-timers.c:clock_gettime,posix_get_realtime_timespec@v6.18.46 -/
theorem sysno_113_is_clock_gettime (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 113 [0, 4096, 0, 0, 0, 0] (fun _ => none) wmem_ts)
        demo_model o ↔
      ∃ bs : List byte, o = Ok (mkEffect 0 [(4096, bs)] []) demo_model []
        ∧ bs.length = 16 ∧ tv_frac_of bs < 1000000000 ∧ timespec_ns bs < 2 ^ 63 := by
  sys_norm

/-- Syscall 113 with a0 = 2 reaches the CPU-time arm through the table: the
Rocq cases run every id-2 example through `check_syscall`, and a table edit
gating id 2 would pass every pin stated on the spec alone.
probe: testing/syscall-check/tests/clock_gettime_spec.c#conform -- cputime -/
theorem sysno_113_is_cputime (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 113 [2, 4096, 0, 0, 0, 0] (fun _ => none) wmem_ts)
        demo_model o ↔
      ∃ bs : List byte, o = Ok (mkEffect 0 [(4096, bs)] []) demo_model []
        ∧ bs.length = 16 ∧ tv_frac_of bs < 1000000000
        ∧ -(2 ^ 63) ≤ timespec_ns_signed bs ∧ timespec_ns_signed bs < 2 ^ 63 := by
  sys_norm

/-- Syscall 113 with a0 = 1 records the reading through the table: two
real readings, the second no earlier than the first.
probe: testing/syscall-check/tests/clock_gettime_spec.c#conform -- two -/
theorem sysno_113_monotonic_records :
    syscall_spec (SyscallInput.mkInput 113 [1, 4096, 0, 0, 0, 0] (fun _ => none) wmem_ts)
      (clock_model 1000000000)
      (Ok (mkEffect 0 [(4096, ts_2s)] []) (clock_model 2000000000) []) := by
  sys_norm

/-- …and refuses the backwards reading through the table too.
probe: testing/syscall-check/tests/clock_gettime_spec.c#reject --mutate clock_gettime#2:poison-writes:0 -- two -/
theorem sysno_113_backwards_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 113 [1, 4096, 0, 0, 0, 0] (fun _ => none) wmem_ts)
        (clock_model 1000000000)
        (Ok (mkEffect 0 [(4096, ts_1s_minus)] []) m' evs) := by
  sys_refute

/-- a0 = 2^32 + 1 is CLOCK_MONOTONIC: `clockid_t` is an `int`, so bit 32
of the register is not part of what the kernel reads, and the call
answers as id 1 does.
probe: testing/syscall-check/tests/clock_gettime_spec.c#conform -- wide -/
theorem sysno_113_wide_id_truncates (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 113 [Z_to_bv 64 (2 ^ 32 + 1), 4096, 0, 0, 0, 0]
                    (fun _ => none) wmem_ts)
        (clock_model 1000000000) o ↔
      ∃ bs : List byte, o = Ok (mkEffect 0 [(4096, bs)] []) (clock_model (timespec_ns bs)) []
        ∧ bs.length = 16 ∧ tv_frac_of bs < 1000000000
        ∧ 1000000000 ≤ timespec_ns bs ∧ timespec_ns bs < 2 ^ 63 := by
  sys_norm

/-- a0 = 2^32 is CLOCK_REALTIME once the `int` is read: the call answers
as id 0 does — here with the recorded clock past the envelope, which only
the monotonic arm declines, so the truncation is shown landing on id 0 and
not on id 1.
probe: testing/syscall-check/tests/clock_gettime_spec.c#conform --mutate clock_gettime:arg0=0x100000000 -- one -/
theorem sysno_113_wide_zero_is_realtime :
    syscall_spec (SyscallInput.mkInput 113 [Z_to_bv 64 (2 ^ 32), 4096, 0, 0, 0, 0] (fun _ => none) wmem_ts)
      (clock_model (2 ^ 63))
      (Ok (mkEffect 0 [(4096, ts_1s)] []) (clock_model (2 ^ 63)) []) := by
  sys_norm

/-- a0 = 2^32 + 2 is CLOCK_PROCESS_CPUTIME_ID: the negative `tv_sec` only
that arm allows is admitted.
probe: testing/syscall-check/tests/clock_gettime_spec.c#conform --mutate clock_gettime:arg0=0x100000002 -- one -/
theorem sysno_113_wide_two_is_cputime :
    syscall_spec (SyscallInput.mkInput 113 [Z_to_bv 64 (2 ^ 32 + 2), 4096, 0, 0, 0, 0] (fun _ => none) wmem_ts)
      (clock_model 0)
      (Ok (mkEffect 0 [(4096, ts_cpu_neg1)] []) (clock_model 0) []) := by
  sys_norm

/-- a0 = -6, a per-process CPU clock reached by the pid-encoded path
(`clockid_to_kclock` sends a negative id to `clock_posix_cpu` unless
`(id & CLOCKFD_MASK) == CLOCKFD` names a dynamic clock,
kernel/time/posix-timers.c:1539-1542, v6.18.46): the SAME kernel sample as id 2, and
it succeeds on Linux.  The model declines the whole negative half of the
id space, a live family it does not decode, so the reading the kernel
really gives is refused here rather than answered — and, per
`clock_gettime_only_the_modeled_clocks`, nothing is answered in its place.
(Stated as a refutation: a decline through the dispatcher is about this
argument, not about syscall 113, which the table models.)
probe: testing/syscall-check/tests/clock_gettime_spec.c#fail-closed -- cpuclock -/
theorem sysno_113_negative_cpuclock_reading_rejected :
    ¬ syscall_spec (SyscallInput.mkInput 113 [Z_to_bv 64 (-6), 4096, 0, 0, 0, 0] (fun _ => none) wmem_ts)
        (clock_model 0) (Ok (mkEffect 0 [(4096, ts_1s)] []) (clock_model 0) []) := by
  sys_refute

/-- a0 = -1 takes the same CPU-clock path and is -EINVAL there for a
reason of its own; the model declines it with the rest, so that -EINVAL
is refused too, not agreed with.
probe: testing/syscall-check/tests/clock_gettime_spec.c#fail-closed -- negid -/
theorem sysno_113_negative_one_einval_rejected :
    ¬ syscall_spec (SyscallInput.mkInput 113 [Z_to_bv 64 (-1), 4096, 0, 0, 0, 0] (fun _ => none) wmem_ts)
        (clock_model 0) (Ok (mkEffect (errno_ret EINVAL) [] []) (clock_model 0) []) := by
  sys_refute

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.PosixTimers
