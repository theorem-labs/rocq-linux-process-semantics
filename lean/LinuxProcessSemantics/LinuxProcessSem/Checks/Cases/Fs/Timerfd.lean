import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570
unported: timerfd_model -- the spec reads no field of the model, so every pin here quantifies over the model instead of naming one -/

/-! rocq-cases: a71fd38a08571d519b9cfc5f66308db5c26da570
covers: timerfd_create_dropped_flag_bits_are_einval -- flag_bit22_is_einval, flag_bit22_descriptor_rejected, flag_bit15_is_einval, flag_bit20_is_einval
covers: timerfd_create_admitted_clocks_decline -- clock_realtime_is_unmodeled, clock_monotonic_is_unmodeled, clock_boottime_is_unmodeled, clock_realtime_alarm_is_unmodeled, clock_boottime_alarm_is_unmodeled, clock_monotonic_descriptor_rejected, clock_realtime_alarm_eperm_rejected, clock_realtime_alarm_einval_rejected, clock_boottime_alarm_einval_rejected, clock_process_cputime_is_einval
covers: timerfd_create_narrows_both_arguments -- high_clock_half_aliases_and_declines, high_clock_half_einval_rejected, high_flag_half_aliases_and_declines, high_flag_half_einval_rejected, high_half_on_bad_clock_is_einval -/

/-! # Checks.Cases.Fs.Timerfd — what `timerfd_create` admits, read off against Linux

Worked examples over `Sys.Fs.Timerfd.timerfd_create_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Fs/Timerfd.v`.  Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about what the kernel does, with the
citation beside it.

HOW THESE ARE STATED.  The Rocq file reads the spec through the executable
checker and the dispatcher (`check_syscall` on inputs built by `tfd_in`).
The pins here are stated on the relation itself, as
`Checks/Cases/Mm/Mmap.lean` does, and the register above maps each Rocq
`Example` to the pins that state its facts on the relation — the -EINVAL
and the refused descriptor for the same words, the decline of the same
clock ids, the narrowing of both arguments.  The checker's own pins are
`Checks/Cases/Checks/Sys/Fs/Timerfd.lean`'s, which imports this file,
restates the first two examples on `check_timerfd_create`, and, since the
registration of 85 (`Checks/Arms/Fs/Timerfd.lean`), all three through the
Lean `check_syscall`; that file's header says why none of them is here —
this file is the spec's mutation twin, and a checker in its import
closure turns every behaviour-changing spec mutant into a stillbirth
before a pin here is read.  The strongest shape
is an `iff` over EVERY outcome `o`, which pins the positive half (the
-EINVAL, or the decline) and the negative half (nothing else: not a
descriptor, not another errno, not a changed model, not an event) in one
statement; beside each `iff` sits the refutation of the concrete mistake
the decision could have made, so that a reader sees the answer Linux would
have given and the one it would not.  `timerfd_create` reads no field of
the model and no byte of the input, so every pin quantifies over both —
that is what the Rocq `timerfd_model` fixture stood in for, and it is
strictly more than a fixture says.

TWO LAYERS, PINNED SEPARATELY.  The gate itself is pinned on
`timerfd_create_spec` with the two words given directly, as the arm
receives them.  The facts the arm cannot see — that the clock id is
ARGUMENT 0 and the flag word ARGUMENT 1, and that both are NARROWED to 32
bits before the gate — are the table's (`Sys/SyscallTable.lean`,
`clockid32 (in_arg i 0)` and `flag32 (in_arg i 1)`), and are pinned
through `Specs.syscall_spec` on inputs built by `tfd_in`, the twin of the
Rocq builder.  No pin mentions both.  The checker's answers are a third
layer, pinned in `Checks/Cases/Checks/Sys/Fs/Timerfd.lean`.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Timerfd

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Timerfd
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! The spec's unfolding, registered where its pins are (`Checks/Cases/
Tactic.lean`'s register says what a spec owes); its gate
`timerfd_create_einval_b` is decided, never unfolded.  The two outcome
helpers below are registered `local`: they are QA spellings this file
alone reads, and the shared set must not carry them into the next Cases
file. -/
attribute [sys_simp low] timerfd_create_spec.eq_1

/-! ## The words these checks spell out

The mask is `O_CLOEXEC | O_NONBLOCK` (`TFD_CREATE_FLAGS`,
include/linux/timerfd.h:14-16, Linux v6.18.46); `#define O_NONBLOCK
00004000` and `#define O_CLOEXEC 02000000` (include/uapi/asm-generic/fcntl.h:38
and :62, Linux v6.18.46) put the two bits at 11 and 19. -/

/-- The create mask is the two `O_` bits.
kernel: fs/timerfd.c:timerfd_create; include/uapi/asm-generic/fcntl.h:O_CLOEXEC,O_NONBLOCK@v6.18.46 -/
example : TFD_CREATE_FLAGS = 2 ^ 19 + 2 ^ 11 := by decide
/-- `O_CLOEXEC`, bit 19.
kernel: include/uapi/asm-generic/fcntl.h:O_CLOEXEC@v6.18.46 -/
example : O_CLOEXEC = 2 ^ 19 := by decide
/-- `O_NONBLOCK`, bit 11.
kernel: include/uapi/asm-generic/fcntl.h:O_NONBLOCK@v6.18.46 -/
example : O_NONBLOCK = 2 ^ 11 := by decide
/-- The five admitted ids, at their uapi values.
kernel: include/uapi/linux/time.h:CLOCK_REALTIME,CLOCK_MONOTONIC,CLOCK_BOOTTIME,CLOCK_REALTIME_ALARM,CLOCK_BOOTTIME_ALARM@v6.18.46 -/
example : CLOCK_REALTIME = 0 ∧ CLOCK_MONOTONIC = 1 ∧ CLOCK_BOOTTIME = 7 ∧
    CLOCK_REALTIME_ALARM = 8 ∧ CLOCK_BOOTTIME_ALARM = 9 := by decide

/-- The outcome the -EINVAL arm admits and nothing else: the errno in `a0`,
no writes, no zero-fill, the model unchanged, no event.  Named, where
`Checks/Cases/Mm/Mmap.lean` spells the literal in every statement, so that
the literal is written once and a pin reads as "this input answers
-EINVAL"; the register line makes the name transparent to `sys_norm`. -/
def einval_outcome (m : Model) : outcome SyscallEffect :=
  Ok (mkEffect (errno_ret EINVAL) [] []) m []

attribute [local sys_simp low] einval_outcome.eq_1

/-- A descriptor: the answer a kernel gives past the gate, which no pin
here may accept — the model has no timer kind to hold it. -/
def descriptor_outcome (m : Model) : outcome SyscallEffect :=
  Ok (mkEffect 3 [] []) m []

attribute [local sys_simp low] descriptor_outcome.eq_1

/-! ## The flag half of the gate

`flags & ~TFD_CREATE_FLAGS` is the `if` condition itself
(`SYSCALL_DEFINE2(timerfd_create)`, fs/timerfd.c:404, Linux v6.18.46, commit
1f99e9ab748f): ANY bit outside `TFD_CLOEXEC|TFD_NONBLOCK` is -EINVAL, and
the two bits inside it pass.  Bit 0 is `TFD_TIMER_ABSTIME`, a
`timerfd_settime` flag (`TFD_SETTIME_FLAGS`, include/linux/timerfd.h:18),
which `timerfd_create` refuses; bits 15, 20 and 22 are the ordinary
swallowed bits the Rocq file walks; bit 31 is the sign bit of the `int`,
where a `> 0` test on the residue would have admitted it and the kernel's
truthiness test does not.  `tests/timerfd_create.c` pins bit 31 and the
all-ones word against a real run; these pin the class on the spec. -/

/-- Bit 0 is `TFD_TIMER_ABSTIME`, a `timerfd_settime` flag: -EINVAL.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem flag_bit0_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 1) i m o ↔
      o = einval_outcome m := by
  sys_norm

/-- A descriptor for bit 0 is refused: the gate returns before any descriptor is allocated.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem flag_bit0_descriptor_rejected (i : SyscallInput) (m : Model) :
    ¬ timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 1) i m
        (descriptor_outcome m) := by
  sys_refute

/-- Bit 1 is `TFD_TIMER_CANCEL_ON_SET`, the other half of
`TFD_SETTIME_FLAGS` (include/linux/timerfd.h:18): -EINVAL.  Pinned beside
bit 0 because the two together are the whole of the OTHER timerfd flag
word, and reading that word for this call is the confusion the gate
refuses — a mask widened to `TFD_CREATE_FLAGS | TFD_SETTIME_FLAGS` passes
every other pin in this file.  `tests/timerfd_create.c`'s `einval` case
asserts it against the kernel.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem flag_bit1_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 1)) i m o ↔
      o = einval_outcome m := by
  sys_norm

/-- Bit 15, a swallowed bit in the second run of them.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem flag_bit15_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 15)) i m o ↔
      o = einval_outcome m := by
  sys_norm

/-- Bit 20, a swallowed bit in the third run of them.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem flag_bit20_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 20)) i m o ↔
      o = einval_outcome m := by
  sys_norm

/-- Bit 22, an ordinary swallowed bit.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem flag_bit22_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 22)) i m o ↔
      o = einval_outcome m := by
  sys_norm

/-- A descriptor for bit 22 is refused: the gate returns before any descriptor is allocated.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem flag_bit22_descriptor_rejected (i : SyscallInput) (m : Model) :
    ¬ timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 22)) i m
        (descriptor_outcome m) := by
  sys_refute

/-- Bit 31: the residue `0x80000000` is negative as an `int` and nonzero,
and the kernel tests nonzero.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem flag_bit31_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 31)) i m o ↔
      o = einval_outcome m := by
  sys_norm

/-- A descriptor for bit 31 is refused: the residue is nonzero however its sign is read.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem flag_bit31_descriptor_rejected (i : SyscallInput) (m : Model) :
    ¬ timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 31)) i m
        (descriptor_outcome m) := by
  sys_refute

/-- The all-ones 32-bit word, `flags = -1` as the kernel reads it.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem flag_all_ones_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 (2 ^ 32 - 1)) i m o ↔
      o = einval_outcome m := by
  sys_norm

/-- The two bits inside the mask pass the gate, singly and together, and
what follows is a descriptor the model cannot hold: `Unmodeled`, and only
that.  The refutation is the -EINVAL a spec that masked the wrong bits
would answer for the pair.
kernel: fs/timerfd.c:timerfd_create; include/uapi/asm-generic/fcntl.h:O_CLOEXEC,O_NONBLOCK@v6.18.46 -/
theorem flag_cloexec_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 O_CLOEXEC) i m o ↔
      o = Unmodeled := by
  sys_norm

/-- `TFD_NONBLOCK` alone passes the gate: declined.
kernel: fs/timerfd.c:timerfd_create; include/uapi/asm-generic/fcntl.h:O_CLOEXEC,O_NONBLOCK@v6.18.46 -/
theorem flag_nonblock_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 O_NONBLOCK) i m o ↔
      o = Unmodeled := by
  sys_norm

/-- Both mask bits together pass the gate: declined.
kernel: fs/timerfd.c:timerfd_create; include/uapi/asm-generic/fcntl.h:O_CLOEXEC,O_NONBLOCK@v6.18.46 -/
theorem flag_both_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 TFD_CREATE_FLAGS) i m o ↔
      o = Unmodeled := by
  sys_norm

/-- -EINVAL for the in-mask pair is refused: a spec masking the wrong bits would answer it.
kernel: fs/timerfd.c:timerfd_create; include/uapi/asm-generic/fcntl.h:O_CLOEXEC,O_NONBLOCK@v6.18.46 -/
theorem flag_both_einval_rejected (i : SyscallInput) (m : Model) :
    ¬ timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 TFD_CREATE_FLAGS) i m
        (einval_outcome m) := by
  sys_refute

/-! ## The clock half of the gate

The five ids the kernel's own five-way comparison admits
(`SYSCALL_DEFINE2(timerfd_create)`, fs/timerfd.c:405-409, Linux v6.18.46)
all pass to a path that ends in a descriptor or an errno the model cannot
resolve — -EPERM from `capable(CAP_WAKE_ALARM)` (:412-415) on the two alarm
ids — so each is `Unmodeled` and only that.  The alarm pair is the point:
a whitelist shortened to the three ids the model could in principle
serve would answer -EINVAL where Linux answers -EPERM or a descriptor, and
the refutations below offer exactly that -EINVAL. -/

/-- `CLOCK_REALTIME` passes the gate: declined, the descriptor has no `FdEntry` kind.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_realtime_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_REALTIME) (Z_to_bv 64 0) i m o ↔ o = Unmodeled := by
  sys_norm

/-- `CLOCK_MONOTONIC` passes the gate: declined, the descriptor has no `FdEntry` kind.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_monotonic_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 0) i m o ↔ o = Unmodeled := by
  sys_norm

/-- `CLOCK_BOOTTIME` passes the gate: declined, the descriptor has no `FdEntry` kind.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_boottime_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_BOOTTIME) (Z_to_bv 64 0) i m o ↔ o = Unmodeled := by
  sys_norm

/-- `CLOCK_REALTIME_ALARM` passes the gate: declined, since -EPERM or a descriptor follows and neither is modeled.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_realtime_alarm_is_unmodeled (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_REALTIME_ALARM) (Z_to_bv 64 0) i m o ↔
      o = Unmodeled := by
  sys_norm

/-- `CLOCK_BOOTTIME_ALARM` passes the gate: declined, since -EPERM or a descriptor follows and neither is modeled.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_boottime_alarm_is_unmodeled (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_BOOTTIME_ALARM) (Z_to_bv 64 0) i m o ↔
      o = Unmodeled := by
  sys_norm

/-- A descriptor is not admitted for an admitted id: the decline is a
decline, not a success the model happens to spell.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_monotonic_descriptor_rejected (i : SyscallInput) (m : Model) :
    ¬ timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 0) i m
        (descriptor_outcome m) := by
  sys_refute

/-- The shortened whitelist's -EINVAL is refused on both alarm ids.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_realtime_alarm_einval_rejected (i : SyscallInput) (m : Model) :
    ¬ timerfd_create_spec (Z_to_bv 64 CLOCK_REALTIME_ALARM) (Z_to_bv 64 0) i m
        (einval_outcome m) := by
  sys_refute

/-- The shortened whitelist's -EINVAL is refused on `CLOCK_BOOTTIME_ALARM` too.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_boottime_alarm_einval_rejected (i : SyscallInput) (m : Model) :
    ¬ timerfd_create_spec (Z_to_bv 64 CLOCK_BOOTTIME_ALARM) (Z_to_bv 64 0) i m
        (einval_outcome m) := by
  sys_refute

/-- …and so is the -EPERM an unprivileged caller really gets: the model has
no `CAP_WAKE_ALARM` (include/uapi/linux/capability.h:368, Linux v6.18.46)
to decide it with, so it declines rather than "happens to answer the right
errno".
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_realtime_alarm_eperm_rejected (i : SyscallInput) (m : Model) :
    ¬ timerfd_create_spec (Z_to_bv 64 CLOCK_REALTIME_ALARM) (Z_to_bv 64 0) i m
        (Ok (mkEffect (errno_ret EPERM) [] []) m []) := by
  sys_refute

/-! ### The admitted set is a set, not a range

The ids are 0, 1, 7, 8 and 9.  A test that read them as the interval
`0 ≤ clockid ≤ 9` would swallow 2 through 6, and every `Unmodeled` pin above
stays green under a change that declines MORE; these are what notice it.
`CLOCK_PROCESS_CPUTIME_ID` (2), `CLOCK_THREAD_CPUTIME_ID` (3),
`CLOCK_MONOTONIC_RAW` (4), `CLOCK_REALTIME_COARSE` (5) and
`CLOCK_MONOTONIC_COARSE` (6) (include/uapi/linux/time.h:51-55, Linux
v6.18.46) each fail the five-way comparison and take the gate's -EINVAL;
so does `CLOCK_TAI` (11, :64) above the set, and so does the all-ones word,
`clockid = -1` as the kernel reads it. -/

/-- `CLOCK_PROCESS_CPUTIME_ID` (2) fails the five-way test: -EINVAL.
kernel: fs/timerfd.c:timerfd_create; include/uapi/linux/time.h:CLOCK_PROCESS_CPUTIME_ID@v6.18.46 -/
theorem clock_process_cputime_is_einval (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_PROCESS_CPUTIME_ID) (Z_to_bv 64 0) i m o ↔
      o = einval_outcome m := by
  sys_norm

/-- A descriptor for `CLOCK_PROCESS_CPUTIME_ID` is refused: it fails the five-way test.
kernel: fs/timerfd.c:timerfd_create; include/uapi/linux/time.h:CLOCK_PROCESS_CPUTIME_ID@v6.18.46 -/
theorem clock_process_cputime_descriptor_rejected (i : SyscallInput) (m : Model) :
    ¬ timerfd_create_spec (Z_to_bv 64 CLOCK_PROCESS_CPUTIME_ID) (Z_to_bv 64 0) i m
        (descriptor_outcome m) := by
  sys_refute

/-- `CLOCK_THREAD_CPUTIME_ID` (3) fails the five-way test: -EINVAL.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_3_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 3) (Z_to_bv 64 0) i m o ↔ o = einval_outcome m := by
  sys_norm

/-- `CLOCK_MONOTONIC_RAW` (4) fails the five-way test: -EINVAL.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_4_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 4) (Z_to_bv 64 0) i m o ↔ o = einval_outcome m := by
  sys_norm

/-- `CLOCK_REALTIME_COARSE` (5) fails the five-way test: -EINVAL.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_5_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 5) (Z_to_bv 64 0) i m o ↔ o = einval_outcome m := by
  sys_norm

/-- `CLOCK_MONOTONIC_COARSE` (6) fails the five-way test: -EINVAL.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_6_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 6) (Z_to_bv 64 0) i m o ↔ o = einval_outcome m := by
  sys_norm

/-- `CLOCK_SGI_CYCLE` (10) fails the five-way test: -EINVAL.  It is the
one id INSIDE the uapi's contiguous run that no arm of the test names, so
it is what separates the set from the interval `0 ≤ clockid ≤ 10`; the
ids 2 to 6 above separate it from `0 ≤ clockid ≤ 9`.  Its driver was
removed and the id is kept as a placeholder
(include/uapi/linux/time.h:59-63), which is why a reader reconstructing
the set from the header can miss it.
kernel: fs/timerfd.c:timerfd_create; include/uapi/linux/time.h:CLOCK_SGI_CYCLE@v6.18.46 -/
theorem clock_sgi_cycle_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 10) (Z_to_bv 64 0) i m o ↔ o = einval_outcome m := by
  sys_norm

/-- `CLOCK_TAI` (11), above the set, fails the five-way test: -EINVAL.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_tai_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 11) (Z_to_bv 64 0) i m o ↔ o = einval_outcome m := by
  sys_norm

/-- The all-ones 32-bit id, `clockid = -1` as the kernel reads it: -EINVAL.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_all_ones_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 (2 ^ 32 - 1)) (Z_to_bv 64 0) i m o ↔
      o = einval_outcome m := by
  sys_norm

/-- A decline for `clockid = -1` is refused: the gate answers it.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem clock_all_ones_unmodeled_rejected (i : SyscallInput) (m : Model) :
    ¬ timerfd_create_spec (Z_to_bv 64 (2 ^ 32 - 1)) (Z_to_bv 64 0) i m Unmodeled := by
  sys_refute

/-! ## Precedence: the gate is one `if`, and it sits above the capability test

The flag test and the clock test are disjuncts of ONE condition
(fs/timerfd.c:404-410, Linux v6.18.46), so an input failing both is -EINVAL
once, not two errnos in some order.  The `capable(CAP_WAKE_ALARM)` test is
the NEXT `if` (:412-415), so an unknown flag bit beside
`CLOCK_REALTIME_ALARM` is -EINVAL and never -EPERM — the one precedence
fact the arm encodes, which `tests/timerfd_create.c` pins against a real
run by offering -EPERM for exactly this input. -/

/-- An unknown flag bit beside `CLOCK_REALTIME_ALARM` is -EINVAL: the gate fires first.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem alarm_with_bad_flag_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_REALTIME_ALARM) (Z_to_bv 64 1) i m o ↔
      o = einval_outcome m := by
  sys_norm

/-- -EPERM is refused: the flag test fires before the capability test.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem alarm_with_bad_flag_eperm_rejected (i : SyscallInput) (m : Model) :
    ¬ timerfd_create_spec (Z_to_bv 64 CLOCK_REALTIME_ALARM) (Z_to_bv 64 1) i m
        (Ok (mkEffect (errno_ret EPERM) [] []) m []) := by
  sys_refute

/-- Both halves failing is one -EINVAL: the two are disjuncts of one condition.
kernel: fs/timerfd.c:timerfd_create; include/uapi/linux/time.h:CLOCK_PROCESS_CPUTIME_ID@v6.18.46 -/
theorem bad_clock_with_bad_flag_is_einval (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    timerfd_create_spec (Z_to_bv 64 CLOCK_PROCESS_CPUTIME_ID) (Z_to_bv 64 (2 ^ 22)) i m o ↔
      o = einval_outcome m := by
  sys_norm

/-- A decline is refused when both halves fail: -EINVAL is decided at the gate.
kernel: fs/timerfd.c:timerfd_create; include/uapi/linux/time.h:CLOCK_PROCESS_CPUTIME_ID@v6.18.46 -/
theorem bad_clock_with_bad_flag_unmodeled_rejected (i : SyscallInput) (m : Model) :
    ¬ timerfd_create_spec (Z_to_bv 64 CLOCK_PROCESS_CPUTIME_ID) (Z_to_bv 64 (2 ^ 22)) i m
        Unmodeled := by
  sys_refute

/-! ## The -EINVAL is inert

The kernel returns at fs/timerfd.c:410 (Linux v6.18.46), before the
`kzalloc` at :417 and before any descriptor slot is taken, so the process
after the call is the process before it and nothing was observed: a
changed model and an event are both refused.  The `iff` pins already say
this; these two name the mistake. -/

/-- A changed model on the -EINVAL path is refused: the kernel returns before it allocates.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem einval_changed_model_rejected (i : SyscallInput) (m m' : Model) (hne : m' ≠ m) :
    ¬ timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 1) i m
        (einval_outcome m') := by
  intro h
  sys_norm at h
  exact hne h

/-- An event on the -EINVAL path is refused: nothing is observed before the return.
kernel: fs/timerfd.c:timerfd_create@v6.18.46 -/
theorem einval_event_rejected (i : SyscallInput) (m : Model) (ev : event) (evs : List event) :
    ¬ timerfd_create_spec (Z_to_bv 64 CLOCK_MONOTONIC) (Z_to_bv 64 1) i m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m (ev :: evs)) := by
  sys_refute

/-! ## Through the table: the clock id is a0, the flag word a1, and both narrow

`SYSCALL_DEFINE2(timerfd_create, int, clockid, int, flags)`
(fs/timerfd.c:394, Linux v6.18.46, commit 1f99e9ab748f): the clock id is
a0 and the flag word a1, and riscv64's `__SYSCALL_DEFINEx`
(arch/riscv/include/asm/syscall_wrapper.h:82) hands the full-width
registers to `__se_sys_timerfd_create` (`SC_RISCV_REGS_TO_ARGS`, :95,
expanded at :21-24) and from there to `__do_sys_timerfd_create` through
`__SC_CAST`
(include/linux/syscalls.h:132, Linux v6.18.46, `(__force t) a`, applied
at syscall_wrapper.h:88), so each is narrowed to its declared `int`
before the `if` at fs/timerfd.c:404 (Linux v6.18.46) runs.  The table
line applies `clockid32` to `in_arg i 0` and `flag32` to `in_arg i 1` for
exactly that reason; these pins are what would catch the line reading the
arguments the wrong way round or the whole register.  The Rocq worked case
is `timerfd_create_narrows_both_arguments`. -/

/-- The clock id comes FIRST and the flag word second; `tfd_in` is the
twin of the Rocq builder and makes that visible at every use site. -/
def tfd_in (clkid flags : Int) : SyscallInput :=
  SyscallInput.mkInput 85 [Z_to_bv 64 clkid, Z_to_bv 64 flags, 0, 0, 0, 0]
    (fun _ => none) (fun _ => none)

/-- Syscall 85 is `timerfd_create` (fs/timerfd.c:394, Linux v6.18.46):
`__NR_timerfd_create 85` (include/uapi/asm-generic/unistd.h:233, Linux
v6.18.46).  That header is
the number's DEFINITION but not riscv64's source of it: riscv64 builds
`asm/unistd_64.h` from scripts/syscall.tbl (line 109, `85 common
timerfd_create sys_timerfd_create`) through scripts/Makefile.asm-headers,
and arch/riscv/include/uapi/asm/unistd.h:19-20 includes the built header.
The two agree at v6.18.46, and the table is what would move first.
kernel: include/uapi/asm-generic/unistd.h:__NR_timerfd_create@v6.18.46 -/
example : (85 : Int) ∈ modeled_sysnos := by decide

/-- …and it reaches the gate with a0 as the clock id and a1 as the flag
word: bit 0 in a1 beside `CLOCK_MONOTONIC` is the -EINVAL of
`flag_bit0_is_einval`, through the dispatcher.
kernel: fs/timerfd.c:timerfd_create; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem sysno_85_is_timerfd_create (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (tfd_in CLOCK_MONOTONIC 1) m o ↔ o = einval_outcome m := by
  sys_norm

/-- The swapped-argument lie: `timerfd_create(CLOCK_MONOTONIC, TFD_CLOEXEC)`
is a legal call Linux answers with a descriptor, so it declines; an arm
judging a0 against the mask and a1 against the clock set would find
`TFD_CLOEXEC` off the clock set and answer -EINVAL.
kernel: fs/timerfd.c:timerfd_create; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem swapped_arguments_declines (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (tfd_in CLOCK_MONOTONIC O_CLOEXEC) m o ↔ o = Unmodeled := by
  sys_norm

/-- -EINVAL for `(CLOCK_MONOTONIC, TFD_CLOEXEC)` is refused: that is the swapped arm's answer.
kernel: fs/timerfd.c:timerfd_create; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem swapped_arguments_einval_rejected (m m' : Model) (evs : List event) :
    ¬ syscall_spec (tfd_in CLOCK_MONOTONIC O_CLOEXEC) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-! ### Both arguments narrow to 32 bits

A high half on either register is discarded by the `int` cast at the
wrapper before the gate sees the word, so `timerfd_create(2^32 + 1, 0)` IS
`timerfd_create(1, 0)` and Linux hands back a descriptor for it
(testing/syscall-check/tests/timerfd_create.c's `hiclock` and `hiflags`
cases).  A spec comparing the whole 64-bit register would have answered
-EINVAL to both; the refutations are what discriminate. -/

/-- A high half on the clock id aliases onto the admitted id: declined.
kernel: fs/timerfd.c:timerfd_create; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem high_clock_half_aliases_and_declines (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (tfd_in (2 ^ 32 + CLOCK_MONOTONIC) 0) m o ↔ o = Unmodeled := by
  sys_norm

/-- -EINVAL for a high half on the clock id is refused: no kernel sees the high half.
kernel: fs/timerfd.c:timerfd_create; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem high_clock_half_einval_rejected (m m' : Model) (evs : List event) :
    ¬ syscall_spec (tfd_in (2 ^ 32 + CLOCK_MONOTONIC) 0) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A high half on the flag word aliases onto the empty word: declined.
kernel: fs/timerfd.c:timerfd_create; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem high_flag_half_aliases_and_declines (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (tfd_in CLOCK_MONOTONIC (2 ^ 32)) m o ↔ o = Unmodeled := by
  sys_norm

/-- -EINVAL for a high half on the flag word is refused: no kernel sees the high half.
kernel: fs/timerfd.c:timerfd_create; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem high_flag_half_einval_rejected (m m' : Model) (evs : List event) :
    ¬ syscall_spec (tfd_in CLOCK_MONOTONIC (2 ^ 32)) m
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The high half does not rescue a bad low half: aliasing is not a
second chance.  `CLOCK_TAI` under bit 32 is -EINVAL.
kernel: fs/timerfd.c:timerfd_create; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem high_half_on_bad_clock_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (tfd_in (2 ^ 32 + 11) 0) m o ↔ o = einval_outcome m := by
  sys_norm

/-- The sign bit THROUGH the table, as a C caller really passes `INT_MIN`
in `flags`: sign-extended to `0xFFFFFFFF80000000`, narrowed to
`0x80000000`, refused by the truthiness test (fs/timerfd.c:404, Linux
v6.18.46); a narrowing that kept 31 bits would have passed it.
kernel: fs/timerfd.c:timerfd_create; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem sign_extended_int_min_flags_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (tfd_in CLOCK_MONOTONIC (-2147483648)) m o ↔ o = einval_outcome m := by
  sys_norm

/-- The sign bit on the CLOCK ID, as a C caller passes `INT_MIN`:
sign-extended to `0xFFFFFFFF80000000`, narrowed to `0x80000000`, which is
no admitted id, so -EINVAL (fs/timerfd.c:405-410).  The flag half has the
same pin above; this is the id half, and what it discriminates is a
comparison that reads the id modulo `2^31` — under which `0x80000000`
becomes `CLOCK_REALTIME` and the call would be admitted.
kernel: fs/timerfd.c:timerfd_create; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem sign_extended_int_min_clock_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (tfd_in (-2147483648) 0) m o ↔ o = einval_outcome m := by
  sys_norm

/-- `clockid = -6`, which is `make_process_cpuclock(0, CPUCLOCK_SCHED)` —
`((~pid) << 3) | clock` in `make_process_cpuclock`
(include/linux/posix-timers.h:19-23, Linux v6.18.46), with `CPUCLOCK_SCHED`
(include/linux/posix-timers_types.h:29, Linux v6.18.46) being 2; older
kernels spelt it `MAKE_PROCESS_CPUCLOCK` — and an id `clock_gettime` really
answers: `timerfd_create` refuses it like any other id off the
whitelist, so the negative half of the id space is not a
uniformly-failing region there and is one here.  The probe asserts this
against the pinned kernel in the same case as `-1`.
probe: testing/syscall-check/tests/timerfd_create.c#conform -- einval -/
theorem sign_extended_minus_six_clock_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (tfd_in (-6) 0) m o ↔ o = einval_outcome m := by
  sys_norm

/-- …and `clockid = -1` as a C caller passes it, the full register set:
its low half is no admitted id, so -EINVAL (fs/timerfd.c:405-410), which
testing/syscall-check/tests/timerfd_create.c's `einval` case observes as
`timerfd_create(-1)`.
kernel: fs/timerfd.c:timerfd_create; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem sign_extended_minus_one_clock_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (tfd_in (-1) 0) m o ↔ o = einval_outcome m := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Timerfd
