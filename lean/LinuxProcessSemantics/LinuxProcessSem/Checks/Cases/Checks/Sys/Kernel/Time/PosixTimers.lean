-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Kernel/Time/PosixTimers.v
-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Kernel/Time/PosixTimers.v
-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Witness/Kernel/Time/PosixTimers.v

import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.PosixTimers
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.PosixTimers
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress


/-! # Checks.Cases.Checks.Sys.Kernel.Time.PosixTimers — what the clock_gettime checker answers, read off against Linux

Pins over `Checks.Sys.Kernel.Time.PosixTimers.check_clock_gettime`, the
twin of `theories/LinuxProcessSem/Checks/Sys/Kernel/Time/PosixTimers.v`'s
checker, and over `clock_gettime_witness`, the twin of
`theories/LinuxProcessSem/Checks/Witness/Kernel/Time/PosixTimers.v`'s
witness.  Not part of the trusted specification: this file is QA on the
executable definitions, written to be READ, and every claim in it is a
claim about what the kernel does, with the citation beside it.  Every
kernel line below was read at Linux v6.18.46 (commit 1f99e9ab748f).

WHAT THIS FILE IS.  Rocq states its worked cases for this syscall on the
CHECKER: the `Example`s of `theories/LinuxProcessSem/Checks/Cases/Kernel/Time/PosixTimers.v`
are `check_syscall … = CheckOk …`, `= CheckReject` and `= CheckUnmodeled`,
and its three `Lemma`s quantify over the checker's arguments.  The Lean
port of that file, `Checks/Cases/Kernel/Time/PosixTimers.lean`, restated
each of them on the RELATION `clock_gettime_spec`, because the Lean tree
had no executable checker when it was written; those restatements carry
the `rocq-twin:` marks and stay where they are.  This file states the
same cases on the checker, under the Rocq names, in the namespace of the
checker's own Cases mirror.  There is no `theories/…/Checks/Cases/Checks/Sys/…`
file for it to twin, so nothing here is marked `rocq-twin:`; each pin
cites the kernel line the Rocq docstring argues from instead, and the
argument is repeated in its own words so the citation can be checked
against it.  The universals close by the checker's own case analysis.

HOW THE CONCRETE CASES CLOSE.  The checker is a closed computation on
these fixtures and `Model` has no `DecidableEq`, so a concrete case is
`rfl`: the elaborator evaluates the call and compares.  On the wall-clock
and CPU-time arms that is the whole proof.  On the monotonic arm, and on
the witness, the elaborator's `rfl` exhausts `maxRecDepth` instead, for
a reason that is Lean's and not the checker's.  `isExprDefEqAuxImpl`
(module `Lean.Meta.ExprDefEq`, through `whnfCoreAtDefEq`, Lean v4.34.0)
first reduces each side with `whnfCore` under the projection setting
`.yesWithDeltaI`; iota reduction evaluates its scrutinee with `whnf`
under that inherited setting (module `Lean.Meta.WHNF`, `reduceRec`); and
under it `BitVec.toNat` of a bit-vector built by an ordinary definition
— `Z_to_bv`, a numeral, `m_clock (with_clock …)` — is a stuck projection
(`whnfCore`'s `.proj` case unfolds the structure with `whnfAtMostI`), so
no `Nat` literal folds.  A `Bool` gate compares such operands with
`Nat.beq`, whose match needs the stuck operand as a constructor and
stops at once; lazy delta then evaluates the arm under the default
setting.  The realtime and cputime arms meet only such gates — the id
test is an `Int` equality, decided through `Nat.beq`, and their byte
predicates are `Bool` — which is why they close by `rfl`.
The monotonic arm's FIRST gate is `bv_unsigned (m_clock m) <
CLOCK_NS_ENVELOPE`, and `Int.lt`'s `x + 1 ≤ 2 ^ 63` is decided through
`Int.subNatNat (2 ^ 63) (Nat.succ X)`, whose `Nat.sub` recurses on its
SECOND argument, the literal, 2^63 times before it could notice that the
first is stuck.  So those cases evaluate the call first, with
`conv => lhs; whnf` — `Meta.whnf` under the default setting, the same
evaluator `rfl` runs, started one step earlier — and `rfl` then compares
constructor arguments, which lazy delta handles.  The claim is pinned at
the end of this file: under `set_option backward.isDefEq.lazyWhnfCore
false`, the option that selects the setting, a monotonic case that needs
`conv` here closes by plain `rfl`.  When that option's default changes,
or `whnfCoreAtDefEq` stops handing its setting to iota, the `conv` lines
can go.

HOW THE CALL IS STATED.  Rocq's cases go through `check_syscall`, the
dispatcher.  The sections below were written before `checked_table` had
a row for 113, and state the cases on the call the `clock_gettime` arm
makes — `check_clock_gettime` on the id register's low 32 bits and on
the destination register — through `clock_check` below, which is what
`ca_check arm_clock_gettime (clock_input clkid) eff m` unfolds to.  The
last section, `V_Kernel_Time_PosixTimers`, restates Rocq's cases through
`check_syscall` over the real table.  A rewrite of each statement above
to `check_syscall (clock_input clkid) eff m`, not the table's arrival, is
the condition under which `clock_check` leaves this file.

WHAT NO PROBE CAN REACH.  No probe under `testing/syscall-check/` runs a
Lean definition: the harness runs the extracted Rocq model, until the V
ticket's replay of the probes' `CASE` lines through the Lean acceptor
lands.  Where a
probe case shows the same decision of the Rocq checker it is named in
prose; the kernel line stays the evidence.  Independently of that,
`m_clock` is internal state no observation reveals, and no kernel can be
asked to run `CLOCK_MONOTONIC` backwards, to stand still on demand, or
to report a reading at either end of an `s64` — which is why the Rocq
tree pins these on the checker in the first place.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Time.PosixTimers

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.PosixTimers
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.PosixTimers
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.PosixTimers

/-! ## The call, as the arm makes it

The fixtures are the Rocq cases' own, from `Checks/Cases/Kernel/Time/PosixTimers.lean`:
`clock_gettime(clkid, 4096)` with exactly sixteen bytes writable at 4096
(`clock_input`), the same call with nothing writable
(`clock_input_unwritable`), a model whose recorded clock reads `t`
(`clock_model t`), and the byte strings `ts_*`. -/

/-- The check the dispatcher arm performs for `clock_gettime(clkid, 4096)`:
`check_clock_gettime` on the id register's low 32 bits and on the
destination register, as Rocq's `arm_clock_gettime`
(`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`) applies it.  The header
says when this alias goes. -/
def clock_check (clkid : word) (eff : SyscallEffect) (m : Model) : check_result :=
  check_clock_gettime (clock_input clkid) (clockid32 (in_arg (clock_input clkid) 0))
    (in_arg (clock_input clkid) 1) eff m

/-- The witness the same arm offers for that call. -/
def clock_witness (clkid : word) (m : Model) : outcome SyscallEffect :=
  clock_gettime_witness (clockid32 (in_arg (clock_input clkid) 0))
    (in_arg (clock_input clkid) 1) (clock_input clkid) m

/-- The alias reads the two registers the arm reads: for the small ids
these cases pass the id is the register itself, and the destination is
4096.
model: `clock_input`'s registers read back through `clockid32` and `in_arg` -/
example : clockid32 (in_arg (clock_input 1) 0) = 1 ∧ in_arg (clock_input 1) 1 = 4096 := by
  decide

/-! ## The id gate, for every id -/

/-- Every id but the three modeled ones declines, whatever the destination,
the effect or the model.  `SYSCALL_DEFINE2(clock_gettime)` looks the id up
in `clockid_to_kclock` before it does anything else, and the checker
tests it first for the same reason, so no hypothesis about `tp`, `eff` or
`m` is needed.  The kernel answers several of these ids — the probe's
`thrcputime` and `cpuclock` cases succeed on Linux — so the decline is
the model's, not an `-EINVAL`; this pin is what a future arm for
`CLOCK_BOOTTIME` or `CLOCK_THREAD_CPUTIME_ID` has to move.  The three ids
are the numerals 0, 2 and 1 because neither cited function spells their
names: `clockid_to_kclock` indexes `posix_clocks[]`, and only that
array's initializer, elsewhere in the file, does.
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock@v6.18.46 -/
theorem clock_gettime_only_the_modeled_clocks (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m : Model)
    (hrt : bv_unsigned clkid ≠ 0) (hraw : bv_unsigned clkid ≠ 4)
    (hrtc : bv_unsigned clkid ≠ 5) (hmc : bv_unsigned clkid ≠ 6)
    (hbt : bv_unsigned clkid ≠ 7) (hcp : bv_unsigned clkid ≠ 2)
    (hmono : bv_unsigned clkid ≠ 1) :
    check_clock_gettime i clkid tp eff m = CheckUnmodeled := by
  unfold check_clock_gettime
  have hpc : clockid_percall_b clkid = false := by
    simp only [clockid_percall_b, CLOCK_REALTIME, CLOCK_MONOTONIC_RAW, CLOCK_REALTIME_COARSE,
      CLOCK_MONOTONIC_COARSE, CLOCK_BOOTTIME, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨⟨⟨hrt, hraw⟩, hrtc⟩, hmc⟩, hbt⟩
  simp only [hpc, Bool.false_eq_true, ↓reduceIte, CLOCK_PROCESS_CPUTIME_ID, CLOCK_MONOTONIC,
    hcp, hmono, ne_eq, not_false_eq_true, ↓reduceIte]

/-! ## The id register's low 32 bits

`SYSCALL_DEFINE2(clock_gettime, const clockid_t, which_clock, …)` takes
the id as a `clockid_t`, an `int`, so the arm narrows the 64-bit register
to its low 32 bits with `clockid32` before the checker sees it, and the
alias above does the same.  Every other case in this file passes an id
that is its own low word, so none of them would notice an alias that
stopped narrowing, sign-extended, or read the wrong register; these
three pass ids that are not.  Bit 31 of the low word is the `int`'s
sign, which `clockid_to_kclock` tests first (`id < 0` selects the CPU
and dynamic clocks), and no arm models a negative id. -/

/-- 2^32 + 1 narrows to 1, the monotonic arm: the reading is admitted and
recorded exactly as `clock_advancing_reading_records_it` records it.
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock@v6.18.46 -/
theorem wide_id_low_word_selects_monotonic :
    clock_check 4294967297 (mkEffect 0 [(4096, ts_2s)] []) (clock_model 1000000000)
      = CheckOk (clock_model 2000000000) [] := by
  conv => lhs; whnf
  rfl

/-- 2^32 narrows to 0, the wall-clock arm — told apart from the monotonic
one by a recorded clock at the envelope, which only that arm declines.
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock@v6.18.46 -/
theorem wide_id_low_word_selects_realtime :
    clock_check 4294967296 (mkEffect 0 [(4096, ts_1s)] []) (clock_model (2 ^ 63))
      = CheckOk (clock_model (2 ^ 63)) [] := rfl

/-- A low word of 0xFFFFFFFF is the `int` -1, which `clockid_to_kclock`
sends to the CPU-clock table; no arm models it, so the checker declines.
The upper word (1 here) is discarded by `clockid32`;
`clock_gettime_only_the_modeled_clocks` covers every other value it could
take.
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock@v6.18.46 -/
theorem wide_id_negative_low_word_declines :
    clock_check 8589934591 (mkEffect 0 [(4096, ts_1s)] []) (clock_model 0) = CheckUnmodeled := by
  conv => lhs; whnf

/-! ## CLOCK_MONOTONIC, the arm that records -/

/-- MODEL-INTERNAL STATE.  A recorded clock already at 2^63 ns declines
rather than inventing a reading.  Unreachable from the initial model — the
origin is 0 and every arm stays under the envelope — but receptiveness
quantifies over every model, so the arm has to be there and be right.
The bound is `ktime_t`'s: `proc_timens_set_offset`, the one writer that
moves a process's `CLOCK_MONOTONIC` — and only before the namespace's
first task runs, after which its offsets are frozen — reads the clock
with `ktime_get_ts64`, refuses (`-ERANGE`) an offset whose seconds exceed
`KTIME_SEC_MAX`, and halves the bound on the sum AT SET TIME so that
`KTIME_MAX` stays unreachable for the uptime the reading then grows by.
It bounds the offset, not the delivered reading; the kernel's own comment
there is what makes 2^63 a count no reading reaches.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46 -/
theorem clock_at_envelope_declines :
    clock_check 1 (mkEffect 0 [(4096, ts_1s)] []) (clock_model (2 ^ 63)) = CheckUnmodeled := by
  conv => lhs; whnf

/-- MODEL-INTERNAL STATE — the other side of `clock_at_envelope_declines`.
A recorded clock of 2^63 - 1 ns, the largest `ktime_t`, still answers:
the envelope gate is `<` and not `≤`, so the last representable instant
is inside it and only 2^63 itself is out.  The equal reading is admitted
and re-recorded, as in `clock_equal_reading_is_admissible`.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46 -/
theorem clock_recorded_at_envelope_minus_one_answers :
    clock_check 1 (mkEffect 0 [(4096, ts_max)] []) (clock_model (2 ^ 63 - 1))
      = CheckOk (clock_model (2 ^ 63 - 1)) [] := by
  conv => lhs; whnf
  rfl

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  Two readings that return
the SAME nanosecond are admissible: `ktime_get_ts64` reads a clock that
never runs backwards but is not required to advance, and a coarse
clocksource really does answer two quick calls alike.  No probe can force
the coincidence (the probe's `two` case with both writes poisoned to zero
shows it on the Rocq checker), so it is pinned here.  The accepted step
leaves `m_clock` where it was.
kernel: kernel/time/timekeeping.c:ktime_get_ts64@v6.18.46 -/
theorem clock_equal_reading_is_admissible :
    clock_check 1 (mkEffect 0 [(4096, ts_1s)] []) (clock_model 1000000000)
      = CheckOk (clock_model 1000000000) [] := by
  conv => lhs; whnf
  rfl

/-- MODEL-INTERNAL STATE.  An advancing reading is admissible too, and the
point of the case is the SECOND half: the accepted step carries the new
time into `m_clock`, where the next `ktime_get_ts64` reading is measured
against it.  The kernel half is the first: an advancing reading is what
`ktime_get_ts64` ordinarily returns.  Nothing about `m_clock` reaches a trace, so no probe can
check this directly; the conformance suite sees it only through a later
call being judged against the recorded value.
kernel: kernel/time/timekeeping.c:ktime_get_ts64@v6.18.46 -/
theorem clock_advancing_reading_records_it :
    clock_check 1 (mkEffect 0 [(4096, ts_2s)] []) (clock_model 1000000000)
      = CheckOk (clock_model 2000000000) [] := by
  conv => lhs; whnf
  rfl

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the `CheckReject` half.
A reading one nanosecond EARLIER than the last is refused.
`ktime_get_ts64` returns `xtime_sec` plus `wall_to_monotonic` and
enforces nothing itself; the monotonicity is decided where the wall clock
is stepped — `do_settimeofday64`, `__timekeeping_inject_offset`,
`__timekeeping_inject_sleeptime` and the leap-second step in
`accumulate_nsecs_to_secs` each subtract from `wall_to_monotonic` what
they add to `xtime`, so the sum never moves — and by `clock_monotonic`
having no `clock_set`,
so that `clock_settime` answers `-EINVAL` for this id.  No real kernel
can be asked to violate it, and the conformance suite reaches the
refusal only through `--mutate`.
kernel: kernel/time/timekeeping.c:ktime_get_ts64,do_settimeofday64,__timekeeping_inject_offset,__timekeeping_inject_sleeptime,accumulate_nsecs_to_secs; kernel/time/posix-timers.c:clock_settime@v6.18.46 -/
theorem clock_backwards_reading_rejected :
    clock_check 1 (mkEffect 0 [(4096, ts_1s_minus)] []) (clock_model 1000000000)
      = CheckReject := by
  conv => lhs; whnf

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the exact boundary.  A
`tv_nsec` of exactly 10^9 is refused even though the total it encodes
moves forward: `ktime_get_ts64` sets the field to 0 and normalizes with
`timespec64_add_ns`, which carries whole seconds out of it, so a full
second never appears there and admitting it would make two byte strings
mean the same instant.
kernel: include/linux/time64.h:timespec64_add_ns; kernel/time/timekeeping.c:ktime_get_ts64@v6.18.46 -/
theorem clock_denormalized_nsec_rejected :
    clock_check 1 (mkEffect 0 [(4096, ts_denorm)] []) (clock_model 0) = CheckReject := by
  conv => lhs; whnf

/-- The largest reading `ktime_t` can hold, 2^63 - 1 ns, is admissible and
is recorded; the pair with the case below makes the envelope's bound
non-vacuous.  The bound is the one `proc_timens_set_offset` keeps the
offset under at set time, with the headroom it leaves for uptime.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46 -/
theorem clock_reading_at_envelope_minus_one_admissible :
    clock_check 1 (mkEffect 0 [(4096, ts_max)] []) (clock_model 0)
      = CheckOk (clock_model (2 ^ 63 - 1)) [] := by
  conv => lhs; whnf
  rfl

/-- One nanosecond further is refused: `ktime_t` is a signed 64-bit count,
and `proc_timens_set_offset`'s halved bound at set time is there to keep
`KTIME_MAX` unreachable, so 2^63 ns is not a time a kernel can report.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46 -/
theorem clock_reading_at_envelope_rejected :
    clock_check 1 (mkEffect 0 [(4096, ts_over)] []) (clock_model 0) = CheckReject := by
  conv => lhs; whnf

/-- THE ONE CASE THAT PINS THE INTEGER ARITHMETIC.  `timespec_ns` sums
`tv_sec * 10^9 + tv_nsec` in `Int` on purpose.  Summed in `word` this
reading is 1000 ns — above the recorded 0 and far under the envelope — so
a wrapping spelling would answer `CheckOk` and let an absurd `tv_sec`
present itself as a small, admissible time.  The reading it really
encodes, 2^64 + 1000 ns, is past `KTIME_MAX`, the bound the cited
writer keeps the offset under so that no reading reaches it.  Every other case in this file
passes under both spellings; this is the only one that separates them.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46 -/
theorem clock_reading_wrapping_sum_rejected :
    clock_check 1 (mkEffect 0 [(4096, ts_wrap)] []) (clock_model 0) = CheckReject := by
  conv => lhs; whnf

/-! ## The per-call ids, whose whole content is what they do NOT promise

The probe covers the shape of an accepted wall-clock reading against a
real kernel.  What no probe can reach is the ABSENCE of the cross-call
constraint: a kernel will not run its wall clock backwards between two
calls on request, and `m_clock` not moving is invisible from outside.
Each case below is paired with the `CLOCK_MONOTONIC` case above that it
contradicts. -/

/-- An accepted call on ANY per-call id leaves the model EXACTLY as it
found
it, for every input, destination, effect and starting model — the
load-bearing universal, since a field written here and read by nothing
would look like a guarantee the kernel does not give.
`do_settimeofday64` refuses what `timespec64_valid_settod` refuses and a
time before the boot instant (its second `-EINVAL` compares the new value
against the wall-to-monotonic offset), nothing else that sets the clock
EARLIER; `__timekeeping_inject_offset` applies a signed `timespec64` from
userspace under the same floor; so no reading constrains the next, and
the checker records none.  The raw and coarse ids and `CLOCK_BOOTTIME`
are on the same arm and record nothing for the reasons
`Sys.Kernel.Time.PosixTimers.clockid_percall_b` gives.
kernel: kernel/time/timekeeping.c:do_settimeofday64,__timekeeping_inject_offset@v6.18.46 -/
theorem clock_gettime_percall_leaves_the_model_alone (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (hid : clockid_percall_b clkid = true)
    (h : check_clock_gettime i clkid tp eff m = CheckOk m' evs) : m' = m ∧ evs = [] := by
  unfold check_clock_gettime at h
  simp only [hid, ↓reduceIte] at h
  rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
  · simp only [hdst, reduceCtorEq] at h
  · simp only [hdst] at h
    split at h
    next =>
      split at h
      next =>
        cases h
        exact ⟨rfl, rfl⟩
      next => cases h
    next => cases h

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and the exact
counterpart of `clock_backwards_reading_rejected`: the SAME bytes, the
SAME recorded clock, the other id.  A wall-clock reading one nanosecond
EARLIER than the last monotonic one is admissible, because the wall clock
carries no monotonicity at all — `do_settimeofday64` accepts any valid
earlier time down to the boot-instant floor, and
`__timekeeping_inject_offset` any signed step that stays above it — and
the accepted step leaves the recorded clock where it was rather than
dragging it backwards.
kernel: kernel/time/timekeeping.c:do_settimeofday64,__timekeeping_inject_offset@v6.18.46 -/
theorem realtime_backwards_reading_is_admissible :
    clock_check 0 (mkEffect 0 [(4096, ts_1s_minus)] []) (clock_model 1000000000)
      = CheckOk (clock_model 1000000000) [] := rfl

/-- MODEL-INTERNAL STATE, the counterpart of `clock_at_envelope_declines`.
A recorded clock past what `ktime_t` holds declines a MONOTONIC read,
whose choice is relative to it and would be empty.  It does not decline a
WALL-CLOCK read: `clockid_to_kclock` sends `CLOCK_REALTIME` to
`posix_get_realtime_timespec`, which is `ktime_get_real_ts64` and consults
nothing of the process, so there is nothing for the envelope to be empty
against.
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock,posix_get_realtime_timespec@v6.18.46 -/
theorem realtime_ignores_the_recorded_clock :
    clock_check 0 (mkEffect 0 [(4096, ts_1s)] []) (clock_model (2 ^ 63))
      = CheckOk (clock_model (2 ^ 63)) [] := rfl

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  What the wall clock DOES
have to satisfy, it satisfies on the same terms as the monotonic one: a
`tv_nsec` of exactly 10^9 is refused, because `ktime_get_real_ts64` sets
the field to 0 and normalizes with `timespec64_add_ns`, so a full second
never appears there.
kernel: kernel/time/timekeeping.c:ktime_get_real_ts64; include/linux/time64.h:timespec64_add_ns@v6.18.46 -/
theorem realtime_denormalized_nsec_rejected :
    clock_check 0 (mkEffect 0 [(4096, ts_denorm)] []) (clock_model 0) = CheckReject := rfl

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  A reading of 2^63 ns is
refused for the wall clock too.  The bound is `timespec64_valid_settod`,
which every setter userspace reaches passes — `do_settimeofday64` on the
new time, `__timekeeping_inject_offset` on the sum — and which stops
`TIME_UPTIME_SEC_MAX` — thirty years — SHORT of `KTIME_SEC_MAX`.  The
writers that do NOT pass it — `__timekeeping_inject_sleeptime` (which
validates only the delta), the tick's accumulation and its leap-second
step in `accumulate_nsecs_to_secs` — are the uptime that headroom is
there to absorb; so the bound rests on the
kernel's design of that headroom, not on a check every writer passes,
and a wall clock past `KTIME_SEC_MAX` would be the kernel's own overflow
rather than a reading.
kernel: include/linux/time64.h:timespec64_valid_settod; kernel/time/timekeeping.c:do_settimeofday64,__timekeeping_inject_offset,__timekeeping_inject_sleeptime,accumulate_nsecs_to_secs@v6.18.46 -/
theorem realtime_reading_at_envelope_rejected :
    clock_check 0 (mkEffect 0 [(4096, ts_over)] []) (clock_model 0) = CheckReject := rfl

/-- The largest wall-clock reading `ktime_t` can hold is admissible and is
NOT recorded: the pair with the case above makes the boundary
non-vacuous, and the pair with `clock_reading_at_envelope_minus_one_admissible`,
which records the same bytes, makes the difference between the arms
non-vacuous.  Same bound, same check.
kernel: include/linux/time64.h:timespec64_valid_settod; kernel/time/timekeeping.c:do_settimeofday64@v6.18.46 -/
theorem realtime_reading_at_envelope_minus_one_admissible :
    clock_check 0 (mkEffect 0 [(4096, ts_max)] []) (clock_model 0)
      = CheckOk (clock_model 0) [] := rfl

/-- The bytes `cputime_negative_tv_sec_admissible` below admits are refused
here: `realtime_ok_b` reads `tv_sec` unsigned because the wall clock has
no such shape — `timespec64_valid`, which `timespec64_valid_settod`
applies first, refuses `tv_sec < 0` as a date before 1970.
kernel: include/linux/time64.h:timespec64_valid,timespec64_valid_settod@v6.18.46 -/
theorem realtime_negative_tv_sec_rejected :
    clock_check 0 (mkEffect 0 [(4096, ts_cpu_neg1)] []) (clock_model 0) = CheckReject := rfl

/-- `CLOCK_MONOTONIC_RAW` (4) is on the per-call arm, so the checker holds
its reading to `realtime_ok_b` alone: a denormalized `tv_nsec` is refused
there as it is for the wall clock.
kernel: kernel/time/timekeeping.c:ktime_get_raw_ts64@v6.18.46
(the spec-level twin of Rocq's `monotonic_raw_denormalized_nsec_rejected`, stated here on
the checker; this file's cases have no Rocq mirror path, as its header says) -/
theorem monotonic_raw_denormalized_nsec_rejected :
    clock_check 4 (mkEffect 0 [(4096, ts_denorm)] []) (clock_model 0) = CheckReject := rfl

/-- `CLOCK_REALTIME_COARSE` (5), same arm, same envelope on the reading.
kernel: kernel/time/timekeeping.c:ktime_get_coarse_real_ts64@v6.18.46
(the checker's side of Rocq's `realtime_coarse_reading_at_envelope_rejected`) -/
theorem realtime_coarse_reading_at_envelope_rejected :
    clock_check 5 (mkEffect 0 [(4096, ts_over)] []) (clock_model 0) = CheckReject := rfl

/-- `CLOCK_MONOTONIC_COARSE` (6) states no cross-call relation, so the
checker answers over a recorded clock the monotonic arm declines, and
records nothing.
kernel: kernel/time/timekeeping.c:ktime_get_coarse_ts64@v6.18.46
(the checker's side of Rocq's `monotonic_coarse_ignores_the_recorded_clock`) -/
theorem monotonic_coarse_ignores_the_recorded_clock :
    clock_check 6 (mkEffect 0 [(4096, ts_1s)] []) (clock_model (2 ^ 63))
      = CheckOk (clock_model (2 ^ 63)) [] := rfl

/-- `CLOCK_BOOTTIME` (7), same arm: a reading BEFORE the recorded
monotonic one is admissible, and the recorded clock does not move.
kernel: include/linux/timekeeping.h:ktime_get_boottime_ts64; kernel/time/timekeeping.c:__timekeeping_inject_sleeptime@v6.18.46
(the checker's side of Rocq's `boottime_backwards_reading_is_admissible`) -/
theorem boottime_backwards_reading_is_admissible :
    clock_check 7 (mkEffect 0 [(4096, ts_1s_minus)] []) (clock_model 1000000000)
      = CheckOk (clock_model 1000000000) [] := rfl

/-! ## CLOCK_PROCESS_CPUTIME_ID, which is not a clock

It reports the thread group's consumed CPU time — `thread_group_cputime`
sums it, `cpu_clock_sample_group` hands it out as a `u64` count of
nanoseconds — so `cputime_ok_b` keeps the wall clock's per-reading
conditions and moves the 2^63 ns envelope onto the SIGNED reading
`ns_to_timespec64` writes, two-sided.  That is the whole difference
between the arms, and it is the half no probe can reach: no kernel can
be asked for a reading near either end of an `s64`. -/

/-- An accepted `CLOCK_PROCESS_CPUTIME_ID` call leaves the model EXACTLY as
it found it, for every input, destination, effect and starting model.
CPU time is `thread_group_cputime`'s sum over the group's threads,
sampled by `cpu_clock_sample_group`: a group spread over several CPUs
burns it faster than any clock advances and a descheduled one burns none,
so a field recorded here could only be written and never read.  The id is
the numeral 2 because neither function spells `CLOCK_PROCESS_CPUTIME_ID`.
kernel: kernel/sched/cputime.c:thread_group_cputime; kernel/time/posix-cpu-timers.c:cpu_clock_sample_group@v6.18.46 -/
theorem clock_gettime_cputime_leaves_the_model_alone (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (hid : bv_unsigned clkid = 2)
    (h : check_clock_gettime i clkid tp eff m = CheckOk m' evs) : m' = m ∧ evs = [] := by
  unfold check_clock_gettime at h
  have hpc : clockid_percall_b clkid = false := by
    simp only [clockid_percall_b, hid, CLOCK_REALTIME, CLOCK_MONOTONIC_RAW,
      CLOCK_REALTIME_COARSE, CLOCK_MONOTONIC_COARSE, CLOCK_BOOTTIME]
    decide
  simp only [hpc, Bool.false_eq_true, ↓reduceIte] at h
  rw [hid] at h
  simp only [CLOCK_PROCESS_CPUTIME_ID, ↓reduceIte] at h
  rcases hdst : read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with _ | w
  · simp only [hdst, reduceCtorEq] at h
  · simp only [hdst] at h
    split at h
    next =>
      split at h
      next =>
        cases h
        exact ⟨rfl, rfl⟩
      next => cases h
    next => cases h

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and the counterpart of
`realtime_backwards_reading_is_admissible` and
`clock_backwards_reading_rejected`: the SAME bytes, the SAME recorded
clock, a third id.  A CPU-time reading is `thread_group_cputime`'s sum,
related to no earlier reading and to no clock, so it is admissible below
the recorded one, and the accepted step leaves that clock alone.
kernel: kernel/sched/cputime.c:thread_group_cputime; kernel/time/posix-cpu-timers.c:cpu_clock_sample_group@v6.18.46 -/
theorem cputime_backwards_reading_is_admissible :
    clock_check 2 (mkEffect 0 [(4096, ts_1s_minus)] []) (clock_model 1000000000)
      = CheckOk (clock_model 1000000000) [] := rfl

/-- MODEL-INTERNAL STATE, the counterpart of `clock_at_envelope_declines`
and `realtime_ignores_the_recorded_clock`.  A recorded clock past what
`ktime_t` holds declines a MONOTONIC read and not this one:
`clockid_to_kclock` sends the id to `process_cpu_clock_get`, which
samples the process and consults no clock of it.
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock; kernel/time/posix-cpu-timers.c:process_cpu_clock_get@v6.18.46 -/
theorem cputime_ignores_the_recorded_clock :
    clock_check 2 (mkEffect 0 [(4096, ts_1s)] []) (clock_model (2 ^ 63))
      = CheckOk (clock_model (2 ^ 63)) [] := rfl

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  The conjunct that
survives on this arm still bites: a `tv_nsec` of exactly 10^9 is refused,
because all three branches of `ns_to_timespec64` leave that field below
10^9 — the `nsec < 0` one by computing `NSEC_PER_SEC - rem - 1`.
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46 -/
theorem cputime_denormalized_nsec_rejected :
    clock_check 2 (mkEffect 0 [(4096, ts_denorm)] []) (clock_model 0) = CheckReject := rfl

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and THE PAIR THAT IS THE
WHOLE DIFFERENCE BETWEEN THIS ARM AND THE WALL CLOCK'S.  A reading with a
NEGATIVE `tv_sec` is what `ns_to_timespec64`'s `nsec < 0` branch writes
once the `u64` sum `thread_group_cputime` produces passes 2^63, so this
arm must accept it; `realtime_negative_tv_sec_rejected` refuses the
identical bytes.
kernel: kernel/time/time.c:ns_to_timespec64; kernel/sched/cputime.c:thread_group_cputime@v6.18.46 -/
theorem cputime_negative_tv_sec_admissible :
    clock_check 2 (mkEffect 0 [(4096, ts_cpu_neg1)] []) (clock_model 0)
      = CheckOk (clock_model 0) [] := rfl

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the bottom of the
envelope, which exists only on this arm.  A sample of exactly 2^63 is
admissible: it is the smallest `u64` the `nsec < 0` branch of
`ns_to_timespec64` sees, and so the one whose READING is the most
negative this id can report (larger samples read HIGHER, back up towards
-1; `ts_cpu_neg1` is the largest sample of all).
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46 -/
theorem cputime_at_signed_envelope_admissible :
    clock_check 2 (mkEffect 0 [(4096, ts_cpu_min)] []) (clock_model 0)
      = CheckOk (clock_model 0) [] := rfl

/-- One nanosecond lower is refused, which is what makes the bound above
non-vacuous: the argument of `ns_to_timespec64` is an `s64`, so nothing
below -2^63 is in its image.
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46 -/
theorem cputime_below_signed_envelope_rejected :
    clock_check 2 (mkEffect 0 [(4096, ts_cpu_below)] []) (clock_model 0) = CheckReject := rfl

/-- THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the top of the envelope,
where this arm agrees with the other two.  Moving the bound onto the
signed reading did not delete it: 2^63 - 1 ns is the largest positive
`s64` `ns_to_timespec64` is handed, and is admitted and NOT recorded.
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46 -/
theorem cputime_reading_at_envelope_minus_one_admissible :
    clock_check 2 (mkEffect 0 [(4096, ts_max)] []) (clock_model 0)
      = CheckOk (clock_model 0) [] := rfl

/-- 2^63 ns is refused here exactly as for the wall clock: no `s64` holds
it, so `ns_to_timespec64` never writes it.
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46 -/
theorem cputime_reading_at_envelope_rejected :
    clock_check 2 (mkEffect 0 [(4096, ts_over)] []) (clock_model 0) = CheckReject := rfl

/-! ## The effect's shape — lies no kernel tells

`SYSCALL_DEFINE2(clock_gettime)` reads the clock into a kernel
`timespec64`, hands it to `put_timespec64` — one `copy_to_user` of the
sixteen-byte `struct __kernel_timespec` at `tp` — and returns 0 unless
that copy fails.  So an accepted effect is exactly one write, of sixteen
bytes, at `tp`, with return 0 and no zeros, unmaps, copies or copy-ins;
the checker refuses every other shape, and these are the shapes a
`--mutate` run puts to the Rocq checker.  The Rocq Cases file has no
checker-level pin for them, so these are the Lean tree's own — and since
the three arms are three separate `match`es on the effect, each arm gets
its own set. -/

/-- A non-zero return with the right bytes in the right place is refused:
the syscall returns `error`, which is 0 once `put_timespec64` succeeded.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_nonzero_return_rejected :
    clock_check 1 (mkEffect 1 [(4096, ts_1s)] []) (clock_model 0) = CheckReject := by
  conv => lhs; whnf

/-- An `-EINVAL` with no write is refused on a modeled id: the syscall's
own `-EINVAL` is for an id `clockid_to_kclock` has no clock for, 1 is
`CLOCK_MONOTONIC`, and its getter `posix_get_monotonic_timespec` returns
0 unconditionally, so no `-EINVAL` comes from the clock either.
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock,posix_get_monotonic_timespec@v6.18.46 -/
theorem clock_einval_rejected :
    clock_check 1 (mkEffect (errno_ret EINVAL) [] []) (clock_model 0) = CheckReject := by
  conv => lhs; whnf

/-- The bytes must land at `tp` and nowhere else: `put_timespec64` copies
to the pointer it was handed.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_write_elsewhere_rejected :
    clock_check 1 (mkEffect 0 [(8192, ts_1s)] []) (clock_model 0) = CheckReject := by
  conv => lhs; whnf

/-- Fifteen bytes are refused: the struct is sixteen, and `copy_to_user`
writes all of it or the syscall fails.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_short_struct_rejected :
    clock_check 1 (mkEffect 0 [(4096, ts_1s.take 15)] []) (clock_model 0) = CheckReject := by
  conv => lhs; whnf

/-- A success with no write at all is refused: a return of 0 means
`put_timespec64` copied.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_no_write_rejected :
    clock_check 1 (mkEffect 0 [] []) (clock_model 0) = CheckReject := by
  conv => lhs; whnf

/-- Seventeen bytes are refused too: the struct is sixteen, no more.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_long_struct_rejected :
    clock_check 1 (mkEffect 0 [(4096, ts_1s ++ [0])] []) (clock_model 0) = CheckReject := by
  conv => lhs; whnf

/-- One write entry, not two: the struct is one `copy_to_user`.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_split_write_rejected :
    clock_check 1 (mkEffect 0 [(4096, ts_1s.take 8), (4104, ts_1s.drop 8)] []) (clock_model 0)
      = CheckReject := by
  conv => lhs; whnf

/-- Two writes with the FIRST one right — the struct at `tp`, then a second
struct beyond it — are refused: `put_timespec64` is the syscall's only
write, so a checker that matched the head of the write list and ignored
the tail would accept a second copy no kernel makes.  The split-write case
above cannot tell that checker apart, since its first entry is already
too short.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_second_write_rejected :
    clock_check 1 (mkEffect 0 [(4096, ts_1s), (4112, ts_1s)] []) (clock_model 0) = CheckReject := by
  conv => lhs; whnf

/-- A zero-fill ledger riding along is refused: the syscall copies out one
struct and touches nothing else.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_smuggled_zeros_rejected :
    clock_check 1 (mkEffect 0 [(4096, ts_1s)] [(4096, 16)]) (clock_model 0) = CheckReject := by
  conv => lhs; whnf

/-- A smuggled unmap ledger is refused for the same reason.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_smuggled_unmap_rejected :
    clock_check 1 (SyscallEffect.mkEffectU 0 [(4096, ts_1s)] [] [(4096, 4096)] [] []) (clock_model 0)
      = CheckReject := by
  conv => lhs; whnf

/-- …and so is a smuggled pre-effect memory copy.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_smuggled_copy_rejected :
    clock_check 1 (SyscallEffect.mkEffectU 0 [(4096, ts_1s)] [] [] [MemCopy.mkCopy 4096 4096 8] [])
      (clock_model 0) = CheckReject := by
  conv => lhs; whnf

/-- …and a copy-in ledger: `clock_gettime` reads nothing from user memory.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_smuggled_copyin_rejected :
    clock_check 1 (SyscallEffect.mkEffectU 0 [(4096, ts_1s)] [] [] [] [(4096, 16)]) (clock_model 0)
      = CheckReject := by
  conv => lhs; whnf

/-! ### The same lies on the arms that record nothing

The wall-clock and CPU-time arms are separate `match`es on the effect,
so a refusal on the monotonic arm exercises neither: each conjunct of
their guards — return 0, one write, at `tp`, the byte predicate — and
the four empty ledgers get their own refusal here.  Bool-gated arms, so
plain `rfl`. -/

/-- A non-zero return with the right bytes at `tp` is refused on the
wall-clock arm.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem realtime_nonzero_return_rejected :
    clock_check 0 (mkEffect 1 [(4096, ts_1s)] []) (clock_model 0) = CheckReject := rfl

/-- An `-EINVAL` with no write is refused on the wall-clock arm:
`posix_clocks[0]` is `clock_realtime`, whose getter
`posix_get_realtime_timespec` returns 0 unconditionally.
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock,posix_get_realtime_timespec@v6.18.46 -/
theorem realtime_einval_rejected :
    clock_check 0 (mkEffect (errno_ret EINVAL) [] []) (clock_model 0) = CheckReject := rfl

/-- The wall-clock bytes must land at `tp` and nowhere else.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem realtime_write_elsewhere_rejected :
    clock_check 0 (mkEffect 0 [(8192, ts_1s)] []) (clock_model 0) = CheckReject := rfl

/-- One write entry on the wall-clock arm too.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem realtime_split_write_rejected :
    clock_check 0 (mkEffect 0 [(4096, ts_1s.take 8), (4104, ts_1s.drop 8)] []) (clock_model 0)
      = CheckReject := rfl

/-- Two writes with the first one right are refused on the wall-clock arm,
for the reason `clock_second_write_rejected` gives.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem realtime_second_write_rejected :
    clock_check 0 (mkEffect 0 [(4096, ts_1s), (4112, ts_1s)] []) (clock_model 0) = CheckReject := rfl

/-- A success with no write is refused on the wall-clock arm.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem realtime_no_write_rejected :
    clock_check 0 (mkEffect 0 [] []) (clock_model 0) = CheckReject := rfl

/-- Fifteen bytes are refused on the wall-clock arm.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem realtime_short_struct_rejected :
    clock_check 0 (mkEffect 0 [(4096, ts_1s.take 15)] []) (clock_model 0) = CheckReject := rfl

/-- The zero, unmap, copy and copy-in ledgers must all be empty on the
wall-clock arm: the syscall copies out one struct and touches nothing
else.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem realtime_smuggled_ledgers_rejected :
    clock_check 0 (SyscallEffect.mkEffectU 0 [(4096, ts_1s)] [(4096, 16)] [] [] []) (clock_model 0)
        = CheckReject
    ∧ clock_check 0 (SyscallEffect.mkEffectU 0 [(4096, ts_1s)] [] [(4096, 4096)] [] []) (clock_model 0)
        = CheckReject
    ∧ clock_check 0 (SyscallEffect.mkEffectU 0 [(4096, ts_1s)] [] [] [MemCopy.mkCopy 4096 4096 8] [])
        (clock_model 0) = CheckReject
    ∧ clock_check 0 (SyscallEffect.mkEffectU 0 [(4096, ts_1s)] [] [] [] [(4096, 16)]) (clock_model 0)
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A non-zero return with the right bytes at `tp` is refused on the
CPU-time arm.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem cputime_nonzero_return_rejected :
    clock_check 2 (mkEffect 1 [(4096, ts_1s)] []) (clock_model 0) = CheckReject := rfl

/-- An `-EINVAL` with no write is refused on the CPU-time arm.  A kernel
built without `CONFIG_POSIX_TIMERS` really answers it — `do_clock_gettime`
in the stubs file knows only the realtime, monotonic and boottime ids —
and the relation refuses it all the same (the S ticket's
`cputime_stubs_einval_rejected` says why that kernel is outside the
arm's scope); the checker follows the relation.
kernel: kernel/time/posix-stubs.c:do_clock_gettime@v6.18.46 -/
theorem cputime_stubs_einval_rejected :
    clock_check 2 (mkEffect (errno_ret EINVAL) [] []) (clock_model 0) = CheckReject := rfl

/-- The CPU-time bytes must land at `tp` and nowhere else.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem cputime_write_elsewhere_rejected :
    clock_check 2 (mkEffect 0 [(8192, ts_1s)] []) (clock_model 0) = CheckReject := rfl

/-- One write entry on the CPU-time arm too.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem cputime_split_write_rejected :
    clock_check 2 (mkEffect 0 [(4096, ts_1s.take 8), (4104, ts_1s.drop 8)] []) (clock_model 0)
      = CheckReject := rfl

/-- Two writes with the first one right are refused on the CPU-time arm.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem cputime_second_write_rejected :
    clock_check 2 (mkEffect 0 [(4096, ts_1s), (4112, ts_1s)] []) (clock_model 0) = CheckReject := rfl

/-- A success with no write is refused on the CPU-time arm.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem cputime_no_write_rejected :
    clock_check 2 (mkEffect 0 [] []) (clock_model 0) = CheckReject := rfl

/-- Fifteen bytes are refused on the CPU-time arm.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem cputime_short_struct_rejected :
    clock_check 2 (mkEffect 0 [(4096, ts_1s.take 15)] []) (clock_model 0) = CheckReject := rfl

/-- The four other ledgers must be empty on the CPU-time arm too.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem cputime_smuggled_ledgers_rejected :
    clock_check 2 (SyscallEffect.mkEffectU 0 [(4096, ts_1s)] [(4096, 16)] [] [] []) (clock_model 0)
        = CheckReject
    ∧ clock_check 2 (SyscallEffect.mkEffectU 0 [(4096, ts_1s)] [] [(4096, 4096)] [] []) (clock_model 0)
        = CheckReject
    ∧ clock_check 2 (SyscallEffect.mkEffectU 0 [(4096, ts_1s)] [] [] [MemCopy.mkCopy 4096 4096 8] [])
        (clock_model 0) = CheckReject
    ∧ clock_check 2 (SyscallEffect.mkEffectU 0 [(4096, ts_1s)] [] [] [] [(4096, 16)]) (clock_model 0)
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- An unwritable destination declines rather than models the `-EFAULT`
`put_timespec64` would return: the spec's probe of `in_wmem` is a 16-byte
writability question with no partial answer, and the checker asks it
before it looks at the effect, so the effect here is the one a lying
kernel would offer.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_unwritable_tp_is_unmodeled :
    check_clock_gettime (clock_input_unwritable 1) 1 4096 (mkEffect 0 [(4096, ts_1s)] [])
      (clock_model 0) = CheckUnmodeled := by
  conv => lhs; whnf

/-- The same decline on the wall-clock arm (id 0): the writability
question is asked before the effect is looked at on every arm (on the
monotonic arm, after the envelope gate), so a checker
that modeled `put_timespec64`'s `-EFAULT` as `CheckReject` on the arms
that record nothing, and declined only where it records, would be
separated here.  Bool-gated arm, so plain `rfl` (see the header).
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem realtime_unwritable_tp_is_unmodeled :
    check_clock_gettime (clock_input_unwritable 0) 0 4096 (mkEffect 0 [(4096, ts_1s)] [])
      (clock_model 0) = CheckUnmodeled := rfl

/-- And on the per-process CPU arm (id 2), for the same reason.
kernel: kernel/time/posix-timers.c:clock_gettime; kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem cputime_unwritable_tp_is_unmodeled :
    check_clock_gettime (clock_input_unwritable 2) 2 4096 (mkEffect 0 [(4096, ts_1s)] [])
      (clock_model 0) = CheckUnmodeled := rfl

/-! ### Sixteen bytes, probed at `tp`

The unwritable-`tp` cases leave nothing writable, so a checker probing
fewer than sixteen bytes, or probing a fixed address, answers them
alike.  These separate it.  A `tp` one byte into the sixteen-byte zone
has fifteen writable bytes and declines on every arm: `copy_to_user`
would fault on byte sixteen having written fifteen, a partial answer the
model does not give.  And a `tp` with sixteen bytes writable at 8192 and
none at 4096 is answered on every arm, with the write required at 8192. -/

/-- `tp` = 4097 against the zone ending at 4112: fifteen writable bytes
are not sixteen, on the monotonic arm.  The effect offered is the one a
lying kernel would offer; the checker never reaches it.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_straddling_tp_is_unmodeled :
    check_clock_gettime (clock_input 1) 1 4097 (mkEffect 0 [(4097, ts_1s)] []) (clock_model 0)
      = CheckUnmodeled := by
  conv => lhs; whnf

/-- The same on the wall-clock arm.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem realtime_straddling_tp_is_unmodeled :
    check_clock_gettime (clock_input 0) 0 4097 (mkEffect 0 [(4097, ts_1s)] []) (clock_model 0)
      = CheckUnmodeled := rfl

/-- And on the CPU-time arm.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem cputime_straddling_tp_is_unmodeled :
    check_clock_gettime (clock_input 2) 2 4097 (mkEffect 0 [(4097, ts_1s)] []) (clock_model 0)
      = CheckUnmodeled := rfl

/-- Sixteen writable bytes at 8192 and nothing anywhere else: `rlim_out`
moved up, spelled with the same `Bool` comparisons so that the arms that
close by `rfl` keep doing so. -/
def wmem_at_8192 : word → Option byte :=
  fun a => if bv_leu 8192 a && bv_ltu a 8208 then some 0 else none

/-- `clock_gettime(clkid, 8192)` with exactly that writable. -/
def clock_input_at_8192 (clkid : word) : SyscallInput :=
  SyscallInput.mkInput 113 [clkid, 8192, 0, 0, 0, 0] (fun _ => none) wmem_at_8192

/-- The struct lands wherever `tp` points: with `tp` = 8192 the monotonic
call is answered and recorded when the write is at 8192, and refused
when it is at 4096, where every other case in this file puts it.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem clock_lands_at_tp :
    check_clock_gettime (clock_input_at_8192 1) 1 8192 (mkEffect 0 [(8192, ts_1s)] [])
        (clock_model 0) = CheckOk (clock_model 1000000000) []
    ∧ check_clock_gettime (clock_input_at_8192 1) 1 8192 (mkEffect 0 [(4096, ts_1s)] [])
        (clock_model 0) = CheckReject := by
  refine ⟨?_, ?_⟩
  · conv => lhs; whnf
    rfl
  · conv => lhs; whnf

/-- The same on the wall-clock arm, which records nothing.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem realtime_lands_at_tp :
    check_clock_gettime (clock_input_at_8192 0) 0 8192 (mkEffect 0 [(8192, ts_1s)] [])
        (clock_model 0) = CheckOk (clock_model 0) []
    ∧ check_clock_gettime (clock_input_at_8192 0) 0 8192 (mkEffect 0 [(4096, ts_1s)] [])
        (clock_model 0) = CheckReject := ⟨rfl, rfl⟩

/-- And on the CPU-time arm.
kernel: kernel/time/time.c:put_timespec64@v6.18.46 -/
theorem cputime_lands_at_tp :
    check_clock_gettime (clock_input_at_8192 2) 2 8192 (mkEffect 0 [(8192, ts_1s)] [])
        (clock_model 0) = CheckOk (clock_model 0) []
    ∧ check_clock_gettime (clock_input_at_8192 2) 2 8192 (mkEffect 0 [(4096, ts_1s)] [])
        (clock_model 0) = CheckReject := ⟨rfl, rfl⟩

/-! ## The witness, evaluated

`clock_gettime_witness_ok` proves the witness is an outcome the spec
admits on every input and model.  These read off WHICH outcome it is on
the fixtures, so a reader can see the receptiveness obligation's
content rather than its type: the recorded clock re-recorded on the
monotonic arm, the zero reading on the arms that record nothing, and a
decline exactly where the checker declines. -/

/-- On the monotonic arm the witness reads the recorded clock — one second
here, encoded by `clock_gettime_bytes` as `ts_1s` — and hands back a model
that records the same value.
model: `clock_gettime_witness` on the monotonic fixture -/
theorem witness_monotonic_reads_the_recorded_clock :
    clock_witness 1 (clock_model 1000000000)
      = Ok (mkEffect 0 [(4096, ts_1s)] []) (clock_model 1000000000) [] := by
  conv => lhs; whnf
  rfl

/-- On the wall-clock and CPU-time arms the witness answers the zero
reading and leaves the model alone.
model: `clock_gettime_witness` on the fixtures of the arms that record nothing -/
theorem witness_unrecording_arms_read_zero :
    clock_witness 0 (clock_model 1000000000)
        = Ok (mkEffect 0 [(4096, ts_0)] []) (clock_model 1000000000) []
      ∧ clock_witness 2 (clock_model 1000000000)
        = Ok (mkEffect 0 [(4096, ts_0)] []) (clock_model 1000000000) [] := ⟨rfl, rfl⟩

/-- The witness declines exactly where the checker does: an unmodeled id,
a recorded clock at the envelope, an unwritable destination.
model: `clock_gettime_witness` on the three declining fixtures -/
theorem witness_declines_where_the_checker_declines :
    clock_witness 3 (clock_model 0) = Unmodeled
      ∧ clock_witness 1 (clock_model (2 ^ 63)) = Unmodeled
      ∧ clock_gettime_witness 1 4096 (clock_input_unwritable 1) (clock_model 0) = Unmodeled :=
  ⟨rfl, by conv => lhs; whnf, by conv => lhs; whnf⟩

/-- And the checker accepts what the witness offers, on the fixture where
the witness records: the concrete face of `clock_gettime_witness_ok`.
The first half is `clock_equal_reading_is_admissible`'s kernel claim — a
reading equal to the last is one `ktime_get_ts64` can return — restated
beside the witness that relies on it.
kernel: kernel/time/timekeeping.c:ktime_get_ts64@v6.18.46 -/
theorem checker_accepts_the_witness :
    clock_check 1 (mkEffect 0 [(4096, ts_1s)] []) (clock_model 1000000000)
      = CheckOk (clock_model 1000000000) []
    ∧ clock_witness 1 (clock_model 1000000000)
      = Ok (mkEffect 0 [(4096, ts_1s)] []) (clock_model 1000000000) [] := by
  refine ⟨?_, ?_⟩
  · conv => lhs; whnf
    rfl
  · conv => lhs; whnf
    rfl

/-! ## The header's claim about the elaborator, pinned

The header says the `conv => lhs; whnf` lines exist because `rfl`'s
`whnfCore` runs under `proj := .yesWithDeltaI`, the setting
`backward.isDefEq.lazyWhnfCore` selects, and that with the option off the
monotonic cases close by plain `rfl`.  One monotonic case, stated that
way: when this stops elaborating, either the option or the mechanism has
changed, and the header is what to reread. -/

set_option backward.isDefEq.lazyWhnfCore false in
/-- `clock_advancing_reading_records_it` by plain `rfl`, under the option
that turns the projection setting off.
model: `check_clock_gettime` on the monotonic fixture, elaborated without `.yesWithDeltaI` -/
example : clock_check 1 (mkEffect 0 [(4096, ts_2s)] []) (clock_model 1000000000)
      = CheckOk (clock_model 2000000000) [] := rfl

-- lean-port sentinel: ticket V-Kernel-Time-PosixTimers appends below this line

section V_Kernel_Time_PosixTimers

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Kernel-Time-PosixTimers — `clock_gettime` over the real table

WHAT IS TWINNED HERE.  The sections above state Rocq's cases on
`clock_check`, because `checked_table` carried no row for 113 when they
were written.  Each of the twenty-two `Example`s
`theories/LinuxProcessSem/Checks/Cases/Kernel/Time/PosixTimers.v` states
through `check_syscall` is restated at the end of this section through
the Lean `check_syscall`, over `checked_table` itself, at the Rocq input
`clock_input clkid`, under its Rocq name with `_over_the_real_table`
after it, K6b's convention for the pins at which the real table first
answers a call.  The kernel argument for each is its twin's above, under
the Rocq name, and its evidence line is that twin's.

WHAT A PIN HERE ADDS to its twin above is the ARM's claim: that the
lookup at 113 finds `arm_clock_gettime` rather than the dispatcher's own
decline, and that the arm hands the checker the id from `a0`, narrowed to
its low 32 bits, and the destination from `a1`.  The narrowing is the
wide-id pins' below; `checker_and_witness_read_whole_words` fixes that it
lives in the arm's reading and not in the checker.

POLARITY: the evidence line is `kernel:` on every pin about the kernel's
answer, `CheckOk`, `CheckReject` and `CheckUnmodeled` alike, and `model:`
on a pin about the table's own contents or about the checker's contract
with the arm's reading, which the pin's own statement says. -/

/-- The lookup the dispatcher performs on a `clock_input`, computed once:
`in_sysno` is 113 whatever the id register holds.
model: `lookup_ca` over `checked_table` at a closed number; the table's own contents, not a kernel claim -/
theorem lookup_clock_input (clkid : word) :
    lookup_ca checked_table (bv_unsigned (clock_input clkid).in_sysno)
      = some arm_clock_gettime :=
  lookup_ca_checked_table_clock_gettime

/-! ### The id register's low 32 bits, through the table

`wide_id_low_word_selects_monotonic` and its neighbours above state the
narrowing on `clock_check`, which applies `clockid32` itself; here the
table applies it, so the arm's reading is what is under test.  One pin
per modeled id: each passes an id whose low word is that id and whose
whole word is no modeled id. -/

/-- `2^32 + 1` narrows to `CLOCK_MONOTONIC`: the advancing reading is
admitted and recorded, as in `clock_advancing_reading_records_it`.
`SYSCALL_DEFINE2(clock_gettime, const clockid_t, which_clock, …)`
(kernel/time/posix-timers.c:1136, Linux v6.18.46) takes the id as a
`clockid_t`, an `int`, and riscv64's wrapper casts the register to it
through `__SC_CAST` (include/linux/syscalls.h:132, Linux v6.18.46) before
`clockid_to_kclock` reads it.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock@v6.18.46 -/
theorem wide_id_low_word_selects_monotonic_over_the_real_table :
    check_syscall (clock_input 4294967297) (mkEffect 0 [(4096, ts_2s)] [])
        (clock_model 1000000000)
      = CheckOk (clock_model 2000000000) [] := by
  conv => lhs; whnf
  rfl

/-- `2^32` narrows to `CLOCK_REALTIME`: the wall-clock arm answers over a
recorded clock at 2^63 ns (`realtime_ignores_the_recorded_clock`), where
`2^32 + 1`, narrowed to the monotonic arm, declines
(`clock_at_envelope_declines`); and it rejects the negative-`tv_sec`
reading (`realtime_negative_tv_sec_rejected`) that `2^32 + 2`, narrowed to
the CPU-time arm, admits (`wide_id_low_word_selects_cputime_over_the_real_table`).
kernel: include/linux/syscalls.h:__SC_CAST; kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock@v6.18.46 -/
theorem wide_id_low_word_selects_realtime_over_the_real_table :
    check_syscall (clock_input 4294967296) (mkEffect 0 [(4096, ts_1s)] [])
        (clock_model (2 ^ 63))
      = CheckOk (clock_model (2 ^ 63)) []
    ∧ check_syscall (clock_input 4294967297) (mkEffect 0 [(4096, ts_1s)] [])
        (clock_model (2 ^ 63))
      = CheckUnmodeled
    ∧ check_syscall (clock_input 4294967296) (mkEffect 0 [(4096, ts_cpu_neg1)] [])
        (clock_model 0)
      = CheckReject := by
  refine ⟨rfl, ?_, rfl⟩
  conv => lhs; whnf

/-- `2^32 + 2` narrows to `CLOCK_PROCESS_CPUTIME_ID`: a reading with a
negative `tv_sec` is admitted (`cputime_negative_tv_sec_admissible`),
where `2^32 + 1`, narrowed to the monotonic arm, rejects it, as `2^32`
does (`wide_id_low_word_selects_realtime_over_the_real_table`).
kernel: include/linux/syscalls.h:__SC_CAST; kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock@v6.18.46 -/
theorem wide_id_low_word_selects_cputime_over_the_real_table :
    check_syscall (clock_input 4294967298) (mkEffect 0 [(4096, ts_cpu_neg1)] [])
        (clock_model 0)
      = CheckOk (clock_model 0) []
    ∧ check_syscall (clock_input 4294967297) (mkEffect 0 [(4096, ts_cpu_neg1)] [])
        (clock_model 0)
      = CheckReject := by
  refine ⟨rfl, ?_⟩
  conv => lhs; whnf

/-- The checker's and the witness's side of the narrowing: handed the
whole register words the three pins above hand the table, the checker
declines each, and the witness declines the first, because both compare
the whole 64-bit word they are given, as Rocq's do.  Together with the
pins above this fixes where the narrowing lives: in the arm's `clockid32`
reading, not in the checker or the witness.  It is not the kernel's
answer at those registers — Linux narrows before it reads the id
(`__SC_CAST`, include/linux/syscalls.h:132, Linux v6.18.46) — which is
why the evidence line is `model:`.
model: the checker's and the witness's contract with the arm's reading; Linux narrows first (__SC_CAST, cited above) -/
theorem checker_and_witness_read_whole_words :
    check_clock_gettime (clock_input 4294967297) 4294967297 4096
        (mkEffect 0 [(4096, ts_2s)] []) (clock_model 1000000000) = CheckUnmodeled
    ∧ check_clock_gettime (clock_input 4294967296) 4294967296 4096
        (mkEffect 0 [(4096, ts_1s)] []) (clock_model (2 ^ 63)) = CheckUnmodeled
    ∧ check_clock_gettime (clock_input 4294967298) 4294967298 4096
        (mkEffect 0 [(4096, ts_cpu_neg1)] []) (clock_model 0) = CheckUnmodeled
    ∧ clock_gettime_witness 4294967297 4096 (clock_input 4294967297) (clock_model 1000000000)
        = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · conv => lhs; whnf
  · conv => lhs; whnf
  · conv => lhs; whnf
  · conv => lhs; whnf

/-! ### The ids the model declines, through the table -/

/-- The ids the probe's `fail-closed` id cases pass are declined through
the table, a reading and a dropped write alike.
`CLOCK_THREAD_CPUTIME_ID` (3) and `CLOCK_TAI` (11) each have a clock in
`posix_clocks[]` (kernel/time/posix-timers.c:1518-1529, Linux v6.18.46),
`CLOCK_SGI_CYCLE` (10) is a NULL hole in it that answers -EINVAL,
and -6 and -1, sign-extended into `a0` as the C caller passes an `int`,
take `clockid_to_kclock`'s `id < 0` branch
(kernel/time/posix-timers.c:1539-1542, Linux v6.18.46); the model answers
none of them (`clock_gettime_only_the_modeled_clocks`).
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock@v6.18.46 -/
theorem probe_unmodeled_ids_decline_over_the_real_table :
    check_syscall (clock_input 3) (mkEffect 0 [(4096, ts_1s)] []) (clock_model 0)
      = CheckUnmodeled
    ∧ check_syscall (clock_input 3) (mkEffect 0 [] []) (clock_model 0) = CheckUnmodeled
    ∧ check_syscall (clock_input 10) (mkEffect 0 [(4096, ts_1s)] []) (clock_model 0)
      = CheckUnmodeled
    ∧ check_syscall (clock_input 10) (mkEffect 0 [] []) (clock_model 0) = CheckUnmodeled
    ∧ check_syscall (clock_input 11) (mkEffect 0 [(4096, ts_1s)] []) (clock_model 0)
      = CheckUnmodeled
    ∧ check_syscall (clock_input 18446744073709551610) (mkEffect 0 [(4096, ts_1s)] [])
        (clock_model 0) = CheckUnmodeled
    ∧ check_syscall (clock_input 18446744073709551615) (mkEffect 0 [(4096, ts_1s)] [])
        (clock_model 0) = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals conv => lhs; whnf

/-! ### The probe's return lies, through the table -/

/-- `ret=-EINVAL` and `ret=1`, two of the probe's `reject` lies, are
refused on the monotonic and the wall-clock arm through the table.
`posix_clocks[]` gives id 0 `posix_get_realtime_timespec`
(kernel/time/posix-timers.c:194-198) and id 1
`posix_get_monotonic_timespec` (kernel/time/posix-timers.c:217-222, both
Linux v6.18.46), which return 0 unconditionally; the syscall's
own -EINVAL is for an id `clockid_to_kclock` finds no clock for
(kernel/time/posix-timers.c:1143-1144), and it returns 0 once
`put_timespec64` has copied the reading out (:1148-1151).
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock,posix_get_monotonic_timespec,posix_get_realtime_timespec@v6.18.46 -/
theorem probe_return_lies_rejected_over_the_real_table :
    check_syscall (clock_input 1) (mkEffect (errno_ret EINVAL) [] []) (clock_model 0)
      = CheckReject
    ∧ check_syscall (clock_input 1) (mkEffect 1 [(4096, ts_1s)] []) (clock_model 0)
      = CheckReject
    ∧ check_syscall (clock_input 0) (mkEffect (errno_ret EINVAL) [] []) (clock_model 0)
      = CheckReject
    ∧ check_syscall (clock_input 0) (mkEffect 1 [(4096, ts_1s)] []) (clock_model 0)
      = CheckReject := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · conv => lhs; whnf
  · conv => lhs; whnf

/-! ### The witness the table hands `receptive`

`syscall_spec_witness` dispatches over the same table, so the arm's
`ca_witness` is what it answers at 113; the witness pins above fix
`clock_gettime_witness` on the arm's call, these fix that the table hands
it the same reading the checker gets. -/

/-- On the monotonic arm the table's witness reads the recorded clock and
re-records it, as `witness_monotonic_reads_the_recorded_clock` shows on
the arm's call.
kernel: kernel/time/posix-timers.c:clock_gettime,posix_get_monotonic_timespec@v6.18.46 -/
theorem witness_monotonic_reads_the_recorded_clock_over_the_real_table :
    syscall_spec_witness (clock_input 1) (clock_model 1000000000)
      = Ok (mkEffect 0 [(4096, ts_1s)] []) (clock_model 1000000000) [] := by
  conv => lhs; whnf
  rfl

/-- `2^32 + 1` in `a0`: narrowed, the id is `CLOCK_MONOTONIC`, and the
witness exhibits the monotonic reading — not the decline it exhibits for
that whole word (`checker_and_witness_read_whole_words`).
kernel: include/linux/syscalls.h:__SC_CAST; kernel/time/posix-timers.c:clock_gettime@v6.18.46 -/
theorem wide_id_witnesses_the_monotonic_reading_over_the_real_table :
    syscall_spec_witness (clock_input 4294967297) (clock_model 1000000000)
      = Ok (mkEffect 0 [(4096, ts_1s)] []) (clock_model 1000000000) [] := by
  conv => lhs; whnf
  rfl

/-- `CLOCK_THREAD_CPUTIME_ID` (3): the witness declines where the checker
does (`probe_unmodeled_ids_decline_over_the_real_table`).
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock@v6.18.46 -/
theorem unmodeled_id_witnesses_unmodeled_over_the_real_table :
    syscall_spec_witness (clock_input 3) (clock_model 0) = Unmodeled := by
  conv => lhs; whnf

/-! ### Rocq's twenty-two cases, through `check_syscall` -/

/-- Rocq's `clock_at_envelope_declines` through `check_syscall`.  The same call
on `clock_check` is `clock_at_envelope_declines`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46 -/
theorem clock_at_envelope_declines_over_the_real_table :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_1s)] [])
        (clock_model (2 ^ 63))
      = CheckUnmodeled := by
  conv => lhs; whnf

/-- Rocq's `clock_equal_reading_is_admissible` through `check_syscall`.  The same call
on `clock_check` is `clock_equal_reading_is_admissible`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/timekeeping.c:ktime_get_ts64@v6.18.46 -/
theorem clock_equal_reading_is_admissible_over_the_real_table :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_1s)] [])
        (clock_model 1000000000)
      = CheckOk (clock_model 1000000000) [] := by
  conv => lhs; whnf
  rfl

/-- Rocq's `clock_advancing_reading_records_it` through `check_syscall`.  The same call
on `clock_check` is `clock_advancing_reading_records_it`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/timekeeping.c:ktime_get_ts64@v6.18.46 -/
theorem clock_advancing_reading_records_it_over_the_real_table :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_2s)] [])
        (clock_model 1000000000)
      = CheckOk (clock_model 2000000000) [] := by
  conv => lhs; whnf
  rfl

/-- Rocq's `clock_backwards_reading_rejected` through `check_syscall`.  The same call
on `clock_check` is `clock_backwards_reading_rejected`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/timekeeping.c:ktime_get_ts64,do_settimeofday64,__timekeeping_inject_offset,__timekeeping_inject_sleeptime,accumulate_nsecs_to_secs; kernel/time/posix-timers.c:clock_settime@v6.18.46 -/
theorem clock_backwards_reading_rejected_over_the_real_table :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_1s_minus)] [])
        (clock_model 1000000000)
      = CheckReject := by
  conv => lhs; whnf

/-- Rocq's `clock_denormalized_nsec_rejected` through `check_syscall`.  The same call
on `clock_check` is `clock_denormalized_nsec_rejected`, above, whose docstring carries the
kernel argument.
kernel: include/linux/time64.h:timespec64_add_ns; kernel/time/timekeeping.c:ktime_get_ts64@v6.18.46 -/
theorem clock_denormalized_nsec_rejected_over_the_real_table :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_denorm)] [])
        (clock_model 0)
      = CheckReject := by
  conv => lhs; whnf

/-- Rocq's `clock_reading_at_envelope_minus_one_admissible` through `check_syscall`.  The same call
on `clock_check` is `clock_reading_at_envelope_minus_one_admissible`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46 -/
theorem clock_reading_at_envelope_minus_one_admissible_over_the_real_table :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_max)] [])
        (clock_model 0)
      = CheckOk (clock_model (2 ^ 63 - 1)) [] := by
  conv => lhs; whnf
  rfl

/-- Rocq's `clock_reading_at_envelope_rejected` through `check_syscall`.  The same call
on `clock_check` is `clock_reading_at_envelope_rejected`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46 -/
theorem clock_reading_at_envelope_rejected_over_the_real_table :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_over)] [])
        (clock_model 0)
      = CheckReject := by
  conv => lhs; whnf

/-- Rocq's `clock_reading_wrapping_sum_rejected` through `check_syscall`.  The same call
on `clock_check` is `clock_reading_wrapping_sum_rejected`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/namespace.c:proc_timens_set_offset@v6.18.46 -/
theorem clock_reading_wrapping_sum_rejected_over_the_real_table :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_wrap)] [])
        (clock_model 0)
      = CheckReject := by
  conv => lhs; whnf

/-- Rocq's `realtime_backwards_reading_is_admissible` through `check_syscall`.  The same call
on `clock_check` is `realtime_backwards_reading_is_admissible`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/timekeeping.c:do_settimeofday64,__timekeeping_inject_offset@v6.18.46 -/
theorem realtime_backwards_reading_is_admissible_over_the_real_table :
    check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_1s_minus)] [])
        (clock_model 1000000000)
      = CheckOk (clock_model 1000000000) [] := rfl

/-- Rocq's `realtime_ignores_the_recorded_clock` through `check_syscall`.  The same call
on `clock_check` is `realtime_ignores_the_recorded_clock`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock,posix_get_realtime_timespec@v6.18.46 -/
theorem realtime_ignores_the_recorded_clock_over_the_real_table :
    check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_1s)] [])
        (clock_model (2 ^ 63))
      = CheckOk (clock_model (2 ^ 63)) [] := rfl

/-- Rocq's `realtime_denormalized_nsec_rejected` through `check_syscall`.  The same call
on `clock_check` is `realtime_denormalized_nsec_rejected`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/timekeeping.c:ktime_get_real_ts64; include/linux/time64.h:timespec64_add_ns@v6.18.46 -/
theorem realtime_denormalized_nsec_rejected_over_the_real_table :
    check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_denorm)] [])
        (clock_model 0)
      = CheckReject := rfl

/-- Rocq's `realtime_reading_at_envelope_rejected` through `check_syscall`.  The same call
on `clock_check` is `realtime_reading_at_envelope_rejected`, above, whose docstring carries the
kernel argument.
kernel: include/linux/time64.h:timespec64_valid_settod; kernel/time/timekeeping.c:do_settimeofday64,__timekeeping_inject_offset,__timekeeping_inject_sleeptime,accumulate_nsecs_to_secs@v6.18.46 -/
theorem realtime_reading_at_envelope_rejected_over_the_real_table :
    check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_over)] [])
        (clock_model 0)
      = CheckReject := rfl

/-- Rocq's `realtime_reading_at_envelope_minus_one_admissible` through `check_syscall`.  The same call
on `clock_check` is `realtime_reading_at_envelope_minus_one_admissible`, above, whose docstring carries the
kernel argument.
kernel: include/linux/time64.h:timespec64_valid_settod; kernel/time/timekeeping.c:do_settimeofday64@v6.18.46 -/
theorem realtime_reading_at_envelope_minus_one_admissible_over_the_real_table :
    check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_max)] [])
        (clock_model 0)
      = CheckOk (clock_model 0) [] := rfl

/-- Rocq's `cputime_backwards_reading_is_admissible` through `check_syscall`.  The same call
on `clock_check` is `cputime_backwards_reading_is_admissible`, above, whose docstring carries the
kernel argument.
kernel: kernel/sched/cputime.c:thread_group_cputime; kernel/time/posix-cpu-timers.c:cpu_clock_sample_group@v6.18.46 -/
theorem cputime_backwards_reading_is_admissible_over_the_real_table :
    check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_1s_minus)] [])
        (clock_model 1000000000)
      = CheckOk (clock_model 1000000000) [] := rfl

/-- Rocq's `cputime_ignores_the_recorded_clock` through `check_syscall`.  The same call
on `clock_check` is `cputime_ignores_the_recorded_clock`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/posix-timers.c:clock_gettime,clockid_to_kclock; kernel/time/posix-cpu-timers.c:process_cpu_clock_get@v6.18.46 -/
theorem cputime_ignores_the_recorded_clock_over_the_real_table :
    check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_1s)] [])
        (clock_model (2 ^ 63))
      = CheckOk (clock_model (2 ^ 63)) [] := rfl

/-- Rocq's `cputime_denormalized_nsec_rejected` through `check_syscall`.  The same call
on `clock_check` is `cputime_denormalized_nsec_rejected`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46 -/
theorem cputime_denormalized_nsec_rejected_over_the_real_table :
    check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_denorm)] [])
        (clock_model 0)
      = CheckReject := rfl

/-- Rocq's `cputime_negative_tv_sec_admissible` through `check_syscall`.  The same call
on `clock_check` is `cputime_negative_tv_sec_admissible`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/time.c:ns_to_timespec64; kernel/sched/cputime.c:thread_group_cputime@v6.18.46 -/
theorem cputime_negative_tv_sec_admissible_over_the_real_table :
    check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_cpu_neg1)] [])
        (clock_model 0)
      = CheckOk (clock_model 0) [] := rfl

/-- Rocq's `realtime_negative_tv_sec_rejected` through `check_syscall`.  The same call
on `clock_check` is `realtime_negative_tv_sec_rejected`, above, whose docstring carries the
kernel argument.
kernel: include/linux/time64.h:timespec64_valid,timespec64_valid_settod@v6.18.46 -/
theorem realtime_negative_tv_sec_rejected_over_the_real_table :
    check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_cpu_neg1)] [])
        (clock_model 0)
      = CheckReject := rfl

/-- Rocq's `cputime_at_signed_envelope_admissible` through `check_syscall`.  The same call
on `clock_check` is `cputime_at_signed_envelope_admissible`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46 -/
theorem cputime_at_signed_envelope_admissible_over_the_real_table :
    check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_cpu_min)] [])
        (clock_model 0)
      = CheckOk (clock_model 0) [] := rfl

/-- Rocq's `cputime_below_signed_envelope_rejected` through `check_syscall`.  The same call
on `clock_check` is `cputime_below_signed_envelope_rejected`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46 -/
theorem cputime_below_signed_envelope_rejected_over_the_real_table :
    check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_cpu_below)] [])
        (clock_model 0)
      = CheckReject := rfl

/-- Rocq's `cputime_reading_at_envelope_minus_one_admissible` through `check_syscall`.  The same call
on `clock_check` is `cputime_reading_at_envelope_minus_one_admissible`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46 -/
theorem cputime_reading_at_envelope_minus_one_admissible_over_the_real_table :
    check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_max)] [])
        (clock_model 0)
      = CheckOk (clock_model 0) [] := rfl

/-- Rocq's `cputime_reading_at_envelope_rejected` through `check_syscall`.  The same call
on `clock_check` is `cputime_reading_at_envelope_rejected`, above, whose docstring carries the
kernel argument.
kernel: kernel/time/time.c:ns_to_timespec64@v6.18.46 -/
theorem cputime_reading_at_envelope_rejected_over_the_real_table :
    check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_over)] [])
        (clock_model 0)
      = CheckReject := rfl

end V_Kernel_Time_PosixTimers

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Time.PosixTimers
