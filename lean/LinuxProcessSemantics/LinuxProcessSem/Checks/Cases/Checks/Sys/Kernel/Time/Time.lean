-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Kernel/Time/Time.v
-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Kernel/Time/Time.v

import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.Time
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.Time
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress


/-! # Checks.Cases.Checks.Sys.Kernel.Time.Time — what the gettimeofday checker answers, read off against Linux

Pins over `check_gettimeofday` of `Checks/Sys/Kernel/Time/Time.lean`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Kernel/Time/Time.v`'s checker, and
over `gettimeofday_witness`, the twin of
`theories/LinuxProcessSem/Checks/Witness/Kernel/Time/Time.v`'s witness,
both in `Checks/Sys/Kernel/Time/Time.lean`.  Not part of the trusted
specification: this file is QA on the executable definitions, written to
be READ, and every claim in it is a claim about what the kernel does, with
the citation beside it.  Every kernel line below was read at Linux
v6.18.46 (commit 1f99e9ab748f), and the Rocq cases restated here at the
checker's `rocq-baseline`, a71fd38a08571d519b9cfc5f66308db5c26da570.

WHAT THIS FILE IS.  Rocq states its worked cases for this syscall on the
CHECKER: the `Example`s of `theories/LinuxProcessSem/Checks/Cases/Kernel/Time/Time.v`
are `check_syscall … = CheckOk …`, `= CheckReject` and `= CheckUnmodeled`.
The Lean port of that file, `Checks/Cases/Kernel/Time/Time.lean`, restated
each of them on the RELATION `gettimeofday_spec`, because the Lean tree
had no executable checker when it was written; those restatements carry
the `rocq-twin:` marks and stay where they are.  This file states the same
cases on the checker, under the names the relation-level twin gave them
(the two quantified pins reworded; each docstring names the Rocq case it
restates), and adds the ones a
checker invites that a relation does not: the lies on the return word, the write
list, the effect's other ledgers and the model that the acceptor must
REJECT rather than merely fail to accept.  There is no
`theories/…/Checks/Cases/Checks/Sys/…` file for it to twin, so nothing
here is marked `rocq-twin:`; each pin cites the kernel line the Rocq
docstring argues from instead, and the argument is repeated in its own
words so the citation can be checked against it.

WHY PINS ON A CHECKER AT ALL, when four lemmas already tie it to the spec:
the lemmas catch a checker changed alone, and only a concrete answer from
outside catches a spec and a checker moved together —
`writable_tv_efault_rejected` is the one that says so in place.

HOW THE CALL IS STATED.  Rocq's cases go through `check_syscall`, the
dispatcher.  The sections below were written while `checked_table`
carried no arm for 169 — the row is the V ticket's registration step,
since PR #904 moved registration out of the checker tickets — so they
state the cases on the call the `gettimeofday` arm makes,
`check_gettimeofday` on the input and the two pointer registers, with the
pointers the dispatcher reads out of `in_arg i 0` and `in_arg i 1`
written in place; `dispatch_shape` states one of them through `in_arg` so
that the fixture's slots are pinned to the order the other pins assume.
The section `V_Kernel_Time_Time` at the end of this file, added with the
registration (`Checks/Arms/Kernel/Time/Time.lean`), restates each Rocq
example through `check_syscall` over the real table.

HOW THE CONCRETE CASES CLOSE.  The checker is a closed computation on
these fixtures and `check_result` carries a `Model`, which has no
`DecidableEq`, so `decide` is not available and a concrete case is `rfl`:
the kernel evaluates the checker, sixteen-byte `copy_bytes_map` walks
included (the one equation between byte lists, `timeval_zero_is_the_epoch`,
has a `DecidableEq` and closes by `decide`).  On these fixtures every `rfl` here closed in the module's
build without meeting the `maxRecDepth` wall the clock_gettime and
nanosleep pins beside this file describe, so this file defines no closer
macro; if a fixture ever meets that wall, the mechanism those files record
applies.  Of the two quantified pins, `never_moves_the_model` reads
`check_gettimeofday_ok_inv` and `declines_every_timezone` unfolds the
checker directly, since the gate it pins fires before any inversion has
a `CheckOk` to invert.

FIXTURES ARE THE SPEC PINS' OWN.  `gettimeofday_input`, the three
timevals, the wrap and high destinations, the open memory and
`task_size_minus` are `Checks/Cases/Kernel/Time/Time.lean`'s, opened
below, so a fixture cannot drift between the two files.  The model is
`Prelude.demo_model` where Rocq's Examples use `clock_model 0`: that
fixture exists in the Lean tree too
(`Checks/Cases/Kernel/Time/PosixTimers.lean`), but opening that file
beside this one puts two `wmem_ts` in scope, and the checker reads no
field of the model, so `demo_model` pins the same facts.
`moved_clock_rejected` below is where the model's clock matters, and it
builds its moved model with `with_clock`, as `clock_model` does.

WHAT NO PROBE CAN REACH.  No probe under `testing/syscall-check/` runs a
Lean definition: the harness runs the extracted Rocq model.  The Lean
acceptor meets the probes' recorded `CASE` lines only through the replay
(`tools/lean_replay.py`, with the runner pin
`tools/lps_runner_arms/gettimeofday_spec/169-gettimeofday.json`), which
judges a recorded verdict and no pin here.  Every pin here cites the
kernel line instead.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Time.Time

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.Time
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.Time

/-! ## `sys_tz`: a non-NULL timezone pointer is `CheckUnmodeled`

`SYSCALL_DEFINE2(gettimeofday, ...)` (kernel/time/time.c:140-156, v6.18.46)
copies a mutable file-scope `struct timezone` into a non-NULL `tz`
(:151-153), whose one writer in the riscv build is `do_sys_settimeofday64`
(:186 — `arch/powerpc/kernel/time.c`'s `time_init` also assigns it, from
firmware, on that architecture alone); the model
has nowhere to carry the value, so the spec declines and the checker's
only answer is `CheckUnmodeled` — never `CheckOk`, which would accept a
guess, and never `CheckReject`, which would refuse the kernel's real
answer on a call the model does not decide. -/

/-- UNIVERSALLY QUANTIFIED, the twin of Rocq's first checker lemma,
`gettimeofday_declines_every_timezone`: every
non-NULL timezone pointer is `CheckUnmodeled`, whatever the destination,
the input, the effect or the model.
kernel: kernel/time/time.c:gettimeofday,do_sys_settimeofday64@v6.18.46 -/
theorem declines_every_timezone (tz : word) (h : w_is0 tz = false) (i : SyscallInput)
    (tv : word) (eff : SyscallEffect) (m : Model) :
    check_gettimeofday i tv tz eff m = CheckUnmodeled := by
  unfold check_gettimeofday
  simp only [h, Bool.not_false, ↓reduceIte]

/-- The confident guess offered to the checker: a reading at `tv` and
`{0, 0}` at `tz` = 8192, which is what the kernel writes on a machine
where nothing has set `sys_tz`.  Not `CheckOk`: declined.
kernel: kernel/time/time.c:gettimeofday,do_sys_settimeofday64@v6.18.46 -/
theorem timezone_zero_answer_declines :
    check_gettimeofday (gettimeofday_input 8192) 4096 8192
      (mkEffect 0 [(4096, tv_ceiling_minus), (8192, List.replicate 8 0)] []) demo_model
    = CheckUnmodeled := by
  rfl

/-- …and the -EFAULT the `tz` copy (:152-153) answers on an unwritable
`tz` is declined too, not rejected: the checker does not decide this call.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem timezone_efault_declines :
    check_gettimeofday (gettimeofday_input 8192) 4096 8192
      (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled := by
  rfl

/-- The kernel's order, at the checker: a `tv` whose first `put_user` is
refused and `tz` set.  Linux returns -EFAULT at :149 before `tz` is read,
so this is the one call where a `tz` arm that answered anything would
have to answer in the kernel's order; the checker declines, which is
sound over that -EFAULT and every other answer.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem timezone_with_bad_tv_declines :
    check_gettimeofday
      (SyscallInput.mkInput 169 [gettimeofday_wrap_tv, 8192, 0, 0, 0, 0] (fun _ => none)
        gettimeofday_wrap_mem)
      gettimeofday_wrap_tv 8192 (mkEffect (errno_ret EFAULT) [] []) demo_model
    = CheckUnmodeled := by
  rfl

/-! ## A NULL `tv` is `CheckUnmodeled`

With both pointers NULL the kernel skips both blocks (:143, :151) and
returns 0 (:155) having written nothing.  The arm declines — Rocq's
declared narrowing, kept by the Lean twin — so the checker answers
`CheckUnmodeled` to the kernel's real 0 and to the -EFAULT no `put_user`
could have produced alike. -/

/-- `gettimeofday(NULL, NULL)` with sixteen writable bytes at 4096 that the
call never touches. -/
def null_tv_input : SyscallInput :=
  SyscallInput.mkInput 169 [0, 0, 0, 0, 0, 0] (fun _ => none) wmem_ts

/-- The kernel's real answer on a NULL `tv`, 0 with nothing written:
declined, not admitted and not rejected.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem null_tv_zero_declines :
    check_gettimeofday null_tv_input 0 0 (mkEffect 0 [] []) demo_model = CheckUnmodeled := by
  rfl

/-- -EFAULT on a NULL `tv`, which no `put_user` runs to produce: declined
all the same, because the arm does not decide the call.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem null_tv_efault_declines :
    check_gettimeofday null_tv_input 0 0 (mkEffect (errno_ret EFAULT) [] []) demo_model
    = CheckUnmodeled := by
  rfl

/-- The NULL-`tv` gate on its own.  Over `wmem_ts` a NULL `tv` is also an
UNMAPPED `tv`, so the two pins above hold with the `w_is0 tv` gate deleted:
the walk fails and the unmapped arm declines in its place.  Here the
memory is wholly writable, address 0 included, and the effect is the
delivered shape at 0: a checker without the gate copies sixteen bytes,
matches the write and answers `CheckOk`.  The kernel skips the `tv` block
at :143 and writes nothing, so the arm's decline is the only right answer.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem null_tv_open_memory_declines :
    check_gettimeofday (gettimeofday_at 0) 0 0 (mkEffect 0 [(0, tv_ceiling_minus)] [])
      demo_model = CheckUnmodeled := by
  rfl

/-! ## The delivered reading

On a wholly writable `tv` and a NULL `tz` the kernel stores `tv_sec` and
`tv_nsec / 1000` with two `put_user`s (kernel/time/time.c:147-148, v6.18.46)
and returns 0 (:155).  The checker fixes the SHAPE the spec fixes: a
return of 0, exactly one write of sixteen bytes at `tv` that
`timeval_ok_b` admits, the model untouched, no event.  The two
`KTIME_SEC_MAX` boundaries are Rocq's two Examples; the rest are the
lies a kernel could tell about the shape, each refused on its own. -/

/-- Rocq's `gettimeofday_reading_below_ceiling_admissible`, at the checker:
tv_sec = KTIME_SEC_MAX - 1 with tv_usec = 999999 is admitted, the model
handed back unchanged and no event emitted.
kernel: kernel/time/time.c:gettimeofday; include/linux/time64.h:timespec64_valid_settod@v6.18.46 -/
theorem reading_below_ceiling_admitted :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (mkEffect 0 [(4096, tv_ceiling_minus)] []) demo_model = CheckOk demo_model [] := by
  rfl

/-- The same reading with the pointers read out of the fixture by
`in_arg`, slot 0 for `tv` and slot 1 for `tz`, the order of
`SYSCALL_DEFINE2(gettimeofday, struct __kernel_old_timeval __user *, tv,
struct timezone __user *, tz)`.  What this pins is that the fixture's
slots hold what the pins above assume; the ARM's reading of its
arguments is `ca_check_arm_gettimeofday`, the `arm_unfold` lemma in
`Checks/Arms/Kernel/Time/Time.lean`, and the section at the end of this
file pins it over the real table.  A `ca_check` with the pointers swapped typechecks, but
its soundness field becomes an obligation `check_gettimeofday_sound_ok`
does not discharge, because the spec arm's order is already fixed on the
base — `Sys/Registry/Kernel/Time/Time.lean`'s `gettimeofday_arm` applies
`gettimeofday_spec (in_arg i 0) (in_arg i 1)` — so a swap on one side
cannot close and a swap on both sides would have to rewrite that base
registry line.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem dispatch_shape :
    check_gettimeofday (gettimeofday_input 0) (in_arg (gettimeofday_input 0) 0)
      (in_arg (gettimeofday_input 0) 1) (mkEffect 0 [(4096, tv_ceiling_minus)] []) demo_model
    = CheckOk demo_model [] := by
  rfl

/-- Rocq's `gettimeofday_reading_at_ceiling_rejected`: one second later,
tv_sec = KTIME_SEC_MAX, is refused — no setter of the wall clock passes
`timespec64_valid_settod` (include/linux/time64.h:118-126, v6.18.46) at or
above `TIME_SETTOD_SEC_MAX`, thirty years below it.  One writer sits
behind that argument rather than inside it: `__timekeeping_inject_sleeptime`
(kernel/time/timekeeping.c) validates only its delta and adds it to
`xtime_sec` unchecked, so the ceiling is a premise on uptime since the
last set, not a kernel certainty, and a reading above it is the false
rejection `linux-process-semantics@ff0313ba4f:bugs/gettimeofday-tv-sec-ceiling-behind-one-writer.md` records.
The decision is Rocq's; this pin fixes that the checker makes it.
kernel: kernel/time/time.c:gettimeofday; include/linux/time64.h:timespec64_valid_settod@v6.18.46 -/
theorem reading_at_ceiling_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (mkEffect 0 [(4096, tv_at_ceiling)] []) demo_model = CheckReject := by
  rfl

/-- tv_usec = 1000000 is refused: the kernel's `tv_nsec / 1000` (:148) of a
`tv_nsec` below `NSEC_PER_SEC` never reaches it, and the reading's
`tv_nsec` is below it because `ktime_get_real_ts64`
(kernel/time/timekeeping.c:809-810, v6.18.46) zeroes the field and folds
the nanoseconds in through the normaliser, `timespec64_add_ns` of
include/linux/time64.h.
kernel: kernel/time/time.c:gettimeofday; include/linux/time64.h:timespec64_add_ns; kernel/time/timekeeping.c:ktime_get_real_ts64@v6.18.46 -/
theorem usec_carry_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (mkEffect 0 [(4096, tv_usec_carry)] []) demo_model = CheckReject := by
  rfl

/-- Eight bytes only — `tv_sec` without `tv_usec` — is refused: both
`put_user`s ran (:147-148) or the call was not 0.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem short_write_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (mkEffect 0 [(4096, List.replicate 8 0)] []) demo_model = CheckReject := by
  rfl

/-- Seventeen bytes is refused: `struct __kernel_old_timeval` is two
`__kernel_long_t`s (include/uapi/linux/time_types.h:25-28, v6.18.46) and
nothing follows them.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem long_write_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (mkEffect 0 [(4096, List.replicate 17 0)] []) demo_model = CheckReject := by
  rfl

/-- A well-formed reading beside a non-zero return is refused: the only
return on the delivered path is the literal 0 of :155.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem nonzero_return_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (mkEffect 1 [(4096, tv_ceiling_minus)] []) demo_model = CheckReject := by
  rfl

/-- The reading written eight bytes past `tv` is refused: the stores go to
`&tv->tv_sec` and `&tv->tv_usec` (:147-148), nowhere else.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem misplaced_write_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (mkEffect 0 [(4104, tv_ceiling_minus)] []) demo_model = CheckReject := by
  rfl

/-- The same two lies told only ABOVE BIT 31: a return of `2^32` beside a
well-formed reading, and the reading written at `tv + 2^32`.  The return
is the 64-bit `long` of `SYSCALL_DEFINE2` (:140), the literal 0 of :155 in
every bit, and the stores of :147-148 go through the whole pointer `tv`.
`nonzero_return_rejected` and `misplaced_write_rejected` offer values that
differ from the truth below bit 32, so a checker comparing either word
through its low half survives both of them; these differ above it only.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem high_bits_of_return_and_address_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
        (mkEffect (Z_to_bv 64 (2 ^ 32)) [(4096, tv_ceiling_minus)] []) demo_model
      = CheckReject
    ∧ check_gettimeofday (gettimeofday_input 0) 4096 0
        (mkEffect 0 [(Z_to_bv 64 (4096 + 2 ^ 32), tv_ceiling_minus)] []) demo_model
      = CheckReject := by
  exact ⟨rfl, rfl⟩

/-- A `tv_sec` with bit 63 set — the byte image of a negative
`__kernel_long_t` — is refused, and so is such a `tv_usec`.  Every setter
that decides the wall clock passes `timespec64_valid_settod`, whose
`timespec64_valid` refuses `tv_sec < 0` (include/linux/time64.h:100,
v6.18.46) before the ceiling compare at :123; the one writer behind that
argument, `__timekeeping_inject_sleeptime`, holds its delta to
`timespec64_valid_strict`, whose `timespec64_valid` refuses a negative
delta at the same line, so a non-negative add keeps `xtime_sec`
non-negative where it could not keep it under the ceiling; and
`ktime_get_real_ts64` copies `xtime_sec` with no clamp
(kernel/time/timekeeping.c:804); its `tv_nsec / 1000` (:148) of a
`tv_nsec` below a second is at most 999999.  The model decodes both fields
UNSIGNED, so a set sign bit is a value past the ceiling and past a second;
a decoder that read them signed would take -1 for a second before the
epoch, and without these two conjuncts nothing here would notice.
kernel: kernel/time/time.c:gettimeofday; include/linux/time64.h:timespec64_valid_settod; kernel/time/timekeeping.c:ktime_get_real_ts64@v6.18.46 -/
theorem sign_bit_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
        (mkEffect 0 [(4096, List.replicate 8 255 ++ List.replicate 8 0)] []) demo_model
      = CheckReject
    ∧ check_gettimeofday (gettimeofday_input 0) 4096 0
        (mkEffect 0 [(4096, List.replicate 8 0 ++ List.replicate 8 255)] []) demo_model
      = CheckReject := by
  exact ⟨rfl, rfl⟩

/-- The checker reads its `tv` and `tz` PARAMETERS, not the input's
argument slots: with slot 0 NULL in the fixture and 4096 passed as `tv`,
the reading at 4096 is admitted.  Every other fixture here passes the
slots' own values, so this is the one pin a checker reading `in_arg i 0`
in place of `tv` would fail; coupling the two is the arm's job, which
`ca_check_arm_gettimeofday` in `Checks/Arms/Kernel/Time/Time.lean`
states, and `checked_table_arms` ties to
`Sys/Registry/Kernel/Time/Time.lean`'s `gettimeofday_arm`.
model: `check_gettimeofday` with the pointer parameters decoupled from the slots -/
theorem parameters_not_slots :
    check_gettimeofday null_tv_input 4096 0
      (mkEffect 0 [(4096, tv_ceiling_minus)] []) demo_model = CheckOk demo_model [] := by
  rfl

/-- Two writes, each a well-formed reading, are refused: one struct is
written.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem second_write_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (mkEffect 0 [(4096, tv_ceiling_minus), (4096, tv_ceiling_minus)] []) demo_model
    = CheckReject := by
  rfl

/-- THE ERRNO THE KERNEL COULD NEVER RETURN HERE: -EFAULT on a `tv` whose
sixteen bytes are all writable.  Both `access_ok` tests (arch/riscv/include/asm/uaccess.h:412,
v6.18.46) pass and both stores land, so :149 is not reached; the checker
rejects it.  The site that refuses this shape is the fallback on the write
list — nothing was written — which `zero_without_write_rejected` reaches
with a 0 as well; the return word itself is compared only once a
well-formed write is present, and `efault_beside_reading_rejected` is the
pin on that compare.  Together the two are what separate the checker from
the spec — a spec and checker both moved to accept -EFAULT here would
still agree with each other.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem writable_tv_efault_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject := by
  rfl

/-- A 0 with nothing written is refused on a writable `tv`: the two
stores are not optional.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem zero_without_write_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0 (mkEffect 0 [] []) demo_model
    = CheckReject := by
  rfl

/-- A well-formed reading beside a zeroed range is refused: the kernel
stores, it does not clear.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem zeroing_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (mkEffect 0 [(4096, tv_ceiling_minus)] [(8192, 16)]) demo_model = CheckReject := by
  rfl

/-- A well-formed reading beside an unmap is refused for the same reason.
`mkEffect` fixes the last three effect lists empty and only `eff_zeros`
is pinned above, so this pin and the two after it offer the shapes a
checker matching `mkEffectU r [(a, bs)] [] _ _ _` would accept.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem unmap_beside_reading_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (SyscallEffect.mkEffectU 0 [(4096, tv_ceiling_minus)] [] [(8192, 4096)] [] [])
      demo_model = CheckReject := by
  rfl

/-- A well-formed reading beside a memory copy is refused.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem copy_beside_reading_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (SyscallEffect.mkEffectU 0 [(4096, tv_ceiling_minus)] [] []
        [MemCopy.mkCopy 8192 12288 16] [])
      demo_model = CheckReject := by
  rfl

/-- A well-formed reading beside a copy-in is refused: `gettimeofday`
reads nothing from user memory.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem copyin_beside_reading_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (SyscallEffect.mkEffectU 0 [(4096, tv_ceiling_minus)] [] [] [] [(4096, 16)])
      demo_model = CheckReject := by
  rfl

/-- -EFAULT BESIDE THE WRITE on a wholly writable `tv`: a checker letting
the delivered arm return either 0 or -EFAULT survives
`nonzero_return_rejected`, which offers 1, and `writable_tv_efault_rejected`,
which offers the errno with nothing written.  At a NULL `tz` the only
-EFAULT is :149's, reached only when a `put_user` failed, and a store that
failed left at least one of its eight bytes unwritten, so -EFAULT never
comes with all sixteen bytes in place; the kernel that stored both fields
returns the literal 0 (:155).  (With a non-NULL `tz` the `tz` copy can
fail after both stores landed, :153, which is one more reason that arm
declines.)
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem efault_beside_reading_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (mkEffect (errno_ret EFAULT) [(4096, tv_ceiling_minus)] []) demo_model = CheckReject := by
  rfl

/-- …and -EINVAL beside the write closes the same door for the setter's
errno: `do_sys_settimeofday64` (kernel/time/time.c:169-197, v6.18.46) is
the function that returns -EINVAL for an invalid `tv` (:175) or an
out-of-range timezone (:184), and `gettimeofday` never calls it, so a
checker admitting the reading under either 0 or -EINVAL admits a return
the getter has no path to.
kernel: kernel/time/time.c:gettimeofday,do_sys_settimeofday64@v6.18.46 -/
theorem einval_beside_reading_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (mkEffect (errno_ret EINVAL) [(4096, tv_ceiling_minus)] []) demo_model = CheckReject := by
  rfl

/-! ## The model is never moved

`gettimeofday` reads the wall clock and writes user memory; the monotonic
clock the model carries as `m_clock` is a different quantity, and nothing
in the call touches the model.  So the checker's only `CheckOk` carries
the input model and no event, and a delivered reading beside a moved
model or an emitted event is refused. -/

/-- UNIVERSALLY QUANTIFIED, the twin of Rocq's second checker lemma,
`gettimeofday_never_moves_the_model`: a
`CheckOk` hands back the model it was given and no event, whatever the
arguments.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem never_moves_the_model (i : SyscallInput) (tv tz : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_gettimeofday i tv tz eff m = CheckOk m' evs) : m' = m ∧ evs = [] := by
  obtain ⟨hm, hevs, -⟩ := check_gettimeofday_ok_inv i tv tz eff m m' evs h
  exact ⟨hm, hevs⟩

/-- Concretely: the delivered reading is not a `CheckOk` beside a moved
monotonic clock.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem moved_clock_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (mkEffect 0 [(4096, tv_ceiling_minus)] []) demo_model
    ≠ CheckOk (with_clock 5 demo_model) [] := by
  intro h
  obtain ⟨hm, -⟩ := never_moves_the_model _ _ _ _ _ _ _ h
  have hclock := congrArg m_clock hm
  exact absurd hclock (by decide)

/-- …nor beside an event: the sixteen bytes go to user memory, not to a
channel.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem event_rejected :
    check_gettimeofday (gettimeofday_input 0) 4096 0
      (mkEffect 0 [(4096, tv_ceiling_minus)] []) demo_model
    ≠ CheckOk demo_model [event.WriteEv 1 0] := by
  intro h
  obtain ⟨-, hevs⟩ := never_moves_the_model _ _ _ _ _ _ _ h
  cases hevs

/-! ## A destination that is not wholly writable

Each `put_user` (kernel/time/time.c:147-148, v6.18.46) tests `access_ok`
over its own eight bytes (arch/riscv/include/asm/uaccess.h:412) and then
stores; a store into an unmapped page faults and the call is -EFAULT
(:149).  With nothing mapped at `tv` the first store faults and nothing
is written; with `tv_sec`'s page mapped and `tv_usec`'s not, the second
store faults and `tv_sec` is written (for the eight-byte-aligned `tv` of
these fixtures, whose stores do not straddle a page).  Each is a definite shape, but the
model does not distinguish them: `copy_bytes_map` says only that the
sixteen-byte walk failed, not where, so the checker cannot tell the
unmapped destination from the torn one and the arm declines both (the
spec pins' header in `Checks/Cases/Kernel/Time/Time.lean` carries the
argument).  The checker answers `CheckUnmodeled` to every effect there,
the kernel's real one included. -/

/-- Nothing mapped at 4096: the first `put_user` faults and the call is
-EFAULT with nothing written.  Declined, not admitted, because the checker
cannot tell this destination from a torn one.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem unmapped_tv_efault_declines :
    check_gettimeofday (SyscallInput.mkInput 169 [4096, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
      4096 0 (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled := by
  rfl

/-- The first eight bytes mapped and the second eight not: -EFAULT with
`tv_sec` written is what Linux does, and the arm declines it rather than
spell a half-written struct.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem torn_mapping_half_write_declines :
    check_gettimeofday (SyscallInput.mkInput 169 [4096, 0, 0, 0, 0, 0] (fun _ => none) wmem_ts_half)
      4096 0 (mkEffect (errno_ret EFAULT) [(4096, List.replicate 8 0)] []) demo_model
    = CheckUnmodeled := by
  rfl

/-! ## The top of the address space: the twins of Rocq's `check_syscall` Examples

`__access_ok` (include/asm-generic/access_ok.h:31-41, v6.18.46) is
`(size <= limit) && (addr <= (limit - size))` (:40), which refuses a
range that would wrap and one that ends past `TASK_SIZE`; `copy_bytes_map`
asks it at width 16 before the walk, and the spec asks it again at width
8 to tell the first `put_user`'s own refusal from the torn band.  Rocq
states these at the dispatcher; here each is the checker's answer on the
same input, model and effect. -/

/-- Rocq's `gettimeofday_wrapping_tv_is_efault`: `tv = 2^64 - 8`, a memory
mapping exactly the sixteen bytes the wrapped walk would read.  The first
`put_user`'s `access_ok` refuses the range, nothing is stored, the call is
-EFAULT — admitted — and the reading the walk would have delivered at
`2^64 - 8` and, wrapped, at 0 is refused.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem wrapping_tv_is_efault :
    check_gettimeofday
        (SyscallInput.mkInput 169 [gettimeofday_wrap_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_wrap_mem)
        gettimeofday_wrap_tv 0 (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_gettimeofday
        (SyscallInput.mkInput 169 [gettimeofday_wrap_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_wrap_mem)
        gettimeofday_wrap_tv 0 (mkEffect 0 [(gettimeofday_wrap_tv, tv_ceiling_minus)] [])
        demo_model
      = CheckReject := by
  exact ⟨rfl, rfl⟩

/-- On the -EFAULT arm the errno is the WHOLE effect: a write beside it,
a different errno, or a 0 are each refused.  -EINVAL is the SETTER's
answer — `do_sys_settimeofday64` (kernel/time/time.c:169-197, v6.18.46)
returns it for a `tv` that fails `timespec64_valid_settod` (:175) and
for a timezone outside ±15 hours (:184) — and `gettimeofday`'s body has
no such return: its only errno is -EFAULT, at :149 for a failed `tv`
store and at :153 for a failed `tz` copy.
kernel: kernel/time/time.c:gettimeofday,do_sys_settimeofday64; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem wrapping_tv_other_answers_rejected :
    check_gettimeofday
        (SyscallInput.mkInput 169 [gettimeofday_wrap_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_wrap_mem)
        gettimeofday_wrap_tv 0
        (mkEffect (errno_ret EFAULT) [(gettimeofday_wrap_tv, List.replicate 8 0)] []) demo_model
      = CheckReject
    ∧ check_gettimeofday
        (SyscallInput.mkInput 169 [gettimeofday_wrap_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_wrap_mem)
        gettimeofday_wrap_tv 0 (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckReject
    ∧ check_gettimeofday
        (SyscallInput.mkInput 169 [gettimeofday_wrap_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_wrap_mem)
        gettimeofday_wrap_tv 0 (mkEffect 0 [] []) demo_model
      = CheckReject := by
  exact ⟨rfl, rfl, rfl⟩

/-- Rocq's `gettimeofday_past_task_size_is_efault`: `tv = 2^63`, sixteen
bytes mapped there, no wrap — and still refused by `__access_ok`'s second
conjunct, since `2^63` is past `TASK_SIZE`.  -EFAULT admitted, the
reading refused.
kernel: kernel/time/time.c:gettimeofday; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem past_task_size_is_efault :
    check_gettimeofday
        (SyscallInput.mkInput 169 [gettimeofday_high_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_high_mem)
        gettimeofday_high_tv 0 (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_gettimeofday
        (SyscallInput.mkInput 169 [gettimeofday_high_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_high_mem)
        gettimeofday_high_tv 0 (mkEffect 0 [(gettimeofday_high_tv, tv_ceiling_minus)] [])
        demo_model
      = CheckReject := by
  exact ⟨rfl, rfl⟩

/-- Rocq's `gettimeofday_last_admitted_tv_is_delivered`: `TASK_SIZE - 16`
is the last destination both stores fit under, and the reading is
delivered there.  The control that keeps the refusals honest: a checker
refusing every `tv` near the top would fail it.
kernel: kernel/time/time.c:gettimeofday; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem last_admitted_tv_is_delivered :
    check_gettimeofday (gettimeofday_at (task_size_minus 16)) (task_size_minus 16) 0
      (mkEffect 0 [(task_size_minus 16, tv_ceiling_minus)] []) demo_model
    = CheckOk demo_model [] := by
  rfl

/-- Rocq's `gettimeofday_torn_band_declines`: at `TASK_SIZE - 15` and
`TASK_SIZE - 8` the first store's own 8-byte test passes and the second's
does not (`widths_at_the_edges`), so `tv_sec` is stored and the call is
-EFAULT — the half-written struct no single effect spells.  The checker
declines the -EFAULT rather than accept or reject it.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem torn_band_declines :
    check_gettimeofday (gettimeofday_at (task_size_minus 15)) (task_size_minus 15) 0
        (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled
    ∧ check_gettimeofday (gettimeofday_at (task_size_minus 8)) (task_size_minus 8) 0
        (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled := by
  exact ⟨rfl, rfl⟩

/-- …and the torn band declines a delivered reading too: a decline is not
a rejection, so the reading Linux never delivers there is not `CheckReject`
either.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem torn_band_delivery_declines :
    check_gettimeofday (gettimeofday_at (task_size_minus 15)) (task_size_minus 15) 0
      (mkEffect 0 [(task_size_minus 15, tv_ceiling_minus)] []) demo_model = CheckUnmodeled := by
  rfl

/-- Rocq's `gettimeofday_first_store_refused_is_efault`: at `TASK_SIZE - 7`
the FIRST store's test fails, nothing is written, -EFAULT is the answer
and a delivered reading is not.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem first_store_refused_is_efault :
    check_gettimeofday (gettimeofday_at (task_size_minus 7)) (task_size_minus 7) 0
        (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckOk demo_model []
    ∧ check_gettimeofday (gettimeofday_at (task_size_minus 7)) (task_size_minus 7) 0
        (mkEffect 0 [(task_size_minus 7, tv_ceiling_minus)] []) demo_model = CheckReject := by
  exact ⟨rfl, rfl⟩

/-! ## The witness, evaluated

`gettimeofday_witness_ok` proves the witness is an outcome the spec admits
on every input and model.  These read off WHICH outcome it is on the
fixtures above, so a reader can see the receptiveness obligation's
content rather than its type: the epoch reading where a reading is
delivered, -EFAULT where the first store's own range test refuses `tv`,
and a decline exactly where the checker declines.  Each read-off closes by
`rfl` on the fixtures the checker pins use, so the two halves of this file
cannot drift apart on what a destination is; the closing equation on
`timeval_zero` itself is `decide`. -/

/-- On a wholly writable `tv` the witness offers the epoch: return 0, one
sixteen-byte write of `timeval_zero` at `tv`, the model untouched, no
event — the shape `reading_below_ceiling_admitted` accepts, with the
earliest instant `timeval_ok_b` admits in place of the latest.
model: `gettimeofday_witness` on the writable fixture at a NULL `tz` -/
theorem witness_offers_the_epoch :
    gettimeofday_witness 4096 0 (gettimeofday_input 0) demo_model
      = Ok (mkEffect 0 [(4096, timeval_zero)] []) demo_model [] := by
  rfl

/-- Where the first `put_user`'s own eight-byte test refuses `tv` — the
wrapping destination and `TASK_SIZE - 7` — the witness offers -EFAULT
with nothing written and the model untouched: the outcome
`wrapping_tv_is_efault` and `first_store_refused_is_efault` accept.
model: `gettimeofday_witness` on the wrap fixture and at `TASK_SIZE - 7` -/
theorem witness_offers_efault_where_the_first_store_is_refused :
    gettimeofday_witness gettimeofday_wrap_tv 0
        (SyscallInput.mkInput 169 [gettimeofday_wrap_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_wrap_mem)
        demo_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) demo_model []
    ∧ gettimeofday_witness (task_size_minus 7) 0 (gettimeofday_at (task_size_minus 7)) demo_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) demo_model [] := by
  exact ⟨rfl, rfl⟩

/-- The witness declines exactly where the checker does: a non-NULL `tz`,
a NULL `tv`, and the torn band at `TASK_SIZE - 15`, where the sixteen-byte
walk fails and the first store's test passes.
model: `gettimeofday_witness` on the three declining fixtures -/
theorem witness_declines_where_the_checker_declines :
    gettimeofday_witness 4096 8192 (gettimeofday_input 8192) demo_model = Unmodeled
    ∧ gettimeofday_witness 0 0 null_tv_input demo_model = Unmodeled
    ∧ gettimeofday_witness (task_size_minus 15) 0 (gettimeofday_at (task_size_minus 15)) demo_model
      = Unmodeled := by
  exact ⟨rfl, rfl, rfl⟩

/-- The witness's gates read from the side the fixtures above do not
reach.  A NULL `tv` over OPEN memory — every byte mapped, address 0
included — is `Unmodeled`: a witness that dropped its `tv` gate would
offer the epoch written at 0 there, where `null_tv_input` over `wmem_ts`
cannot tell the two apart (its sixteen-byte walk from 0 fails and the
first store's own test passes, so the un-gated witness declines there
too).  And at `TASK_SIZE - 8`, the last destination whose first store
passes and whose sixteen-byte walk fails, the witness declines rather
than offer -EFAULT, which pins the first store's width at 8 from above as
`TASK_SIZE - 7` pins it from below: a test any wider refuses that
destination.  `torn_band_declines` is the checker's half of the same fact.
model: `gettimeofday_witness` at a NULL `tv` over open memory and at `TASK_SIZE - 8` -/
theorem witness_gates_read_from_the_open_side :
    gettimeofday_witness 0 0 (gettimeofday_at 0) demo_model = Unmodeled
    ∧ gettimeofday_witness (task_size_minus 8) 0 (gettimeofday_at (task_size_minus 8)) demo_model
      = Unmodeled := by
  exact ⟨rfl, rfl⟩

/-- `timeval_zero` IS the epoch, not merely an admitted reading: sixteen
zero bytes, so `tv_sec = 0` and `tv_usec = 0`.  `timeval_zero_ok` fixes
only that `timeval_ok_b` admits it, which any instant below the ceiling
would satisfy; this is what makes "the epoch" in the docstrings around it
a checked claim rather than a name.
model: `timeval_zero` unfolded -/
theorem timeval_zero_is_the_epoch : timeval_zero = List.replicate 16 0 := by
  decide

/-- And the checker accepts what the witness offers, on the fixture where
a reading is delivered: the concrete face of `gettimeofday_witness_ok`.
The kernel claim is `reading_below_ceiling_admitted`'s — both stores
succeeded, the literal 0 is returned (:155) — restated beside the witness
that relies on it, with the epoch as the reading.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem checker_accepts_the_witness :
    check_gettimeofday (gettimeofday_input 0) 4096 0 (mkEffect 0 [(4096, timeval_zero)] [])
        demo_model
      = CheckOk demo_model []
    ∧ gettimeofday_witness 4096 0 (gettimeofday_input 0) demo_model
      = Ok (mkEffect 0 [(4096, timeval_zero)] []) demo_model [] := by
  exact ⟨rfl, rfl⟩

section V_Kernel_Time_Time

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

variable (m : Model)

/-! ## V-Kernel-Time-Time — `gettimeofday` over the real table

WHAT IS TWINNED HERE.  The header's "HOW THE CALL IS STATED" says why
the sections above address the checker directly: `checked_table`
carried no row for 169 when they were written.  This section was added
with the registration.  Each of the seven `Example`s of
`theories/LinuxProcessSem/Checks/Cases/Kernel/Time/Time.v` stated through
`check_syscall` is restated here through the Lean `check_syscall`, over
`checked_table` itself, on the Rocq input, under its Rocq name with
`_over_the_real_table` after it, the convention K6b set for the pins at
which the real table first answers a call.  Rocq fixes `clock_model 0`;
these hold at every model, since neither the lookup, the arm nor the
checker reads one.

WHY HERE AND NOT IN `Checks/Cases/Kernel/Time/Time.lean`.  That file is
the spec's pin file, and the spec's mutation twin: a mutant of
`Sys/Kernel/Time/Time.lean` is compiled against it, and the checker
entering its import closure would record a gate-changing spec mutant as
a checker that fails to build instead of as a kill by a spec pin.  The
eventfd2 and mmap registrations made the same choice for the same reason.

WHAT A PIN HERE ADDS to its checker-level twin above is the ARM's claim:
the lookup at 169 finds `arm_gettimeofday` rather than the dispatcher's
own decline, and the arm hands the checker register `a0` as `tv` and `a1`
as `tz`, whole.  Every restatement below whose answer is `CheckOk` or
`CheckReject` fails under a swap, six of the seven, because each puts a
non-zero pointer in `a0`: swapped, that pointer would be `tz`, and the
call a decline.  `gettimeofday_torn_band_declines_over_the_real_table`,
which already expects a decline, is the one that survives it.  The
checker-level twins above pass `tv` and `tz` to `check_gettimeofday`
directly and cannot see a swap.  The last three pins below read the
registers from the sides the Rocq Examples do not.

POLARITY: the evidence line is `kernel:` on every pin about the kernel's
answer, `CheckOk`, `CheckReject` and `CheckUnmodeled` alike, and `model:`
on the pin about the table's own contents, the lookup.  The witness pin
is `kernel:` where the sections above label their witness read-offs
`model:`, because `check_lean_pin_evidence.py` refuses `model:` on a
statement that names `syscall_spec_witness`; that is a departure from
those sections, not their polarity. -/

/-- The lookup the dispatcher performs at 169, computed once.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_gettimeofday :
    lookup_ca checked_table 169 = some arm_gettimeofday :=
  lookup_ca_checked_table_gettimeofday

/-! ### The seven Rocq examples, through `check_syscall` -/

/-- `gettimeofday_reading_below_ceiling_admissible` over the real table:
both stores succeed (kernel/time/time.c:147-148, Linux v6.18.46) and the
literal 0 is returned (:155), with a reading one second below
`KTIME_SEC_MAX`; the model is handed back and no event emitted.
kernel: kernel/time/time.c:gettimeofday; include/linux/time64.h:timespec64_valid_settod@v6.18.46 -/
theorem gettimeofday_reading_below_ceiling_admissible_over_the_real_table :
    check_syscall (gettimeofday_input 0) (mkEffect 0 [(4096, tv_ceiling_minus)] []) m
      = CheckOk m [] := rfl

/-- `gettimeofday_reading_at_ceiling_rejected` over the real table: the
same reading one second later, at `KTIME_SEC_MAX`, is refused; no setter
of the wall clock passes `timespec64_valid_settod`
(include/linux/time64.h:118-126, Linux v6.18.46) there, and
`reading_at_ceiling_rejected` above carries the one writer behind that
argument.
kernel: kernel/time/time.c:gettimeofday; include/linux/time64.h:timespec64_valid_settod@v6.18.46 -/
theorem gettimeofday_reading_at_ceiling_rejected_over_the_real_table :
    check_syscall (gettimeofday_input 0) (mkEffect 0 [(4096, tv_at_ceiling)] []) m
      = CheckReject := rfl

/-- `gettimeofday_wrapping_tv_is_efault` over the real table: at
`tv = 2^64 - 8` the first `put_user`'s `access_ok` refuses the range, so
nothing is stored and the call is -EFAULT (kernel/time/time.c:149, Linux
v6.18.46); the reading the wrapped walk would have delivered is refused.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem gettimeofday_wrapping_tv_is_efault_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 169 [gettimeofday_wrap_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_wrap_mem)
        (mkEffect (errno_ret EFAULT) [] []) m
      = CheckOk m []
    ∧ check_syscall
        (SyscallInput.mkInput 169 [gettimeofday_wrap_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_wrap_mem)
        (mkEffect 0 [(gettimeofday_wrap_tv, tv_ceiling_minus)] []) m
      = CheckReject := ⟨rfl, rfl⟩

/-- `gettimeofday_past_task_size_is_efault` over the real table: `tv =
2^63` does not wrap, and `__access_ok`'s `addr <= limit - size`
(include/asm-generic/access_ok.h:40, Linux v6.18.46) refuses it anyway;
-EFAULT is admitted and the reading refused.
kernel: kernel/time/time.c:gettimeofday; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem gettimeofday_past_task_size_is_efault_over_the_real_table :
    check_syscall
        (SyscallInput.mkInput 169 [gettimeofday_high_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_high_mem)
        (mkEffect (errno_ret EFAULT) [] []) m
      = CheckOk m []
    ∧ check_syscall
        (SyscallInput.mkInput 169 [gettimeofday_high_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_high_mem)
        (mkEffect 0 [(gettimeofday_high_tv, tv_ceiling_minus)] []) m
      = CheckReject := ⟨rfl, rfl⟩

/-- `gettimeofday_last_admitted_tv_is_delivered` over the real table:
`TASK_SIZE - 16` is the last destination both stores fit under.
kernel: kernel/time/time.c:gettimeofday; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem gettimeofday_last_admitted_tv_is_delivered_over_the_real_table :
    check_syscall (gettimeofday_at (task_size_minus 16))
        (mkEffect 0 [(task_size_minus 16, tv_ceiling_minus)] []) m
      = CheckOk m [] := rfl

/-- `gettimeofday_torn_band_declines` over the real table: at
`TASK_SIZE - 15` and `TASK_SIZE - 8` the first store's own 8-byte test
passes and the second's does not, so `tv_sec` is stored before the
-EFAULT of kernel/time/time.c:149 (Linux v6.18.46), a half-written struct
no single effect spells; the arm declines.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem gettimeofday_torn_band_declines_over_the_real_table :
    check_syscall (gettimeofday_at (task_size_minus 15)) (mkEffect (errno_ret EFAULT) [] []) m
      = CheckUnmodeled
    ∧ check_syscall (gettimeofday_at (task_size_minus 8)) (mkEffect (errno_ret EFAULT) [] []) m
      = CheckUnmodeled := ⟨rfl, rfl⟩

/-- `gettimeofday_first_store_refused_is_efault` over the real table: at
`TASK_SIZE - 7` the first store's test fails, nothing is written, and
-EFAULT is the answer; a delivered reading is refused.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem gettimeofday_first_store_refused_is_efault_over_the_real_table :
    check_syscall (gettimeofday_at (task_size_minus 7)) (mkEffect (errno_ret EFAULT) [] []) m
      = CheckOk m []
    ∧ check_syscall (gettimeofday_at (task_size_minus 7))
        (mkEffect 0 [(task_size_minus 7, tv_ceiling_minus)] []) m
      = CheckReject := ⟨rfl, rfl⟩

/-! ### The registers, read from the other side

The Rocq Examples put the pointer in `a0` and zero in `a1`, so an arm
that read `a1` as `tv` would decline them all rather than answer, and an
arm that ignored `a1` would pass them.  These put a value where the
Examples put none. -/

/-- A non-NULL `a1` is the timezone pointer: the kernel copies `sys_tz`
out through it (kernel/time/time.c:151-153, Linux v6.18.46), which the
model has nowhere to carry, so the arm declines the reading it would
otherwise accept.  An arm that ignored `a1` would accept it.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem a1_is_the_timezone_over_the_real_table :
    check_syscall (gettimeofday_input 8192) (mkEffect 0 [(4096, tv_ceiling_minus)] []) m
      = CheckUnmodeled := rfl

/-- `a1` is a POINTER, read whole: bit 32 alone makes it non-NULL, and
the call declines; an arm that narrowed `a1` to an `int` would see 0 and
accept.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem a1_is_not_narrowed_over_the_real_table :
    check_syscall (gettimeofday_input 4294967296) (mkEffect 0 [(4096, tv_ceiling_minus)] []) m
      = CheckUnmodeled := rfl

/-- The witness the table hands `receptive` at 169 reads the same two
registers: the epoch at 4096 where `a1` is NULL, a decline where it is
not.  The first conjunct has the shape of the accepted answer of
`gettimeofday_reading_below_ceiling_admissible_over_the_real_table`
(both stores succeed, :147-148, and 0 is returned, :155), at the epoch
rather than one second below the ceiling; the second is
the decline `a1_is_the_timezone_over_the_real_table`
argues, since a non-NULL `tz` has `sys_tz` copied out through it
(kernel/time/time.c:151-153, Linux v6.18.46) and the model has nowhere
to carry it.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem gettimeofday_witnesses_over_the_real_table :
    syscall_spec_witness (gettimeofday_input 0) m
      = Ok (mkEffect 0 [(4096, timeval_zero)] []) m []
    ∧ syscall_spec_witness (gettimeofday_input 8192) m = Unmodeled := ⟨rfl, rfl⟩

end V_Kernel_Time_Time

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Time.Time
