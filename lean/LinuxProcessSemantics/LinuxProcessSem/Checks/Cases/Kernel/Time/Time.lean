import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Kernel.Time.Time — what `gettimeofday` answers, read off against Linux

Worked examples over `Time.gettimeofday_spec` and `Time.timeval_ok_b`, the
twin of `theories/LinuxProcessSem/Checks/Cases/Kernel/Time/Time.v`.  Not
part of the trusted specification: this file is QA on the definitions,
written to be READ, and every claim in it is a claim about what the kernel
does, with the citation beside it.  Line numbers are Linux v6.18.46 (commit
1f99e9ab748f) throughout, each read there.

HOW THESE ARE STATED.  As in `Checks/Cases/Fs/Sync.lean`: a check is
stated on the relation itself, as an `iff` over EVERY outcome `o`, so one
theorem fixes what is admitted and what is refused; beside it, the concrete
lie a kernel could tell is refuted on its own.  Where the admitted set is
not finite — a delivered reading is `choose`n — the `iff` carries the
existential the spec does, in the order `sys_norm` reads it.  Every pin on
the spec is closed by `sys_norm` or `sys_refute` (`Checks/Cases/Tactic.lean`)
except two: `every_timezone_declines` and `success_never_moves_the_model`
quantify over the arguments, so their gates are opened by hand before the
normalizer reads each arm, and each says so where it occurs.  The closed
readings of the fixtures are `decide`, and the one register claim on a
number is `rfl`.

WHAT THE ROCQ FILE PINS AND WHAT IT PROBES.  Rocq's file keeps thirteen
cases — the two quantified claims, the two `KTIME_SEC_MAX` boundaries, and
the destinations at the top of the address space — and sends the rest to
`testing/syscall-check/tests/gettimeofday_spec.c`.  Every one of the
thirteen has a twin here, marked `rocq-twin:` (seventeen lines, since four
of the Rocq examples are conjunctions); the Lean tree has no replay
harness, so the probe-covered decisions are pinned here as well: the NULL
`tv` and non-NULL `tz` declines, the delivered reading's shape, the
predicate's two other boundaries, and a destination that is unmapped or
only half mapped.

TWO FIXTURES ARE ROCQ'S `PosixTimers` ONES.  `wmem_ts` and the
`clock_model` Rocq builds its input on are defined beside `clock_gettime`'s
cases there; `clock_gettime` is not ported, so `wmem_ts` is defined here
under its Rocq name and the model is `Prelude.demo_model`, which
`gettimeofday_spec` reads no field of.  When `PosixTimers` lands, its
`wmem_ts` is the one to keep.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins prove
is that this spec and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.Time

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time.Time
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The register

What `Checks/Cases/Tactic.lean` says a spec owes the `sys_simp` set: its
unfolding at low priority.  `timeval_ok_b` is a gate — decided, never
unfolded — so it is not registered.  The line lives here rather than in
`Tactic.lean`'s register so that a port PR edits no shared file. -/

attribute [sys_simp low] gettimeofday_spec.eq_1

/-! ## The fixtures

Sixteen writable bytes at 4096 and nothing else, a struct on each side of
the `KTIME_SEC_MAX` ceiling, and the memories and destinations of the
`TASK_SIZE` bands.  Each closed reading a pin needs is one fact, proved by
`decide` and registered in `sys_simp` at the default priority, ahead of the
spec's unfolding, so the `match` on `copy_bytes_map` is decided in the
first pass and the arm behind it is read. -/

/-- Sixteen writable bytes at 4096, and nothing else (Rocq's `wmem_ts`). -/
def wmem_ts : word → Option byte :=
  fun a => if 4096 ≤ bv_unsigned a ∧ bv_unsigned a < 4112 then some 0 else none

/-- The first EIGHT of them only: `tv_sec`'s page mapped, `tv_usec`'s not. -/
def wmem_ts_half : word → Option byte :=
  fun a => if 4096 ≤ bv_unsigned a ∧ bv_unsigned a < 4104 then some 0 else none

/-- `gettimeofday(4096, tz)`: sixteen writable bytes at 4096, nothing
readable, and the timezone pointer left free. -/
def gettimeofday_input (tz : word) : SyscallInput :=
  SyscallInput.mkInput 169 [4096, tz, 0, 0, 0, 0] (fun _ => none) wmem_ts

/-- tv_sec = KTIME_SEC_MAX - 1 = 9223372035, tv_usec = 999999 — the
latest wall-clock instant `timeval_ok_b` admits. -/
def tv_ceiling_minus : List byte :=
  [3, 125, 193, 37, 2, 0, 0, 0] ++ [63, 66, 15, 0, 0, 0, 0, 0]

/-- The same microsecond one second later: tv_sec = KTIME_SEC_MAX. -/
def tv_at_ceiling : List byte :=
  [4, 125, 193, 37, 2, 0, 0, 0] ++ [63, 66, 15, 0, 0, 0, 0, 0]

/-- tv_sec = 1, tv_usec = 1000000: a whole second left in the microsecond
field, which the kernel's division never produces. -/
def tv_usec_carry : List byte :=
  [1, 0, 0, 0, 0, 0, 0, 0] ++ [64, 66, 15, 0, 0, 0, 0, 0]

/-- The two bounds and the two fields, read off the fixtures: the file's
numerals are the values they say they are.
model: the fixtures' fields, decoded by `tv_sec_of` and `tv_frac_of`. -/
theorem fixtures_decode :
    tv_sec_of tv_ceiling_minus = 9223372035 ∧ tv_frac_of tv_ceiling_minus = 999999
    ∧ tv_sec_of tv_at_ceiling = 9223372036 ∧ tv_frac_of tv_at_ceiling = 999999
    ∧ tv_sec_of tv_usec_carry = 1 ∧ tv_frac_of tv_usec_carry = 1000000
    ∧ tv_ceiling_minus.length = 16 ∧ KTIME_SEC_MAX = 9223372036 := by
  decide

/-- The sixteen bytes are exactly 4096..4111, and the half fixture stops
at 4103.
model: the fixtures' zones at their edges. -/
theorem wmem_ts_zones :
    wmem_ts 4095 = none ∧ wmem_ts 4096 = some 0 ∧ wmem_ts 4111 = some 0 ∧ wmem_ts 4112 = none
    ∧ wmem_ts_half 4103 = some 0 ∧ wmem_ts_half 4104 = none := by
  decide

/-- The whole struct is writable at 4096.
model: a closed `copy_bytes_map` over the fixture, a rewrite for `sys_norm`. -/
theorem copy_ts_full : copy_bytes_map wmem_ts 4096 16 = some (List.replicate 16 0) := by decide
/-- …and not over the half fixture, nor over nothing.
model: a closed `copy_bytes_map` over the fixture, a rewrite for `sys_norm`. -/
theorem copy_ts_half : copy_bytes_map wmem_ts_half 4096 16 = none := by decide
/-- The unmapped destination.
model: a closed `copy_bytes_map` over the fixture, a rewrite for `sys_norm`. -/
theorem copy_ts_none : copy_bytes_map (fun _ => (none : Option byte)) 4096 16 = none := by decide

attribute [sys_simp] copy_ts_full copy_ts_half copy_ts_none

/-! ## `sys_tz`: a non-NULL timezone pointer declines

`SYSCALL_DEFINE2(gettimeofday, ...)` (kernel/time/time.c:140-156, v6.18.46) copies
`sys_tz` into a non-NULL `tz` (:151-153).  `sys_tz` is a file-scope
`struct timezone` with no initializer (:50), eight bytes
(include/uapi/linux/time.h:33-36, v6.18.46), and its one writer is
`do_sys_settimeofday64` (kernel/time/time.c:186, v6.18.46), which any process with
the capability can reach.  The model has nowhere to carry the value, so
the arm declines.  This is NOT a claim that the supported implementations
disagree: it is the fail-closed answer for a value the model cannot
know — `{0, 0}` on a machine whose clock is kept in UTC — and the
refutation below is what stops a future arm answering that guess.

The kernel decides `tv` BEFORE `tz` (:143-150, then :151-154); the spec
tests `tz` first.  Nothing turns on it: a non-NULL `tz` is declined
whatever `tv` would have answered, and a decline admits no outcome, so no
trace is admitted in the wrong order — the two pins after the quantified
one fix the two ways the kernel's `tv` block could have answered first. -/

/-- UNIVERSALLY QUANTIFIED, the twin of Rocq's first lemma: every non-NULL
timezone pointer declines, whatever the destination, the input or the
model.  The gate is symbolic, so the hypothesis is rewritten into it
before the normalizer reads the arm.
kernel: kernel/time/time.c:gettimeofday,do_sys_settimeofday64@v6.18.46
rocq-twin: gettimeofday_declines_every_timezone -/
theorem every_timezone_declines (tz : word) (h : w_is0 tz = false) (tv : word)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    gettimeofday_spec tv tz i m o ↔ o = Unmodeled := by
  unfold gettimeofday_spec
  rw [h]
  sys_norm

/-- One concrete timezone pointer, 8192, on a writable `tv`: declined.
kernel: kernel/time/time.c:gettimeofday,do_sys_settimeofday64@v6.18.46 -/
theorem timezone_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    gettimeofday_spec 4096 8192 i m o ↔ o = Unmodeled := by
  sys_norm

/-- The confident guess: a reading at `tv` and `{0, 0}` at `tz`, which is
what the kernel writes on a machine where nothing has set `sys_tz`.  It is
refused, because "nothing has set it" is a fact about the deployment.
kernel: kernel/time/time.c:gettimeofday,do_sys_settimeofday64@v6.18.46 -/
theorem timezone_zero_answer_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ gettimeofday_spec 4096 8192 i demo_model
        (Ok (mkEffect 0 [(4096, tv_ceiling_minus), (8192, List.replicate 8 0)] []) m' evs) := by
  sys_refute

/-- …and no errno is given through the decline either: -EFAULT, which the
`tz` copy (:152-153) answers on an unwritable `tz`, is not an answer the
arm makes for any `tz`.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem timezone_efault_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ gettimeofday_spec 4096 8192 i m (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- The kernel's order, first way: `tv` NULL and `tz` set.  The `tv` block
is skipped (:143) and the call returns 0 after the `tz` copy (:155); the
spec declines on `tz`, which admits nothing, so the 0 is not admitted
in either order.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem timezone_with_null_tv_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    gettimeofday_spec 0 8192 i m o ↔ o = Unmodeled := by
  sys_norm

/-- The kernel's order, second way: a `tv` whose first `put_user` is
refused, and `tz` set.  The kernel returns -EFAULT at :149 before `tz` is
read; the spec's `tz` gate declines first, and a decline is sound over
that -EFAULT.  This is the one call where the two orders would answer
differently if the `tz` arm answered anything.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem timezone_with_bad_tv_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    gettimeofday_spec (Z_to_bv 64 (2 ^ 64 - 8)) 8192 i m o ↔ o = Unmodeled := by
  sys_norm

/-! ## A NULL `tv` declines

With `tv` NULL and `tz` NULL the kernel skips the `tv` block (:143), skips
the `tz` block (:151) and returns 0 (:155), having written nothing.  The
arm declines: Rocq folds the wholly unwritable destination into the same
gate as `clock_gettime`'s, for uniformity, and the Lean twin keeps every
Rocq arm.  So the pins below fix a DECLARED NARROWING, not an empty
intersection: the kernel's 0 is refused because the arm answers nothing,
and the -EFAULT beside it is refused because no `put_user` runs. -/

/-- `gettimeofday(NULL, NULL)` declines.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem null_tv_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    gettimeofday_spec 0 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- The kernel's real answer, 0 with nothing written, is not admitted: the
narrowing Rocq declares, kept here.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem null_tv_zero_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ gettimeofday_spec 0 0 i m (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- -EFAULT is not admitted either, and here that is a kernel claim: with
both pointers NULL no `put_user` and no `copy_to_user` runs, so nothing
can fault.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem null_tv_efault_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ gettimeofday_spec 0 0 i m (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-! ## The delivered reading

On a wholly writable `tv` and a NULL `tz`, the kernel reads the wall clock
(`ktime_get_real_ts64`, kernel/time/timekeeping.c:793-811, v6.18.46), stores
`tv_sec` and `tv_nsec / 1000` with two `put_user`s (kernel/time/time.c:
147-148) and returns 0 (:155).  The reading is the environment's choice:
`do_settimeofday64` (kernel/time/timekeeping.c:1434-1465, v6.18.46) and
`__timekeeping_inject_offset` (:1480-1520) let any privileged process step
the clock between two calls, in either direction, so no relation to an
earlier reading exists to state.  What the arm fixes is the SHAPE: a
return of 0, exactly one write of sixteen bytes at `tv`, the model
untouched, no event, and a struct `timeval_ok_b` admits. -/

/-- The whole admitted set, as the existential the spec makes: some
sixteen bytes at 4096 satisfying `timeval_ok_b`, return 0, the model and
the event list untouched — and nothing else.
kernel: kernel/time/time.c:gettimeofday; kernel/time/timekeeping.c:ktime_get_real_ts64@v6.18.46 -/
theorem delivered_reading_iff (o : outcome SyscallEffect) :
    gettimeofday_spec 4096 0 (gettimeofday_input 0) demo_model o ↔
      ∃ bs : List byte, o = Ok (mkEffect 0 [(4096, bs)] []) demo_model []
        ∧ timeval_ok_b bs = true := by
  sys_norm

/-- The admitted side of the `KTIME_SEC_MAX` boundary: tv_sec =
KTIME_SEC_MAX - 1 with tv_usec = 999999, the last microsecond under the
ceiling.  `timespec64_valid_settod` (include/linux/time64.h:118-126)
admits every `tv_sec` under `TIME_SETTOD_SEC_MAX` (:123), thirty years
below this, and the read path (`ktime_get_real_ts64`) clamps nothing, so a
clock set just under the settable ceiling and left running reaches this
value.
kernel: include/linux/time64.h:timespec64_valid_settod; kernel/time/timekeeping.c:ktime_get_real_ts64,do_settimeofday64@v6.18.46
rocq-twin: gettimeofday_reading_below_ceiling_admissible -/
theorem reading_below_ceiling_admitted :
    gettimeofday_spec 4096 0 (gettimeofday_input 0) demo_model
      (Ok (mkEffect 0 [(4096, tv_ceiling_minus)] []) demo_model []) := by
  sys_norm

/-- One second further is refused.  `KTIME_SEC_MAX` is `KTIME_MAX /
NSEC_PER_SEC` (include/linux/time64.h:32): a `tv_sec` at or above it is a
wall clock `ktime_t` cannot hold once converted to nanoseconds, and every
writer refuses it thirty years earlier through `timespec64_valid_settod`
(:123).  The docstring of `Time.timeval_ok_b` names the one writer that
sits behind this argument.
kernel: include/linux/time64.h:timespec64_valid_settod; kernel/time/timekeeping.c:do_settimeofday64@v6.18.46
rocq-twin: gettimeofday_reading_at_ceiling_rejected -/
theorem reading_at_ceiling_rejected (m' : Model) (evs : List event) :
    ¬ gettimeofday_spec 4096 0 (gettimeofday_input 0) demo_model
        (Ok (mkEffect 0 [(4096, tv_at_ceiling)] []) m' evs) := by
  sys_refute

/-- `tv_usec` = 1000000 is refused: the kernel writes `ts.tv_nsec / 1000`
(kernel/time/time.c:148) out of a `timespec64` whose `tv_nsec`
`timespec64_add_ns` (include/linux/time64.h:163-167) has just reduced
below `NSEC_PER_SEC` by carrying whole seconds into `tv_sec` (:165), so
the quotient is below 10^6.
kernel: kernel/time/time.c:gettimeofday; include/linux/time64.h:timespec64_add_ns@v6.18.46 -/
theorem usec_carry_rejected (m' : Model) (evs : List event) :
    ¬ gettimeofday_spec 4096 0 (gettimeofday_input 0) demo_model
        (Ok (mkEffect 0 [(4096, tv_usec_carry)] []) m' evs) := by
  sys_refute

/-- Eight bytes are refused: the kernel stores BOTH `__kernel_long_t`
fields (kernel/time/time.c:147-148; include/uapi/linux/time_types.h:25-28)
or returns -EFAULT, never a `tv_sec` alone with a 0.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem short_write_rejected (m' : Model) (evs : List event) :
    ¬ gettimeofday_spec 4096 0 (gettimeofday_input 0) demo_model
        (Ok (mkEffect 0 [(4096, [3, 125, 193, 37, 2, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- Seventeen bytes are refused: two 8-byte stores write sixteen.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem long_write_rejected (m' : Model) (evs : List event) :
    ¬ gettimeofday_spec 4096 0 (gettimeofday_input 0) demo_model
        (Ok (mkEffect 0 [(4096, tv_ceiling_minus ++ [0])] []) m' evs) := by
  sys_refute

/-- The return is the literal 0 of kernel/time/time.c:155; a 1 is refused.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem nonzero_return_rejected (m' : Model) (evs : List event) :
    ¬ gettimeofday_spec 4096 0 (gettimeofday_input 0) demo_model
        (Ok (mkEffect 1 [(4096, tv_ceiling_minus)] []) m' evs) := by
  sys_refute

/-- The write lands at `tv`: `&tv->tv_sec` and `&tv->tv_usec`
(kernel/time/time.c:147-148), not eight bytes on.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem misplaced_write_rejected (m' : Model) (evs : List event) :
    ¬ gettimeofday_spec 4096 0 (gettimeofday_input 0) demo_model
        (Ok (mkEffect 0 [(4104, tv_ceiling_minus)] []) m' evs) := by
  sys_refute

/-- Exactly one write: with `tz` NULL the `tz` block (:151) is skipped, so
a second write anywhere is refused.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem second_write_rejected (m' : Model) (evs : List event) :
    ¬ gettimeofday_spec 4096 0 (gettimeofday_input 0) demo_model
        (Ok (mkEffect 0 [(4096, tv_ceiling_minus), (4112, [0])] []) m' evs) := by
  sys_refute

/-- -EFAULT is refused on a wholly writable `tv`: both `put_user`s pass
their `access_ok` (arch/riscv/include/asm/uaccess.h:412) and store into
mapped, writable memory.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem writable_tv_efault_rejected (m' : Model) (evs : List event) :
    ¬ gettimeofday_spec 4096 0 (gettimeofday_input 0) demo_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- The arm does not decline a wholly writable `tv` with a NULL `tz`: the
call is answered.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem writable_tv_never_unmodeled :
    ¬ gettimeofday_spec 4096 0 (gettimeofday_input 0) demo_model Unmodeled := by
  sys_refute

/-! ### The model is left alone

There is deliberately no realtime field in `Model`: the reading is chosen
afresh per call and related to nothing, because relating realtime to
monotonic would need a per-run offset that stops being constant the moment
anything sets the clock (`do_settimeofday64`, `__timekeeping_inject_offset`
above).  The consequence is that an accepted `gettimeofday` moves NOTHING —
not the clock, not the fds, not the maps — and emits no event.  No trace
can establish that: a trace shows what an execution did, not that a whole
class of executions left the model alone. -/

/-- UNIVERSALLY QUANTIFIED, the twin of Rocq's second lemma: every accepted
call, on every argument, input and model, returns the model it was given
and emits nothing.  The gates are symbolic, so each is split by hand and
the normalizer reads the arm it selects: the two declines and the torn
band are empty, the -EFAULT arm is a `pure`, and the delivered reading is a
`choose` whose continuation is a `pure`.  The `match` on the copy is
opened by generalizing its discriminant, and the range gate behind it by
casing on the Bool and rewriting it in, since `split` cannot find the
discriminant of a `match` or an `if` that is applied to the monad's
arguments.
kernel: kernel/time/time.c:gettimeofday@v6.18.46
rocq-twin: gettimeofday_never_moves_the_model -/
theorem success_never_moves_the_model (tv tz : word) (i : SyscallInput) (m m' : Model)
    (eff : SyscallEffect) (evs : List event)
    (h : gettimeofday_spec tv tz i m (Ok eff m' evs)) : m' = m ∧ evs = [] := by
  unfold gettimeofday_spec at h
  split at h
  · sys_refute at h
  · split at h
    · sys_refute at h
    · simp only [bind_input_iff] at h
      generalize copy_bytes_map i.in_wmem tv 16 = r at h
      cases r with
      | none =>
        cases hc : access_okb tv 8 with
        | false =>
          simp only [hc, Bool.not_false, ↓reduceIte] at h
          sys_norm at h
          exact ⟨h.2.1, h.2.2⟩
        | true =>
          simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          sys_refute at h
      | some _ =>
        sys_norm at h
        obtain ⟨_, _, hm, he, _⟩ := h
        exact ⟨hm, he⟩

/-- Concretely: a delivered reading beside a moved clock is refused.  The
monotonic clock is `m_clock`; `gettimeofday` reads a different clock and
writes neither.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem moved_clock_rejected :
    ¬ gettimeofday_spec 4096 0 (gettimeofday_input 0) demo_model
        (Ok (mkEffect 0 [(4096, tv_ceiling_minus)] []) (with_clock 5 demo_model) []) := by
  sys_refute

/-- …and beside an event: the sixteen bytes go to user memory, not to a
channel.
kernel: kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem event_rejected :
    ¬ gettimeofday_spec 4096 0 (gettimeofday_input 0) demo_model
        (Ok (mkEffect 0 [(4096, tv_ceiling_minus)] []) demo_model [event.WriteEv 1 0]) := by
  sys_refute

/-! ## A destination that is not wholly writable

The kernel writes `tv` with TWO `put_user`s (kernel/time/time.c:147-148, v6.18.46).
Each tests `access_ok` over its own eight bytes
(arch/riscv/include/asm/uaccess.h:408-415 at v6.18.46, the test at :412) and then
stores; a store into an unmapped page faults and the call returns -EFAULT
(:149).  Two shapes follow for a `tv` inside the address space that is not
wholly mapped, and the arm declines both, because `copy_bytes_map` reports
only that the sixteen-byte walk failed and not where:

- the FIRST page unmapped: `tv_sec`'s store faults, nothing is written,
  -EFAULT.  The model could spell this, and the arm declines it anyway —
  Rocq's arm makes the same choice, and the decline is sound.
- the SECOND page unmapped: `tv_sec` is stored, `tv_usec`'s store faults,
  -EFAULT with a half-written struct.  No single effect spells that.

So these are declared narrowings: what is refused below is refused because
the arm answers nothing there, not because the kernel does not do it. -/

/-- Sixteen unmapped bytes at 4096: declined.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem unmapped_tv_declines (m : Model) (o : outcome SyscallEffect) :
    gettimeofday_spec 4096 0
        (SyscallInput.mkInput 169 [4096, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- The kernel's -EFAULT with nothing written is not admitted there: the
narrowing, stated.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem unmapped_tv_efault_rejected (m m' : Model) (evs : List event) :
    ¬ gettimeofday_spec 4096 0
        (SyscallInput.mkInput 169 [4096, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- `tv_sec`'s eight bytes mapped and `tv_usec`'s not: declined.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem torn_mapping_declines (m : Model) (o : outcome SyscallEffect) :
    gettimeofday_spec 4096 0
        (SyscallInput.mkInput 169 [4096, 0, 0, 0, 0, 0] (fun _ => none) wmem_ts_half) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- The half-written struct the kernel really leaves — `tv_sec` stored,
-EFAULT returned — is not an outcome the arm admits; nor is the bare
-EFAULT.  Both are the shape the decline exists for.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem torn_mapping_half_write_rejected (m m' : Model) (evs : List event) :
    ¬ gettimeofday_spec 4096 0
        (SyscallInput.mkInput 169 [4096, 0, 0, 0, 0, 0] (fun _ => none) wmem_ts_half) m
        (Ok (mkEffect (errno_ret EFAULT) [(4096, [3, 125, 193, 37, 2, 0, 0, 0])] []) m' evs)
    ∧ ¬ gettimeofday_spec 4096 0
        (SyscallInput.mkInput 169 [4096, 0, 0, 0, 0, 0] (fun _ => none) wmem_ts_half) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  constructor <;> sys_refute

/-! ## The destination that walks off the top of the address space

The bands on either side of `TASK_SIZE`, and the two widths, 8 and 16.
`__access_ok` (include/asm-generic/access_ok.h:31-41, v6.18.46) is
`(size <= limit) && (addr <= (limit - size))` (:40) with `limit` the
`TASK_SIZE_MAX` that falls back to `TASK_SIZE` (:15-16); riscv's
`access_ok` (arch/riscv/include/asm/uaccess.h, v6.18.46) is that test, and
`put_user` (:408-415) applies it over the pointee's eight bytes (:412)
before it stores.  So a refused 16-byte range splits: where the first
store's own test fails nothing is written and the call is -EFAULT; where
only the second's fails, `tv_sec` is committed first.

The VERDICTS at these `tv`s are probe-covered on the Rocq side
(`gettimeofday_spec.c`'s `efault_top`, `efault_wrap` and `torn` modes).
What belongs here is what a probe cannot show: the harness's writable
view answers `none` at and above 2^47 by construction, so under it a
wrapping range is unwritable twice over and a spec that merely walked
would reach the same verdict as one that asks the range first.  The
memories below therefore map the wrapped range IN FULL, the bare walk is
shown reading it back, and the range test is shown refusing it anyway —
which is what tells `copy_bytes_map` from `read_bytes_map`, and what
makes the widths a measurement against `TASK_SIZE` rather than against
what happened to be mapped. -/

/-- The last eight bytes of the address space, so the 16-byte walk covers
them and then the eight at 0. -/
def gettimeofday_wrap_tv : word := Z_to_bv 64 (2 ^ 64 - 8)

/-- A memory that maps EXACTLY the wrapped range and nothing else, which is
what makes the walk pin below tight. -/
def gettimeofday_wrap_mem : word → Option byte :=
  fun a => if bv_unsigned a < 8 ∨ 2 ^ 64 - 8 ≤ bv_unsigned a then some 0 else none

/-- THE MUTATION TEST, MADE PERMANENT.  The bare walk WRAPS, because
`read_bytes_map` advances in word arithmetic, and reads all sixteen bytes
back off a memory that maps only those sixteen.  A spec consulting it
alone would answer 0 and a 16-byte write where Linux's first `put_user` is
refused.  Without this beside them the pins below would also pass if
`gettimeofday_wrap_tv` stopped wrapping or `gettimeofday_wrap_mem` stopped
mapping the range.
model: the walk's word arithmetic, a fact about `read_bytes_map` alone.
rocq-twin: gettimeofday_wrap_would_pass_the_bare_walk -/
theorem wrap_would_pass_the_bare_walk :
    read_bytes_map gettimeofday_wrap_mem gettimeofday_wrap_tv (Z_to_bv 64 16) ≠ none := by
  decide

/-- `copy_bytes_map` refuses it before the walk is consulted: `__access_ok`
subtracts in `unsigned long` and the wrapped range fails `addr <= limit -
size` (include/asm-generic/access_ok.h:40).
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46
rocq-twin: gettimeofday_wrap_is_refused_before_the_walk -/
theorem wrap_is_refused_before_the_walk :
    copy_bytes_map gettimeofday_wrap_mem gettimeofday_wrap_tv 16 = none := by
  decide

/-- …and so is the FIRST store's own eight bytes, which is what makes the
answer -EFAULT with nothing written rather than a decline.
kernel: arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem wrap_first_store_refused : access_okb gettimeofday_wrap_tv 8 = false := by
  decide

attribute [sys_simp] wrap_is_refused_before_the_walk

/-- THE ONE THAT MATTERS: -EFAULT with nothing written is the answer, and
nothing else is.  `put_user`'s `access_ok` (arch/riscv/include/asm/uaccess.h:
412) refuses the first store and the macro answers `-EFAULT` (:414), which
`gettimeofday` returns (kernel/time/time.c:149).
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46
rocq-twin: gettimeofday_wrapping_tv_is_efault -/
theorem wrapping_tv_is_efault (m : Model) (o : outcome SyscallEffect) :
    gettimeofday_spec gettimeofday_wrap_tv 0
        (SyscallInput.mkInput 169 [gettimeofday_wrap_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_wrap_mem) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm

/-- The write the bare walk would have admitted — a reading landing at
`2^64 - 8` and, after the word wrapped, at 0 — is refused.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46
rocq-twin: gettimeofday_wrapping_tv_is_efault -/
theorem wrapping_tv_delivery_rejected (m m' : Model) (evs : List event) :
    ¬ gettimeofday_spec gettimeofday_wrap_tv 0
        (SyscallInput.mkInput 169 [gettimeofday_wrap_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_wrap_mem) m
        (Ok (mkEffect 0 [(gettimeofday_wrap_tv, tv_ceiling_minus)] []) m' evs) := by
  sys_refute

/-- PAST `TASK_SIZE` WITHOUT WRAPPING: `tv = 2^63` with sixteen bytes sums
to `2^63 + 16`, under `2^64`, so a bare no-wrap test would accept it and
the walk reads it in full. -/
def gettimeofday_high_tv : word := Z_to_bv 64 (2 ^ 63)

def gettimeofday_high_mem : word → Option byte :=
  fun a => if 2 ^ 63 ≤ bv_unsigned a ∧ bv_unsigned a < 2 ^ 63 + 16 then some 0 else none

/-- The walk reads the high range in full.
model: a fact about `read_bytes_map` over the fixture.
rocq-twin: gettimeofday_high_range_reads -/
theorem high_range_reads :
    read_bytes_map gettimeofday_high_mem gettimeofday_high_tv (Z_to_bv 64 16) ≠ none := by
  decide

/-- …and a guard that only refused a WRAPPING range would accept it: the
sum stays under `2^64`.
model: the shape of a guard the spec does not use, measured on the fixture.
rocq-twin: gettimeofday_high_range_would_pass_a_no_wrap_test -/
theorem high_range_would_pass_a_no_wrap_test :
    bv_unsigned gettimeofday_high_tv + 16 < two_pow_64 := by
  decide

/-- `__access_ok` refuses it because it tests `addr <= limit - size`
(include/asm-generic/access_ok.h:40), and refuses the first store's eight
bytes alone by the same test.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem high_range_refused :
    copy_bytes_map gettimeofday_high_mem gettimeofday_high_tv 16 = none
    ∧ access_okb gettimeofday_high_tv 8 = false := by
  decide

attribute [sys_simp] high_range_refused

/-- So the answer is -EFAULT with nothing written, and nothing else.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46
rocq-twin: gettimeofday_past_task_size_is_efault -/
theorem past_task_size_is_efault (m : Model) (o : outcome SyscallEffect) :
    gettimeofday_spec gettimeofday_high_tv 0
        (SyscallInput.mkInput 169 [gettimeofday_high_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_high_mem) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm

/-- …and the delivered reading is refused there.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46
rocq-twin: gettimeofday_past_task_size_is_efault -/
theorem past_task_size_delivery_rejected (m m' : Model) (evs : List event) :
    ¬ gettimeofday_spec gettimeofday_high_tv 0
        (SyscallInput.mkInput 169 [gettimeofday_high_tv, 0, 0, 0, 0, 0] (fun _ => none)
          gettimeofday_high_mem) m
        (Ok (mkEffect 0 [(gettimeofday_high_tv, tv_ceiling_minus)] []) m' evs) := by
  sys_refute

/-! ### The two widths, 8 and 16

Measured over a memory that maps everything, so the walk is settled for
every destination at once and the verdict turns on the range tests alone.
Four `tv`s, one step apart at each edge of the band the spec declines:

- `TASK_SIZE - 16`: both stores inside, the reading is delivered.  This
  is the control that keeps the refusals above honest — they would also
  pass under a guard that refused every `tv`.
- `TASK_SIZE - 15` and `TASK_SIZE - 8`, the two ends of the torn band:
  the first `put_user` passes its own 8-byte test and the second does
  not, so the arm declines whatever the effect says.
- `TASK_SIZE - 7`: the FIRST store is refused, so -EFAULT with nothing
  written is the answer and a delivered reading is not.

Move either width by one and one of these flips. -/

def gettimeofday_open_mem : word → Option byte := fun _ => some 0

def gettimeofday_at (tv : word) : SyscallInput :=
  SyscallInput.mkInput 169 [tv, 0, 0, 0, 0, 0] (fun _ => none) gettimeofday_open_mem

def task_size_minus (k : Int) : word := Z_to_bv 64 (TASK_SIZE - k)

/-- The four destinations against `__access_ok`'s two tests, at the two
widths: sixteen bytes fit at `TASK_SIZE - 16` and nowhere above it, eight
fit up to `TASK_SIZE - 8` and not at `TASK_SIZE - 7`.
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem widths_at_the_edges :
    access_okb (task_size_minus 16) 16 = true
    ∧ access_okb (task_size_minus 15) 16 = false ∧ access_okb (task_size_minus 15) 8 = true
    ∧ access_okb (task_size_minus 8) 16 = false ∧ access_okb (task_size_minus 8) 8 = true
    ∧ access_okb (task_size_minus 7) 8 = false := by
  decide

/-- The walk over the open memory, at the four destinations: read in full
where the range test admits it, and the closed readings `sys_norm` needs
where it does not.
model: closed `copy_bytes_map` readings over the open fixture, rewrites for `sys_norm`. -/
theorem copies_at_the_edges :
    copy_bytes_map gettimeofday_open_mem (task_size_minus 16) 16 = some (List.replicate 16 0)
    ∧ copy_bytes_map gettimeofday_open_mem (task_size_minus 15) 16 = none
    ∧ copy_bytes_map gettimeofday_open_mem (task_size_minus 8) 16 = none
    ∧ copy_bytes_map gettimeofday_open_mem (task_size_minus 7) 16 = none := by
  decide

attribute [sys_simp] copies_at_the_edges

/-- The last admitted destination delivers the reading.
kernel: kernel/time/time.c:gettimeofday; include/asm-generic/access_ok.h:__access_ok@v6.18.46
rocq-twin: gettimeofday_last_admitted_tv_is_delivered -/
theorem last_admitted_tv_is_delivered :
    gettimeofday_spec (task_size_minus 16) 0 (gettimeofday_at (task_size_minus 16)) demo_model
      (Ok (mkEffect 0 [(task_size_minus 16, tv_ceiling_minus)] []) demo_model []) := by
  sys_norm

/-- Both ends of the torn band decline: the first store passes its own
test (`widths_at_the_edges`) and the second is refused, so `tv_sec` is
committed and the call is -EFAULT — the half-written struct no single
effect spells.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46
rocq-twin: gettimeofday_torn_band_declines -/
theorem torn_band_declines (m : Model) (o : outcome SyscallEffect) :
    (gettimeofday_spec (task_size_minus 15) 0 (gettimeofday_at (task_size_minus 15)) m o
      ↔ o = Unmodeled)
    ∧ (gettimeofday_spec (task_size_minus 8) 0 (gettimeofday_at (task_size_minus 8)) m o
      ↔ o = Unmodeled) := by
  constructor <;> sys_norm

/-- The bare -EFAULT is not given in the torn band: the decline admits
nothing, and a spec answering -EFAULT there would be claiming nothing
was written where `tv_sec` was.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46
rocq-twin: gettimeofday_torn_band_declines -/
theorem torn_band_efault_rejected (m m' : Model) (evs : List event) :
    ¬ gettimeofday_spec (task_size_minus 15) 0 (gettimeofday_at (task_size_minus 15)) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- One byte past the band the first store is refused, so -EFAULT with
nothing written is the answer, and the only one.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46
rocq-twin: gettimeofday_first_store_refused_is_efault -/
theorem first_store_refused_is_efault (m : Model) (o : outcome SyscallEffect) :
    gettimeofday_spec (task_size_minus 7) 0 (gettimeofday_at (task_size_minus 7)) m o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  sys_norm

/-- …and a delivered reading there is refused.
kernel: kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46
rocq-twin: gettimeofday_first_store_refused_is_efault -/
theorem first_store_refused_delivery_rejected (m m' : Model) (evs : List event) :
    ¬ gettimeofday_spec (task_size_minus 7) 0 (gettimeofday_at (task_size_minus 7)) m
        (Ok (mkEffect 0 [(task_size_minus 7, tv_ceiling_minus)] []) m' evs) := by
  sys_refute

/-! ## The dispatcher: syscall 169, two pointer arguments

`SYSCALL_DEFINE2(gettimeofday, struct __kernel_old_timeval __user *, tv,
struct timezone __user *, tz)` (kernel/time/time.c:140-141, v6.18.46) takes a0 and
a1 as full 64-bit pointers — no narrowing, unlike an `int` argument — and
reads a2..a5 not at all.  The three shape declines below are named
`…_declines` and stated in the direct shape, which
`tools/check_decline_registers.py` reads as declines on a modeled number;
`sysno_170_is_unmodeled` at the end is the register claim on a NUMBER. -/

/-- Syscall 169 with a2..a5 set to junk reaches the arm and delivers.
kernel: include/uapi/asm-generic/unistd.h:__NR_gettimeofday; kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem sysno_169_is_gettimeofday (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 169 [4096, 0, 7, 7, 7, 7] (fun _ => none) wmem_ts)
        demo_model o
      ↔ ∃ bs : List byte, o = Ok (mkEffect 0 [(4096, bs)] []) demo_model []
          ∧ timeval_ok_b bs = true := by
  sys_norm

/-- a1 is the timezone pointer: set, the call declines through the
dispatcher as it does at the arm.
kernel: include/uapi/asm-generic/unistd.h:__NR_gettimeofday; kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem sysno_169_tz_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 169 [4096, 8192, 0, 0, 0, 0] (fun _ => none) wmem_ts) m
      Unmodeled := by
  sys_norm

/-- …and the `{0, 0}` guess is refused through the dispatcher too.
kernel: include/uapi/asm-generic/unistd.h:__NR_gettimeofday; kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem sysno_169_tz_zero_answer_rejected :
    ¬ syscall_spec (SyscallInput.mkInput 169 [4096, 8192, 0, 0, 0, 0] (fun _ => none) wmem_ts)
        demo_model
        (Ok (mkEffect 0 [(4096, tv_ceiling_minus), (8192, List.replicate 8 0)] []) demo_model []) := by
  sys_refute

/-- a1 is a POINTER, not narrowed: a `tz` with only bit 32 set is non-NULL
and declines, where a port that narrowed a1 to an `int` would answer.
kernel: include/uapi/asm-generic/unistd.h:__NR_gettimeofday; kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem sysno_169_tz_high_bits_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 169 [4096, 4294967296, 0, 0, 0, 0] (fun _ => none) wmem_ts) m
      Unmodeled := by
  sys_norm

/-- a0 NULL declines through the dispatcher.
kernel: include/uapi/asm-generic/unistd.h:__NR_gettimeofday; kernel/time/time.c:gettimeofday@v6.18.46 -/
theorem sysno_169_null_tv_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 169 [0, 0, 0, 0, 0, 0] (fun _ => none) wmem_ts) m
      Unmodeled := by
  sys_norm

/-- a0 is a POINTER, not narrowed: the wrapping destination reaches the
arm whole and answers -EFAULT, where a narrowed a0 would be 2^32 - 8,
a low address the open memory delivers to.
kernel: include/uapi/asm-generic/unistd.h:__NR_gettimeofday; kernel/time/time.c:gettimeofday; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem sysno_169_wrap_is_efault (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 169 [gettimeofday_wrap_tv, 0, 0, 0, 0, 0] (fun _ => none)
        gettimeofday_wrap_mem) demo_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) demo_model [] := by
  sys_norm

/-- `settimeofday` (170), the one writer of `sys_tz` and a setter of the
wall clock, has no arm in this table, nor in Rocq's: it declines by
absence.  Read by `tools/check_decline_registers.py` as register L3's
claim on the number.
kernel: kernel/time/time.c:settimeofday@v6.18.46 -/
theorem sysno_170_is_unmodeled (m : Model) :
    syscall_spec (SyscallInput.mkInput 170 [4096, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
      Unmodeled := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time.Time
