import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Fork
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.State
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Fork
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Oracle
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
import LinuxProcessSemantics.LinuxProcessSem.Checks.ProcessCreation

/-! # Checks.Cases.Checks.Sys.Kernel.Fork — what the set_tid_address, clone and clone3 checkers answer, read off against Linux

Pins over `Checks.Sys.Kernel.Fork`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Kernel/Fork.v` and of
`theories/LinuxProcessSem/Checks/Witness/Kernel/Fork.v`.  Rocq's one
worked case on the set_tid_address arm,
`set_tid_address_first_choice_is_within_modeled_envelope`
(`Checks/Cases/Kernel/Fork.v`), is stated over the SPEC — its proof reaches
through the checker, its statement does not — and is twinned in
`Checks/Cases/Kernel/Fork.lean`.  Rocq's cases on the clone checker live in
`Checks/ProcessCreation.v` (`clone_checker_admits_a_pid` and its
neighbours) and are stated through `check_syscall`, the dispatcher, which
only the conformance ticket's registration step reaches; the section on
clone below states each of them against `check_clone` and `check_clone3`
directly and says which Rocq case it is the companion of.  So this file
mirrors nothing: these are the Lean tree's tests for what the twin ports,
placed where every pin in this tree lives (`Checks/Cases/<mirror path>`) so
that `tools/check_lean_pins.py` reads them and the twin holds only
definitions and their Rocq-twin lemmas.  Not part of the trusted specification: this
file is QA on the definitions, written to be READ, and every claim in it
is a claim about what the kernel does, with the citation beside it.
Every kernel line below was read at Linux v6.18.46 (commit 1f99e9ab748f).

WHAT A CHECKER PIN IS FOR.  The four proof obligations the arm carries
(`ca_sound_ok` and the rest) already tie the checker to the spec, in
both directions, for every input.  What they cannot say is that either
side agrees with Linux: change the spec and the checker the same wrong
way and every obligation still closes.  Each pin below therefore names a
CONCRETE answer — a return the kernel gives, refused; a return it cannot
give, accepted — so that the wrong change fails here.  Beside each
accepted answer is the lie a kernel cannot tell, refuted on its own.

The probes `testing/syscall-check/tests/set_tid.c` and
`gettid_spec.c` state the same facts of the ROCQ checker, through the
extracted model, and are the evidence a `--mutate` run rests on.

The pins over a SYMBOLIC model take the recorded tid as a hypothesis
(`m_tid m = none`, `m_tid m = some 7`) and read the arm it selects by
`simp only [check_set_tid_address, h, …]`; the closed comparisons the arm
then makes are decided by `show … by decide`.  The pins over the shared
`demo_model`, whose tid slot is empty (`m_tid_demo_model`,
`Checks/Cases/Prelude.lean`), close by `rfl`.  The clone pins reuse the
descriptor fixtures and the `clone3` image fixtures of
`Checks/Cases/Kernel/Fork.lean` (`open_file_model`, `fork_mem`,
`c3_input`, …) so that the checker is read on the very tables and images
the spec's own pins are read on.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Fork

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Fork
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.State (pin_mem)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Fork

section FirstCall

/-! ## The first call: the trace's return becomes the recorded tid

`set_tid_address` (kernel/fork.c:1747-1752, v6.18.46) returns
`task_pid_vnr(current)`, a number the model cannot predict.  The checker
accepts any return the spec could have drawn — a tid `alloc_pid`
(kernel/pid.c:163-309, v6.18.46) could have stored — and records it, so
that every later call is held to it. -/

variable (m : Model) (a : word) (b : byte)

/-- tid 1 is accepted on a first call and becomes the recorded tid:
`pid_min` starts at 1 (kernel/pid.c:226), the number the kernel's own
comment reserves for init (kernel/pid.c:228-229), so a fresh namespace's
first draw can be 1.  The post-model is `with_tid 1 m`, not `m` — the pin after this one is what
separates the two.
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_set_tid_address_records_the_first_draw (h : m_tid m = none) :
    check_set_tid_address (mkEffect 1 [] []) m = CheckOk (with_tid 1 m) [] := by
  simp only [check_set_tid_address, h,
    show (decide (0 < bv_unsigned (1 : word)) && decide (bv_unsigned (1 : word) < PID_MAX_ENVELOPE))
      = true by decide, ↓reduceIte]

/-- The recorded model is not the old one: a checker answering `CheckOk m
[]` on the first call would accept the same traces and be wrong about
what the process now is, since `m_tid` moved from `none` to `some 1`.
This is the half of `ca_complete_ok` a return-only acceptor would fail.
model: the post-model is the checker's own construction; `m_tid (with_tid 1 m) = some 1` against the hypothesis `m_tid m = none` -/
theorem check_set_tid_address_first_call_moves_the_model (h : m_tid m = none) :
    check_set_tid_address (mkEffect 1 [] []) m ≠ CheckOk m [] := by
  rw [check_set_tid_address_records_the_first_draw m h]
  intro heq
  have hm : with_tid 1 m = m := (check_result.CheckOk.inj heq).1
  have ht : m_tid (with_tid 1 m) = m_tid m := congrArg m_tid hm
  have hs : m_tid (with_tid 1 m) = some 1 := rfl
  rw [hs, h] at ht
  cases ht

/-- The highest tid a real kernel hands out is accepted too:
`create_pid_namespace` sets a child namespace's `pid_max` to
`PID_MAX_LIMIT` (kernel/pid_namespace.c:110), which on a 64-bit kernel
without `CONFIG_BASE_SMALL` is `4 * 1024 * 1024`
(include/linux/threads.h:34-35), and
`idr_alloc_cyclic`'s `end` is exclusive (lib/idr.c:122), so `2^22 - 1` is
the last number `alloc_pid` can store.
kernel: kernel/pid.c:alloc_pid; kernel/pid_namespace.c:create_pid_namespace@v6.18.46 -/
theorem check_set_tid_address_records_the_highest_draw (h : m_tid m = none) :
    check_set_tid_address (mkEffect 4194303 [] []) m = CheckOk (with_tid 4194303 m) [] := by
  simp only [check_set_tid_address, h,
    show (decide (0 < bv_unsigned (4194303 : word))
        && decide (bv_unsigned (4194303 : word) < PID_MAX_ENVELOPE)) = true by decide, ↓reduceIte]

/-- tid 0 is refused: no live task holds it.  `alloc_pid` allocates from
`pid_min = 1` (kernel/pid.c:226) and a requested tid below 1 is -EINVAL
(kernel/pid.c:198-199), so a kernel reporting 0 is lying.
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_set_tid_address_refuses_tid_zero (h : m_tid m = none) :
    check_set_tid_address (mkEffect 0 [] []) m = CheckReject := by
  simp only [check_set_tid_address, h,
    show (decide (0 < bv_unsigned (0 : word)) && decide (bv_unsigned (0 : word) < PID_MAX_ENVELOPE))
      = false by decide, Bool.false_eq_true, ↓reduceIte]

/-- `2^22` itself is refused: `idr_alloc_cyclic` treats its `end` as
exclusive — `max = end > 0 ? end - 1 : INT_MAX` (lib/idr.c:122) — so
`pid_max` is never allocated, and `pid_max` never exceeds `PID_MAX_LIMIT`
(the five writes are walked on `Sys.Kernel.Fork.PID_MAX_ENVELOPE`).
kernel: lib/idr.c:idr_alloc_cyclic; kernel/pid_namespace.c:create_pid_namespace@v6.18.46 -/
theorem check_set_tid_address_refuses_the_envelope_end (h : m_tid m = none) :
    check_set_tid_address (mkEffect 4194304 [] []) m = CheckReject := by
  simp only [check_set_tid_address, h,
    show (decide (0 < bv_unsigned (4194304 : word))
        && decide (bv_unsigned (4194304 : word) < PID_MAX_ENVELOPE)) = false by decide,
    Bool.false_eq_true, ↓reduceIte]

/-- The all-ones word is refused on a first call: read unsigned, the bit
pattern of -1 is `2^64 - 1`, above the envelope, and the call has no path
that returns it (kernel/fork.c:1749-1751).  First-call twin of
`check_set_tid_address_refuses_all_ones_later`; the probe's
`set_tid_address:ret=max64 -- one` case
(`testing/syscall-check/tests/set_tid.c`) states the same of the Rocq
checker.
kernel: kernel/fork.c:set_tid_address; lib/idr.c:idr_alloc_cyclic@v6.18.46 -/
theorem check_set_tid_address_refuses_all_ones (h : m_tid m = none) :
    check_set_tid_address (mkEffect 18446744073709551615 [] []) m = CheckReject := by
  simp only [check_set_tid_address, h,
    show (decide (0 < bv_unsigned (18446744073709551615 : word))
        && decide (bv_unsigned (18446744073709551615 : word) < PID_MAX_ENVELOPE)) = false by decide,
    Bool.false_eq_true, ↓reduceIte]

/-- The low 32 bits are 5, and bit 32 is set.
Linux returns a `pid_t`, an `int`, so the return register excludes this value.
This pin fails for a checker that tests only the low 32 bits.
The probe case `set_tid_address:ret=4294967301 -- one` in
`testing/syscall-check/tests/set_tid.c` states the same of the Rocq checker.
The Rocq twin is `check_set_tid_address_refuses_a_tid_past_32_bits` in
`theories/LinuxProcessSem/Checks/Cases/Kernel/Fork.v`.
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem check_set_tid_address_refuses_a_tid_past_32_bits (h : m_tid m = none) :
    check_set_tid_address (mkEffect 4294967301 [] []) m = CheckReject := by
  simp only [check_set_tid_address, h,
    show (decide (0 < bv_unsigned (4294967301 : word))
        && decide (bv_unsigned (4294967301 : word) < PID_MAX_ENVELOPE)) = false by decide,
    Bool.false_eq_true, ↓reduceIte]

/-- An errno is refused: `set_tid_address` has no error path — two
statements, a store and a return (kernel/fork.c:1749-1751) — so a trace
reporting -EINVAL is lying.  -EINVAL is what `alloc_pid` returns for a
bad REQUESTED tid (kernel/pid.c:198-199), a path `set_tid_address` does
not reach.  The checker sees the bit pattern of -22, `2^64 - 22`, fail the
envelope's upper bound; there is no errno arm to reach.
kernel: kernel/fork.c:set_tid_address; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_set_tid_address_refuses_an_errno (h : m_tid m = none) :
    check_set_tid_address (mkEffect (errno_ret EINVAL) [] []) m = CheckReject := by
  simp only [check_set_tid_address, h,
    show (decide (0 < bv_unsigned (errno_ret EINVAL))
        && decide (bv_unsigned (errno_ret EINVAL) < PID_MAX_ENVELOPE)) = false by decide,
    Bool.false_eq_true, ↓reduceIte]

/-- A write is refused beside an acceptable return: the call stores
`tidptr` in the caller's `clear_child_tid` (kernel/fork.c:1749) and
dereferences nothing, so a trace showing a byte written by it is lying.
The refusal is by the effect's shape and does not consult the model.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem check_set_tid_address_refuses_a_write :
    check_set_tid_address (mkEffect 1 [(a, [b])] []) m = CheckReject := rfl

/-- So is a copy-in ledger: the call reads no user memory, so a recorded
read is a lie about what the kernel did.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem check_set_tid_address_refuses_a_copyin_ledger :
    check_set_tid_address (SyscallEffect.mkEffectU 1 [] [] [] [] [(a, 4)]) m = CheckReject := rfl

/-- A zeros ledger is refused the same way: the call zero-fills nothing.
The probe's `smuggle-zeros` case (`testing/syscall-check/tests/set_tid.c`)
states this of the Rocq checker.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem check_set_tid_address_refuses_a_zeros_ledger :
    check_set_tid_address (mkEffect 1 [] [(a, 8)]) m = CheckReject := rfl

/-- …an unmap ledger: the call unmaps nothing.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem check_set_tid_address_refuses_an_unmap :
    check_set_tid_address (SyscallEffect.mkEffectU 1 [] [] [(a, 8)] [] []) m = CheckReject := rfl

/-- …and a copies ledger: the call copies nothing.  With the four
refusals before it, every ledger of the effect is pinned empty, so a
checker matching `mkEffectU ret [] zs us cs []` — the spec's `ret_only`
misread as "no writes and no copy-ins" — passes the tid pins and fails
these three.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem check_set_tid_address_refuses_a_copy :
    check_set_tid_address (SyscallEffect.mkEffectU 1 [] [] [] [MemCopy.mkCopy a a 8] []) m
      = CheckReject := rfl

/-- The same first call on the shared fixture, whose tid slot is empty,
closed by computation alone.
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_set_tid_address_records_the_first_draw_on_the_fixture :
    check_set_tid_address (mkEffect 1 [] []) demo_model = CheckOk (with_tid 1 demo_model) [] := rfl

/-- …and tid 0 refused on it.
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_set_tid_address_refuses_tid_zero_on_the_fixture :
    check_set_tid_address (mkEffect 0 [] []) demo_model = CheckReject := rfl

end FirstCall

section LaterCall

/-! ## A later call: the recorded tid, and nothing else

`task_pid_vnr(current)` (include/linux/pid.h:244-247, v6.18.46) reads the
pid of the calling task, which does not move while the task is its own
thread-group leader — the premise `Sys/Kernel/Fork.lean` states and
`testing/syscall-check/tests/unmodeled_clone.c` pins on the Rocq side. -/

variable (m : Model) (tid : word) (a : word) (b : byte)

/-- The recorded tid is accepted, and the model does not move.  Stated for
every recorded `tid`, 0 and values at or above the envelope included: the
checker holds a later call to whatever was recorded, and the statement
asserts nothing a kernel cannot do only while every writer of `m_tid`
records a value inside the envelope — this arm and `Sys/Kernel/Sys.lean`'s
`setsid_spec` both draw there.
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem check_set_tid_address_repeats_the_recorded_tid (h : m_tid m = some tid) :
    check_set_tid_address (mkEffect tid [] []) m = CheckOk m [] := by
  simp only [check_set_tid_address, h, bv_eqb_refl, ↓reduceIte]

/-- Another tid is refused, even one inside the envelope: the pid of a
task is the one number, and a kernel reporting 8 to a task holding 7 is
lying.  `task_pid_vnr` reads whatever `struct pid` the task holds now; the
one mover of a live task's pid is `exchange_tids` (kernel/pid.c:384-403),
reached from `de_thread` for a non-leader thread that execs, which the
single-task premise in the section header rules out.
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr; kernel/pid.c:exchange_tids@v6.18.46 -/
theorem check_set_tid_address_refuses_another_tid (h : m_tid m = some 7) :
    check_set_tid_address (mkEffect 8 [] []) m = CheckReject := by
  simp only [check_set_tid_address, h, show bv_eqb (8 : word) 7 = false by decide,
    Bool.false_eq_true, ↓reduceIte]

/-- A second draw is refused: tid 1 is inside the envelope and would have
been accepted on a first call, and is refused once 7 is recorded.  This
is the pin that separates the checker from one that re-draws on every
call.
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem check_set_tid_address_refuses_a_second_draw (h : m_tid m = some 7) :
    check_set_tid_address (mkEffect 1 [] []) m = CheckReject := by
  simp only [check_set_tid_address, h, show bv_eqb (1 : word) 7 = false by decide,
    Bool.false_eq_true, ↓reduceIte]

/-- 0 is refused on a later call as well.  `task_pid_vnr(current)`
(include/linux/pid.h:244-247) reaches `pid_nr_ns` (kernel/pid.c:490-501),
whose `nr = 0` default is for a pid with no number in the namespace
asked about; the calling task always has one in its own active
namespace, which `Sys/Kernel/Fork.lean` walks.  This is the pin a checker
admitting 0 beside the recorded tid fails while passing every other pin
in this file; the probe's `set_tid_address#2:ret=0` case states the same
of the Rocq checker.
kernel: kernel/fork.c:set_tid_address; kernel/pid.c:pid_nr_ns@v6.18.46 -/
theorem check_set_tid_address_refuses_tid_zero_later (h : m_tid m = some 7) :
    check_set_tid_address (mkEffect 0 [] []) m = CheckReject := by
  simp only [check_set_tid_address, h, show bv_eqb (0 : word) 7 = false by decide,
    Bool.false_eq_true, ↓reduceIte]

/-- Values outside the envelope are refused on a later call by the same
comparison, not by the envelope test, which a later call never runs:
`2^22` and the all-ones word are each not 7.  The probe's
`set_tid_address#2:ret=2^64` case (`testing/syscall-check/tests/set_tid.c`)
offers the Rocq checker the integer `2^64` itself — the harness's `2^64`
literal is not wrapped to a word, and `max64` is its spelling of the
all-ones word — so it states neither of these two exactly; the all-ones
lie is probed on the first call only (`set_tid_address:ret=max64 -- one`),
which `check_set_tid_address_refuses_all_ones` above pins.
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem check_set_tid_address_refuses_the_envelope_end_later (h : m_tid m = some 7) :
    check_set_tid_address (mkEffect 4194304 [] []) m = CheckReject := by
  simp only [check_set_tid_address, h, show bv_eqb (4194304 : word) 7 = false by decide,
    Bool.false_eq_true, ↓reduceIte]

/-- …and the all-ones word.
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem check_set_tid_address_refuses_all_ones_later (h : m_tid m = some 7) :
    check_set_tid_address (mkEffect 18446744073709551615 [] []) m = CheckReject := by
  simp only [check_set_tid_address, h,
    show bv_eqb (18446744073709551615 : word) 7 = false by decide, Bool.false_eq_true, ↓reduceIte]

/-- The low 32 bits are 7, the recorded tid, and bit 32 is set.
Linux returns a `pid_t`, an `int`, so the return register excludes this value.
This pin fails for a checker that compares only the low 32 bits.
The probe case `set_tid_address#2:ret+4294967296 -- two` in
`testing/syscall-check/tests/set_tid.c` states the same of the Rocq checker.
The Rocq twin is `check_set_tid_address_refuses_the_recorded_tid_past_32_bits` in
`theories/LinuxProcessSem/Checks/Cases/Kernel/Fork.v`.
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem check_set_tid_address_refuses_the_recorded_tid_past_32_bits (h : m_tid m = some 7) :
    check_set_tid_address (mkEffect 4294967303 [] []) m = CheckReject := by
  simp only [check_set_tid_address, h, show bv_eqb (4294967303 : word) 7 = false by decide,
    Bool.false_eq_true, ↓reduceIte]

/-- An errno is refused on a later call for the same reason as on the
first: there is no error path (kernel/fork.c:1749-1751), and -EINVAL,
which `alloc_pid` sets for a bad requested tid (kernel/pid.c:198-199),
is on a path `set_tid_address` never enters.
kernel: kernel/fork.c:set_tid_address; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_set_tid_address_refuses_an_errno_later (h : m_tid m = some 7) :
    check_set_tid_address (mkEffect (errno_ret EINVAL) [] []) m = CheckReject := by
  simp only [check_set_tid_address, h, show bv_eqb (errno_ret EINVAL) 7 = false by decide,
    Bool.false_eq_true, ↓reduceIte]

/-- On the fixture with tid 7 recorded, the same two answers by
computation.
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem check_set_tid_address_repeats_the_recorded_tid_on_the_fixture :
    check_set_tid_address (mkEffect 7 [] []) (with_tid 7 demo_model) = CheckOk (with_tid 7 demo_model) [] := rfl

/-- …and 8 refused on it.
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem check_set_tid_address_refuses_another_tid_on_the_fixture :
    check_set_tid_address (mkEffect 8 [] []) (with_tid 7 demo_model) = CheckReject := rfl

/-- A ledger beside the RIGHT tid is refused on a later call: the effect's
shape is judged before the model is consulted, so the recorded tid buys
no write, zeros or unmap.  The probe's `set_tid_address#2:smuggle-*`
cases state the same of the Rocq checker.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem check_set_tid_address_refuses_a_write_beside_the_recorded_tid :
    check_set_tid_address (mkEffect 7 [(a, [b])] []) (with_tid 7 demo_model) = CheckReject := rfl

/-- …the zeros ledger…
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem check_set_tid_address_refuses_a_zeros_ledger_beside_the_recorded_tid :
    check_set_tid_address (mkEffect 7 [] [(a, 8)]) (with_tid 7 demo_model) = CheckReject := rfl

/-- …and the unmap ledger.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem check_set_tid_address_refuses_an_unmap_beside_the_recorded_tid :
    check_set_tid_address (SyscallEffect.mkEffectU 7 [] [] [(a, 8)] [] []) (with_tid 7 demo_model)
      = CheckReject := rfl

end LaterCall

section NeverDeclines

/-! ## The checker never declines

Every answer is `CheckOk` or `CheckReject`: the arm is inside the modeled
surface whatever the trace shows, which is what
`check_set_tid_address_complete_unmodeled` says of the spec and this
section says of the checker, on the two shapes a trace can take. -/

/-- No effect and no model makes the checker decline.  Stated over the
checker through its soundness half and the spec's own never-declines
pin: a `CheckUnmodeled` answer would put the spec at `Unmodeled`, which
`set_tid_address_never_declines` refuses because the kernel's
`set_tid_address` (kernel/fork.c:1747-1752) has no path the model leaves
open.  That kernel line backs the claim here as it backs the spec pin; a
`model:` line would have hidden a modeled-surface claim behind a model
fact, and `check_lean_pin_evidence.py` cannot tell the two apart in a
`Checks/Cases/Checks/` file (its twin lookup lands on no file).
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem check_set_tid_address_never_declines (eff : SyscallEffect) (m : Model) :
    check_set_tid_address eff m ≠ CheckUnmodeled :=
  fun h => set_tid_address_never_declines
    (SyscallInput.mkInput 96 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
    (check_set_tid_address_sound_unmodeled _ eff m h)

/-- The same fact read off the checker alone, with no lemma of the twin
in the proof: the pin above dies with
`check_set_tid_address_sound_unmodeled`, this one with the checker.  Every
arm answers `CheckOk` or `CheckReject`, because `set_tid_address`
(kernel/fork.c:1747-1752) has no path the model leaves open.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem check_set_tid_address_never_declines_directly (eff : SyscallEffect) (m : Model) :
    check_set_tid_address eff m ≠ CheckUnmodeled := by
  unfold check_set_tid_address
  split
  · split
    · split <;> exact nofun
    · split <;> exact nofun
  · exact nofun

end NeverDeclines

section Witness

/-! ## The witness

`set_tid_address_witness` is one outcome the spec admits at every model,
which is what the progress argument consumes.  It is pinned here at its
two shapes, and its acceptance by the checker is the composition of the
two pins with the checker's. -/

variable (m : Model) (tid : word)

/-- With no tid recorded the witness draws 1 and records it: the tid init
holds, and the lowest `alloc_pid` can store (kernel/pid.c:226).
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem set_tid_address_witness_draws_one (h : m_tid m = none) :
    set_tid_address_witness m = Ok (mkEffect (Z_to_bv 64 1) [] []) (with_tid (Z_to_bv 64 1) m) [] := by
  simp only [set_tid_address_witness, h, ret_outcome]

/-- With a tid recorded the witness repeats it and moves nothing.
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem set_tid_address_witness_repeats_the_recorded_tid (h : m_tid m = some tid) :
    set_tid_address_witness m = Ok (mkEffect tid [] []) m [] := by
  simp only [set_tid_address_witness, h, ret_outcome]

/-- The witness never declines: both of its shapes are `ret_outcome`,
which is an `Ok`, so the progress argument always has an outcome to hand
the checker.
model: `ret_outcome r m` is `Ok (mkEffect r [] []) m []` by definition; no kernel behaviour is claimed -/
theorem set_tid_address_witness_never_declines : set_tid_address_witness m ≠ Unmodeled := by
  intro h
  unfold set_tid_address_witness at h
  cases htid : m_tid m <;> simp only [htid, ret_outcome, reduceCtorEq] at h

/-- The witness's first draw is what the checker accepts, with the same
post-model: the two constructions agree on what the process becomes.
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_set_tid_address_accepts_the_witness_draw (h : m_tid m = none) :
    check_set_tid_address (mkEffect (Z_to_bv 64 1) [] []) m = CheckOk (with_tid (Z_to_bv 64 1) m) [] := by
  simp only [check_set_tid_address, h,
    show (decide (0 < bv_unsigned (Z_to_bv 64 1))
        && decide (bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)) = true by decide, ↓reduceIte]

end Witness

section Clone

/-! ## clone (220) and clone3 (435)

`check_clone` is `clone_spec`'s checker: the flag gate, then the descriptor
gate, then the answer, in the order `SYSCALL_DEFINE5(clone, …)`
(kernel/fork.c:2720-2753, Linux v6.18.46: riscv64 selects CLONE_BACKWARDS,
arch/riscv/Kconfig:97, so its prototype is :2720-2723, and the body
:2741-2753 is every prototype's) splits the flag word (:2743,
:2747), `copy_process` copies the table (`copy_files`, :2173) and
`kernel_clone` returns (:2611-2615, :2624, :2654).  `check_clone3` is
`clone3_spec`'s: the size gate and the read `copy_clone_args_from_user`
makes (:2772-2777), the image `copy_clone_args_from_user` (:2781-2800)
and `clone3_args_valid` (:2853-2879) judge, and
the same resolution with the 88 bytes on the copy-in ledger.  Rocq states
its concrete cases on this arm through the dispatcher
(`Checks/ProcessCreation.v`, `clone_checker_admits_a_pid` and its
neighbours); each is restated here against the checker itself and named
beside its companion.

WHAT THE PINS SEPARATE.  The four obligations tie `check_clone` to
`clone_spec` in both directions, so a spec and a checker moved the same
wrong way — admitting 0, or the neighbour errno -ENFILE, or a pid on a
table with an open regular file — still close them.  Each pin below names
the concrete answer the kernel gives or cannot give, so that the wrong
change fails here and nowhere else.

The pins over the shared `demo_model` (three `FdChannel`s, no tid recorded)
and over the descriptor fixtures of `Checks/Cases/Kernel/Fork.lean` close
by `rfl`, the checker being a closed computation on them; a refusal cited
to a probe's rejecting case is stated as the refusal of every `CheckOk`
(`≠ CheckOk m' evs`), a decline cited to a fail-closed case likewise, and
the `= CheckReject` / `= CheckUnmodeled` companions of the Rocq cases carry
the kernel line.  The pins over a SYMBOLIC model take the gate as a
hypothesis (`clone_no_shared_file_b (m_fds m) = true`) and read the arm it
selects by `simp only`. -/

/-! ### The flag gate: one word in

`clone_fork_flags_b` admits the register `SIGCHLD` (17) and nothing else;
the words below are the ones `testing/syscall-check/tests/clone_spec.c`
walks.  Every decline here is a modeled-surface decline the header of
`Sys/Kernel/Fork.lean` argues: the kernel answers each word. -/

/-- Flag word 0 — no exit signal — declines whatever the effect and
whatever the model; the companion of `Checks/ProcessCreation.v`'s
`clone_checker_declines_flags_zero`, which states it through the
dispatcher on a zero-argument input.  Linux forks on this word
(`SYSCALL_DEFINE5(clone, …)`, kernel/fork.c:2720-2753, Linux v6.18.46,
hands `kernel_clone` an `exit_signal` of 0); the model does not follow.
kernel: kernel/fork.c:clone,kernel_clone@v6.18.46 -/
theorem check_clone_declines_flags_zero (eff : SyscallEffect) (m : Model) :
    check_clone 0 eff m = CheckUnmodeled := rfl

/-- …so nothing offered under word 0 is accepted — a forged pid, or the
-EINVAL the probe's case really records, the kernel's own answer to the
`CLONE_SIGHAND` word its guest issued, which `arg0=` leaves unmutated: the
gate precedes the resolution, so the effect is quantified rather than
spelled.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=0 -- clone -/
theorem check_clone_flags_zero_pid_not_accepted (eff : SyscallEffect) (m' : Model) (evs : List event) :
    check_clone 0 eff demo_model ≠ CheckOk m' evs := nofun

/-- `CLONE_SIGHAND` (0x800), the word the probe's guest really issues, on
its forged-pid case: declined, not answered.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:ret=1234 -- clone -/
theorem check_clone_sighand_word_pid_not_accepted (m' : Model) (evs : List event) :
    check_clone 2048 (mkEffect 1234 [] []) demo_model ≠ CheckOk m' evs := nofun

/-- `SIGCHLD | CLONE_VM` (0x111): a shared address space, declined whatever
the effect.  Linux answers it — `copy_mm` (kernel/fork.c:1543-1544, Linux
v6.18.46) takes a reference to the parent's `mm` (`mmget(oldmm)`) where a
plain fork calls `dup_mm` (:1547).
kernel: kernel/fork.c:copy_mm@v6.18.46 -/
theorem check_clone_declines_clone_vm (eff : SyscallEffect) (m : Model) :
    check_clone 273 eff m = CheckUnmodeled := rfl

/-- `SIGCHLD | CLONE_FILES` (0x411): a shared descriptor table
(`copy_files`, kernel/fork.c:1596-1598, Linux v6.18.46, bumps the count
and returns), declined whatever the effect.
kernel: kernel/fork.c:copy_files@v6.18.46 -/
theorem check_clone_declines_clone_files (eff : SyscallEffect) (m : Model) :
    check_clone 1041 eff m = CheckUnmodeled := rfl

/-- musl's `pthread_create` word (0x7d0f00): a thread, which Linux creates
and this model declines; the argument for declining rather than answering
-EAGAIN is on `Sys/Kernel/Fork.lean`'s `clone_fork_flags_b`.
kernel: kernel/fork.c:clone,copy_process@v6.18.46 -/
theorem check_clone_declines_the_thread_word (eff : SyscallEffect) (m : Model) :
    check_clone 8195840 eff m = CheckUnmodeled := rfl

/-- `SIGCHLD` with bit 32 set (0x1_00000011): a plain fork to Linux, which
reads `lower_32_bits(clone_flags)` (kernel/fork.c:2743, :2747, Linux
v6.18.46), and a decline here, because the gate reads the register whole.
The strict direction, argued on `clone_fork_flags_b`.
kernel: kernel/fork.c:clone@v6.18.46 -/
theorem check_clone_declines_high_bits (eff : SyscallEffect) (m : Model) :
    check_clone 4294967313 eff m = CheckUnmodeled := rfl

/-! ### The answer on the bare table

`demo_model`'s descriptors are the three channels `init_fds` seeds, which
`clone_no_shared_file_b` passes, so the gate is open and the resolution
answers.  These are the companions of `Checks/ProcessCreation.v`'s
`clone_checker_admits_a_pid`, `clone_checker_admits_eagain`,
`clone_checker_refuses_zero`, `clone_checker_refuses_the_envelope_bound`
and `clone_checker_refuses_another_errno`, on the same pid (4242) and the
same errnos, stated against `check_clone` rather than `check_syscall`. -/

/-- A pid inside the envelope is accepted and the child recorded: the
post-model is `with_children demo_model`, not `demo_model`, because
`copy_process` links the new task on `current->children`
(`list_add_tail(&p->sibling, &p->real_parent->children)`,
kernel/fork.c:2398, Linux v6.18.46) and `kernel_clone` returns its
`pid_vnr` (:2624, :2654).  This is the pin that makes the checker compose
with `wait4`'s -ECHILD gate.
kernel: kernel/fork.c:kernel_clone,copy_process@v6.18.46 -/
theorem check_clone_admits_a_pid :
    check_clone 17 (mkEffect 4242 [] []) demo_model = CheckOk (with_children demo_model) [] := rfl

/-- The same on the probe's pid, 1234.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=1234 -- clone -/
theorem check_clone_admits_the_probe_pid :
    check_clone 17 (mkEffect 1234 [] []) demo_model = CheckOk (with_children demo_model) [] := rfl

/-- The recorded child is the ONLY change: a checker answering `CheckOk
demo_model []` on a pid would leave `wait4` at -ECHILD after a fork the
kernel completed.  The kernel's half is the spec pins' — `clone_pid_records_the_child`
and `clone_pid_without_child_rejected` in `Checks/Cases/Kernel/Fork.lean`,
the latter on `clone_fork.c`'s `wait4` case.
model: the post-model is the checker's own construction; `m_has_children (with_children demo_model) = true` against `m_has_children_demo_model` -/
theorem check_clone_pid_moves_the_model :
    check_clone 17 (mkEffect 4242 [] []) demo_model ≠ CheckOk demo_model [] := by
  intro h
  have h2 : m_has_children (with_children demo_model) = m_has_children demo_model := by
    have h1 : check_clone 17 (mkEffect 4242 [] []) demo_model = CheckOk (with_children demo_model) [] := rfl
    rw [h1] at h
    exact congrArg m_has_children (check_result.CheckOk.inj h).1
  rw [m_has_children_demo_model] at h2
  exact absurd h2 (by decide)

/-- The lowest pid the envelope admits, 1.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=1 -- clone -/
theorem check_clone_admits_pid_one :
    check_clone 17 (mkEffect 1 [] []) demo_model = CheckOk (with_children demo_model) [] := rfl

/-- …and the highest, `2^22 - 1`: the largest id `idr_alloc_cyclic`'s
exclusive `end` leaves (lib/idr.c:102, :122, Linux v6.18.46) under a
`pid_max` at `PID_MAX_LIMIT`.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=4194303 -- clone -/
theorem check_clone_admits_the_envelope_top :
    check_clone 17 (mkEffect 4194303 [] []) demo_model = CheckOk (with_children demo_model) [] := rfl

/-- -EAGAIN is accepted with the model UNCHANGED: `copy_process`'s
`RLIMIT_NPROC` test and its `nr_threads >= max_threads` ceiling
(kernel/fork.c:2058-2073, Linux v6.18.46) fail before any child is linked,
and `copy_process` unwinds to `ERR_PTR(retval)`.  Companion of
`clone_checker_admits_eagain`.
kernel: kernel/fork.c:copy_process,kernel_clone@v6.18.46 -/
theorem check_clone_admits_eagain :
    check_clone 17 (mkEffect (errno_ret EAGAIN) [] []) demo_model = CheckOk demo_model [] := rfl

/-- -ENOMEM: every allocation on the path, `dup_task_struct` first
(kernel/fork.c:2019-2021, Linux v6.18.46).
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=-ENOMEM -- clone -/
theorem check_clone_admits_enomem :
    check_clone 17 (mkEffect (errno_ret ENOMEM) [] []) demo_model = CheckOk demo_model [] := rfl

/-- -EMFILE: `alloc_fdtable` under `dup_fd` against a lowered
`sysctl_nr_open` (fs/file.c:194-197, Linux v6.18.46).
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=-EMFILE -- clone -/
theorem check_clone_admits_emfile :
    check_clone 17 (mkEffect (errno_ret EMFILE) [] []) demo_model = CheckOk demo_model [] := rfl

/-- -EACCES: SELinux refusing `process:fork` (`avc_denied`,
security/selinux/avc.c:995-1005, Linux v6.18.46).
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=-EACCES -- clone -/
theorem check_clone_admits_eacces :
    check_clone 17 (mkEffect (errno_ret EACCES) [] []) demo_model = CheckOk demo_model [] := rfl

/-- An errno leaves the model where it was: a checker recording a child on
-EAGAIN would let `wait4` reap a child that was never created.  The
kernel's half is the spec pins' `clone_errno_leaves_the_model` and
`clone_errno_with_child_rejected`, the latter on `clone_wait4_compose.c`.
model: the post-model is the checker's own construction; `m_has_children (with_children demo_model) = true` against `m_has_children_demo_model` -/
theorem check_clone_eagain_does_not_record_a_child :
    check_clone 17 (mkEffect (errno_ret EAGAIN) [] []) demo_model
      ≠ CheckOk (with_children demo_model) [] := by
  intro h
  have h1 : check_clone 17 (mkEffect (errno_ret EAGAIN) [] []) demo_model = CheckOk demo_model [] := rfl
  rw [h1] at h
  have h2 : m_has_children demo_model = m_has_children (with_children demo_model) :=
    congrArg m_has_children (check_result.CheckOk.inj h).1
  rw [m_has_children_demo_model] at h2
  exact absurd h2 (by decide)

/-- ZERO IS REFUSED: 0 is what `copy_thread` seats in the CHILD's a0
(arch/riscv/kernel/process.c:255, Linux v6.18.46); the parent gets
`pid_vnr` of a pid `alloc_pid` drew from `pid_min = 1` (kernel/pid.c:226,
:238-239, Linux v6.18.46).  Companion of `clone_checker_refuses_zero`.
kernel: arch/riscv/kernel/process.c:copy_thread; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_clone_refuses_zero :
    check_clone 17 (mkEffect 0 [] []) demo_model = CheckReject := rfl

/-- …on the probe's rejecting case, stated as the refusal of every `CheckOk`.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=0 -- clone -/
theorem check_clone_zero_not_accepted (m' : Model) (evs : List event) :
    check_clone 17 (mkEffect 0 [] []) demo_model ≠ CheckOk m' evs := nofun

/-- `2^22` itself is refused: `idr_alloc_cyclic` treats its `end` as
exclusive — `max = end > 0 ? end - 1 : INT_MAX` (lib/idr.c:122, Linux
v6.18.46) — and `pid_max` never exceeds `PID_MAX_LIMIT`.  Companion of
`clone_checker_refuses_the_envelope_bound`.
kernel: lib/idr.c:idr_alloc_cyclic; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_clone_refuses_the_envelope_end :
    check_clone 17 (mkEffect 4194304 [] []) demo_model = CheckReject := rfl

/-- …on the probe's case.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=4194304 -- clone -/
theorem check_clone_envelope_end_not_accepted (m' : Model) (evs : List event) :
    check_clone 17 (mkEffect 4194304 [] []) demo_model ≠ CheckOk m' evs := nofun

/-- -ENFILE (23) is refused: the nearest neighbour of the admitted -EMFILE
(24).  It is the system-wide file table's answer (`alloc_empty_file`,
fs/file_table.c:278, Linux v6.18.46), and a fork opens no file — `dup_fd`
takes references to the parent's.  Companion of
`clone_checker_refuses_another_errno`.
kernel: fs/file_table.c:alloc_empty_file@v6.18.46 -/
theorem check_clone_refuses_enfile :
    check_clone 17 (mkEffect (errno_ret ENFILE) [] []) demo_model = CheckReject := rfl

/-- -EINVAL is refused: every -EINVAL of `copy_process`'s own flag checks
(kernel/fork.c:1951-1998, Linux v6.18.46) is a flag combination the word
17 does not have; `kernel_clone`'s own (:2588-2591) needs the pidfd flag
with the parent-tid flag; and the three past them are `alloc_pid`'s on a
`set_tid` array (kernel/pid.c:181-182, :198-200, :205-206, Linux
v6.18.46), which legacy `clone` never passes.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=-EINVAL -- clone -/
theorem check_clone_einval_not_accepted (m' : Model) (evs : List event) :
    check_clone 17 (mkEffect (errno_ret EINVAL) [] []) demo_model ≠ CheckOk m' evs := nofun

/-- -EPERM is refused: every -EPERM of `copy_process` is gated on a
namespace flag this word does not set.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=-EPERM -- clone -/
theorem check_clone_eperm_not_accepted (m' : Model) (evs : List event) :
    check_clone 17 (mkEffect (errno_ret EPERM) [] []) demo_model ≠ CheckOk m' evs := nofun

/-- The all-ones word is refused: read unsigned it is above the envelope,
read as an errno it is -EPERM, which no plain fork returns.
kernel: kernel/fork.c:copy_process; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_clone_refuses_all_ones :
    check_clone 17 (mkEffect 18446744073709551615 [] []) demo_model = CheckReject := rfl

/-- `2^63`, in the band between the two envelopes, is refused: above every
pid — the limit is `2^22` (include/linux/threads.h:34-35, Linux
v6.18.46) — and below every errno, whose magnitude is at most 4095
(include/linux/err.h:18, Linux v6.18.46).
kernel: kernel/fork.c:kernel_clone; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_clone_refuses_the_band_between :
    check_clone 17 (mkEffect 9223372036854775808 [] []) demo_model = CheckReject := rfl

/-! ### The ledgers beside an acceptable pid

Legacy `clone` dereferences none of its pointer arguments for this word:
`kernel_clone`'s `put_user` (kernel/fork.c:2626-2627, Linux v6.18.46) runs
under `CLONE_PARENT_SETTID` alone and `copy_process`'s (:2215-2227) under
`CLONE_PIDFD` alone — legacy `clone` hands `parent_tidptr` to both
(:2744-2746) and the word 17 carries neither flag — `child_tidptr` is
stored for the CHILD's `CLONE_CHILD_SETTID`/`CLONE_CHILD_CLEARTID` (in
`copy_process`, kernel/fork.c:2040 and :2044, Linux v6.18.46), and `dup_mm`
(kernel/fork.c:1479-1518, Linux v6.18.46) copies the parent's mappings
into the child's new `mm` and writes no byte of the parent's memory (the
write-protection it applies is to page-table entries, which no ledger
records).  So every ledger
is refused beside the very pid the bare effect is accepted with. -/

/-- A write beside pid 1234 is refused — any write at any address, the
probe's four bytes at `a2` among them.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=1234,smuggle-write:a2:4 -- clone -/
theorem check_clone_write_not_accepted (a : word) (bs : List byte) (m' : Model) (evs : List event) :
    check_clone 17 (mkEffect 1234 [(a, bs)] []) demo_model ≠ CheckOk m' evs := nofun

/-- …a zeros ledger.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=1234,smuggle-zeros:0x40000000 -- clone -/
theorem check_clone_zeros_not_accepted (m' : Model) (evs : List event) :
    check_clone 17 (mkEffect 1234 [] [(1073741824, 4096)]) demo_model ≠ CheckOk m' evs := nofun

/-- …an unmap ledger.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=1234,smuggle-unmap:0x40000000 -- clone -/
theorem check_clone_unmap_not_accepted (m' : Model) (evs : List event) :
    check_clone 17 (SyscallEffect.mkEffectU 1234 [] [] [(1073741824, 4096)] [] []) demo_model
      ≠ CheckOk m' evs := nofun

/-- …a copies ledger.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=1234,smuggle-copy:a2:a2+8:8 -- clone -/
theorem check_clone_copy_not_accepted (m' : Model) (evs : List event) :
    check_clone 17 (SyscallEffect.mkEffectU 1234 [] [] [] [⟨4096, 4104, 8⟩] []) demo_model
      ≠ CheckOk m' evs := nofun

/-- …and a copy-in ledger: legacy `clone` reads no user memory for this
word (`clone3`'s ledger is the other way round, below).
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone:arg0=17,ret=1234,smuggle-copyin:a2:8 -- clone -/
theorem check_clone_copyin_not_accepted (m' : Model) (evs : List event) :
    check_clone 17 (with_copyins [(4096, 8)] (mkEffect 1234 [] [])) demo_model
      ≠ CheckOk m' evs := nofun

/-- The ledgers are refused beside an ERRNO too.  -EAGAIN with a write is
a lie no kernel tells: `copy_process` unwinds through its bad_fork labels
to an error pointer (kernel/fork.c:2490-2503, Linux v6.18.46) and the two
`put_user`s on the path sit under flags this word lacks.  Every refusal
above is stated on a pid; without this pin an errno arm admitting any
ledger would pass them all.
kernel: kernel/fork.c:copy_process,kernel_clone@v6.18.46 -/
theorem check_clone_write_beside_eagain_not_accepted (a : word) (bs : List byte) (m' : Model) (evs : List event) :
    check_clone 17 (mkEffect (errno_ret EAGAIN) [(a, bs)] []) demo_model ≠ CheckOk m' evs := nofun

/-- …and a copy-in beside -EAGAIN: legacy `clone` reads no user memory on
its failing paths any more than on its succeeding one.
kernel: kernel/fork.c:kernel_clone,copy_process@v6.18.46 -/
theorem check_clone_copyin_beside_eagain_not_accepted (a : word) (n : Nat) (m' : Model) (evs : List event) :
    check_clone 17 (with_copyins [(a, n)] (mkEffect (errno_ret EAGAIN) [] [])) demo_model
      ≠ CheckOk m' evs := nofun

/-- The write refusal as the Rocq cases spell a refusal: `CheckReject`, and
not a decline — the word and the table are inside the modeled surface, so
the checker answers rather than abstains.
kernel: kernel/fork.c:clone,kernel_clone@v6.18.46 -/
theorem check_clone_refuses_a_write :
    check_clone 17 (mkEffect 1234 [(4096, [0])] []) demo_model = CheckReject := rfl

/-! ### The caller's own tid

`alloc_pid` hands out a FREE pid (kernel/pid.c:238-239, Linux v6.18.46),
and the caller's own is in use; the model knows the caller's tid once an
identity call has recorded it (`with_tid`), and `clone_pid_ok_b` excludes
it from then on.  Until then the conjunct is vacuous — the widening
`bugs/clone-retires-no-pid.md` records, which `check_clone_admits_a_pid`
above shows on the bare fixture. -/

/-- With tid 1234 recorded, pid 1234 is refused.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate set_tid_address:ret=1234 --mutate clone:arg0=17,ret=1234 -- tid -/
theorem check_clone_own_tid_not_accepted (m' : Model) (evs : List event) :
    check_clone 17 (mkEffect 1234 [] []) (with_tid 1234 demo_model) ≠ CheckOk m' evs := nofun

/-- …as `CheckReject`.
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_clone_refuses_the_own_tid :
    check_clone 17 (mkEffect 7 [] []) (with_tid 7 demo_model) = CheckReject := rfl

/-- …and the neighbouring pid 1235 accepted, with the tid carried into the
post-model beside the recorded child.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate set_tid_address:ret=1234 --mutate clone:arg0=17,ret=1235 -- tid -/
theorem check_clone_admits_another_pid_with_a_tid :
    check_clone 17 (mkEffect 1235 [] []) (with_tid 1234 demo_model)
      = CheckOk (with_children (with_tid 1234 demo_model)) [] := rfl

/-! ### The descriptor gate

`copy_files` (kernel/fork.c:1579-1607, Linux v6.18.46) duplicates the
table through `dup_fd` (fs/file.c:383), whose loop takes a second
reference to every open `struct file` (:458), so the two tables share
every description's `f_pos`.  `State.FdEntry` inlines the offset of a
regular file and the receive script of a socket into the descriptor, so
the checker declines on any such entry — BEFORE looking at the effect,
which is what the quantified pins say — and answers on the kinds whose
shared state nothing modeled in this process can observe.  The fixtures are
`Checks/Cases/Kernel/Fork.lean`'s. -/

/-- A regular file open for reading at fd 3 closes the gate on pid 4242:
the companion of `Checks/ProcessCreation.v`'s
`clone_checker_declines_with_a_file_open`, whose table holds an `FdFile`
at 3 as `open_file_model` does.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem check_clone_declines_with_a_file_open :
    check_clone 17 (mkEffect 4242 [] []) open_file_model = CheckUnmodeled := rfl

/-- …whatever the effect: the gate is on the table, not on the answer.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem check_clone_declines_with_a_file_open_on_any_effect (eff : SyscallEffect) :
    check_clone 17 eff open_file_model = CheckUnmodeled := by
  simp only [check_clone, check_clone_resolve, show clone_fork_flags_b 17 = true by decide,
    show clone_no_shared_file_b (m_fds open_file_model) = false by decide, Bool.not_false,
    ↓reduceIte]

/-- …so a pid on that table is not accepted, on the probe's read-only file.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=17,ret=1234 -- openread -/
theorem check_clone_file_open_pid_not_accepted (m' : Model) (evs : List event) :
    check_clone 17 (mkEffect 1234 [] []) open_file_model ≠ CheckOk m' evs := nofun

/-- …and -EAGAIN on that table is declined too, although `copy_process`'s
`RLIMIT_NPROC` test (kernel/fork.c:2058-2064, Linux v6.18.46) could really
answer it: the decline precedes the resolution, so no errno of the
resolution is reachable through a closed gate.
kernel: kernel/fork.c:copy_process,copy_files@v6.18.46 -/
theorem check_clone_declines_eagain_with_a_file_open :
    check_clone 17 (mkEffect (errno_ret EAGAIN) [] []) open_file_model = CheckUnmodeled := rfl

/-- A file open for WRITING closes it the same way: the probe's `openfile`.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone --mutate clone:arg0=17,ret=1234 -- openfile -/
theorem check_clone_wfile_open_pid_not_accepted (m' : Model) (evs : List event) :
    check_clone 17 (mkEffect 1234 [] []) open_wfile_model ≠ CheckOk m' evs := nofun

/-- A socket closes it: its receive script is inlined into the descriptor.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem check_clone_declines_with_a_socket_open :
    check_clone 17 (mkEffect 4242 [] []) open_socket_model = CheckUnmodeled := rfl

/-- A pipe end closes it: after `dup_fd` both tables name one `struct
file` and one `pipe_inode_info`, so a child that reads drains bytes the
parent then cannot (`anon_pipe_read`, fs/pipe.c:269-273, Linux v6.18.46),
and a child that closes its copy does not drop the writer count
(`pipe_release`, :730-733, runs once for the shared file) that decides
whether the peer sees EOF or blocks — the spec's own reason; an `FdEntry`
carries no per-description state and nothing counts ends.
kernel: fs/pipe.c:anon_pipe_read,pipe_release; kernel/fork.c:copy_files@v6.18.46 -/
theorem check_clone_declines_with_a_pipe_open :
    check_clone 17 (mkEffect 4242 [] []) open_pipe_model = CheckUnmodeled := rfl

/-- A directory does NOT close the gate: its `f_pos` is shared exactly as
a file's, but no modeled syscall OF THIS PROCESS moves a directory
position — `Sys/Fs/Readdir.lean`'s -EINVAL arm rests on that position-0
premise and advances nothing — so the call is answered as on the bare
table.  A child's own `getdents64` through the shared `struct file` would
move it, and the parent's next short-count call would then read 0 from
Linux where the model says -EINVAL: the child's action, outside the model
with the rest of the child (bugs/clone-child-not-in-the-model.md, which
does not yet name this route), and a question for the spec's gate —
`clone_no_shared_file_b`, Rocq's and its Lean twin's, whose docstrings
carry the unqualified sentence — not for this checker.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone:arg0=17,ret=1234 -- opendir -/
theorem check_clone_answers_with_a_dir_open :
    check_clone 17 (mkEffect 1234 [] []) open_dir_model = CheckOk (with_children open_dir_model) [] := rfl

/-- /dev/null does not close it either: `null_lseek` (drivers/char/mem.c:561,
Linux v6.18.46) pins the shared `f_pos` at 0 and `read_null`/`write_null`
(:412-421) never move it.
kernel: drivers/char/mem.c:null_lseek,read_null,write_null@v6.18.46 -/
theorem check_clone_answers_with_devnull_open :
    check_clone 17 (mkEffect 1234 [] []) open_devnull_model
      = CheckOk (with_children open_devnull_model) [] := rfl

/-- Nor /dev/urandom: `urandom_read_iter` (drivers/char/random.c:1453,
Linux v6.18.46) reads no position and the bytes come from the run's
declared stream.
kernel: drivers/char/random.c:urandom_read_iter; fs/read_write.c:noop_llseek@v6.18.46 -/
theorem check_clone_answers_with_urandom_open :
    check_clone 17 (mkEffect 1234 [] []) open_urandom_model
      = CheckOk (with_children open_urandom_model) [] := rfl

/-- Nor a fourth channel, `dup(1)` at fd 3: the gate is on the descriptor's
KIND, and an `FdChannel` anywhere in the table is the hole the three
seeds already are.
kernel: kernel/fork.c:copy_files@v6.18.46 -/
theorem check_clone_answers_with_an_extra_channel :
    check_clone 17 (mkEffect 1234 [] []) open_channel_model
      = CheckOk (with_children open_channel_model) [] := rfl

/-! ### The gate read symbolically

The same facts over ANY model the gate lets through, or shuts on: what
the fixtures above show one table at a time. -/

/-- With the gate open, -EAGAIN is accepted and the model left where it
was — over every such model.
kernel: kernel/fork.c:copy_process,kernel_clone@v6.18.46 -/
theorem check_clone_admits_eagain_with_the_gate_open (m : Model)
    (hg : clone_no_shared_file_b (m_fds m) = true) :
    check_clone 17 (mkEffect (errno_ret EAGAIN) [] []) m = CheckOk m [] := by
  simp only [check_clone, check_clone_resolve, check_clone_answer,
    show clone_fork_flags_b 17 = true by decide, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show errno_ret_in clone_errnos (errno_ret EAGAIN) = true by decide]

/-- With the gate open and no tid recorded, pid 4242 is accepted and the
child recorded — over every such model.
kernel: kernel/fork.c:kernel_clone,copy_process; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_clone_admits_a_pid_with_the_gate_open (m : Model)
    (hg : clone_no_shared_file_b (m_fds m) = true) (htid : m_tid m = none) :
    check_clone 17 (mkEffect 4242 [] []) m = CheckOk (with_children m) [] := by
  have hp : clone_pid_ok_b m 4242 = true := by
    simp only [clone_pid_ok_b, htid]
    decide
  simp only [check_clone, check_clone_resolve, check_clone_answer,
    show clone_fork_flags_b 17 = true by decide, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show errno_ret_in clone_errnos 4242 = false by decide, hp]

/-- With the gate open, zero is refused over every model: the pid guard's
first conjunct, `0 < bv_unsigned r`, is `pid_min = 1` (kernel/pid.c:226,
Linux v6.18.46), and no recorded tid changes it.
kernel: kernel/pid.c:alloc_pid; arch/riscv/kernel/process.c:copy_thread@v6.18.46 -/
theorem check_clone_refuses_zero_with_the_gate_open (m : Model)
    (hg : clone_no_shared_file_b (m_fds m) = true) :
    check_clone 17 (mkEffect 0 [] []) m = CheckReject := by
  have hp : clone_pid_ok_b m 0 = false := by
    simp only [clone_pid_ok_b, show decide (0 < bv_unsigned (0 : word)) = false by decide,
      Bool.false_and]
  simp only [check_clone, check_clone_resolve, check_clone_answer,
    show clone_fork_flags_b 17 = true by decide, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show errno_ret_in clone_errnos 0 = false by decide, hp]

/-- With the gate open the checker never declines: every answer is
`CheckOk` or `CheckReject`.  `check_clone_sound_unmodeled` says as much
through the spec, and the spec pins' own `clone_fork_never_declines`
(`Checks/Cases/Kernel/Fork.lean`) says it on `demo_model` alone; this one
is read off the checker, over every model
with the gate open.
kernel: kernel/fork.c:clone,kernel_clone@v6.18.46 -/
theorem check_clone_never_declines_with_the_gate_open (eff : SyscallEffect) (m : Model)
    (hg : clone_no_shared_file_b (m_fds m) = true) :
    check_clone 17 eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_clone check_clone_resolve at h
  simp only [show clone_fork_flags_b 17 = true by decide, hg, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte] at h
  split at h
  · unfold check_clone_answer at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
  · cases h

/-- …and the same through `check_clone_resolve_unmodeled_inv`, the helper
`check_clone_resolve_sound_unmodeled` leans on: stated here so the helper's
disjunction is read on the concrete word once, outside the obligation
proofs that consume it.
kernel: kernel/fork.c:clone,kernel_clone@v6.18.46 -/
theorem check_clone_never_declines_with_the_gate_open_by_inversion (eff : SyscallEffect) (m : Model)
    (hg : clone_no_shared_file_b (m_fds m) = true) :
    check_clone 17 eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_clone at h
  simp only [show clone_fork_flags_b 17 = true by decide, ↓reduceIte] at h
  have hc := check_clone_resolve_unmodeled_inv eff m h
  rw [hg] at hc
  cases hc

/-- What the resolution ACCEPTS is the dichotomy `Checks/ProcessCreation.v`'s
`clone_resolve_declines_or_sets_children` states of the spec, read off the
checker over every model and every effect: an errno's answer is the model
handed in — `copy_process` unwinds through its `bad_fork_*` labels to an
error pointer (kernel/fork.c:2490-2503, Linux v6.18.46) and links nothing —
and a pid's answer has a child recorded, `list_add_tail` on the parent's
`children` (:2398).  `check_clone_pid_moves_the_model` and
`check_clone_eagain_does_not_record_a_child` above are this at one model;
the dispatcher-level `check_clone_success_sets_children` waits on the arm's
registration, as `Checks/ProcessCreation.lean` says.
kernel: kernel/fork.c:copy_process,kernel_clone@v6.18.46 -/
theorem check_clone_resolve_accepts_into_the_dichotomy (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_clone_resolve eff m = CheckOk m' evs) :
    (errno_ret_in clone_errnos eff.eff_ret = true → m' = m) ∧
    (errno_ret_in clone_errnos eff.eff_ret = false → m_has_children m' = true) := by
  obtain ⟨_, ret, rfl, ha⟩ := check_clone_resolve_ok_inv eff m m' evs h
  unfold check_clone_answer at ha
  cases hin : errno_ret_in clone_errnos ret with
  | true =>
      simp only [hin, ↓reduceIte, check_result.CheckOk.injEq] at ha
      exact ⟨fun _ => ha.1.symm, fun hf => Bool.noConfusion hf⟩
  | false =>
      simp only [hin, Bool.false_eq_true, ↓reduceIte] at ha
      cases hp : clone_pid_ok_b m ret with
      | false => simp only [hp, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at ha
      | true =>
          simp only [hp, ↓reduceIte, check_result.CheckOk.injEq] at ha
          refine ⟨(fun ht => Bool.noConfusion ht), fun _ => ?_⟩
          rw [← ha.1]
          rfl

/-- …and through `check_clone` on the fork word.
kernel: kernel/fork.c:copy_process,kernel_clone@v6.18.46 -/
theorem check_clone_accepts_into_the_dichotomy (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_clone 17 eff m = CheckOk m' evs) :
    (errno_ret_in clone_errnos eff.eff_ret = true → m' = m) ∧
    (errno_ret_in clone_errnos eff.eff_ret = false → m_has_children m' = true) := by
  unfold check_clone at h
  simp only [show clone_fork_flags_b 17 = true by decide, ↓reduceIte] at h
  exact check_clone_resolve_accepts_into_the_dichotomy eff m m' evs h

/-- With the gate SHUT the checker declines whatever the effect and
whatever the flag word — the companion of `Checks/ProcessCreation.v`'s
`clone_open_file_unmodeled`, which states it of the spec over every
`flags` as well: a word the flag gate refuses declines there, and the one
it admits declines at the descriptor gate.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem check_clone_declines_with_the_gate_shut (flags : word) (eff : SyscallEffect) (m : Model)
    (hg : clone_no_shared_file_b (m_fds m) = false) :
    check_clone flags eff m = CheckUnmodeled := by
  unfold check_clone
  split
  · simp only [check_clone_resolve, hg, Bool.not_false, ↓reduceIte]
  · rfl

/-! ### clone3: the size gate

`copy_clone_args_from_user` (kernel/fork.c:2756-2822, Linux v6.18.46)
tests `size` before copying anything — -E2BIG above `PAGE_SIZE`
(:2772-2773), -EINVAL below `CLONE_ARGS_SIZE_VER0` (:2774-2775) — and
inside that range `copy_struct_from_user` accepts every size whose bytes
past the struct are zero (include/linux/uaccess.h:402-405, Linux
v6.18.46; -E2BIG when the excess is readable and not zero, the zero
check's own -EFAULT when it is not readable, :403-405).  The model
answers 88 alone and declines the rest, the kernel's own answer unsaid;
`size` is a `size_t`, so the register is compared whole. -/

/-- Size 0 declines whatever the input, the effect and the model: the
companion of `Checks/ProcessCreation.v`'s
`clone3_checker_declines_size_zero`.  The kernel's -EINVAL
(kernel/fork.c:2774-2775, Linux v6.18.46) is not given.
kernel: kernel/fork.c:copy_clone_args_from_user@v6.18.46 -/
theorem check_clone3_declines_size_zero (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_clone3 i 4096 0 eff m = CheckUnmodeled := rfl

/-- `CLONE_ARGS_SIZE_VER0` (64), the first published struct, which the
kernel zero-fills and forks on: declined.
kernel: kernel/fork.c:copy_clone_args_from_user@v6.18.46 -/
theorem check_clone3_declines_ver0 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_clone3 i 4096 64 eff m = CheckUnmodeled := rfl

/-- …so nothing is accepted under it, whatever the effect — a pid with a
64-byte ledger, or the -EINVAL with no ledger the probe's case really
records, since `arg1=` rewrites the input alone and the harness ledgers a
`clone3` read only at size 88.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=64 -- c3 -/
theorem check_clone3_ver0_pid_not_accepted (eff : SyscallEffect) (m' : Model) (evs : List event) :
    check_clone3 (c3_input 64 fork_mem) 4096 64 eff demo_model ≠ CheckOk m' evs := nofun

/-- One byte short of the struct, whatever the effect.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=87 -- c3 -/
theorem check_clone3_short_size_pid_not_accepted (eff : SyscallEffect) (m' : Model) (evs : List event) :
    check_clone3 (c3_input 87 fork_mem) 4096 87 eff demo_model ≠ CheckOk m' evs := nofun

/-- One byte long, which the kernel accepts when the excess byte is zero
(`copy_struct_from_user`, include/linux/uaccess.h:402-405, Linux v6.18.46):
declined.
kernel: kernel/fork.c:copy_clone_args_from_user; include/linux/uaccess.h:copy_struct_from_user@v6.18.46 -/
theorem check_clone3_declines_long_size (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_clone3 i 4096 89 eff m = CheckUnmodeled := rfl

/-- `88 + 2^32`: the size test is not truncated — `size_t` is 64 bits —
so a register whose low half reads 88 is not 88.
kernel: kernel/fork.c:copy_clone_args_from_user@v6.18.46 -/
theorem check_clone3_declines_size_high_bits (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_clone3 i 4096 4294967384 eff m = CheckUnmodeled := rfl

/-! ### clone3: the read

`copy_struct_from_user` (include/linux/uaccess.h:389-411, Linux v6.18.46)
either moves the whole struct (`copy_from_user`, :408-409) or answers
-EFAULT; the model declines the unreadable struct rather than answer it,
and charges nothing to the ledger for a copy that faulted. -/

/-- Nothing mapped: declined whatever the effect and the model.
kernel: include/linux/uaccess.h:copy_struct_from_user; kernel/fork.c:copy_clone_args_from_user@v6.18.46 -/
theorem check_clone3_declines_nothing_mapped (eff : SyscallEffect) (m : Model) :
    check_clone3 (c3_input 88 (fun _ => none)) 4096 88 eff m = CheckUnmodeled := rfl

/-- …so nothing is accepted over unreadable memory, whatever the effect —
a pid with the full ledger, or the -EINVAL with none that the probe's case
really records: its guest passed size 0 and `copy_clone_args_from_user`
refused before any read (kernel/fork.c:2774-2775, Linux v6.18.46); the
mutation hands the model size 88 and no memory.
probe: testing/syscall-check/tests/clone_spec.c#fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88,mem-none -- c3 -/
theorem check_clone3_nothing_mapped_pid_not_accepted (eff : SyscallEffect) (m' : Model) (evs : List event) :
    check_clone3 (c3_input 88 (fun _ => none)) 4096 88 eff demo_model ≠ CheckOk m' evs := nofun

/-- The last byte unmapped: 87 readable bytes are not the struct.  A
checker reading only `CLONE_ARGS_SIZE_VER1` bytes would accept this call.
kernel: include/linux/uaccess.h:copy_struct_from_user@v6.18.46 -/
theorem check_clone3_declines_last_byte_unmapped (eff : SyscallEffect) (m : Model) :
    check_clone3 (c3_input 88 (pin_mem 4096 (fork_args.take 87))) 4096 88 eff m = CheckUnmodeled := rfl

/-- The register one byte along on the same memory: 87 bytes of the image
and one unmapped byte, declined.  With `check_clone3_admits_a_pid_at_another_register`
below, the read's address is the register and nothing else.
kernel: kernel/fork.c:clone3,copy_clone_args_from_user@v6.18.46 -/
theorem check_clone3_declines_a_register_off_the_image (eff : SyscallEffect) (m : Model) :
    check_clone3 (c3_input 88 fork_mem) 4097 88 eff m = CheckUnmodeled := rfl

/-! ### clone3: the image

Every field but `exit_signal` must be zero, and `exit_signal` must be
`SIGCHLD`; `clone3_args_valid` (kernel/fork.c:2853-2879, Linux v6.18.46)
accepts several of the images below and this model declines each, for the
reasons `Checks/Cases/Kernel/Fork.lean` gives field by field.  The image
gate runs on the bytes the read returned, so the pins fix the memory and
leave the effect and the model free. -/

/-- `flags = CLONE_VM` (0x100): declined, as the legacy word 0x111 is.
kernel: kernel/fork.c:clone3_args_valid,copy_clone_args_from_user@v6.18.46 -/
theorem check_clone3_declines_clone_vm (eff : SyscallEffect) (m : Model) :
    check_clone3 (c3_input 88 (pin_mem 4096 (fork_args_with 0 256))) 4096 88 eff m
      = CheckUnmodeled := rfl

/-- `exit_signal = SIGTERM` (15): a fork reporting another signal, which
the kernel accepts (`copy_clone_args_from_user`, kernel/fork.c:2794-2796,
Linux v6.18.46) and the model declines.
kernel: kernel/fork.c:copy_clone_args_from_user@v6.18.46 -/
theorem check_clone3_declines_sigterm (eff : SyscallEffect) (m : Model) :
    check_clone3 (c3_input 88 (pin_mem 4096 (fork_args_with 4 15))) 4096 88 eff m
      = CheckUnmodeled := rfl

/-- `stack` alone: `clone3_stack_valid` refuses it (kernel/fork.c:2839-2840,
Linux v6.18.46); the model declines rather than give the -EINVAL.
kernel: kernel/fork.c:clone3_stack_valid,clone3_args_valid@v6.18.46 -/
theorem check_clone3_declines_a_stack (eff : SyscallEffect) (m : Model) :
    check_clone3 (c3_input 88 (pin_mem 4096 (fork_args_with 5 1))) 4096 88 eff m
      = CheckUnmodeled := rfl

/-! ### clone3: the answer, with the ledger

On the fixture memory `fork_mem` (the plain-fork image at 4096) and size
88, the resolution is legacy `clone`'s, and EVERY arm carries the 88
bytes read on the copy-in ledger: `copy_struct_from_user` faults the
struct in (kernel/fork.c:2777, Linux v6.18.46) before `kernel_clone`
(:2913) can fail, so an errno returned past the read has read them too.  The
descriptor gate is the same gate, reached through the other entry
point. -/

/-- A pid with the ledger is accepted and the child recorded.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone3:arg1=88,ret=1234 -- c3 -/
theorem check_clone3_admits_a_pid :
    check_clone3 (c3_input 88 fork_mem) 4096 88 (with_copyins [(4096, 88)] (mkEffect 1234 [] []))
      demo_model = CheckOk (with_children demo_model) [] := rfl

/-- …the envelope's top, 4194303.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone3:arg1=88,ret=4194303 -- c3 -/
theorem check_clone3_admits_the_envelope_top :
    check_clone3 (c3_input 88 fork_mem) 4096 88 (with_copyins [(4096, 88)] (mkEffect 4194303 [] []))
      demo_model = CheckOk (with_children demo_model) [] := rfl

/-- …and its foot, 1, through this entry point too: `pid_min` starts at 1
(kernel/pid.c:226, Linux v6.18.46) and `alloc_pid` draws from it
(:238-239).  A `clone3` guard reading `1 < pid` would pass every other pin
in both Cases files.
kernel: kernel/pid.c:alloc_pid; lib/idr.c:idr_alloc_cyclic@v6.18.46 -/
theorem check_clone3_admits_pid_one :
    check_clone3 (c3_input 88 fork_mem) 4096 88 (with_copyins [(4096, 88)] (mkEffect 1 [] []))
      demo_model = CheckOk (with_children demo_model) [] := rfl

/-- The struct is read at the REGISTER and the ledger compared to it: the
image at 8192, `uargs` 8192 and the ledger at 8192 answer as at 4096.
Every other clone3 pin in this file puts the image and the register at
4096, so a checker with that address wired into the read or the ledger
test — which the spec pins cannot tell apart from the spec, having fixed
the register the same way — passed them all; with the decline pin at 4097
below, neither address can be a constant.
kernel: kernel/fork.c:clone3,copy_clone_args_from_user@v6.18.46 -/
theorem check_clone3_admits_a_pid_at_another_register :
    check_clone3 (c3_input 88 (pin_mem 8192 fork_args)) 8192 88
      (with_copyins [(8192, 88)] (mkEffect 1234 [] [])) demo_model
      = CheckOk (with_children demo_model) [] := rfl

/-- The recorded child is the ONLY change through this entry point too: a
checker answering `CheckOk demo_model []` on a pid with the ledger would
leave `wait4` at -ECHILD after a fork the kernel completed; the kernel's
half is the spec pins', as for `check_clone_pid_moves_the_model`.
model: the post-model is the checker's own construction; `m_has_children (with_children demo_model) = true` against `m_has_children_demo_model` -/
theorem check_clone3_pid_moves_the_model :
    check_clone3 (c3_input 88 fork_mem) 4096 88 (with_copyins [(4096, 88)] (mkEffect 1234 [] []))
      demo_model ≠ CheckOk demo_model [] := by
  intro h
  have h2 : m_has_children (with_children demo_model) = m_has_children demo_model := by
    have h1 : check_clone3 (c3_input 88 fork_mem) 4096 88
        (with_copyins [(4096, 88)] (mkEffect 1234 [] [])) demo_model
        = CheckOk (with_children demo_model) [] := rfl
    rw [h1] at h
    exact congrArg m_has_children (check_result.CheckOk.inj h).1
  rw [m_has_children_demo_model] at h2
  exact absurd h2 (by decide)

/-- -EAGAIN with the ledger is accepted, the model unchanged: the errno
arm is past the read.  This effect is also what `clone3_witness` offers,
below, so the pin is the checker accepting the witness.
probe: testing/syscall-check/tests/clone_spec.c#conform --mutate clone3:arg1=88,ret=-EAGAIN -- c3 -/
theorem check_clone3_admits_eagain_with_the_ledger :
    check_clone3 (c3_input 88 fork_mem) 4096 88
      (with_copyins [(4096, 88)] (mkEffect (errno_ret EAGAIN) [] [])) demo_model
      = CheckOk demo_model [] := rfl

/-- Zero is refused through this entry point too: the same `copy_thread`
(arch/riscv/kernel/process.c:255, Linux v6.18.46) seats it in the child.
kernel: arch/riscv/kernel/process.c:copy_thread; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem check_clone3_refuses_zero :
    check_clone3 (c3_input 88 fork_mem) 4096 88 (with_copyins [(4096, 88)] (mkEffect 0 [] []))
      demo_model = CheckReject := rfl

/-- …on the probe's case.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=0 -- c3 -/
theorem check_clone3_zero_not_accepted (m' : Model) (evs : List event) :
    check_clone3 (c3_input 88 fork_mem) 4096 88 (with_copyins [(4096, 88)] (mkEffect 0 [] []))
      demo_model ≠ CheckOk m' evs := nofun

/-- `2^22` is refused through this entry point too.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=4194304 -- c3 -/
theorem check_clone3_envelope_end_not_accepted (m' : Model) (evs : List event) :
    check_clone3 (c3_input 88 fork_mem) 4096 88 (with_copyins [(4096, 88)] (mkEffect 4194304 [] []))
      demo_model ≠ CheckOk m' evs := nofun

/-- -ENOSYS (38) is refused — LINUX's answer alone, as the spec pin
`clone3_enosys_rejected` (`Checks/Cases/Kernel/Fork.lean`) says in full.
On the pinned kernel no path of `clone3` produces it: the number is wired,
and the refusals of `copy_clone_args_from_user` are -EINVAL, -E2BIG and
-EFAULT (kernel/fork.c:2772-2818, Linux v6.18.46).  QEMU's user-mode
emulation at v11.1.1 has no `clone3` handler and answers -ENOSYS with
nothing read, so the refusal is the model's and not the supported set's;
bugs/clone3-enosys-arm-admits-linux-alone.md records the gap, which is
`clone_errnos`'s and reaches this checker through the obligations.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=-ENOSYS -- c3 -/
theorem check_clone3_enosys_not_accepted (m' : Model) (evs : List event) :
    check_clone3 (c3_input 88 fork_mem) 4096 88
      (with_copyins [(4096, 88)] (mkEffect (errno_ret 38) [] [])) demo_model ≠ CheckOk m' evs := nofun

/-- THE LEDGER IS REQUIRED: the same pid with the ledger dropped is
refused, because the 88 bytes were read.  This is the case that separates
`clone3`'s checker from `clone`'s.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=1234,drop-copyins -- c3 -/
theorem check_clone3_dropped_ledger_not_accepted (m' : Model) (evs : List event) :
    check_clone3 (c3_input 88 fork_mem) 4096 88 (mkEffect 1234 [] []) demo_model
      ≠ CheckOk m' evs := nofun

/-- …and so is the errno with the ledger dropped: the errno arm is PAST the
read.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=-EAGAIN,drop-copyins -- c3 -/
theorem check_clone3_eagain_without_the_ledger_not_accepted (m' : Model) (evs : List event) :
    check_clone3 (c3_input 88 fork_mem) 4096 88 (mkEffect (errno_ret EAGAIN) [] []) demo_model
      ≠ CheckOk m' evs := nofun

/-- A ledger one byte too long: 89 is not what `copy_struct_from_user`
faulted in.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=1234,grow-copyins:1 -- c3 -/
theorem check_clone3_grown_ledger_not_accepted (m' : Model) (evs : List event) :
    check_clone3 (c3_input 88 fork_mem) 4096 88 (with_copyins [(4096, 89)] (mkEffect 1234 [] []))
      demo_model ≠ CheckOk m' evs := nofun

/-- …nor one byte too short: the copy is `size` bytes, the caller's 88
(include/linux/uaccess.h:408-409, Linux v6.18.46), so 87 is not what was
faulted in either.
kernel: include/linux/uaccess.h:copy_struct_from_user@v6.18.46 -/
theorem check_clone3_shrunk_ledger_not_accepted (m' : Model) (evs : List event) :
    check_clone3 (c3_input 88 fork_mem) 4096 88 (with_copyins [(4096, 87)] (mkEffect 1234 [] []))
      demo_model ≠ CheckOk m' evs := nofun

/-- …nor one range shifted one byte along.
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=1234,shift-copyins:1 -- c3 -/
theorem check_clone3_shifted_ledger_not_accepted (m' : Model) (evs : List event) :
    check_clone3 (c3_input 88 fork_mem) 4096 88 (with_copyins [(4097, 88)] (mkEffect 1234 [] []))
      demo_model ≠ CheckOk m' evs := nofun

/-- Two copies of the range: `copy_struct_from_user` reads the struct once
(include/linux/uaccess.h:408-409, Linux v6.18.46), and the ledger is
exactly one entry.
kernel: include/linux/uaccess.h:copy_struct_from_user@v6.18.46 -/
theorem check_clone3_refuses_a_doubled_ledger :
    check_clone3 (c3_input 88 fork_mem) 4096 88
      (with_copyins [(4096, 88), (4096, 88)] (mkEffect 1234 [] [])) demo_model = CheckReject := rfl

/-- A write beside the ledger is refused: `clone3` writes no parent memory
for this image — its `flags` word is 0, so neither `put_user` runs,
`copy_process`'s under `CLONE_PIDFD` (kernel/fork.c:2215-2227, Linux
v6.18.46) nor `kernel_clone`'s under `CLONE_PARENT_SETTID` (:2626-2627).
probe: testing/syscall-check/tests/clone_spec.c#reject --mutate clone3:arg1=88,ret=1234,smuggle-write:a0:1 -- c3 -/
theorem check_clone3_write_not_accepted (a : word) (bs : List byte) (m' : Model) (evs : List event) :
    check_clone3 (c3_input 88 fork_mem) 4096 88
      (SyscallEffect.mkEffectU 1234 [(a, bs)] [] [] [] [(4096, 88)]) demo_model
      ≠ CheckOk m' evs := nofun

/-- …and beside -EAGAIN with the ledger: the read happened, the write did
not.  `clone3` reads the 88 bytes (kernel/fork.c:2906, Linux v6.18.46)
before `kernel_clone` (:2913) can fail, and no write the image's zero
`flags` could enable follows a failure.
kernel: kernel/fork.c:clone3,copy_process@v6.18.46 -/
theorem check_clone3_write_beside_eagain_not_accepted (a : word) (bs : List byte) (m' : Model) (evs : List event) :
    check_clone3 (c3_input 88 fork_mem) 4096 88
      (SyscallEffect.mkEffectU (errno_ret EAGAIN) [(a, bs)] [] [] [] [(4096, 88)]) demo_model
      ≠ CheckOk m' evs := nofun

/-- …a zeros ledger beside it: `clone3` (kernel/fork.c:2892-2914, Linux
v6.18.46) zeroes no parent memory on any path.
kernel: kernel/fork.c:clone3,kernel_clone@v6.18.46 -/
theorem check_clone3_zeros_beside_the_ledger_not_accepted (m' : Model) (evs : List event) :
    check_clone3 (c3_input 88 fork_mem) 4096 88
      (SyscallEffect.mkEffectU 1234 [] [(1073741824, 4096)] [] [] [(4096, 88)]) demo_model
      ≠ CheckOk m' evs := nofun

/-- …an unmap ledger beside it.
kernel: kernel/fork.c:clone3,kernel_clone@v6.18.46 -/
theorem check_clone3_unmap_beside_the_ledger_not_accepted (m' : Model) (evs : List event) :
    check_clone3 (c3_input 88 fork_mem) 4096 88
      (SyscallEffect.mkEffectU 1234 [] [] [(1073741824, 4096)] [] [(4096, 88)]) demo_model
      ≠ CheckOk m' evs := nofun

/-- …a copies ledger beside it.
kernel: kernel/fork.c:clone3,kernel_clone@v6.18.46 -/
theorem check_clone3_copy_beside_the_ledger_not_accepted (m' : Model) (evs : List event) :
    check_clone3 (c3_input 88 fork_mem) 4096 88
      (SyscallEffect.mkEffectU 1234 [] [] [] [⟨4096, 4104, 8⟩] [(4096, 88)]) demo_model
      ≠ CheckOk m' evs := nofun

/-- The descriptor gate through `clone3`: an open regular file declines
the call with the right ledger and a good pid, because `clone3`
(kernel/fork.c:2892-2914, Linux v6.18.46) reaches `kernel_clone` (:2913)
and thereby the same `copy_files` (:2173).
kernel: kernel/fork.c:clone3,kernel_clone,copy_files@v6.18.46 -/
theorem check_clone3_declines_with_a_file_open :
    check_clone3 (c3_input 88 fork_mem) 4096 88 (with_copyins [(4096, 88)] (mkEffect 1234 [] []))
      open_file_model = CheckUnmodeled := rfl

/-- …whatever the effect: the gate is on the table, reached through this
entry point as through the other.
kernel: kernel/fork.c:clone3,kernel_clone,copy_files@v6.18.46 -/
theorem check_clone3_declines_with_a_file_open_on_any_effect (eff : SyscallEffect) :
    check_clone3 (c3_input 88 fork_mem) 4096 88 eff open_file_model = CheckUnmodeled := by
  have hr := fork_mem_reads
  simp only [holds_image] at hr
  unfold check_clone3
  simp only [show (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false by decide,
    Bool.false_eq_true, ↓reduceIte, hr, fork_args_is_a_fork, check_clone3_resolve,
    show clone_no_shared_file_b (m_fds open_file_model) = false by decide, Bool.not_false]

/-- With the gate open and the fork image readable the checker never
declines, over every effect: the size and image gates are passed by the
fixture, and the resolution answers.
kernel: kernel/fork.c:clone3,kernel_clone@v6.18.46 -/
theorem check_clone3_never_declines_on_the_fork_image (eff : SyscallEffect) (m : Model)
    (hg : clone_no_shared_file_b (m_fds m) = true) :
    check_clone3 (c3_input 88 fork_mem) 4096 88 eff m ≠ CheckUnmodeled := by
  intro h
  have hr := fork_mem_reads
  simp only [holds_image] at hr
  unfold check_clone3 at h
  simp only [show (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false by decide,
    Bool.false_eq_true, ↓reduceIte, hr, fork_args_is_a_fork] at h
  have hc := check_clone3_resolve_unmodeled_inv 4096 eff m h
  rw [hg] at hc
  cases hc

/-! ### The witnesses

`clone_witness` and `clone3_witness` are one outcome each spec admits at
every model, which the progress argument consumes.  Both offer -EAGAIN
where the gates are open — the errno every kernel can return, from
`RLIMIT_NPROC` (kernel/fork.c:2058-2064, Linux v6.18.46) — and decline
where the spec declines. -/

/-- On the bare fixture the clone witness offers -EAGAIN with the model
unchanged.
kernel: kernel/fork.c:copy_process@v6.18.46 -/
theorem clone_witness_offers_eagain :
    clone_witness 17 demo_model = Ok (mkEffect (errno_ret EAGAIN) [] []) demo_model [] := rfl

/-- …which the checker accepts, stated as the handshake itself: whatever
the witness offers on the bare fixture, the checker answers `CheckOk` with
the witness's own model and events — `check_clone_admits_eagain` above is
the same fact with the offer written out.
model: the witness's offer is the effect `check_clone_admits_eagain`
accepts; no kernel behaviour is claimed beyond that pin's -/
theorem check_clone_accepts_the_witness (eff : SyscallEffect) (m' : Model) (evs : List event)
    (h : clone_witness 17 demo_model = Ok eff m' evs) :
    check_clone 17 eff demo_model = CheckOk m' evs := by
  rw [clone_witness_offers_eagain] at h
  cases h
  rfl

/-- Under a declined flag word the witness declines, whatever the model.
kernel: kernel/fork.c:clone@v6.18.46 -/
theorem clone_witness_declines_flags_zero (m : Model) : clone_witness 0 m = Unmodeled := rfl

/-- Under a shut descriptor gate it declines too.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem clone_witness_declines_with_a_file_open :
    clone_witness 17 open_file_model = Unmodeled := rfl

/-- With the gate open it never declines: the shape is `ret_outcome`, an
`Ok`, so the progress argument always has an outcome to hand the checker.
kernel: kernel/fork.c:clone,kernel_clone@v6.18.46 -/
theorem clone_witness_never_declines_with_the_gate_open (m : Model)
    (hg : clone_no_shared_file_b (m_fds m) = true) :
    clone_witness 17 m ≠ Unmodeled := by
  simp only [clone_witness, clone_resolve_witness, show clone_fork_flags_b 17 = true by decide, hg,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, ret_outcome, ne_eq, reduceCtorEq,
    not_false_eq_true]

/-- The clone3 witness on the fixture memory: -EAGAIN with the 88 bytes on
the ledger, the model unchanged — the effect
`check_clone3_admits_eagain_with_the_ledger` accepts.
kernel: kernel/fork.c:clone3,copy_process@v6.18.46 -/
theorem clone3_witness_offers_eagain_with_the_ledger :
    clone3_witness (c3_input 88 fork_mem) 4096 88 demo_model
      = Ok (with_copyins [(4096, 88)] (mkEffect (errno_ret EAGAIN) [] [])) demo_model [] := rfl

/-- Under a declined size it declines, whatever the input and the model.
kernel: kernel/fork.c:copy_clone_args_from_user@v6.18.46 -/
theorem clone3_witness_declines_size_zero (i : SyscallInput) (m : Model) :
    clone3_witness i 4096 0 m = Unmodeled := rfl

/-- Over unreadable memory it declines.
kernel: include/linux/uaccess.h:copy_struct_from_user@v6.18.46 -/
theorem clone3_witness_declines_nothing_mapped (m : Model) :
    clone3_witness (c3_input 88 (fun _ => none)) 4096 88 m = Unmodeled := rfl

/-- On an image that is not the plain fork it declines.
kernel: kernel/fork.c:clone3_args_valid@v6.18.46 -/
theorem clone3_witness_declines_clone_vm (m : Model) :
    clone3_witness (c3_input 88 (pin_mem 4096 (fork_args_with 0 256))) 4096 88 m = Unmodeled := rfl

/-- …and under a shut descriptor gate.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem clone3_witness_declines_with_a_file_open :
    clone3_witness (c3_input 88 fork_mem) 4096 88 open_file_model = Unmodeled := rfl

/-- With the gate open and the fork image readable it never declines, over
every model: the size and image gates pass on the fixture and the
resolution offers -EAGAIN with the ledger.
kernel: kernel/fork.c:clone3,kernel_clone@v6.18.46 -/
theorem clone3_witness_never_declines_on_the_fork_image (m : Model)
    (hg : clone_no_shared_file_b (m_fds m) = true) :
    clone3_witness (c3_input 88 fork_mem) 4096 88 m ≠ Unmodeled := by
  have hr := fork_mem_reads
  simp only [holds_image] at hr
  simp only [clone3_witness, clone3_resolve_witness,
    show (!bv_eqb (88 : word) (Z_to_bv 64 CLONE_ARGS_SIZE)) = false by decide,
    Bool.false_eq_true, ↓reduceIte, hr, fork_args_is_a_fork, hg, Bool.not_true, ne_eq,
    reduceCtorEq, not_false_eq_true]

end Clone

-- lean-port sentinel: ticket V-Kernel-Fork-set_tid_address appends below this line

section V_Kernel_Fork_set_tid_address

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Oracle

/-! ## V-Kernel-Fork-set_tid_address — `set_tid_address` over the real table

WHAT IS TWINNED HERE: NOTHING.  The statements Rocq makes about this arm
through `check_syscall` all sit in files the port declines
(`tools/lean_port_graph.py`): `check_syscall_set_tid_address` and
`syscall_witness_set_tid_address` in `Checks/Sys/DispatchCompute.v`
(271-278, at a71fd38a), and `abrt_sc1` with
`abrt_sc1_admits_another_tid` in `Checks/AbortWitness.v` (241-245,
437-441, at a71fd38a).  Its one worked case in a ported file,
`set_tid_address_first_choice_is_within_modeled_envelope`
(`theories/LinuxProcessSem/Checks/Cases/Kernel/Fork.v`), is stated over the
spec and twinned in `Checks/Cases/Kernel/Fork.lean`, and the paragraph
`Checks/Examples.v` gives the arm states no lemma.  The pins below are the
registration's own, all stated over `checked_table` itself, the three
witness pins through `syscall_spec_witness` and every other through
`check_syscall`, and all named `_over_the_real_table` (K6a's convention,
from `Checks/Cases/Checks/Sys/Kernel/Exit.lean`, for the pins at which the
real table first answers a call).  That the lookup at 96 finds the arm is
pinned by `lookups_agree_at_arm_set_tid_address`, which
`tools/gen_lean_checked.py` renders for every arm, and not again here.  Two of them say in Lean what
`DispatchCompute.v`'s two lemmas say in Rocq, at every input numbered 96
and every model: `set_tid_address_reads_no_register_over_the_real_table`
states `check_syscall_set_tid_address`, and
`set_tid_address_witness_reads_no_register_over_the_real_table` states
`syscall_witness_set_tid_address`, of which the two witness pins over a
fixed model are instances.
They sit here, in the checker's Cases file, and not in the spec's
`Checks/Cases/Kernel/Fork.lean`, for the reason #1234 gave for eventfd2:
that file is the spec's mutation twin, and the checked table entering its
import closure would make a spec mutant that breaks the checker's proofs
read as stillborn rather than as killed by a spec pin.

WHAT A PIN HERE ADDS to its checker-level neighbour above is the ARM's
claim, in two halves.  The lookup at 96 finds `arm_set_tid_address` and
not the dispatcher's own decline: a table with no row for 96 answers
`CheckUnmodeled` to every call, so each `CheckOk` and `CheckReject` below,
and `set_tid_address_never_declines_over_the_real_table` above all, fails
on such a table.  And the arm reads nothing of the input but its number:
`tidptr` is stored and never tested
(`SYSCALL_DEFINE1(set_tid_address, int __user *, tidptr)`,
kernel/fork.c:1747-1752, Linux v6.18.46) and no other register or byte of
memory is read, so the five pins stated at every input numbered 96 — the
`reads_no_register` and `never_declines` pins and the three witness pins
below — hold whatever `a0`-`a5` and the memory views are.

The fixtures are the recorded runs.  Every pin on a recorded call but one
takes its call, its state and its return from the `Checks.Cases.Oracle`
rows of the run it names (`tools/gen_lean_oracle.py`, which renders each
row from `testing/syscall-check/traces/set_tid/` and folds the state
through the checker itself), the refusing pins included: a row carries the
return the case's `--mutate` staged, so the lie is the recording's and not
written here.  The first-call refusals (set_tid/004, 005 and 009) are over
their row's own state, whose tid slot is empty, as a freestanding probe's
is at its first call: `set_tid.c` is built `-nostdlib`, so no `__init_tp`
has called `set_tid_address` before it.  The later-call refusals
(set_tid/018 and 024) are over the fold of the run's first record, which
recorded the kernel's answer at 018 and the staged 1 at 024.  The exception
is set_tid/011, whose lie is a byte written beside the kernel's own 44:
`tools/gen_lean_oracle.py`'s ROW-PURE renders no row whose effect carries
a write, so that pin builds its input with `sta_in` — `a0` the probe's
`&slot_a` (69640) and the other five registers 0, as the tracer recorded
them — and is stated over `demo_model`, whose tid slot is empty
(`m_tid_demo_model`, `Checks/Cases/Prelude.lean`).

EVIDENCE differs from the sections above in one respect.  A
`CheckReject` pin is POSITIVE to `tools/check_lean_pin_evidence.py` (its
type carries no negation), so, as above, it cites the kernel line, and
here it also names the probe's `reject` case in prose.  But the four
`CheckOk` pins below are stated over the row of the unmutated recorded run
they cite (`trace:`, the row's own run), where no pin above cites
`trace:`. -/

/-- Only the pin whose run renders no row (set_tid/011)
builds its input here. -/
def sta_in (tidptr : word) : SyscallInput :=
  SyscallInput.mkInput 96 [tidptr, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The arm reads no register: at every input numbered 96, every effect
and every model, the table's answer is the checker's on the effect and
the model alone.  `set_tid_address` stores `tidptr` in
`current->clear_child_tid` and returns `task_pid_vnr(current)`
(kernel/fork.c:1749-1751, Linux v6.18.46), with no test of the pointer on
the way and no other argument, so no register and no byte of memory can
move what the call returns.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem set_tid_address_reads_no_register_over_the_real_table (i : SyscallInput)
    (h : bv_unsigned i.in_sysno = 96) (eff : SyscallEffect) (m : Model) :
    check_syscall i eff m = check_set_tid_address eff m := by
  unfold check_syscall check_syscall_in
  rw [h]
  rfl

/-- The row answers every call: no input numbered 96, effect or model
makes the table decline it, because `set_tid_address`
(kernel/fork.c:1747-1752, Linux v6.18.46) has no path the model leaves
open.  This is the pin a table without the row fails at every input,
since the dispatcher's own answer to an unregistered number is
`CheckUnmodeled`.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem set_tid_address_never_declines_over_the_real_table (i : SyscallInput)
    (h : bv_unsigned i.in_sysno = 96) (eff : SyscallEffect) (m : Model) :
    check_syscall i eff m ≠ CheckUnmodeled := by
  rw [set_tid_address_reads_no_register_over_the_real_table i h eff m]
  exact check_set_tid_address_never_declines_directly eff m

/-! ### The first call -/

/-- The recorded first call, stated over its `Checks.Cases.Oracle` row: in
the state the run gave it, the table accepts the return the kernel produced
and records it as the process's tid.  The call, the state and the return are
the row's, so nothing here is written by hand.  The return is inside
`(0, 2^22)`.  Its own draw is over
`[pid_min, pid_max)`, `pid_min` starting at 1 and raised only to
`RESERVED_PIDS` (kernel/pid.c:226-239, Linux v6.18.46); a tid REQUESTED
through clone3's `set_tid` is stored exactly as requested
(kernel/pid.c:216-218, Linux v6.18.46), and only if it is in
`[1, pid_max)`, since `tid < 1 || tid >= pid_max` is -EINVAL first
(kernel/pid.c:198-200, Linux v6.18.46), so it may lie below `pid_min`.
trace: set_tid/001 -/
theorem set_tid_address_records_the_traced_tid_over_the_real_table :
    ∃ m, row_set_tid_001_s0_state = some m
      ∧ check_syscall row_set_tid_001_s0_call row_set_tid_001_s0_effect m
          = CheckOk (with_tid row_set_tid_001_s0_effect.eff_ret m) [] :=
  ⟨_, rfl, rfl⟩

/-- The recorded first call at `NULL`, over its row: the table accepts the
kernel's return exactly as at `&slot_a`, the pointer being stored and never
tested (kernel/fork.c:1749, Linux v6.18.46).
trace: set_tid/010 -/
theorem set_tid_address_records_the_traced_tid_at_null_over_the_real_table :
    ∃ m, row_set_tid_010_s0_state = some m
      ∧ check_syscall row_set_tid_010_s0_call row_set_tid_010_s0_effect m
          = CheckOk (with_tid row_set_tid_010_s0_effect.eff_ret m) [] :=
  ⟨_, rfl, rfl⟩

/-- tid 0 on a first call is refused through the table, over the row of
the probe's `reject --mutate set_tid_address:ret=0 -- one` case
(set_tid/004), whose state has no tid recorded: no task that can make a
syscall holds 0.  `alloc_pid`'s own draw starts at `pid_min = 1`
(kernel/pid.c:226, Linux v6.18.46), and a REQUESTED tid below 1 is -EINVAL
(kernel/pid.c:198-199, Linux v6.18.46).  (`init_struct_pid` has `.nr = 0`,
kernel/pid.c:50-61, but only `init_task` and the per-CPU idle tasks carry
it as their own pid, and `copy_process` skips `alloc_pid` for it,
kernel/fork.c:2201-2208.)
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem set_tid_address_tid_zero_rejected_over_the_real_table :
    ∃ m, row_set_tid_004_s0_state = some m
      ∧ check_syscall row_set_tid_004_s0_call row_set_tid_004_s0_effect m = CheckReject :=
  ⟨_, rfl, rfl⟩

/-- `2^22` is refused through the table, over the row of the probe's
`reject --mutate set_tid_address:ret=4194304 -- one` case (set_tid/005),
whose state has no tid recorded.  The kernel's own draw never reaches
`pid_max`: `idr_alloc_cyclic`'s `end` is exclusive (lib/idr.c:122, Linux
v6.18.46).  A REQUESTED tid at or above `pid_max` is -EINVAL
(kernel/pid.c:198-200, Linux v6.18.46).  And no `pid_max` exceeds
`PID_MAX_LIMIT` (include/linux/threads.h:34-35, Linux v6.18.46), which
is at most 2^22 on riscv64: 2^22 without
`CONFIG_BASE_SMALL`, and `PAGE_SIZE * 8` with it, 2^15 at riscv64's one
page size, 4 KiB (arch/riscv/Kconfig:186, Linux v6.18.46).  The walk from
`pid_max` to `2^22` is on `Sys.Kernel.Fork.PID_MAX_ENVELOPE`.
kernel: lib/idr.c:idr_alloc_cyclic; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem set_tid_address_envelope_end_rejected_over_the_real_table :
    ∃ m, row_set_tid_005_s0_state = some m
      ∧ check_syscall row_set_tid_005_s0_call row_set_tid_005_s0_effect m = CheckReject :=
  ⟨_, rfl, rfl⟩

/-- An errno is refused through the table, over the row of the probe's
`reject --mutate set_tid_address:ret=-EINVAL -- one` case (set_tid/009),
whose staged return is the bit pattern of -22, `2^64 - 22`: the call has
no error path — a store and a return (kernel/fork.c:1749-1751, Linux
v6.18.46).  -EINVAL is what `alloc_pid` returns for a bad REQUESTED tid
(kernel/pid.c:198-199, Linux v6.18.46), a path `set_tid_address` does not
reach.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem set_tid_address_errno_rejected_over_the_real_table :
    ∃ m, row_set_tid_009_s0_state = some m
      ∧ check_syscall row_set_tid_009_s0_call row_set_tid_009_s0_effect m = CheckReject :=
  ⟨_, rfl, rfl⟩

/-- A byte written at `tidptr` beside the tid the kernel really returned
is refused through the table: the call stores the pointer and dereferences
nothing (kernel/fork.c:1749, Linux v6.18.46).  The write is the one the
probe's `reject --mutate set_tid_address:smuggle-write:a0:1 -- one` case
smuggled (set_tid/011), one byte 0x41 at `&slot_a`, beside the kernel's
44.  This pin alone is not over its row: `tools/gen_lean_oracle.py`'s
ROW-PURE renders no row whose effect carries a write, so the input is
`sta_in`'s and the model `demo_model`'s, whose tid slot is empty as the
run's was.
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem set_tid_address_smuggled_write_rejected_over_the_real_table :
    check_syscall (sta_in 69640) (mkEffect 44 [(69640, [0x41])] []) demo_model = CheckReject :=
  rfl

/-! ### A later call -/

/-- The recorded pair of calls, over its two rows: the kernel answered the
same tid twice, and the table accepts the first and records it, then accepts
the second against that record with the model unmoved.  The second row's
state is the fold of the first, so the record the second call meets is the
one the checker made.  `task_pid_vnr(current)` (include/linux/pid.h:244-247,
Linux v6.18.46) reads the calling task's own pid, which does not move while
the task is its own thread-group leader.
trace: set_tid/017 -/
theorem set_tid_address_repeats_the_traced_tid_over_the_real_table :
    (∃ m, row_set_tid_017_s0_state = some m
      ∧ check_syscall row_set_tid_017_s0_call row_set_tid_017_s0_effect m
          = CheckOk (with_tid row_set_tid_017_s0_effect.eff_ret m) [])
    ∧ (∃ m, row_set_tid_017_s1_state = some m
      ∧ check_syscall row_set_tid_017_s1_call row_set_tid_017_s1_effect m
          = CheckOk m []) :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

/-- A second call answering a different tid is refused, over the second
row of the probe's `reject --mutate set_tid_address#2:ret+1 -- two` case
(set_tid/018): the lie added 1 to the kernel's second answer, and the row's
state is the fold of the first call, which recorded the kernel's answer.
This is the defect the probe was written for, a fresh draw on every call,
which no kernel makes (include/linux/pid.h:244-247, Linux v6.18.46).
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem set_tid_address_second_draw_rejected_over_the_real_table :
    ∃ m, row_set_tid_018_s1_state = some m
      ∧ check_syscall row_set_tid_018_s1_call row_set_tid_018_s1_effect m = CheckReject :=
  ⟨_, rfl, rfl⟩

/-- A second call through a different pointer repeats the tid, over the two
rows: the kernel answered the same tid at `&slot_a` and at `&slot_b`, and
the table accepts the second against the record, since the new pointer only
replaces `clear_child_tid` (kernel/fork.c:1749, Linux v6.18.46).
trace: set_tid/023 -/
theorem set_tid_address_repeats_the_traced_tid_at_another_pointer_over_the_real_table :
    (∃ m, row_set_tid_023_s0_state = some m
      ∧ check_syscall row_set_tid_023_s0_call row_set_tid_023_s0_effect m
          = CheckOk (with_tid row_set_tid_023_s0_effect.eff_ret m) [])
    ∧ (∃ m, row_set_tid_023_s1_state = some m
      ∧ check_syscall row_set_tid_023_s1_call row_set_tid_023_s1_effect m
          = CheckOk m []) :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

/-- …and a different pointer does not start a new record, over the second
row of the probe's `reject --mutate set_tid_address#1:ret=1 --mutate
set_tid_address#2:ret=2 -- two-ptr` case (set_tid/024): the row's state is
the fold of the first call, which recorded the staged 1, and a second call
at `&slot_b` (69632) answering 2 is refused against it.
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem set_tid_address_new_pointer_new_tid_rejected_over_the_real_table :
    ∃ m, row_set_tid_024_s1_state = some m
      ∧ check_syscall row_set_tid_024_s1_call row_set_tid_024_s1_effect m = CheckReject :=
  ⟨_, rfl, rfl⟩

/-! ### The witness the table hands `receptive`

`syscall_spec_witness` dispatches over the same table, so the arm's
`ca_witness` is what it answers at 96; the witness pins above fix
`set_tid_address_witness` on its own.  The first pin here fixes that the
arm hands it the model and nothing of the input, at every input numbered
96 and every model, which is Rocq's `syscall_witness_set_tid_address`; the
two after it are its instances at the two states the witness tells apart,
and say what it answers there through the table. -/

/-- The witness reads no register: at every input numbered 96 and every
model, the table's witness is `set_tid_address_witness` of the model
alone, as the call's answer is `task_pid_vnr(current)` whatever `tidptr`
holds (kernel/fork.c:1749-1751, Linux v6.18.46).
kernel: kernel/fork.c:set_tid_address@v6.18.46 -/
theorem set_tid_address_witness_reads_no_register_over_the_real_table (i : SyscallInput)
    (h : bv_unsigned i.in_sysno = 96) (m : Model) :
    syscall_spec_witness i m = set_tid_address_witness m := by
  unfold syscall_spec_witness table_witness
  rw [h]
  rfl

/-- With no tid recorded, the witness through the table draws 1, the
lowest tid `alloc_pid` can store: its own draw starts at `pid_min = 1`
(kernel/pid.c:226, Linux v6.18.46), and a REQUESTED tid below 1 is -EINVAL
(kernel/pid.c:198-199, Linux v6.18.46).  This holds whatever the registers
and memory hold.
kernel: kernel/pid.c:alloc_pid@v6.18.46 -/
theorem set_tid_address_witness_draws_one_over_the_real_table (i : SyscallInput)
    (h : bv_unsigned i.in_sysno = 96) :
    syscall_spec_witness i demo_model
      = Ok (mkEffect (Z_to_bv 64 1) [] []) (with_tid (Z_to_bv 64 1) demo_model) [] := by
  unfold syscall_spec_witness table_witness
  rw [h]
  rfl

/-- With a tid recorded, the witness through the table repeats it and
moves nothing, whatever the registers and memory hold.
kernel: kernel/fork.c:set_tid_address; include/linux/pid.h:task_pid_vnr@v6.18.46 -/
theorem set_tid_address_witness_repeats_the_record_over_the_real_table (i : SyscallInput)
    (h : bv_unsigned i.in_sysno = 96) :
    syscall_spec_witness i (with_tid 618 demo_model)
      = Ok (mkEffect 618 [] []) (with_tid 618 demo_model) [] := by
  unfold syscall_spec_witness table_witness
  rw [h]
  rfl

end V_Kernel_Fork_set_tid_address

-- lean-port sentinel: ticket V-Kernel-Fork-clone appends below this line

section V_Kernel_Fork_clone

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Oracle
open LinuxProcessSemantics.LinuxProcessSem.Checks.ProcessCreation
  (pc_model pc_input pc_clone_input pc_model_open_file)

/-! ## V-Kernel-Fork-clone — `clone` and `clone3` over the real table

WHAT IS TWINNED HERE.  Rocq states its checker cases on these two arms
through `check_syscall`, in `theories/LinuxProcessSem/Checks/ProcessCreation.v`
(952-1020, at a71fd38a): `clone_checker_declines_flags_zero`,
`clone3_checker_declines_size_zero`, five on `pc_clone_input` from
`clone_checker_admits_a_pid` to `clone_checker_refuses_another_errno`, and
`clone_checker_declines_with_a_file_open`; and the corollary
`check_clone_success_sets_children` (486-496).  The section on clone above
states the eight cases against `check_clone` and `check_clone3` directly,
as this file's header says, because no arm was registered then.  Each is
restated below over `checked_table`, under its Rocq name with
`_over_the_real_table` (K6a's convention, as in the section above), on the
fixtures `Checks/ProcessCreation.lean` twins (`pc_model`, `pc_input`,
`pc_clone_input`, `pc_model_open_file`), and so is the corollary.  They
land here and not beside their Rocq file in `Checks/ProcessCreation.lean`
because this ticket registers the arms and writes no Lean file but the arm
file and this one.  `tools/check_lean_pin_evidence.py`'s `rocq-twin:` names
a lemma of this file's own Rocq mirror, which `ProcessCreation.v` is not,
so each pin carries its own evidence and names its Rocq companion in
prose.  That the lookups at 220 and 435 find the arms is pinned by
`lookups_agree_at_arm_clone` and `lookups_agree_at_arm_clone3`, which
`tools/gen_lean_checked.py` renders for every arm, and not again here.

WHAT A PIN HERE ADDS to its checker-level neighbour above is the ARM's
claim, in two halves.  The table answers through the arm and not through
the dispatcher's own decline: a table with no row for 220 or 435 answers
`CheckUnmodeled` to every call there, so each `CheckOk` and `CheckReject`
below, and each witness pin, fails on such a table.  The declines do not
tell the two tables apart on their own, and stand for the Rocq companions
and the recorded fail-closed runs they twin.  And the arm hands its
checker the right registers: the four `reads` pins fix, at every input
numbered 220 or 435, that the table's answer is the checker's on `a0`
whole (220) or on the input, `a0` and `a1` whole (435), which is what a
narrowed or swapped register would break.

THE FIXTURES.  The pins on recorded calls are stated over
`Checks.Cases.Oracle` rows (`tools/gen_lean_oracle.py`) of
`testing/syscall-check/traces/clone_fork/`, whose runs really forked: the
kernel answered `clone(SIGCHLD, …)` with pid 39 in clone_fork/001 and
with 41 and then 42 in clone_fork/002.  None is over a row of
`clone_spec`, the probe that walks the flag word, the size and the
struct: `tools/check_lean_pins.py` reads every name with `_spec_` in it
as a spec's (`SPEC_NAME`), a row's name carries its probe's, and a pin
over such a row is refused as comparing three specs.  The three runs of
that probe pinned here, all declines, are restated instead over
`clone_rec_in` and `clone3_rec_in`, which carry the registers the run
recorded and no memory, at every effect and every model.  Nor does any
`clone3` record that reached the struct render a row: ROW-PURE refuses
its copy-in and ROW-BOUND its 88-byte `in_mem`.  So the `clone3` pins
that answer a call are over `c3_input` and `fork_mem`
(`Checks/Cases/Kernel/Fork.lean`), and the real `clone3` fork,
clone_fork/021, is what the accepting one cites.

EVIDENCE.  `tools/check_lean_pin_evidence.py` reads every pin here as
POSITIVE, the `CheckUnmodeled` ones included: its decline mark is the
word `Unmodeled` alone, which `CheckUnmodeled` does not spell.  So a
`CheckOk` pin over a row cites that row's own run (`trace:`), every other
pin cites the kernel, and a recorded run that declined or refused is
named in prose, since a `trace:` of a fail-closed or reject case beside
a positive pin is refused.  A pin over a fixture says on a `no-row:` line
why no row is its own. -/

/-! ### The registers each arm hands its checker -/

/-- The arm reads `a0` and nothing else of the input: at every input
numbered 220, every effect and every model, the table's answer is
`check_clone` of the whole register.  Under the one word the checker's
gate admits, the other registers reach nothing the parent's answer
shows: `newsp` becomes the CHILD's `sp` and `tls` its `tp`, the latter
only under `CLONE_SETTLS` (`copy_thread`, arch/riscv/kernel/process.c:251-254,
Linux v6.18.46), and the two tid pointers are read only behind flags that
word does not carry (`arm_clone`'s docstring, `Checks/Arms/Kernel/Fork.lean`).
kernel: kernel/fork.c:clone; arch/riscv/kernel/process.c:copy_thread@v6.18.46 -/
theorem clone_reads_a0_over_the_real_table (i : SyscallInput)
    (h : bv_unsigned i.in_sysno = 220) (eff : SyscallEffect) (m : Model) :
    check_syscall i eff m = check_clone (in_arg i 0) eff m := by
  unfold check_syscall check_syscall_in
  rw [h]
  rfl

/-- The arm reads `a0` and `a1`, and the input's memory through them: at
every input numbered 435, every effect and every model, the table's
answer is `check_clone3` of the input with `uargs` the whole of `a0` and
`size` the whole of `a1` (`SYSCALL_DEFINE2(clone3, struct clone_args
__user *, uargs, size_t, size)`, kernel/fork.c:2892, Linux v6.18.46).  An
arm swapping the two would test the pointer against 88, and fails here.
kernel: kernel/fork.c:clone3,copy_clone_args_from_user@v6.18.46 -/
theorem clone3_reads_a0_and_a1_over_the_real_table (i : SyscallInput)
    (h : bv_unsigned i.in_sysno = 435) (eff : SyscallEffect) (m : Model) :
    check_syscall i eff m = check_clone3 i (in_arg i 0) (in_arg i 1) eff m := by
  unfold check_syscall check_syscall_in
  rw [h]
  rfl

/-- The witness the table hands `receptive` reads what the checker reads:
at every input numbered 220 and every model, it is `clone_witness` of the
whole of `a0` and the model.
kernel: kernel/fork.c:clone@v6.18.46 -/
theorem clone_witness_reads_a0_over_the_real_table (i : SyscallInput)
    (h : bv_unsigned i.in_sysno = 220) (m : Model) :
    syscall_spec_witness i m = clone_witness (in_arg i 0) m := by
  unfold syscall_spec_witness table_witness
  rw [h]
  rfl

/-- …and at every input numbered 435, `clone3_witness` of the input, the
whole of `a0` and the whole of `a1`.
kernel: kernel/fork.c:clone3,copy_clone_args_from_user@v6.18.46 -/
theorem clone3_witness_reads_a0_and_a1_over_the_real_table (i : SyscallInput)
    (h : bv_unsigned i.in_sysno = 435) (m : Model) :
    syscall_spec_witness i m = clone3_witness i (in_arg i 0) (in_arg i 1) m := by
  unfold syscall_spec_witness table_witness
  rw [h]
  rfl

/-! ### Rocq's corollary -/

/-- Every call the table accepts at 220 or 435 either answers an errno of
`clone_errnos` and leaves the model as it was, or answers a pid and
records the child, the field `wait4_spec`'s child gate reads
(`Sys/Kernel/Exit.lean`).  Rocq: `check_clone_success_sets_children`
(`Checks/ProcessCreation.v`), proved as Rocq proves it:
`check_syscall_sound_ok` turns the acceptance into an admitted outcome,
and `clone_success_sets_children` (`Checks/ProcessCreation.lean`) reads
that.  A table with no row at 220 or 435 accepts nothing there and
satisfies this vacuously; the accepting pins below are what fail on it.
kernel: kernel/fork.c:copy_process,kernel_clone@v6.18.46 -/
theorem clone_success_sets_children_over_the_real_table (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (hno : bv_unsigned i.in_sysno = 220 ∨ bv_unsigned i.in_sysno = 435)
    (h : check_syscall i eff m = CheckOk m' evs) :
    (errno_ret_in clone_errnos eff.eff_ret = true → m' = m)
    ∧ (errno_ret_in clone_errnos eff.eff_ret = false → m_has_children m' = true) :=
  LinuxProcessSemantics.LinuxProcessSem.Checks.ProcessCreation.clone_success_sets_children
    i m eff m' evs hno (check_syscall_sound_ok i eff m m' evs h)

/-! ### Rocq's eight checker cases -/

/-- `clone` with a flag word of 0 is declined through the table: 0 is not
`SIGCHLD`, the one word the gate admits.  Linux forks on it all the same,
a child with no exit signal (`kernel_clone`, kernel/fork.c:2570, Linux
v6.18.46).  Rocq: `clone_checker_declines_flags_zero`.
kernel: kernel/fork.c:clone,kernel_clone@v6.18.46 -/
theorem clone_checker_declines_flags_zero_over_the_real_table :
    check_syscall (pc_input 220) (mkEffect 0 [] []) pc_model = CheckUnmodeled := rfl

/-- `clone3` with a size of 0 is declined through the table, before the
struct is read.  Linux answers -EINVAL there, `size` being below
`CLONE_ARGS_SIZE_VER0` (`copy_clone_args_from_user`,
kernel/fork.c:2774-2775, Linux v6.18.46); the checker declines every size
but 88.  Rocq: `clone3_checker_declines_size_zero`.
kernel: kernel/fork.c:clone3,copy_clone_args_from_user@v6.18.46 -/
theorem clone3_checker_declines_size_zero_over_the_real_table :
    check_syscall (pc_input 435) (mkEffect 0 [] []) pc_model = CheckUnmodeled := rfl

/-- `clone(SIGCHLD, 0, 0, 0, 0)` answered with a pid is accepted through
the table and the child recorded, over `pc_model`, whose three
descriptors are `State.init_model`'s channel seeds, so the descriptor
gate is open.  `kernel_clone` hands the parent the child's pid
(kernel/fork.c:2623-2624, Linux v6.18.46).  Rocq:
`clone_checker_admits_a_pid`.
no-row: Rocq's fixture and pid; clone_fork's rows below hold the kernel's own
kernel: kernel/fork.c:kernel_clone,copy_process@v6.18.46 -/
theorem clone_checker_admits_a_pid_over_the_real_table :
    check_syscall pc_clone_input (mkEffect 4242 [] []) pc_model
      = CheckOk (with_children pc_model) [] := rfl

/-- …answered -EAGAIN, accepted with the model unmoved: `copy_process`
answers it at the `RLIMIT_NPROC` check (kernel/fork.c:2058-2063, Linux
v6.18.46), and a fork that failed created no child.  Rocq:
`clone_checker_admits_eagain`.
no-row: Rocq's fixture; clone_fork/012's row below forges the same errno
kernel: kernel/fork.c:copy_process@v6.18.46 -/
theorem clone_checker_admits_eagain_over_the_real_table :
    check_syscall pc_clone_input (mkEffect (errno_ret EAGAIN) [] []) pc_model
      = CheckOk pc_model [] := rfl

/-- …answered 0, refused: 0 is the CHILD's return (`childregs->a0 = 0`,
`copy_thread`, arch/riscv/kernel/process.c:255, Linux v6.18.46), and the
parent's is the child's pid.  Rocq: `clone_checker_refuses_zero`.
no-row: Rocq's fixture; clone_fork/003's row below forges the same answer
kernel: kernel/fork.c:kernel_clone; arch/riscv/kernel/process.c:copy_thread@v6.18.46 -/
theorem clone_checker_refuses_zero_over_the_real_table :
    check_syscall pc_clone_input (mkEffect 0 [] []) pc_model = CheckReject := rfl

/-- …answered 4194304, `PID_MAX_ENVELOPE`, refused: `alloc_pid`'s draw
stays below `pid_max`, which never exceeds `PID_MAX_LIMIT`, at most 2^22
on riscv64 (include/linux/threads.h:34-35, Linux v6.18.46; the walk is on
`Sys.Kernel.Fork.PID_MAX_ENVELOPE`).  Rocq states it at
`Z_to_bv 64 PID_MAX_ENVELOPE`, the same word.  Rocq:
`clone_checker_refuses_the_envelope_bound`.
no-row: Rocq's fixture; no kernel can return this pid to record
kernel: lib/idr.c:idr_alloc_cyclic; kernel/pid.c:alloc_pid@v6.18.46 -/
theorem clone_checker_refuses_the_envelope_bound_over_the_real_table :
    check_syscall pc_clone_input (mkEffect 4194304 [] []) pc_model = CheckReject := rfl

/-- …answered -ENFILE, refused: it is not in `clone_errnos`, whose
docstring (`Sys/Kernel/Fork.lean`) walks the errnos the admitted word can
reach.  -ENFILE is what `alloc_empty_file` answers when the system's file
count is spent (fs/file_table.c:278, Linux v6.18.46), and
`copy_process` (kernel/fork.c:2215-2222, Linux v6.18.46) reaches a file
allocation for `CLONE_PIDFD`, a flag the admitted word does not carry.
ENFILE (23) is the nearest neighbour of the admitted EMFILE
(24).  Rocq: `clone_checker_refuses_another_errno`.
no-row: Rocq's fixture; no run of the admitted word can return this errno
kernel: fs/file_table.c:alloc_empty_file; kernel/fork.c:copy_process@v6.18.46 -/
theorem clone_checker_refuses_another_errno_over_the_real_table :
    check_syscall pc_clone_input (mkEffect (errno_ret ENFILE) [] []) pc_model
      = CheckReject := rfl

/-- At the admitted word, with a regular file open at 3, the call is
declined through the table: `copy_files` gives the child a table whose
entries point at the parent's `struct file`s (`dup_fd`, fs/file.c, Linux
v6.18.46), so the two share the offset, which `State.FdEntry`, inlining
it into the descriptor, cannot express.  Rocq:
`clone_checker_declines_with_a_file_open`.
kernel: kernel/fork.c:copy_files; fs/file.c:dup_fd@v6.18.46 -/
theorem clone_checker_declines_with_a_file_open_over_the_real_table :
    check_syscall pc_clone_input (mkEffect 4242 [] []) pc_model_open_file
      = CheckUnmodeled := rfl

/-! ### Recorded runs -/

/-- A real fork, over its row: the kernel answered `clone(SIGCHLD, …)`
with pid 39, and the table accepts it and records the child.
trace: clone_fork/001 -/
theorem clone_records_the_traced_fork_over_the_real_table :
    ∃ m, row_clone_fork_001_s0_state = some m
      ∧ check_syscall row_clone_fork_001_s0_call row_clone_fork_001_s0_effect m
          = CheckOk (with_children m) [] :=
  ⟨_, rfl, rfl⟩

/-- Two real forks, over their two rows: the kernel answered 41 and then
42, and the table accepts both.  The second row's state is the fold of
the first, so the second call is judged in a model that already records
a child, as the kernel's second fork was made by a parent that had one.
trace: clone_fork/002 -/
theorem clone_records_two_traced_forks_over_the_real_table :
    (∃ m, row_clone_fork_002_s0_state = some m
      ∧ check_syscall row_clone_fork_002_s0_call row_clone_fork_002_s0_effect m
          = CheckOk (with_children m) [])
    ∧ (∃ m, row_clone_fork_002_s1_state = some m
      ∧ check_syscall row_clone_fork_002_s1_call row_clone_fork_002_s1_effect m
          = CheckOk (with_children m) []) :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

/-- -EAGAIN forged over a real fork, over the row of the probe's
`conform --mutate clone:ret=-EAGAIN -- fork` case (clone_fork/012): the
table accepts it and records no child.  `copy_process` answers -EAGAIN at
the `RLIMIT_NPROC` check (kernel/fork.c:2058-2063, Linux v6.18.46), so the
lie is an answer this call can get in another state.
trace: clone_fork/012 -/
theorem clone_admits_a_forged_eagain_over_the_real_table :
    ∃ m, row_clone_fork_012_s0_state = some m
      ∧ check_syscall row_clone_fork_012_s0_call row_clone_fork_012_s0_effect m
          = CheckOk m [] :=
  ⟨_, rfl, rfl⟩

/-- The CHILD's answer forged over a real fork is refused, over the row of
the probe's `reject --mutate clone:ret=0 -- fork` case (clone_fork/003):
0 is the return `copy_thread` writes into the child's `a0`
(arch/riscv/kernel/process.c:255, Linux v6.18.46), never the parent's.
kernel: kernel/fork.c:kernel_clone; arch/riscv/kernel/process.c:copy_thread@v6.18.46 -/
theorem clone_refuses_the_childs_answer_over_the_real_table :
    ∃ m, row_clone_fork_003_s0_state = some m
      ∧ check_syscall row_clone_fork_003_s0_call row_clone_fork_003_s0_effect m
          = CheckReject :=
  ⟨_, rfl, rfl⟩

/-- A real `clone(CLONE_VFORK | SIGCHLD, …)` is declined, over its row
(clone_fork/008): `kernel_clone` (kernel/fork.c:2648-2651, Linux
v6.18.46) waits for the child to release the parent before it answers,
and it answered pid 56 once the child's exit did; `CLONE_VFORK` is not
in the word the gate admits.
kernel: kernel/fork.c:kernel_clone,wait_for_vfork_done@v6.18.46 -/
theorem clone_declines_a_traced_vfork_over_the_real_table :
    ∃ m, row_clone_fork_008_s0_state = some m
      ∧ check_syscall row_clone_fork_008_s0_call row_clone_fork_008_s0_effect m
          = CheckUnmodeled :=
  ⟨_, rfl, rfl⟩

/-- The registers `clone_spec`'s `clone` mode issues, the flag word and
`parent_tidptr` as a run recorded them and the rest zero, with no memory. -/
def clone_rec_in (flags tidptr : word) : SyscallInput :=
  SyscallInput.mkInput 220 [flags, 0, tidptr, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The registers `clone_spec`'s `c3` and `c3null` modes issue, `uargs` and
`size`, with no memory: the `mem-none` the probe stages and its NULL
leave nothing readable at `uargs`. -/
def clone3_rec_in (uargs size : word) : SyscallInput :=
  SyscallInput.mkInput 435 [uargs, size, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- `SIGCHLD` with bit 32 set is declined at every effect and every model.
These are the registers of clone_spec/013, the probe's `fail-closed
--expect-unmodeled clone --mutate clone:arg0=0x100000011 -- clone` case,
which forged the word over the probe's own `clone(CLONE_SIGHAND, 0,
&tidslot, 0, 0)`.  Linux keeps `lower_32_bits(clone_flags)`
(kernel/fork.c:2743, :2747, Linux v6.18.46) and would fork on this word;
the checker reads the register whole and declines it.  An arm handing it
the low 32 bits would read `SIGCHLD`, pass the flag gate and answer at
every model whose descriptor gate is open, which this pin refuses.
no-row: check_lean_pins.py reads a clone_spec row's name as a spec's
kernel: kernel/fork.c:clone@v6.18.46 -/
theorem clone_declines_bit_32_over_the_real_table (eff : SyscallEffect) (m : Model) :
    check_syscall (clone_rec_in 0x100000011 69632) eff m = CheckUnmodeled := rfl

/-- `clone3` at size 88 with nothing readable at `uargs` is declined at
every effect and every model: the arm hands the checker the input's
memory, and a struct it cannot read is a decline.  These are the
registers of clone_spec/048, the probe's `fail-closed --expect-unmodeled
clone3 --mutate clone3:arg1=88,mem-none -- c3` case.  Linux answers
-EFAULT there (`copy_struct_from_user`, include/linux/uaccess.h:408-409,
called at kernel/fork.c:2777, Linux v6.18.46).
no-row: check_lean_pins.py reads a clone_spec row's name as a spec's
kernel: kernel/fork.c:clone3,copy_clone_args_from_user@v6.18.46 -/
theorem clone3_declines_an_unreadable_struct_over_the_real_table (eff : SyscallEffect)
    (m : Model) :
    check_syscall (clone3_rec_in 69640 88) eff m = CheckUnmodeled := rfl

/-- …and so is a NULL `uargs` at size 88, the registers of clone_spec/052,
the probe's `fail-closed --expect-unmodeled clone3 --mutate clone3:arg1=88
-- c3null` case, which Linux answers -EFAULT by the same path.
no-row: check_lean_pins.py reads a clone_spec row's name as a spec's
kernel: kernel/fork.c:clone3,copy_clone_args_from_user@v6.18.46 -/
theorem clone3_declines_a_null_struct_over_the_real_table (eff : SyscallEffect) (m : Model) :
    check_syscall (clone3_rec_in 0 88) eff m = CheckUnmodeled := rfl

/-! ### `clone3` past the struct, over the image fixture -/

/-- `clone3(&args, 88)` over `fork_mem`, the image of the admitted
`clone_args`, answered with a pid and the 88-byte copy-in, is accepted
through the table and the child recorded.  The real `clone3` fork,
clone_fork/021, was answered with pid 101 and the same copy-in.
no-row: ROW-PURE refuses its copy-in and ROW-BOUND its 88-byte input
trace: clone_fork/021 -/
theorem clone3_accepts_a_pid_with_the_ledger_over_the_real_table :
    check_syscall (c3_input 88 fork_mem) (with_copyins [(4096, 88)] (mkEffect 1234 [] []))
      demo_model = CheckOk (with_children demo_model) [] := rfl

/-- …and the same pid with the copy-in dropped is refused: the 88 bytes
were read (`copy_struct_from_user`, include/linux/uaccess.h:408, called at
kernel/fork.c:2777, Linux v6.18.46), so an effect without them is not one
the kernel produced.  The probe's case over a real fork is clone_fork's
`reject --mutate clone3:drop-copyins -- c3fork`.
no-row: ROW-PURE refuses its copy-in and ROW-BOUND its 88-byte input
kernel: kernel/fork.c:copy_clone_args_from_user@v6.18.46 -/
theorem clone3_refuses_a_dropped_ledger_over_the_real_table :
    check_syscall (c3_input 88 fork_mem) (mkEffect 1234 [] []) demo_model = CheckReject := rfl

/-! ### The witness the table hands `receptive` -/

/-- At `clone(SIGCHLD, …)` over `pc_model` the witness is -EAGAIN with the
model unmoved, an answer the descriptor gate being open is enough for:
`copy_process` can fail there (kernel/fork.c:2058-2063, Linux v6.18.46)
without creating a child.
no-row: a witness is the model's own pick, not a recorded answer
kernel: kernel/fork.c:copy_process@v6.18.46 -/
theorem clone_witness_offers_eagain_over_the_real_table :
    syscall_spec_witness pc_clone_input pc_model
      = Ok (mkEffect (errno_ret EAGAIN) [] []) pc_model [] := rfl

/-- …and at `clone3(&args, 88)` over `fork_mem`, the same errno with the
88-byte copy-in, which `copy_clone_args_from_user` made (kernel/fork.c:2777,
Linux v6.18.46) before `kernel_clone` is called (:2913).
no-row: a witness is the model's own pick, not a recorded answer
kernel: kernel/fork.c:copy_process@v6.18.46 -/
theorem clone3_witness_offers_eagain_with_the_ledger_over_the_real_table :
    syscall_spec_witness (c3_input 88 fork_mem) demo_model
      = Ok (with_copyins [(4096, 88)] (mkEffect (errno_ret EAGAIN) [] [])) demo_model [] := rfl

end V_Kernel_Fork_clone

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Fork
