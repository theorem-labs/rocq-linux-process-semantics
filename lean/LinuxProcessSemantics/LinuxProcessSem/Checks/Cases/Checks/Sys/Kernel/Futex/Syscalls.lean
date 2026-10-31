import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Futex.Syscalls
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Futex.Syscalls
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Kernel.Futex.Syscalls — what the futex CHECKER accepts and refuses and what its WITNESS names, read off against Linux

Pins over `Checks.Sys.Kernel.Futex.Syscalls`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Kernel/Futex/Syscalls.v` and of
`theories/LinuxProcessSem/Checks/Witness/Kernel/Futex/Syscalls.v`: the
checker first, arm by arm in the order the checker tests them, the witness
last.  Not part of the trusted specification: this file is QA on the
definitions, written to be READ, and every claim in it is a claim about
what the kernel does, with the citation beside it.  Every kernel line below
was read at Linux v6.18.46 (commit 1f99e9ab748f).

WHAT A CHECKER PIN IS.  `Checks/Cases/Kernel/Futex/Syscalls.lean` states,
for each decision of the spec, an `iff` over every outcome and refutes the
lie a kernel could not tell.  The checker is that spec made executable —
the four `_sound_`/`_complete_` lemmas beside it say the two agree on
every input — so a pin here does not restate those `iff`s.  It hands the
checker a concrete `(input, effect)` pair, the shape a trace hands it, and
states the verdict: `CheckOk` on the kernel's answer, `CheckReject` on the
lie, `CheckUnmodeled` where the spec declines.  That is the question a
trace asks, and the one the four lemmas cannot: soundness and completeness
are biconditionals between two definitions of this tree, and hold as well
of a wrong spec beside a matching wrong checker.  Only a verdict on a
value named from outside tells the two apart, which is what each pin
below is.

WHAT THIS RESTATES.  Rocq keeps no worked `Example`s over this checker:
its `Checks/Cases/Kernel/Futex/Syscalls.v` is about the spec, and every
one of its cases is twinned in `Checks/Cases/Kernel/Futex/Syscalls.lean`,
`futex_copyins_exact` — the ledger theorem stated in the Rocq CHECKER
file — included.  So this file mirrors no Rocq Cases file and carries no
coverage header for `check_lean_cases_parity.py` to read (that tool lists
it as unmirrored, which is a status and not a finding); the `Rocq:` line
on each PORTED definition and lemma of `Checks/Sys/Kernel/Futex/Syscalls.lean`
is the mapping, and its five helper lemmas carry none because they twin
nothing.  What the pins below restate is the spec pins' fixtures
and cases, put to the checker instead: the same addresses, the same word,
the same effects, so that a reader can lay the two files side by side.
The dispatcher twin and the arm record exist (`Checks/Sys/Dispatch.lean`,
`Checks/Sys/Table.lean`); the ARM for 98 and its row in `checked_table`
are the registration step's (BRIEF.md section 5, CHECK, ticket
V-Kernel-Futex-Syscalls), so each pin is stated on `check_futex i uaddr op
val utime eff m` directly — the body of the arm that row will hold — and
is one line over `check_syscall` once the registration lands.  What a restatement loses is the register file: which
of a0–a3 the arm reads and that a4 and a5 are never read.  Those are the
registration's to pin, and go with it; here `uaddr2` and `val3` simply do
not exist, which is the checker's own statement that a private wake and
wait never look at them.

WHICH PROBES REACH THIS FILE.  The harness runs the EXTRACTED ROCQ model
(`check.sh` extracts it), so no Lean definition is ever evaluated against
a trace; a probe citation here says that the Rocq checker, on the recorded
run, gave the verdict this pin states of the Lean one, and the tool that
reads the citation opens the recorded run and requires the return the pin
names to be the one the kernel gave.  Two probes state these facts of the
Rocq side.  `testing/syscall-check/tests/futex_private.c` runs the wake
and wait this checker models — `wake`, `wake_junk`, `wake_counts`,
`wake_unmapped`, `misaligned`, `past_task_size`, `wait_eagain` — and
stages the lies `ret=1`, `ret=-EFAULT`, `ret=0`, `drop-copyins` and
`smuggle-copyin`; `testing/syscall-check/tests/unmodeled_futex.c` runs
the eight shapes the model declines.  The fixtures stand in for the
probe's addresses: the word at 4096 for the probe's page (69632 in every
recorded run of `futex_private.c`, 69656 in `unmodeled_futex.c`'s), 8192
for the hole `wake_unmapped` and `wait_unmapped` probe, and the word 7
against `val` 8 for the probe's word 0 against `val` 1 — the mismatch is
what is tested, not the two values.  The three timeout pins — the
checker's decline, its `≠ CheckOk` twin and the witness's — deviate on
purpose and say so.  Every pin that no probe case states cites the kernel
line instead, and the rejections cite the kernel in any case: a lie the
kernel never tells has no conforming run to open.

WHAT IS PINNED BEYOND THE SPEC'S FIXTURES.  Verdicts on effects the spec
never produces and the spec pins therefore never name: the count a wake
did not perform, the errno of the OTHER gate, an errno truncated to its
low word, the right errno with a ledger beside it (a wake that read
memory, a refused address that was read anyway), the -EAGAIN of a
mismatch with its four-byte read dropped, lengthened, moved or doubled,
and a write beside it; and, on every refusal path, the right errno with
each of the five ledger fields filled, because `check_ret_only` reads the
whole effect and a checker that read the return alone would pass every
one of them.  Three addresses neither probe reaches: the last aligned
word in range and 2^64 - 4, whose range wraps, which the spec pins name
(`last_in_range_wake_is_zero`, `wrapped_wake_is_efault`), and NULL, which
they do not — `access_ok` admits it and a private wake answers 0 for it,
read off the kernel alone.  The order of the checker's tests over a symbolic
effect: a timeout declines before the address is judged, so an effect the
checker never inspects is `CheckUnmodeled` on a misaligned address with a
timeout and -EINVAL without one.  And, of the witness, WHICH outcome it
names on each path: `futex_witness_ok` says the outcome is admitted and
cannot say which one it is, so the last section pins that, and that every
outcome the witness names the checker accepts.

HOW THE PINS ARE PROVED.  No pin over the checker or the witness is
`rfl` (the three fixture identities are): the unifier behind `rfl` walks
into the alignment test's `Int.fmod` and the range test's comparison
against `TASK_SIZE` on a literal address and does not come back
(`Checks/Cases/Kernel/Futex/Syscalls.lean` closes its concrete spec pins
with `sys_norm` too, and gives no reason; this is the one).  A checker pin runs `check_norm`: one
`simp +decide only` pass that opens the checker, the two acceptors and the
ledger helpers, reads the fixture memory through the projections the spec
pins registered, and decides the closed gates; `sys_norm` finishes
whatever that pass leaves.  A witness pin runs `witness_norm`, the same
pass over the witness.  A `≠ CheckOk m' evs` twin is not re-evaluated: it
rewrites with the positive pin it twins and closes on the constructor
mismatch, so the two are one evaluation stated with both polarities.  The
model is symbolic throughout — `m`, never a fixture — because the checker
reads none of it, and a pin over every model says so.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE.  What these pins
prove is that this checker and a named line of Linux agree on what is
accepted, what is refused, and what is declined. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Futex.Syscalls

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Futex.Syscalls
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Futex.Syscalls
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Futex.Syscalls
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The fixtures

The addresses and the two words are `Checks/Cases/Kernel/Futex/Syscalls.lean`'s
— `futex_addr` holding 7, `unmapped_addr`, `misaligned_addr`,
`past_task_size`, `misaligned_past`, `last_in_range`, and the all-ones
word — so that spec and checker are pinned on the same memory.  The
input is restated under a name of this file's own, for a reason outside
Lean: the tool that opens a probe citation reads the syscall number a pin
is about off a `mkInput` in the pin's own file, and the spec file's
`futex_input` is one import away from it.  The two are the same input,
and the first lemma says so. -/

/-- The register file of a `futex` call over the fixture word: syscall 98,
the given registers, `futex_mem` readable and nothing writable.  The
checker takes its arguments explicitly, so the register list is what the
tracer would have recorded and nothing the checker reads. -/
def futex_call (args : List word) : SyscallInput :=
  SyscallInput.mkInput 98 args futex_mem (fun _ => none)

/-- The same over the all-ones word. -/
def futex_call_ff (args : List word) : SyscallInput :=
  SyscallInput.mkInput 98 args futex_mem_ff (fun _ => none)

/-- The two inputs are the spec file's fixtures under another name, so
every reading the spec pins registered applies to them unchanged.
model: a fixture identity, the rewrite `check_norm` opens the input with. -/
theorem futex_call_eq (args : List word) : futex_call args = futex_input args := rfl

/-- …and the all-ones one.
model: a fixture identity, the rewrite `check_norm` opens the input with. -/
theorem futex_call_ff_eq (args : List word) : futex_call_ff args = futex_input_ff args := rfl

/-- One fixture of this file's own: the word 7 at the LAST aligned address
inside the range, `last_in_range`, and `none` everywhere else.  The spec
pins wake there; a wait there is what tells a range test of the right
width from one that is off by a word, which no spec fixture can. -/
def futex_mem_top : word → Option byte := bytes_at last_in_range [7, 0, 0, 0]

/-- The syscall input over that word. -/
def futex_call_top (args : List word) : SyscallInput :=
  SyscallInput.mkInput 98 args futex_mem_top (fun _ => none)

/-- The readable memory of every input over the top word.
model: a fixture projection, a rewrite for `check_norm`. -/
theorem in_mem_futex_call_top (args : List word) :
    (futex_call_top args).in_mem = futex_mem_top := rfl

/-- The four bytes of the top word, as `read_bytes_map` reads them.
model: a closed read off the fixture memory, a rewrite for `check_norm`. -/
theorem read_top_word :
    read_bytes_map futex_mem_top last_in_range (Z_to_bv 64 FUTEX_WORD_SIZE) = some [7, 0, 0, 0] := by
  decide

/-- Nothing is mapped at 4100 — the fixture word ends at 4099 — so the
read of a word there is `none`; the pins that tell a four-byte alignment
test from an eight-byte one need it.
model: a closed read off the fixture memory, a rewrite for `check_norm`. -/
theorem read_word_past_the_fixture :
    read_bytes_map futex_mem 4100 (Z_to_bv 64 FUTEX_WORD_SIZE) = none := by
  decide

/-- Nothing is mapped at NULL either.
model: a closed read off the fixture memory, a rewrite for `check_norm`. -/
theorem read_word_at_null :
    read_bytes_map futex_mem 0 (Z_to_bv 64 FUTEX_WORD_SIZE) = none := by
  decide

/-- Evaluate a closed call of the checker: open the checker, the two
acceptors and the ledger helpers, decide every closed gate, read the
fixture memory with the `sys_simp` set, and finish with `sys_norm` if a
read is left.  The header says why this and not `rfl`.  `local`, because
`Checks/Cases/Checks/Sys/Kernel/Groups.lean` declares a `check_norm` of
its own and a module importing both would otherwise parse the word two
ways. -/
local macro "check_norm" : tactic =>
  `(tactic| (simp +decide only [check_futex, check_futex_wake_private, check_futex_wait_private,
      check_ret_only, check_ret_only_copyins, clear_copyins, with_copyins, access_ranges_eqb,
      futex_call_eq, futex_call_ff_eq, in_mem_futex_call_top, read_top_word,
      read_word_past_the_fixture, read_word_at_null, sys_simp,
      ↓reduceIte]; first | done | sys_norm))

/-- Evaluate a closed witness the same way; `local` for the same reason. -/
local macro "witness_norm" : tactic =>
  `(tactic| (simp +decide only [futex_witness, ret_outcome, futex_call_eq, futex_call_ff_eq,
      in_mem_futex_call_top, read_top_word, read_word_past_the_fixture, read_word_at_null,
      sys_simp, ↓reduceIte]; first | done | sys_norm))

section Wake

/-! ## `FUTEX_WAKE_PRIVATE` (129): the count is 0 and nothing else is read

`futex_wake` (kernel/futex/waitwake.c:155-200, Linux v6.18.46) builds the
private key — `get_futex_key` at :165-167, which for a private futex
records the mm and the address (kernel/futex/core.c:624-630) and resolves
no page — and returns the `ret` it left at 0 once its bucket holds no
waiter matching the key; no task shares this mm to have queued one.  So
the answer is 0 whatever `val` says, whatever `utime` holds, and whether
or not the address is mapped. -/

/-- A private wake of a mapped, aligned word is 0 on every model, with
nothing written and no event.  The probe's word is 0 and its count
`INT_MAX`; the count is not read.
probe: testing/syscall-check/tests/futex_private.c#conform -- wake -/
theorem check_wake_accepts_zero (m : Model) :
    check_futex (futex_call []) futex_addr 129 2147483647 0 (mkEffect 0 [] []) m
      = CheckOk m [] := by
  check_norm

/-- …on EVERY input, count and timeout word: none of the three reaches a
test.  The input's memory is never read on this path, so the pin is over
a symbolic input rather than the fixture.
kernel: kernel/futex/waitwake.c:futex_wake; kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem check_wake_reads_only_the_address (i : SyscallInput) (val utime : word) (m : Model) :
    check_futex i futex_addr 129 val utime (mkEffect 0 [] []) m = CheckOk m [] := by
  check_norm

/-- The probe's junk registers: `utime` 0x1234 with `uaddr2` 0x902 and
`val3` 2306 beside it.  A wake reads none of them; the last two do not
reach the checker at all.
probe: testing/syscall-check/tests/futex_private.c#conform -- wake_junk -/
theorem check_wake_junk_accepts_zero (m : Model) :
    check_futex (futex_call []) futex_addr 129 2147483647 4660 (mkEffect 0 [] []) m
      = CheckOk m [] := by
  check_norm

/-- A count of 0 and a count of -1 wake nobody either, and the kernel
does not refuse them: the one test `futex_wake` has on `nr_wake`, `if
((flags & FLAGS_STRICT) && !nr_wake) return 0;` (kernel/futex/waitwake.c:169-170,
Linux v6.18.46), sits behind a flag `futex_to_flags` never sets for this
syscall, and would answer the same 0 the empty bucket does.
probe: testing/syscall-check/tests/futex_private.c#conform -- wake_counts -/
theorem check_wake_counts_accept_zero (m : Model) :
    check_futex (futex_call []) futex_addr 129 0 0 (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_futex (futex_call []) futex_addr 129 18446744073709551615 0 (mkEffect 0 [] []) m
        = CheckOk m [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- An aligned, in-range address with NOTHING mapped there is 0: a private
wake resolves no page.  8192 stands for the hole the probe finds one page
past its own mapping.
probe: testing/syscall-check/tests/futex_private.c#conform -- wake_unmapped -/
theorem check_wake_unmapped_accepts_zero (m : Model) :
    check_futex (futex_call []) unmapped_addr 129 2147483647 0 (mkEffect 0 [] []) m
      = CheckOk m [] := by
  check_norm

/-- The -EFAULT a kernel that resolved the page would answer there is
refused: the one -EFAULT a private key can meet on this path is
`access_ok`'s (kernel/futex/core.c:573-574), and 8192 passes it.  The
`should_fail_futex` -EFAULT two lines on (:576-577) is a fault injector
that refuses until an administrator arms it; the spec's header carries
that argument.
kernel: kernel/futex/core.c:get_futex_key; kernel/futex/waitwake.c:futex_wake@v6.18.46 -/
theorem check_wake_unmapped_rejects_efault (m : Model) :
    check_futex (futex_call []) unmapped_addr 129 2147483647 0 (mkEffect (errno_ret EFAULT) [] [])
        m = CheckReject := by
  check_norm

/-- …which is the staged lie the harness refuses on the Rocq side.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:ret=-EFAULT -- wake_unmapped -/
theorem check_wake_unmapped_efault_not_accepted (m m' : Model) (evs : List event) :
    check_futex (futex_call []) unmapped_addr 129 2147483647 0 (mkEffect (errno_ret EFAULT) [] [])
        m ≠ CheckOk m' evs := by
  rw [check_wake_unmapped_rejects_efault]
  intro h
  cases h

/-- The last aligned word below `TASK_SIZE` is in range — `__access_ok`
is `addr <= limit - size` (include/asm-generic/access_ok.h:40) — and a
wake there is 0; the -EFAULT of a range test exclusive at the top, or
sized for eight bytes, is refused.  The spec's `last_in_range_wake_is_zero`
says what qemu-user does with this address; it is the pinned kernel's
answer that is pinned here.
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem check_last_in_range_wake_accepts_zero (m : Model) :
    check_futex (futex_call []) last_in_range 129 1 0 (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_futex (futex_call []) last_in_range 129 1 0 (mkEffect (errno_ret EFAULT) [] []) m
        = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- NULL IS IN RANGE: `__access_ok(0, 4)` is `0 <= limit - 4`, and
`get_futex_key` has no test of its own for a NULL pointer, so a private
wake at 0 is 0 like any other unmapped aligned address, and the -EFAULT
a checker with a NULL test would answer is refused.  Neither probe wakes
at NULL, so this is read off the kernel alone.
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/futex/core.c:get_futex_key; kernel/futex/waitwake.c:futex_wake@v6.18.46 -/
theorem check_null_wake_accepts_zero (i : SyscallInput) (val utime : word) (m : Model) :
    check_futex i 0 129 val utime (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_futex i 0 129 val utime (mkEffect (errno_ret EFAULT) [] []) m = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- A RANGE THAT WRAPS 2^64 IS -EFAULT: `__access_ok` compares the address
against `limit - size` and never `addr + size` against `limit`
(include/asm-generic/access_ok.h:40), so 2^64 - 4, aligned and with its
sum wrapping to 0, is refused by the range test, and the 0 of a checker
that added first is refused; 2^64 - 1 fails the alignment test ahead of
it.
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem check_wrapped_wake_accepts_efault (m : Model) :
    check_futex (futex_call []) 18446744073709551612 129 1 0 (mkEffect (errno_ret EFAULT) [] []) m
        = CheckOk m []
    ∧ check_futex (futex_call []) 18446744073709551612 129 1 0 (mkEffect 0 [] []) m = CheckReject
    ∧ check_futex (futex_call []) 18446744073709551615 129 1 0 (mkEffect (errno_ret EINVAL) [] []) m
        = CheckOk m [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- A count is refused: 1, the probe's `INT_MAX`, and a count in the high
word alone.  `futex_wake`'s loop (kernel/futex/waitwake.c:180-195) counts
a waiter per `futex_match`, and there is none to match.
kernel: kernel/futex/waitwake.c:futex_wake; kernel/futex/futex.h:futex_match@v6.18.46 -/
theorem check_wake_rejects_a_count (m : Model) :
    check_futex (futex_call []) futex_addr 129 2147483647 0 (mkEffect 1 [] []) m = CheckReject
    ∧ check_futex (futex_call []) futex_addr 129 2147483647 0 (mkEffect 2147483647 [] []) m
        = CheckReject
    ∧ check_futex (futex_call []) futex_addr 129 2147483647 0 (mkEffect 4294967296 [] []) m
        = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- …and the staged count of 1 is the lie the harness refuses.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:ret=1 -- wake -/
theorem check_wake_count_one_not_accepted (m m' : Model) (evs : List event) :
    check_futex (futex_call []) futex_addr 129 2147483647 0 (mkEffect 1 [] []) m
      ≠ CheckOk m' evs := by
  rw [check_wake_rejects_a_count m |>.1]
  intro h
  cases h

/-- The right count with anything beside it is refused: a store, a
zero-fill, an unmap, a copy, and a copy-in — a wake touches no user
memory in either direction, so its ledger is empty.  The address is
symbolic: the verdict does not read it.
kernel: kernel/futex/waitwake.c:futex_wake; kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem check_wake_rejects_every_other_ledger (p : word) (m : Model) :
    check_futex (futex_call []) futex_addr 129 2147483647 0 (mkEffect 0 [(p, [0, 0, 0, 0])] []) m
        = CheckReject
    ∧ check_futex (futex_call []) futex_addr 129 2147483647 0
        (SyscallEffect.mkEffectU 0 [] [(p, 4)] [] [] []) m = CheckReject
    ∧ check_futex (futex_call []) futex_addr 129 2147483647 0
        (SyscallEffect.mkEffectU 0 [] [] [(p, 4096)] [] []) m = CheckReject
    ∧ check_futex (futex_call []) futex_addr 129 2147483647 0
        (SyscallEffect.mkEffectU 0 [] [] [] [MemCopy.mkCopy p p 4] []) m = CheckReject
    ∧ check_futex (futex_call []) futex_addr 129 2147483647 0
        (SyscallEffect.mkEffectU 0 [] [] [] [] [(p, 8)]) m = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The staged copy-in — eight bytes at 0x10000, the probe's text page
(its first LOAD segment; the word's page is 0x11000) — is the ledger lie
the harness refuses.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:smuggle-copyin:0x10000:8 -- wake -/
theorem check_wake_smuggled_copyin_not_accepted (m m' : Model) (evs : List event) :
    check_futex (futex_call []) futex_addr 129 2147483647 0
        (SyscallEffect.mkEffectU 0 [] [] [] [] [(65536, 8)]) m ≠ CheckOk m' evs := by
  rw [(check_wake_rejects_every_other_ledger 65536 m).2.2.2.2]
  intro h
  cases h

end Wake

section KeyCheck

/-! ## `get_futex_key`: -EINVAL on alignment first, then -EFAULT on the range

`get_futex_key` (kernel/futex/core.c:548-770, Linux v6.18.46) decides
`if (unlikely((address % size) != 0)) return -EINVAL;` at :569-570 and
`if (unlikely(!access_ok(uaddr, size))) return -EFAULT;` at :573-574,
in that order, before it resolves anything.  Both commands reach it
first — `futex_wake` at kernel/futex/waitwake.c:165-167 and
`futex_wait_setup` at :617-619 (both Linux v6.18.46) — so these verdicts
are the same for a wait; the wait's are in the next section beside its
ledger. -/

/-- A misaligned address is -EINVAL.
probe: testing/syscall-check/tests/futex_private.c#conform -- misaligned -/
theorem check_misaligned_wake_accepts_einval (m : Model) :
    check_futex (futex_call []) misaligned_addr 129 1 0 (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] := by
  check_norm

/-- A kernel that let the address through to the count, and one that
answered the range gate's errno for the alignment gate's refusal, are
both refused.
kernel: kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem check_misaligned_wake_rejects_the_lies (m : Model) :
    check_futex (futex_call []) misaligned_addr 129 1 0 (mkEffect 0 [] []) m = CheckReject
    ∧ check_futex (futex_call []) misaligned_addr 129 1 0 (mkEffect (errno_ret EFAULT) [] []) m
        = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- …and the staged 0 is the lie the harness refuses.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:ret=0 -- misaligned -/
theorem check_misaligned_wake_zero_not_accepted (m m' : Model) (evs : List event) :
    check_futex (futex_call []) misaligned_addr 129 1 0 (mkEffect 0 [] []) m ≠ CheckOk m' evs := by
  rw [(check_misaligned_wake_rejects_the_lies m).1]
  intro h
  cases h

/-- The errno is the WHOLE register's: `do_futex` returns `long` and
`syscall_handler` stores it whole, `regs->a0 = fn(regs)`
(arch/riscv/include/asm/syscall.h:112), so -EINVAL in a0 is
0xffffffffffffffea and never its low word 0xffffffea.  A checker comparing
the low 32 bits of a0 would take this for -EINVAL; it is refused.
kernel: kernel/futex/syscalls.c:futex; arch/riscv/include/asm/syscall.h:syscall_handler@v6.18.46 -/
theorem check_misaligned_wake_rejects_a_truncated_errno (m : Model) :
    check_futex (futex_call []) misaligned_addr 129 1 0 (mkEffect 4294967274 [] []) m
      = CheckReject := by
  check_norm

/-- THE ALIGNMENT IS FOUR BYTES at the checker too: 4098 (≡ 2 mod 4) is
-EINVAL from both commands, its 0 is refused, and 4100 (≡ 4 mod 8) is a
wake of 0 although nothing is readable there, and a wait that DECLINES
for the unreadable word rather than answering -EINVAL.  A checker testing
`% 2` would accept the 0 at 4098; one testing `% 8` would refuse it at
4100 and answer -EINVAL for the wait.
`size` is `futex_size(flags)` = 4 (kernel/futex/futex.h:77-80) on the
`FLAGS_SIZE_32` every op word of this syscall carries.
kernel: kernel/futex/core.c:get_futex_key; kernel/futex/futex.h:futex_size@v6.18.46 -/
theorem check_alignment_is_four_bytes (eff : SyscallEffect) (m : Model) :
    check_futex (futex_call []) 4098 129 1 0 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_futex (futex_call []) 4098 128 7 0 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_futex (futex_call []) 4098 129 1 0 (mkEffect 0 [] []) m = CheckReject
    ∧ check_futex (futex_call []) 4100 129 1 0 (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_futex (futex_call []) 4100 128 7 0 eff m = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- THE REFUSALS READ THE WHOLE EFFECT: -EINVAL for the misaligned address
and -EFAULT for the one past the range are each refused with a store, a
zero-fill, an unmap, a copy or a copy-in beside them.  `get_futex_key`
returns before either command touches user memory, so a ledger beside its
errno is not the kernel's; a checker comparing the return alone on these
two paths would accept every one of the ten.  The address on the ledger
is symbolic.
kernel: kernel/futex/core.c:get_futex_key; kernel/futex/waitwake.c:futex_wake@v6.18.46 -/
theorem check_wake_refusals_reject_every_ledger (p : word) (m : Model) :
    check_futex (futex_call []) misaligned_addr 129 1 0
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [(p, [0, 0, 0, 0])] [] [] [] []) m = CheckReject
    ∧ check_futex (futex_call []) misaligned_addr 129 1 0
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [(p, 4)] [] [] []) m = CheckReject
    ∧ check_futex (futex_call []) misaligned_addr 129 1 0
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(p, 4096)] [] []) m = CheckReject
    ∧ check_futex (futex_call []) misaligned_addr 129 1 0
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy p p 4] []) m
        = CheckReject
    ∧ check_futex (futex_call []) misaligned_addr 129 1 0
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(p, 4)]) m = CheckReject
    ∧ check_futex (futex_call []) past_task_size 129 1 0
        (SyscallEffect.mkEffectU (errno_ret EFAULT) [(p, [0, 0, 0, 0])] [] [] [] []) m = CheckReject
    ∧ check_futex (futex_call []) past_task_size 129 1 0
        (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [(p, 4)] [] [] []) m = CheckReject
    ∧ check_futex (futex_call []) past_task_size 129 1 0
        (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [(p, 4096)] [] []) m = CheckReject
    ∧ check_futex (futex_call []) past_task_size 129 1 0
        (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [MemCopy.mkCopy p p 4] []) m
        = CheckReject
    ∧ check_futex (futex_call []) past_task_size 129 1 0
        (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(p, 4)]) m = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The first aligned address past the user range is -EFAULT:
`access_ok(2^47, 4)` fails on Sv48, and it is the RANGE that failed.
probe: testing/syscall-check/tests/futex_private.c#conform -- past_task_size -/
theorem check_past_range_wake_accepts_efault (m : Model) :
    check_futex (futex_call []) past_task_size 129 1 0 (mkEffect (errno_ret EFAULT) [] []) m
      = CheckOk m [] := by
  check_norm

/-- A kernel whose user range ran past `TASK_SIZE`, and one that answered
the alignment gate's errno for an aligned address, are refused.
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem check_past_range_wake_rejects_the_lies (m : Model) :
    check_futex (futex_call []) past_task_size 129 1 0 (mkEffect 0 [] []) m = CheckReject
    ∧ check_futex (futex_call []) past_task_size 129 1 0 (mkEffect (errno_ret EINVAL) [] []) m
        = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- …and the staged 0 is the lie the harness refuses.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:ret=0 -- past_task_size -/
theorem check_past_range_wake_zero_not_accepted (m m' : Model) (evs : List event) :
    check_futex (futex_call []) past_task_size 129 1 0 (mkEffect 0 [] []) m ≠ CheckOk m' evs := by
  rw [(check_past_range_wake_rejects_the_lies m).1]
  intro h
  cases h

/-- ORDER IS BEHAVIOUR: an address misaligned AND past the range is
-EINVAL, and the -EFAULT a checker with the two gates the other way
round would accept is refused.
kernel: kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem check_misaligned_past_range_is_einval_first (m : Model) :
    check_futex (futex_call []) misaligned_past 129 1 0 (mkEffect (errno_ret EINVAL) [] []) m
        = CheckOk m []
    ∧ check_futex (futex_call []) misaligned_past 129 1 0 (mkEffect (errno_ret EFAULT) [] []) m
        = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

end KeyCheck

section Wait

/-! ## `FUTEX_WAIT_PRIVATE` (128) with a NULL timeout

`futex_wait_setup` (kernel/futex/waitwake.c:591-664, Linux v6.18.46) runs
`get_futex_key` at :617-619, reads the word through
`futex_get_value_locked` (kernel/futex/futex.h:332-341) at :627, and
answers `if (uval != val) { … return -EWOULDBLOCK; }` at :642-645 —
`EWOULDBLOCK` is `EAGAIN` (include/uapi/asm-generic/errno.h:22, Linux
v6.18.46).  A word that matches is queued and slept on (:660, then
`__futex_wait`), which the model declines.  The `val` compared is the
syscall's `u32 val` (kernel/futex/syscalls.c:188-190, Linux v6.18.46): the
register's low word. -/

/-- The word holds 7 and `val` is 8: -EAGAIN, with exactly the four-byte
read of the word on the ledger and nothing else.  The probe's word is 0
and its `val` 1; the mismatch is what is tested.
probe: testing/syscall-check/tests/futex_private.c#conform -- wait_eagain -/
theorem check_wait_mismatch_accepts_eagain_with_the_read (m : Model) :
    check_futex (futex_call []) futex_addr 128 8 0
        (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(futex_addr, 4)]) m
      = CheckOk m [] := by
  check_norm

/-- A kernel claiming the wait slept and was woken — 0, with or without
the read — is refused: a mismatch never reaches `futex_queue` at :660.
kernel: kernel/futex/waitwake.c:futex_wait_setup,__futex_wait@v6.18.46 -/
theorem check_wait_mismatch_rejects_success (m : Model) :
    check_futex (futex_call []) futex_addr 128 8 0 (mkEffect 0 [] []) m = CheckReject
    ∧ check_futex (futex_call []) futex_addr 128 8 0
        (SyscallEffect.mkEffectU 0 [] [] [] [] [(futex_addr, 4)]) m = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- …and the staged 0 is the lie the harness refuses.  The mutation
replaces the return and nothing else, so the recorded lie still carries
the four-byte read: it is the second conjunct's shape, refused for the
return alone.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:ret=0 -- wait_eagain -/
theorem check_wait_mismatch_zero_not_accepted (m m' : Model) (evs : List event) :
    check_futex (futex_call []) futex_addr 128 8 0
        (SyscallEffect.mkEffectU 0 [] [] [] [] [(futex_addr, 4)]) m ≠ CheckOk m' evs := by
  rw [(check_wait_mismatch_rejects_success m).2]
  intro h
  cases h

/-- The right errno with the read DROPPED is refused: -EAGAIN is the
answer of a comparison against a word the kernel fetched from user
memory at :627, so a ledger without that read is not the kernel's.
kernel: kernel/futex/futex.h:futex_get_value_locked; kernel/futex/waitwake.c:futex_wait_setup; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem check_wait_mismatch_rejects_a_dropped_read (m : Model) :
    check_futex (futex_call []) futex_addr 128 8 0 (mkEffect (errno_ret EAGAIN) [] []) m
      = CheckReject := by
  check_norm

/-- …which is the staged erasure the harness refuses.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:drop-copyins -- wait_eagain -/
theorem check_wait_mismatch_dropped_read_not_accepted (m m' : Model) (evs : List event) :
    check_futex (futex_call []) futex_addr 128 8 0 (mkEffect (errno_ret EAGAIN) [] []) m
      ≠ CheckOk m' evs := by
  rw [check_wait_mismatch_rejects_a_dropped_read]
  intro h
  cases h

/-- The read is EXACTLY four bytes at `uaddr`, once: a longer read, a read
moved by one byte, and the same read twice are refused.  `futex_get_value_locked`
fetches one `u32` from `uaddr`.
kernel: kernel/futex/futex.h:futex_get_value_locked; kernel/futex/waitwake.c:futex_wait_setup; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem check_wait_mismatch_rejects_a_wrong_ledger (m : Model) :
    check_futex (futex_call []) futex_addr 128 8 0
        (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(futex_addr, 8)]) m = CheckReject
    ∧ check_futex (futex_call []) futex_addr 128 8 0
        (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(misaligned_addr, 4)]) m
        = CheckReject
    ∧ check_futex (futex_call []) futex_addr 128 8 0
        (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(futex_addr, 4), (futex_addr, 4)])
        m = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- The right errno and the right read with a store beside them is
refused: a plain wait writes nothing.  The store's address is symbolic.
kernel: kernel/futex/waitwake.c:futex_wait_setup; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem check_wait_mismatch_rejects_a_write (p : word) (m : Model) :
    check_futex (futex_call []) futex_addr 128 8 0
        (SyscallEffect.mkEffectU (errno_ret EAGAIN) [(p, [0, 0, 0, 0])] [] [] [] [(futex_addr, 4)])
        m = CheckReject := by
  check_norm

/-- …and so are a zero-fill, an unmap and a copy beside them:
`check_ret_only_copyins` clears the ledger and hands the rest of the
effect to `check_ret_only`, which reads every field.  A checker that
cleared more than the ledger would accept these three.  And the WRONG
errno with the right read is refused too: -EFAULT is `get_futex_key`'s
answer, given before the word is read.
kernel: kernel/futex/waitwake.c:futex_wait_setup; kernel/futex/core.c:get_futex_key; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem check_wait_mismatch_rejects_every_other_ledger (p : word) (m : Model) :
    check_futex (futex_call []) futex_addr 128 8 0
        (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [(p, 4)] [] [] [(futex_addr, 4)]) m
        = CheckReject
    ∧ check_futex (futex_call []) futex_addr 128 8 0
        (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [(p, 4096)] [] [(futex_addr, 4)]) m
        = CheckReject
    ∧ check_futex (futex_call []) futex_addr 128 8 0
        (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [MemCopy.mkCopy p p 4] [(futex_addr, 4)])
        m = CheckReject
    ∧ check_futex (futex_call []) futex_addr 128 8 0
        (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(futex_addr, 4)]) m
        = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- THE WORD IS READ LITTLE-ENDIAN by the checker too: the bytes `7, 0, 0,
0` are 7, so a `val` of 0x07000000 mismatches and is -EAGAIN with the
read; a checker assembling the bytes the other way round would decline
here for a match.  riscv is little-endian and `get_user` fetches the
`u32` in that order; the spec's `wait_reads_little_endian` is the same
case over the spec.
kernel: kernel/futex/waitwake.c:futex_wait_setup; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem check_wait_reads_little_endian (m : Model) :
    check_futex (futex_call []) futex_addr 128 117440512 0
        (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(futex_addr, 4)]) m
      = CheckOk m [] := by
  check_norm

/-- The word holds 7 and `val` is 7: the kernel queues the waiter and
sleeps (:660, then `__futex_wait` through `futex_wait`), and the model
declines WHATEVER effect is offered — the effect is symbolic here, so no
answer, right or wrong, is inspected.
kernel: kernel/futex/waitwake.c:futex_wait_setup,futex_wait@v6.18.46 -/
theorem check_wait_match_declines (eff : SyscallEffect) (m : Model) :
    check_futex (futex_call []) futex_addr 128 7 0 eff m = CheckUnmodeled := by
  check_norm

/-- A wait on an aligned, in-range address with nothing mapped there:
`futex_get_value_locked` fails at :627, and the `get_user` at :632 that
would page the word in returns -EFAULT for an address no mapping backs
(:633-634) — a page fault this model does not follow, so it declines on
every effect rather than answer for it.
kernel: kernel/futex/futex.h:futex_get_value_locked; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem check_wait_unmapped_declines (eff : SyscallEffect) (m : Model) :
    check_futex (futex_call []) unmapped_addr 128 0 0 eff m = CheckUnmodeled := by
  check_norm

/-- …so no answer there is accepted, which is the fail-closed run the
harness records.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wait_unmapped -/
theorem check_wait_unmapped_not_accepted (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    check_futex (futex_call []) unmapped_addr 128 0 0 eff m ≠ CheckOk m' evs := by
  rw [check_wait_unmapped_declines]
  intro h
  cases h

/-- A wait at NULL is the unmapped case, not a refusal: `access_ok(0, 4)`
passes (the wake pin above), so `futex_wait_setup` reaches the read at
:627 and the `get_user` at :632 faults on the page no mapping backs.  The
model declines; a checker with a NULL test would answer -EFAULT, and one
that skipped the read would answer -EAGAIN for the mismatch.
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/futex/core.c:get_futex_key; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem check_wait_at_null_declines (eff : SyscallEffect) (m : Model) :
    check_futex (futex_call []) 0 128 8 0 eff m = CheckUnmodeled := by
  check_norm

/-- A wait with a non-NULL `utime` is declined on every effect: the
timeout is fetched at kernel/futex/syscalls.c:196-202 before `do_futex`
is called, and the timer it arms is not modeled.  The `val` here is 8
against the word 7 — a MISMATCH, where the probe's wait matches its word
and is ended by its timer — so that a checker which dropped the timeout
test would answer -EAGAIN here instead of declining for the match, and
the pin would see it.
kernel: kernel/futex/syscalls.c:futex,futex_cmd_has_timeout@v6.18.46 -/
theorem check_wait_with_a_timeout_declines (eff : SyscallEffect) (m : Model) :
    check_futex (futex_call []) futex_addr 128 8 8192 eff m = CheckUnmodeled := by
  check_norm

/-- …so no answer there is accepted, which is the fail-closed run the
harness records (its word matches and its timer fires: -ETIMEDOUT; the
pin's `val` mismatches instead, for the reason the pin above gives).
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wait_timeout -/
theorem check_wait_with_a_timeout_not_accepted (eff : SyscallEffect) (m m' : Model)
    (evs : List event) :
    check_futex (futex_call []) futex_addr 128 8 8192 eff m ≠ CheckOk m' evs := by
  rw [check_wait_with_a_timeout_declines]
  intro h
  cases h

/-- ORDER IS BEHAVIOUR: the timeout test outranks the key check.  A
misaligned address, or one past the range, with a timeout beside it is
declined, not -EINVAL or -EFAULT: `SYSCALL_DEFINE6(futex)` reads `utime`
at :196 and `get_futex_key` is reached only from `do_futex` at :207.
kernel: kernel/futex/syscalls.c:futex; kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem check_timeout_outranks_the_key_check (eff : SyscallEffect) (m : Model) :
    check_futex (futex_call []) misaligned_addr 128 8 8192 eff m = CheckUnmodeled
    ∧ check_futex (futex_call []) past_task_size 128 8 8192 eff m = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- THE TIMEOUT IS TESTED ON THE WHOLE REGISTER: `utime` is a pointer, and
`if (utime && futex_cmd_has_timeout(cmd))` (kernel/futex/syscalls.c:196)
tests all 64 bits of it, so a register whose low word is zero and whose
high word is not is a timeout, and the wait declines for it on every
effect.  A checker testing `abi_low32 utime` would take it for NULL and
answer the mismatch's -EAGAIN; the spec's
`wait_with_high_timeout_is_unmodeled` is the same case over the spec.
kernel: kernel/futex/syscalls.c:futex,futex_cmd_has_timeout@v6.18.46 -/
theorem check_wait_timeout_is_tested_whole (eff : SyscallEffect) (m : Model) :
    check_futex (futex_call []) futex_addr 128 8 4294967296 eff m = CheckUnmodeled := by
  check_norm

/-- `val` IS ITS LOW WORD: the parameter is `u32 val`, and `__SC_CAST`
narrows the register to it.  2^32 + 8 compares as 8 against the word 7
and is -EAGAIN with the read; 2^32 + 7 compares as 7 and is declined.
kernel: kernel/futex/syscalls.c:futex; include/linux/syscalls.h:__SC_CAST; kernel/futex/waitwake.c:futex_wait_setup; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem check_wait_val_is_its_low_word (eff : SyscallEffect) (m : Model) :
    check_futex (futex_call []) futex_addr 128 4294967304 0
        (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(futex_addr, 4)]) m
      = CheckOk m []
    ∧ check_futex (futex_call []) futex_addr 128 4294967303 0 eff m = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- THE COMPARISON IS 32 BITS WIDE, unsigned: against the all-ones word,
`val` 0xffffffff matches and is declined, 0xffff does not and is -EAGAIN
with the read, and the all-ones register narrows to 0xffffffff and
matches.  A two-byte or a sign-extending compare would answer otherwise
on one of the three.
kernel: kernel/futex/futex.h:futex_get_value_locked; kernel/futex/waitwake.c:futex_wait_setup; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem check_wait_compares_thirty_two_bits (eff : SyscallEffect) (m : Model) :
    check_futex (futex_call_ff []) futex_addr 128 4294967295 0 eff m = CheckUnmodeled
    ∧ check_futex (futex_call_ff []) futex_addr 128 65535 0
        (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(futex_addr, 4)]) m
        = CheckOk m []
    ∧ check_futex (futex_call_ff []) futex_addr 128 18446744073709551615 0 eff m
        = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- A misaligned wait is -EINVAL with an EMPTY ledger, and the same errno
with the word's read beside it is refused: `get_futex_key` at :617-619
returns before the read at :627.
kernel: kernel/futex/core.c:get_futex_key; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem check_misaligned_wait_accepts_einval_with_an_empty_ledger (m : Model) :
    check_futex (futex_call []) misaligned_addr 128 7 0 (mkEffect (errno_ret EINVAL) [] []) m
        = CheckOk m []
    ∧ check_futex (futex_call []) misaligned_addr 128 7 0
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(misaligned_addr, 4)]) m
        = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- …and a wait past the range is -EFAULT with an EMPTY ledger, for the
same reason.
kernel: kernel/futex/core.c:get_futex_key; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem check_past_range_wait_accepts_efault_with_an_empty_ledger (m : Model) :
    check_futex (futex_call []) past_task_size 128 7 0 (mkEffect (errno_ret EFAULT) [] []) m
        = CheckOk m []
    ∧ check_futex (futex_call []) past_task_size 128 7 0
        (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(past_task_size, 4)]) m
        = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- THE WAIT'S REFUSALS READ THE WHOLE EFFECT TOO: -EINVAL for the
misaligned address and -EFAULT for the one past the range are each
refused with a store, a zero-fill, an unmap or a copy beside them (the
copy-in beside each is the two pins above).  The wait arm spells its own
two gates, so the wake arm's pin does not cover it; a checker comparing
the return alone on these two paths would accept every one of the eight.
The address on the ledger is symbolic.
kernel: kernel/futex/core.c:get_futex_key; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem check_wait_refusals_reject_every_ledger (p : word) (m : Model) :
    check_futex (futex_call []) misaligned_addr 128 7 0
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [(p, [0, 0, 0, 0])] [] [] [] []) m = CheckReject
    ∧ check_futex (futex_call []) misaligned_addr 128 7 0
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [(p, 4)] [] [] []) m = CheckReject
    ∧ check_futex (futex_call []) misaligned_addr 128 7 0
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(p, 4096)] [] []) m = CheckReject
    ∧ check_futex (futex_call []) misaligned_addr 128 7 0
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy p p 4] []) m
        = CheckReject
    ∧ check_futex (futex_call []) past_task_size 128 7 0
        (SyscallEffect.mkEffectU (errno_ret EFAULT) [(p, [0, 0, 0, 0])] [] [] [] []) m = CheckReject
    ∧ check_futex (futex_call []) past_task_size 128 7 0
        (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [(p, 4)] [] [] []) m = CheckReject
    ∧ check_futex (futex_call []) past_task_size 128 7 0
        (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [(p, 4096)] [] []) m = CheckReject
    ∧ check_futex (futex_call []) past_task_size 128 7 0
        (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [MemCopy.mkCopy p p 4] []) m
        = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- ORDER IS BEHAVIOUR on the wait arm too: misaligned AND past the range
is -EINVAL, and the -EFAULT of the two gates the other way round is
refused.  The wait arm spells its own two gates, so the wake arm's pin
does not cover it.
kernel: kernel/futex/core.c:get_futex_key; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem check_misaligned_past_range_wait_is_einval_first (m : Model) :
    check_futex (futex_call []) misaligned_past 128 7 0 (mkEffect (errno_ret EINVAL) [] []) m
        = CheckOk m []
    ∧ check_futex (futex_call []) misaligned_past 128 7 0 (mkEffect (errno_ret EFAULT) [] []) m
        = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- THE RANGE TEST IS INCLUSIVE AT THE TOP on the wait arm too: a word at
the last aligned address inside the range is read and compared — -EAGAIN
with that read — and the -EFAULT of a range test off by one word, or
exclusive at the top, is refused.  `__access_ok` is `addr <= limit -
size` (include/asm-generic/access_ok.h:40) with `size` 4.
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/futex/core.c:get_futex_key; kernel/futex/waitwake.c:futex_wait_setup; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem check_last_in_range_wait_reads_the_word (m : Model) :
    check_futex (futex_call_top []) last_in_range 128 8 0
        (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(last_in_range, 4)]) m
        = CheckOk m []
    ∧ check_futex (futex_call_top []) last_in_range 128 8 0 (mkEffect (errno_ret EFAULT) [] []) m
        = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

end Wait

section OtherOps

/-! ## Every other op word is declined

The op word is tested WHOLE against 129 and 128.  `do_futex`
(kernel/futex/syscalls.c:112-159, Linux v6.18.46) dispatches on `cmd =
op & FUTEX_CMD_MASK` after `SYSCALL_DEFINE6(futex)` has read the timeout
and `FLAGS_CLOCKRT` has refused a command it does not decorate (:118-123):
a shared wake or wait, a bitset, a wake-op, a command outside the switch
(-ENOSYS at :158), and an op word with anything above bit 31 set (the
`int op` parameter drops it; the model does not) are each outside this
model, so the checker declines every effect for them. -/

/-- The op words the probe issues, each declined on every effect: the
shared wake (1) and wait (0), a private wake with a set high word
(2^32 + 129), a command outside `do_futex`'s switch (192), `FUTEX_CLOCK_REALTIME`
over a private WAKE (385 = 1 | 128 | 256), a private bitset wake (138)
and a private wake-op (133).  The shared wait carries `val` 8 against the
word 7, so that a checker admitting op 0 as a wait would answer -EAGAIN
here rather than decline for a match, and the pin would see it.
kernel: kernel/futex/syscalls.c:futex,do_futex@v6.18.46 -/
theorem check_other_ops_decline (eff : SyscallEffect) (m : Model) :
    check_futex (futex_call []) futex_addr 1 1 0 eff m = CheckUnmodeled
    ∧ check_futex (futex_call []) futex_addr 0 8 0 eff m = CheckUnmodeled
    ∧ check_futex (futex_call []) futex_addr 4294967425 2147483647 0 eff m = CheckUnmodeled
    ∧ check_futex (futex_call []) futex_addr 192 1 0 eff m = CheckUnmodeled
    ∧ check_futex (futex_call []) futex_addr 385 1 0 eff m = CheckUnmodeled
    ∧ check_futex (futex_call []) misaligned_addr 138 1 0 eff m = CheckUnmodeled
    ∧ check_futex (futex_call []) futex_addr 133 1 1 eff m = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The op words the spec pins beyond the probe's, declined the same way:
a private WAIT with a set high word (2^32 + 128, which `int op` would
make a wait and which the model tests whole), `FUTEX_CLOCK_REALTIME`
over a private WAIT (384 = 128 | 256, -ENOSYS in `do_futex` at :118-123
because `FUTEX_WAIT` is not among the three commands the flag decorates),
and the private bitset wake on the ALIGNED word, where only the bitset's
own -EINVAL is left in Linux and the decline is the op word's, not the
address's.  Each carries `val` 8 against the word 7 so that a checker
admitting the op as a wait would answer -EAGAIN rather than decline.
kernel: kernel/futex/syscalls.c:futex,do_futex@v6.18.46 -/
theorem check_spec_pinned_ops_decline (eff : SyscallEffect) (m : Model) :
    check_futex (futex_call []) futex_addr 4294967424 8 0 eff m = CheckUnmodeled
    ∧ check_futex (futex_call []) futex_addr 384 8 0 eff m = CheckUnmodeled
    ∧ check_futex (futex_call []) futex_addr 138 8 0 eff m = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- The shared wake's 0 is not accepted: the kernel answers it, and the
model declines rather than accept an answer whose key it does not model.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wake_shared -/
theorem check_shared_wake_not_accepted (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    check_futex (futex_call []) futex_addr 1 1 0 eff m ≠ CheckOk m' evs := by
  rw [(check_other_ops_decline eff m).1]
  intro h
  cases h

/-- A private wake whose high word is set is not accepted: the kernel's
`int op` drops the high word and wakes; the model tests the whole register.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wake_high -/
theorem check_high_wake_not_accepted (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    check_futex (futex_call []) futex_addr 4294967425 2147483647 0 eff m ≠ CheckOk m' evs := by
  rw [(check_other_ops_decline eff m).2.2.1]
  intro h
  cases h

/-- A command outside the switch is -ENOSYS in the kernel and declined
here.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- badop -/
theorem check_bad_op_not_accepted (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    check_futex (futex_call []) futex_addr 192 1 0 eff m ≠ CheckOk m' evs := by
  rw [(check_other_ops_decline eff m).2.2.2.1]
  intro h
  cases h

/-- `FUTEX_CLOCK_REALTIME` over a private wake is -ENOSYS in the kernel —
`do_futex` (kernel/futex/syscalls.c:118-123, Linux v6.18.46) allows the
flag on `FUTEX_WAIT_BITSET`, `FUTEX_WAIT_REQUEUE_PI` and `FUTEX_LOCK_PI2`
and refuses it on every other command — and declined here, where the op
word is simply not one of the two.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- clockrt -/
theorem check_clockrt_not_accepted (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    check_futex (futex_call []) futex_addr 385 1 0 eff m ≠ CheckOk m' evs := by
  rw [(check_other_ops_decline eff m).2.2.2.2.1]
  intro h
  cases h

/-- A private bitset wake is declined even where the kernel's answer is
the same -EINVAL a plain wake would give the misaligned address: the
command is outside the model.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- bitset_zero -/
theorem check_bitset_wake_not_accepted (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    check_futex (futex_call []) misaligned_addr 138 1 0 eff m ≠ CheckOk m' evs := by
  rw [(check_other_ops_decline eff m).2.2.2.2.2.1]
  intro h
  cases h

/-- A private wake-op writes user memory before it wakes; declined.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wake_op -/
theorem check_wake_op_not_accepted (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    check_futex (futex_call []) futex_addr 133 1 1 eff m ≠ CheckOk m' evs := by
  rw [(check_other_ops_decline eff m).2.2.2.2.2.2]
  intro h
  cases h

end OtherOps

section Witness

/-! ## The witness: which outcome it names

A witness is one outcome the spec admits, computed from the arguments and
the input with no effect to check; `futex_witness_ok` says it is admitted,
which is the receptiveness half of the arm the registration step builds.
What that lemma cannot say is WHICH outcome the witness names, so each pin
below states it — the kernel's answer on the path the model models,
`Unmodeled` on the path it declines — and the last one that whatever the
witness names, the checker accepts. -/

/-- A private wake of the fixture word is 0 on every input, count,
timeout word and model.
kernel: kernel/futex/waitwake.c:futex_wake; kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem futex_witness_wake_is_zero (i : SyscallInput) (val utime : word) (m : Model) :
    futex_witness futex_addr 129 val utime i m = Ok (mkEffect 0 [] []) m [] := by
  witness_norm

/-- A misaligned address is -EINVAL from both commands, before any read.
kernel: kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem futex_witness_misaligned_is_einval (i : SyscallInput) (val utime : word) (m : Model) :
    futex_witness misaligned_addr 129 val utime i m = Ok (mkEffect (errno_ret EINVAL) [] []) m []
    ∧ futex_witness misaligned_addr 128 val 0 i m = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  refine ⟨?_, ?_⟩ <;> witness_norm

/-- An address past the range is -EFAULT from both commands.
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem futex_witness_past_range_is_efault (i : SyscallInput) (val utime : word) (m : Model) :
    futex_witness past_task_size 129 val utime i m = Ok (mkEffect (errno_ret EFAULT) [] []) m []
    ∧ futex_witness past_task_size 128 val 0 i m = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  refine ⟨?_, ?_⟩ <;> witness_norm

/-- Misaligned AND past the range names -EINVAL: the witness keeps the
kernel's order.
kernel: kernel/futex/core.c:get_futex_key@v6.18.46 -/
theorem futex_witness_misaligned_past_range_is_einval (i : SyscallInput) (val : word) (m : Model) :
    futex_witness misaligned_past 129 val 0 i m = Ok (mkEffect (errno_ret EINVAL) [] []) m []
    ∧ futex_witness misaligned_past 128 val 0 i m = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  refine ⟨?_, ?_⟩ <;> witness_norm

/-- A mismatching wait names -EAGAIN with the word's read on the ledger.
probe: testing/syscall-check/tests/futex_private.c#conform -- wait_eagain -/
theorem futex_witness_wait_mismatch_is_eagain_with_the_read (m : Model) :
    futex_witness futex_addr 128 8 0 (futex_call []) m
      = Ok (with_copyins [(futex_addr, FUTEX_WORD_SIZE_nat)] (mkEffect (errno_ret EAGAIN) [] []))
          m [] := by
  witness_norm

/-- A matching wait names `Unmodeled`: the kernel sleeps.
kernel: kernel/futex/waitwake.c:futex_wait_setup,futex_wait@v6.18.46 -/
theorem futex_witness_wait_match_is_unmodeled (m : Model) :
    futex_witness futex_addr 128 7 0 (futex_call []) m = Unmodeled := by
  witness_norm

/-- A wait on an unmapped word names `Unmodeled`.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wait_unmapped -/
theorem futex_witness_wait_unmapped_is_unmodeled (m : Model) :
    futex_witness unmapped_addr 128 0 0 (futex_call []) m = Unmodeled := by
  witness_norm

/-- A wait with a timeout names `Unmodeled`, before the address is judged.
The `val` is 8 against the word 7, a mismatch where the probe's wait
matches and is ended by its timer, for the checker pin's reason: a
witness that dropped the timeout test would name -EAGAIN here instead.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wait_timeout -/
theorem futex_witness_wait_with_a_timeout_is_unmodeled (m : Model) :
    futex_witness futex_addr 128 8 8192 (futex_call []) m = Unmodeled
    ∧ futex_witness misaligned_addr 128 8 8192 (futex_call []) m = Unmodeled := by
  refine ⟨?_, ?_⟩ <;> witness_norm

/-- …and so does a timeout whose low word alone is zero: the witness tests
the whole register as the checker does.
kernel: kernel/futex/syscalls.c:futex,futex_cmd_has_timeout@v6.18.46 -/
theorem futex_witness_timeout_is_tested_whole (m : Model) :
    futex_witness futex_addr 128 8 4294967296 (futex_call []) m = Unmodeled := by
  witness_norm

/-- THE WITNESS KEEPS THE CHECKER'S WIDTHS.  Alignment is four bytes: the
wake at 4100 names 0 and the wait there names `Unmodeled` for the
unreadable word, where a witness testing `% 8` would name -EINVAL for
both.  The range is inclusive at the top and sized for four bytes: the
wake at the last aligned word names 0 and the wait there names -EAGAIN
with the read, where a witness sized for eight would name -EFAULT.  NULL
is in range and a wake there names 0.  And the wrapping address names
-EFAULT.
kernel: include/asm-generic/access_ok.h:__access_ok; kernel/futex/core.c:get_futex_key; kernel/futex/futex.h:futex_size; kernel/futex/waitwake.c:futex_wait_setup; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem futex_witness_keeps_the_widths (i : SyscallInput) (val utime : word) (m : Model) :
    futex_witness 4100 129 val utime i m = Ok (mkEffect 0 [] []) m []
    ∧ futex_witness 4100 128 7 0 (futex_call []) m = Unmodeled
    ∧ futex_witness last_in_range 129 val utime i m = Ok (mkEffect 0 [] []) m []
    ∧ futex_witness last_in_range 128 8 0 (futex_call_top [])  m
        = Ok (with_copyins [(last_in_range, FUTEX_WORD_SIZE_nat)] (mkEffect (errno_ret EAGAIN) [] []))
            m []
    ∧ futex_witness 0 129 val utime i m = Ok (mkEffect 0 [] []) m []
    ∧ futex_witness 18446744073709551612 129 val utime i m
        = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- `val` IS ITS LOW WORD at the witness too, and the compare is 32 bits
wide and unsigned: 2^32 + 8 names -EAGAIN with the read and 2^32 + 7
names `Unmodeled` against the word 7; against the all-ones word,
0xffffffff names `Unmodeled` and 0xffff names -EAGAIN.  A witness
comparing the whole register, or sign-extending the word, would name the
other outcome on one of each pair.
kernel: kernel/futex/syscalls.c:futex; include/linux/syscalls.h:__SC_CAST; kernel/futex/waitwake.c:futex_wait_setup; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem futex_witness_val_is_its_low_word (m : Model) :
    futex_witness futex_addr 128 4294967304 0 (futex_call []) m
        = Ok (with_copyins [(futex_addr, FUTEX_WORD_SIZE_nat)] (mkEffect (errno_ret EAGAIN) [] []))
            m []
    ∧ futex_witness futex_addr 128 4294967303 0 (futex_call []) m = Unmodeled
    ∧ futex_witness futex_addr 128 4294967295 0 (futex_call_ff []) m = Unmodeled
    ∧ futex_witness futex_addr 128 65535 0 (futex_call_ff []) m
        = Ok (with_copyins [(futex_addr, FUTEX_WORD_SIZE_nat)] (mkEffect (errno_ret EAGAIN) [] []))
            m [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- A shared wake names `Unmodeled`.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- wake_shared -/
theorem futex_witness_shared_wake_is_unmodeled (m : Model) :
    futex_witness futex_addr 1 1 0 (futex_call []) m = Unmodeled := by
  witness_norm

/-- THE OP IS TESTED WHOLE at the witness too, and only the two private
words pass: the shared wait (0), the wake and the wait with a set high
word (2^32 + 129, 2^32 + 128) and `FUTEX_CLOCK_REALTIME` over the private
wait (384) each name `Unmodeled`, with `val` 8 against the word 7 so that
a witness admitting any of them as a wait would name -EAGAIN instead.
kernel: kernel/futex/syscalls.c:futex,do_futex@v6.18.46 -/
theorem futex_witness_other_ops_are_unmodeled (m : Model) :
    futex_witness futex_addr 0 8 0 (futex_call []) m = Unmodeled
    ∧ futex_witness futex_addr 4294967425 8 0 (futex_call []) m = Unmodeled
    ∧ futex_witness futex_addr 4294967424 8 0 (futex_call []) m = Unmodeled
    ∧ futex_witness futex_addr 384 8 0 (futex_call []) m = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- An op word outside the switch names `Unmodeled`.
probe: testing/syscall-check/tests/unmodeled_futex.c#fail-closed --expect-unmodeled futex -- badop -/
theorem futex_witness_bad_op_is_unmodeled (m : Model) :
    futex_witness futex_addr 192 1 0 (futex_call []) m = Unmodeled := by
  witness_norm

/-- Whatever answer the witness names, the checker accepts with the same
model and events: the witness is admitted (`futex_witness_ok`) and the
checker is complete for the spec (`check_futex_complete_ok`).  Stated so
that the two halves of the arm the registration step builds are known to
agree before it is built.
model: the witness's answers are inside the checker's, by the two lemmas named. -/
theorem futex_witness_is_accepted (uaddr op val utime : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (h : futex_witness uaddr op val utime i m = Ok eff m' evs) :
    check_futex i uaddr op val utime eff m = CheckOk m' evs :=
  check_futex_complete_ok i uaddr op val utime eff m m' evs (h ▸ futex_witness_ok uaddr op val utime i m)

end Witness

-- lean-port sentinel: ticket V-Kernel-Futex-Syscalls appends below this line

section V_Kernel_Futex_Syscalls

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Kernel-Futex-Syscalls — `futex` over the real table

The sections above state every pin on `check_futex` with its four
arguments given explicitly, and the header leaves the register file to
the registration.  This is the registration: `arm_futex`, in
`Checks/Arms/Kernel/Futex/Syscalls.lean`.  What a pin here adds to its
checker-level twin is the ARM's claim: the lookup at 98 finds
`arm_futex` rather than the dispatcher's own decline, and the arm hands
the checker `a0`, `a1`, `a2` and `a3` as `uaddr`, `op`, `val` and
`utime`, each whole, and reads neither `a4` nor `a5`.  That is the order
of the six parameters of `SYSCALL_DEFINE6(futex)`
(kernel/futex/syscalls.c:188-190, Linux v6.18.46), which riscv64's
wrapper fills from `orig_a0` and then `a1` to `a5`
(`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24,
same version).  `check_syscall_futex_call` states that reading for every
six registers; the pins after it name verdicts.

Each register pin puts one value in one of `a0` to `a3` of the wait the
first verdict pin accepts (-EAGAIN with the four-byte read, at `val` 8
against the fixture word 7), and 0 in `a4` and `a5`.  That wait itself
holds 7 in `a4` and `a5`.  Read as `uaddr`, 7 is
misaligned; as `op`, it is no op the model answers; as `val`, it matches
the word; as `utime`, it is a timeout.  None of those four readings
gives the -EAGAIN that pin accepts.

POLARITY follows the header: `kernel:` on a verdict of the table or an
outcome of its witness, `CheckUnmodeled` and `Unmodeled` included;
`probe:` on a `conform` case's acceptance and on the `≠ CheckOk` twin of
a `reject` case; `model:` on the table's own contents. -/

/-- The lookup the dispatcher performs on a `futex_call`, computed once:
`in_sysno` is `98` whatever the registers hold.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_futex_call (args : List word) :
    lookup_ca checked_table (bv_unsigned (futex_call args).in_sysno) = some arm_futex :=
  lookup_ca_checked_table_futex

/-- The table finds `futex` at 98 and hands back the trusted arm.
kernel: include/uapi/asm-generic/unistd.h:__NR_futex@v6.18.46 -/
theorem checked_table_finds_futex : lookup_ca checked_table 98 = some arm_futex :=
  lookup_ca_checked_table_futex

/-- What the table hands the checker on a six-register `futex_call`: the
call itself and its first four registers, in order, each whole.
model: `check_syscall` through `arm_futex`, unfolded; the table's own
contents, not a kernel claim. -/
theorem check_syscall_futex_call (a0 a1 a2 a3 a4 a5 : word) (eff : SyscallEffect)
    (m : Model) :
    check_syscall (futex_call [a0, a1, a2, a3, a4, a5]) eff m
      = check_futex (futex_call [a0, a1, a2, a3, a4, a5]) a0 a1 a2 a3 eff m := by
  exact check_syscall_of_found _ _ _ _ (lookup_futex_call _)

/-! ### The wait the register pins start from -/

/-- The wait through the table: `val` 8 against the word 7 is -EAGAIN
with exactly the four-byte read, accepted, the model unchanged and no
event, with 7 in `a4` and `a5`.  `futex_wait_setup`
(kernel/futex/waitwake.c:591-664, Linux v6.18.46) reads the word at :627
and answers `-EWOULDBLOCK` at :642-645.  The probe's word is 0 and its
`val` 1; the mismatch is what is tested.
probe: testing/syscall-check/tests/futex_private.c#conform -- wait_eagain -/
theorem futex_wait_mismatch_is_eagain_over_the_real_table (m : Model) :
    check_syscall (futex_call [futex_addr, 128, 8, 0, 7, 7])
        (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(futex_addr, 4)]) m
      = CheckOk m [] := by
  rw [check_syscall_futex_call]
  check_norm

/-- The two lies the probe stages on that wait are refused through the
table: 0 with the read kept, the answer of a wait that slept and was
woken, and the -EAGAIN with its read erased.  A mismatch returns at
:642-645 of `futex_wait_setup` and never reaches `futex_queue` at :660,
and the -EAGAIN answers a comparison against a word read from user
memory at :627.
kernel: kernel/futex/waitwake.c:futex_wait_setup; kernel/futex/futex.h:futex_get_value_locked; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem futex_wait_mismatch_rejects_the_lies_over_the_real_table (m : Model) :
    check_syscall (futex_call [futex_addr, 128, 8, 0, 7, 7])
        (SyscallEffect.mkEffectU 0 [] [] [] [] [(futex_addr, 4)]) m = CheckReject
    ∧ check_syscall (futex_call [futex_addr, 128, 8, 0, 7, 7])
        (mkEffect (errno_ret EAGAIN) [] []) m = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rw [check_syscall_futex_call] <;> check_norm

/-- The first lie is the staged `ret=0`.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:ret=0 -- wait_eagain -/
theorem futex_wait_zero_not_accepted_over_the_real_table (m m' : Model) (evs : List event) :
    check_syscall (futex_call [futex_addr, 128, 8, 0, 7, 7])
        (SyscallEffect.mkEffectU 0 [] [] [] [] [(futex_addr, 4)]) m ≠ CheckOk m' evs := by
  rw [(futex_wait_mismatch_rejects_the_lies_over_the_real_table m).1]
  intro h
  cases h

/-- The second lie is the staged `drop-copyins`.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:drop-copyins -- wait_eagain -/
theorem futex_wait_dropped_read_not_accepted_over_the_real_table (m m' : Model)
    (evs : List event) :
    check_syscall (futex_call [futex_addr, 128, 8, 0, 7, 7])
        (mkEffect (errno_ret EAGAIN) [] []) m ≠ CheckOk m' evs := by
  rw [(futex_wait_mismatch_rejects_the_lies_over_the_real_table m).2]
  intro h
  cases h

/-! ### One register at a time -/

/-- `a0` is `uaddr`: `misaligned_addr` in `a0` fails
the alignment test of `get_futex_key` (kernel/futex/core.c:569-570,
Linux v6.18.46) with -EINVAL before any word is read.  The other five
registers hold 128, 8 and three zeros, all multiples of four.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/futex/core.c:get_futex_key; include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
theorem futex_uaddr_is_a0_over_the_real_table (m : Model) :
    check_syscall (futex_call [misaligned_addr, 128, 8, 0, 0, 0])
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := by
  rw [check_syscall_futex_call]
  check_norm

/-- `a1` is `op`, tested whole: 2^32 + 128 in `a1` is declined on every
effect.  Linux's `int op` keeps the low word (`__SC_CAST`,
include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46) and runs the
private wait; the model's test of the whole register fails closed, as
`futex_spec`'s docstring argues.
kernel: include/linux/syscalls.h:__SC_CAST; kernel/futex/syscalls.c:futex,do_futex@v6.18.46 -/
theorem futex_op_is_a1_whole_over_the_real_table (eff : SyscallEffect) (m : Model) :
    check_syscall (futex_call [futex_addr, 4294967424, 8, 0, 0, 0]) eff m
      = CheckUnmodeled := by
  rw [check_syscall_futex_call]
  check_norm

/-- `a2` is `val`: 7 in `a2`, 0 in `a4` and `a5`, matches the word, and
`futex_wait_setup` queues the task (kernel/futex/waitwake.c:660, Linux
v6.18.46) for `__futex_wait` to sleep, which the model declines on every
effect.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/futex/syscalls.c:futex; kernel/futex/waitwake.c:futex_wait_setup@v6.18.46 -/
theorem futex_val_is_a2_over_the_real_table (eff : SyscallEffect) (m : Model) :
    check_syscall (futex_call [futex_addr, 128, 7, 0, 0, 0]) eff m = CheckUnmodeled := by
  rw [check_syscall_futex_call]
  check_norm

/-- `val` is the low word of `a2`: 2^32 + 8 compares as 8 against the
word 7 and is -EAGAIN with the read, accepted; 2^32 + 7 compares as 7,
matches, and is declined on every effect.  `val` is `u32`, narrowed from
the register by `__SC_CAST` (include/linux/syscalls.h:132, Linux
v6.18.46).
kernel: include/linux/syscalls.h:__SC_CAST; kernel/futex/waitwake.c:futex_wait_setup; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem futex_val_is_the_low_word_of_a2_over_the_real_table (eff : SyscallEffect)
    (m : Model) :
    check_syscall (futex_call [futex_addr, 128, 4294967304, 0, 0, 0])
        (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(futex_addr, 4)]) m
      = CheckOk m []
    ∧ check_syscall (futex_call [futex_addr, 128, 4294967303, 0, 0, 0]) eff m
      = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> rw [check_syscall_futex_call] <;> check_norm

/-- `a3` is `utime`: 8192 in `a3`, 0 in `a4` and `a5`, carries a timeout.
The timeout is fetched at kernel/futex/syscalls.c:196-205 (Linux
v6.18.46), before the call into do_futex at :207, and the timer it arms
is not modeled, so the call is declined on every effect.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/futex/syscalls.c:futex,futex_cmd_has_timeout@v6.18.46 -/
theorem futex_utime_is_a3_over_the_real_table (eff : SyscallEffect) (m : Model) :
    check_syscall (futex_call [futex_addr, 128, 8, 8192, 0, 0]) eff m = CheckUnmodeled := by
  rw [check_syscall_futex_call]
  check_norm

/-! ### The private wake -/

/-- The private wake through the table, at the probe's registers over the
fixture word: 0, accepted, for the reason `futex_wake_private_spec`'s
docstring gives from `futex_wake` (kernel/futex/waitwake.c:155-200, Linux
v6.18.46).
probe: testing/syscall-check/tests/futex_private.c#conform -- wake -/
theorem futex_wake_is_zero_over_the_real_table (m : Model) :
    check_syscall (futex_call [futex_addr, 129, 2147483647, 0, 0, 0]) (mkEffect 0 [] []) m
      = CheckOk m [] := by
  rw [check_syscall_futex_call]
  check_norm

/-- With the probe's junk in `a3`, `a4` and `a5` (4660, 2306 and 2306)
the wake is still 0: `futex_cmd_has_timeout`
(kernel/futex/syscalls.c:161-172, Linux v6.18.46) is false for a wake, so
`utime` is never fetched, and the wake reads neither `uaddr2` nor `val3`.
probe: testing/syscall-check/tests/futex_private.c#conform -- wake_junk -/
theorem futex_wake_ignores_a3_to_a5_over_the_real_table (m : Model) :
    check_syscall (futex_call [futex_addr, 129, 2147483647, 4660, 2306, 2306])
        (mkEffect 0 [] []) m = CheckOk m [] := by
  rw [check_syscall_futex_call]
  check_norm

/-- A count of 1 on that wake is refused through the table: the spec
answers 0 only, by the argument its docstring makes.
kernel: kernel/futex/waitwake.c:futex_wake@v6.18.46 -/
theorem futex_wake_rejects_a_count_over_the_real_table (m : Model) :
    check_syscall (futex_call [futex_addr, 129, 2147483647, 0, 0, 0]) (mkEffect 1 [] []) m
      = CheckReject := by
  rw [check_syscall_futex_call]
  check_norm

/-- That count is the staged `ret=1`.
probe: testing/syscall-check/tests/futex_private.c#reject --mutate futex:ret=1 -- wake -/
theorem futex_wake_count_not_accepted_over_the_real_table (m m' : Model) (evs : List event) :
    check_syscall (futex_call [futex_addr, 129, 2147483647, 0, 0, 0]) (mkEffect 1 [] []) m
      ≠ CheckOk m' evs := by
  rw [futex_wake_rejects_a_count_over_the_real_table]
  intro h
  cases h

/-! ### The witness the table hands `receptive`

`syscall_spec_witness` dispatches over the same table, so at 98 it
answers with the arm's `ca_witness`, which is `futex_witness` at the
same four registers. -/

/-- At the wait the register pins start from, the witness names -EAGAIN
with the read: the outcome the checker accepts there.
kernel: kernel/futex/waitwake.c:futex_wait_setup; include/uapi/asm-generic/errno-base.h:EAGAIN@v6.18.46 -/
theorem futex_wait_mismatch_witnesses_eagain_over_the_real_table (m : Model) :
    syscall_spec_witness (futex_call [futex_addr, 128, 8, 0, 7, 7]) m
      = Ok (with_copyins [(futex_addr, FUTEX_WORD_SIZE_nat)] (mkEffect (errno_ret EAGAIN) [] []))
          m [] := by
  rfl

/-- With 8192 in `a3` the witness names the decline, as the checker does.
kernel: kernel/futex/syscalls.c:futex,futex_cmd_has_timeout@v6.18.46 -/
theorem futex_utime_witnesses_unmodeled_over_the_real_table (m : Model) :
    syscall_spec_witness (futex_call [futex_addr, 128, 8, 8192, 0, 0]) m = Unmodeled := by
  rfl

end V_Kernel_Futex_Syscalls

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Futex.Syscalls
