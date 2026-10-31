-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Kernel/Sched/Syscalls.v

import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Sched.Syscalls
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Sched.Syscalls
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress


/-! # Checks.Cases.Checks.Sys.Kernel.Sched.Syscalls — what the three sched checkers and witnesses answer, read off against Linux

Pins over `Checks.Sys.Kernel.Sched.Syscalls`: `check_sched_getaffinity`,
`check_sched_setscheduler`, `check_sched_yield` and the three witnesses.
The checker pins restate the `Example`s of
`theories/LinuxProcessSem/Checks/Cases/Kernel/Sched/Syscalls.v`, at the
commit the header line above names.  The upstream port's baseline was
6e7c0d18ddbaa2d453318f0af4665958350a1871 (the file was byte-identical at
a71fd38a and at f44244ad6b80, the commit that ticket named, and gained
the `sched_yield` examples at that baseline): every `Example` there about a checker's verdict is
stated on `check_syscall`, and each is restated here on `check_<name>` at
the same register values, with the same offered effect and the same
fixture.
Two `sched_yield` Examples are not
restated: `sched_yield_is_modeled`, which is about the table and no
checker, and `sched_yield_ignores_every_argument_word`, whose subject is
the argument registers `check_sched_yield` never sees; both are the
spec-level file's.  The spec-level twins of the same
Rocq examples are `Checks/Cases/Kernel/Sched/Syscalls.lean`'s, which this
file imports for its fixtures and does not restate.  No ledger
reads this file's mapping today: `linux-process-semantics@ff0313ba4f:tools/check_lean_cases_parity.py` pairs
a Cases file with the Rocq file at its mirrored path, none sits at this
one, and the S file's `covers:` lines may name only its own theorems — so
this file is listed `unmirrored`, and the mapping is the theorem's name:
each restated pin keeps its Rocq `Example`'s name verbatim, and nothing
checks that until that tool learns a coverage header for a checker-level
Cases file.  Not part of the trusted specification: this
file is QA on the definitions, written to be READ, and every claim in it
is a claim about what the kernel does, with the citation beside it.  Line
numbers are Linux v6.18.46 (commit 1f99e9ab748f) throughout.

WHY THE CHECKERS AND NOT `check_syscall`.  Rocq's examples go through the
dispatcher, so that a wrong argument order in the arm is caught where the
registers are named.  The Lean tree has no `check_syscall` until the
`Checks/ExecutableSpecs.v` twin lands, and the arm that reads the
registers through `in_arg` is built when these checkers are registered
(BRIEF.md section 5, the VERIFY block: registration first), so the pins
here apply the checkers to the register values directly:
`check_sched_getaffinity` to `len` alone, the one register
`SYSCALL_DEFINE3(sched_getaffinity, pid, len, user_mask_ptr)` decides on
before the model declines, and `check_sched_setscheduler` to the
`SyscallInput` — for the four bytes at `param` — and then `pid`, `policy`,
`param` in `SYSCALL_DEFINE3(sched_setscheduler, pid, policy, param)`'s
order.  The fixture input carries the same three registers, as Rocq's
`mkInput` has it, so that a pin reads as the Rocq example does; the
checker reads only its memory.  What these pins cannot see is a
transposed register in the arm, or that 119, 123 and 124 reach these
three checkers; those facts are the registration's to pin, beside the
arms they are about.  `check_sched_yield` takes no register at all, so
for it the whole of what a pin here can say is the verdict on an offered
effect.

WHAT THIS FILE ADDS to the spec-level twins is the checker's VERDICT on
each example: that the executable acceptor answers `CheckOk` where the
spec admits, `CheckUnmodeled` where it declines, and `CheckReject` on the
lies — which the soundness and completeness lemmas promise for every
input, and a closed run shows on these — and, for the witnesses, WHICH
admissible outcome progress is proved from: `*_witness_ok` says the spec
admits it, for every input, and says nothing about which branch was taken
on any, so each witness pin runs the witness on one fixture and names the
outcome.  The Rocq tree has no check file for the witnesses — their
`*_witness_ok` lemmas are stated in the file itself — so the witness pins
mirror nothing: they are the Lean tree's tests for what the twin ports,
placed where every pin in this tree lives so that `linux-process-semantics@ff0313ba4f:tools/check_lean_pins.py`
reads them.  The kernel readings are the spec-level file's; each
docstring below keeps the function of Linux its Rocq original cites, with
the line numbers read at v6.18.46 beside it, so that a pin is judged
against the function it names.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE. -/

/- The `kernel:` tag grammar requires bare symbols.
Its resolver includes the syscall definition under `sched_setscheduler`.
The adjacent prose identifies that entry point with `SYSCALL_DEFINE3(sched_setscheduler)` and its line numbers. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Sched.Syscalls

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Sched.Syscalls
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Sched.Syscalls

section GetAffinity

/-! ## sched_getaffinity (123)

Every example here is a `CheckReject` that needs a kernel answering
something no kernel answers, or a `CheckUnmodeled` on a length Linux
ANSWERS, which is a claim about the model alone.  The wrapping lengths
themselves are issuable — `SYSCALL_DEFINE3(sched_getaffinity)` computes
`(len * BITS_PER_BYTE) < nr_cpu_ids` on an `unsigned int len` and touches
neither the pid nor the pointer before either gate
(kernel/sched/syscalls.c:1335-1338, Linux v6.18.46) — and
`testing/syscall-check/tests/sched_getaffinity_len.c`'s `einval` run
asserts 0, 2^29, 2^31 and 7 * 2^29
alongside the unaligned lengths, with `reject` lines refusing a byte
count, -EFAULT and -ESRCH for every call in the run.  The rest of the
wrapping set and the compat-aligned lengths are walked here rather than
one probe call each.

ONE LIE NO PIN HERE REFUSES: a gate -EINVAL branch that also accepted
-EPERM.  The call's only -EPERM is whatever `security_task_getscheduler`
returns inside `sched_getaffinity()` (kernel/sched/syscalls.c:1310-1312,
Linux v6.18.46), behind both gates, and that is a security module's value:
no function on the path spells the errno, so `linux-process-semantics@ff0313ba4f:tools/check_lean_pin_evidence.py`'s
KMENTION rule — the cited function must spell the errno the pin judges —
would refuse the pin's evidence line, and the bound is named here instead
of pinned. -/

/-- THE WRAPPING LENGTHS.  `len` is an `unsigned int` and `BITS_PER_BYTE`
is a plain `8`, so `len * BITS_PER_BYTE` is computed in 32 bits.  The
product is zero exactly on the multiples of 2^29, and `nr_cpu_ids` is at
least 1, so every one of them is -EINVAL at
kernel/sched/syscalls.c:1335-1336 — the large ones included, which read
as obviously-big-enough to a model that did the multiplication over the
integers.  Rocq's example passes garbage for the pid and the mask pointer,
and the checker here takes neither: both gates run before either is
looked at.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_wrapping_lengths_are_einval :
    check_sched_getaffinity 0
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_getaffinity 536870912
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_getaffinity 1073741824
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_getaffinity 1610612736
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_getaffinity 2147483648
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_getaffinity 2684354560
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_getaffinity 3221225472
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_getaffinity 3758096384
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- THE LENGTHS CONGRUENT TO 4 MOD 8 are what tell the native gate's `& 7`
(`sizeof(unsigned long)-1`, kernel/sched/syscalls.c:1337) from the compat
gate's `& 3` (`sizeof(compat_ulong_t)-1`, kernel/compat.c:144-153), and
they are the sharpest available mistake: a checker written from
`COMPAT_SYSCALL_DEFINE3(sched_getaffinity)` instead of the native
definition would decline these and still accept -EINVAL for every other
length in this file.  They are -EINVAL for an LP64 caller, which is the
only kind this model loads.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_compat_aligned_lengths_are_einval :
    check_sched_getaffinity 4
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_getaffinity 12
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_getaffinity 4294967292
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model [] :=
  ⟨rfl, rfl, rfl⟩

/-- THE BOUNDARY IS EXACTLY WHERE THE WRAP PUTS IT.  The two neighbours of
2^29 are eight-aligned like it, differ from it by one machine word, and
are NOT refused by the size gate: 2^29 - 8 has 2^32 - 64 bits, above every
`NR_CPUS`, and 2^29 + 8 has 64 bits, below `nr_cpu_ids` only on a machine
with more than 64 CPUs.  Past both gates the answer is the success path's
`min(len, cpumask_size())` byte count (kernel/sched/syscalls.c:1345-1350)
or the -EFAULT of its `copy_to_user` at :1347; the model carries neither
`cpumask_size()` nor the task's mask and the checker declines every length
both gates let through, whatever effect it is offered — the -EINVAL here
included.  2^29 itself, between them, is still accepted: pinning it here
is what makes this pin fail when the boundary moves rather than merely say
where it is.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_wrap_neighbours_are_unmodeled :
    check_sched_getaffinity 536870904
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckUnmodeled
    ∧ check_sched_getaffinity 536870920
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckUnmodeled
    ∧ check_sched_getaffinity 536870912
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model [] :=
  ⟨rfl, rfl, rfl⟩

/-- THE NEGATIVE DIRECTION, on the wrapping length the probe's `einval` run
issues.  A kernel that answered it with a plausible byte count, with the
-EFAULT its untouched pointer cannot produce (the copy out is
`sched_getaffinity`'s, kernel/sched/syscalls.c:1347, behind both gates), or with the -ESRCH its
unreached task lookup cannot produce (:1305-1308, inside the helper called
at :1343), is REJECTED.  So is one that answered -EINVAL and wrote to the
mask anyway: nothing is stored before either gate.  Rocq spells the -ESRCH
as the number 3, having no constant for it; `State` here has `ESRCH`.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_wrapping_length_lies_rejected :
    check_sched_getaffinity 536870912
        (mkEffect 8 [] []) demo_model = CheckReject
    ∧ check_sched_getaffinity 536870912
        (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject
    ∧ check_sched_getaffinity 536870912
        (mkEffect (errno_ret ESRCH) [] []) demo_model = CheckReject
    ∧ check_sched_getaffinity 536870912
        (mkEffect (errno_ret EINVAL) [(3735928559, [Z_to_bv 8 0])] []) demo_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- THE LIES THE ROCQ EXAMPLE LEAVES OPEN, on the same wrapping length and
on the unaligned one.  `SYSCALL_DEFINE3(sched_getaffinity)` copies nothing
IN — `user_mask_ptr` is only ever written, at kernel/sched/syscalls.c:1347
(Linux v6.18.46) — so a -EINVAL carrying a copy-in on its ledger is a
lie; it never returns 0 — the success path returns `min(len,
cpumask_size())` (:1345-1350), at least one machine word — so a 0 is a
lie; and the -ENOMEM of `zalloc_cpumask_var` (:1340-1341) sits behind
both gates, so on a length either gate refuses it is a lie too.  The
last two conjuncts say the same of the unaligned length 4, which the
second gate (:1337-1338) refuses: without them a checker whose second
gate reached its -EINVAL through a branch that also cleared the ledger
would pass the pin above, whose length is the first gate's.  A checker
that accepted any one of these agreed with every Rocq example.
This pin has no Rocq original: no `Example` in the Rocq Cases file states it.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_gate_lies_rejected :
    check_sched_getaffinity 536870912
        (with_copyins [(3735928559, 8)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
        = CheckReject
    ∧ check_sched_getaffinity 536870912
        (mkEffect (Z_to_bv 64 0) [] []) demo_model = CheckReject
    ∧ check_sched_getaffinity 536870912
        (mkEffect (errno_ret ENOMEM) [] []) demo_model = CheckReject
    ∧ check_sched_getaffinity 4
        (with_copyins [(3735928559, 8)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
        = CheckReject
    ∧ check_sched_getaffinity 4
        (mkEffect (Z_to_bv 64 0) [] []) demo_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- THE LENGTH IS READ AT 32 BITS: `len` is the `unsigned int` of
`SYSCALL_DEFINE3(sched_getaffinity)` (kernel/sched/syscalls.c:1329-1330,
Linux v6.18.46), so 2^32 + 8 arrives as 8 and, on any machine with at
most 64 CPUs, passes both gates (:1335-1338) into the cpumask answer the
model does not carry — on a larger one the first gate refuses it, and the
model, carrying no `nr_cpu_ids`, declines either way — and 2^32 + 4
arrives as 4 and is the alignment -EINVAL (:1337-1338).  A
checker refusing a length for not fitting 32 bits fails the first; the
probe `sched_getaffinity_len.c` asserts the second on Linux.  (The two
gates depend only on `len mod 2^29` and `len mod 8`, so a checker that
merely skips the 32-bit cut answers the same on every length and no pin
can tell it apart; it is not a mutant.)
This pin has no Rocq original: no `Example` in the Rocq Cases file states it.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_length_is_32_bit :
    check_sched_getaffinity 4294967304
        (mkEffect 8 [] []) demo_model = CheckUnmodeled
    ∧ check_sched_getaffinity 4294967300
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model [] :=
  ⟨rfl, rfl⟩

/-- THE ODD LENGTHS, and the odd length that is the largest `unsigned int`.
`len & (sizeof(unsigned long)-1)` (kernel/sched/syscalls.c:1337-1338,
Linux v6.18.46) refuses every length with any of its three low bits set:
1, 7 and 9 alike, and 2^32 - 1, which arrives whole through the `unsigned
int` cut with all three set.  Every unaligned length pinned above is a
multiple of 4, so a mask written as `& 4` — testing the one bit the
compat-aligned pin exercises — refuses 4 and 12 and every length in the
wrapping pins, and lets these through to the decline; this pin is what
fails on it.  qemu-user's `TARGET_NR_sched_getaffinity`
(linux-user/syscall.c:11979-12018, QEMU v11.1.1, the range
`linux-process-semantics@ff0313ba4f:bugs/sched-setscheduler-pre-copy-einval-is-linux-order.md` records)
refuses `arg2 & (sizeof(abi_ulong) - 1)` with
-TARGET_EINVAL before it rounds the length up, so the -EINVAL here is the
intersection's, not one implementation's.
This pin has no Rocq original: no `Example` in the Rocq Cases file states it.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_odd_lengths_are_einval :
    check_sched_getaffinity 1
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_getaffinity 7
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_getaffinity 9
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_getaffinity 4294967295
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

end GetAffinity

section SetScheduler

/-- Compute closed gates with `sys_norm` before `rfl` compares the remaining constructors.
The two pre-copy branches test `decide (sint32 policy < 0)` and `decide (sint32 pid < 0)`.
Reducing their `Int.decLt` instances can expand `Nat.sub` before evaluating the bit-vector reading.
`sys_norm` evaluates these readings first.
The type `check_result` has no `DecidableEq`, so `decide` cannot prove the whole verdict directly. -/
local macro "sched_check_run" : tactic =>
  `(tactic| (unfold check_sched_setscheduler; sys_norm <;> rfl))

/-- THE PRIORITY IS A `__u32` AT THE RANGE GATE, and this is the pair that
says so.  `struct sched_param` holds an `int`, and `_sched_setscheduler`
copies it into `struct sched_attr`'s `__u32 sched_priority`
(kernel/sched/syscalls.c:771), so -1 meets `attr->sched_priority >
MAX_RT_PRIO-1` (:567-568) as 4294967295 and is refused THERE — by the same
gate that refuses 100, and before the `rt_policy(policy) !=
(sched_priority != 0)` comparison (:570) ever runs.  Both answers are
-EINVAL, so no probe can separate them; what CAN be separated is 99, which
the range gate admits, from -1, which it does not.  A checker that read the
field signed would put -1 on the far side of the range gate and reach the
same -EINVAL through the RT-agreement test for SCHED_IDLE — and would then
treat SCHED_FIFO at priority -1 as it treats 99, an RT request the model
declines, where Linux answers -EINVAL from the range gate; the first
conjunct is a `CheckOk` such a checker cannot produce.
kernel: kernel/sched/syscalls.c:__sched_setscheduler,_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_negative_priority_is_out_of_range :
    -- -1 as a signed int, 4294967295 as the u32 the gate compares
    check_sched_setscheduler
        (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 4294967295))
        0 1 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckOk demo_model []
    -- ...and 99 is admitted by that gate, so SCHED_FIFO at 99 is not an -EINVAL at all: it is
    -- the RT request the model declines
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 99))
        0 1 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckUnmodeled
    -- ...while 100 is refused, one past MAX_RT_PRIO-1
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 100))
        0 1 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckOk demo_model [] :=
  by
  refine ⟨?_, ?_, ?_⟩ <;> sched_check_run

/-- THE ORDER OF THE TWO PRE-COPY -EINVALS, on a call that is wrong in
three ways at once.  `policy < 0` is decided in
`SYSCALL_DEFINE3(sched_setscheduler)` itself (kernel/sched/syscalls.c:962-968,
Linux v6.18.46), before `do_sched_setscheduler` is entered, so a negative
policy beats the NULL `param` and the negative pid that function refuses
at :880-888 — and beats the -EFAULT an unreadable `param` would raise,
which is the discrimination the unreadable pointer of the second conjunct
makes.  A checker that tested the pointer first would accept -EFAULT
there.
…and the truncation is real: `int policy` reads 2^32 + 5 as SCHED_IDLE at
:962, so the same register with its low half changed is answered with the
0 `__sched_setscheduler` gives a priority-0 SCHED_IDLE request (:555-571,
:757) rather than refused.
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_negative_policy_wins :
    check_sched_setscheduler
        (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)) 0 (fun _ => none))
        (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)) 0
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 63)) (fun _ => none))
        0 (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 63))
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 32 + 5)) sched_param_ptr (sched_param_mem 0))
        0 (Z_to_bv 64 (2 ^ 32 + 5)) sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckOk demo_model [] :=
  by
  refine ⟨?_, ?_, ?_⟩ <;> sched_check_run

/-- `TASK_SIZE - k` as a word.  `__access_ok`
(include/asm-generic/access_ok.h:31-40, Linux v6.18.46) tests, at line
40, against `TASK_SIZE_MAX`, which line 16 of the same header resolves to
`TASK_SIZE` on an arch that does not define it, and riscv does not:
arch/riscv/include/asm/uaccess.h:57 includes the generic header and
nothing under `arch/riscv/include` defines the name.  So the constant the
fault pins below name reaches the cited function through a header, and
the alias keeps `linux-process-semantics@ff0313ba4f:tools/check_lean_pin_evidence.py`'s constant search off
it, as `Checks/Cases/Kernel/Time/Time.lean` does for the same test.  This
stops being right the day riscv defines `TASK_SIZE_MAX` to anything but
`TASK_SIZE`: the fault line moves, and every `task_size_minus` pin is a
claim about the wrong constant. -/
def task_size_minus (k : Int) : word := Z_to_bv 64 (TASK_SIZE - k)

/-- -EFAULT IS THE RANGE VERDICT AND NOTHING ELSE, and it records no
copy-in.  The copy of `do_sched_setscheduler`
(kernel/sched/syscalls.c:887-888) is `access_ok` and then the copy: `__access_ok`
(include/asm-generic/access_ok.h) refuses four bytes whose last one is at
`TASK_SIZE`, and refuses them before a load, so the answer carries an
empty ledger and one that carries a ledger is a lie; a range `access_ok`
ADMITS that memory does not back is declined instead, because Linux
answers -EFAULT there too and the ledger cannot say which bytes it read
first.  The two addresses below are one byte apart and land on opposite
sides of that line.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem sched_setscheduler_fault_is_the_range_verdict :
    check_sched_setscheduler
        (sched_setscheduler_in 0 5 (task_size_minus 3) (fun _ => none))
        0 5 (task_size_minus 3)
        (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckOk demo_model []
    -- the last four bytes wholly under TASK_SIZE: the range passes, and the model declines
    -- rather than reporting the fault
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 (task_size_minus 4) (fun _ => none))
        0 5 (task_size_minus 4)
        (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled
    -- ...and the -EFAULT it does accept carries no ledger
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 (task_size_minus 3) (fun _ => none))
        0 5 (task_size_minus 3)
        (with_copyins [(task_size_minus 3, 4)] (mkEffect (errno_ret EFAULT) [] []))
        demo_model = CheckReject :=
  by
  unfold task_size_minus
  refine ⟨?_, ?_, ?_⟩ <;> sched_check_run

/-- THE FAULT'S OWN LIES.  Four bytes whose last one is at `TASK_SIZE` are
refused by `access_ok` inside the `copy_from_user` of
`do_sched_setscheduler` (kernel/sched/syscalls.c:887-888, Linux v6.18.46;
`__access_ok`, include/asm-generic/access_ok.h:31-40), and that refusal
is -EFAULT and nothing else: not the -EINVAL of the gate before it
(:885-886), which a NULL or negative argument earns and an unreadable one
does not; not the -ESRCH of the lookup after it (:890-892), which is
never reached; and not a 0, which needs the copy to have succeeded.  The
Rocq example fixes the -EFAULT and its empty ledger; these are the
answers the same checker refuses on the same call, without which a fault
branch that ALSO accepted an -EINVAL or an -ESRCH passed every pin in
this file.
This pin has no Rocq original: no `Example` in the Rocq Cases file states it.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem sched_setscheduler_fault_lies_rejected :
    check_sched_setscheduler
        (sched_setscheduler_in 0 5 (task_size_minus 3) (fun _ => none))
        0 5 (task_size_minus 3)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 (task_size_minus 3) (fun _ => none))
        0 5 (task_size_minus 3)
        (mkEffect (errno_ret ESRCH) [] []) demo_model = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 (task_size_minus 3) (fun _ => none))
        0 5 (task_size_minus 3)
        (mkEffect (Z_to_bv 64 0) [] []) demo_model = CheckReject :=
  by
  unfold task_size_minus
  refine ⟨?_, ?_, ?_⟩ <;> sched_check_run

/-- THE COPY RUNS BEFORE THE TASK LOOKUP, on a call that is wrong in both
ways: a `param` past `TASK_SIZE` and a pid that is not the pinned tid.
`do_sched_setscheduler` copies first (kernel/sched/syscalls.c:887-888,
Linux v6.18.46) and looks the task up second (`CLASS(find_get_task, p)`,
:890), so the answer is the copy's -EFAULT with nothing on the ledger,
and the -ESRCH the unresolved pid would earn at :891-892 is a lie.  A
checker that tested the pid before the read would DECLINE this call — the
model cannot resolve 4097 — and so accept nothing here; the first
conjunct is a `CheckOk` such a checker cannot produce.  The order is the
order `sched_setscheduler_pid_is_the_pinned_tid` below relies on, said
of the branch before the read rather than the one after it.
This pin has no Rocq original: no `Example` in the Rocq Cases file states it.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_fault_precedes_the_task_lookup :
    check_sched_setscheduler
        (sched_setscheduler_in 4097 5 (Z_to_bv 64 (2 ^ 63)) (fun _ => none))
        4097 5 (Z_to_bv 64 (2 ^ 63))
        (mkEffect (errno_ret EFAULT) [] []) sched_tid_model = CheckOk sched_tid_model []
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 4097 5 (Z_to_bv 64 (2 ^ 63)) (fun _ => none))
        4097 5 (Z_to_bv 64 (2 ^ 63))
        (mkEffect (errno_ret ESRCH) [] []) sched_tid_model = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 4097 5 (Z_to_bv 64 (2 ^ 63)) (fun _ => none))
        4097 5 (Z_to_bv 64 (2 ^ 63))
        (with_copyins [(Z_to_bv 64 (2 ^ 63), 4)] (mkEffect (errno_ret EFAULT) [] []))
        sched_tid_model = CheckReject :=
  by
  refine ⟨?_, ?_, ?_⟩ <;> sched_check_run

/-- THE DECLINES, each on the exact argument that makes it one.  Every
call here is one Linux ANSWERS — SCHED_FIFO at priority 1 and SCHED_NORMAL
at 0 are ordinary requests, and SCHED_IDLE with SCHED_RESET_ON_FORK is a
0 — so each is a claim about the model alone: `RLIMIT_RTPRIO` and
`CAP_SYS_NICE` decide the first (`user_check_sched_setscheduler`,
kernel/sched/syscalls.c:483-493 and :524-526); whether the task is ALREADY SCHED_IDLE
decides the next two (:509-512); `CONFIG_SCHED_CLASS_EXT` decides whether
7 is a policy at all (`normal_policy`, kernel/sched/sched.h:192-198); the
reset-on-fork bit `_sched_setscheduler` strips (:779-783) is a state
change nothing records; and a positive pid with no tid pinned is a task
the model cannot say is this one.  The 0 each really returns on a
permitted machine is what is offered, and declined.
kernel: kernel/sched/syscalls.c:user_check_sched_setscheduler,_sched_setscheduler; kernel/sched/sched.h:normal_policy@v6.18.46 -/
theorem sched_setscheduler_declines :
    -- RLIMIT_RTPRIO and CAP_SYS_NICE decide this one
    check_sched_setscheduler
        (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 1))
        0 1 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled
    -- whether the task is ALREADY SCHED_IDLE decides this one
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 0 sched_param_ptr (sched_param_mem 0))
        0 0 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled
    -- ...and this one, for the same reason
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 3 sched_param_ptr (sched_param_mem 0))
        0 3 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled
    -- CONFIG_SCHED_CLASS_EXT decides whether 7 is a policy at all
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 7 sched_param_ptr (sched_param_mem 0))
        0 7 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled
    -- the SCHED_RESET_ON_FORK bit is a state change nothing records
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 (Z_to_bv 64 (5 + 2 ^ 30)) sched_param_ptr (sched_param_mem 0))
        0 (Z_to_bv 64 (5 + 2 ^ 30)) sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled
    -- a positive pid, with no tid pinned: the model cannot say whether the number names
    -- this task
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 4096 5 sched_param_ptr (sched_param_mem 0))
        4096 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled :=
  by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sched_check_run

/-- THE ONE ANSWER PAST THE TASK LOOKUP, and the lies a kernel would have
to tell to make it something else.  SCHED_IDLE at priority 0 on the
calling task passes every gate of `__sched_setscheduler`
(kernel/sched/syscalls.c:555-571) and returns 0, with the four bytes it
read recorded.  -EPERM is the sharpest of the lies: it is what the call
really returns when the caller lacks `CAP_SYS_NICE` AND
`user_check_sched_setscheduler` has sent it to `req_priv` (:524-526) —
for a task whose `sched_reset_on_fork` is set and not kept (:519-520),
another user's task (:515-516), or a SCHED_IDLE task leaving the policy
without the nice headroom (:509-511), none of which the spec's envelope
admits — so a checker that had made the SCHED_IDLE answer depend on a
credential the model does not carry would ACCEPT it here and agree with
this file everywhere else.  -EINVAL is refused (priority 0 is the one
SCHED_IDLE accepts), a write-back is refused (the call has no output
parameter at all), and a success without its ledger is refused (the copy
of `do_sched_setscheduler` at :887 ran).
kernel: kernel/sched/syscalls.c:__sched_setscheduler,user_check_sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_idle_is_zero :
    check_sched_setscheduler
        (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        0 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        0 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EPERM) [] [])) demo_model
      = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        0 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckReject
    -- nor does the success write anything back: the call has no output parameter at all
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        0 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)]
          (mkEffect (Z_to_bv 64 0) [(sched_param_ptr, [Z_to_bv 8 0])] [])) demo_model
      = CheckReject
    -- ...and it does record the four bytes it read
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        0 5 sched_param_ptr
        (mkEffect (Z_to_bv 64 0) [] []) demo_model = CheckReject :=
  by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> sched_check_run

/-- THE LEDGER IS EXACTLY THE FOUR BYTES AT `param`, not any non-empty
record of a read.  `do_sched_setscheduler` copies `sizeof(struct
sched_param)` — four bytes, one `int` (include/linux/sched.h:410-412) —
from `param` and nothing else (kernel/sched/syscalls.c:887-888, Linux
v6.18.46), so a success recording eight bytes, three, four at the
neighbouring address, or the same four twice is a lie:
`check_ret_only_copyins` compares the ledger to `[(param, 4)]` as a list,
and this is the pin that fails when that is loosened to "some copy-in
happened".  The idle pin above refuses the EMPTY ledger; these are the
wrong non-empty ones.
This pin has no Rocq original: no `Example` in the Rocq Cases file states it.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_success_ledger_is_exactly_the_four_bytes :
    check_sched_setscheduler
        (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        0 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 8)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        0 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 3)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        0 5 sched_param_ptr
        (with_copyins [(Z_to_bv 64 4100, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        0 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4), (sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] []))
        demo_model = CheckReject :=
  by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sched_check_run

/-- THE -EINVALS PAST THE COPY CARRY THE LEDGER, and each is the one answer
on its route.  Once `do_sched_setscheduler` has copied the four bytes
(kernel/sched/syscalls.c:887-888, Linux v6.18.46) and resolved the caller,
`__sched_setscheduler` refuses -EINVAL: a policy `valid_policy` does not
name (4, the gap between SCHED_BATCH and SCHED_IDLE that no `SCHED_*`
fills, include/uapi/linux/sched.h:114-121; :555-556), SCHED_DEADLINE
asked for through `struct sched_param` — `_sched_setscheduler` (:769-773)
builds the `sched_attr` with no deadline, and `__checkparam_dl`
(kernel/sched/deadline.c:3533) refuses a zero `sched_deadline` at
:3542-3543, through :569-571 — SCHED_FIFO at priority 0 and SCHED_IDLE at
priority 1 (the RT-agreement half of :569-571), each with the copy
already on the ledger.  The lies: the same -EINVAL without its ledger; a
0 or an -EPERM for SCHED_DEADLINE, which is refused before
`user_check_sched_setscheduler` (:573-576) can ask about a credential;
and a 0 for SCHED_FIFO at 4294967295, the -1 the range gate refuses
(:567-568).
This pin has no Rocq original: no `Example` in the Rocq Cases file states it.
kernel: kernel/sched/syscalls.c:__sched_setscheduler,_sched_setscheduler,do_sched_setscheduler; kernel/sched/deadline.c:__checkparam_dl@v6.18.46 -/
theorem sched_setscheduler_post_copy_einvals_carry_the_ledger :
    -- 4 is no policy
    check_sched_setscheduler
        (sched_setscheduler_in 0 4 sched_param_ptr (sched_param_mem 0))
        0 4 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckOk demo_model []
    -- SCHED_DEADLINE has no parameters on this route
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 6 sched_param_ptr (sched_param_mem 0))
        0 6 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckOk demo_model []
    -- SCHED_FIFO at 0, and SCHED_IDLE at 1: the RT-agreement test
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 0))
        0 1 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 1))
        0 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckOk demo_model []
    -- the lies: no ledger, a 0, an -EPERM, and a 0 past the range gate
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 4 sched_param_ptr (sched_param_mem 0))
        0 4 sched_param_ptr
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 6 sched_param_ptr (sched_param_mem 0))
        0 6 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 6 sched_param_ptr (sched_param_mem 0))
        0 6 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EPERM) [] [])) demo_model
      = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 4294967295))
        0 1 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckReject :=
  by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sched_check_run

/-- THE PID THE PINNED TID NAMES, against one it does not, on the SAME
model.  `find_process_by_pid` (kernel/sched/syscalls.c:253-256) is
`pid ? find_task_by_vpid(pid) : current`, and `do_sched_setscheduler`
takes a `pid_t`, which is an `int`: so the pinned tid names the caller,
the same register with its high half set names the caller too, the
neighbouring pid is a different task and declined, and pid 0 is `current`
whatever the tid is.  This is the shape musl's `pthread_setschedparam`
issues — it passes `t->tid`, never 0 — so the pair matters: an arm that
answered only pid 0 leaves every real caller outside the modeled surface,
and one that answered any positive pid would claim to know about a task it
has no representation of.
kernel: kernel/sched/syscalls.c:find_process_by_pid,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_pid_is_the_pinned_tid :
    check_sched_setscheduler
        (sched_setscheduler_in 4096 5 sched_param_ptr (sched_param_mem 0))
        4096 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) sched_tid_model
      = CheckOk sched_tid_model []
    -- the same register with its high half set: pid_t is an int, so this IS the pinned tid
    ∧ check_sched_setscheduler
        (sched_setscheduler_in (Z_to_bv 64 (2 ^ 32 + 4096)) 5 sched_param_ptr (sched_param_mem 0))
        (Z_to_bv 64 (2 ^ 32 + 4096)) 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) sched_tid_model
      = CheckOk sched_tid_model []
    -- the neighbouring pid is a different task, and declined
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 4097 5 sched_param_ptr (sched_param_mem 0))
        4097 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) sched_tid_model
      = CheckUnmodeled
    -- ...and pid 0 is current whatever the tid is
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        0 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) sched_tid_model
      = CheckOk sched_tid_model [] :=
  by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sched_check_run

/-- PID 2^32 IS PID 0.  `pid` is the `pid_t` of
`SYSCALL_DEFINE3(sched_setscheduler)`, an `int` cut by `__SC_CAST`
(include/linux/syscalls.h:132, Linux v6.18.46), so 2^32 arrives as 0 and
`find_process_by_pid` (kernel/sched/syscalls.c:253-256) returns
`current` — on a model with NO tid pinned, which is what separates this
from the pinned-tid pin above: there the high half rode on a pid the
model resolves by its tid, here the cut alone makes the call answerable.
A checker that tested the pid against 0 at 64 bits declines this call.
This pin has no Rocq original: no `Example` in the Rocq Cases file states it.
kernel: kernel/sched/syscalls.c:find_process_by_pid,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_pid_is_cut_to_32_bits_before_the_zero_test :
    check_sched_setscheduler
        (sched_setscheduler_in (Z_to_bv 64 (2 ^ 32)) 5 sched_param_ptr (sched_param_mem 0))
        (Z_to_bv 64 (2 ^ 32)) 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckOk demo_model [] :=
  by sched_check_run

/-- THE TASK LOOKUP COMES BEFORE THE POLICY CHECK.  Policy 4 is no policy
(`valid_policy`, kernel/sched/sched.h:216-220), and `__sched_setscheduler`
refuses it -EINVAL at kernel/sched/syscalls.c:555-556 — but only once
`do_sched_setscheduler` has resolved the pid (:890-892), which for a pid
that is not the pinned tid the model cannot do.  So the answer here is a
decline and not the -EINVAL: a checker that ran
`sched_setscheduler_answer` before the self test would accept the -EINVAL
on a task it knows nothing about, and would pass every pin above, whose
declined pids all carry an ANSWERED (policy, priority).  The -ESRCH a
kernel might give for the same pid is declined too, not refused: 4097 may
well be a real task.
This pin has no Rocq original: no `Example` in the Rocq Cases file states it.
kernel: kernel/sched/syscalls.c:__sched_setscheduler,do_sched_setscheduler; kernel/sched/sched.h:valid_policy@v6.18.46 -/
theorem sched_setscheduler_task_lookup_precedes_the_policy_check :
    check_sched_setscheduler
        (sched_setscheduler_in 4097 4 sched_param_ptr (sched_param_mem 0))
        4097 4 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) sched_tid_model
      = CheckUnmodeled
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 4097 4 sched_param_ptr (sched_param_mem 0))
        4097 4 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret ESRCH) [] [])) sched_tid_model
      = CheckUnmodeled :=
  by
  refine ⟨?_, ?_⟩ <;> sched_check_run

/-- THE PRE-COPY GATE IS -EINVAL AND NOTHING ELSE.  `do_sched_setscheduler`
tests `!param || pid < 0` (kernel/sched/syscalls.c:885-886, Linux v6.18.46)
before the `copy_from_user` at :887-888, so the NULL `param` and the pid
-1 are both the bare -EINVAL: the -EFAULT a checker reading the pointer
first would accept is refused, a ledger on an answer whose copy never ran
is refused, and the register 2^31 — the smallest `int` in its low half —
takes the same route.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_pre_copy_gate_is_einval :
    check_sched_setscheduler
        (sched_setscheduler_in 0 5 0 (fun _ => none))
        0 5 0
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 0 (fun _ => none))
        0 5 0
        (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) 5 sched_param_ptr (sched_param_mem 0))
        (Z_to_bv 64 (2 ^ 64 - 1)) 5 sched_param_ptr
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_setscheduler
        (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) 5 sched_param_ptr (sched_param_mem 0))
        (Z_to_bv 64 (2 ^ 64 - 1)) 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) 5 sched_param_ptr (sched_param_mem 0))
        (Z_to_bv 64 (2 ^ 64 - 1)) 5 sched_param_ptr
        (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in (Z_to_bv 64 (2 ^ 31)) 5 sched_param_ptr (sched_param_mem 0))
        (Z_to_bv 64 (2 ^ 31)) 5 sched_param_ptr
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model [] :=
  by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sched_check_run

/-- THE PRE-COPY -EINVALS CARRY NO LEDGER AND NO WRITE.  Both of them are
decided before the `copy_from_user` of `do_sched_setscheduler`
(kernel/sched/syscalls.c:887-888, Linux v6.18.46): the negative policy in
`SYSCALL_DEFINE3(sched_setscheduler)` at :962-968, the NULL `param` and
the negative pid at :885-886.  So an -EINVAL claiming the four bytes at
`param`, or claiming a write, is refused on every one of those routes —
including the ones whose `param` is a readable `struct sched_param` the
copy would have succeeded on.
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_pre_copy_einvals_carry_no_ledger :
    -- the negative policy, beside a readable param
    check_sched_setscheduler
        (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 64 - 1)) sched_param_ptr (sched_param_mem 0))
        0 (Z_to_bv 64 (2 ^ 64 - 1)) sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 64 - 1)) sched_param_ptr (sched_param_mem 0))
        0 (Z_to_bv 64 (2 ^ 64 - 1)) sched_param_ptr
        (mkEffect (errno_ret EINVAL) [(sched_param_ptr, [Z_to_bv 8 0])] []) demo_model
      = CheckReject
    -- the NULL param
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 0 (fun _ => none))
        0 5 0
        (with_copyins [(0, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model = CheckReject
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 0 (fun _ => none))
        0 5 0
        (mkEffect (errno_ret EINVAL) [(sched_param_ptr, [Z_to_bv 8 0])] []) demo_model
      = CheckReject
    -- the negative pid, beside the same readable parameter
    ∧ check_sched_setscheduler
        (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) 5 sched_param_ptr (sched_param_mem 0))
        (Z_to_bv 64 (2 ^ 64 - 1)) 5 sched_param_ptr
        (mkEffect (errno_ret EINVAL) [(sched_param_ptr, [Z_to_bv 8 0])] []) demo_model
      = CheckReject :=
  by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> sched_check_run

/-- THE POLICY'S SIGN IS READ AT 32 BITS.  `SYSCALL_DEFINE3(sched_setscheduler)`
takes an `int policy` (kernel/sched/syscalls.c:962) and refuses `policy < 0`
at :964-965 (Linux v6.18.46), so the register 2^31 is negative there and
is -EINVAL before `do_sched_setscheduler` reads the pointer at :885-888 —
which is why the -EFAULT its unreadable `param` would otherwise draw is
refused.
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_policy_sign_is_32_bit :
    check_sched_setscheduler
        (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 31)) (Z_to_bv 64 (2 ^ 63)) (fun _ => none))
        0 (Z_to_bv 64 (2 ^ 31)) (Z_to_bv 64 (2 ^ 63))
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 31)) (Z_to_bv 64 (2 ^ 63)) (fun _ => none))
        0 (Z_to_bv 64 (2 ^ 31)) (Z_to_bv 64 (2 ^ 63))
        (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject :=
  by
  refine ⟨?_, ?_⟩ <;> sched_check_run

/-- THE NULL TEST IS ON THE WHOLE POINTER: 2^32 has a zero low word and is
not NULL, so `!param` (kernel/sched/syscalls.c:885) is false, `__access_ok`
admits the range, and Linux answers from the copy at :887-888 — -EFAULT
on a process with nothing mapped there.  The model has no byte at 2^32
and the range is in bounds, so it declines rather than name the fault;
what the pin fixes is that the decline is not the -EINVAL a checker
testing the pointer at 32 bits would accept.
This pin has no Rocq original: no `Example` in the Rocq Cases file states it.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_null_test_is_64_bit :
    check_sched_setscheduler
        (sched_setscheduler_in 0 5 (Z_to_bv 64 (2 ^ 32)) (fun _ => none))
        0 5 (Z_to_bv 64 (2 ^ 32))
        (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 (Z_to_bv 64 (2 ^ 32)) (fun _ => none))
        0 5 (Z_to_bv 64 (2 ^ 32))
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckUnmodeled :=
  by
  refine ⟨?_, ?_⟩ <;> sched_check_run

/-- THE PARAMETER IS READ AT FOUR BYTES, and this pin has no Rocq original.
`do_sched_setscheduler` copies `sizeof(struct sched_param)` bytes
(kernel/sched/syscalls.c:887-888, Linux v6.18.46), and `struct sched_param`
is one `int sched_priority` (include/linux/sched.h:410-412): four bytes.
`sched_param_mem_3` backs three of them at `param` and nothing at the
fourth, so the read is `none`, `access_ok` admits the range, and the
checker declines — Linux answers -EFAULT there, and the ledger cannot say
which bytes were read first.  A checker reading one, two or three bytes
finds them all backed and reaches the SCHED_IDLE answer: it accepts the 0
offered here, which every other readable fixture in this file, being
`sched_param_mem`'s four bytes, would let it do unnoticed.  The
completeness lemma ties the checker's width to the spec's, and the spec's
own width pins are on the same fixture in
`Checks/Cases/Kernel/Sched/Syscalls.lean`; this one says it of the checker.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_param_is_read_at_four_bytes :
    check_sched_setscheduler
        (sched_setscheduler_in 0 5 sched_param_ptr sched_param_mem_3)
        0 5 sched_param_ptr
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled
    -- ...and not the -EFAULT Linux gives, which the model cannot name either
    ∧ check_sched_setscheduler
        (sched_setscheduler_in 0 5 sched_param_ptr sched_param_mem_3)
        0 5 sched_param_ptr
        (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckUnmodeled :=
  by
  refine ⟨?_, ?_⟩ <;> sched_check_run

/-- EVERY NEGATIVE POLICY TAKES THE FIRST GATE, whatever the pid, the
`param`, the input and the model: `SYSCALL_DEFINE3(sched_setscheduler)`
refuses `policy < 0` (kernel/sched/syscalls.c:962-968, Linux v6.18.46)
before `do_sched_setscheduler` is entered, so the checker's whole verdict
is the -EINVAL acceptance, with no copy-in ledger to agree on.
kernel: kernel/sched/syscalls.c:sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_negative_policy_any_effect_is_einval
    (pid policy param : word) (h : sint32 policy < 0)
    (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_sched_setscheduler i pid policy param eff m
      = check_ret_only eff (errno_ret EINVAL) m [] := by
  simp only [check_sched_setscheduler, h, decide_true, ↓reduceIte]

/-- EVERY NEGATIVE PID TOO, whatever the policy, the `param`, the input and
the model: a negative policy is refused first and by the same errno
(kernel/sched/syscalls.c:962-968, Linux v6.18.46), and every other
negative pid is refused by `do_sched_setscheduler` at :885-886, before the
copy at :887-888.
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_negative_pid_any_effect_is_einval
    (pid policy param : word) (h : sint32 pid < 0)
    (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_sched_setscheduler i pid policy param eff m
      = check_ret_only eff (errno_ret EINVAL) m [] := by
  by_cases hp : sint32 policy < 0
  · simp only [check_sched_setscheduler, hp, decide_true, ↓reduceIte]
  · simp only [check_sched_setscheduler, hp, decide_false, Bool.false_eq_true, ↓reduceIte, h,
      decide_true, Bool.or_true]

/-- A NULL `param` IS -EINVAL WHATEVER THE SIGNED ARGUMENTS DO.  A negative
policy is refused by `SYSCALL_DEFINE3(sched_setscheduler)`
(kernel/sched/syscalls.c:962-968, Linux v6.18.46) and a NULL `param` or a
negative pid by `do_sched_setscheduler` (:885-886); the three calls reach
that -EINVAL by the first route, by the second, and by both at once.
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_null_param_negative_arguments :
    check_sched_setscheduler (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 64 - 1)) 0 (fun _ => none))
        0 (Z_to_bv 64 (2 ^ 64 - 1)) 0 (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_setscheduler (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) 5 0 (fun _ => none))
        (Z_to_bv 64 (2 ^ 64 - 1)) 5 0 (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_sched_setscheduler (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)) 0 (fun _ => none))
        (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)) 0 (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> sched_check_run

/-- …and on each of those three calls the -EFAULT of a checker that read
the pointer first, and an -EINVAL carrying the four bytes of a copy that
never ran, are refused: both gates sit before the `copy_from_user` of
`do_sched_setscheduler` (kernel/sched/syscalls.c:887-888, Linux v6.18.46).
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_null_param_negative_argument_lies_rejected :
    check_sched_setscheduler (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 64 - 1)) 0 (fun _ => none))
        0 (Z_to_bv 64 (2 ^ 64 - 1)) 0 (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject
    ∧ check_sched_setscheduler (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 64 - 1)) 0 (fun _ => none))
        0 (Z_to_bv 64 (2 ^ 64 - 1)) 0 (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model = CheckReject
    ∧ check_sched_setscheduler (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) 5 0 (fun _ => none))
        (Z_to_bv 64 (2 ^ 64 - 1)) 5 0 (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject
    ∧ check_sched_setscheduler (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) 5 0 (fun _ => none))
        (Z_to_bv 64 (2 ^ 64 - 1)) 5 0 (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model = CheckReject
    ∧ check_sched_setscheduler (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)) 0 (fun _ => none))
        (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)) 0 (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject
    ∧ check_sched_setscheduler (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)) 0 (fun _ => none))
        (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)) 0 (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sched_check_run

end SetScheduler

/-! ## The witnesses, run

What a witness decides is WHICH admissible outcome progress is proved
from: the errno with its empty ledger on a refusal, `Unmodeled` on a
decline, and the one success with the four bytes it read. -/

/-- Evaluate closed signed readings with `sys_norm` before `rfl` compares witness outcomes.
The two pre-copy branches test `decide (sint32 policy < 0)` and `decide (sint32 pid < 0)`.
Direct `Int.decLt` reduction can expand `Nat.sub` before evaluating the bit-vector reading. -/
local macro "sched_witness_run" : tactic =>
  `(tactic| (unfold sched_setscheduler_witness; sys_norm <;> rfl))

section GetAffinityWitness

/-- 2^29 is a wrapping length: `(len * BITS_PER_BYTE) < nr_cpu_ids` is
computed in 32 bits on an `unsigned int`
(kernel/sched/syscalls.c:1335-1336, Linux v6.18.46), the product is 0,
and the witness is the -EINVAL with nothing stored.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_witness_refuses_a_wrapping_length :
    sched_getaffinity_witness 536870912 demo_model
      = ret_outcome (errno_ret EINVAL) demo_model := rfl

/-- 4 is refused by the alignment gate, `len & (sizeof(unsigned long)-1)`
(kernel/sched/syscalls.c:1337-1338), by the same -EINVAL.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_witness_refuses_an_unaligned_length :
    sched_getaffinity_witness 4 demo_model = ret_outcome (errno_ret EINVAL) demo_model := rfl

/-- 8 passes both gates on any machine with at most 64 CPUs and is then
answered from `cpumask_size()` (kernel/sched/syscalls.c:1345-1350), which
the model does not carry: the witness is the decline, which is an
admissible outcome and what progress holds on.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_witness_declines_a_modeled_out_length :
    sched_getaffinity_witness 8 demo_model = Unmodeled := rfl

end GetAffinityWitness

section SetSchedulerWitness

/-- SCHED_IDLE at priority 0 on the caller is the one answer past the task
lookup: 0 from `__sched_setscheduler` (kernel/sched/syscalls.c:555-571 and
its exits), with the four bytes `do_sched_setscheduler` copied in
(:887-888) on the ledger.
kernel: kernel/sched/syscalls.c:__sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_witness_is_the_idle_success :
    sched_setscheduler_witness 0 5 sched_param_ptr
        (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0)) demo_model
      = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model [] := by
  sched_witness_run

/-- A NEGATIVE POLICY IS THE WITNESS'S FIRST DECISION TOO:
`SYSCALL_DEFINE3(sched_setscheduler)` refuses `policy < 0`
(kernel/sched/syscalls.c:962-968, Linux v6.18.46) before
`do_sched_setscheduler` reads the pointer, so the witness is the -EINVAL
with an empty ledger and not the -EFAULT that unreadable `param` would
otherwise draw at :887-888.
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_witness_refuses_a_negative_policy :
    sched_setscheduler_witness 0 (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 63))
        (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 63)) (fun _ => none))
        demo_model
      = ret_outcome (errno_ret EINVAL) demo_model := by
  sched_witness_run

/-- A NULL `param` AND A NEGATIVE PID ARE ONE WITNESS, because they are one
test: `if (unlikely(!param || pid < 0)) return -EINVAL;`
(kernel/sched/syscalls.c:885-886, Linux v6.18.46) refuses both before the
copy at :887-888, so both witnesses are the same -EINVAL with an empty
ledger — the second even though its `param` is a readable `struct
sched_param`.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_witness_agrees_on_null_param_and_negative_pid :
    sched_setscheduler_witness 0 5 0 (sched_setscheduler_in 0 5 0 (fun _ => none)) demo_model
      = ret_outcome (errno_ret EINVAL) demo_model
    ∧ sched_setscheduler_witness (Z_to_bv 64 (2 ^ 64 - 1)) 5 sched_param_ptr
        (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) 5 sched_param_ptr (sched_param_mem 0))
        demo_model
      = ret_outcome (errno_ret EINVAL) demo_model := by
  refine ⟨?_, ?_⟩ <;> sched_witness_run

/-- Four bytes whose last one is at `TASK_SIZE` fail `access_ok` before a
load (`__access_ok`, include/asm-generic/access_ok.h; the copy is
`do_sched_setscheduler`'s, kernel/sched/syscalls.c:887-888): -EFAULT with
no ledger.  `task_size_minus` is the checker pins' alias, and is one for
the reason given where it is defined.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem sched_setscheduler_witness_faults_past_task_size :
    sched_setscheduler_witness 0 5 (task_size_minus 3)
        (sched_setscheduler_in 0 5 (task_size_minus 3) (fun _ => none)) demo_model
      = ret_outcome (errno_ret EFAULT) demo_model := by
  unfold task_size_minus
  sched_witness_run

/-- Four bytes wholly under `TASK_SIZE` that nothing backs pass `access_ok`
and fault inside the copy itself (`do_sched_setscheduler`,
kernel/sched/syscalls.c:887-888, Linux v6.18.46): Linux answers -EFAULT,
and the witness declines rather than name it, because the model cannot
say which bytes the copy read before it faulted — the reason the checker
declines the same call in `sched_setscheduler_fault_is_the_range_verdict`.
A witness naming the fault here would exhibit an outcome outside the spec,
and `sched_setscheduler_witness_ok` would not close; this pin says which
branch the fixture takes, which that lemma does not.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_witness_declines_an_unbacked_range :
    sched_setscheduler_witness 0 5 (task_size_minus 4)
        (sched_setscheduler_in 0 5 (task_size_minus 4) (fun _ => none)) demo_model = Unmodeled := by
  unfold task_size_minus
  sched_witness_run

/-- SCHED_FIFO at priority 1 is decided by `RLIMIT_RTPRIO` and
`CAP_SYS_NICE` (`user_check_sched_setscheduler`,
kernel/sched/syscalls.c:483-493 and :524-526), which the model does not
carry: the witness declines.
kernel: kernel/sched/syscalls.c:user_check_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_witness_declines_fifo :
    sched_setscheduler_witness 0 1 sched_param_ptr
        (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 1)) demo_model = Unmodeled := by
  sched_witness_run

/-- A positive pid with no tid pinned is a task the model cannot say is
this one (`find_process_by_pid`, kernel/sched/syscalls.c:253-256, is
`find_task_by_vpid` for it), so the witness declines; pin the tid and the
same call is the success.
kernel: kernel/sched/syscalls.c:find_process_by_pid,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_witness_declines_an_unpinned_pid :
    sched_setscheduler_witness 4096 5 sched_param_ptr
        (sched_setscheduler_in 4096 5 sched_param_ptr (sched_param_mem 0)) demo_model = Unmodeled
    ∧ sched_setscheduler_witness 4096 5 sched_param_ptr
        (sched_setscheduler_in 4096 5 sched_param_ptr (sched_param_mem 0)) sched_tid_model
      = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) sched_tid_model [] := by
  refine ⟨?_, ?_⟩ <;> sched_witness_run

end SetSchedulerWitness

section SchedYield

/-! ## sched_yield (124)

`check_sched_yield` has one branch, so what there is to pin is the shape
of the effect it accepts rather than a decision between branches: the 0,
and the four neighbouring answers no kernel gives.  The Rocq `Example`s
these restate go through `check_syscall`, which quantifies the arguments
as well; the argument-independence half is the spec-level file's, since
this checker takes no argument to vary.

Each of the three restatements keeps its Rocq `Example`'s name verbatim —
`sched_yield_answers_zero`, `sched_yield_nonzero_answers_rejected` and
`sched_yield_effect_shape_is_bare` of
`theories/LinuxProcessSem/Checks/Cases/Kernel/Sched/Syscalls.v` — which
is the mapping this file's header describes, and the reason none carries a
`rocq-twin:` line: `linux-process-semantics@ff0313ba4f:tools/check_lean_pin_evidence.py` resolves that
marker against the Rocq file at the Lean file's own mirror path, and no
Rocq file sits at a `Checks/Cases/Checks/` one, so a `rocq-twin:` here
names a file that does not exist however right the name is.
`sched_yield_witness_is_the_zero` twins no Rocq `Example`: the Rocq tree
has no check file for the witnesses.

WHERE THESE WERE READ.  As in the spec-level file, and for the reason
given there: v6.18.46, commit 1f99e9ab748f, re-read at the pin rather
than carried over from the v6.12.1 tree the port was drafted against. -/

/-- THE ANSWER IS 0.  `SYSCALL_DEFINE0(sched_yield)` is
`do_sched_yield(); return 0;` and its kernel-doc says "Return: 0"; the
wrapper is cited for the 0, the helper for what does not move.
kernel: kernel/sched/syscalls.c:sched_yield,do_sched_yield@v6.18.46 -/
theorem sched_yield_answers_zero :
    check_sched_yield (mkEffect (Z_to_bv 64 0) [] []) demo_model = CheckOk demo_model [] := rfl

/-- THE REFUSALS, conjunct for conjunct as Rocq states them: the two
nearest integers, `-EINTR`, and the `-EPERM` the Rocq example names as the
word `ALLOW_ERROR_INJECTION` makes reachable under an override — a
residual under which every word is reachable, not that one alone
(`Sys.Kernel.Sched.Syscalls.sched_yield_spec` has the source), so all four
refusals rest on the premise that none is attached.  Four conjuncts, three
words: `errno_ret EPERM` is the all-ones word of the second conjunct
(`sched_yield_refused_errnos_are_these_words` in
`Checks/Cases/Kernel/Sched/Syscalls.lean` pins it, and that the three are
distinct), and the redundancy is Rocq's, kept so a reader comparing the
two finds the same shape.  A `CheckUnmodeled` is impossible and no
conjunct asserts one: the checker has no fail-closed branch.

WHY THE ERRNO HEADER IS CITED BESIDE THE SYSCALL.
`linux-process-semantics@ff0313ba4f:tools/check_lean_pin_evidence.py` reads a pin's polarity off `¬`, `≠`,
`False` and `Unmodeled`, so a `= CheckReject` verdict is judged a POSITIVE
claim and held to KMENTION: every uppercase constant the statement names
and this tree defines must occur in the cited symbols' text.  The syscall
spells no errno — its `return 0;` is the whole reason `-EINTR` is refused
— so the first version of this pin, cited to `do_sched_yield` alone, drew
the finding, and a second version answered it by spelling the two errnos
as words, which lost the tie to `errno_ret` that Rocq's spelling carries
for free.  Neither was needed: an annotation may cite several
`<file>:<symbol>` groups and KMENTION reads the text of all of them, the
shape the tool's own header gives for a set of outcomes decided in
different places.  So the header that defines `EPERM` and `EINTR` is
cited beside the syscall that returns 0: the syscall is why the words are
refused, the header is which words they are.
kernel: kernel/sched/syscalls.c:sched_yield,do_sched_yield; include/uapi/asm-generic/errno-base.h:EPERM,EINTR@v6.18.46 -/
theorem sched_yield_nonzero_answers_rejected :
    check_sched_yield (mkEffect (Z_to_bv 64 1) [] []) demo_model = CheckReject
    ∧ check_sched_yield (mkEffect (Z_to_bv 64 (2 ^ 64 - 1)) [] []) demo_model = CheckReject
    ∧ check_sched_yield (mkEffect (errno_ret EINTR) [] []) demo_model = CheckReject
    ∧ check_sched_yield (mkEffect (errno_ret EPERM) [] []) demo_model = CheckReject := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- …and a 0 that claims to have written user memory, read it, or freed a
mapping is refused too: the call has no output parameter, no argument to
fetch and nothing to unmap.
kernel: kernel/sched/syscalls.c:do_sched_yield@v6.18.46 -/
theorem sched_yield_effect_shape_is_bare :
    check_sched_yield (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 4096, [Z_to_bv 8 0])] []) demo_model
      = CheckReject
    ∧ check_sched_yield
        (with_copyins [(Z_to_bv 64 4096, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckReject
    ∧ check_sched_yield
        (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 4096, Z_to_bv 64 4096)] [] [])
        demo_model = CheckReject := by
  refine ⟨rfl, rfl, rfl⟩

/-- The witness is the one outcome the spec admits, which is what progress
is proved from here: there is no declining branch to exhibit instead; the
0 is the wrapper's.
kernel: kernel/sched/syscalls.c:sched_yield,do_sched_yield@v6.18.46 -/
theorem sched_yield_witness_is_the_zero :
    sched_yield_witness demo_model = Ok (mkEffect (Z_to_bv 64 0) [] []) demo_model [] := rfl

end SchedYield

-- lean-port sentinel: ticket V-Kernel-Sched-Syscalls appends below this line

section V_Kernel_Sched_Syscalls

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-- Compute a `sched_setscheduler` verdict on closed arguments through the
real table; the SetScheduler section says why `rfl` alone cannot. -/
local macro "sched_table_check_run" lookup:term : tactic =>
  `(tactic| (unfold check_syscall check_syscall_in; rw [$lookup:term];
             simp only [arm_unfold]; unfold check_sched_setscheduler; sys_norm <;> rfl))

/-! ## V-Kernel-Sched-Syscalls — the three sched arms over the real table

WHAT IS TWINNED HERE.  The sections above restate the verdict `Example`s
of `theories/LinuxProcessSem/Checks/Cases/Kernel/Sched/Syscalls.v` on the
checkers, because `checked_table` had no row for 119, 123 or 124 when they
were written, and leave the restatement through `check_syscall` to the
registration.  This is the registration.  Each of those `Example`s is
restated here through the Lean `check_syscall`, over `checked_table`
itself, at the Rocq input and fixture, under its Rocq name with
`_over_the_real_table` after it.  So is
`sched_yield_ignores_every_argument_word`, which the SchedYield section
leaves out because `check_sched_yield` takes no register.
`sched_yield_is_modeled` is about the dispatcher's table and stays the
spec-level file's.  The kernel reading of each example is its
checker-level twin's docstring above; a docstring here names the lines
that decide the outcome and what the arm adds.

WHAT A PIN HERE ADDS to its checker-level twin is the ARM's claim: that
the lookup at 119, 123 or 124 finds `arm_sched_setscheduler`,
`arm_sched_getaffinity` or `arm_sched_yield` rather than the dispatcher's
own decline, and that the arm hands its checker the registers
`SC_RISCV_REGS_TO_ARGS` (arch/riscv/include/asm/syscall_wrapper.h:21-24,
Linux v6.18.46) maps to the parameters: `a0`, `a1` and `a2` as `pid`,
`policy` and `param` for 119, `a1` as `len` for 123, and no register for
124, whose `SYSCALL_DEFINE0` (:99-103) takes none.  The swapped pins
below carry the order where a Rocq example does not.

POLARITY: the evidence line is `kernel:` on every pin about the kernel's
answer, and `model:` on a pin about the table's own contents. -/

/-- The lookup the dispatcher performs on a `sched_setscheduler_in`:
`in_sysno` is `119` whatever the registers and memory hold.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_sched_setscheduler_in (pid policy param : word) (mem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (sched_setscheduler_in pid policy param mem).in_sysno)
      = some arm_sched_setscheduler :=
  lookup_ca_checked_table_sched_setscheduler

/-- The lookup on a `sched_getaffinity_in`: `in_sysno` is `123`.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_sched_getaffinity_in (pid len user_mask_ptr : word) :
    lookup_ca checked_table (bv_unsigned (sched_getaffinity_in pid len user_mask_ptr).in_sysno)
      = some arm_sched_getaffinity :=
  lookup_ca_checked_table_sched_getaffinity

/-- The lookup on a `sched_yield_in`: `in_sysno` is `124`.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_sched_yield_in (a0 a1 a2 a3 a4 a5 : word) :
    lookup_ca checked_table (bv_unsigned (sched_yield_in a0 a1 a2 a3 a4 a5).in_sysno)
      = some arm_sched_yield :=
  lookup_ca_checked_table_sched_yield

/-! ### sched_getaffinity (123), through `check_syscall` -/

/-- `sched_getaffinity_wrapping_lengths_are_einval` over the real table:
every multiple of 2^29 below 2^32 in `a1` is the -EINVAL of the size gate
at kernel/sched/syscalls.c:1335-1336 (Linux v6.18.46), with `a0` and `a2`
holding the Rocq example's garbage.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_wrapping_lengths_are_einval_over_the_real_table :
    check_syscall (sched_getaffinity_in 0 0 3735928559)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (sched_getaffinity_in 0 536870912 3735928559)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (sched_getaffinity_in 0 1073741824 3735928559)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (sched_getaffinity_in 0 1610612736 3735928559)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (sched_getaffinity_in 0 2147483648 3735928559)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (sched_getaffinity_in 0 2684354560 3735928559)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (sched_getaffinity_in 0 3221225472 3735928559)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (sched_getaffinity_in 0 3758096384 3735928559)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model [] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `sched_getaffinity_compat_aligned_lengths_are_einval` over the real
table: 4, 12 and 2^32 - 4 in `a1` fail the native alignment gate,
`len & (sizeof(unsigned long)-1)`, at kernel/sched/syscalls.c:1337-1338
(Linux v6.18.46).
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_compat_aligned_lengths_are_einval_over_the_real_table :
    check_syscall (sched_getaffinity_in 0 4 3735928559)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (sched_getaffinity_in 0 12 3735928559)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (sched_getaffinity_in 0 4294967292 3735928559)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model [] := by
  exact ⟨rfl, rfl, rfl⟩

/-- `sched_getaffinity_wrap_neighbours_are_unmodeled` over the real table:
2^29 - 8 and 2^29 + 8 in `a1` pass both gates at
kernel/sched/syscalls.c:1335-1338 (Linux v6.18.46) and are declined, while
2^29 between them is the size gate's -EINVAL.  With 0 in `a0` and an odd
word in `a2`, an arm reading either of those as the length answers
-EINVAL to the two neighbours, which the first two conjuncts refuse.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_wrap_neighbours_are_unmodeled_over_the_real_table :
    check_syscall (sched_getaffinity_in 0 536870904 3735928559)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckUnmodeled
    ∧ check_syscall (sched_getaffinity_in 0 536870920 3735928559)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckUnmodeled
    ∧ check_syscall (sched_getaffinity_in 0 536870912 3735928559)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model [] := by
  exact ⟨rfl, rfl, rfl⟩

/-- `sched_getaffinity_wrapping_length_lies_rejected` over the real table:
on the wrapping length 2^29 the size gate at
kernel/sched/syscalls.c:1335-1336 (Linux v6.18.46) returns before the
task lookup and the copy out, so a byte count, -EFAULT, -ESRCH and an
-EINVAL that wrote the mask are refused.  Rocq spells the -ESRCH as the
number 3; `State` here has `ESRCH`, as the checker-level twin uses.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_wrapping_length_lies_rejected_over_the_real_table :
    check_syscall (sched_getaffinity_in 0 536870912 3735928559)
        (mkEffect 8 [] []) demo_model = CheckReject
    ∧ check_syscall (sched_getaffinity_in 0 536870912 3735928559)
        (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject
    ∧ check_syscall (sched_getaffinity_in 0 536870912 3735928559)
        (mkEffect (errno_ret ESRCH) [] []) demo_model = CheckReject
    ∧ check_syscall (sched_getaffinity_in 0 536870912 3735928559)
        (mkEffect (errno_ret EINVAL) [(3735928559, [Z_to_bv 8 0])] []) demo_model
        = CheckReject := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- THE LENGTH IS `a1`, in both directions.  `len` is the second
parameter of `SYSCALL_DEFINE3(sched_getaffinity, pid, len, user_mask_ptr)`
(kernel/sched/syscalls.c:1329-1330, Linux v6.18.46), which
`SC_RISCV_REGS_TO_ARGS` takes from `a1`.  0 in `a1` beside 8 in `a0` and
`a2` is the size gate's -EINVAL (:1335-1336); 8 in `a1` beside 0 in the
other two passes both gates and is declined.  An arm reading `a0` or `a2`
as the length reverses both verdicts.
This pin has no Rocq original: no `Example` in the Rocq Cases file states it.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_length_is_a1_over_the_real_table :
    check_syscall (sched_getaffinity_in 8 0 8)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (sched_getaffinity_in 0 8 0)
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckUnmodeled := by
  exact ⟨rfl, rfl⟩

/-! ### sched_setscheduler (119), through `check_syscall` -/

/-- `sched_setscheduler_negative_priority_is_out_of_range` over the real
table: SCHED_FIFO with priority -1 and 100 is the range gate's -EINVAL at
kernel/sched/syscalls.c:567-568 (Linux v6.18.46), the priority read as the
`__u32` `_sched_setscheduler` copies it into (:771), and 99 passes that
gate into the RT request the model declines.
kernel: kernel/sched/syscalls.c:__sched_setscheduler,_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_negative_priority_is_out_of_range_over_the_real_table :
    check_syscall (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 4294967295))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 99))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckUnmodeled
    ∧ check_syscall (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 100))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckOk demo_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> sched_table_check_run lookup_sched_setscheduler_in

/-- THE ORDER OF THE TWO PRE-COPY -EINVALS over the real table.
`policy < 0` is decided in `SYSCALL_DEFINE3(sched_setscheduler)` itself
(kernel/sched/syscalls.c:962-968, Linux v6.18.46), before
`do_sched_setscheduler` is entered, so a negative policy beats the NULL
`param` and the negative pid of :880-888 and beats the -EFAULT an
unreadable `param` would raise; and `int policy` reads 2^32 + 5 as
SCHED_IDLE at :962, which `__sched_setscheduler` answers 0 at priority 0
(:555-571, :757).
kernel: kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_negative_policy_wins_over_the_real_table :
    check_syscall
        (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)) 0 (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall
        (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 63)) (fun _ => none))
        (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall
        (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 32 + 5)) sched_param_ptr (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckOk demo_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> sched_table_check_run lookup_sched_setscheduler_in

/-- `sched_setscheduler_fault_is_the_range_verdict` over the real table:
four bytes at `TASK_SIZE - 3` fail `__access_ok`
(include/asm-generic/access_ok.h:31-40, Linux v6.18.46) inside the copy
at kernel/sched/syscalls.c:887-888, so the -EFAULT is accepted with an
empty ledger and refused with one; four bytes at `TASK_SIZE - 4` pass the
range test, nothing backs them, and the call is declined.
`task_size_minus` is the checker-level alias, for the reason given where
it is defined.
kernel: kernel/sched/syscalls.c:do_sched_setscheduler; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem sched_setscheduler_fault_is_the_range_verdict_over_the_real_table :
    check_syscall (sched_setscheduler_in 0 5 (task_size_minus 3) (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (sched_setscheduler_in 0 5 (task_size_minus 4) (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckUnmodeled
    ∧ check_syscall (sched_setscheduler_in 0 5 (task_size_minus 3) (fun _ => none))
        (with_copyins [(task_size_minus 3, 4)] (mkEffect (errno_ret EFAULT) [] []))
        demo_model = CheckReject := by
  unfold task_size_minus
  refine ⟨?_, ?_, ?_⟩ <;> sched_table_check_run lookup_sched_setscheduler_in

/-- `sched_setscheduler_declines` over the real table: SCHED_FIFO at
priority 1, SCHED_NORMAL and SCHED_BATCH at 0, policy 7, SCHED_IDLE with
SCHED_RESET_ON_FORK, and pid 4096 on a model with no tid pinned are each
declined; what decides each is named in the checker-level twin's
docstring (`user_check_sched_setscheduler` and `_sched_setscheduler` in
kernel/sched/syscalls.c, `normal_policy` in kernel/sched/sched.h, Linux
v6.18.46).
kernel: kernel/sched/syscalls.c:user_check_sched_setscheduler,_sched_setscheduler; kernel/sched/sched.h:normal_policy@v6.18.46 -/
theorem sched_setscheduler_declines_over_the_real_table :
    check_syscall (sched_setscheduler_in 0 1 sched_param_ptr (sched_param_mem 1))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled
    ∧ check_syscall (sched_setscheduler_in 0 0 sched_param_ptr (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled
    ∧ check_syscall (sched_setscheduler_in 0 3 sched_param_ptr (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled
    ∧ check_syscall (sched_setscheduler_in 0 7 sched_param_ptr (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled
    ∧ check_syscall (sched_setscheduler_in 0 (Z_to_bv 64 (5 + 2 ^ 30)) sched_param_ptr
          (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled
    ∧ check_syscall (sched_setscheduler_in 4096 5 sched_param_ptr (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sched_table_check_run lookup_sched_setscheduler_in

/-- `sched_setscheduler_idle_is_zero` over the real table: SCHED_IDLE at
priority 0 on the caller is 0 from `__sched_setscheduler`
(kernel/sched/syscalls.c:555-571, Linux v6.18.46) with the four bytes
copied at :887-888 on the ledger; -EPERM, -EINVAL, a write to the
parameter and an empty ledger are refused.
kernel: kernel/sched/syscalls.c:__sched_setscheduler,user_check_sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_idle_is_zero_over_the_real_table :
    check_syscall (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EPERM) [] [])) demo_model
      = CheckReject
    ∧ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckReject
    ∧ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)]
          (mkEffect (Z_to_bv 64 0) [(sched_param_ptr, [Z_to_bv 8 0])] [])) demo_model
      = CheckReject
    ∧ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        (mkEffect (Z_to_bv 64 0) [] []) demo_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> sched_table_check_run lookup_sched_setscheduler_in

/-- `sched_setscheduler_pid_is_the_pinned_tid` over the real table, on
`sched_tid_model` (Rocq's `with_tid 4096 demo_model`): pid 4096, and
`2^32 + 4096`, which `pid_t` cuts to it, name the caller and are answered
0; 4097 is declined; pid 0 is `current` (`find_process_by_pid`,
kernel/sched/syscalls.c:253-256, Linux v6.18.46, reached from
`do_sched_setscheduler`'s `CLASS(find_get_task, p)(pid)` at :890).
kernel: kernel/sched/syscalls.c:find_process_by_pid,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_pid_is_the_pinned_tid_over_the_real_table :
    check_syscall (sched_setscheduler_in 4096 5 sched_param_ptr (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) sched_tid_model
      = CheckOk sched_tid_model []
    ∧ check_syscall
        (sched_setscheduler_in (Z_to_bv 64 (2 ^ 32 + 4096)) 5 sched_param_ptr (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) sched_tid_model
      = CheckOk sched_tid_model []
    ∧ check_syscall (sched_setscheduler_in 4097 5 sched_param_ptr (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) sched_tid_model
      = CheckUnmodeled
    ∧ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) sched_tid_model
      = CheckOk sched_tid_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sched_table_check_run lookup_sched_setscheduler_in

/-- THE REGISTERS ARE `a0`, `a1`, `a2`, against the two swaps
`sched_setscheduler_idle_is_zero_over_the_real_table` does not refuse.
`SYSCALL_DEFINE3(sched_setscheduler, pid, policy, param)`
(kernel/sched/syscalls.c:962, Linux v6.18.46) takes them in that order
through `SC_RISCV_REGS_TO_ARGS`.  5 in `a0` and 0 in `a1` is SCHED_NORMAL
for pid 5, which no tid pins on `demo_model`, and is declined; an arm
swapping `a0` and `a1` would see the idle call on the caller and accept
the 0.  `sched_param_ptr` in `a1` and 5 in `a2` is policy 4096 with its
parameter at address 5, which the range test admits and nothing backs, so
it is declined; an arm swapping `a1` and `a2` would accept the 0 too.
This pin has no Rocq original: no `Example` in the Rocq Cases file states it.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/sched/syscalls.c:sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_registers_in_order_over_the_real_table :
    check_syscall (sched_setscheduler_in 5 0 sched_param_ptr (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled
    ∧ check_syscall (sched_setscheduler_in 0 sched_param_ptr 5 (sched_param_mem 0))
        (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> sched_table_check_run lookup_sched_setscheduler_in

/-! ### sched_yield (124), through `check_syscall` -/

/-- `sched_yield_answers_zero` over the real table: `SYSCALL_DEFINE0(sched_yield)`
is `do_sched_yield(); return 0;` (kernel/sched/syscalls.c:1382-1386,
Linux v6.18.46).
kernel: kernel/sched/syscalls.c:sched_yield,do_sched_yield@v6.18.46 -/
theorem sched_yield_answers_zero_over_the_real_table :
    check_syscall sched_yield_zeros (mkEffect (Z_to_bv 64 0) [] []) demo_model
      = CheckOk demo_model [] := by
  rfl

/-- `sched_yield_ignores_every_argument_word` over the real table: riscv64's
`SYSCALL_DEFINE0` (arch/riscv/include/asm/syscall_wrapper.h:99-103, Linux
v6.18.46) takes `const struct pt_regs *__unused` and expands without
`SC_RISCV_REGS_TO_ARGS`, so the 0 of kernel/sched/syscalls.c:1382-1386 is
the answer at the three register shapes Rocq names.  The checker-level
SchedYield section leaves this example to this pin.  Register 1 of the
second shape is `errno_ret EINVAL`, as Rocq spells it: an argument the
wrapper discards, not an answer, so the header that defines `EINVAL` is
cited beside the wrapper, as the spec-level twin of this example does.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SYSCALL_DEFINE0; kernel/sched/syscalls.c:sched_yield; include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
theorem sched_yield_ignores_every_argument_word_over_the_real_table :
    check_syscall
        (sched_yield_in (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1))
          (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1))
          (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)))
        (mkEffect (Z_to_bv 64 0) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall
        (sched_yield_in 4096 (errno_ret EINVAL) (Z_to_bv 64 0x7fff80000000) (Z_to_bv 64 (2 ^ 32)) 1 0)
        (mkEffect (Z_to_bv 64 0) [] []) demo_model = CheckOk demo_model []
    ∧ check_syscall (sched_yield_in 0 0 0 0 0 (Z_to_bv 64 (2 ^ 64 - 1)))
        (mkEffect (Z_to_bv 64 0) [] []) demo_model = CheckOk demo_model [] := by
  exact ⟨rfl, rfl, rfl⟩

/-- `sched_yield_nonzero_answers_rejected` over the real table: 1, the
all-ones word, -EINTR and -EPERM are refused, on the premise the
checker-level twin names (no error-injection override attached).
kernel: kernel/sched/syscalls.c:sched_yield,do_sched_yield; include/uapi/asm-generic/errno-base.h:EPERM,EINTR@v6.18.46 -/
theorem sched_yield_nonzero_answers_rejected_over_the_real_table :
    check_syscall sched_yield_zeros (mkEffect (Z_to_bv 64 1) [] []) demo_model = CheckReject
    ∧ check_syscall sched_yield_zeros (mkEffect (Z_to_bv 64 (2 ^ 64 - 1)) [] []) demo_model
      = CheckReject
    ∧ check_syscall sched_yield_zeros (mkEffect (errno_ret EINTR) [] []) demo_model
      = CheckReject
    ∧ check_syscall sched_yield_zeros (mkEffect (errno_ret EPERM) [] []) demo_model
      = CheckReject := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `sched_yield_effect_shape_is_bare` over the real table: a 0 carrying a
write, a copy-in or an unmapping is refused; `do_sched_yield`
(kernel/sched/syscalls.c, Linux v6.18.46) touches no user memory.
kernel: kernel/sched/syscalls.c:do_sched_yield@v6.18.46 -/
theorem sched_yield_effect_shape_is_bare_over_the_real_table :
    check_syscall sched_yield_zeros
        (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 4096, [Z_to_bv 8 0])] []) demo_model = CheckReject
    ∧ check_syscall sched_yield_zeros
        (with_copyins [(Z_to_bv 64 4096, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model
      = CheckReject
    ∧ check_syscall sched_yield_zeros
        (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 4096, Z_to_bv 64 4096)] [] [])
        demo_model = CheckReject := by
  exact ⟨rfl, rfl, rfl⟩

/-! ### The witnesses the table hands `receptive`

`syscall_spec_witness` dispatches over the same table, so each arm's
`ca_witness` is what it answers at its number; the witness pins above run
the witnesses at bare arguments, and these run them through the arm, at
calls where a misread register changes the outcome. -/

/-- SCHED_IDLE at priority 0 on the caller: the witness is the 0 with the
four bytes copied at kernel/sched/syscalls.c:887-888 (Linux v6.18.46) on
the ledger; with 5 in `a0` and 0 in `a1` it is the decline, where an arm
swapping the two would hand the witness the idle call.
kernel: kernel/sched/syscalls.c:__sched_setscheduler,do_sched_setscheduler@v6.18.46 -/
theorem sched_setscheduler_witness_over_the_real_table :
    syscall_spec_witness (sched_setscheduler_in 0 5 sched_param_ptr (sched_param_mem 0)) demo_model
      = Ok (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] [])) demo_model []
    ∧ syscall_spec_witness (sched_setscheduler_in 5 0 sched_param_ptr (sched_param_mem 0))
        demo_model = Unmodeled := by
  refine ⟨?_, ?_⟩ <;>
    (unfold syscall_spec_witness table_witness
     rw [lookup_sched_setscheduler_in]
     simp only [arm_unfold]
     sched_witness_run)

/-- 2^29 in `a1` is the size gate's -EINVAL at
kernel/sched/syscalls.c:1335-1336 (Linux v6.18.46), and the witness
exhibits it; 2^29 in `a0` beside 8 in `a1` passes both gates and the
witness declines, where an arm reading `a0` would exhibit the -EINVAL.
kernel: kernel/sched/syscalls.c:sched_getaffinity@v6.18.46 -/
theorem sched_getaffinity_witness_over_the_real_table :
    syscall_spec_witness (sched_getaffinity_in 0 536870912 3735928559) demo_model
      = ret_outcome (errno_ret EINVAL) demo_model
    ∧ syscall_spec_witness (sched_getaffinity_in 536870912 8 0) demo_model = Unmodeled := by
  exact ⟨rfl, rfl⟩

/-- All six registers set to all-ones: the witness is the 0 of
kernel/sched/syscalls.c:1382-1386 (Linux v6.18.46).
kernel: kernel/sched/syscalls.c:sched_yield,do_sched_yield@v6.18.46 -/
theorem sched_yield_witness_over_the_real_table :
    syscall_spec_witness
        (sched_yield_in (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1))
          (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1))
          (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1))) demo_model
      = Ok (mkEffect (Z_to_bv 64 0) [] []) demo_model [] := by
  rfl

end V_Kernel_Sched_Syscalls

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Sched.Syscalls
