import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Drivers.Char.Random
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Drivers.Char.Random
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Drivers.Char.Random — what the getrandom CHECKER accepts and its WITNESS names, read off against Linux

Pins over `Checks.Sys.Drivers.Char.Random`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Drivers/Char/Random.v` and of
`theories/LinuxProcessSem/Checks/Witness/Drivers/Char/Random.v`: the
checker first, the witness last.  Not part of the trusted specification:
this file is QA on the definitions, written to be READ, and every pin in
it carries one evidence line, which follows what the pin states:
`kernel:` on a pin naming the verdict the checker gives or the outcome
the witness names, directly or through the table, on the calls it
states — one call, or every call of one shape — and `model:` on every
other: a byte walk, `len_word`, the table's own contents, the checker's
agreement with the witness, and the checker's and the witness's each
agreeing with itself across the two flag words it answers.  A `kernel:`
line does not say that every conjunct under it rests on the v6.18.46
Linux it names: where one rests on another version, or on the model —
its bound, its width, its seeded-pool premise, its closed world of
unmasked pointers, its effect convention (one write entry per delivery,
holding every byte the return counts, none for a delivery of no bytes,
and no zero-fill, unmap, copy or copy-in beside the outcome, even one
that leaves both memory views — the bytes as the process reads them and
as the kernel may write them, `ms_read_byte` and `ms_writable_byte` in
`RiscvSemantics.lean` — and the model as the outcome without it does), a
decline — the docstring beside it says so.  Every kernel line below was
read at Linux v6.18.46 (commit 1f99e9ab748f), except where a line names
another version beside it.

WHAT A CHECKER PIN IS.  `Checks/Cases/Drivers/Char/Random.lean` states,
for each decision of the spec, an `iff` over every outcome and refutes
the lie a kernel could not tell.  The checker is that spec made
executable — the four `_sound_`/`_complete_` lemmas beside it say the two
agree on every input — so a checker pin here does not restate those
`iff`s.  It hands the checker an `(input, effect)` pair, the shape a
trace hands it (or every pair of one shape, where the verdict is the
same on all of them), and states the verdict the checker gives on it.
That is the question a trace asks, and the one the four lemmas cannot:
soundness and completeness are biconditionals between two definitions
of this tree, and hold as well of a wrong spec beside a matching wrong
checker.  Only a verdict on a value named from outside tells the two
apart, which is what each `kernel:` pin on the checker below is — and it
is what refuses the checker that answers `CheckUnmodeled` everywhere,
which the four lemmas would accept beside an always-`unmodeled` spec.

WHAT THIS RESTATES.  Rocq keeps the worked examples for this checker in
`Checks/Cases/Drivers/Char/Random.v`, beside the spec's, as three
`Example`s over `check_syscall`: the small request delivered in full and
only in full, the inclusive edge of the bound, and the large request's
short count and -EINTR.  The dispatcher twin and the arm record are the
registration step's, so each is restated here on
`check_getrandom (getrandom_call n) 4096 n 0 eff getrandom_model`
directly — the body of the arm the checked table holds for 278 — and
again over `check_syscall`, in the section after the sentinel.  The
`RocqExamples` section below carries the first, one theorem per group of
conjuncts, under names that say what each accepts or refuses.  Rocq
states no lemma against `check_getrandom` itself, so there is no
`CheckReject` twin to carry by name; the rejections below are the ones
the spec's Cases file refutes, offered to the checker.  What a
restatement over `check_getrandom` loses is the register file — that 278
reads a0, a1 and a2 — and the section after the sentinel pins it: its
`check_syscall` twins separate a0 from a1, its flag-word pins separate
a2 from a3 and the whole register from its low half, and its
buffer-and-length pins do the same for a0 and a1 — for a1 restating what
`check_syscall_getrandom_call` there, stated for every length, already
fixes.  This file mirrors no Rocq Cases file, so
`check_lean_cases_parity.py` reads no coverage header here.

THE PROBES REACH THE CHECKER, NOT THESE PINS.  With 278 in the checked
table, `lps_runner` evaluates `check_getrandom` against the recorded
traces, but a pin here is a statement proved once and no trace evaluates
it.  Among the probe cases that state the same facts are the `CASE`
lines of `testing/syscall-check/tests/getrandom_spec.c` and
`testing/syscall-check/tests/getrandom_flags.c`, `grand-over` in
`testing/syscall-check/tests/rw_bytes_bound.c` (a length past the
bound), the `rand0` cases of `testing/syscall-check/tests/zero_len_fault.c`
(the zero-byte request in range, at the top of the address space and
past it) and two of `testing/syscall-check/tests/errno_getrandom.c`'s
(-EINTR admitted and -EAGAIN refused on a 512-byte request).  Each
`kernel:` pin below cites the kernel line and not the probe: what it
claims about Linux rests on the source its docstring reads, where a
probe's case shows what one run recorded.  A pin is a statement proved
once — on this file's fixtures or on every input of one shape — and no
trace evaluates it, even where a recorded pair is one of those inputs.
Each `model:` pin is about the model's own definitions and cites
neither.

THE FIXTURES are `Checks/Cases/Drivers/Char/Random.lean`'s, name for
name, so that spec and checker are pinned on the same call: the writable
zone `getrandom_dest` at 4096, `getrandom_model`, the call
`getrandom_call n` with the zone as both views, `getrandom_call_ro` and
`getrandom_call_wo` with it as one view, and `some_bytes n`, the
irreducible fixture list whose docstring there says why nothing may look
inside it.  The section after the sentinel defines calls of its own,
over the same zone and model, to set one register apart from another;
each precedes the first pin that uses it.  The byte walks over the zone are
`zone_walk_*` lemmas: that file's, registered in the `sys_simp` set,
which is how a checker pin reduces the walk's `match` without walking
the zone, and this file's own few, which the pins that need them name by
hand.

HOW THE PINS ARE PROVED.  The checker is a function and on a fixture it
computes, but `rfl` cannot look inside `some_bytes`, so a pin that
evaluates the checker runs a `simp +decide only` pass: `check_norm`,
which opens the checker and its zero-byte acceptor, DECIDES the closed
gates, rewrites the walk by the zone lemmas and the fixture list's
length by its two rewrites, and reduces the `match` on the effect — or,
where the `sys_simp` set holds no equation for the call, the walk or the
hypothesis a pin needs, a pass of the same kind with what it lacks named.  A
pin that evaluates the witness runs `witness_norm`, the same pass over
the witness, or its kind with what it lacks named — the call, and at
`getrandom_args` the walk too; where the witness names a
delivered list, the pin spells that list as the witness spells it, and
`rfl` closes what the pass leaves.  A pin through `check_syscall` or
`syscall_spec_witness` first computes the dispatch, then runs such a
pass or closes on the pin above that it restates.  Nothing here is
`decide` on a `check_result` or an `outcome`: `Model` has no
`DecidableEq`, so no such equation can be decided, and none needs to be.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE.  What these pins
prove are facts about this tree's own Lean definitions — the verdicts
and outcomes the legend above puts under `kernel:`, and the walks, the
length word, the table's contents, the checker's agreement with its
witness and each one's agreement with itself across the two flag words
that it puts under `model:` — each beside the evidence its docstring
names. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Drivers.Char.Random

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Drivers.Char.Random
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Drivers.Char.Random
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Drivers.Char.Random
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-- Evaluate a closed call of the checker: open it and its zero-byte
acceptor, decide every closed gate, rewrite the zone walk and the
fixture list's length with the `sys_simp` set, and reduce the `match` on
the effect.  The header says why this and not `rfl`. -/
scoped macro "check_norm" : tactic =>
  `(tactic| (simp +decide only [check_getrandom, check_getrandom_zero, sys_simp, ↓reduceIte]; done))

/-- The same pass over the witness; `rfl` closes the delivered list where
the pass leaves one. -/
scoped macro "witness_norm" : tactic =>
  `(tactic| (simp +decide only [getrandom_witness, sys_simp, ↓reduceIte]; first | done | rfl))

section RocqExamples

/-! ## Rocq's three examples, on the checker

Each is the conjunction Rocq states, on Rocq's fixture, with the verdict
the checker gives in place of the relation's membership.  Rocq's
admission reasons are on the Rocq examples; the kernel lines are the
spec file's, repeated where the verdict rests on them. -/

/-- A SMALL REQUEST IS DELIVERED IN FULL: sixteen bytes at 4096 with a
return of sixteen is accepted, the model unchanged and no event.  A
request of at most CHACHA_KEY_SIZE (32) bytes is copied straight out of
the key material (drivers/char/random.c:455-458), so nothing can cut it
short.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_small_request_accepts_full_delivery :
    check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect 16 [(4096, some_bytes 16)] [])
        getrandom_model = CheckOk getrandom_model [] := by
  check_norm

/-- ... AND ONLY IN FULL: the short count, the interrupt and the
over-delivery are refused on the same call.  Five of sixteen is a count
`get_random_bytes_user` cannot answer: a request of at most
CHACHA_KEY_SIZE bytes is copied out of the key material in one
`copy_to_iter` (:455-458) and never enters the loop whose
`signal_pending` test (:471-473) could cut a longer one short; the bare
-EINTR is the wait's (`wait_for_random_bytes`, :136-147), which the spec
keeps out of a small request on the seeded-pool premise
`bugs/getrandom-answers-rest-on-a-seeded-pool.md` records — the wait at
:1403 runs before `len` is read, so no length keeps it out by itself;
seventeen bytes is more than the iterator holds (`import_ubuf` sizes it
at `len`, lib/iov_iter.c:1440).  The -EINTR named is the one
`arch_do_signal_or_restart` makes of the wait's -ERESTARTSYS
(arch/riscv/kernel/signal.c:438-443).
kernel: drivers/char/random.c:getrandom,get_random_bytes_user,wait_for_random_bytes; lib/iov_iter.c:import_ubuf; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem check_getrandom_small_request_rejects_short_count_interrupt_and_over_delivery :
    check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect 5 [(4096, some_bytes 5)] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect (errno_ret EINTR) [] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect 17 [(4096, some_bytes 17)] [])
        getrandom_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- THE BOUND IS INCLUSIVE: 255 of 256 is refused, 256 of 256 is
accepted, and 255 of 257 is accepted again — the first request the
checker judges as large, admitted by the spec's `[1, buflen]` width as
on the 300-byte call below, not by a kernel line.  Above CHACHA_KEY_SIZE
the loop at :460-476 lands a 64-byte block per `copy_to_iter` (:465) and
breaks when the count is exhausted (:467-468) before the page test at
:471-473 can fire — `ret` is a multiple of 64 below 4096 — so nothing
but a fault, which the walk excludes, cuts 33..256 short; why the spec
stops at 256 rather than the page is on `getrandom_small_max`.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_small_bound_is_inclusive :
    check_getrandom (getrandom_call 256) 4096 256 0 (mkEffect 255 [(4096, some_bytes 255)] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 256) 4096 256 0 (mkEffect 256 [(4096, some_bytes 256)] [])
        getrandom_model = CheckOk getrandom_model []
    ∧ check_getrandom (getrandom_call 257) 4096 257 0 (mkEffect 255 [(4096, some_bytes 255)] [])
        getrandom_model = CheckOk getrandom_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- A LARGE REQUEST STILL ADMITS THE SHORT COUNT AND THE INTERRUPT: 300 of
300, 5 of 300, 1 of 300 and the bare -EINTR are all accepted.  The
counts are the spec's declared width, `[1, buflen]` (its docstring in
`Sys/Drivers/Char/Random.lean` says that costs priority 2, not 1): at
v6.18.46 a writable 300-byte destination is filled whole — the loop
breaks at :467-468 only on exhaustion or a faulting copy, and the page
test at :471-473 cannot fire below 4096 bytes — so 5 and 1 are admitted
as the man page's short count, not read off a kernel line.  Nor is the
-EINTR a v6.18.46 answer: the wait that can answer it there
(`wait_for_random_bytes`, called at :1403) is ruled out by the
seeded-pool premise `bugs/getrandom-answers-rest-on-a-seeded-pool.md`
records, and `get_random_bytes_user` answers no errno but -EFAULT
(:481).  It is `extract_crng_user`'s, on mainline v4.17 through v5.17
and the stable releases cut before the rewritten random.c reached their
line: for a request over 256 bytes, whenever `need_resched()` holds and
a signal is pending, it returns -ERESTARTSYS if nothing was copied yet
(drivers/char/random.c:1036-1040 at v4.17), and riscv makes that -EINTR
for a handler without SA_RESTART, as v6.18.46's
`arch_do_signal_or_restart` does (arch/riscv/kernel/signal.c:438-443).
`getrandom_large_request_still_admits_the_short_count_over_the_real_table`
below names the releases and gives the path's lines.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem check_getrandom_large_request_accepts_the_short_count_and_the_interrupt :
    check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect 300 [(4096, some_bytes 300)] [])
        getrandom_model = CheckOk getrandom_model []
    ∧ check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect 5 [(4096, some_bytes 5)] [])
        getrandom_model = CheckOk getrandom_model []
    ∧ check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect 1 [(4096, some_bytes 1)] [])
        getrandom_model = CheckOk getrandom_model []
    ∧ check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect (errno_ret EINTR) [] [])
        getrandom_model = CheckOk getrandom_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- ... and still refuses the bare 0: a nonzero request never succeeds
with nothing delivered — `get_random_bytes_user` answers 0 only for an
empty iterator (:440-441) and otherwise `ret ? ret : -EFAULT` (:481).
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_large_request_rejects_the_bare_zero :
    check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect 0 [] []) getrandom_model
      = CheckReject := by
  check_norm

end RocqExamples

section FlagWord

/-! ## Gate 1: the flag word

`SYSCALL_DEFINE3(getrandom, char __user *, ubuf, size_t, len, unsigned int, flags)`
(drivers/char/random.c:1385-1412, Linux v6.18.46) reads `flags` before
anything else: a
bit outside GRND_NONBLOCK | GRND_RANDOM | GRND_INSECURE is -EINVAL at
:1390-1391, GRND_INSECURE with GRND_RANDOM is -EINVAL at :1397-1398, and
GRND_RANDOM alone selects a pool the model does not distinguish.  The
spec models 0 and GRND_NONBLOCK and declines every other word, so the
checker's first answer on such a word is `CheckUnmodeled`, whatever the
input, the effect and the model: no argument is read before it. -/

/-- GRND_NONBLOCK alone is the plain call: with the pool ready the
`!crng_ready()` gate (:1400) is not entered, so :1401-1402 never answers
-EAGAIN and the request is delivered as at flags 0.
kernel: drivers/char/random.c:getrandom,crng_ready,get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_nonblock_accepts_full_delivery :
    check_getrandom (getrandom_call 16) 4096 16 1 (mkEffect 16 [(4096, some_bytes 16)] [])
        getrandom_model = CheckOk getrandom_model [] := by
  check_norm

/-- ... and the -EAGAIN a not-yet-ready pool would answer under it is
refused: the model rests on a seeded pool (the spec's flags note), so
:1401-1402 is unreachable.
kernel: drivers/char/random.c:getrandom,crng_ready@v6.18.46 -/
theorem check_getrandom_nonblock_rejects_eagain :
    check_getrandom (getrandom_call 16) 4096 16 1 (mkEffect (errno_ret EAGAIN) [] [])
        getrandom_model = CheckReject := by
  check_norm

/-- GRND_NONBLOCK is judged at every size, not at sixteen bytes alone: a
300-byte delivery in full and the zero-byte 0 are accepted under it as
at flags 0 — :1400 is not entered with the pool ready, and neither
:1408 nor :440-441 reads `flags`.
kernel: drivers/char/random.c:getrandom,crng_ready,get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_nonblock_accepts_at_every_size (i : SyscallInput) (m : Model) :
    check_getrandom (getrandom_call 300) 4096 300 1 (mkEffect 300 [(4096, some_bytes 300)] [])
        getrandom_model = CheckOk getrandom_model []
    ∧ check_getrandom i 4096 0 1 (mkEffect 0 [] []) m = CheckOk m [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- ... and the bare -EINTR is accepted under GRND_NONBLOCK too, at 300
bytes and at none.  The spec admits -EINTR on a large request and on a
zero-byte one at flags 1 as at flags 0: past the test that declines
every other flag word, `getrandom_spec` reads the flags no further, and
its interrupt is `getrandom_errnos`.  The checker tests it the same way,
and Rocq's does too.  At 300 bytes that
width covers a real answer, so the admission is priority 1's: with
GRND_NONBLOCK alone, `getrandom` on the kernels that carry
`extract_crng_user` tests it only on an unready pool
(drivers/char/random.c's :2021-2023 at v4.17, :1919-1921 at v5.17), so
with the pool ready the request reaches the -ERESTARTSYS
`check_getrandom_large_request_accepts_the_short_count_and_the_interrupt`
above traces, as it does at flags 0.  At v6.18.46 nothing answers -EINTR
under this flag: an unready pool is -EAGAIN at :1401-1402, before the
wait, and a ready one imports the buffer first (:1408-1410), where
`import_ubuf` (lib/iov_iter.c:1437-1438, Linux v6.18.46) answers no
errno but -EFAULT, before `get_random_bytes_user`, whose only errno is
-EFAULT too (:481).  At zero bytes no kernel answers it under this flag:
an unready pool is -EAGAIN before any wait, and with it ready no copy
loop is entered (`extract_crng_user`'s `while (nbytes)`,
drivers/char/random.c's :1035 at v4.17; `get_random_bytes_user`'s
:440-441 at v6.18.46).  There
the admission is the spec's width alone,
and its cost is priority 2 whatever the pool's state.  Pinned so that
closing either admission is a visible change here.
kernel: drivers/char/random.c:getrandom,crng_ready,get_random_bytes_user; lib/iov_iter.c:import_ubuf; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem check_getrandom_nonblock_admits_the_interrupt_by_width (i : SyscallInput) (m : Model) :
    check_getrandom (getrandom_call 300) 4096 300 1 (mkEffect (errno_ret EINTR) [] [])
        getrandom_model = CheckOk getrandom_model []
    ∧ check_getrandom i 4096 0 1 (mkEffect (errno_ret EINTR) [] []) m = CheckOk m [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- GRND_NONBLOCK IS THE PLAIN CALL, on every input, buffer, length,
effect and model: `check_getrandom` reads `flags` at its first gate and
nowhere after it, and 0 and GRND_NONBLOCK both pass that gate, so every
verdict it gives at flags 0 it gives at flags 1 — the zero-byte range
verdict at every address among them, which
`check_getrandom_nonblock_zero_length_range_verdict` names at three.
This is a fact about the checker's definition, not a kernel claim;
whether Linux agrees is argued on the point pins, each against its
kernel line.  With the pool ready it does: the `!crng_ready()` gate of
`getrandom` (drivers/char/random.c:1400, Linux v6.18.46) is not entered,
and nothing after it reads the flag.  On an unready pool it does not —
the flag answers -EAGAIN (:1401-1402) where flags 0 waits (:1403-1405) —
and the seeded-pool premise `bugs/getrandom-answers-rest-on-a-seeded-pool.md`
records rules that pool out;
`check_getrandom_nonblock_admits_the_interrupt_by_width` says where the
-EINTR this carries to the flag is the spec's width alone.  What this
refuses is an arm whose flags-1 verdict departs anywhere from its own
flags-0 verdict: one that range-tests only the buffer's low 48 bits
under the flag accepts 0 and refuses -EFAULT at
`getrandom(2^60, 0, GRND_NONBLOCK)`, and passes every point pin.  An arm
that moves a verdict at both flag words alike passes it.
model: `check_getrandom` reads `flags` at its first gate only, which 0 and GRND_NONBLOCK both pass -/
theorem check_getrandom_nonblock_is_the_plain_call (i : SyscallInput) (buf cap : word)
    (eff : SyscallEffect) (m : Model) :
    check_getrandom i buf cap 1 eff m = check_getrandom i buf cap 0 eff m := by
  check_norm

/-- GRND_RANDOM (2), GRND_RANDOM | GRND_NONBLOCK (3), GRND_INSECURE (4)
and an unknown bit (256) are declined for every input, every effect and
every model — the -EINVAL Linux answers at :1390-1391 for the unknown
bit included, since a decline is not a verdict on the effect.
kernel: drivers/char/random.c:getrandom@v6.18.46 -/
theorem check_getrandom_other_flag_words_decline (i : SyscallInput) (buf cap : word)
    (eff : SyscallEffect) (m : Model) :
    check_getrandom i buf cap 2 eff m = CheckUnmodeled
    ∧ check_getrandom i buf cap 3 eff m = CheckUnmodeled
    ∧ check_getrandom i buf cap 4 eff m = CheckUnmodeled
    ∧ check_getrandom i buf cap 256 eff m = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The flag word is compared WHOLE: a0..a2 arrive as 64-bit registers
and the checker takes `flags` as the spec does, so 2^32 — a word whose
low half is 0 — is declined, not accepted as flags 0.  (Linux's
`unsigned int` cast would take the low half, so Linux delivers at 2^32
as at 0; the spec's docstring says why the whole word is judged instead
— a narrowing, hence a decline and never a `CheckReject`.  No probe
passes such a word today, though `getrandom_flags.c` hands argv's
decimal to a2 raw and one could; a run that did would be declined, not
misjudged.)
kernel: drivers/char/random.c:getrandom@v6.18.46 -/
theorem check_getrandom_high_half_flags_decline (i : SyscallInput) (buf cap : word)
    (eff : SyscallEffect) (m : Model) :
    check_getrandom i buf cap (Z_to_bv 64 (2 ^ 32)) eff m = CheckUnmodeled := by
  check_norm

end FlagWord

section TransferBound

/-! ## Gate 2: the transfer bound

`Uaccess.rw_bytes_max` is 128 KiB, not a Linux constant; Linux clamps a
request at MAX_RW_COUNT in `import_ubuf` (lib/iov_iter.c:1435-1436, Linux
v6.18.46) and delivers.  The spec declines above the bound before it walks memory and
judges at the bound; the checker does the same. -/

/-- One byte over the bound is declined for every input, every effect and
every model — the gate sits in front of the walk, so no memory rescues it.
So is 2^32 + 16: `len` is a `size_t` (:1385), so a1 arrives whole and a
word whose low half reads 16 is a request 2^32 + 16 bytes long, over the
bound, never sixteen bytes.  What `import_ubuf` carries here is only that
Linux does NOT stop at 131072 — it clamps at MAX_RW_COUNT
(lib/iov_iter.c:1435-1436) and delivers — so both verdicts are the
model's bound, not a kernel answer.
kernel: drivers/char/random.c:getrandom; lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem check_getrandom_over_the_bound_declines (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    check_getrandom i 4096 131073 0 eff m = CheckUnmodeled
    ∧ check_getrandom i 4096 (Z_to_bv 64 (2 ^ 32 + 16)) 0 eff m = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- AT the bound, over any input whose destination the walk finds
writable, the call is judged as a large request: the interrupt and a
five-byte delivery are both accepted — the five bytes by the spec's
`[1, buflen]` width, as on the 300-byte call above, not by a kernel
line, and the interrupt as there, `extract_crng_user`'s on the kernels
that carry it: at v6.18.46 `get_random_bytes_user` tests for a signal
only at a page boundary, with a count in hand (:471-473), and answers
the count or -EFAULT (:481), so a signal there can cut the request short
but not answer -EINTR.  Stated on a hypothesis about the
walk because a 128 KiB zone is not a fixture worth evaluating;
`Checks/Cases/Drivers/Char/Random.lean`'s `all_writable_walks_the_bound`
shows it satisfiable.
kernel: lib/iov_iter.c:import_ubuf; drivers/char/random.c:getrandom,get_random_bytes_user; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem check_getrandom_at_the_bound_is_judged (i : SyscallInput) (m : Model) (bs : List byte)
    (hw : read_bytes_map i.in_wmem 4096 131072 = some bs) :
    check_getrandom i 4096 131072 0 (mkEffect (errno_ret EINTR) [] []) m = CheckOk m []
    ∧ check_getrandom i 4096 131072 0 (mkEffect 5 [(4096, some_bytes 5)] []) m = CheckOk m [] := by
  refine ⟨?_, ?_⟩ <;> simp +decide only [check_getrandom, hw, sys_simp, ↓reduceIte]

end TransferBound

section Destination

/-! ## Gate 3: the destination

`import_ubuf(ITER_DEST, ubuf, len, &iter)` (drivers/char/random.c:1408,
Linux v6.18.46) makes `ubuf` a destination and `get_random_bytes_user` only ever copies
INTO it (`copy_to_iter`, :456 and :465), so the walk is of the input's
WRITABLE view.  A destination the view does not hold in full is declined:
Linux would answer the count that landed before the fault, or -EFAULT
when nothing did (:481), and the spec declines the program bug rather
than pick. -/

/-- A destination half inside the zone (4600 for 16 bytes; the zone ends
at 4608) and one wholly outside it (8192) are declined for every effect.
kernel: lib/iov_iter.c:import_ubuf; drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_unwritable_destination_declines (eff : SyscallEffect) :
    check_getrandom (getrandom_call 16) 4600 16 0 eff getrandom_model = CheckUnmodeled
    ∧ check_getrandom (getrandom_call 16) 8192 16 0 eff getrandom_model = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- THE WALK READS THE WRITABLE VIEW: the zone as the readable view alone
is declined, and the zone as the writable view alone is delivered.  This
is the pin that fixes which view the checker walks.
kernel: lib/iov_iter.c:import_ubuf; drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_walks_the_writable_view (eff : SyscallEffect) :
    check_getrandom (getrandom_call_ro 16) 4096 16 0 eff getrandom_model = CheckUnmodeled
    ∧ check_getrandom (getrandom_call_wo 16) 4096 16 0 (mkEffect 16 [(4096, some_bytes 16)] [])
        getrandom_model = CheckOk getrandom_model [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- THE WALK IS OF EXACTLY `cap` BYTES FROM EXACTLY `buf`: the two
declines above sit eight bytes inside or wholly outside the zone, which
a walk from `buf + 1` or of `cap - 1` bytes would answer the same way.
The zone's last sixteen bytes (4592..4607) are delivered; one byte
further (4593, whose sixteenth byte is 4608) declines for every effect —
`import_ubuf` imports `len` bytes from `buf` (lib/iov_iter.c:1440) and
`get_random_bytes_user` copies into nothing else.
kernel: lib/iov_iter.c:import_ubuf; drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_walks_exactly_the_request (eff : SyscallEffect) :
    check_getrandom (getrandom_call 16) 4592 16 0 (mkEffect 16 [(4592, some_bytes 16)] [])
        getrandom_model = CheckOk getrandom_model []
    ∧ check_getrandom (getrandom_call 16) 4593 16 0 eff getrandom_model = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The walk is not the small request's alone: a LARGE request over a
destination the writable view does not hold is declined for every effect
and every model.  Stated on a hypothesis about the walk, as
`check_getrandom_at_the_bound_is_judged` is; `empty_walk_300` below
shows the hypothesis satisfiable, and the theorem after it says the same
on that fixture with nothing left to discharge.
kernel: lib/iov_iter.c:import_ubuf; drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_large_unwritable_destination_declines (i : SyscallInput)
    (eff : SyscallEffect) (m : Model) (hw : read_bytes_map i.in_wmem 4096 300 = none) :
    check_getrandom i 4096 300 0 eff m = CheckUnmodeled := by
  simp +decide only [check_getrandom, hw, sys_simp, ↓reduceIte]

/-- A 300-byte walk of a memory with no bytes fails at its first byte:
the writable view of `getrandom_call_ro` satisfies the hypothesis above.
model: the byte walk over the empty map, evaluated -/
theorem empty_walk_300 : read_bytes_map (fun _ => none) 4096 300 = none := by
  decide +kernel

/-- ... so the 300-byte request over the zone as the readable view alone
is declined for every effect, on the fixture and with no hypothesis.
kernel: lib/iov_iter.c:import_ubuf; drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_large_readable_only_destination_declines (eff : SyscallEffect) :
    check_getrandom (getrandom_call_ro 300) 4096 300 0 eff getrandom_model = CheckUnmodeled := by
  simp +decide only [check_getrandom, empty_walk_300, sys_simp, ↓reduceIte]

end Destination

section ZeroLength

/-! ## The zero-byte request

`import_ubuf` range-tests the empty range (lib/iov_iter.c:1437-1438, Linux
v6.18.46, through `__access_ok`, include/asm-generic/access_ok.h at the
same version) and
`get_random_bytes_user` returns 0 for an empty iterator (:440-441); the
wait at :1403-1405 precedes the import, so -EINTR joins either range
verdict.  The walk of zero bytes succeeds over every memory
(`read_bytes_map_zero`), so these pins quantify over the input. -/

/-- In range, 0 and -EINTR are both accepted, over every input.
kernel: lib/iov_iter.c:import_ubuf; include/asm-generic/access_ok.h:__access_ok; drivers/char/random.c:getrandom,get_random_bytes_user,wait_for_random_bytes; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem check_getrandom_zero_length_accepts_zero_and_the_interrupt (i : SyscallInput) (m : Model) :
    check_getrandom i 4096 0 0 (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_getrandom i 4096 0 0 (mkEffect (errno_ret EINTR) [] []) m = CheckOk m [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The lies at zero length: an empty write entry at the buffer, a
delivered byte, the bare 1, -EFAULT with the range fine, -EAGAIN at
flags 0, and -EINVAL past the flag gate — the errno `getrandom` answers
for `flags` alone (:1390-1391, :1397-1398), which a clean flag word has
already ruled out.  The empty entry is refused by the model's effect
convention, not by a kernel line: nothing is copied (:440-441), which
the entry says as well as the bare 0 does, and a delivery of no bytes
carries no entry, the canonical zero-byte shape `delivered_writes` in
`Sys/Uaccess.lean` states and the tracer records.  No pool state
answers the -EAGAIN at flags 0: :1401-1402 answers it only under
GRND_NONBLOCK, and the wait an unready pool enters instead,
`wait_for_random_bytes` (:136-147), answers 0 or -ERESTARTSYS.  And the
return is the whole register's here too: `syscall_handler` stores the
`long` whole (arch/riscv/include/asm/syscall.h:112), so 0 with its high
word set (2^32) is not 0 and the low word of -EINTR (0xfffffffc) is not
-EINTR — both refused where 0 and -EINTR are accepted.  This is the pin
that refuses a zero-byte acceptor comparing the low 32 bits: every other
lie here differs from 0 in its low word as well.
kernel: lib/iov_iter.c:import_ubuf; include/asm-generic/access_ok.h:__access_ok; drivers/char/random.c:getrandom,crng_ready,get_random_bytes_user,wait_for_random_bytes; arch/riscv/include/asm/syscall.h:syscall_handler@v6.18.46 -/
theorem check_getrandom_zero_length_rejects_the_lies (i : SyscallInput) (m : Model) :
    check_getrandom i 4096 0 0 (mkEffect 0 [(4096, [])] []) m = CheckReject
    ∧ check_getrandom i 4096 0 0 (mkEffect 1 [(4096, some_bytes 1)] []) m = CheckReject
    ∧ check_getrandom i 4096 0 0 (mkEffect 1 [] []) m = CheckReject
    ∧ check_getrandom i 4096 0 0 (mkEffect (errno_ret EFAULT) [] []) m = CheckReject
    ∧ check_getrandom i 4096 0 0 (mkEffect (errno_ret EAGAIN) [] []) m = CheckReject
    ∧ check_getrandom i 4096 0 0 (mkEffect (errno_ret EINVAL) [] []) m = CheckReject
    ∧ check_getrandom i 4096 0 0 (mkEffect 4294967296 [] []) m = CheckReject
    ∧ check_getrandom i 4096 0 0 (mkEffect 4294967292 [] []) m = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- No ledger rides along with the 0: a zero-fill, an unmap, a copy and a
copy-in beside it are each refused.  The copy, of the byte at 4096 onto
itself, is refused by the model's effect convention, not by a kernel
line: in every state it leaves both memory views and the model as the
bare 0 does, since `apply_copy` in `Run.lean` reads the snapshot taken
before the effect.  So are the other three where they change nothing:
the zero-fill where both views already hold 0 at that byte (`in_mem` and
`in_wmem` both `some 0`), a fact of `i`; the unmap where the overlay
`ms_mem` holds nothing at that byte, or holds the byte a readable,
writable segment of the loaded image holds there, a fact of the machine
state behind `i` and not of `i` — `apply_unmaps` in `Run.lean` rewrites
`ms_mem` alone and both views fall back to the image (`ms_read_byte`,
and `wview` in `RiscvSemantics.lean`), so one input can be an erased
byte on one state and no change on another; and the copy-in where its
page is not lazily backed or is already materialized, a fact of `m`.
Everywhere else they are the kernel's refusals: `get_random_bytes_user`
returns at :440-441 before it touches memory.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_zero_length_rejects_other_ledgers (i : SyscallInput) (m : Model) :
    check_getrandom i 4096 0 0 (mkEffect 0 [] [(4096, 1)]) m = CheckReject
    ∧ check_getrandom i 4096 0 0 (SyscallEffect.mkEffectU 0 [] [] [(4096, 1)] [] []) m = CheckReject
    ∧ check_getrandom i 4096 0 0 (SyscallEffect.mkEffectU 0 [] [] [] [MemCopy.mkCopy 4096 4096 1] []) m
        = CheckReject
    ∧ check_getrandom i 4096 0 0 (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 1)]) m
        = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- AT the top of the address space, `buf = 2^47` with no bytes:
`__access_ok` admits the range (`addr <= limit - 0`), so 0 is accepted as
in range.  One byte past it, `__access_ok` refuses the range and
`import_ubuf` answers -EFAULT (lib/iov_iter.c:1437-1438): -EFAULT is
accepted there, the 0 an arm without the range test would answer is
refused, and -EINTR — the wait precedes the import — is accepted still.
The top is the Sv48 `TASK_SIZE` the run declares (at v6.18.46
arch/riscv defines no `TASK_SIZE_MAX`, so access_ok.h:15-17 falls back
to it).  The 0 at the top is the answer of every process not at
PMLEN 16: at PMLEN 0, of a process that has not enabled pointer
masking, the closed world `check_getrandom`'s docstring argues and
`bugs/access-okb-closed-world.md` records, and at PMLEN 7, which
`set_tagged_addr_ctrl` (arch/riscv/kernel/process.c:309-311, Linux
v6.18.46) chooses for an enabling request of 1 to 7 where the harts
support it.  riscv's `access_ok` under CONFIG_RISCV_ISA_SUPM
(arch/riscv/include/asm/uaccess.h:42, Linux v6.18.46) range-tests the
untagged address, which `__untagged_addr_remote`
(arch/riscv/include/asm/uaccess.h:23, Linux v6.18.46) computes as
`(long)(addr << pmlen) >> pmlen`: at PMLEN 7 that leaves 2^47
unchanged, and at PMLEN 16 it makes 2^47 0xffff800000000000, which the
test refuses.  One byte past the top the verdict is the same at every
PMLEN.  The refused
0 is the model's v6.18.46 answer and not the
supported set's: the mainline kernels read before v5.19 — v4.17, v5.17
and v5.18 — answer 0 there, as do v5.15.40 and v5.15.43, stable
releases cut before the rewritten random.c reached their line, the
priority-1 residual `bugs/getrandom-zero-length-refuses-the-pre-v5-19-zero.md`
records and the spec's own pin `zero_length_past_the_top_zero_rejected`
carries.  Not every pre-v5.19 kernel answers 0: the stable releases
that took the rewrite range-test the empty range as v6.18.46 does — at
v5.15.44 `getrandom` imports the buffer with `import_single_range`
(line 1246 of that release's random.c), whose `access_ok` test runs at
every length, 0 included (line 2025 of its iov_iter.c, 2013 at
v5.15.50, 2020 at v5.15.170 and 1585 at v4.19.325).  The riscv
`TASK_SIZE_MAX = LONG_MAX` window that also answered 0 is argued away as
a kernel bug in `Checks/Cases/Uaccess.lean`.
kernel: lib/iov_iter.c:import_ubuf; include/asm-generic/access_ok.h:__access_ok; drivers/char/random.c:getrandom,get_random_bytes_user,wait_for_random_bytes; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem check_getrandom_zero_length_range_verdict (i : SyscallInput) (m : Model) :
    check_getrandom i (Z_to_bv 64 (2 ^ 47)) 0 0 (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_getrandom i (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 (mkEffect (errno_ret EFAULT) [] []) m
        = CheckOk m []
    ∧ check_getrandom i (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 (mkEffect 0 [] []) m = CheckReject
    ∧ check_getrandom i (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 (mkEffect (errno_ret EINTR) [] []) m
        = CheckOk m [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- GRND_NONBLOCK DOES NOT MOVE THE ZERO-BYTE RANGE VERDICT: under flags 1,
one byte past the top -EFAULT is accepted and the 0 refused, at the top
itself the 0 is accepted, and in range -EFAULT is refused — the verdicts
`check_getrandom_zero_length_range_verdict` and
`check_getrandom_zero_length_rejects_the_lies` give at flags 0.  These
are three points; `check_getrandom_nonblock_is_the_plain_call` above
carries every flags-0 verdict to the flag.  With
the pool ready, the `!crng_ready()` gate of `getrandom`
(drivers/char/random.c:1400, Linux v6.18.46) is not entered and nothing
after it reads the flag, so the request reaches the import at :1408:
`import_ubuf` (lib/iov_iter.c:1437-1438, Linux v6.18.46) answers -EFAULT
when its range test fails, and otherwise builds an empty iterator and
returns 0 (:1440-1441); `getrandom` then returns what
`get_random_bytes_user` answers for that iterator
(drivers/char/random.c:1411, Linux v6.18.46), which is 0 (:440-441).
The range test admits the top itself: `__access_ok`
(include/asm-generic/access_ok.h:40, Linux v6.18.46) is
`(size <= limit) && (addr <= (limit - size))`, which at `size` 0 is
`addr <= limit`, and the top, `limit`, is the Sv48 `TASK_SIZE` the run
declares, 2^47 (`TASK_SIZE_64`, arch/riscv/include/asm/pgtable.h:1081,
Linux v6.18.46).  As at flags 0, the 0 at the top is the answer of
every process not at PMLEN 16
(`check_getrandom_zero_length_range_verdict` says why).  The refused 0
past the top is the
model's v6.18.46 answer and not the supported set's.  With the pool
ready, GRND_NONBLOCK passes the `crng_ready` test there as flags 0 does
(drivers/char/random.c's :2021-2023 at v4.17, :1919-1921 at v5.17,
:1482-1486 at v5.18), and those three kernels run no range test on a
zero-length request.  At v4.17 `getrandom` hands it to `urandom_read`
(:2028; its body is :1857-1877) and at v5.17 to `urandom_read_nowarn`
(:1926; its body is :1727-1736), and each hands it to
`extract_crng_user`, whose loop is `while (nbytes)`
(drivers/char/random.c:1035 at v4.17, :1043 at v5.17); at v5.18
`get_random_bytes_user` opens with `if (!nbytes) return 0;`
(drivers/char/random.c:537-538 at v5.18).  So they answer 0 there, the
priority-1 residual `bugs/getrandom-zero-length-refuses-the-pre-v5-19-zero.md`
records and `check_getrandom_zero_length_range_verdict` carries for
flags 0.
kernel: drivers/char/random.c:getrandom,crng_ready,get_random_bytes_user; lib/iov_iter.c:import_ubuf; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_getrandom_nonblock_zero_length_range_verdict (i : SyscallInput) (m : Model) :
    check_getrandom i (Z_to_bv 64 (2 ^ 47 + 1)) 0 1 (mkEffect (errno_ret EFAULT) [] []) m
        = CheckOk m []
    ∧ check_getrandom i (Z_to_bv 64 (2 ^ 47 + 1)) 0 1 (mkEffect 0 [] []) m = CheckReject
    ∧ check_getrandom i (Z_to_bv 64 (2 ^ 47)) 0 1 (mkEffect 0 [] []) m = CheckOk m []
    ∧ check_getrandom i 4096 0 1 (mkEffect (errno_ret EFAULT) [] []) m = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

end ZeroLength

section SmallRequestLies

/-! ## The small request: the lies from outside

Beyond Rocq's three shapes, the answers a lying kernel could report on a
sixteen-byte request and the checker must refuse: each differs from the
one admissible effect in a component the checker tests. -/

/-- A nonzero request never succeeds with nothing delivered: the bare 0
and the empty write entry are refused (`ret ? ret : -EFAULT`, :481).
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_small_request_rejects_nothing_delivered :
    check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect 0 [] []) getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect 0 [(4096, [])] []) getrandom_model
        = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- THE RETURN IS THE DELIVERED LENGTH, WHOLE: a return of 2 beside one
byte, the count with its high word set beside the full delivery, the
whole delivery beside a return of 15, and the REQUEST's count beside a
five-byte write are each refused — the last separates "the return is
the delivered length" from "the return is the request", which every
other lie here leaves equal.  That last refusal is the model's effect
convention, not a kernel line: the zone's bytes past the fifth already
hold 0, so the five-byte entry leaves both memory views and the model as an
accepted sixteen-byte delivery ending in eleven zero bytes does, and it
is refused because a delivery's one entry holds every byte the return
counts.  No `int` carries the count:
`get_random_bytes_user` keeps it in a `size_t` (drivers/char/random.c:438,
Linux v6.18.46) and returns it as its `ssize_t` (:434, :481), and
`getrandom` returns that unchanged (:1411) — its own `int ret` (:1388)
is returned only as the errno of :1403-1405 or :1408-1410 — from the
`long` function riscv's `__SYSCALL_DEFINEx` makes of its body
(arch/riscv/include/asm/syscall_wrapper.h:85 and :97, Linux v6.18.46;
riscv selects ARCH_HAS_SYSCALL_WRAPPER at arch/riscv/Kconfig:54, so the
generic wrapper in include/linux/syscalls.h is not the one built).
`syscall_handler` stores that `long` whole
(arch/riscv/include/asm/syscall.h:112, Linux v6.18.46), so 16 in a0 is
0x0000000000000010 and never 0xffffffff00000010.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; arch/riscv/include/asm/syscall.h:syscall_handler@v6.18.46 -/
theorem check_getrandom_small_request_rejects_a_return_that_disagrees :
    check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect 2 [(4096, some_bytes 1)] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 16) 4096 16 0
        (mkEffect 18446744069414584336 [(4096, some_bytes 16)] []) getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect 15 [(4096, some_bytes 16)] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect 16 [(4096, some_bytes 5)] [])
        getrandom_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- THE DELIVERY LANDS AT `ubuf`, IN ONE ENTRY: a write at 4097, and one
split across two entries, are refused.  The first is the kernel's: the
one `copy_to_iter` (:456) fills the destination `import_ubuf` made of
`ubuf` (:1408).  The second is the model's effect convention, not a
kernel line: the two adjacent entries write the bytes the one entry
does, and a syscall's delivery is ONE entry `(base, bytes)`, the shape
`delivered_writes` in `Sys/Uaccess.lean` states and the tracer records
— as `check_getrandom_large_request_rejects_the_remaining_lies` says of
the same lie at 300 bytes.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user; lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem check_getrandom_small_request_rejects_a_misplaced_or_split_delivery :
    check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect 16 [(4097, some_bytes 16)] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 16) 4096 16 0
        (mkEffect 16 [(4096, some_bytes 8), (4104, some_bytes 8)] []) getrandom_model
        = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- No memory ledger rides along with the delivery: a zero-fill range, an
unmap range, a copy and a copy-in beside it are each refused, all four
by the model's effect convention, not by a kernel line.  Each leaves
both memory views and the model as the delivery alone does: `apply_effect` in
`Run.lean` applies the writes last, so the delivery writes over the
zero-filled and the unmapped byte at 4096; the copy, of the buffer onto
itself, reads the snapshot taken before the effect, so it puts back
each byte it covers; and the copy-in names the one page the write
already names (`syscall_effect_accesses` in `State/Backing.lean`).
kernel: drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_small_request_rejects_other_ledgers :
    check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect 16 [(4096, some_bytes 16)] [(4096, 1)])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 16) 4096 16 0
        (SyscallEffect.mkEffectU 16 [(4096, some_bytes 16)] [] [(4096, 1)] [] []) getrandom_model
        = CheckReject
    ∧ check_getrandom (getrandom_call 16) 4096 16 0
        (SyscallEffect.mkEffectU 16 [(4096, some_bytes 16)] [] [] [MemCopy.mkCopy 4096 4096 16] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 16) 4096 16 0
        (SyscallEffect.mkEffectU 16 [(4096, some_bytes 16)] [] [] [] [(4096, 16)]) getrandom_model
        = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The errnos a small request never answers: -EAGAIN (no pool state
answers it at flags 0: :1401-1402 answers it only under GRND_NONBLOCK,
and the wait an unready pool enters instead, `wait_for_random_bytes`
at :136-147, answers 0 or -ERESTARTSYS), -EFAULT (the walk found the
destination writable, so `copy_to_iter` does not fault and :481 has a
count to return), and -EINVAL (the flag gate passed, :1390-1391 and
:1397-1398 are behind it);
and two shapes of the one errno a large request may answer: the low word
of -EINTR, 0xfffffffc, bare (the register holds the `long` whole,
arch/riscv/include/asm/syscall.h:112), and -EINTR beside the full
delivery (the wait returns before the import, :1403-1405 before :1408;
the -EINTR is `arch_do_signal_or_restart`'s, arch/riscv/kernel/signal.c:438-443).
kernel: drivers/char/random.c:getrandom,crng_ready,get_random_bytes_user,wait_for_random_bytes; arch/riscv/include/asm/syscall.h:syscall_handler; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem check_getrandom_small_request_rejects_other_errnos :
    check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect (errno_ret EAGAIN) [] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect (errno_ret EFAULT) [] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect (errno_ret EINVAL) [] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 16) 4096 16 0 (mkEffect 4294967292 [] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 16) 4096 16 0
        (mkEffect (errno_ret EINTR) [(4096, some_bytes 16)] []) getrandom_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- A one-byte walk of the zone, for the smallest request.
model: the byte walk over `getrandom_dest`, evaluated -/
theorem zone_walk_4096_1 : read_bytes_map getrandom_dest 4096 1 = some (List.replicate 1 0) := by
  decide +kernel

/-- THE SMALLEST NONZERO REQUEST IS A SMALL REQUEST, not the zero-byte
arm's: one byte is delivered in full (:455-458; `ret ? ret : -EFAULT` at
:481 returns the 1), and the bare 0 the zero-byte arm accepts is refused
here.  This is the pin on the `w_is0` split itself — every other pin
sits at 0 or at sixteen bytes and above.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_one_byte_is_a_small_request :
    check_getrandom (getrandom_call 1) 4096 1 0 (mkEffect 1 [(4096, some_bytes 1)] [])
        getrandom_model = CheckOk getrandom_model []
    ∧ check_getrandom (getrandom_call 1) 4096 1 0 (mkEffect 0 [] []) getrandom_model
        = CheckReject := by
  refine ⟨?_, ?_⟩ <;>
    simp +decide only [check_getrandom, zone_walk_4096_1, sys_simp, ↓reduceIte]

end SmallRequestLies

section LargeRequestLies

/-! ## The large request: the lies from outside

Beyond Rocq's four accepted shapes and its refused bare 0. -/

/-- The interrupt carries no data, so -EINTR beside one byte is refused:
`extract_crng_user`, whose -ERESTARTSYS is a large request's -EINTR on
the kernels that carry it, answers it only while its count is 0, on the
loop's first pass and before its first `copy_to_user`; from the second
pass on it breaks with the count instead (drivers/char/random.c:1036-1047
at v4.17).  The wait an unready pool adds returns before the buffer is
imported, too (:1403-1405 before :1408 at v6.18.46).  And nothing above
the request is delivered, so 301 of 300 is refused.  riscv makes -EINTR
of the -ERESTARTSYS for a handler without SA_RESTART, as v6.18.46's
`arch_do_signal_or_restart` does (arch/riscv/kernel/signal.c:438-443).
kernel: drivers/char/random.c:getrandom,get_random_bytes_user; lib/iov_iter.c:import_ubuf; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem check_getrandom_large_request_rejects_the_interrupt_with_data_and_over_delivery :
    check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect (errno_ret EINTR) [(4096, some_bytes 1)] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect 301 [(4096, some_bytes 301)] [])
        getrandom_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The empty write entry, the return that disagrees with the delivered
length (the effect convention's refusal, not a kernel line's, as on a
small one: the zone's sixth byte already holds the 0 an accepted
six-byte delivery may end in), the misplaced delivery, the delivery
split in two (the kernel
copies block by block, :465, into one contiguous run from `ubuf`; that
a syscall's delivery is ONE entry `(base, bytes)` is the effect
convention `delivered_writes` in `Sys/Uaccess.lean` states and the
tracer records, so two adjacent entries are the harness's own lie) and the
errnos a large request never answers (-EAGAIN, -EFAULT, and -EINVAL past
the flag gate) are refused as on a small one; and the return is the
whole register's — the low word of -EINTR, 0xfffffffc, is refused where
-EINTR is accepted, and 2^32 + 5 beside five bytes where 5 is.
kernel: drivers/char/random.c:getrandom,crng_ready,get_random_bytes_user; arch/riscv/include/asm/syscall.h:syscall_handler@v6.18.46 -/
theorem check_getrandom_large_request_rejects_the_remaining_lies :
    check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect 0 [(4096, [])] []) getrandom_model
        = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect 6 [(4096, some_bytes 5)] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect 5 [(4100, some_bytes 5)] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0
        (mkEffect 10 [(4096, some_bytes 5), (4101, some_bytes 5)] []) getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect (errno_ret EAGAIN) [] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect (errno_ret EFAULT) [] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect (errno_ret EINVAL) [] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect 4294967292 [] []) getrandom_model
        = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect 4294967301 [(4096, some_bytes 5)] [])
        getrandom_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- No ledger rides along with a large delivery or with the interrupt: a
zero-fill, an unmap, a copy and a copy-in beside five bytes of 300, and
beside the bare -EINTR, are each refused.  `get_random_bytes_user` copies
into the buffer (:465) and touches nothing else, and the interrupt,
`extract_crng_user`'s on the kernels that carry it, comes before that
function's first copy, and its loop touches no memory of the process
but the buffer (drivers/char/random.c:1035-1055 at v4.17).  Seven of
the eight are refused by the model's effect convention, not by a kernel
line, each leaving both memory views and the model as the outcome
without it does: in every state, the four beside the five bytes, for
the reasons `check_getrandom_small_request_rejects_other_ledgers` gives,
and the copy of the byte at 4096 onto itself beside -EINTR; and on this
fixture, though not on every input and model, the zero-fill beside
-EINTR, of a byte both views of the input already hold as 0, and the
copy-in beside it, on a model with no lazily backed page.  Which of
the two refuses the eighth, the unmap beside -EINTR, is a fact of the
machine state behind the fixture, not of the fixture
(`check_getrandom_zero_length_rejects_other_ledgers` gives the rule).  The
sixteen-byte pin of these four lies is
`check_getrandom_small_request_rejects_other_ledgers`; this one is here
so that a large arm matching `mkEffectU r ws _ _ _ _` is refused too.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem check_getrandom_large_request_rejects_other_ledgers :
    check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect 5 [(4096, some_bytes 5)] [(4096, 1)])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0
        (SyscallEffect.mkEffectU 5 [(4096, some_bytes 5)] [] [(4096, 1)] [] []) getrandom_model
        = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0
        (SyscallEffect.mkEffectU 5 [(4096, some_bytes 5)] [] [] [MemCopy.mkCopy 4096 4096 5] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0
        (SyscallEffect.mkEffectU 5 [(4096, some_bytes 5)] [] [] [] [(4096, 5)]) getrandom_model
        = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0 (mkEffect (errno_ret EINTR) [] [(4096, 1)])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0
        (SyscallEffect.mkEffectU (errno_ret EINTR) [] [] [(4096, 1)] [] []) getrandom_model
        = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0
        (SyscallEffect.mkEffectU (errno_ret EINTR) [] [] [] [MemCopy.mkCopy 4096 4096 1] [])
        getrandom_model = CheckReject
    ∧ check_getrandom (getrandom_call 300) 4096 300 0
        (SyscallEffect.mkEffectU (errno_ret EINTR) [] [] [] [] [(4096, 1)]) getrandom_model
        = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

end LargeRequestLies

section Witness

/-! ## The witness

`getrandom_witness`'s `_ok` lemma says the spec admits what it names;
these pins say WHAT it names, on the fixtures, and that the checker
accepts it. -/

/-- A small request: the witness delivers `buflen` zero bytes at `buf`
and returns their length — the one shape the spec admits, with the
environment's bytes fixed at 0 (any list of the right length is
admissible: :455-458 copies the key material for a request of at most 32
bytes, and the loop at :460-476 whatever the block function produced for
a longer one).  Spelled as the witness spells it, at 16 and at the bound.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem getrandom_witness_small_request_is_the_full_delivery :
    getrandom_witness 4096 16 0 (getrandom_call 16) getrandom_model
      = Ok (mkEffect (len_word (List.replicate 16 (Z_to_bv 8 0)))
                     [(4096, List.replicate 16 (Z_to_bv 8 0))] []) getrandom_model []
    ∧ getrandom_witness 4096 256 0 (getrandom_call 256) getrandom_model
      = Ok (mkEffect (len_word (List.replicate 256 (Z_to_bv 8 0)))
                     [(4096, List.replicate 256 (Z_to_bv 8 0))] []) getrandom_model [] := by
  refine ⟨?_, ?_⟩ <;> witness_norm

/-- ... and that return IS the length: 16 and 256 as words, read off
`List.length_replicate` rather than by walking the list.
model: the fixture list's `len_word`, through `List.length_replicate` -/
theorem getrandom_witness_delivered_length_is_the_count :
    len_word (List.replicate 16 (Z_to_bv 8 0)) = 16
    ∧ len_word (List.replicate 256 (Z_to_bv 8 0)) = 256 := by
  refine ⟨?_, ?_⟩ <;> (unfold len_word; simp only [List.length_replicate]; decide)

/-- Every other modeled request is the interrupt: the first large
request (257), Rocq's 300, and the zero-byte request in range and past
the top.  At 257 and 300 bytes the -EINTR is `extract_crng_user`'s, on
the kernels
`check_getrandom_large_request_accepts_the_short_count_and_the_interrupt`
names.  At zero bytes it is the wait's, on an unready pool — the spec's
width under the seeded-pool premise — and the wait is interrupted at
:1403-1405, before the buffer is imported at :1408, so -EINTR is
admitted whatever the range verdict and the witness need not decide the
range.
kernel: drivers/char/random.c:getrandom; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem getrandom_witness_other_requests_are_the_interrupt (i : SyscallInput) :
    getrandom_witness 4096 257 0 (getrandom_call 257) getrandom_model
      = Ok (mkEffect (errno_ret EINTR) [] []) getrandom_model []
    ∧ getrandom_witness 4096 300 0 (getrandom_call 300) getrandom_model
      = Ok (mkEffect (errno_ret EINTR) [] []) getrandom_model []
    ∧ getrandom_witness 4096 0 0 i getrandom_model
      = Ok (mkEffect (errno_ret EINTR) [] []) getrandom_model []
    ∧ getrandom_witness (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 i getrandom_model
      = Ok (mkEffect (errno_ret EINTR) [] []) getrandom_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- The witness declines where the spec declines, in the spec's order: a
flag word outside {0, GRND_NONBLOCK} (2, the unknown bit 256, and 2^32,
whose low half is 0), a request over the model's bound, and a
destination the writable view does not hold — half inside the zone,
wholly outside it, and the zone as the readable view alone.
kernel: drivers/char/random.c:getrandom; lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem getrandom_witness_declines_where_the_spec_declines (i : SyscallInput) (buf cap : word)
    (m : Model) :
    getrandom_witness buf cap 2 i m = Unmodeled
    ∧ getrandom_witness buf cap 256 i m = Unmodeled
    ∧ getrandom_witness buf cap (Z_to_bv 64 (2 ^ 32)) i m = Unmodeled
    ∧ getrandom_witness 4096 131073 0 i m = Unmodeled
    ∧ getrandom_witness 4600 16 0 (getrandom_call 16) getrandom_model = Unmodeled
    ∧ getrandom_witness 8192 16 0 (getrandom_call 16) getrandom_model = Unmodeled
    ∧ getrandom_witness 4096 16 0 (getrandom_call_ro 16) getrandom_model = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- UNDER GRND_NONBLOCK THE WITNESS NAMES WHAT IT NAMES AT FLAGS 0, on
every call: `getrandom_witness` reads `flags` at its first gate and
nowhere after it, as `check_getrandom` does, so every outcome the pins
above name at flags 0 — the delivery, the interrupt, and the declines of
the bound and of the destination — it names under the flag too.  A fact
about the witness's definition, as
`check_getrandom_nonblock_is_the_plain_call` is about the checker's.
model: `getrandom_witness` reads `flags` at its first gate only, which 0 and GRND_NONBLOCK both pass -/
theorem getrandom_witness_nonblock_is_the_plain_call (buf buflen : word) (i : SyscallInput)
    (m : Model) :
    getrandom_witness buf buflen 1 i m = getrandom_witness buf buflen 0 i m := by
  witness_norm

/-- THE CHECKER ACCEPTS WHAT THE WITNESS NAMES, on every call: an `Ok`
the witness names is `CheckOk` with the same post-model and events, and
an `Unmodeled` it names is `CheckUnmodeled` on every effect.  Both are
the witness's `_ok` lemma read through the checker's completeness, so
the two sides of this file agree by proof and not by inspection.
model: `getrandom_witness_ok` through `check_getrandom_complete_ok` and `check_getrandom_complete_unmodeled` -/
theorem check_getrandom_accepts_the_witness (buf buflen flags : word) (i : SyscallInput)
    (m : Model) :
    (∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
        getrandom_witness buf buflen flags i m = Ok eff m' evs →
        check_getrandom i buf buflen flags eff m = CheckOk m' evs)
    ∧ (∀ eff : SyscallEffect,
        getrandom_witness buf buflen flags i m = Unmodeled →
        check_getrandom i buf buflen flags eff m = CheckUnmodeled) := by
  refine ⟨?_, ?_⟩
  · intro eff m' evs h
    have hw := getrandom_witness_ok buf buflen flags i m
    rw [h] at hw
    exact check_getrandom_complete_ok i buf buflen flags eff m m' evs hw
  · intro eff h
    have hw := getrandom_witness_ok buf buflen flags i m
    rw [h] at hw
    exact check_getrandom_complete_unmodeled i buf buflen flags m eff hw

/-- ... and on the fixture, by evaluation rather than by the lemma: the
sixteen zero bytes the witness names are accepted.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem check_getrandom_accepts_the_witness_delivery :
    check_getrandom (getrandom_call 16) 4096 16 0
        (mkEffect 16 [(4096, List.replicate 16 (Z_to_bv 8 0))] []) getrandom_model
      = CheckOk getrandom_model [] := by
  check_norm

end Witness

-- lean-port sentinel: ticket V-Drivers-Char-Random appends below this line

section V_Drivers_Char_Random

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Drivers-Char-Random — `getrandom` over the real table

WHAT IS TWINNED HERE.  The `RocqExamples` section above states each Rocq
example on `check_getrandom` itself, because `checked_table` carried no
row for 278 when it was written, and the header leaves the restatement
through `check_syscall` to the registration.  This is the registration.
Each of the three examples
`theories/LinuxProcessSem/Checks/Cases/Drivers/Char/Random.v` states —
every one through `check_syscall`, closed by `check_eq` — is restated
here through the Lean `check_syscall`, over `checked_table` itself, at
Rocq's input `getrandom_call n` and Rocq's `getrandom_model`, under its
Rocq name with `_over_the_real_table` after it.  Each is proved by
computing the dispatch once (`check_syscall_getrandom_call`) and handing
the checker-level twin above the call it now receives, so the verdicts
are the ones `check_norm` computed there.

WHAT A PIN HERE ADDS to its checker-level twin is the ARM's claim: that
the lookup at 278 finds `arm_getrandom` rather than the dispatcher's own
decline, and that the arm hands the checker `a0`, `a1` and `a2`, whole.
The twins separate `a0` from `a1`: read the other way round,
`getrandom(4096, 16, 0)` walks 4096 bytes from address 16, which the
zone does not hold, so the full delivery the first twin accepts would be
declined.  The flag-word pins below separate `a2` from `a3`, and the
whole register from its low half; the buffer-and-length pins after them
do the same for `a0`, which every input the table is handed before them
carries as 4096, its own low half, and restate for `a1` what
`check_syscall_getrandom_call` below, stated for every length, already
fixes.

POLARITY follows the header's legend: here `model:` is on the table's
own contents and the zone walk, and `kernel:` on every verdict of the
table and outcome of its witness, `CheckUnmodeled` included. -/

/-- The lookup the dispatcher performs on a `getrandom_call`, computed
once: `in_sysno` is `278` whatever the length.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_getrandom_call (n : Int) :
    lookup_ca checked_table (bv_unsigned (getrandom_call n).in_sysno) = some arm_getrandom :=
  lookup_ca_checked_table_getrandom

/-- What the table hands the checker on a `getrandom_call`: the call
itself and its first three registers — 4096, the length and 0.
model: `check_syscall` through `arm_getrandom`, unfolded; the table's own
contents, not a kernel claim. -/
theorem check_syscall_getrandom_call (n : Int) (eff : SyscallEffect) (m : Model) :
    check_syscall (getrandom_call n) eff m
      = check_getrandom (getrandom_call n) 4096 (Z_to_bv 64 n) 0 eff m :=
  check_syscall_of_found _ _ _ _ (lookup_getrandom_call n)

/-! ### The three Rocq examples, through `check_syscall` -/

/-- `getrandom_small_request_is_delivered_in_full` over the real table:
sixteen bytes at 4096 with a return of sixteen is accepted, the model
unchanged and no event, and the short count, the bare -EINTR and the
over-delivery are refused on the same call.  `get_random_bytes_user`
(drivers/char/random.c:455-458, Linux v6.18.46) copies a request of at
most CHACHA_KEY_SIZE (32) bytes out of the key material at once, and
such a request never enters the loop whose `signal_pending` test
(:471-473) could cut it short; the -EINTR is the wait's (`wait_for_random_bytes`, :136-147) as
`arch_do_signal_or_restart` delivers it (arch/riscv/kernel/signal.c:438-443),
kept out of a small request on the seeded-pool premise
`bugs/getrandom-answers-rest-on-a-seeded-pool.md` records; seventeen
bytes is more than the iterator holds (`import_ubuf` sizes it at `len`,
lib/iov_iter.c:1440).
kernel: drivers/char/random.c:getrandom,get_random_bytes_user,wait_for_random_bytes; lib/iov_iter.c:import_ubuf; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem getrandom_small_request_is_delivered_in_full_over_the_real_table :
    check_syscall (getrandom_call 16) (mkEffect 16 [(4096, some_bytes 16)] []) getrandom_model
      = CheckOk getrandom_model []
    ∧ check_syscall (getrandom_call 16) (mkEffect 5 [(4096, some_bytes 5)] []) getrandom_model
      = CheckReject
    ∧ check_syscall (getrandom_call 16) (mkEffect (errno_ret EINTR) [] []) getrandom_model
      = CheckReject
    ∧ check_syscall (getrandom_call 16) (mkEffect 17 [(4096, some_bytes 17)] []) getrandom_model
      = CheckReject := by
  simp only [check_syscall_getrandom_call]
  exact ⟨check_getrandom_small_request_accepts_full_delivery,
    check_getrandom_small_request_rejects_short_count_interrupt_and_over_delivery⟩

/-- `getrandom_small_bound_is_inclusive` over the real table: 255 of 256
is refused, 256 of 256 is accepted, and 255 of 257 is accepted again —
the first request the checker judges as large, admitted by the spec's
`[1, buflen]` width as 5 of 300 is in the next pin, not by a kernel
line.  Above CHACHA_KEY_SIZE the loop at drivers/char/random.c:460-476
(Linux v6.18.46) lands a 64-byte block per `copy_to_iter` and breaks
when the count is exhausted (:467-468) before the page test at :471-473
can fire, so nothing but a fault, which the walk excludes, cuts 33..256
short.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem getrandom_small_bound_is_inclusive_over_the_real_table :
    check_syscall (getrandom_call 256) (mkEffect 255 [(4096, some_bytes 255)] [])
        getrandom_model = CheckReject
    ∧ check_syscall (getrandom_call 256) (mkEffect 256 [(4096, some_bytes 256)] [])
        getrandom_model = CheckOk getrandom_model []
    ∧ check_syscall (getrandom_call 257) (mkEffect 255 [(4096, some_bytes 255)] [])
        getrandom_model = CheckOk getrandom_model [] := by
  simp only [check_syscall_getrandom_call]
  exact check_getrandom_small_bound_is_inclusive

/-- `getrandom_large_request_still_admits_the_short_count` over the real
table: 300 of 300, 5 of 300 and the bare -EINTR are accepted, and the
bare 0 is refused.  The short count is the spec's declared width
`[1, buflen]`.  The -EINTR at 300 bytes is not a v6.18.46 answer:
`wait_for_random_bytes` runs before the length is read and is ruled out
here on the seeded-pool premise.  It is `extract_crng_user`'s, on the
kernels that still carry that function: mainline v4.17 through v5.17,
and the stable releases cut before the rewritten random.c reached their
line (v5.15.43 carries it; v5.15.44, v5.15.170 and v4.19.325 do not, nor
does mainline v5.18).  For `large_request = nbytes > 256` it tests
`signal_pending` whenever `need_resched()` holds, and returns
-ERESTARTSYS when nothing was copied yet
(drivers/char/random.c:1029-1062 at v4.17, :1037-1070 at v5.17), reached
from the getrandom syscall with `crng_ready` true through `urandom_read`
at v4.17 (:2028) and `urandom_read_nowarn` at v5.17 (:1926), and riscv's
`handle_signal` turns it into -EINTR when the handler has no SA_RESTART
(arch/riscv/kernel/signal.c:223-227 at v4.17, :248-252 at v5.17; v6.18.46
does the same in `arch_do_signal_or_restart`, :416-423 against :437-444).
At v6.18.46, a nonzero request never succeeds with nothing delivered:
`get_random_bytes_user` answers 0 only for an empty iterator
(drivers/char/random.c:440-441) and otherwise `ret ? ret : -EFAULT`
(drivers/char/random.c:481).
kernel: drivers/char/random.c:getrandom,get_random_bytes_user; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem getrandom_large_request_still_admits_the_short_count_over_the_real_table :
    check_syscall (getrandom_call 300) (mkEffect 300 [(4096, some_bytes 300)] [])
        getrandom_model = CheckOk getrandom_model []
    ∧ check_syscall (getrandom_call 300) (mkEffect 5 [(4096, some_bytes 5)] [])
        getrandom_model = CheckOk getrandom_model []
    ∧ check_syscall (getrandom_call 300) (mkEffect (errno_ret EINTR) [] []) getrandom_model
      = CheckOk getrandom_model []
    ∧ check_syscall (getrandom_call 300) (mkEffect 0 [] []) getrandom_model = CheckReject := by
  simp only [check_syscall_getrandom_call]
  obtain ⟨h300, h5, -, hintr⟩ :=
    check_getrandom_large_request_accepts_the_short_count_and_the_interrupt
  exact ⟨h300, h5, hintr, check_getrandom_large_request_rejects_the_bare_zero⟩

/-! ### The flag word is `a2`, whole

`getrandom_call` leaves every register past `a1` at 0, so no pin above
can tell which register the arm reads the flag word from, or how much of
it.  The fixture below sets `a2` and `a3` apart. -/

/-- One `getrandom(4096, 16, a2)` over the zone, with `a3` set beside
it: the register after the flag word, which a three-parameter syscall
never reads. -/
def getrandom_regs (a2 a3 : word) : SyscallInput :=
  SyscallInput.mkInput 278 [4096, 16, a2, a3, 0, 0] getrandom_dest getrandom_dest

/-- What the table hands the checker on a `getrandom_regs`: `a0`, `a1`
and `a2`, and not `a3`.
model: `check_syscall` through `arm_getrandom`, unfolded; the table's own
contents, not a kernel claim. -/
theorem check_syscall_getrandom_regs (a2 a3 : word) (eff : SyscallEffect) (m : Model) :
    check_syscall (getrandom_regs a2 a3) eff m
      = check_getrandom (getrandom_regs a2 a3) 4096 16 a2 eff m :=
  -- Through the arm's own unfold lemma: `check_syscall_of_found`
  -- alone against this statement is a type mismatch under Lean v4.34.0,
  -- although the projection and each `in_arg` against its literal are
  -- `rfl` one at a time.
  (check_syscall_of_found (getrandom_regs a2 a3) eff m arm_getrandom lookup_ca_checked_table_getrandom).trans
    (ca_check_arm_getrandom (getrandom_regs a2 a3) eff m)

/-- GRND_RANDOM (2) in `a2` is a flag word the spec declines, so the full
delivery is declined; the same bit in `a3` leaves `a2` at 0, and the full
delivery is accepted.  riscv64's wrapper hands `getrandom` `orig_a0`,
`a1` and `a2` (`SC_RISCV_REGS_TO_ARGS`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46) for the
three parameters of
`SYSCALL_DEFINE3(getrandom, char __user *, ubuf, size_t, len, unsigned int, flags)`
(drivers/char/random.c:1385, same version), so `flags` is `a2`, and an
arm reading `a3` would answer both calls the other way round.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem getrandom_flag_word_is_a2_over_the_real_table :
    check_syscall (getrandom_regs 2 0) (mkEffect 16 [(4096, some_bytes 16)] []) getrandom_model
      = CheckUnmodeled
    ∧ check_syscall (getrandom_regs 0 2) (mkEffect 16 [(4096, some_bytes 16)] []) getrandom_model
      = CheckOk getrandom_model [] := by
  simp only [check_syscall_getrandom_regs]
  -- `check_norm`'s pass, with the fixture unfolded so that the walk sees
  -- `getrandom_dest`: `getrandom_regs` carries no `sys_simp` equation.
  refine ⟨?_, ?_⟩ <;>
    (simp +decide only [check_getrandom, getrandom_regs, sys_simp, ↓reduceIte]; done)

/-- `a2` is read WHOLE: bit 32 alone is declined, for the full delivery
and for the -EINTR alike, where `flags`, an `unsigned int` narrowed from
`a2` through `__SC_CAST` (include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46), is 0 and
Linux delivers as at flags 0 — or answers the -EINTR
`arch_do_signal_or_restart` makes of an interrupted wait
(arch/riscv/kernel/signal.c:438-443).  That is the narrowing
`arm_getrandom`'s docstring names, pinned through the table: a decline
and not a `CheckReject` (for every effect, by
`check_getrandom_high_half_flags_decline` above, which this restates at
two), so a run whose program passed such a word would be declined rather
than misjudged.  An arm handing the checker the
low half alone would accept the delivery.
kernel: include/linux/syscalls.h:__SC_CAST; drivers/char/random.c:getrandom,get_random_bytes_user,wait_for_random_bytes; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem getrandom_high_half_flags_decline_over_the_real_table :
    check_syscall (getrandom_regs (Z_to_bv 64 (2 ^ 32)) 0) (mkEffect 16 [(4096, some_bytes 16)] [])
        getrandom_model = CheckUnmodeled
    ∧ check_syscall (getrandom_regs (Z_to_bv 64 (2 ^ 32)) 0) (mkEffect (errno_ret EINTR) [] [])
        getrandom_model = CheckUnmodeled := by
  simp only [check_syscall_getrandom_regs]
  exact ⟨check_getrandom_high_half_flags_decline _ _ _ _ _,
    check_getrandom_high_half_flags_decline _ _ _ _ _⟩

/-! ### The buffer and the length are `a0` and `a1`, whole

Every input above that reaches the arm, `getrandom_call n` and
`getrandom_regs`, carries 4096 in `a0`, its own low half, so no pin
above can tell whether the arm reads that register whole.  `a1` is held
whole already: `check_syscall_getrandom_call` is stated for every
length, and at 2^32 + 16, whose low half is 16, it hands the checker
the request `check_getrandom_over_the_bound_declines` declines, where an
arm reading the low half would accept the sixteen-byte delivery.  The
fixture below sets both registers apart, and states the `a1` half as a
verdict. -/

/-- One `getrandom(a0, a1, 0)` over the zone: the buffer and the length
registers set apart, the flag word at 0. -/
def getrandom_args (a0 a1 : word) : SyscallInput :=
  SyscallInput.mkInput 278 [a0, a1, 0, 0, 0, 0] getrandom_dest getrandom_dest

/-- 2^32 + 4096: the zone's first address, 4096, with bit 32 set — a word
outside the zone whose low half is 4096.  Named, so that the walk from
it is one rewrite. -/
def getrandom_buf_bit32 : word := Z_to_bv 64 (2 ^ 32 + 4096)

/-- A 16-byte walk from 2^32 + 4096, which the zone does not hold.
model: the byte walk over `getrandom_dest`, evaluated -/
theorem zone_walk_buf_bit32_16 :
    read_bytes_map getrandom_dest getrandom_buf_bit32 16 = none := by
  decide +kernel

/-- What the table hands the checker on a `getrandom_args`: `a0` and
`a1`, and the flag word's 0.
model: `check_syscall` through `arm_getrandom`, unfolded; the table's own
contents, not a kernel claim. -/
theorem check_syscall_getrandom_args (a0 a1 : word) (eff : SyscallEffect) (m : Model) :
    check_syscall (getrandom_args a0 a1) eff m
      = check_getrandom (getrandom_args a0 a1) a0 a1 0 eff m :=
  (check_syscall_of_found (getrandom_args a0 a1) eff m arm_getrandom lookup_ca_checked_table_getrandom).trans
    (ca_check_arm_getrandom (getrandom_args a0 a1) eff m)

/-- `a0` and `a1` are read WHOLE: sixteen bytes delivered at 4096 are
accepted from `getrandom(4096, 16, 0)`, and the same delivery is declined
with bit 32 set in the buffer register, or in the length register.
riscv64's wrapper hands `getrandom` `orig_a0` and `a1` as `ubuf` and
`len` (`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24,
Linux v6.18.46), a pointer and a size_t, which `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46) keeps 64
bits wide.  At 2^32 + 4096 the destination is one the writable view
does not hold, which the spec declines as Gate 3 declines 8192: Linux
would import it and fault on the copy with nothing landed, and
`get_random_bytes_user` (drivers/char/random.c:481) answers -EFAULT.  A
request of 2^32 + 16 bytes is over the model's bound, the second half of
`check_getrandom_over_the_bound_declines`, which this restates through
the table — as `check_syscall_getrandom_call` at that length already
does, since `getrandom_args 4096 (Z_to_bv 64 (2 ^ 32 + 16))` and
`getrandom_call (2 ^ 32 + 16)` unfold to the same input: the third
conjunct follows from those two pins and refuses no arm they let
through.  An arm handing the checker either low half would walk the
zone at 4096 for sixteen bytes and accept the delivery.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; include/linux/syscalls.h:__SC_CAST; lib/iov_iter.c:import_ubuf; drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem getrandom_buffer_and_length_are_a0_and_a1_whole_over_the_real_table :
    check_syscall (getrandom_args 4096 16) (mkEffect 16 [(4096, some_bytes 16)] [])
        getrandom_model = CheckOk getrandom_model []
    ∧ check_syscall (getrandom_args getrandom_buf_bit32 16)
        (mkEffect 16 [(4096, some_bytes 16)] []) getrandom_model = CheckUnmodeled
    ∧ check_syscall (getrandom_args 4096 (Z_to_bv 64 (2 ^ 32 + 16)))
        (mkEffect 16 [(4096, some_bytes 16)] []) getrandom_model = CheckUnmodeled := by
  simp only [check_syscall_getrandom_args]
  refine ⟨?_, ?_, (check_getrandom_over_the_bound_declines _ _ _).2⟩ <;>
    (simp +decide only [check_getrandom, getrandom_args, zone_walk_buf_bit32_16, sys_simp,
      ↓reduceIte]; done)

/-! ### The witness the table hands `receptive`

`syscall_spec_witness` dispatches over the same table, so the arm's
`ca_witness` is what it answers at 278; the witness pins above fix
`getrandom_witness` at bare words, these fix that the arm hands it the
same registers the checker gets. -/

/-- A small request through the table: the witness delivers sixteen zero
bytes at `a0` and returns their length.
kernel: drivers/char/random.c:getrandom,get_random_bytes_user@v6.18.46 -/
theorem getrandom_small_request_witnesses_the_full_delivery_over_the_real_table :
    syscall_spec_witness (getrandom_call 16) getrandom_model
      = Ok (mkEffect (len_word (List.replicate 16 (Z_to_bv 8 0)))
                     [(4096, List.replicate 16 (Z_to_bv 8 0))] []) getrandom_model [] := by
  show getrandom_witness 4096 (Z_to_bv 64 16) 0 (getrandom_call 16) getrandom_model = _
  exact getrandom_witness_small_request_is_the_full_delivery.1

/-- Bit 32 of `a2` through the table: the witness exhibits the decline,
as the checker does, and not the delivery the low half would earn.
kernel: include/linux/syscalls.h:__SC_CAST; drivers/char/random.c:getrandom@v6.18.46 -/
theorem getrandom_high_half_flags_witness_unmodeled_over_the_real_table :
    syscall_spec_witness (getrandom_regs (Z_to_bv 64 (2 ^ 32)) 0) getrandom_model = Unmodeled := by
  show getrandom_witness 4096 16 (Z_to_bv 64 (2 ^ 32)) (getrandom_regs (Z_to_bv 64 (2 ^ 32)) 0)
    getrandom_model = _
  exact (getrandom_witness_declines_where_the_spec_declines _ 4096 16 _).2.2.1

/-- `a0` and `a1` through the table: with bit 32 set in either, the
witness exhibits the decline, as the checker does, and not the delivery
the low half would earn.  In `a0` the decline is Gate 3's, of a
destination the writable view does not hold, and in `a1` it is the
model's bound, as
`getrandom_buffer_and_length_are_a0_and_a1_whole_over_the_real_table`
says.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; lib/iov_iter.c:import_ubuf; drivers/char/random.c:getrandom@v6.18.46 -/
theorem getrandom_buffer_and_length_witness_unmodeled_over_the_real_table :
    syscall_spec_witness (getrandom_args getrandom_buf_bit32 16) getrandom_model = Unmodeled
    ∧ syscall_spec_witness (getrandom_args 4096 (Z_to_bv 64 (2 ^ 32 + 16))) getrandom_model
      = Unmodeled := by
  refine ⟨?_, ?_⟩
  · show getrandom_witness getrandom_buf_bit32 16 0 (getrandom_args getrandom_buf_bit32 16)
      getrandom_model = _
    simp +decide only [getrandom_witness, getrandom_args, zone_walk_buf_bit32_16, sys_simp,
      ↓reduceIte]
  · show getrandom_witness 4096 (Z_to_bv 64 (2 ^ 32 + 16)) 0
      (getrandom_args 4096 (Z_to_bv 64 (2 ^ 32 + 16))) getrandom_model = _
    witness_norm

end V_Drivers_Char_Random

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Drivers.Char.Random
