-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Fs/EventFd.v
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.EventFd
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventFd
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Fs.EventFd — what the eventfd2 checker and witness answer, read off against Linux

Pins over `Checks.Sys.Fs.EventFd.check_eventfd2`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Fs/EventFd.v`, and over
`eventfd2_witness`, the twin of
`theories/LinuxProcessSem/Checks/Witness/Fs/EventFd.v`.  Not part of the
trusted specification: this file is QA on the checker, written to be
READ, and a claim in it is a claim about what the kernel does, with the
citation beside it, unless its evidence line is `model:` and says
otherwise.  Line numbers are Linux v6.18.46 (commit 1f99e9ab748f).

WHY THESE EXIST beside the four lemmas.  `check_eventfd2_sound_ok` and
its three companions relate the checker to `eventfd2_spec`, and a gate
misspelled the same way in both files closes every one of them; the
Rocq checker's own docstring says so.  What separates the pair from Linux
is a concrete answer from outside: offer the checker an effect a real
kernel could never produce and require `CheckReject`, offer the one it
does produce and require `CheckOk`.  Rocq does this in
`Checks/Cases/Fs/EventFd.v` through `check_syscall`.  The sections before
`V_pilot_Fs_EventFd` were written while `Checks/Sys/Table.lean`'s
`checked_table` carried no arm for 19, so they address `check_eventfd2`
and `eventfd2_witness` directly; `V_pilot_Fs_EventFd`, added with the arm's registration,
restates each Rocq example through `Checks/ExecutableSpecs.lean`'s
`check_syscall` over the real table.  The sections before it hold two
kinds of pin:
a bare flag word where the point is the gate, and the composition
`flag32 (in_arg (efd_in count flags) 1)` — argument ONE, low 32 bits —
where the point is the reading the arm applies before the checker
sees anything.  Read the second kind carefully: the composition is
evaluated BEFORE the checker, so those pins fix that the reading picks
the flag word and not the counter and narrows it to 32 bits, and that the
checker's answer on the narrowed word is the kernel's; they do not tie
the table's arm to that reading (the pins over the real table in
`V_pilot_Fs_EventFd` do), and a checker gating on the whole 64-bit word passes every
one of them — which `the_checker_itself_reads_the_whole_word` below pins,
so that where the narrowing lives is fixed from both sides.  Through the
spec's dispatcher, the spec twin's `swapped_arguments_rejected` and
`full_register_einval_rejected` (Lean pins on `Specs.syscall_spec` in
`Checks/Cases/Fs/EventFd.lean`; Rocq carries the points in
`eventfd2_counter_is_not_judged` and `eventfd2_narrows_the_flag_word`)
carry the same points at the spec level; their restatement through
`check_syscall` is `eventfd2_counter_is_not_judged_over_the_real_table`
and `eventfd2_narrows_the_flag_word_over_the_real_table`, in
`V_pilot_Fs_EventFd`.  The pins are stated at any
`Model`, where Rocq fixes `eventfd_model`: the checker never reads the
model, and a pin that holds at every model says so more sharply than one
that holds at one.

WHY THIS FILE IS NOT `Checks/Cases/Fs/EventFd.lean`.  That file is the
spec's mutation twin: `tools/lean_mutate.py` compiles each mutant of
`Sys/Fs/EventFd.lean` against it and counts a mutant killed only when THAT
file fails to build.  Were the checker in its import closure, the checker
module would be compiled first, and the four lemmas of
`Checks/Sys/Fs/EventFd.lean` relate the checker to the spec, so a
gate-changing spec mutant would fail there — recorded as STILLBORN rather
than as a kill by a spec pin — before a spec pin was read.  This file
imports the spec twin and no source module imports this file (only the
audit root the lakefile generates), so the checker never enters the spec
twin's closure and a change to THIS file re-keys nothing.  The twin's own
header is inside its closure, though: a prose edit there — its `HOW THESE
ARE STATED` paragraph, which names this file, or the cases-parity mapping
of Rocq's examples onto its theorems — re-keys the committed
`tools/lean_mutation/scores/Fs.EventFd.json` and costs a re-sweep of the
spec's mutants although no proof changed, which is why that cache moves
with a header edit to the twin.

The Rocq check file's examples are here as separately named
theorems, one per conjunct, so that a failure names the conjunct; beside
them sit the lies the probe tells with `--mutate`, the words it sends
that no Rocq conjunct does, and the checker's own whole-word gating.
The probe that meets these answers in a booted kernel,
testing/syscall-check/tests/eventfd2.c, is recorded against the Rocq
checker.  The evidence line is `kernel:` on every pin about the kernel's
answer, positive and negative alike — a `CheckReject` says the kernel
does not give the offered answer, and its citation is where the kernel's
own answer is decided — and `model:` on a pin that is about the checker
and not about Linux, such as one whose -EINVAL at a bit above 31 is the
checker's contract with the reading and the opposite of what Linux
answers at that register word; the `model:` line itself says which.  Every
equality but the frame instance is closed by `rfl` — or, for the pins
quantified over a bit position, by a case split on the position with
`rfl` in each case, and for the pins of `V_Fs_EventFd`, stated over a
free input, by a `simp only` rewriting the dispatch with their
hypotheses, then `rfl` where a goal is left:
`Model` has no `DecidableEq`, so `decide` is unavailable, and the checker
on a closed word reduces to a constructor by evaluation alone, reading no
field of the quantified model.

WHAT THE KERNEL SAYS, once.  `do_eventfd` (fs/eventfd.c:379-421, Linux
v6.18.46, commit 1f99e9ab748f) refuses a flag word with any bit outside
`EFD_FLAGS_SET` — `EFD_SEMAPHORE | EFD_CLOEXEC | EFD_NONBLOCK`, which is
`O_CLOEXEC | O_NONBLOCK | 1` — with -EINVAL at lines 390-391, before the
allocation at 393 (the -ENOMEM), before `get_unused_fd_flags` at 405 (the
-EMFILE `alloc_fd` raises, fs/file.c at the same Linux v6.18.46), and before
`anon_inode_getfile_fmode` at 409 (fs/anon_inodes.c).  Past the gate it
returns a descriptor to an object the model has no kind for, or one of
the allocation errnos — -ENOMEM, -EMFILE, -ENFILE — that only the path
past the gate can raise, under the premise the spec twin's header states,
that no LSM `file_alloc_security` hook returns nonzero (`init_file`,
fs/file_table.c:180-183, Linux v6.18.46, forwards whatever one returns);
the model judges neither, which is the decline.  The flag argument is
`int flags` in `SYSCALL_DEFINE2(eventfd2,
unsigned int, count, int, flags)` at line 423, so the arm reads its low 32
bits, and the counter is `count`, argument zero, which the gate never
reads. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.EventFd

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventFd
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.EventFd
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventFd

variable (m : Model)

section DroppedBits

/-! ## Rocq `eventfd2_dropped_flag_bits_are_einval`: one bit outside the mask, at four positions

Bit 1 sits between `EFD_SEMAPHORE` (bit 0) and `O_NONBLOCK` (bit 11);
bit 10 is just below `O_NONBLOCK`; bit 15 is between it and `O_CLOEXEC`
(bit 19); bit 20 is just above.  Each is refused with -EINVAL and a
descriptor for each is a lie. -/

/-- Bit 1 alone: -EINVAL, model untouched, no event.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_1_einval_accepted :
    check_eventfd2 2 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- Bit 1 alone, a descriptor: refused.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_1_descriptor_rejected :
    check_eventfd2 2 (mkEffect 3 [] []) m = CheckReject := rfl

/-- Bit 10 alone: -EINVAL.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_10_einval_accepted :
    check_eventfd2 1024 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- Bit 10 alone, a descriptor: refused.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_10_descriptor_rejected :
    check_eventfd2 1024 (mkEffect 3 [] []) m = CheckReject := rfl

/-- Bit 15 alone: -EINVAL.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_15_einval_accepted :
    check_eventfd2 32768 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- Bit 15 alone, a descriptor: refused.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_15_descriptor_rejected :
    check_eventfd2 32768 (mkEffect 3 [] []) m = CheckReject := rfl

/-- Bit 20 alone: -EINVAL.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_20_einval_accepted :
    check_eventfd2 1048576 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- Bit 20 alone, a descriptor: refused.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_20_descriptor_rejected :
    check_eventfd2 1048576 (mkEffect 3 [] []) m = CheckReject := rfl

/-! The two words below are the probe's, not Rocq's: no conjunct of
`eventfd2_dropped_flag_bits_are_einval` sets a mask bit beside the bad
one or every low bit at once, and testing/syscall-check/tests/eventfd2.c's
`einval` case sends exactly these (the second as both `-1` and
`0xFFFFFFFF`). -/

/-- The whole mask beside bit 1, 526337 + 2: every accepted bit set does not excuse the one that is not.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem mask_plus_bad_bit_einval_accepted :
    check_eventfd2 (526337 + 2) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- The same word with a descriptor: refused.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem mask_plus_bad_bit_descriptor_rejected :
    check_eventfd2 (526337 + 2) (mkEffect 3 [] []) m = CheckReject := rfl

/-- Every low bit set, `0xffffffff` — the word both the probe's `-1` and
its `0xFFFFFFFF` arrive as once `int flags` has narrowed them: -EINVAL.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem all_ones_32bit_einval_accepted :
    check_eventfd2 4294967295 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- ...and a descriptor for it is a lie.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem all_ones_32bit_descriptor_rejected :
    check_eventfd2 4294967295 (mkEffect 3 [] []) m = CheckReject := rfl

end DroppedBits

section OtherLies

/-! ## Lies about the refused word that Rocq's probe tells with `--mutate`

`eventfd2.c`'s reject cases offer the Rocq checker a descriptor for a
refused word — each `--mutate eventfd2:ret=<fd>` line of the probe — and
the spec-side pins of `Checks/Cases/Fs/EventFd.lean` refute the errnos
`do_eventfd` can only reach past the gate.  The checker must give the same answers
executably, and must refuse an -EINVAL that arrives beside a ledger
entry, which `check_ret_only` alone is responsible for. -/

/-- Descriptor 0 for a refused word: as much a lie as descriptor 3.  The
`--mutate eventfd2:ret=0` case of the probe.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_1_fd0_rejected :
    check_eventfd2 2 (mkEffect 0 [] []) m = CheckReject := rfl

/-- -ENOMEM for bit 1 is refused: every allocation that could
raise it — the context's `kmalloc` at fs/eventfd.c:393 first, then the
descriptor table's and the file's behind lines 405 and 409 — is below
the gate.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_1_enomem_rejected :
    check_eventfd2 2 (mkEffect (errno_ret ENOMEM) [] []) m = CheckReject := rfl

/-- -EMFILE for bit 1 is refused: `get_unused_fd_flags` runs at
fs/eventfd.c:405, below the gate, and `alloc_fd` (fs/file.c:591-593, the
RLIMIT_NOFILE test) and the `expand_files` it calls decide the errno.
kernel: fs/eventfd.c:do_eventfd; fs/file.c:alloc_fd@v6.18.46 -/
theorem dropped_bit_1_emfile_rejected :
    check_eventfd2 2 (mkEffect (errno_ret EMFILE) [] []) m = CheckReject := rfl

/-- -ENFILE for bit 1 is refused: the system-wide file count is
tested in `alloc_empty_file` (fs/file_table.c:239-278), which the file
allocation `anon_inode_getfile_fmode` (fs/anon_inodes.c) performs for
the call at fs/eventfd.c:409-410, below the gate.  The
spec twin's `dropped_bit_enfile_rejected` states the same lie on the
relation.
kernel: fs/eventfd.c:do_eventfd; fs/file_table.c:alloc_empty_file@v6.18.46 -/
theorem dropped_bit_1_enfile_rejected :
    check_eventfd2 2 (mkEffect (errno_ret ENFILE) [] []) m = CheckReject := rfl

/-- -ENOENT for bit 1 is refused. It is the errno
`State/Errno.lean` defines next after -EINVAL, so it is what
`tools/lean_mutate.py`'s errno-swap puts in the spec's place (the tool
mutates the twin under `Sys/`, never this checker); the
-ENOENT `__anon_inode_getfile` can raise (fs/anon_inodes.c:143-144) is
below the gate and needs a `fops->owner` that `eventfd_fops`
(fs/eventfd.c:302-311) does not set.
kernel: fs/eventfd.c:do_eventfd; fs/anon_inodes.c:__anon_inode_getfile@v6.18.46 -/
theorem dropped_bit_1_enoent_rejected :
    check_eventfd2 2 (mkEffect (errno_ret ENOENT) [] []) m = CheckReject := rfl

/-- The right errno beside a one-byte store is refused: `eventfd2` writes
no user memory on any path, and the gate returns before anything is
touched.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_1_einval_with_write_rejected :
    check_eventfd2 2 (mkEffect (errno_ret EINVAL) [(4096, [0])] []) m = CheckReject := rfl

/-- The right errno beside a zero-fill is refused for the same reason.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_1_einval_with_zero_rejected :
    check_eventfd2 2 (mkEffect (errno_ret EINVAL) [] [(4096, 1)]) m = CheckReject := rfl

/-- The right errno beside an unmap is refused: `do_eventfd` unmaps
nothing on any path.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_1_einval_with_unmap_rejected :
    check_eventfd2 2 (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(4096, 4096)] [] []) m
      = CheckReject := rfl

/-- The right errno beside a memory copy is refused: `do_eventfd` has no
`copy_to_user` and no `copy_from_user` on any path.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_1_einval_with_copy_rejected :
    check_eventfd2 2 (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy 0 4096 8] []) m
      = CheckReject := rfl

/-- The right errno beside a recorded copy-in is refused, for the same
reason: nothing is read from user memory.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_1_einval_with_copyin_rejected :
    check_eventfd2 2 (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 1)]) m
      = CheckReject := rfl

/-- A 32-bit -22, `0xffffffea`, is refused: `do_eventfd` returns an
`int`, but the syscall body `__SYSCALL_DEFINEx` generates is a `long`.
On riscv64 that macro is arch/riscv/include/asm/syscall_wrapper.h's
(lines 82-97, Linux v6.18.46): `ARCH_HAS_SYSCALL_WRAPPER` is selected at
arch/riscv/Kconfig:54, so the generic copy in include/linux/syscalls.h
(lines 246-267) sits under an `#ifndef` that is false there.  It
declares `__do_sys##name` as `static inline long` (lines 85 and 97), so
the `int` -22 becomes a `long` at `return do_eventfd(count, flags)` in
the body of `eventfd2` (fs/eventfd.c:423-426), and
`long ret = __do_sys##name(…)` at line 88 carries it on unchanged;
`syscall_handler` then stores the whole `long` with `regs->a0 = fn(regs)`
(arch/riscv/include/asm/syscall.h:101-112), so the register carries all
64 bits of the -EINVAL.
kernel: fs/eventfd.c:do_eventfd; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx@v6.18.46 -/
theorem dropped_bit_1_einval_32bit_rejected :
    check_eventfd2 2 (mkEffect 4294967274 [] []) m = CheckReject := rfl

end OtherLies

section AcceptedWords

/-! ## Rocq `eventfd2_accepted_flag_words_decline`: every word inside the mask is declined

The model has no kind for the object `do_eventfd` hands back past the
gate, so neither a descriptor nor any errno is judged there: the answer
is `CheckUnmodeled`, never `CheckOk` and never `CheckReject`.  -/

/-- `EFD_SEMAPHORE` alone with a descriptor: declined, not judged.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem semaphore_descriptor_declined :
    check_eventfd2 1 (mkEffect 3 [] []) m = CheckUnmodeled := rfl

/-- Zero flags with a descriptor: declined.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem zero_flags_descriptor_declined :
    check_eventfd2 0 (mkEffect 3 [] []) m = CheckUnmodeled := rfl

/-- `O_CLOEXEC` alone with a descriptor: declined.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem cloexec_descriptor_declined :
    check_eventfd2 524288 (mkEffect 3 [] []) m = CheckUnmodeled := rfl

/-- `O_NONBLOCK` alone with a descriptor: declined.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem nonblock_descriptor_declined :
    check_eventfd2 2048 (mkEffect 3 [] []) m = CheckUnmodeled := rfl

/-- The whole mask, `EFD_FLAGS_SET` = 526337, with a descriptor: declined.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem whole_mask_descriptor_declined :
    check_eventfd2 526337 (mkEffect 3 [] []) m = CheckUnmodeled := rfl

/-- The two shared-fcntl bits together, `O_CLOEXEC | O_NONBLOCK` = 526336
— the probe's `cloexec` case, and no Rocq conjunct — with a descriptor:
declined.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem shared_fcntl_descriptor_declined :
    check_eventfd2 526336 (mkEffect 3 [] []) m = CheckUnmodeled := rfl

/-- Past the gate the checker declines WHATEVER it is offered — a
descriptor, any errno, any ledger entry: `CheckUnmodeled` for every
`eff`, never `CheckReject`.  The kernel's -ENOMEM, -EMFILE, -ENFILE and
its descriptor grade the same, which is what fail-closed means here.
Stated at the empty word and at the whole mask.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem accepted_words_decline_every_effect (eff : SyscallEffect) :
    check_eventfd2 0 eff m = CheckUnmodeled ∧ check_eventfd2 526337 eff m = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- `EFD_SEMAPHORE` alone with -EINVAL: declined too — a wrong errno for
an accepted word is not REJECTED, because the arm does not judge that
word at all.  The probe's `fail-closed` case records the decline itself,
at this word.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem semaphore_einval_declined :
    check_eventfd2 1 (mkEffect (errno_ret EINVAL) [] []) m = CheckUnmodeled := rfl

/-- And the bit just above the mask's top bit, `2 * O_CLOEXEC` = 1048576
(bit 20 alone, no mask bit beside it), is still answered: Rocq's last
conjunct here, the one that keeps the declines above from staying green
under a mask that widened (or an arm that went unmodeled outright).
`dropped_bit_20_einval_accepted` states the same word from the other
example; the word with the mask beside a bad bit is
`mask_plus_bad_bit_einval_accepted`.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem bit_above_the_mask_top_still_answered :
    check_eventfd2 (524288 + 524288) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

end AcceptedWords

section Counter

/-! ## Rocq `eventfd2_counter_is_not_judged`: the counter is argument zero and the reading never picks it

Through the composition `flag32 (in_arg (efd_in count flags) 1)`, which
is what the arm will hand the checker: these fix that the reading is of
argument one, and what the checker answers on what it picks.  A reading
of argument zero would hand the checker the counter, and 2^20 is a bad
bit there. -/

/-- Counter 2^20 with zero flags, a descriptor: declined — the reading
picks the zero flag word, not the counter.
kernel: fs/eventfd.c:eventfd2@v6.18.46 -/
theorem counter_bit_20_descriptor_declined :
    check_eventfd2 (flag32 (in_arg (efd_in 1048576 0) 1)) (mkEffect 3 [] []) m
      = CheckUnmodeled := rfl

/-- Counter 2^20 with zero flags, -EINVAL: declined, not accepted; a
reading of argument zero would hand the checker 2^20 and it would accept.
kernel: fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem counter_bit_20_einval_declined :
    check_eventfd2 (flag32 (in_arg (efd_in 1048576 0) 1)) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled := rfl

/-- Counter 2^32 - 1, the whole `unsigned int`, zero flags, a descriptor:
declined.
kernel: fs/eventfd.c:eventfd2@v6.18.46 -/
theorem counter_max_descriptor_declined :
    check_eventfd2 (flag32 (in_arg (efd_in 4294967295 0) 1)) (mkEffect 3 [] []) m
      = CheckUnmodeled := rfl

/-- Counter 2^32 - 1, zero flags, -EINVAL: declined.
kernel: fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem counter_max_einval_declined :
    check_eventfd2 (flag32 (in_arg (efd_in 4294967295 0) 1)) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled := rfl

/-- Counter 2^32 - 1 beside bit 20 in the flags: the flags decide, and
the -EINVAL is accepted whatever the counter.
kernel: fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem counter_max_bad_flags_einval_accepted :
    check_eventfd2 (flag32 (in_arg (efd_in 4294967295 1048576) 1))
      (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- The probe's `einval` mode sends a wild counter beside bit 1,
`refused(0xFFFFFFFF, 1 << 1, …)`: the reading picks the flag word, and the
-EINVAL is accepted.
kernel: fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem counter_max_bit_1_einval_accepted :
    check_eventfd2 (flag32 (in_arg (efd_in 4294967295 2) 1))
      (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- The probe's `swapped` mode, `accepted(O_LARGEFILE | (1 << 1), 0, …)`:
a word full of unaccepted bits in the COUNTER position with clean flags
is declined — Linux hands back a descriptor, and an arm reading argument
zero would have refused it.
kernel: fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem swapped_arguments_descriptor_declined :
    check_eventfd2 (flag32 (in_arg (efd_in 32770 0) 1)) (mkEffect 3 [] []) m
      = CheckUnmodeled := rfl

end Counter

section Narrowing

/-! ## Rocq `eventfd2_narrows_the_flag_word`: `int flags` is 32 bits wide

A bit at or above 32 in the register is not part of the argument
`SYSCALL_DEFINE2(eventfd2, unsigned int, count, int, flags)` receives, so
a word whose low 32 bits are clean is clean.  The narrowing is `flag32`'s,
applied in the pins' own statements before the checker runs: these fix
that the composition drops the high half, not that the checker would —
it gates the whole word it is given, as Rocq's does, which
`the_checker_itself_reads_the_whole_word` states. -/

/-- Bit 32 alone, a descriptor: declined — the argument is clean.
kernel: fs/eventfd.c:eventfd2@v6.18.46 -/
theorem bit_32_descriptor_declined :
    check_eventfd2 (flag32 (in_arg (efd_in 0 4294967296) 1)) (mkEffect 3 [] []) m
      = CheckUnmodeled := rfl

/-- Bit 32 alone, -EINVAL: declined, not accepted — the reading drops
the bit, so the checker never sees the word that would make it accept
an errno the kernel never returns here.
kernel: fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem bit_32_einval_declined :
    check_eventfd2 (flag32 (in_arg (efd_in 0 4294967296) 1)) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled := rfl

/-- Bit 32 beside `EFD_SEMAPHORE`, a descriptor: declined.
kernel: fs/eventfd.c:eventfd2@v6.18.46 -/
theorem bit_32_and_semaphore_descriptor_declined :
    check_eventfd2 (flag32 (in_arg (efd_in 0 4294967297) 1)) (mkEffect 3 [] []) m
      = CheckUnmodeled := rfl

/-- Bit 32 beside bit 20: the low word carries a bad bit, and the -EINVAL
is accepted.
kernel: fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem bit_32_and_bit_20_einval_accepted :
    check_eventfd2 (flag32 (in_arg (efd_in 0 (4294967296 + 1048576)) 1))
      (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- The register's own top bit, 63, alone: the reading drops it with the
rest of the high half, `int flags` is 0, and a descriptor is declined —
Linux allocates.  Bit 32 stands for the high half at its bottom; this
word stands for it at its top, so a reading that kept bit 32 or bit 63
would fail one of them; a bit strictly between them is pinned by neither.
kernel: fs/eventfd.c:eventfd2@v6.18.46 -/
theorem top_bit_descriptor_declined :
    check_eventfd2 (flag32 (in_arg (efd_in 0 9223372036854775808) 1)) (mkEffect 3 [] []) m
      = CheckUnmodeled := rfl

/-- Bit 63 alone, -EINVAL: declined, not accepted.
kernel: fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem top_bit_einval_declined :
    check_eventfd2 (flag32 (in_arg (efd_in 0 9223372036854775808) 1))
      (mkEffect (errno_ret EINVAL) [] []) m = CheckUnmodeled := rfl

/-- Bit 63 beside bit 1: the low word carries the bad bit, and the
-EINVAL is accepted.
kernel: fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem top_bit_and_bit_1_einval_accepted :
    check_eventfd2 (flag32 (in_arg (efd_in 0 (9223372036854775808 + 2)) 1))
      (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- The probe's `refused(0, -1, …)`: a register of all ones narrows to
`0xffffffff`, every bit of `int flags`, and the -EINVAL is accepted — the
word `all_ones_32bit_einval_accepted` pins bare, reached through the
reading.
kernel: fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem all_ones_register_einval_accepted :
    check_eventfd2 (flag32 (in_arg (efd_in 0 (-1)) 1))
      (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- ...and the checker ITSELF, handed bit 32 without the reading, answers
-EINVAL to it: `do_eventfd` tests the residue of whatever word it is
given (fs/eventfd.c:390-391, Linux v6.18.46), and the `int` narrowing is
`__SC_CAST`'s (include/linux/syscalls.h:132, applied by riscv64's
`__SYSCALL_DEFINEx` at arch/riscv/include/asm/syscall_wrapper.h:88, same
version), one frame
up — as the
narrowing here is the reading's, one definition up.  The pins above
would hold of a checker that masked the low 32 bits itself; this one
does not, so the two together fix where the narrowing lives.  This is
not the kernel's answer at that register: Linux narrows before it
tests, and `eventfd2(0, 1 << 32)` gets a descriptor (the probe's
`hiflags` case), which is why the evidence line is `model:`.  It would
become a false claim about Linux the day a `checked_table` row handed
this checker the register in place of `flag32 (in_arg i 1)`; what
refuses that row is the spec twin's `full_register_einval_rejected` on
`syscall_spec`, and `eventfd2_narrows_the_flag_word_over_the_real_table`
in `V_pilot_Fs_EventFd`, the restatement of Rocq's
`eventfd2_narrows_the_flag_word` through `check_syscall`.
model: the checker's contract with the reading; Linux narrows first (__SC_CAST, cited above) and answers a descriptor at this register word -/
theorem the_checker_itself_reads_the_whole_word :
    check_eventfd2 4294967296 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

end Narrowing

section SignBit

/-! ## Rocq `eventfd2_sign_bit_is_still_a_bad_bit`: bit 31 of `int flags`

The gate is `flags & ~EFD_FLAGS_SET` on `int`s — every constituent of the
mask is an `int` constant — so the sign bit is a bit outside the mask
like any other, and neither the reading nor the gate treats it
specially. -/

/-- Bit 31 alone: -EINVAL.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem sign_bit_einval_accepted :
    check_eventfd2 2147483648 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- Bit 31 alone, a descriptor: refused.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem sign_bit_descriptor_rejected :
    check_eventfd2 2147483648 (mkEffect 3 [] []) m = CheckReject := rfl

/-- Bit 31 beside `EFD_SEMAPHORE`: -EINVAL.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem sign_bit_and_semaphore_einval_accepted :
    check_eventfd2 2147483649 (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- Bit 31 beside `EFD_SEMAPHORE`, a descriptor: refused — the mask bit
beside it clears nothing of the residue.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem sign_bit_and_semaphore_descriptor_rejected :
    check_eventfd2 2147483649 (mkEffect 3 [] []) m = CheckReject := rfl

/-- Bit 31 through the reading, `flag32 (in_arg (efd_in 0 2147483648) 1)`:
the narrowing keeps it — bit 31 is a bit of `int flags` — and the -EINVAL
is accepted, as the spec twin's `sign_bit_through_the_table_is_einval`
states on the relation.
kernel: fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem sign_bit_through_the_reading_einval_accepted :
    check_eventfd2 (flag32 (in_arg (efd_in 0 2147483648) 1))
      (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- `INT_MIN` as a C caller passes it: the register is sign-extended,
`0xffffffff80000000`, and `int flags` is `0x80000000` again once
`__SYSCALL_DEFINEx` narrows it (arch/riscv/include/asm/syscall_wrapper.h:88,
Linux v6.18.46).  The reading keeps bit 31 and drops the extension, and
the -EINVAL is accepted, as the spec twin's `sign_extended_int_min_is_einval`
states on the relation.
kernel: fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem sign_extended_int_min_through_the_reading_einval_accepted :
    check_eventfd2 (flag32 (in_arg (efd_in 0 (-2147483648)) 1))
      (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- ...and a descriptor at that register is refused.
kernel: fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem sign_extended_int_min_through_the_reading_descriptor_rejected :
    check_eventfd2 (flag32 (in_arg (efd_in 0 (-2147483648)) 1))
      (mkEffect 3 [] []) m = CheckReject := rfl

end SignBit

section BitSweep

/-! ## Every single bit of `int flags`, at once

The pins above fix the mask at the bits Rocq's examples and the probe
visit, and a mask widened by any OTHER bit passes every one of them: no
word pinned above has bit 3, say, as its only bit outside the mask (the
all-ones word carries every other).  The checker-to-spec lemmas catch a widening of the
checker alone, and the Uapi pin `create_masks_differ_by_the_semaphore_bit`
(`Checks/Cases/Sys/Uapi/Fs.lean`) catches one written into the constant;
what neither sees is the same literal widening written into the spec's
gate and the checker's together.  The sweeps below close that from
outside: one bit at a time, at every position outside the mask,
against the mask `do_eventfd` tests (fs/eventfd.c:390-391, Linux
v6.18.46, commit 1f99e9ab748f), the kernel's answer accepted and the
answer it cannot give refused at each.  The position is a
`Nat` under hypotheses, so the closer is a case split — `omega` turns
the bounds into one disjunct per position, `rfl` closes each — rather
than the bare `rfl` of a closed word. -/

/-- Each bit of `int flags` outside `EFD_FLAGS_SET`, alone, is refused
with -EINVAL, the model untouched, no event.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem every_single_bit_outside_the_mask_einval_accepted (b : Nat) (hb : b < 32)
    (h0 : b ≠ 0) (h11 : b ≠ 11) (h19 : b ≠ 19) :
    check_eventfd2 ((1 : word) <<< b) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := by
  have hb' : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 12 ∨ b = 13 ∨ b = 14 ∨ b = 15 ∨ b = 16 ∨ b = 17 ∨ b = 18 ∨ b = 20 ∨ b = 21 ∨ b = 22 ∨ b = 23 ∨ b = 24 ∨ b = 25 ∨ b = 26 ∨ b = 27 ∨ b = 28 ∨ b = 29 ∨ b = 30 ∨ b = 31 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- ...and a descriptor at any of those positions is refused: the gate
returns -EINVAL before `do_eventfd` (fs/eventfd.c:405, Linux v6.18.46)
calls `get_unused_fd_flags` (fs/file.c) for one, so at no single bad bit
does a descriptor exist for the checker to accept.  The negative half of the sweep above:
without it a checker admitting a second answer at a position no
single-word pin visits would pass this file.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem every_single_bit_outside_the_mask_descriptor_rejected (b : Nat) (hb : b < 32)
    (h0 : b ≠ 0) (h11 : b ≠ 11) (h19 : b ≠ 19) :
    check_eventfd2 ((1 : word) <<< b) (mkEffect 3 [] []) m = CheckReject := by
  have hb' : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 12 ∨ b = 13 ∨ b = 14 ∨ b = 15 ∨ b = 16 ∨ b = 17 ∨ b = 18 ∨ b = 20 ∨ b = 21 ∨ b = 22 ∨ b = 23 ∨ b = 24 ∨ b = 25 ∨ b = 26 ∨ b = 27 ∨ b = 28 ∨ b = 29 ∨ b = 30 ∨ b = 31 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Each of the three bits inside `EFD_FLAGS_SET`, alone, is declined
whatever effect is offered: the gate passes, and Linux goes on to
allocate.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem every_single_bit_inside_the_mask_declines (b : Nat)
    (hb : b = 0 ∨ b = 11 ∨ b = 19) (eff : SyscallEffect) :
    check_eventfd2 ((1 : word) <<< b) eff m = CheckUnmodeled := by
  rcases hb with rfl | rfl | rfl <;> rfl

end BitSweep

section Frame

/-! ## The frame lemma, at a concrete word

`check_eventfd2_frame` is proved for every word; one instance at a bad
bit records what the lemma is for: the ledger field of the model the
accepted answer returns is the one it was given.  That the whole model
comes back unchanged is what the `= CheckOk m []` pins above state; this
instance states less. -/

/-- The accepted -EINVAL leaves `m_vmmaps` as it was.
model: the checker's own frame; `check_eventfd2_frame` is the general fact -/
theorem einval_keeps_vmmaps (eff : SyscallEffect) (m' : Model) (evs : List event)
    (h : check_eventfd2 2 eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m :=
  check_eventfd2_frame 2 eff m m' evs h

end Frame

section Witness

/-! ## The witness: which outcome it names

`eventfd2_witness_ok` says the witness is admitted at every word,
which is the receptiveness field of the arm the registration builds.
The witness deliberately picks -EINVAL from the refused-word
alternative; its correctness no longer fixes a unique outcome. A
change made to both the spec and witness can still evade that proof.
The pins fix the outcome from outside, against `do_eventfd`
(fs/eventfd.c:390-391, Linux v6.18.46, commit 1f99e9ab748f), word by word
and then one bit position at a time. -/

/-- Bit 1 is outside `EFD_FLAGS_SET`, and the witness exhibits the -EINVAL
the kernel returns for it: the model untouched, no event.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_1_witnesses_einval :
    eventfd2_witness 2 m = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := rfl

/-- The sign bit of `int flags` is a bit outside the mask like any other:
-EINVAL.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem sign_bit_witnesses_einval :
    eventfd2_witness 2147483648 m = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := rfl

/-- Zero flags pass the gate, and the kernel goes on to hand back a
descriptor the model has no kind for, or an allocation errno: the
witness exhibits the decline, never an invented answer.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem zero_flags_witnesses_unmodeled : eventfd2_witness 0 m = Unmodeled := rfl

/-- `EFD_SEMAPHORE` alone passes the gate: declined.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem semaphore_witnesses_unmodeled : eventfd2_witness 1 m = Unmodeled := rfl

/-- The whole mask, 526337, passes the gate: declined.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem whole_mask_witnesses_unmodeled : eventfd2_witness 526337 m = Unmodeled := rfl

/-- The witness too reads the whole word it is given: bit 32 alone is a
bit outside the mask to it, and it exhibits the -EINVAL.  That Linux
narrows first is the reading's, as `the_checker_itself_reads_the_whole_word`
says of the checker; the registration row that would falsify that pin
falsifies this one, and the same two pins named there stand against it.
model: the witness's contract with the reading; Linux narrows first (__SC_CAST, as on the checker's twin) and answers a descriptor at this register word -/
theorem the_witness_itself_reads_the_whole_word :
    eventfd2_witness 4294967296 m = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := rfl

/-- Each bit of `int flags` outside `EFD_FLAGS_SET`, alone: the witness
exhibits the -EINVAL, the model untouched,
no event — its mask fixed from outside at every position, as the checker's
is by `every_single_bit_outside_the_mask_einval_accepted`.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem every_single_bit_outside_the_mask_witnesses_einval (b : Nat) (hb : b < 32)
    (h0 : b ≠ 0) (h11 : b ≠ 11) (h19 : b ≠ 19) :
    eventfd2_witness ((1 : word) <<< b) m = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  have hb' : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 12 ∨ b = 13 ∨ b = 14 ∨ b = 15 ∨ b = 16 ∨ b = 17 ∨ b = 18 ∨ b = 20 ∨ b = 21 ∨ b = 22 ∨ b = 23 ∨ b = 24 ∨ b = 25 ∨ b = 26 ∨ b = 27 ∨ b = 28 ∨ b = 29 ∨ b = 30 ∨ b = 31 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Each of the three bits inside `EFD_FLAGS_SET`, alone: the witness
exhibits the decline.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem every_single_bit_inside_the_mask_witnesses_unmodeled (b : Nat)
    (hb : b = 0 ∨ b = 11 ∨ b = 19) :
    eventfd2_witness ((1 : word) <<< b) m = Unmodeled := by
  rcases hb with rfl | rfl | rfl <;> rfl

end Witness

-- lean-port sentinel: ticket V-pilot-Fs-EventFd appends below this line

section V_pilot_Fs_EventFd

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-pilot-Fs-EventFd — `eventfd2` over the real table

WHAT IS TWINNED HERE.  The sections above state each Rocq example on the
checker itself, because `checked_table` carried no row for 19 when they
were written, and left the restatement through `check_syscall` to the
registration.  This is the registration.  Each of
the five examples `theories/LinuxProcessSem/Checks/Cases/Fs/EventFd.v`
states — every one through `check_syscall`, closed by `vm_compute` — is
restated here through the Lean `check_syscall`, over `checked_table`
itself, at the Rocq input `efd_in count flags` (the counter in `a0`, the
flag word in `a1`), under its Rocq name with `_over_the_real_table` after
it, K6b's convention for the pins at which the real table first answers a
call.  Rocq fixes `eventfd_model`; these hold at every model, as the
sections above do, since neither the lookup nor the arm reads one.

WHAT A PIN HERE ADDS to its checker-level twin above is the ARM's claim:
that the lookup at 19 finds `arm_eventfd2` rather than the dispatcher's
own decline, and that the arm hands the checker `flag32 (in_arg i 1)` —
argument one, low 32 bits.  A conjunct separates the two registers only
when exactly one of the two words carries a bit outside `EFD_FLAGS_SET`,
whichever answer it states: `eventfd2_counter_is_not_judged_over_the_real_table`'s
first four conjuncts decline at a dirty counter beside a clean flag word,
which an arm reading `a0` would accept or refuse, and the `counter_2` and
`flags_2` pins below separate them in both directions.  That theorem's
last conjunct does NOT: a counter of all ones is itself a dirty word, so
an arm reading `a0` accepts that -EINVAL too.  The declines carry the
narrowing: `eventfd2_narrows_the_flag_word_over_the_real_table` declines
an -EINVAL at bit 32, which the checker itself accepts
(`the_checker_itself_reads_the_whole_word`, above), so an arm handing it
the whole register fails that conjunct.  These are the two restatements
the header and `the_checker_itself_reads_the_whole_word` name.

POLARITY is the sections' above: the evidence line is `kernel:` on every
pin about the kernel's answer, `CheckOk` and `CheckReject` alike, and
`model:` on a pin about the table's own contents. -/

/-- The lookup the dispatcher performs on an `efd_in`, computed once:
`in_sysno` is `19` whatever the two words hold.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_efd_in (count flags : Int) :
    lookup_ca checked_table (bv_unsigned (efd_in count flags).in_sysno) = some arm_eventfd2 :=
  lookup_ca_checked_table_eventfd2

/-! ### The five Rocq examples, through `check_syscall` -/

/-- `eventfd2_dropped_flag_bits_are_einval` over the real table: one bit
outside `EFD_FLAGS_SET` at each of bits 1, 10, 15 and 20 is refused with
-EINVAL at fs/eventfd.c:390-391 (Linux v6.18.46), the model untouched and
no event, and a descriptor for any of them is a lie, since the gate
returns before `get_unused_fd_flags` at line 405.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem eventfd2_dropped_flag_bits_are_einval_over_the_real_table :
    check_syscall (efd_in 0 (2 ^ 1)) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_syscall (efd_in 0 (2 ^ 1)) (mkEffect 3 [] []) m = CheckReject
    ∧ check_syscall (efd_in 0 (2 ^ 10)) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_syscall (efd_in 0 (2 ^ 10)) (mkEffect 3 [] []) m = CheckReject
    ∧ check_syscall (efd_in 0 (2 ^ 15)) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_syscall (efd_in 0 (2 ^ 15)) (mkEffect 3 [] []) m = CheckReject
    ∧ check_syscall (efd_in 0 (2 ^ 20)) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_syscall (efd_in 0 (2 ^ 20)) (mkEffect 3 [] []) m = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `eventfd2_accepted_flag_words_decline` over the real table: every word
inside `EFD_FLAGS_SET` — `EFD_SEMAPHORE`, 0, `O_CLOEXEC`, `O_NONBLOCK` and
the whole mask — passes the gate at fs/eventfd.c:390-391 (Linux
v6.18.46), and `do_eventfd` goes on to allocate, so a descriptor is
declined rather than judged, and so is an -EINVAL at `EFD_SEMAPHORE`:
past the gate an LSM hook can end an accepted word in any errno,
-EINVAL included, through `security_file_alloc` (security/security.c,
Linux v6.18.46; the premise `eventfd2_spec`'s docstring walks), so that
answer is possible and may not be refused; bit 20, just above the mask's
top bit, is outside it and its -EINVAL accepted.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem eventfd2_accepted_flag_words_decline_over_the_real_table :
    check_syscall (efd_in 0 EFD_SEMAPHORE) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (efd_in 0 EFD_SEMAPHORE) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled
    ∧ check_syscall (efd_in 0 0) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (efd_in 0 O_CLOEXEC) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (efd_in 0 O_NONBLOCK) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (efd_in 0 EFD_FLAGS_SET) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (efd_in 0 (2 * O_CLOEXEC)) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `eventfd2_counter_is_not_judged` over the real table: the counter is
`unsigned int count`, argument ZERO of `SYSCALL_DEFINE2(eventfd2,
unsigned int, count, int, flags)` (fs/eventfd.c:423, Linux v6.18.46),
which `do_eventfd` stores (line 399) and never tests.  A counter of
`2^20` or of `2^32 - 1` in `a0` beside a clean flag word is declined for
either answer, which is what fixes that the arm reads the flag word off
`a1`, the register the riscv64 wrapper hands the second parameter
(`SC_RISCV_REGS_TO_ARGS` under `CONFIG_64BIT`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, same version).  A bad
flag bit in `a1` beside a counter of all ones is refused with -EINVAL,
and that -EINVAL is accepted; an arm reading `a0` would accept it too,
a counter of all ones being itself a dirty word.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem eventfd2_counter_is_not_judged_over_the_real_table :
    check_syscall (efd_in (2 ^ 20) 0) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (efd_in (2 ^ 20) 0) (mkEffect (errno_ret EINVAL) [] []) m = CheckUnmodeled
    ∧ check_syscall (efd_in (2 ^ 32 - 1) 0) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (efd_in (2 ^ 32 - 1) 0) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckUnmodeled
    ∧ check_syscall (efd_in (2 ^ 32 - 1) (2 ^ 20)) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `eventfd2_narrows_the_flag_word` over the real table: `flags` is
`int`, and riscv64's `__SYSCALL_DEFINEx` hands it to `__do_sys_eventfd2`
through `__SC_CAST` (include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46), so bit 32
of `a1` is not a bit of the argument.  Bit 32 alone is a clean word:
declined for a descriptor and for an -EINVAL alike, and so is bit 32
beside `EFD_SEMAPHORE`; bit 32 beside bit 20 leaves bit 20 in the low
word, and the -EINVAL is accepted.
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem eventfd2_narrows_the_flag_word_over_the_real_table :
    check_syscall (efd_in 0 (2 ^ 32)) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (efd_in 0 (2 ^ 32)) (mkEffect (errno_ret EINVAL) [] []) m = CheckUnmodeled
    ∧ check_syscall (efd_in 0 (2 ^ 32 + EFD_SEMAPHORE)) (mkEffect 3 [] []) m = CheckUnmodeled
    ∧ check_syscall (efd_in 0 (2 ^ 32 + 2 ^ 20)) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `eventfd2_sign_bit_is_still_a_bad_bit` over the real table: bit 31 is
the sign bit of `int flags`, outside `EFD_FLAGS_SET` like any other, so
`flags & ~EFD_FLAGS_SET` is nonzero and the gate at fs/eventfd.c:390-391
(Linux v6.18.46) refuses it with -EINVAL, alone and beside
`EFD_SEMAPHORE`; a descriptor at bit 31 is a lie.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem eventfd2_sign_bit_is_still_a_bad_bit_over_the_real_table :
    check_syscall (efd_in 0 (2 ^ 31)) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_syscall (efd_in 0 (2 ^ 31)) (mkEffect 3 [] []) m = CheckReject
    ∧ check_syscall (efd_in 0 (2 ^ 31 + EFD_SEMAPHORE)) (mkEffect (errno_ret EINVAL) [] []) m
      = CheckOk m [] :=
  ⟨rfl, rfl, rfl⟩

/-! ### The swapped registers, stated once through the table

The Rocq arm's docstring gives `eventfd2(1, 0)` as the call a reading of
the wrong argument would misjudge, but 1 is `EFD_SEMAPHORE`, inside the
mask, so a0 = 1 read as the flag word passes the gate too and that call
separates nothing; `Checks/Sys/Table.lean`'s row says so.  Bit 1 does
separate them, in both directions. -/

/-- `eventfd2(2, 0)`: a counter of 2 and no flags.  `int flags` is 0, the
gate passes and the kernel allocates, so an -EINVAL is declined; an arm
reading `a0` as the flag word would see bit 1 and accept it.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem counter_2_einval_declined_over_the_real_table :
    check_syscall (efd_in 2 0) (mkEffect (errno_ret EINVAL) [] []) m = CheckUnmodeled := rfl

/-- `eventfd2(0, 2)`: the same two words the other way round.  Bit 1 is in
`int flags` now, and the -EINVAL is accepted; an arm reading `a0` would
see 0 and decline.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem flags_2_einval_accepted_over_the_real_table :
    check_syscall (efd_in 0 2) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := rfl

/-- …and a descriptor at `eventfd2(0, 2)` is refused.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem flags_2_descriptor_rejected_over_the_real_table :
    check_syscall (efd_in 0 2) (mkEffect 3 [] []) m = CheckReject := rfl

/-! ### The witness the table hands `receptive`

`syscall_spec_witness` dispatches over the same table, so the arm's
`ca_witness` is what it answers at 19; the witness pins above fix
`eventfd2_witness` at a bare word, these fix that the arm hands it the
same reading the checker gets. -/

/-- A bad bit in `a1`: the witness exhibits the kernel's -EINVAL, the
model untouched, no event.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem flags_2_witnesses_einval_over_the_real_table :
    syscall_spec_witness (efd_in 0 2) m = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := rfl

/-- The same bit in `a0`, the counter: the flag word is 0, and the witness
exhibits the decline.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem counter_2_witnesses_unmodeled_over_the_real_table :
    syscall_spec_witness (efd_in 2 0) m = Unmodeled := rfl

/-- Bit 32 of `a1` alone: narrowed away, the flag word is 0, and the
witness exhibits the decline — not the -EINVAL it exhibits for that word
bare (`the_witness_itself_reads_the_whole_word`, above).
kernel: include/linux/syscalls.h:__SC_CAST; fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem bit_32_witnesses_unmodeled_over_the_real_table :
    syscall_spec_witness (efd_in 0 (2 ^ 32)) m = Unmodeled := rfl

end V_pilot_Fs_EventFd

-- lean-port sentinel: ticket V-Fs-EventFd appends below this line

section V_Fs_EventFd

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Fs-EventFd — the scenario's two creates, whatever else the input holds

`testing/syscall-check/tests/scenarios/wait_slot_close_reopen.c` creates an
eventfd at two flag words, each beside a zero counter: bit 1 in its `slot`
run, which the flags gate of `do_eventfd` (fs/eventfd.c:390-391,
Linux v6.18.46) refuses, and `EFD_NONBLOCK` in its `notify` and `epfirst`
runs, which that gate lets through.  Two of its CASE lines forge the answer:
a descriptor for the refused create (`eventfd2:ret=3 -- slot`), which must
be rejected, and a refusal of the other (`eventfd2:ret=-EINVAL -- notify`),
which must be declined.

WHAT THESE ADD to the pins above is an answer quantified over the
`SyscallInput`.  The checker and witness pins above take a flag word, not
an input: outright, some of them at every bit position in a set, or as
the reading of `efd_in` at chosen values.  The pins over the table take
`efd_in` at chosen values, and `efd_in` fixes a2..a5 at zero and the
memory empty.  `lookup_efd_in` binds the counter and the flag word, but
for the table lookup alone, and states no answer.  Each pin below
`lookup_19` is stated over every input `i` numbered 19 whose `a1` has the
scenario's word as its low 32 bits, whatever `a0`, a2..a5, the high half
of `a1` and the memory hold, at every model.  The low 32 bits are what the
kernel tests: `flags` is `int`, and riscv64's `__SYSCALL_DEFINEx` hands it
to `__do_sys_eventfd2` through `__SC_CAST` (include/linux/syscalls.h:132,
applied at arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46).
Two of those pins hold at every answer as well:
`notify_create_declines_every_answer_over_the_real_table` at `O_NONBLOCK`,
and `slot_refused_create_ignores_the_counter_over_the_real_table` at bit 1.
So an arm whose `check_syscall` result at either word, for one model and
one offered answer, differs between two such inputs fails one of those
two, whatever the two inputs differ in — `a0`, a2..a5 or any later
argument, the high half of `a1`, or the memory.  An arm that hands the
checker the whole register is among them: it rejects descriptor 3 at
`a1 = O_NONBLOCK + 2 ^ 32`, where the kernel's `int flags` is
`O_NONBLOCK`.  The two witness pins fix `syscall_spec_witness` at such
inputs the same way, one value at each word.

Why the rest of the input may be quantified is the same gate at both
words, which decides on `flags` alone: `do_eventfd` (fs/eventfd.c:390-391,
Linux v6.18.46) tests it before any other statement that can fail, and
before it stores the counter.
`SYSCALL_DEFINE2(eventfd2, unsigned int, count, int, flags)`
(fs/eventfd.c:423-426, Linux v6.18.46) reads no user memory, and its
riscv64 wrapper passes on the first two argument registers alone
(`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24,
Linux v6.18.46).  So at bit 1 every such input is refused with -EINVAL,
and at `O_NONBLOCK` every such input passes the gate and is declined,
whatever it then ends in.  Like every refusal in this file, the one at
bit 1 is of the syscall as the kernel runs it, with nothing attached that
rewrites its answer.  `sched_yield_spec`'s note in
`Sys/Kernel/Sched/Syscalls.lean` states that premise for the
error-injection entry the same wrapper declares
(arch/riscv/include/asm/syscall_wrapper.h:84, Linux v6.18.46).  The
-EINVAL rests on CONFIG_EVENTFD=y, the premise `Sys/Fs/EventFd.lean`
states and this file does not retest: no syscall argument distinguishes
the two builds.
WHY THE REPLAY DOES NOT SETTLE THEM.  `tools/lean_replay.py` compares the
notify run's create, and nothing past an occurrence of a number
`checked_table` has no row for.  The slot run's create is not compared
before every number that run makes before it (113, 56, 21, 22, 73, 72 and
57) has a row.  The epfirst run's is in no recording: case 013's ends at
`epoll_create1`'s decline.  The pins hold either way. -/

/-- The lookup the dispatcher performs at number 19, computed once for the
pins below, which take the number as a hypothesis on a free input.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_19 : lookup_ca checked_table 19 = some arm_eventfd2 :=
  lookup_ca_checked_table_eventfd2

/-- The slot run's refused create, at every input numbered 19 whose `a1`
has bit 1 alone as its low 32 bits: bit 1 of `int flags` is outside
`EFD_FLAGS_SET`, so `do_eventfd` (fs/eventfd.c:390-391, Linux v6.18.46)
returns -EINVAL at its gate, before it stores the counter, and the
-EINVAL is accepted whatever the rest of the input holds, the model
untouched, no event.
kernel: include/linux/syscalls.h:__SC_CAST; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem slot_refused_create_einval_accepted_over_the_real_table (i : SyscallInput)
    (hno : bv_unsigned i.in_sysno = 19) (hflags : bv_unsigned (in_arg i 1) % 2 ^ 32 = 2 ^ 1) :
    check_syscall i (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := by
  simp only [check_syscall, check_syscall_in, hno, lookup_19, ca_check_arm_eventfd2, flag32,
    abi_low32, hflags]
  rfl

/-- …and descriptor 3 for it is rejected at every such input, the
scenario's `eventfd2:ret=3 -- slot`: the gate returns before
`do_eventfd` (fs/eventfd.c:405, Linux v6.18.46) reserves a descriptor.
kernel: include/linux/syscalls.h:__SC_CAST; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem slot_refused_create_descriptor_rejected_over_the_real_table (i : SyscallInput)
    (hno : bv_unsigned i.in_sysno = 19) (hflags : bv_unsigned (in_arg i 1) % 2 ^ 32 = 2 ^ 1) :
    check_syscall i (mkEffect 3 [] []) m = CheckReject := by
  simp only [check_syscall, check_syscall_in, hno, lookup_19, ca_check_arm_eventfd2, flag32,
    abi_low32, hflags]
  rfl

/-- …and whatever the answer, the table's result for that create is the
same at every two such inputs.  The two pins above fix it for the -EINVAL
and for descriptor 3; this fixes that no other answer moves with the rest
of the input either, so an arm that accepted, say, an -ENOMEM at one
counter and not at another fails here.  The `simp only` rewrites both
sides to one term, which closes the goal.
kernel: include/linux/syscalls.h:__SC_CAST; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem slot_refused_create_ignores_the_counter_over_the_real_table (i i' : SyscallInput)
    (eff : SyscallEffect) (hno : bv_unsigned i.in_sysno = 19)
    (hflags : bv_unsigned (in_arg i 1) % 2 ^ 32 = 2 ^ 1) (hno' : bv_unsigned i'.in_sysno = 19)
    (hflags' : bv_unsigned (in_arg i' 1) % 2 ^ 32 = 2 ^ 1) :
    check_syscall i eff m = check_syscall i' eff m := by
  simp only [check_syscall, check_syscall_in, hno, hno', lookup_19, ca_check_arm_eventfd2, flag32,
    abi_low32, hflags, hflags']

/-- The notify run's create, at every input numbered 19 whose `a1` has
`O_NONBLOCK` alone as its low 32 bits, and whatever the answer:
`O_NONBLOCK` is inside `EFD_FLAGS_SET`, the gate passes, and `do_eventfd`
goes on to end in a descriptor to an object the model has no kind for, in
an allocation errno, or in whatever an LSM hook returns through
`security_file_alloc` (security/security.c:2958-2968, Linux v6.18.46),
which for a BPF program is any errno from -MAX_ERRNO up
(`bpf_lsm_get_retval_range`, kernel/bpf/bpf_lsm.c:447-467, Linux v6.18.46).
The scenario's `eventfd2:ret=-EINVAL -- notify` is therefore a possible
answer, declined rather than rejected.
kernel: include/linux/syscalls.h:__SC_CAST; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/eventfd.c:do_eventfd,eventfd2; security/security.c:security_file_alloc; kernel/bpf/bpf_lsm.c:bpf_lsm_get_retval_range@v6.18.46 -/
theorem notify_create_declines_every_answer_over_the_real_table (i : SyscallInput)
    (eff : SyscallEffect) (hno : bv_unsigned i.in_sysno = 19)
    (hflags : bv_unsigned (in_arg i 1) % 2 ^ 32 = O_NONBLOCK) :
    check_syscall i eff m = CheckUnmodeled := by
  simp only [check_syscall, check_syscall_in, hno, lookup_19, ca_check_arm_eventfd2, flag32,
    abi_low32, hflags]
  rfl

/-- The witness the table hands `receptive` for the slot run's create, at
every input numbered 19 whose `a1` has bit 1 alone as its low 32 bits:
the kernel's -EINVAL, the model untouched, no event.
kernel: include/linux/syscalls.h:__SC_CAST; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem slot_refused_create_witnesses_einval_over_the_real_table (i : SyscallInput)
    (hno : bv_unsigned i.in_sysno = 19) (hflags : bv_unsigned (in_arg i 1) % 2 ^ 32 = 2 ^ 1) :
    syscall_spec_witness i m = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  simp only [syscall_spec_witness, table_witness, hno, lookup_19, ca_witness_arm_eventfd2, flag32,
    abi_low32, hflags]
  rfl

/-- …and for the notify run's, at every input numbered 19 whose `a1` has
`O_NONBLOCK` alone as its low 32 bits: the decline, never an invented
answer.
kernel: include/linux/syscalls.h:__SC_CAST; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/eventfd.c:do_eventfd,eventfd2@v6.18.46 -/
theorem notify_create_witnesses_unmodeled_over_the_real_table (i : SyscallInput)
    (hno : bv_unsigned i.in_sysno = 19)
    (hflags : bv_unsigned (in_arg i 1) % 2 ^ 32 = O_NONBLOCK) :
    syscall_spec_witness i m = Unmodeled := by
  simp only [syscall_spec_witness, table_witness, hno, lookup_19, ca_witness_arm_eventfd2, flag32,
    abi_low32, hflags]
  rfl

end V_Fs_EventFd

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.EventFd
