-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Fs/EventFd.v
import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058
unported: eventfd_model -- the spec reads no field of the model, so every pin here quantifies over the model instead of naming one -/

/-! # Checks.Cases.Fs.EventFd — what `eventfd2` admits, read off against Linux

Worked examples over `Sys.Fs.EventFd.eventfd2_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Fs/EventFd.v`.  Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about what the kernel does, with the
citation beside it.

WHAT THE ARM ANSWERS, in one line: a flag word with a bit outside
`EFD_FLAGS_SET` is -EINVAL, the model unchanged and no event; every other
word is declined.  There is no second answer and no third arm.

HOW THESE ARE STATED.  The Rocq file reads the spec through the executable
checker and the dispatcher (`check_syscall` on inputs built by `efd_in`).
The pins here are stated on the relation itself (`Checks/Cases/Mm/Mmap.lean`'s
header says how).  The checker's own pins are
`Checks/Cases/Checks/Sys/Fs/EventFd.lean`'s, which imports this file and
restates the five Rocq examples on `check_eventfd2`; that file's header
says why they are not here — this file is the spec's mutation twin, and a
checker in its import closure turns every spec mutant into a stillbirth
before a pin here is read — and why they are not stated through the Lean
`check_syscall` either, which dispatches over a checked table with no arm
for 19 until the registration adds one. Each positive pin below is an
`iff` over EVERY outcome `o`, which fixes what is
admitted and what is refused in one statement; the refutations beside them
name the concrete lie a kernel could tell — a descriptor, an -ENOMEM, an
-EMFILE, an -ENFILE — and are what a reader looks for first.  Every proof is
`sys_norm` or `sys_refute`: the spec is unfolded, the gate decided, and
the monad primitives read.

TWO LAYERS, PINNED SEPARATELY.  The gate itself is pinned on
`eventfd2_spec` with the flag word given directly, as the arm receives it.
The two facts the arm cannot see — that the flag word is ARGUMENT 1 and
that it is NARROWED to 32 bits before the mask — are the table's
(`Sys/SyscallTable.lean`, `Syscall.flag32 (in_arg i 1)`), and are pinned
through `Specs.syscall_spec` on inputs built by `efd_in`.  No pin mentions
both.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventFd

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventFd
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! The spec's unfolding, registered where its pins are (`Checks/Cases/
Tactic.lean`'s register says what a spec owes); its gate
`eventfd2_einval_b` is decided, never unfolded. -/
attribute [sys_simp low] eventfd2_spec.eq_1

/-! ## The flag words these checks spell out

Kept as numerals in the statements so a reader sees the register value the
program passes; these pins say what each one is, at the values
include/uapi/asm-generic/fcntl.h and include/uapi/linux/eventfd.h give
them (Linux v6.18.46, commit 1f99e9ab748f; the derivations are on the
`Sys/Uapi/Fs.lean` constants). -/

/-- `EFD_SEMAPHORE`, bit 0.
kernel: include/uapi/linux/eventfd.h:EFD_SEMAPHORE@v6.18.46 -/
example : EFD_SEMAPHORE = 1 := by decide
/-- `O_NONBLOCK`, bit 11.
kernel: include/uapi/asm-generic/fcntl.h:O_NONBLOCK@v6.18.46 -/
example : O_NONBLOCK = 2 ^ 11 := by decide
/-- `O_CLOEXEC`, bit 19.
kernel: include/uapi/asm-generic/fcntl.h:O_CLOEXEC@v6.18.46 -/
example : O_CLOEXEC = 2 ^ 19 := by decide
/-- `O_LARGEFILE`, bit 15.
kernel: include/uapi/asm-generic/fcntl.h:O_LARGEFILE@v6.18.46 -/
example : O_LARGEFILE = 2 ^ 15 := by decide
/-- The mask `do_eventfd` tests, bits 0, 11 and 19: `EFD_FLAGS_SET` is
`EFD_SHARED_FCNTL_FLAGS | EFD_SEMAPHORE` and `EFD_SHARED_FCNTL_FLAGS` is
`O_CLOEXEC | O_NONBLOCK` (include/linux/eventfd.h:26-27, Linux v6.18.46).
kernel: fs/eventfd.c:do_eventfd; include/uapi/linux/eventfd.h:EFD_SEMAPHORE; include/uapi/asm-generic/fcntl.h:O_CLOEXEC,O_NONBLOCK@v6.18.46 -/
example : EFD_FLAGS_SET = 526337 := by decide
/-- The two shared-fcntl bits together, `EFD_SHARED_FCNTL_FLAGS`.
kernel: include/uapi/asm-generic/fcntl.h:O_CLOEXEC,O_NONBLOCK@v6.18.46 -/
example : O_CLOEXEC + O_NONBLOCK = 526336 := by decide

/-- THE SEPARATION FROM `timerfd_create`: the two create masks differ in
bit 0 and nowhere else.  `EFD_FLAGS_SET` is `EFD_SHARED_FCNTL_FLAGS |
EFD_SEMAPHORE` (include/linux/eventfd.h:26-27) and `TFD_CREATE_FLAGS` is
`TFD_SHARED_FCNTL_FLAGS` alone (include/linux/timerfd.h:14-16), both at
Linux v6.18.46, commit 1f99e9ab748f.
kernel: fs/eventfd.c:do_eventfd; fs/timerfd.c:timerfd_create; include/uapi/linux/eventfd.h:EFD_SEMAPHORE@v6.18.46 -/
example : EFD_FLAGS_SET = TFD_CREATE_FLAGS + EFD_SEMAPHORE := by decide

/-- The bit immediately above the mask's top bit (`O_CLOEXEC`, bit 19) is
bit 20.
kernel: include/uapi/asm-generic/fcntl.h:O_CLOEXEC@v6.18.46 -/
example : 2 * O_CLOEXEC = 2 ^ 20 := by decide

/-! ## The gate: `do_eventfd`'s one `if`, on the flag word the arm receives

`if (flags & ~EFD_FLAGS_SET) return -EINVAL;` is the first statement of
`do_eventfd` (fs/eventfd.c:390-391, Linux v6.18.46, commit 1f99e9ab748f)
that can fail: the three `BUILD_BUG_ON`s above it (lines 386-388) are
compile-time.  Everything that can answer anything else — the `kmalloc`
(line 393), `get_unused_fd_flags` (line 405), `anon_inode_getfile_fmode`
(line 409) — sits below it.  For a word with a bit outside the mask the
answer is -EINVAL, the model is untouched and no event is emitted,
whatever the counter and whatever the model.  Each `iff` below pins all
of that at once; the refutations name the lies. -/

/-- Bit 1, the bit immediately above `EFD_SEMAPHORE`: the likeliest
off-by-one when a reader remembers "eventfd2 takes a low bit".  -EINVAL
from the gate (fs/eventfd.c:390-391, Linux v6.18.46).
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_1_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec 2 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- Bit 10, just below `O_NONBLOCK`'s bit 11: the same gate.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_10_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec 1024 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- Bit 15, `O_LARGEFILE`'s bit, which musl ORs into every `open` it
issues and which this call does NOT accept: `EFD_FLAGS_SET` has no
`O_LARGEFILE` (include/linux/eventfd.h:26-27, Linux v6.18.46), so the
gate answers -EINVAL.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_15_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec 32768 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- Bit 20, the bit immediately above the mask's top bit (`O_CLOEXEC`,
bit 19): the sharpest witness that the mask is a mask and not a bound.
-EINVAL from the gate (fs/eventfd.c:390-391, Linux v6.18.46).
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_20_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec 1048576 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- The whole mask and one bit outside it (bit 1): accepted bits do not
excuse a refused one, because the residue `flags & ~EFD_FLAGS_SET` keeps
only the bits outside the mask (fs/eventfd.c:390-391, Linux v6.18.46).
testing/syscall-check/tests/eventfd2.c's `einval` case passes this word
to the pinned kernel.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem mask_plus_one_bad_bit_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec 526339 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- Every bit of the 32-bit word — what `eventfd2(0, -1)` and
`eventfd2(0, 0xFFFFFFFF)` both arrive as after the `int` narrowing, and
the words testing/syscall-check/tests/eventfd2.c's `einval` case sends:
-EINVAL (fs/eventfd.c:390-391, Linux v6.18.46).
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem every_flag_bit_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec 4294967295 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-! ### The lies a kernel could tell on a refused word

Each is refused by the `iff`s above already; these name the concrete
answer so the refusal is read, not derived. -/

/-- A DESCRIPTOR for a refused flag word is the lie
testing/syscall-check/tests/eventfd2.c's `larg` mutation tells
(`--mutate eventfd2:ret=3`, on the word `O_LARGEFILE` = 32768): `do_eventfd`
(fs/eventfd.c:390-391 against :405, Linux v6.18.46) returns before it
reaches `get_unused_fd_flags`, so no descriptor number exists to hand
back.  Stated on the probe's own word, so the evidence line and the pin
describe one call.
probe: testing/syscall-check/tests/eventfd2.c#reject --mutate eventfd2:ret=3 -- larg -/
theorem dropped_bit_15_descriptor_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ eventfd2_spec 32768 i m (Ok (mkEffect 3 [] []) m' evs) := by
  sys_refute

/-- The same lie on the lowest refused bit.  The `bit1` case offers fd 0
on word 2 (refused below, `--mutate eventfd2:ret=0`); no probe case
offers fd 3 on it, so this pin closes the fd-3 half by hand: the gate
(fs/eventfd.c:390-391, Linux v6.18.46) returns before `get_unused_fd_flags`
(:405) on this word as on every refused one.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_1_descriptor_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ eventfd2_spec 2 i m (Ok (mkEffect 3 [] []) m' evs) := by
  sys_refute

/-- …nor fd 0, which is a descriptor and not an errno (the `bit1`
mutation, `--mutate eventfd2:ret=0`, on the word `1 << 1`): `errno_ret EINVAL`
is `-22` as a 64-bit word, and 0 is not it.
probe: testing/syscall-check/tests/eventfd2.c#reject --mutate eventfd2:ret=0 -- bit1 -/
theorem dropped_bit_fd_zero_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ eventfd2_spec 2 i m (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- -ENOMEM is unreachable on a refused word: the `kmalloc` that can
answer it (fs/eventfd.c:393-395, Linux v6.18.46) is below the gate, so a
kernel that reports the allocation failing for a word it never allocated
for is lying.  This is the errno-precedence pin: the gate's -EINVAL wins
over the allocator's -ENOMEM because the allocator is never reached.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_enomem_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ eventfd2_spec 2 i m (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- -EMFILE is unreachable the same way: `alloc_fd` (fs/file.c:570, Linux
v6.18.46, reached from `do_eventfd` (fs/eventfd.c:405, Linux v6.18.46)
through `get_unused_fd_flags`) is below the gate, so a full descriptor table cannot turn a refused flag word into
-EMFILE.
kernel: fs/eventfd.c:do_eventfd; fs/file.c:alloc_fd@v6.18.46 -/
theorem dropped_bit_emfile_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ eventfd2_spec 2 i m (Ok (mkEffect (errno_ret EMFILE) [] []) m' evs) := by
  sys_refute

/-- -ENFILE is the system-wide file table's refusal: `alloc_empty_file`
decides it at fs/file_table.c:248-255 and returns it at :278 (Linux
v6.18.46), for a caller without CAP_SYS_ADMIN, reached from `do_eventfd`
(fs/eventfd.c:409-410, Linux v6.18.46) through `anon_inode_getfile_fmode`
(fs/anon_inodes.c:226), `__anon_inode_getfile` (fs/anon_inodes.c:134),
`alloc_file_pseudo` (fs/file_table.c:408) and `alloc_file`
(fs/file_table.c:386), all Linux v6.18.46; the Sys header walks the call
sites.  It is the errno the errno walk of the Rocq header omits, and the
fourth thing an accepted word can end in.  On a refused word it is below
the gate like the rest, so a kernel reporting it is lying.
kernel: fs/file_table.c:alloc_empty_file@v6.18.46 -/
theorem dropped_bit_enfile_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ eventfd2_spec 2 i m (Ok (mkEffect (errno_ret ENFILE) [] []) m' evs) := by
  sys_refute

/-- -ENOENT is refused on a refused word, and not ONLY because the gate
comes first: `__anon_inode_getfile` (fs/anon_inodes.c:143-144, Linux v6.18.46)
answers it only when `fops->owner` is set and `try_module_get` fails, and
`eventfd_fops` (fs/eventfd.c:302-311, Linux v6.18.46) has no `owner`, so
that test refuses no `eventfd2` call on any word.  Its neighbour -ENODEV
(fs/anon_inodes.c:155-156, Linux v6.18.46) needs `anon_inode_inode` to be
an error pointer, which `anon_inode_init` panics on instead
(fs/anon_inodes.c:370-372, Linux v6.18.46), so it is unreachable on a
booted kernel too; the errno block does not name it, so it has no pin of
its own.  What CAN follow the gate on an accepted word is the walk the
Sys header gives — -ENOMEM, -EMFILE, -ENFILE, or the descriptor — under
the one premise stated there: that no LSM `file_alloc_security` hook
returns nonzero, which every static hook keeps and a BPF LSM program
need not.  This pin stands beside `dropped_bit_enomem_rejected` as the
same lie with an errno no test on the path produces.
kernel: fs/anon_inodes.c:__anon_inode_getfile@v6.18.46 -/
theorem dropped_bit_enoent_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ eventfd2_spec 2 i m (Ok (mkEffect (errno_ret ENOENT) [] []) m' evs) := by
  sys_refute

/-- A refused word is ANSWERED and never declined: the arm leaves no
room for a fail-closed reading of a word the gate judges.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem dropped_bit_never_unmodeled (i : SyscallInput) (m : Model) :
    ¬ eventfd2_spec 2 i m Unmodeled := by
  sys_refute

/-- No policy errno at this gate: `do_eventfd` tests the flag word and
nothing about the caller (fs/eventfd.c:390-391, Linux v6.18.46), so
-EPERM is a lie on a refused word as surely as a descriptor is.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem refused_eperm (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ eventfd2_spec 2 i m (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  sys_refute

/-- The -EINVAL is INERT: `do_eventfd` returns before any store or
allocation (fs/eventfd.c:391, Linux v6.18.46), so an outcome carrying an
event beside the right errno is refused too — something a probe's view of
the return value cannot see.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem einval_with_an_event_rejected (i : SyscallInput) (m m' : Model) :
    ¬ eventfd2_spec 2 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' [WriteEv 1 65]) := by
  sys_refute

/-- …and inert in user memory: `eventfd2` takes two scalars
(`SYSCALL_DEFINE2(eventfd2, unsigned int, count, int, flags)`,
fs/eventfd.c:423, Linux v6.18.46) and `do_eventfd` returns at the gate
(fs/eventfd.c:390-391, Linux v6.18.46) before any store, so an -EINVAL
that delivered a byte to user memory is a lie — the harness's
`smuggle-write` mutation's, which no `ret=` case of
testing/syscall-check/tests/eventfd2.c can tell.  The event pin above and
this one are the two legs of inertness a refutation can state; the third,
an unchanged model, is what every `iff` above fixes with `m` on both sides.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem einval_with_a_write_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ eventfd2_spec 2 i m (Ok (mkEffect (errno_ret EINVAL) [(0, [0])] []) m' evs) := by
  sys_refute

/-! ## The sign bit: a truthiness test, not a sign test

`flags & ~EFD_FLAGS_SET` is the `if` condition itself (fs/eventfd.c:390,
Linux v6.18.46), so a residue of 0x80000000 — negative as the `int`
`flags` is declared — takes the -EINVAL exactly as a residue of 1 does.
A spec that compared the residue against 0 with `>` on a signed reading
would accept this word; testing/syscall-check/tests/eventfd2.c's `dropped`
pair pins it against a real run. -/

/-- Bit 31 alone: -EINVAL.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem sign_bit_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec 2147483648 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- …and beside an accepted bit (`EFD_SEMAPHORE`), so the sign bit is not
excused by the company it keeps.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem sign_bit_beside_semaphore_is_einval (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    eventfd2_spec 2147483649 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- The `dropped` mutation of testing/syscall-check/tests/eventfd2.c: a
kernel that dropped bit 31 and handed out a descriptor.
probe: testing/syscall-check/tests/eventfd2.c#reject --mutate eventfd2:ret=3 -- dropped -/
theorem sign_bit_descriptor_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ eventfd2_spec 2147483648 i m (Ok (mkEffect 3 [] []) m' evs) := by
  sys_refute

/-! ## The accepted mask declines rather than answers

Every word inside `EFD_FLAGS_SET` passes the gate, and everything past
the gate ends in one of four answers (fs/eventfd.c:393-421, Linux
v6.18.46): -ENOMEM from the `kmalloc` (fs/eventfd.c:393-395), from
`alloc_fdtable` (fs/file.c:242, Linux v6.18.46; under `alloc_fd` :596
through `expand_files` :315 and `expand_fdtable` :259), from
`alloc_empty_file` (fs/file_table.c:260, Linux v6.18.46; or :262-265
forwarding `lsm_file_alloc`, security/security.c:772-774) or from
`alloc_path_pseudo` (fs/file_table.c:402, Linux v6.18.46); -EMFILE from
`alloc_fd` (fs/file.c:591), `expand_files` (fs/file.c:310-311) or
`alloc_fdtable` (fs/file.c:197 and :213, Linux v6.18.46), all under
`get_unused_fd_flags` (fs/file.c:620), which `do_eventfd` calls at
fs/eventfd.c:405; -ENFILE from the file table (`alloc_empty_file`,
fs/file_table.c:248-255 and :278, Linux v6.18.46, under
`anon_inode_getfile_fmode`, fs/anon_inodes.c:226, which `do_eventfd`
calls at fs/eventfd.c:409-410); or the descriptor number — never
-ENOENT or -ENODEV from the path's own tests, for the reason on
`dropped_bit_enoent_rejected`, and all of it under the LSM premise the
Sys header states.
The model has no eventfd descriptor kind, so the arm declines these — the
Rocq file header's argument.  The `iff`s below say the decline is keyed
on the flag word and on nothing else, and the refutations say what the
decline is NOT: it is not an -EINVAL a narrower mask would produce, and
it is not an admission of the descriptor. -/

/-- The empty flag word, which is what glibc's and musl's `eventfd(0, 0)`
compile to: past the gate, declined.
probe: testing/syscall-check/tests/eventfd2.c#fail-closed --expect-unmodeled eventfd2 -- plain -/
theorem empty_flags_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `EFD_SEMAPHORE` alone: accepted by `eventfd2`, since bit 0 is in
`EFD_FLAGS_SET` (include/linux/eventfd.h:27, Linux v6.18.46) — and
refused by `timerfd_create`, whose mask lacks it.  Declined here.
probe: testing/syscall-check/tests/eventfd2.c#fail-closed --expect-unmodeled eventfd2 -- sem -/
theorem semaphore_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec 1 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `O_CLOEXEC` alone (`EFD_CLOEXEC`, include/uapi/linux/eventfd.h:8, Linux
v6.18.46): declined.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem cloexec_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec 524288 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `O_NONBLOCK` alone (`EFD_NONBLOCK`, include/uapi/linux/eventfd.h:9, Linux
v6.18.46): declined.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem nonblock_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec 2048 i m o ↔ o = Unmodeled := by
  sys_norm

/-- The two shared-fcntl bits together (`EFD_SHARED_FCNTL_FLAGS`,
include/linux/eventfd.h:26, Linux v6.18.46): declined.
probe: testing/syscall-check/tests/eventfd2.c#fail-closed --expect-unmodeled eventfd2 -- cloexec -/
theorem shared_fcntl_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec 526336 i m o ↔ o = Unmodeled := by
  sys_norm

/-- Every accepted bit at once: declined.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem whole_mask_declines (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec 526337 i m o ↔ o = Unmodeled := by
  sys_norm

/-- THE SEPARATION FROM `timerfd_create`, as a refutation: a model that
spelled this gate with `TFD_CREATE_FLAGS` would answer -EINVAL for
`EFD_SEMAPHORE`, and Linux does not — `eventfd2(0, 1)` hands back a
descriptor (fs/eventfd.c:390-391 with include/linux/eventfd.h:27, Linux
v6.18.46).  The -EINVAL is refused.
probe: testing/syscall-check/tests/eventfd2.c#fail-closed --expect-unmodeled eventfd2 -- sem -/
theorem semaphore_einval_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ eventfd2_spec 1 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and for the whole mask, so a spec that refused any accepted bit is
caught at its widest.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem whole_mask_einval_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ eventfd2_spec 526337 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The descriptor Linux DOES hand back for `eventfd2(0, 0)` is not
admitted either: the arm declines it, so an acceptor built on this spec
must answer unmodeled and never accept — the fail-closed half, which
testing/syscall-check/tests/eventfd2.c's `plain` case reaches as
`--expect-unmodeled`.  What this pin rules out is a spec that admitted
the success without a descriptor kind to record it in.
probe: testing/syscall-check/tests/eventfd2.c#fail-closed --expect-unmodeled eventfd2 -- plain -/
theorem empty_flags_descriptor_not_admitted (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ eventfd2_spec 0 i m (Ok (mkEffect 3 [] []) m' evs) := by
  sys_refute

/-! ## Single-bit sweeps

The two sweeps between them say what the mask is, bit by bit, without
leaning on which single words happen to have a pin of their own: every
bit outside `EFD_FLAGS_SET` is answered -EINVAL and every bit inside it
declines.  A mask widened or narrowed by one bit fails one of the two. -/

/-- Every single bit outside the mask is -EINVAL.  This is what catches
a mask that grew a bit the kernel's `EFD_FLAGS_SET` does not have
(include/linux/eventfd.h:26-27, Linux v6.18.46).
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem every_single_bit_outside_the_mask_is_einval (b : Nat) (hb : b < 32)
    (h0 : b ≠ 0) (h11 : b ≠ 11) (h19 : b ≠ 19)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec (2 ^ b) i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  have hb' : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨
      b = 12 ∨ b = 13 ∨ b = 14 ∨ b = 15 ∨ b = 16 ∨ b = 17 ∨ b = 18 ∨ b = 20 ∨ b = 21 ∨ b = 22 ∨
      b = 23 ∨ b = 24 ∨ b = 25 ∨ b = 26 ∨ b = 27 ∨ b = 28 ∨ b = 29 ∨ b = 30 ∨ b = 31 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    sys_norm

/-- Every single bit inside the mask declines.  This is what catches a
mask that lost one of the three bits `EFD_FLAGS_SET` has.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem every_single_guest_mask_bit_declines (b : Nat)
    (hb : b = 0 ∨ b = 11 ∨ b = 19)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    eventfd2_spec (2 ^ b) i m o ↔ o = Unmodeled := by
  rcases hb with rfl | rfl | rfl <;> sys_norm

/-! ## Through the table: the flag word is argument 1, and it narrows

`SYSCALL_DEFINE2(eventfd2, unsigned int, count, int, flags)`
(fs/eventfd.c:423, Linux v6.18.46, commit 1f99e9ab748f): the counter is
a0 and the flag word is a1, and riscv64's `__SYSCALL_DEFINEx`
(arch/riscv/include/asm/syscall_wrapper.h:82-88) hands the full-width
registers to `__do_sys_eventfd2` through `__SC_CAST`
(include/linux/syscalls.h:132, Linux v6.18.46, `(__force t) a`), so
`flags` is narrowed
to its declared `int` before the mask is applied and `count` to its
`unsigned int` before it is stored.  The table line applies
`Syscall.flag32` to `in_arg i 1` for exactly that reason; these pins are
what would catch the line reading the wrong argument or the whole
register. -/

/-- The counter comes FIRST and the flag word second, which is the one
thing about this call's shape a reader is likely to get backwards;
`efd_in` is written to make that visible at every use site. -/
def efd_in (count flags : Int) : SyscallInput :=
  SyscallInput.mkInput 19 [Z_to_bv 64 count, Z_to_bv 64 flags, 0, 0, 0, 0]
    (fun _ => none) (fun _ => none)

/-- Syscall 19 is `eventfd2`: `__NR_eventfd2 19`
(include/uapi/asm-generic/unistd.h:75, Linux v6.18.46), and there is no
`__NR_eventfd` in that table at all.
kernel: include/uapi/asm-generic/unistd.h:__NR_eventfd2@v6.18.46 -/
example : (19 : Int) ∈ modeled_sysnos := by decide

/-- …and it reaches the gate with a1 as the flag word: bit 1 in a1 gives
the -EINVAL of `dropped_bit_1_is_einval`, through the dispatcher.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem sysno_19_is_eventfd2 (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (efd_in 0 2) m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-! ### The counter is not judged

`count` is stored by `ctx->count = count` (fs/eventfd.c:399, Linux
v6.18.46), BELOW the gate; nothing above the gate reads it.  So no value
of it can be refused, and a wild counter neither earns an -EINVAL with a
clean flag word nor rescues a bad one. -/

/-- A counter with bits far outside any flag mask, flags clean: past the
gate, declined — and NOT -EINVAL, which is what an arm reading a0 as the
flag word would answer.
kernel: fs/eventfd.c:eventfd2,do_eventfd@v6.18.46 -/
theorem counter_bit_20_is_not_judged (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (efd_in 1048576 0) m o ↔ o = Unmodeled := by
  sys_norm

/-- The largest counter an `unsigned int` can carry, which
testing/syscall-check/tests/eventfd2.c's `bigcount` case passes: every
value is a legal initial counter.
probe: testing/syscall-check/tests/eventfd2.c#fail-closed --expect-unmodeled eventfd2 -- bigcount -/
theorem counter_max_is_not_judged (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (efd_in 4294967295 0) m o ↔ o = Unmodeled := by
  sys_norm

/-- A wild counter does not rescue a BAD flag word either: bit 20 in a1
still yields -EINVAL whatever a0 holds.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem wild_counter_bad_flags_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (efd_in 4294967295 1048576) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- The swapped-argument lie: an arm judging a0 against `EFD_FLAGS_SET`
would answer -EINVAL for `eventfd2(2^20, 0)`, a legal call Linux answers
with a descriptor (fs/eventfd.c:399, Linux v6.18.46, stores the counter
unjudged).
kernel: fs/eventfd.c:eventfd2,do_eventfd@v6.18.46 -/
theorem swapped_arguments_rejected (m m' : Model) (evs : List event) :
    ¬ syscall_spec (efd_in 1048576 0) m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-! ### The flag word narrows to 32 bits

A high half on the flag word is discarded by the `int` cast at the
wrapper (include/linux/syscalls.h:132, Linux v6.18.46) before
`do_eventfd` sees the word, so `eventfd2(0, 2^32)` IS `eventfd2(0, 0)`
and Linux hands back a descriptor for it (testing/syscall-check/tests/
eventfd2.c's `hiflags` case).  A spec comparing the whole 64-bit register
against the mask would have answered -EINVAL. -/

/-- Bit 32 alone aliases onto the empty word: declined.
probe: testing/syscall-check/tests/eventfd2.c#fail-closed --expect-unmodeled eventfd2 -- hiflags -/
theorem high_half_aliases_to_empty (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (efd_in 0 4294967296) m o ↔ o = Unmodeled := by
  sys_norm

/-- An accepted low half under a high half is still accepted: declined.
kernel: fs/eventfd.c:eventfd2,do_eventfd; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem high_half_over_semaphore_declines (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (efd_in 0 4294967297) m o ↔ o = Unmodeled := by
  sys_norm

/-- …and the high half does not rescue a BAD low half: aliasing is not a
second chance.  Bit 20 under bit 32 yields -EINVAL.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem high_half_over_bad_bit_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (efd_in 0 (4294967296 + 1048576)) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- The full register set, `eventfd2(0, -1)` as a 64-bit word: the low
half is every flag bit, so -EINVAL (fs/eventfd.c:390-391, Linux
v6.18.46); testing/syscall-check/tests/eventfd2.c's `einval` case sends
this word.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem all_ones_register_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (efd_in 0 (-1)) m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- The full-register lie: -EINVAL for a word whose low 32 bits are clean.
No kernel returns it, because no kernel sees the high half.
probe: testing/syscall-check/tests/eventfd2.c#fail-closed --expect-unmodeled eventfd2 -- hiflags -/
theorem full_register_einval_rejected (m m' : Model) (evs : List event) :
    ¬ syscall_spec (efd_in 0 4294967296) m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The sign bit THROUGH the table: a narrowing that kept 31 bits, or
masked the sign bit, would pass every pin above (the all-ones word still
carries bits 1..30) and answer nothing here.  `flag32` keeps all 32, and
the kernel's `int` keeps all 32 (include/linux/syscalls.h:132, Linux
v6.18.46), so bit 31 in a1 is -EINVAL at the gate (fs/eventfd.c:390-391),
as testing/syscall-check/tests/eventfd2.c's `dropped` case observes.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem sign_bit_through_the_table_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (efd_in 0 2147483648) m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- …and as a C caller really passes `INT_MIN`: sign-extended to the
64-bit register, `0xFFFFFFFF80000000`.  The `int` cast keeps the low 32
bits, `0x80000000`, and the gate refuses them (fs/eventfd.c:390-391,
Linux v6.18.46); the high half changes nothing.
kernel: fs/eventfd.c:do_eventfd@v6.18.46 -/
theorem sign_extended_int_min_is_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (efd_in 0 (-2147483648)) m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.EventFd
