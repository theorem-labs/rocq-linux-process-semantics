-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Fs/Locks.v
import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! rocq-cases: f1006fe8178338a499b5e5c41be83006c4edd058
covers: flock_success_is_inert -- ex_on_sole_opener_is_zero, ex_on_sole_opener_eagain_rejected, unlock_on_dir_is_zero, unlock_on_dir_einval_rejected, mand_on_closed_fd_is_zero, mand_on_closed_fd_ebadf_refuted
covers: flock_second_opener_declines -- sh_on_sole_opener_is_zero, sh_on_second_opener_is_unmodeled, unlock_on_second_opener_is_zero, unlock_on_second_opener_eagain_rejected
covers: flock_every_file_kind_counts_as_an_opener -- sole_file_is_zero, sole_filew_is_zero, pair_file_declines, pair_filew_declines, mixed_filew_declines, unlock_on_pair_filew_is_zero, sole_filew_eagain_rejected, a17_rdwr_counts_as_opener, a17_file_beside_rdwr_declines, a17_rdwr_unlock_on_pair_is_zero, a17_append_counts_as_opener, a17_file_beside_append_declines, a17_append_unlock_on_pair_is_zero -/

/-! # Checks.Cases.Fs.Locks — what `flock` admits, read off against Linux

Worked examples over `Sys.Fs.Locks.flock_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Fs/Locks.v`.  Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about what the kernel does, with the
citation beside it. Kernel citations name fs/locks.c at Linux v6.18.46
(commit 1f99e9ab748f); version-dependent declines cite the fail-closed
probe and the source argument in `Sys/Fs/Locks.lean`.

HOW THESE ARE STATED.  A check is stated on the relation itself
(`Checks/Cases/Mm/Mmap.lean`'s header says why): an `iff` over EVERY
outcome `o`,

    flock_spec fd cmd i m o ↔ o = Ok (mkEffect 0 [] []) m []

pins the positive half (0 is admitted, and the model and event list are
untouched) and the negative half (nothing else is — not another errno, not
a write, not `Unmodeled`) in one statement.  Every arm of `flock` answers
with a single outcome, so every `iff` here has a single right-hand side and
is closed by `sys_norm` alone; each is followed by a refutation of the
concrete alternative answer, closed by `sys_refute`.  The command word is
judged BEFORE the descriptor: `LOCK_MAND` answers 0 and an unrecognized
operation -EINVAL whether or not the descriptor is open, and only a
recognized operation on a closed descriptor reaches -EBADF.

THE TABLES.  `flock_model` is Rocq's: one opener per file, fd 3 reading
"f", fd 4 writing "g", fd 5 a directory reference, so fd 3 and fd 4 are
each the SOLE opener of their path and are granted.
`flock_two_openers_model` adds fd 6, a SECOND descriptor on "f" — what a
second `openat` of the same name produces — and differs in nothing else.
`flock_kinds_model` adds a socket, a pipe end and the two device nodes.
These fixtures exercise the grant and the decline across different
tables; `path_openers` is the count the grant turns on.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins
prove is that this spec and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Locks

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Locks
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The command words these checks spell out

Kept as numerals in the statements so a reader sees the register value the
program passes (include/uapi/asm-generic/fcntl.h:176-186, Linux v6.18.46);
these pins say what each one is.  `LOCK_NB`'s `#define` (:178) trails a
multi-line comment the evidence checker cannot evaluate, so the pins that
name it point at `SYSCALL_DEFINE2(flock)`, whose `cmd & ~LOCK_NB` is
where the bit is read. -/

/-- kernel: include/uapi/asm-generic/fcntl.h:LOCK_SH@v6.18.46 -/
example : LOCK_SH = 1 := by decide
/-- kernel: include/uapi/asm-generic/fcntl.h:LOCK_EX@v6.18.46 -/
example : LOCK_EX = 2 := by decide
/-- kernel: include/uapi/asm-generic/fcntl.h:LOCK_SH,LOCK_EX@v6.18.46 -/
example : LOCK_SH + LOCK_EX = 3 := by decide
/-- kernel: fs/locks.c:flock@v6.18.46 -/
example : LOCK_NB = 4 := by decide
/-- kernel: include/uapi/asm-generic/fcntl.h:LOCK_SH; fs/locks.c:flock@v6.18.46 -/
example : LOCK_SH + LOCK_NB = 5 := by decide
/-- kernel: include/uapi/asm-generic/fcntl.h:LOCK_EX; fs/locks.c:flock@v6.18.46 -/
example : LOCK_EX + LOCK_NB = 6 := by decide
/-- kernel: include/uapi/asm-generic/fcntl.h:LOCK_UN@v6.18.46 -/
example : LOCK_UN = 8 := by decide
/-- kernel: include/uapi/asm-generic/fcntl.h:LOCK_SH,LOCK_UN@v6.18.46 -/
example : LOCK_SH + LOCK_UN = 9 := by decide
/-- kernel: include/uapi/asm-generic/fcntl.h:LOCK_EX,LOCK_UN@v6.18.46 -/
example : LOCK_EX + LOCK_UN = 10 := by decide
/-- kernel: include/uapi/asm-generic/fcntl.h:LOCK_UN; fs/locks.c:flock@v6.18.46 -/
example : LOCK_UN + LOCK_NB = 12 := by decide
/-- kernel: include/uapi/asm-generic/fcntl.h:LOCK_MAND@v6.18.46 -/
example : LOCK_MAND = 32 := by decide
/-- kernel: include/uapi/asm-generic/fcntl.h:LOCK_MAND,LOCK_EX@v6.18.46 -/
example : LOCK_MAND + LOCK_EX = 34 := by decide
/-- kernel: include/uapi/asm-generic/fcntl.h:LOCK_MAND,LOCK_READ@v6.18.46 -/
example : LOCK_MAND + 64 = 96 := by decide   -- 64 is `LOCK_READ` (fcntl.h:187)

/-! ## The register

The spec's unfolding, at low priority like every other (the
`Checks/Cases/Tactic.lean` header says why); nothing for its gates, which
are decided, never unfolded.  The fixtures enter by their unfoldings, so a
post-state and the fixture a check names meet in one constructor tree. -/

attribute [sys_simp low] flock_spec.eq_1

/-! ## The tables -/

/-- One opener per file: fd 3 reads "f", fd 4 writes "g", fd 5 is a
directory reference.  Rocq's `flock_model`, as `fixture_of` at the fd and
file-system slots. -/
def flock_model : Model :=
  fixture_of
    (fds := [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
              (3, .FdFile [102] 7), (4, .FdFileW [103] 9), (5, .FdDir) ])
    (fs := [([102], [120]), ([103], [121])])

/-- The same table with a SECOND descriptor on "f" — what a second
`openat` of the same name produces.  Only fd 6 differs. -/
def flock_two_openers_model : Model :=
  fixture_of
    (fds := [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
              (3, .FdFile [102] 7), (4, .FdFileW [103] 9), (5, .FdDir),
              (6, .FdFile [102] 0) ])
    (fs := [([102], [120]), ([103], [121])])

/-- The sole writer's table with a second writable opener on "g".
Both writer tables decline the lock request because lock state and
filesystem identity are unknown. -/
def flock_two_writers_model : Model :=
  fixture_of
    (fds := [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
              (3, .FdFile [102] 7), (4, .FdFileW [103] 9), (5, .FdDir),
              (6, .FdFileW [103] 0) ])
    (fs := [([102], [120]), ([103], [121])])

/-- The four descriptor kinds Rocq's table never needed: fd 3 a fresh
socket, fd 4 the read end of a pipe, fd 5 /dev/null opened read-write, fd 6
/dev/urandom. -/
def flock_kinds_model : Model :=
  fixture_of
    (fds := [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
              (3, .FdSocket .SkFresh), (4, .FdPipe 7 false),
              (5, .FdDevNull true true), (6, .FdUrandom) ])

/-- One closed lookup in the kinds table: fd 6 IS the /dev/urandom entry.
The pins on it below (`ex_on_urandom_is_unmodeled`, its two refutations,
`unlock_on_urandom_is_zero`) are answered identically by a socket, a pipe
end or /dev/null in that slot, so without this line a slip in the fixture
would leave every one of them green while pinning nothing of the kind.
model: a closed `fd_lookup` at a numeral over the fixture table. -/
theorem flock_kinds_model_fd_6 : fd_lookup (m_fds flock_kinds_model) 6 = some .FdUrandom := rfl

/-- The three channels plus the given descriptors, over a file system
holding "f" alone: the table the kind-by-kind pins vary. -/
def flock_openers_model (es : List (word × FdEntry)) : Model :=
  fixture_of
    (fds := [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2) ] ++ es)
    (fs := [([102], [120])])

attribute [sys_simp low]
  flock_model.eq_1 flock_two_openers_model.eq_1 flock_two_writers_model.eq_1 flock_kinds_model.eq_1 flock_openers_model.eq_1

/-! ## Command validation, before the descriptor is resolved

`SYSCALL_DEFINE2(flock)` tests `LOCK_MAND` and translates the operation
before `CLASS(fd, f)(fd)` (fs/locks.c:2153 against :2157, Linux
v6.18.46), so these answers do not depend on the fixture's table. -/

/-- `LOCK_MAND` is tested before the descriptor and answers 0.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem mand_on_open_fd_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 1 32 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem mand_on_open_fd_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 1 32 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The bit is tested, not the whole word, so `LOCK_MAND | LOCK_EX` takes
the same path and answers 0 on a contended table too.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem mand_or_ex_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 34 i flock_two_openers_model o ↔
      o = Ok (mkEffect 0 [] []) flock_two_openers_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem mand_or_ex_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 34 i flock_two_openers_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- `LOCK_MAND | LOCK_READ` is a word the operation switch would refuse,
and the `LOCK_MAND` test comes first: 0, not -EINVAL.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem mand_with_unrecognized_op_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 1 96 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem mand_with_unrecognized_op_einval_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ flock_spec 1 96 i flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-! ## Unrecognized operations on an open descriptor -/

/-- Command 0 falls through the operation switch and returns -EINVAL.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem unrecognized_op_on_open_fd_is_einval (i : SyscallInput)
    (o : outcome SyscallEffect) :
    flock_spec 1 0 i flock_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- …so -EBADF, which fd 1 being open rules out, is refused.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem unrecognized_op_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 1 0 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …nor is an unrecognized operation a no-op: 0 is refused.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem unrecognized_op_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 1 0 i flock_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- `LOCK_NB` alone strips to 0 (`cmd & ~LOCK_NB`, :2153), which is no
operation: -EINVAL on an OPEN file, so the errno is the operation's and
not the descriptor's.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem nb_alone_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 4 i flock_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem nb_alone_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 4 i flock_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- `LOCK_SH|LOCK_EX` (3) is not a `case` of the switch (:454-459): the
operations are an enumeration, not a bit set.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem sh_and_ex_together_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 3 i flock_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem sh_and_ex_together_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 3 i flock_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- `LOCK_READ` (64, fcntl.h:187) sits in the header beside `LOCK_MAND` and
is read by nothing in fs/locks.c at v6.18.46: it reaches the switch as an
ordinary unrecognized word and is -EINVAL (:461).
kernel: fs/locks.c:flock,flock_translate_cmd; include/uapi/asm-generic/fcntl.h:LOCK_READ@v6.18.46 -/
theorem lock_read_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 64 i flock_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem lock_read_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 64 i flock_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- `LOCK_UN|LOCK_EX` (10): the operations are an enumeration, not a bit
set, so a release OR'd with a request matches no `case` of the switch
(:454-459) and is -EINVAL (:461) — neither the unlock nor the lock.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem un_and_ex_together_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 10 i flock_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- A model that read the word as a bit set and honoured the `LOCK_UN` bit
would answer 0.  Refused.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem un_and_ex_together_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 10 i flock_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- Bit 31 is inside the `unsigned int` the syscall takes (:2135), so
`LOCK_EX | 2^31` survives the narrowing and reaches `flock_translate_cmd`
as an `int` (:452) that matches no `case`: -EINVAL (:461).  A model that
tested `LOCK_EX`'s bit alone, or dropped the sign bit, would lock.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem sign_bit_cmd_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 2147483650 i flock_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem sign_bit_cmd_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 2147483650 i flock_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-! ### The three operations are an enumeration, pair by pair

The `switch` has three `case` labels and a `return -EINVAL` past them
(fs/locks.c:452-462, Linux v6.18.46): the operations are VALUES, not
bits, so no OR of two of them is an operation.  Two of the three pairs are
pinned above -- `LOCK_SH|LOCK_EX` (3) and `LOCK_UN|LOCK_EX`
(10, `un_and_ex_together_is_einval`) -- and this is the third, so the claim
is made for each of the three pairs rather than for the one a reader thinks
of first. -/

/-- `LOCK_SH|LOCK_UN` (9) is no `case` of the switch: -EINVAL at :461.
The fd is 3, which is OPEN, so this pin sees the operation check and not
its order against the lookup, which supported kernels do not share
(`badcmd_on_closed_fd_is_unmodeled`).
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem sh_and_un_together_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 9 i flock_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- A kernel reading 9 as "share, then release" translated a word the
switch has no `case` for.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem sh_and_un_together_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 9 i flock_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-! ### What the membership test does not decide, and why no pin can

`flock_cmd_ok_b` asks whether `cmd & ~LOCK_NB` is one of the three
operations and nothing else, so nothing it computes depends on the ORDER
the three constants are written in.  That is not a gap a pin can close.
The mutation sweep over this spec (`tools/lean_mutate.py --spec Fs/Locks`)
exchanges two of the three constants at a time; each exchange permutes the
disjuncts of the one `||` chain and leaves the same Bool function, so the
three survivors it reports are EQUIVALENT MUTANTS, excused in
`tools/lean_mutation/allowlist.Fs.Locks.json` as the same shape
`allowlist.Fs.Timerfd.json` already carries for `timerfd_create_einval_b`.

What those entries rest on is the pins, and the pins are the ones that
fix the SET: an exchange cannot move it, and the set is what the -EINVAL
answers above (0, 3, 4, 9, 10, 64) and the answers that accept a word
(1, 2, 8) pin between them, each going on closing under all three
mutants.  The examples below say the same thing of the gate directly,
word by word, and they are closed computations, so they too are blind to
the order — which is the property that makes them evidence here.

THE TRAP, worth writing down because it is one keystroke away and reads
like a fix: a lemma stating an exchanged chain as an equality with the
original, `flock_cmd_ok_b cmd = (b == LOCK_EX || b == LOCK_SH || b ==
LOCK_UN)`, is TRUE, and closes by a proof term keyed on the disjunct
order.  Under the very mutant it describes, that statement degenerates to
`X = X` and stays true while the proof term stops matching, so the module
fails to elaborate and the sweep reports the mutant KILLED.  This file
carried three such lemmas for one revision (PR #840) and the run turned
green on them; a kill by construction hides the operator's blind spot
instead of recording it, and the blind spot is real — `lean_mutate.py`
skips this exchange for the summands of a `+` chain and not for the
disjuncts of a `||` chain, which is where these three and the ten in
`allowlist.Fs.Timerfd.json` come from.

What the entries do NOT excuse: WHICH command a word is stays pinned, and
elsewhere.  `flock_unlock_b` asks for `LOCK_UN` alone, and the answers
around it separate the release from the two takes — 0 against `Unmodeled`
on the two-opener table.  Each constant's value is pinned against fcntl.h
at the head of this file.  And an edit that changed the set rather than
permuting it fails a pin either way: enlarging it fails the -EINVAL
answers, shrinking it fails the answers that accept the word it dropped. -/

/-- The gate's set, word by word: `flock_translate_cmd`'s three `case`
labels (:454-459) accept, and the words around them fall to :461 — 0 and
`LOCK_NB` alone (4), the three pairs (3, 9, 10), and `LOCK_READ` (64).
Closed Bools, so no permutation of the chain moves any of them.
kernel: fs/locks.c:flock_translate_cmd@v6.18.46 -/
example : flock_cmd_ok_b 1 = true := by decide
/-- kernel: fs/locks.c:flock_translate_cmd@v6.18.46 -/
example : flock_cmd_ok_b 2 = true := by decide
/-- kernel: fs/locks.c:flock_translate_cmd@v6.18.46 -/
example : flock_cmd_ok_b 8 = true := by decide
/-- kernel: fs/locks.c:flock_translate_cmd@v6.18.46 -/
example : flock_cmd_ok_b 0 = false := by decide
/-- `LOCK_NB` alone strips to 0 (`cmd & ~LOCK_NB`, :2153).
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
example : flock_cmd_ok_b 4 = false := by decide
/-- kernel: fs/locks.c:flock_translate_cmd@v6.18.46 -/
example : flock_cmd_ok_b 3 = false := by decide
/-- kernel: fs/locks.c:flock_translate_cmd@v6.18.46 -/
example : flock_cmd_ok_b 9 = false := by decide
/-- kernel: fs/locks.c:flock_translate_cmd@v6.18.46 -/
example : flock_cmd_ok_b 10 = false := by decide
/-- kernel: fs/locks.c:flock_translate_cmd@v6.18.46 -/
example : flock_cmd_ok_b 64 = false := by decide

/-! ## `fd_empty(f)`: -EBADF on a closed descriptor

fs/locks.c:2157-2159 (Linux v6.18.46): `CLASS(fd, f)(fd); if (fd_empty(f))
return -EBADF;`
— the only thing between the operation check and the lock, and reached
for every recognized operation, the unlock included. -/

/-- A recognized operation on a descriptor that is not open is -EBADF.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem closed_fd_ex_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 9999 2 i flock_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) flock_model [] := by
  sys_norm

/-- A closed fd claiming to hold a lock.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem closed_fd_ex_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 9999 2 i flock_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- PRECEDENCE, -EBADF and not -EINVAL: `LOCK_EX` IS recognized, so the
operation check passes and the descriptor check is what answers.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem closed_fd_ex_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 9999 2 i flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The unlock is no exception: `LOCK_UN` on a closed fd is -EBADF, because
:2158 fires before the `type != F_UNLCK` test at :2161 could skip anything.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem closed_fd_un_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 9999 8 i flock_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem closed_fd_un_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 9999 8 i flock_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- `LOCK_SH|LOCK_NB` on a closed fd: the modifier is stripped before the
switch, the operation is recognized, and -EBADF follows.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem closed_fd_sh_nb_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 9999 5 i flock_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem closed_fd_sh_nb_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 9999 5 i flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-! ## `LOCK_UN` on any open descriptor: 0

The `f_mode` test is `type != F_UNLCK && …` (fs/locks.c:2161, Linux
v6.18.46), so an unlock skips it; `locks_lock_file_wait`
(include/linux/filelock.h:425-428, Linux v6.18.46) reaches
`flock_lock_inode` (fs/locks.c:1074-1144, Linux v6.18.46), where a NULL
context is
`return (flc_flags & FL_EXISTS) ? -ENOENT : 0` for an unlock (:1084-1088)
and `FL_EXISTS` is never set by `flock_make_lock` (:465-475); with a
context, the first loop drops only what THIS `struct file` held
(:1101-1109) and `lock_is_unlock` takes `goto out` with `error` still 0
(:1111-1115).  Neither branch reads the locks OTHER files hold. -/

/-- `LOCK_UN` on a directory reference is 0 without the fd kind being
consulted: the kind matters only to a lock request.
kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem unlock_on_dir_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 5 8 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- Neither -EINVAL (the operation is recognized, :458-459) nor -ENOENT
(the `FL_EXISTS` answer at :1087, which flock never requests) nor -EAGAIN
(an unlock reads no conflicting lock) is the kernel's.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem unlock_on_dir_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 5 8 i flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem unlock_on_dir_enoent_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 5 8 i flock_model (Ok (mkEffect (errno_ret ENOENT) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem unlock_on_dir_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 5 8 i flock_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- `LOCK_UN|LOCK_NB` on a channel (the tracer's fd 1) is 0: the modifier
is stripped (:2153), and the object being outside the model does not
matter to an unlock.  `fsync`'s -EINVAL for a channel does not apply —
`flock` has no `.flock` file-operation test that a pipe or tty fails.
kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem unlock_nb_on_channel_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 1 12 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem unlock_nb_on_channel_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 1 12 i flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- fd 1 is open, so the -EBADF of :2158 is a lie.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem unlock_nb_on_channel_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 1 12 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- Releasing a lock that was never taken is 0: the first loop of
`flock_lock_inode` finds nothing for this `struct file` (:1101-1109) and
`lock_is_unlock` leaves `error` at 0 (:1111-1115).
kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem unlock_never_taken_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 8 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem unlock_never_taken_enoent_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 8 i flock_model (Ok (mkEffect (errno_ret ENOENT) [] []) m' evs) := by
  sys_refute

/-- The local unlock path does not inspect another file's lock.
The model keeps this answer under the recorded filesystem premise.
kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem unlock_on_second_opener_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 8 i flock_two_openers_model o ↔
      o = Ok (mkEffect 0 [] []) flock_two_openers_model [] := by
  sys_norm

/-- …so the decline is refused there, and so is -EAGAIN.
kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem unlock_on_second_opener_unmodeled_rejected (i : SyscallInput) :
    ¬ flock_spec 3 8 i flock_two_openers_model Unmodeled := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_lock_inode@v6.18.46 -/
theorem unlock_on_second_opener_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 8 i flock_two_openers_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- The sole opener of "g" is provably uncontended: an FLOCK lock's owner
is the `struct file` (`flock_make_lock` sets `flc_owner = filp`, and
`flock_locks_conflict` returns false when both locks name one file), so
the only conflict the model could build is a second opener.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 2 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 2 i flock_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_eagain_rejected_on_unlock (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 8 i flock_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 2 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_ebadf_rejected_on_unlock (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 8 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 2 i flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_einval_rejected_on_unlock (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 8 i flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_count_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 2 i flock_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_count_rejected_on_unlock (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 8 i flock_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_smuggled_write_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ flock_spec 4 2 i flock_model (Ok (mkEffect 0 [(0, [0])] []) m' evs) := by
  sys_refute

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_smuggled_write_rejected_on_unlock (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ flock_spec 4 8 i flock_model (Ok (mkEffect 0 [(0, [0])] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_smuggled_zeros_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ flock_spec 4 2 i flock_model (Ok (mkEffect 0 [] [(0, 4)]) m' evs) := by
  sys_refute

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_smuggled_zeros_rejected_on_unlock (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ flock_spec 4 8 i flock_model (Ok (mkEffect 0 [] [(0, 4)]) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_event_rejected (i : SyscallInput) (m' : Model) :
    ¬ flock_spec 4 2 i flock_model (Ok (mkEffect 0 [] []) m' [WriteEv 1 0]) := by
  sys_refute

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_event_rejected_on_unlock (i : SyscallInput) (m' : Model) :
    ¬ flock_spec 4 8 i flock_model (Ok (mkEffect 0 [] []) m' [WriteEv 1 0]) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_moved_table_rejected (i : SyscallInput) (evs : List event) :
    ¬ flock_spec 4 2 i flock_model (Ok (mkEffect 0 [] []) (with_fds [] flock_model) evs) := by
  sys_refute

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_opener_moved_table_rejected_on_unlock (i : SyscallInput) (evs : List event) :
    ¬ flock_spec 4 8 i flock_model (Ok (mkEffect 0 [] []) (with_fds [] flock_model) evs) := by
  sys_refute

/-- A shared request on the sole opener of "f" is granted for the same
reason.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem sh_on_sole_opener_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 1 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem sh_on_sole_opener_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 1 i flock_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem sh_on_sole_opener_eagain_rejected_on_unlock (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 8 i flock_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- `LOCK_NB` is stripped before the operation is recognized, so the
nonblocking exclusive request on the sole opener is the same 0.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem ex_nb_on_sole_opener_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 6 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_nb_on_sole_opener_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 6 i flock_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem ex_nb_on_sole_opener_eagain_rejected_on_unlock (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 12 i flock_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_sole_writer_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 2 i flock_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- All four take requests on the two sole openers are granted, with and
without `LOCK_NB`.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem matching_locks_are_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    (flock_spec 3 1 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model []) ∧
    (flock_spec 3 5 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model []) ∧
    (flock_spec 4 2 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model []) ∧
    (flock_spec 4 6 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model []) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_norm

/-- T202: Unlock remains answered on both sole file kinds.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem matching_unlocks_are_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    (flock_spec 3 8 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model []) ∧
    (flock_spec 3 12 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model []) ∧
    (flock_spec 4 8 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model []) ∧
    (flock_spec 4 12 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model []) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_norm

/-- …and none of them answers -EBADF: the descriptor is open, and the
access-mode check that returns -EBADF on an NFS mount refuses only a
mismatched lock type, never these.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode; fs/nfs/nfs4proc.c:nfs4_proc_lock@v6.18.46 -/
theorem matching_grants_and_unlocks_ebadf_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ flock_spec 3 1 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) ∧
    ¬ flock_spec 3 5 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) ∧
    ¬ flock_spec 3 8 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) ∧
    ¬ flock_spec 3 12 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) ∧
    ¬ flock_spec 4 2 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) ∧
    ¬ flock_spec 4 6 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) ∧
    ¬ flock_spec 4 8 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) ∧
    ¬ flock_spec 4 12 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sys_refute

/-! ## A second opener

fd 6 of `flock_two_writers_model` is a second `struct file` on the inode
of "g".  If it holds a lock, `flock_locks_conflict` (:945-948) reports a
conflict and `flock_lock_inode` answers -EAGAIN (:1121-1123) or blocks
(:1124-1126); if it holds none, the answer is 0.  Which one depends on a
lock the model does not record — and could not key, since `dup` and a
reopen produce the same pair of entries — so the intersection of what the
model can prove is empty and `Unmodeled` is the only sound answer. -/

/-- kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_second_writer_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 2 i flock_two_writers_model o ↔ o = Unmodeled := by
  sys_norm

/-- The lock request declines, so it cannot certify the offered 0.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_second_writer_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 2 i flock_two_writers_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The lock request declines independently of the offered errno.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_second_writer_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    flock_spec 4 2 i flock_two_writers_model Unmodeled ∧
      ¬ flock_spec 4 2 i flock_two_writers_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  constructor
  · sys_norm
  · sys_refute

/-! ### Shared locks beside a second opener

`locks_conflict` (fs/locks.c:886-894, Linux v6.18.46) distinguishes
shared and exclusive locks. The model records neither held locks nor
filesystem identity, so both requests decline. -/

/-- The shared request declines because lock ownership and filesystem
identity are unknown.
kernel: fs/locks.c:flock_translate_cmd,flock_make_lock,flock_locks_conflict,locks_conflict,flock_lock_inode@v6.18.46 -/
theorem sh_on_second_opener_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 1 i flock_two_openers_model o ↔ o = Unmodeled := by
  sys_norm

/-- The 0 the kernel gives while fd 6 holds no exclusive lock (:889 and
:891 both fall through, the lock is inserted at :1130-1133) …
kernel: fs/locks.c:flock_locks_conflict,locks_conflict,flock_lock_inode@v6.18.46 -/
theorem sh_on_second_opener_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 1 i flock_two_openers_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The shared request declines independently of the offered errno.
kernel: fs/locks.c:flock,flock_locks_conflict,locks_conflict,flock_lock_inode@v6.18.46 -/
theorem sh_on_second_opener_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 1 i flock_two_openers_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- `sys_flock` reads no `f_mode` on the path to `flock_lock_inode_wait`,
so a read-only description answers both requests the same way: 0.
kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem sh_and_ex_on_read_only_are_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    (flock_spec 3 1 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model []) ∧
    (flock_spec 3 2 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model []) := by
  constructor <;> sys_norm

/-- The nonblocking shared request declines because lock ownership and
filesystem identity are unknown.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_locks_conflict,locks_conflict,flock_lock_inode@v6.18.46 -/
theorem sh_nb_on_second_opener_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 5 i flock_two_openers_model o ↔ o = Unmodeled := by
  sys_norm

/-- Here -EAGAIN IS one of the kernel's two answers (:1121-1123), and it
is refused all the same: committing to it would be wrong on every world
where fd 6 holds nothing or holds a shared lock.
kernel: fs/locks.c:flock_locks_conflict,locks_conflict,flock_lock_inode@v6.18.46 -/
theorem sh_nb_on_second_opener_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 5 i flock_two_openers_model
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- … and so is the 0, the other one.
kernel: fs/locks.c:flock_locks_conflict,locks_conflict,flock_lock_inode@v6.18.46 -/
theorem sh_nb_on_second_opener_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 5 i flock_two_openers_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-! ### The opener count, kind by kind

A sole opener is granted on every file kind; a second descriptor on the
same name declines, whether it is of the same kind or another. -/

/-- kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem sole_file_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0)]) o ↔
      o = Ok (mkEffect 0 [] []) (flock_openers_model [(3, .FdFile [102] 0)]) [] := by
  sys_norm

/-- kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem sole_filew_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 2 i (flock_openers_model [(3, .FdFileW [102] 0)]) o ↔
      o = Ok (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileW [102] 0)]) [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem pair_file_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdFile [102] 5)]) o ↔
      o = Unmodeled := by
  sys_norm

/-- kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem pair_filew_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 2 i (flock_openers_model [(3, .FdFileW [102] 0), (4, .FdFileW [102] 5)]) o ↔
      o = Unmodeled := by
  sys_norm

/-- …and a second descriptor of a DIFFERENT kind contends just the same.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem mixed_filew_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 2 i (flock_openers_model [(3, .FdFileW [102] 0), (4, .FdFile [102] 5)]) o ↔
      o = Unmodeled := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem mixed_file_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdFileW [102] 5)]) o ↔
      o = Unmodeled := by
  sys_norm

/-- A descriptor on ANOTHER name is not an opener of this one, so the
count is still 1 and the request is granted.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem other_name_beside_file_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdFile [103] 5)]) o ↔
      o = Ok (mkEffect 0 [] [])
        (flock_openers_model [(3, .FdFile [102] 0), (4, .FdFile [103] 5)]) [] := by
  sys_norm

/-- `LOCK_UN` on the
very same two-descriptor table still answers 0.
kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem unlock_on_pair_filew_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 8 i (flock_openers_model [(3, .FdFileW [102] 0), (4, .FdFileW [102] 5)]) o ↔
      o = Ok (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileW [102] 0), (4, .FdFileW [102] 5)]) [] := by
  sys_norm

/--
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem pair_filew_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 2 i (flock_openers_model [(3, .FdFileW [102] 0), (4, .FdFileW [102] 5)])
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The lock request declines independently of the offered errno.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem sole_filew_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 2 i (flock_openers_model [(3, .FdFileW [102] 0)])
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem sole_filew_eagain_rejected_on_unlock (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 8 i (flock_openers_model [(3, .FdFileW [102] 0)])
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- `path_openers` walks PAST an `FdUrandom` entry rather than stopping at
it or counting it: the device's inode is no key of `Fs.Fs`, and the one
`FdFile` on "f" listed after it is still counted.
model: a direct pin on the helper the grant arms of `flock_spec` consult. -/
theorem path_openers_skips_urandom :
    path_openers [(3, .FdUrandom), (4, .FdFile [102] 0)] [102] = 1 := rfl

/-! ### `path_openers` read directly

`flock_sole_opener` is the gate of every grant arm, and `path_openers` is
the count it reads; these pins fix the walk on the helper itself, where
one table says what a whole family of syscall pins would.  In each
file-kind table, two entries name "f" and one names "g": a test that
counted every entry gives 3, one that counted none gives 0, and an
exchanged test gives 1.  In each skipped-kind table, the skipped entry
comes first and two openers of "f" follow it: a walk that stopped there
gives 0 or 1, not 2. -/

/-- An `FdFile` counts exactly when it names the path.
model: a direct pin on the helper the grant arms of `flock_spec` consult. -/
theorem path_openers_file_counts_its_path :
    path_openers [(3, .FdFile [102] 0), (4, .FdFile [103] 0), (5, .FdFile [102] 0)] [102] = 2 := by
  decide

/-- An `FdFileW` counts exactly when it names the path.
model: a direct pin on the helper the grant arms of `flock_spec` consult. -/
theorem path_openers_filew_counts_its_path :
    path_openers [(3, .FdFileW [102] 0), (4, .FdFileW [103] 0), (5, .FdFileW [102] 0)] [102] = 2 := by
  decide

/-- An `FdFileA` counts exactly when it names the path.
model: a direct pin on the helper the grant arms of `flock_spec` consult. -/
theorem path_openers_filea_counts_its_path :
    path_openers [(3, .FdFileA [102] 0), (4, .FdFileA [103] 0), (5, .FdFileA [102] 0)] [102] = 2 := by
  decide

/-- An `FdFileRW` counts exactly when it names the path.
model: a direct pin on the helper the grant arms of `flock_spec` consult. -/
theorem path_openers_filerw_counts_its_path :
    path_openers [(3, .FdFileRW [102] 0), (4, .FdFileRW [103] 0), (5, .FdFileRW [102] 0)] [102] = 2 := by
  decide

/-- The walk passes an `FdChannel` and counts both openers after it.
model: a direct pin on the helper the grant arms of `flock_spec` consult. -/
theorem path_openers_walks_past_channel :
    path_openers [(0, .FdChannel 0), (3, .FdFile [102] 0), (4, .FdFile [102] 0)] [102] = 2 := by
  decide

/-- The walk passes an `FdDir` and counts both openers after it.
model: a direct pin on the helper the grant arms of `flock_spec` consult. -/
theorem path_openers_walks_past_dir :
    path_openers [(0, .FdDir), (3, .FdFile [102] 0), (4, .FdFile [102] 0)] [102] = 2 := by
  decide

/-- The walk passes an `FdSocket` and counts both openers after it.
model: a direct pin on the helper the grant arms of `flock_spec` consult. -/
theorem path_openers_walks_past_socket :
    path_openers [(0, .FdSocket .SkFresh), (3, .FdFile [102] 0), (4, .FdFile [102] 0)] [102] = 2 := by
  decide

/-- The walk passes an `FdPipe` and counts both openers after it.
model: a direct pin on the helper the grant arms of `flock_spec` consult. -/
theorem path_openers_walks_past_pipe :
    path_openers [(0, .FdPipe 7 false), (3, .FdFile [102] 0), (4, .FdFile [102] 0)] [102] = 2 := by
  decide

/-- The walk passes an `FdDevNull` and counts both openers after it.
model: a direct pin on the helper the grant arms of `flock_spec` consult. -/
theorem path_openers_walks_past_devnull :
    path_openers [(0, .FdDevNull true true), (3, .FdFile [102] 0), (4, .FdFile [102] 0)] [102] = 2 := by
  decide

/-- The walk passes an `FdUrandom` and counts both openers after it.
model: a direct pin on the helper the grant arms of `flock_spec` consult. -/
theorem path_openers_walks_past_urandom_to_two :
    path_openers [(0, .FdUrandom), (3, .FdFile [102] 0), (4, .FdFile [102] 0)] [102] = 2 := by
  decide

/-- A /dev/urandom descriptor is no opener of "f", so the file is still
the sole opener and the request is granted.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem urandom_beside_file_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdUrandom)]) o ↔
      o = Ok (mkEffect 0 [] [])
        (flock_openers_model [(3, .FdFile [102] 0), (4, .FdUrandom)]) [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem urandom_does_not_hide_a_second_opener (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdUrandom), (5, .FdFile [102] 5)]) o
      ↔ o = Unmodeled := by
  sys_norm

/-- A socket is no opener of "f" either.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem sole_file_beside_socket_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 1 i (flock_openers_model [(3, .FdSocket .SkFresh), (4, .FdFile [102] 0)]) o ↔
      o = Ok (mkEffect 0 [] [])
        (flock_openers_model [(3, .FdSocket .SkFresh), (4, .FdFile [102] 0)]) [] := by
  sys_norm

/-- Nor is a pipe end.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem sole_file_beside_pipe_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 1 i (flock_openers_model [(3, .FdPipe 7 false), (4, .FdFile [102] 0)]) o ↔
      o = Ok (mkEffect 0 [] [])
        (flock_openers_model [(3, .FdPipe 7 false), (4, .FdFile [102] 0)]) [] := by
  sys_norm

/-- Nor is a directory reference.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem sole_file_beside_dir_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 1 i (flock_openers_model [(3, .FdDir), (4, .FdFile [102] 0)]) o ↔
      o = Ok (mkEffect 0 [] [])
        (flock_openers_model [(3, .FdDir), (4, .FdFile [102] 0)]) [] := by
  sys_norm

/-- Nor is /dev/null.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem sole_file_beside_devnull_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 1 i (flock_openers_model [(3, .FdDevNull true true), (4, .FdFile [102] 0)]) o ↔
      o = Ok (mkEffect 0 [] [])
        (flock_openers_model [(3, .FdDevNull true true), (4, .FdFile [102] 0)]) [] := by
  sys_norm

/-- The same with the socket listed after the file.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem socket_beside_file_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdSocket .SkFresh)]) o ↔
      o = Ok (mkEffect 0 [] [])
        (flock_openers_model [(3, .FdFile [102] 0), (4, .FdSocket .SkFresh)]) [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem socket_beside_opener_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdSocket .SkFresh)])
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem socket_beside_opener_eagain_rejected_on_unlock (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 8 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdSocket .SkFresh)])
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- The same with the pipe end listed after the file.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem pipe_end_beside_file_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdPipe 7 false)]) o ↔
      o = Ok (mkEffect 0 [] [])
        (flock_openers_model [(3, .FdFile [102] 0), (4, .FdPipe 7 false)]) [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem pipe_end_beside_opener_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdPipe 7 false)])
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem pipe_end_beside_opener_eagain_rejected_on_unlock (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 8 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdPipe 7 false)])
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- The same with /dev/null listed after the file.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem devnull_beside_file_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdDevNull true true)]) o ↔
      o = Ok (mkEffect 0 [] [])
        (flock_openers_model [(3, .FdFile [102] 0), (4, .FdDevNull true true)]) [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem devnull_beside_opener_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdDevNull true true)])
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- T202: Keep the refusal on an answered unlock as well.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem devnull_beside_opener_eagain_rejected_on_unlock (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 8 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdDevNull true true)])
        (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem socket_does_not_hide_a_second_opener (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdSocket .SkFresh), (5, .FdFile [102] 5)]) o
      ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem socket_hiding_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdSocket .SkFresh), (5, .FdFile [102] 5)])
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem pipe_end_does_not_hide_a_second_opener (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdPipe 7 false), (5, .FdFile [102] 5)]) o
      ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem pipe_end_hiding_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdPipe 7 false), (5, .FdFile [102] 5)])
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem devnull_does_not_hide_a_second_opener (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdDevNull true true), (5, .FdFile [102] 5)]) o
      ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem devnull_hiding_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 1 i (flock_openers_model [(3, .FdFile [102] 0), (4, .FdDevNull true true), (5, .FdFile [102] 5)])
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem pair_after_socket_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 1 i (flock_openers_model [(3, .FdSocket .SkFresh), (4, .FdFile [102] 0), (5, .FdFile [102] 5)]) o
      ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem pair_after_pipe_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 1 i (flock_openers_model [(3, .FdPipe 7 false), (4, .FdFile [102] 0), (5, .FdFile [102] 5)]) o
      ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem pair_after_devnull_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 1 i (flock_openers_model [(3, .FdDevNull true true), (4, .FdFile [102] 0), (5, .FdFile [102] 5)]) o
      ↔ o = Unmodeled := by
  sys_norm

/-! ## The other descriptor kinds decline a lock request

Each for its own reason (`Sys/Fs/Locks.lean`'s `flock_spec`, and Rocq's in
full).  Every one is a shape where the kernel's answer — 0, or -EAGAIN /
blocking at :1121-1126 — depends on a second `struct file` the model
cannot rule out or does not represent, so no single answer is provable and
`Unmodeled` is the only sound one.  Each pin is paired with the refusal of
the 0 a model that ignored the question would give. -/

/-- A directory reference: "." and ".." are one constructor, so two
`openat(".")` descriptors — two `struct file`s on one inode — cannot be
told from one.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_dir_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 5 2 i flock_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_dir_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 5 2 i flock_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A channel: the object is not in the model, and two channels may or may
not be two ends of one pipe, which is exactly what an inode-scoped lock
asks.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_channel_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 1 2 i flock_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_channel_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 1 2 i flock_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- Not `fsync`'s -EINVAL either: `flock` has no file-operation test a
channel fails, so a decline is the only honest answer and an errno is a
lie.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem ex_on_channel_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 1 2 i flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A socket: sockfs gives every socket its own inode, so the conflicting
pair is not constructible and the answer would be 0 — by an argument
about `sock_alloc`, not fs/locks.c, and no caller wants it.  Declined.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_socket_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 2 i flock_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_socket_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 2 i flock_kinds_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A pipe end: both ends of one pipe share an inode and are two `struct
file`s, so `pipe2` alone builds the conflicting pair.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_pipe_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 2 i flock_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_pipe_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 2 i flock_kinds_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The model records no device lock state, so this request declines.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_devnull_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 5 2 i flock_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_devnull_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 5 2 i flock_kinds_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The model records no device lock state, so this request declines.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_urandom_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 6 2 i flock_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_urandom_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 6 2 i flock_kinds_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and so is the -EAGAIN of a conflict the model cannot see (:1121): the
decline commits to neither answer, so neither the 0 of a model that ignored
a second opener of the device nor the -EAGAIN of one that assumed one is
admitted.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict,flock_lock_inode@v6.18.46 -/
theorem ex_on_urandom_eagain_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 6 2 i flock_kinds_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- The unlock is answered on all four, as on every open descriptor.
kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem unlock_on_socket_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 8 i flock_kinds_model o ↔ o = Ok (mkEffect 0 [] []) flock_kinds_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem unlock_on_pipe_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 8 i flock_kinds_model o ↔ o = Ok (mkEffect 0 [] []) flock_kinds_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem unlock_on_devnull_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 5 8 i flock_kinds_model o ↔ o = Ok (mkEffect 0 [] []) flock_kinds_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem unlock_on_urandom_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 6 8 i flock_kinds_model o ↔ o = Ok (mkEffect 0 [] []) flock_kinds_model [] := by
  sys_norm

/-! ## The dispatcher: `flock` is number 32, and both arguments are 32 bits

`SYSCALL_DEFINE2(flock, unsigned int, fd, unsigned int, cmd)`
(fs/locks.c:2135, Linux v6.18.46): both registers are narrowed to their low 32 bits
(`Syscall.fd32`, `Syscall.cmd32`) before anything above runs, so
`fd | 2^32` is `fd` and `2^32 | LOCK_UN` is `LOCK_UN`. -/

/-- kernel: include/uapi/asm-generic/unistd.h:__NR_flock@v6.18.46 -/
theorem flock_is_dispatched : (32 : Int) ∈ modeled_sysnos := by decide

/-- fd `2^32 + 3` is fd 3 and cmd `2^32 + 8` is `LOCK_UN`: truncation
aliases, it does not reject.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem truncated_fd_and_cmd_alias (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 32 [0x100000003, 0x100000008] (fun _ => none) (fun _ => none))
        flock_model o ↔
      o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- A full-register model would answer -EBADF (no fd `2^32 + 3`) or -EINVAL
(no operation `2^32 + 8`); both are refused.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem truncated_fd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 32 [0x100000003, 0x100000008] (fun _ => none) (fun _ => none))
        flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem truncated_cmd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 32 [0x100000003, 0x100000008] (fun _ => none) (fun _ => none))
        flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and truncation does not invent live fds: `2^32 + 9999` is 9999, which
is closed, and -EBADF.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem truncated_wild_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 32 [0x10000270F, 2] (fun _ => none) (fun _ => none))
        flock_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem truncated_wild_fd_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 32 [0x10000270F, 2] (fun _ => none) (fun _ => none))
        flock_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- Through the table: bit 31 of a1 is INSIDE the low 32 bits, so
`Syscall.cmd32` keeps it and the word is still unrecognised — -EINVAL on
the open file, not the lock a model that narrowed to 31 bits would take.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem sign_bit_cmd_survives_narrowing (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 32 [3, 0x80000002] (fun _ => none) (fun _ => none))
        flock_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-! ## The command word is judged before the descriptor -/

/-- `LOCK_MAND` on a CLOSED fd is still 0: the bit is tested first of all
(fs/locks.c, `SYSCALL_DEFINE2(flock)`, Linux v6.18.46), and what replaced
mandatory flocks is a successful no-op, so no lookup happens and -EBADF
cannot arise.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem mand_on_closed_fd_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 9999 32 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- A model that translated the operation before testing the bit would
answer -EINVAL here; that answer is refused.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem mand_on_closed_fd_einval_refuted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 9999 32 i flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and a model that resolved the descriptor first would answer -EBADF,
which is refused as well.
probe: testing/syscall-check/tests/flock_spec.c#fail-closed --expect-unmodeled flock -- mandclosed
kernel: fs/locks.c:flock@v6.18.46 -/
theorem mand_on_closed_fd_ebadf_refuted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 9999 32 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- An unrecognized operation on a closed fd is -EINVAL, not -EBADF:
`flock_translate_cmd` falls off its switch (fs/locks.c:452-462, Linux
v6.18.46) before `CLASS(fd, f)(fd)` resolves the descriptor.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem badcmd_on_closed_fd_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 9999 0 i flock_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- The 0 of the `LOCK_MAND` arm is not this word's answer.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem badcmd_on_closed_fd_zero_refuted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 9999 0 i flock_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and the -EBADF a lookup-first order would give is refused.
probe: testing/syscall-check/tests/flock_spec.c#fail-closed --expect-unmodeled flock -- badcmdclosed
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem badcmd_on_closed_fd_ebadf_refuted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 9999 0 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The -EINVAL is on every unrecognized word, not operation 0 alone:
`LOCK_SH|LOCK_EX` is one word the switch has no label for.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem combined_op_on_closed_fd_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 9999 3 i flock_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- …so the -EBADF a lookup-first order would give is refused here too.
probe: testing/syscall-check/tests/flock_spec.c#fail-closed --expect-unmodeled flock -- combinedclosed
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem combined_op_on_closed_fd_ebadf_refuted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 9999 3 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- `LOCK_UN|LOCK_EX` is unrecognized whole, so -EINVAL as well.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem unlock_ex_on_closed_fd_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 9999 10 i flock_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- …and its -EBADF is not an outcome.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem unlock_ex_on_closed_fd_ebadf_refuted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 9999 10 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- `LOCK_EX` with bit 31 set is unrecognized whole (the translation
compares the full `cmd & ~LOCK_NB`), so -EINVAL.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem sign_bit_op_on_closed_fd_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 9999 0x80000002 i flock_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- …and its -EBADF is not an outcome.
probe: testing/syscall-check/tests/flock_spec.c#fail-closed --expect-unmodeled flock -- highcmdclosed -/
theorem sign_bit_op_on_closed_fd_ebadf_refuted (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 9999 0x80000002 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem mand_eagain_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 1 32 i flock_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem mand_einval_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 1 32 i flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock@v6.18.46 -/
theorem mand_ebadf_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 1 32 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- An exclusive request through a READ-ONLY description: `sys_flock`
reads no `f_mode`, so the sole opener is granted.
kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem ro_ex_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 2 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem ro_ex_eagain_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 2 i flock_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/nfs/nfs4proc.c:nfs4_proc_lock@v6.18.46 -/
theorem ro_ex_einval_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 2 i flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/nfs/nfs4proc.c:nfs4_proc_lock@v6.18.46 -/
theorem ro_ex_ebadf_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 2 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem ro_ex_nb_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 6 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem ro_ex_nb_eagain_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 6 i flock_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/nfs/nfs4proc.c:nfs4_proc_lock@v6.18.46 -/
theorem ro_ex_nb_einval_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 6 i flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/nfs/nfs4proc.c:nfs4_proc_lock@v6.18.46 -/
theorem ro_ex_nb_ebadf_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 3 6 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- A shared request through a WRITE-ONLY description: the same, 0.
kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem wo_sh_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 1 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem wo_sh_eagain_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 1 i flock_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/nfs/nfs4proc.c:nfs4_proc_lock@v6.18.46 -/
theorem wo_sh_einval_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 1 i flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/nfs/nfs4proc.c:nfs4_proc_lock@v6.18.46 -/
theorem wo_sh_ebadf_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 1 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/locks.c:flock,flock_lock_inode_wait@v6.18.46 -/
theorem wo_sh_nb_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 5 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- kernel: fs/locks.c:flock_lock_inode@v6.18.46 -/
theorem wo_sh_nb_eagain_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 5 i flock_model (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/nfs/nfs4proc.c:nfs4_proc_lock@v6.18.46 -/
theorem wo_sh_nb_einval_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 5 i flock_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- kernel: fs/nfs/nfs4proc.c:nfs4_proc_lock@v6.18.46 -/
theorem wo_sh_nb_ebadf_is_not_an_answer (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ flock_spec 4 5 i flock_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The `LOCK_MAND` answer does not depend on the descriptor's kind: the
bit is read before the table is.
kernel: fs/locks.c:flock@v6.18.46 -/
theorem mand_on_any_fd_kind_is_zero (e : FdEntry) (i : SyscallInput)
    (o : outcome SyscallEffect) :
    flock_spec 3 32 i (flock_openers_model [(3, e)]) o ↔
      o = Ok (mkEffect 0 [] []) (flock_openers_model [(3, e)]) [] := by
  sys_norm

/-! ## A17: FdFileRW and FdFileA -/

def a17_locks_model : Model :=
  fixture_of (fds := [(3, .FdFileRW [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_locks_model.eq_1

/-- Rocq: `Locks.path_openers`, Locks.v:78 at 96c2debdb.
Both descriptions count: fs/locks.c, flock_make_lock, Linux v6.18.46
sets flc_owner to filp, so two opens of one path can contend.
kernel: fs/locks.c:flock_make_lock@v6.18.46 -/
theorem a17_rdwr_counts_as_opener :
    path_openers [(3, .FdFileRW [102] 0), (5, .FdFileRW [103] 0),
      (4, .FdFile [102] 0)] [102] = 2 := by
  decide

/-- `flock(LOCK_SH)` through a read-write file is granted on the sole
opener: a regular file's lock is on the inode and the access mode is not
one of its inputs.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem a17_rdwr_flock_is_zero (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 32 [3, 1, 0, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_locks_model o ↔
      o = Ok (mkEffect 0 [] []) a17_locks_model [] := by
  sys_norm

/-- `flock(LOCK_EX)` through a read-write file is granted too.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem a17_rdwr_flock_ex_is_zero (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_locks_model o ↔
      o = Ok (mkEffect 0 [] []) a17_locks_model [] := by
  sys_norm

def a17_locks_two_openers_model : Model :=
  fixture_of (fds := [(3, .FdFile [102] 0), (4, .FdFileRW [102] 0)])
    (fs := [([102], [120])])

attribute [sys_simp low] a17_locks_two_openers_model.eq_1

/-- The read-only opener cannot be assumed uncontended beside a read-write
opener: fs/locks.c, flock_make_lock, Linux v6.18.46 sets flc_owner to
filp, so the second description can own a conflicting lock.
kernel: fs/locks.c:flock_make_lock@v6.18.46 -/
theorem a17_file_beside_rdwr_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 32 [3, 1, 0, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_locks_two_openers_model o ↔ o = Unmodeled := by
  sys_norm

/-- `LOCK_UN` through a read-write file answers 0 beside a second opener
of its path, as Rocq's arm does: `flock_spec` answers an unlock ahead of
the kind match, so the read-write decline never reaches it.  A mutant
that moved the decline ahead of the unlock fails here.
kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem a17_rdwr_unlock_on_pair_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 8 i (flock_openers_model [(3, .FdFileRW [102] 0), (4, .FdFileRW [102] 5)]) o ↔
      o = Ok (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileRW [102] 0), (4, .FdFileRW [102] 5)]) [] := by
  sys_norm

def a17_locks_append_model : Model :=
  fixture_of (fds := [(3, .FdFileA [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_locks_append_model.eq_1

/-- Rocq: `Locks.path_openers`, Locks.v:77 at 96c2debdb.
The append-mode description counts, and the scan passes an unrelated one to
reach the read-only opener: fs/locks.c, flock_make_lock, Linux v6.18.46
sets flc_owner to filp, so two opens of one path can contend.
kernel: fs/locks.c:flock_make_lock@v6.18.46 -/
theorem a17_append_counts_as_opener :
    path_openers [(3, .FdFileA [102] 0), (5, .FdFileA [103] 0),
      (4, .FdFile [102] 0)] [102] = 2 := by
  decide

/-- `flock(LOCK_EX)` through an append-mode file is granted on the sole
opener: O_APPEND decides where a write lands, not which `->flock` the
inode has.
kernel: fs/locks.c:flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem a17_append_flock_is_zero (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_locks_append_model o ↔
      o = Ok (mkEffect 0 [] []) a17_locks_append_model [] := by
  sys_norm

def a17_locks_two_openers_append_model : Model :=
  fixture_of (fds := [(3, .FdFile [102] 0), (4, .FdFileA [102] 0)])
    (fs := [([102], [120])])

attribute [sys_simp low] a17_locks_two_openers_append_model.eq_1

/-- The read-only opener cannot be assumed uncontended beside an append-mode
opener: fs/locks.c, flock_make_lock, Linux v6.18.46 sets flc_owner to
filp, so the second description can own a conflicting lock.
kernel: fs/locks.c:flock_make_lock@v6.18.46 -/
theorem a17_file_beside_append_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 32 [3, 1, 0, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_locks_two_openers_append_model o ↔ o = Unmodeled := by
  sys_norm

/-- `LOCK_UN` through an append-mode file answers 0 beside a second
opener of its path, as Rocq's arm does: `flock_spec` answers an unlock
ahead of the kind match, so the append-mode decline never reaches it.  A
mutant that moved the decline ahead of the unlock fails here.
kernel: fs/locks.c:flock,flock_lock_inode,locks_get_lock_context; include/linux/filelock.h:locks_lock_file_wait@v6.18.46 -/
theorem a17_append_unlock_on_pair_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 8 i (flock_openers_model [(3, .FdFileA [102] 0), (4, .FdFileA [102] 5)]) o ↔
      o = Ok (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileA [102] 0), (4, .FdFileA [102] 5)]) [] := by
  sys_norm

/-- `LOCK_SH` and `LOCK_SH | LOCK_NB` on a sole append-mode opener are
granted: the append-mode arm counts openers like the other three file
arms, and `sys_flock` reads no `f_mode`.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem a17_append_sh_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    (flock_spec 3 1 i (flock_openers_model [(3, .FdFileA [102] 0)]) o ↔
      o = Ok (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileA [102] 0)]) []) ∧
    (flock_spec 3 5 i (flock_openers_model [(3, .FdFileA [102] 0)]) o ↔
      o = Ok (mkEffect 0 [] []) (flock_openers_model [(3, .FdFileA [102] 0)]) []) := by
  refine ⟨?_, ?_⟩ <;> sys_norm

/-- …and none of -EINVAL, -EBADF and -EAGAIN is admitted for either word
on that opener: the operation is recognized, the descriptor is open, and
the sole opener cannot conflict with itself.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem a17_append_sh_errnos_are_not_answers (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ flock_spec 3 1 i (flock_openers_model [(3, .FdFileA [102] 0)]) (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) ∧
    ¬ flock_spec 3 1 i (flock_openers_model [(3, .FdFileA [102] 0)]) (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) ∧
    ¬ flock_spec 3 1 i (flock_openers_model [(3, .FdFileA [102] 0)]) (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) ∧
    ¬ flock_spec 3 5 i (flock_openers_model [(3, .FdFileA [102] 0)]) (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) ∧
    ¬ flock_spec 3 5 i (flock_openers_model [(3, .FdFileA [102] 0)]) (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) ∧
    ¬ flock_spec 3 5 i (flock_openers_model [(3, .FdFileA [102] 0)]) (Ok (mkEffect (errno_ret EAGAIN) [] []) m' evs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sys_refute

/-- The nonblocking shared request on the sole read-only opener is
granted, as the blocking one is: `LOCK_NB` is stripped before the
operation is recognized and changes no answer the model gives.
kernel: fs/locks.c:flock,flock_make_lock,flock_locks_conflict@v6.18.46 -/
theorem t202_ro_sh_nb_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 5 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- T202: Retain unlock under the recorded filesystem premise.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_unlock_on_sole_filew_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 4 8 i flock_model o ↔ o = Ok (mkEffect 0 [] []) flock_model [] := by
  sys_norm

/-- T202: Extra command bits survive validation; LOCK_UN controls expose a dropped bit.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_sign_bit_unlock_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 0x80000008 i flock_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- T202: Extra command bits survive validation; these words carry LOCK_EX and an invalid extra bit.
The fd-1 answer uses linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_extra_42_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 1 0x42 i flock_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- T202: Extra command bits survive validation; these words carry LOCK_EX and an invalid extra bit.
The fd-1 answer uses linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_extra_82_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 1 0x82 i flock_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- T202: Extra command bits survive validation; these words carry LOCK_EX and an invalid extra bit.
The fd-1 answer uses linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_extra_10002_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 1 0x10002 i flock_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- T202: Extra command bits survive validation; LOCK_UN controls expose a dropped bit.
The fd-1 answer uses linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_extra_48_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 1 0x48 i flock_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- T202: Extra command bits survive validation; LOCK_UN controls expose a dropped bit.
The fd-1 answer uses linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_extra_88_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 1 0x88 i flock_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- T202: Extra command bits survive validation; LOCK_UN controls expose a dropped bit.
The fd-1 answer uses linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_extra_10008_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 1 0x10008 i flock_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- An unrecognized word on a closed descriptor is -EINVAL: the
translation runs before the lookup.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem t202_closed_extra_ex_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 9999 0x42 i flock_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- T202: A 31-bit command mask would turn this into an answered unlock.
kernel: fs/locks.c:flock,flock_translate_cmd,flock_lock_inode@v6.18.46 -/
theorem t202_sign_bit_unlock_zero_refuted (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ flock_spec 3 0x80000008 i flock_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- T202: A 31-bit dispatcher mask would turn this into an answered unlock.
kernel: fs/locks.c:flock,flock_translate_cmd; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem t202_sign_bit_unlock_survives_narrowing (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 32 [3, 0x80000008] (fun _ => none) (fun _ => none))
        flock_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- The file descriptor avoids the channel-direction premise.
Extra command bits still make this operation invalid.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem t202_file_extra_42_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 0x42 i flock_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

/-- The file descriptor avoids the channel-direction premise.
Extra command bits still make this operation invalid.
kernel: fs/locks.c:flock,flock_translate_cmd@v6.18.46 -/
theorem t202_file_extra_48_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    flock_spec 3 0x48 i flock_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) flock_model [] := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Locks
