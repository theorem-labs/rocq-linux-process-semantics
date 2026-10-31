import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Fs.Fcntl — what `fcntl` admits, read off against Linux

Worked examples over `Sys.Fs.Fcntl.fcntl_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Fs/Fcntl.v`.  Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about what the kernel does, with
the citation beside it.

HOW THESE ARE STATED.  Every call goes through the dispatcher —
`syscall_spec` on a `SyscallInput` numbered 25 — so that the table's
`fd32`/`cmd32` narrowing is under test with the arm, as Rocq's
`check_syscall (mkInput 25 …)` cases have it.  A decision is pinned twice:
an `iff` over EVERY outcome `o`, which fixes the admitted answer and refuses
every other one, `Unmodeled` included; and a refutation of the concrete
answer a wrong model or a lying kernel would give — the errno of the
neighbouring arm, the flag word qemu-user reports on a glibc host, the 0 a
wildcard
would have answered.  Both close by `sys_norm` / `sys_refute`.

A DECLINE HERE IS A COVERAGE GAP, NOT AN EMPTY INTERSECTION.  Every
`Unmodeled` below is one Linux answers with a definite value that the
model has no state to derive — a flag word `openat` discarded, a
close-on-exec bit nothing records, a non-blocking mode that does not
exist — and the pins that offer the kernel's own value and still require
`Unmodeled` are what keep a later arm from turning a gap into a guess:
the arm that closes one has to land the state first.  The one decline
that is a CHOICE rather than a gap is the pipe end, and its pins say so.

Rocq's `fcntl_append_model` and `fcntl_flag_commands_decline_on_an_append_fd`
are restated at the end of this file, one pin per conjunct, beside the pins
on the `FdFileA` arms themselves.  `fcntl_setfl_on_a_pipe_end_declines`
from Rocq's `Checks/Cases/Fs/Pipe.v` is pinned HERE instead, since the
arm it reads is this file's and no Lean pipe case file exists.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Fcntl

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Fcntl
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The register line the spec owes `sys_simp`

`Checks/Cases/Tactic.lean`'s header asks each spec for its unfolding
equation in the set; it is registered here, beside the pins that read it,
rather than in that file's register, because this port edits only its
own two files.  Moving the line there is a one-line change. -/

attribute [sys_simp low] fcntl_spec.eq_1

/-! ## The constants these checks spell out

Kept as numerals in the statements so a reader sees the register value the
program passes; these pins say what each one is. -/

/-- F_GETFD, the cmd the close-on-exec getter pins spell as 1.
model: the model's own `word` constant at the numeral the statements spell; the header reading is `fcntl_commands` in `Checks/Cases/Sys/Uapi/Fs.lean`. -/
example : F_GETFD = 1 := by decide
/-- F_SETFD, the cmd the close-on-exec setter pins spell as 2.
model: the model's own `word` constant at the numeral the statements spell; the header reading is `fcntl_commands` in `Checks/Cases/Sys/Uapi/Fs.lean`. -/
example : F_SETFD = 2 := by decide
/-- F_GETFL, the cmd the status-flag getter pins spell as 3.
model: the model's own `word` constant at the numeral the statements spell; the header reading is `fcntl_commands` in `Checks/Cases/Sys/Uapi/Fs.lean`. -/
example : F_GETFL = 3 := by decide
/-- F_SETFL, the cmd the status-flag setter pins spell as 4.
model: the model's own `word` constant at the numeral the statements spell; the header reading is `fcntl_commands` in `Checks/Cases/Sys/Uapi/Fs.lean`. -/
example : F_SETFL = 4 := by decide
/-- O_LARGEFILE, the bit musl ORs into every F_SETFL it issues and the
high half of every path-opened fd's flag word below.
kernel: include/uapi/asm-generic/fcntl.h:O_LARGEFILE@v6.18.46 -/
example : O_LARGEFILE = 32768 := by decide
/-- O_RDWR, the whole of a socket's flag word.
kernel: include/uapi/asm-generic/fcntl.h:O_RDWR@v6.18.46 -/
example : O_RDWR = 2 := by decide

/-- The mask, as the five bits `setfl` reads (fs/fcntl.c:39-89, Linux
v6.18.46, commit 1f99e9ab748f): 1024 + 2048 + 8192 + 16384 + 262144.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:O_APPEND,O_NONBLOCK,FASYNC,O_DIRECT,O_NOATIME@v6.18.46 -/
theorem setfl_acted_on_is_289792 : setfl_acted_on = 289792 := by decide

/-- …and it is NOT `SETFL_MASK` (fs/fcntl.c:37, Linux v6.18.46): FASYNC
(8192) is in the mask here and absent from the macro, whose value on this
ABI is 281600.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:O_APPEND,O_NONBLOCK,O_DIRECT,O_NOATIME,FASYNC@v6.18.46 -/
theorem setfl_acted_on_is_not_SETFL_MASK :
    setfl_acted_on ≠ O_APPEND + O_NONBLOCK + O_DIRECT + O_NOATIME := by decide

/-- A socket's whole `f_flags` word is O_RDWR: `sock_alloc_file` builds
the file from `O_RDWR | (flags & O_NONBLOCK)` (net/socket.c:483-485,
Linux v6.18.46), and every modeled socket declined SOCK_NONBLOCK.
kernel: net/socket.c:sock_alloc_file; include/uapi/asm-generic/fcntl.h:O_RDWR@v6.18.46 -/
theorem socket_f_flags_is_2 : socket_f_flags = 2 := by decide

/-! ## The fixture and the call -/

/-- Rocq's `fcntl_model`: two channels, a read-only file, a write-only
file, a directory, a fresh socket and both ends of a pipe, over a file
system holding "hi" at path `[102]`.  fd 2 and fd 9 are deliberately
absent: 9 is the closed fd the -EBADF pins name. -/
def fcntl_fds : List (word × FdEntry) :=
  [(0, .FdChannel 0), (1, .FdChannel 1), (3, .FdFile [102] 0), (4, .FdFileW [103] 0),
   (5, .FdDir), (6, .FdSocket .SkFresh), (7, .FdPipe 0 false), (8, .FdPipe 0 true)]

def fcntl_model : Model := fixture_of (fds := fcntl_fds) (fs := [([102], [104, 105])])

/-- The same table with /dev/null open read-write at fd 11: the kind Rocq's
case file does not put through the arms, pinned here because both matches
in `Sys.Fs.Fcntl` have an arm for it. -/
def fcntl_devnull_model : Model :=
  fixture_of (fds := (11, .FdDevNull true true) :: fcntl_fds) (fs := [([102], [104, 105])])

/-- The same table with /dev/urandom at fd 12: the second device kind, put
through the same two arms as /dev/null.
model: a fixture; what it pins is stated on the theorems that read it. -/
def fcntl_urandom_model : Model :=
  fixture_of (fds := (12, .FdUrandom) :: fcntl_fds) (fs := [([102], [104, 105])])

/-- `fcntl(fd, cmd, arg)` as the dispatcher sees it: syscall 25, the three
arguments in a0..a2, nothing readable or writable. -/
def fcntl_in (fd cmd arg : word) : SyscallInput :=
  SyscallInput.mkInput 25 [fd, cmd, arg, 0, 0, 0] (fun _ => none) (fun _ => none)

attribute [sys_simp low] fcntl_in.eq_1

/-! ## The fd is resolved before the command

`SYSCALL_DEFINE3(fcntl, …)` (fs/fcntl.c:574-592, Linux v6.18.46, commit
1f99e9ab748f) runs `CLASS(fd_raw, f)(fd)` and answers -EBADF on
`fd_empty(f)` (:576-580) before `do_fcntl` (:444-557) ever switches on
`cmd`. -/

/-- A cmd the kernel does not recognise (57005 = 0xdead), on an fd that is
NOT open, is -EBADF and nothing else: not `do_fcntl`'s `default:` -EINVAL
(:450, :553-555), which a closed fd never reaches, and not `Unmodeled`,
since the answer is fully determined before the command is read.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem unknown_cmd_on_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 9 57005 0) fcntl_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) fcntl_model [] := by
  sys_norm

/-- …and the -EINVAL a cmd-first model would give is refuted.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem unknown_cmd_on_closed_fd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 9 57005 0) fcntl_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The same order on a command the model ANSWERS: F_GETFL on a closed fd
is -EBADF, although F_GETFL on an open regular file is declined (below).
A model that dispatched on cmd first would fail closed here and lose a
determined answer; the probe's `badfd` case is the live twin.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem getfl_on_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 9 3 0) fcntl_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) fcntl_model [] := by
  sys_norm

/-- …and the 0 a live fd could earn is refused: `cmd` is never read.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem getfl_on_closed_fd_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 9 3 0) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-! ## F_SETFD: 0 for any arg, on any kind

`case F_SETFD: err = 0; set_close_on_exec(fd, argi & FD_CLOEXEC); break;`
(`do_fcntl`, fs/fcntl.c:468-471, Linux v6.18.46, commit 1f99e9ab748f): no
error path, and bit 0 of `arg` is the only one consulted. -/

/-- F_SETFD is 0 on a CHANNEL as well as on a file: its return does not
depend on the file's status flags, only on the fd resolving.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem setfd_on_channel_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 1 2 1) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- …never -EBADF: the fd resolved (the probe's `setfd` reject twin).
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem setfd_on_channel_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 1 2 1) fcntl_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The arg is not consulted beyond FD_CLOEXEC, so a garbage one
(0xdeadbeef) is the same 0.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem setfd_garbage_arg_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 2 3735928559) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- `F_SETFD, 2` is the trap: `argi & FD_CLOEXEC` is 0, so it CLEARS
close-on-exec rather than being an unknown-flag error, and the answer is
0.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem setfd_arg_two_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 2 2) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- …and the -EINVAL an unknown-flag model would answer for bit 1 is
refuted.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem setfd_arg_two_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 2 2) fcntl_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-! ## F_SETFL: the mask, and the kinds

`case F_SETFL: err = setfl(fd, filp, argi);` (`do_fcntl`,
fs/fcntl.c:475-477, Linux v6.18.46, commit 1f99e9ab748f); `setfl` is
:39-89.  32768 is O_LARGEFILE, the bit musl ORs into every F_SETFL and
`setfl` never reads. -/

/-- An F_SETFL naming none of `setfl`'s bits is 0 on a file the model
opened: no test fires and the closing assignment (:83) is the identity.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem setfl_empty_on_file_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 32768) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- …and the model commits to that 0.  The probe's `setfl` mode issues this
word too, on its write fd; the mode's reject twin mutates its FIRST
`fcntl`, `arg` 0, and is pinned on fd 4 below.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem setfl_empty_on_file_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 4 32768) fcntl_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The same empty F_SETFL DECLINES on fd 1.  A channel's status flags
come from whoever ran the binary (`prog >> log` hands the program an
O_APPEND stdout, and then this very call is an append-CLEARING one, -EPERM
on an append-only inode), so "this changes nothing" is not the model's to
say there.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem setfl_empty_on_channel_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 1 4 32768) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the 0 the file arm answers is refused on the channel even though
it is what the kernel says for a plain stdout.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem setfl_empty_on_channel_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 1 4 32768) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- THE MASK AT ITS EDGE.  O_DSYNC (4096) is a real open flag `setfl`
never reads, so it answers 0; FASYNC (8192) is the adjacent bit, absent
from `SETFL_MASK` (:37) and read all the same by the `f_op->fasync` test
(:75-76), so it declines.  A mask copied from `SETFL_MASK` alone would
answer 0 for both.
kernel: fs/fcntl.c:do_fcntl,setfl; include/uapi/asm-generic/fcntl.h:O_DSYNC@v6.18.46 -/
theorem setfl_o_dsync_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 4096) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- FASYNC (8192), the bit `setfl` reads and `SETFL_MASK` omits, declines.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:FASYNC@v6.18.46 -/
theorem setfl_fasync_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 8192) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- FASYNC on a regular file really IS 0 on Linux — `ext4_file_operations`
(fs/ext4/file.c:963, Linux v6.18.46, commit 1f99e9ab748f) defines no
`fasync`, so the test at :75 is dead there — and the model refuses that 0
anyway, because the answer would be a fact about which filesystem the
working directory is on.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:FASYNC@v6.18.46 -/
theorem setfl_fasync_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 4 8192) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- THE MASK, BIT BY BIT — the declining half.  Each of the five bits
`setfl` reads declines on its own: O_APPEND (1024, :48), O_NONBLOCK (2048,
:37), FASYNC (8192, :75), O_DIRECT (16384, :62-65) and O_NOATIME (262144,
:52-54); the whole mask at once; and a high half over one of its bits,
which the kernel's own `(int)arg` truncation (:448) cannot rescue.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:O_APPEND@v6.18.46 -/
theorem setfl_o_append_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 1024) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the 0 Linux answers it with is refused: `setfl` stores O_APPEND
through `SETFL_MASK` (:83) with no error path keyed on the bit for a file
that is not append-only (`IS_APPEND`, :48-49), so the kernel says 0 and a
model that cannot record the bit must not repeat it (no arm turns a
descriptor into an `FdFileA`): on this read-only fd the bit would go
unrecorded, and on the write fd pinned next a later `write` answered at
the old offset would be a confident wrong answer where this is a gap.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem setfl_o_append_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 4 1024) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The probe's own word, on the probe's own kind of fd.  `O_APPEND |
O_LARGEFILE` (33792) is what musl's `fcntl` passes for `F_SETFL` of
`O_APPEND`, and the `append` mode issues it on an `open_file()` fd —
`O_WRONLY | O_CREAT | O_TRUNC` (`WR_CREATE`, probe.h), the `FdFileW` kind,
fixture fd 4, not the read-only fd 3.  `O_LARGEFILE` is outside
`SETFL_MASK` (:37) and falls away at :83; the `O_APPEND` bit is what
remains, and the write-fd arm declines on it.  This is `setfl_noop_on`'s
`FdFileW` case on its DECLINING side, which no pin on fd 3 reaches: a
model whose `FdFileW` arm answered every word would pass every other pin
in this file.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem setfl_o_append_largefile_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 4 4 33792) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the 0 Linux answers it with (`IS_APPEND` false at :48-49, the bit
stored at :83) is refused on that fd, as the probe's `fail-closed` case
has it: a model that answered 0 here would answer a later `write` at the
old offset.
probe: testing/syscall-check/tests/fcntl_spec.c#fail-closed -- append -/
theorem setfl_o_append_largefile_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 4 4 33792) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- O_NONBLOCK (2048) alone declines: `setfl` stores it through `SETFL_MASK`.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:O_NONBLOCK@v6.18.46 -/
theorem setfl_o_nonblock_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 2048) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- O_DIRECT (16384) alone declines: `setfl`'s `FMODE_CAN_ODIRECT` test reads
it.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:O_DIRECT@v6.18.46 -/
theorem setfl_o_direct_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 16384) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- O_NOATIME (262144) alone declines: `setfl`'s ownership test reads it.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:O_NOATIME@v6.18.46 -/
theorem setfl_o_noatime_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 262144) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- All five bits at once decline.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:O_APPEND,O_NONBLOCK,FASYNC,O_DIRECT,O_NOATIME@v6.18.46 -/
theorem setfl_whole_mask_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 289792) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- 2^32 + O_NONBLOCK declines: `do_fcntl`'s `(int)arg` hands `setfl` exactly
O_NONBLOCK.
kernel: fs/fcntl.c:do_fcntl,setfl; include/uapi/asm-generic/fcntl.h:O_NONBLOCK@v6.18.46 -/
theorem setfl_high_half_over_mask_bit_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 4294969344) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- A high half ALONE (2^32) is 0: `(int)arg` (fs/fcntl.c:448) hands `setfl`
0, no branch fires and the store at :83 writes no `SETFL_MASK` bit — the
identity unless the open recorded one, which the model does not track and
the return value does not see; the
model masks all 64 bits against `setfl_acted_on` and finds nothing.  The
two agree on this word, and the pair with the pin above is what separates
"the mask ignores the high half" from "the high half is refused".
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem setfl_high_half_only_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 4294967296) fcntl_model o ↔
      o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- …and it is not -EINVAL: no errno of `setfl` is keyed on bits `(int)arg`
discards.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem setfl_high_half_only_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 4 4294967296) fcntl_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- Dropbear's own call, `F_SETFL, O_NONBLOCK`, succeeds with 0 on Linux
(no error path is keyed on the bit) and the model refuses that 0: it has
no non-blocking mode, and a later `read` answered as if the fd were still
blocking would be a confident wrong answer where this is an honest gap.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:O_NONBLOCK@v6.18.46 -/
theorem setfl_o_nonblock_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 4 2048) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- O_DIRECT is the sharp one: on a kernel where `FMODE_CAN_ODIRECT` is
set the call is 0 and the fd becomes O_DIRECT, so the NEXT unaligned
`write` is -EINVAL where the model promises a count; on one where it is
not, the call is -EINVAL (:62-65).  Both are refused.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:O_DIRECT@v6.18.46 -/
theorem setfl_o_direct_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 4 16384) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and the -EINVAL of the `FMODE_CAN_ODIRECT` branch is refused too.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:O_DIRECT@v6.18.46 -/
theorem setfl_o_direct_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 4 16384) fcntl_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- O_NOATIME is -EPERM unless the caller owns the inode (:52-54); the
model knows neither the owner nor the answer, and refuses both.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:O_NOATIME@v6.18.46 -/
theorem setfl_o_noatime_eperm_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 4 262144) fcntl_model (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  sys_refute

/-- …and the 0 an inode owner would get is refused too.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:O_NOATIME@v6.18.46 -/
theorem setfl_o_noatime_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 4 262144) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and the accepting half: every neighbouring open flag `setfl` never
reads answers 0.  O_DIRECTORY (65536) and O_NOFOLLOW (131072) bracket
O_LARGEFILE; O_SYNC (1052672) and O_PATH (2097152) are the whole words a
caller is likeliest to OR in by accident; and 2^31 is `arg`'s sign bit,
which the kernel reads back through `unsigned int` (:39) and which the
unsigned mask must therefore not treat as special.  Together with
`setfl_o_dsync_is_zero` these are what make the declines above a
BOUNDARY rather than a list: every decline stays green under a change
that only ever declines more, and these go red under it.
kernel: fs/fcntl.c:do_fcntl,setfl; include/uapi/asm-generic/fcntl.h:O_DIRECTORY@v6.18.46 -/
theorem setfl_o_directory_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 65536) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- O_NOFOLLOW (131072), a bit `setfl` never reads, answers 0.
kernel: fs/fcntl.c:do_fcntl,setfl; include/uapi/asm-generic/fcntl.h:O_NOFOLLOW@v6.18.46 -/
theorem setfl_o_nofollow_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 131072) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- O_SYNC (1052672, `__O_SYNC|O_DSYNC`), two bits `setfl` never reads,
answers 0.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem setfl_o_sync_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 1052672) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- O_PATH (2097152), a bit `setfl` never reads, answers 0.
kernel: fs/fcntl.c:do_fcntl,setfl; include/uapi/asm-generic/fcntl.h:O_PATH@v6.18.46 -/
theorem setfl_o_path_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 2097152) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- Bit 31 of `arg`, read back as `unsigned int` by `setfl`, answers 0.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem setfl_sign_bit_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4 2147483648) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- A model that read the sign bit as an error (or declined an unknown
bit, which `setfl` never does: there is no `arg & ~valid` test) is refuted
on the word the accepting half is most exposed on.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem setfl_sign_bit_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 4 2147483648) fcntl_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-! ## The other kinds `openat` mints, and the socket

`setfl_noop_on` excludes channels, pipes and /dev/null and nothing else,
so a write-created file, a directory and a socket take the file answer. -/

/-- A write-created fd takes the file answer.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem setfl_empty_on_write_fd_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 4 4 32768) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- …and with `arg` 0 outright: no branch of `setfl` fires and :83 stores
the word it read.  The third conjunct of Rocq `Pipe.v`'s
`fcntl_setfl_on_a_pipe_end_declines`, which the header above says is
pinned here.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem setfl_zero_on_write_fd_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 4 4 0) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- …and the model commits to that 0.  The probe's `setfl` mode opens its
file `WR_CREATE` and its FIRST `fcntl` is `F_SETFL, 0`, so the mode's
`reject --mutate fcntl:ret=-EINVAL` case is exactly this input answered
-EINVAL — the input the fd-3 pins above cannot replay.
probe: testing/syscall-check/tests/fcntl_spec.c#reject --mutate fcntl:ret=-EINVAL -- setfl -/
theorem setfl_zero_on_write_fd_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 4 4 0) fcntl_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The high half alone on the write fd, the `setfl` mode's last `F_SETFL`
(`HI`, 2^32): `(int)arg` (fs/fcntl.c:448, Linux v6.18.46) hands `setfl` 0
and the answer is 0 on this kind as on fd 3.
probe: testing/syscall-check/tests/fcntl_spec.c#conform -- setfl -/
theorem setfl_high_half_only_on_write_fd_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 4 4 4294967296) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- A directory fd takes the file answer — right, because
`ext4_dir_operations` (fs/ext4/dir.c:682, Linux v6.18.46, commit
1f99e9ab748f) defines neither `check_flags` nor `fasync` — and it
is the entry a reader is likeliest to expect beside `FdChannel` on the
declining side.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem setfl_empty_on_directory_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 5 4 32768) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- F_SETFD is 0 on a directory fd.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem setfd_on_directory_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 5 2 1) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- O_NONBLOCK on a directory fd declines as on a file.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:O_NONBLOCK@v6.18.46 -/
theorem setfl_o_nonblock_on_directory_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 5 4 2048) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the kernel's 0 is refused there too.
kernel: fs/fcntl.c:setfl; include/uapi/asm-generic/fcntl.h:O_NONBLOCK@v6.18.46 -/
theorem setfl_o_nonblock_on_directory_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 5 4 2048) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- THE SOCKET, both sides of the mask.  A socket takes the file answer,
and the declining side is the one worth three lines: `socket_file_ops`
(net/socket.c:156-173, Linux v6.18.46, commit 1f99e9ab748f) carries
`.fasync = sock_fasync` (:168), so FASYNC is the bit the mask
exists to keep unreachable, and a socket is the descriptor that
guarantee is about.  F_SETFD is 0 here as on every other kind.
kernel: fs/fcntl.c:do_fcntl,setfl; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem setfl_empty_on_socket_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 6 4 32768) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- FASYNC on a socket declines: `sock_fasync` is live there.
kernel: fs/fcntl.c:setfl; net/socket.c:sock_fasync; include/uapi/asm-generic/fcntl.h:FASYNC@v6.18.46 -/
theorem setfl_fasync_on_socket_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 6 4 8192) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- `sock_fasync` (net/socket.c:1471, Linux v6.18.46, commit 1f99e9ab748f)
succeeds and puts the socket on a fasync list: the
kernel's 0 is refused, because the model would then go on answering for
a socket that can raise SIGIO.
kernel: fs/fcntl.c:setfl; net/socket.c:sock_fasync; include/uapi/asm-generic/fcntl.h:FASYNC@v6.18.46 -/
theorem setfl_fasync_on_socket_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 6 4 8192) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- F_SETFD is 0 on a socket.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem setfd_on_socket_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 6 2 1) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- fcntl has no socket-specific refusal: -ENOTSOCK is what a model that
resolved sockets through a different table might give, and it is refuted
(the probe's `sockfl` reject twin offers the same errno).
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem setfd_on_socket_enotsock_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 6 2 1) fcntl_model (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-! ## The three kinds that decline F_SETFL outright: a pipe end and the two device nodes -/

/-- F_SETFL with an EMPTY arg — the cheapest 0 on every kind above —
declines on a pipe end.  Rocq's `Checks/Cases/Fs/Pipe.v` pins this; the
arm is `setfl_noop_on`'s `FdPipe`, a choice: O_DIRECT is the pipe's
packet-mode bit (`is_packetized`, fs/pipe.c:415-418, Linux v6.18.46,
commit 1f99e9ab748f) and inside `SETFL_MASK`, so the closing assignment
would clear it on the one shape `pipe2` will someday accept, and
`pipeanon_fops` carries `.fasync = pipe_fasync` (fs/pipe.c:1264).
kernel: fs/fcntl.c:setfl; fs/pipe.c:is_packetized,pipe_fasync@v6.18.46 -/
theorem setfl_empty_on_pipe_reader_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 7 4 0) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- The write end declines the same way.
kernel: fs/fcntl.c:setfl; fs/pipe.c:is_packetized,pipe_fasync@v6.18.46 -/
theorem setfl_empty_on_pipe_writer_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 8 4 0) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- On every pipe the model can build the call really is 0 (flags 0, so
nothing to clear); the 0 is refused all the same, which is what makes the
arm a choice the next `pipe2` widening cannot silently unmake.
kernel: fs/fcntl.c:setfl; fs/pipe.c:is_packetized,pipe_fasync@v6.18.46 -/
theorem setfl_empty_on_pipe_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 7 4 0) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- /dev/null, opened read-write: F_SETFL declines for any arg — the
`f_flags` word is not on the entry and `null_fops`'s inertness under
`setfl` (drivers/char/mem.c:644-652, Linux v6.18.46, commit 1f99e9ab748f)
is not written down — while the kind-blind F_SETFD still answers 0.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem setfl_empty_on_devnull_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 11 4 0) fcntl_devnull_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the 0 Linux answers on /dev/null is refused.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem setfl_empty_on_devnull_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 11 4 0) fcntl_devnull_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- F_SETFD is 0 on /dev/null.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem setfd_on_devnull_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 11 2 1) fcntl_devnull_model o ↔
      o = Ok (mkEffect 0 [] []) fcntl_devnull_model [] := by
  sys_norm

/-- /dev/urandom, read-only by construction: F_SETFL declines for any arg —
the `f_flags` word is not on the entry, and the fact that would make a no-op
answer derivable — that for an `arg` naming none of `setfl_acted_on`'s bits
no branch of `setfl` fires — is not written down.  The device is not inert
under `setfl` at large: `urandom_fops` carries `.fasync = random_fasync`
(drivers/char/random.c:1577, Linux v6.18.46), which `setfl` calls on a
FASYNC toggle (fs/fcntl.c:75-76), and O_DIRECT and O_NOATIME have their
branches too (:62-65, :52-54) — one more reason the arm answers nothing;
the kind-blind F_SETFD still answers 0.  Linux itself answers 0 to this
call (`setfl`, fs/fcntl.c:39-89: `arg` 0 fires no branch, `urandom_fops`
has no `.check_flags`, and the closing assignment at :83 is the identity
on a word with no `SETFL_MASK` bit), so the refutation below pins the decline, not an
impossibility.  At `arg` 0 `random_fasync` is never called; the toggle
that calls it is pinned two below.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem setfl_empty_on_urandom_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 12 4 0) fcntl_urandom_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem setfl_empty_on_urandom_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 12 4 0) fcntl_urandom_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- FASYNC (8192) on /dev/urandom, the word that makes "the device reads none
of the bits" wrong: `setfl` sees the toggle (:75-76) and calls
`urandom_fops`' `.fasync`, `random_fasync` (drivers/char/random.c:1555-1558,
installed at :1577), which is `fasync_helper` and returns no errno — Linux
answers 0, and the arm declines here as at every other `arg`.  This is the
input the `random_fasync` reading decides; the arg-0 pair above is decided
by `setfl` alone.
kernel: fs/fcntl.c:setfl; drivers/char/random.c:random_fasync@v6.18.46 -/
theorem setfl_fasync_on_urandom_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 12 4 8192) fcntl_urandom_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/fcntl.c:setfl; drivers/char/random.c:random_fasync@v6.18.46 -/
theorem setfl_fasync_on_urandom_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 12 4 8192) fcntl_urandom_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The decline is for ANY arg, not only the empty one: O_NONBLOCK (2048) is
a bit `setfl` would store (`SETFL_MASK`, fs/fcntl.c:37) and the arm declines
it the same way.
kernel: fs/fcntl.c:setfl; drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem setfl_o_nonblock_on_urandom_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 12 4 2048) fcntl_urandom_model o ↔ o = Unmodeled := by
  sys_norm

/-- F_SETFD reads the kind not at all: `do_fcntl` sets the close-on-exec bit
in the table and answers 0 (fs/fcntl.c:468-471, Linux v6.18.46).
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem setfd_on_urandom_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 12 2 1) fcntl_urandom_model o ↔
      o = Ok (mkEffect 0 [] []) fcntl_urandom_model [] := by
  sys_norm

/-! ## The 32-bit arguments, on a LIVE fd

Every truncation a probe can show is on a closed fd, where both spellings
answer -EBADF.  Only a live fd separates `fd32` from the identity
(`SYSCALL_DEFINE3(fcntl, unsigned int, fd, unsigned int, cmd, …)`,
fs/fcntl.c:574, Linux v6.18.46, commit 1f99e9ab748f). -/

/-- `2^32 + 3` is fd 3 to the kernel, and F_SETFD on it is 0.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem fd32_on_a_live_fd_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 4294967299 2 1) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- …and the -EBADF an untruncated fd would earn is refused.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem fd32_on_a_live_fd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 4294967299 2 1) fcntl_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and the channel exclusion survives the truncation: `2^32 + 1` is
fd 1, and the empty F_SETFL declines there.
kernel: fs/fcntl.c:fcntl,setfl@v6.18.46 -/
theorem fd32_channel_exclusion_survives (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 4294967297 4 32768) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- `cmd` is 32 bits and BIT 31 IS PART OF IT: `2^32 + 2` still names
F_SETFD, while `2^31 + 2` names no command at all — `do_fcntl`'s
`unsigned int cmd` is 2147483650, the switch falls to `default: break`
and returns its pre-set -EINVAL (fs/fcntl.c:450, :553-555, Linux
v6.18.46).  The model
declines the second rather than answer it, and a `cmd32` that kept only
31 bits would answer 0 to a call Linux refuses.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem cmd32_high_half_is_setfd (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 4294967298 1) fcntl_model o ↔ o = Ok (mkEffect 0 [] []) fcntl_model [] := by
  sys_norm

/-- `2^31 + 2` names no command: declined.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem cmd32_bit_31_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 2147483650 1) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the F_SETFD 0 a 31-bit `cmd32` would answer is refused.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem cmd32_bit_31_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 2147483650 1) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- An all-ones cmd is `0xffffffff` to the kernel, unrecognized, -EINVAL;
the model declines, and offering that very -EINVAL is still refused: an
unrecognized command is outside the modeled surface, not a modeled
error.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem cmd_all_ones_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 18446744073709551615 0) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and `do_fcntl`'s own -EINVAL for it is refused.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem cmd_all_ones_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 18446744073709551615 0) fcntl_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-! ## F_GETFL: the socket answers, every other kind declines

`case F_GETFL: err = filp->f_flags;` (`do_fcntl`, fs/fcntl.c:472-474,
Linux v6.18.46, commit 1f99e9ab748f), verbatim and unmasked. -/

/-- F_GETFL ON A SOCKET is O_RDWR exactly: `sock_alloc_file` builds the
file from `O_RDWR | (flags & O_NONBLOCK)` (net/socket.c:483-485, Linux
v6.18.46) and never goes near `build_open_flags`; `force_o_largefile()`
is applied by the open-family entry points (fs/open.c:1458, :1466, :1492,
:1528, Linux v6.18.46) and by a few other file-creating paths, none of
which a socket takes — the list is in
`bugs/fcntl-getfl-socket-arm-admits-linux-alone.md`.  The answer does not depend on the socket's
`SockState`: every state is reached from a `socket` or `accept4` that
declined SOCK_NONBLOCK.
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file; include/uapi/asm-generic/fcntl.h:O_RDWR@v6.18.46 -/
theorem getfl_on_socket_is_o_rdwr (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 6 3 0) fcntl_model o ↔ o = Ok (mkEffect 2 [] []) fcntl_model [] := by
  sys_norm

/-- THE ONE THAT MATTERS: 32770 is O_RDWR|O_LARGEFILE, the word qemu-user's
`do_fcntl` reports on a 64-bit glibc host (`TARGET_F_GETFL`,
linux-user/syscall.c:7508-7517, QEMU 11.1.1, ORs `TARGET_O_LARGEFILE` into
every F_GETFL answer where the host's `O_LARGEFILE` is 0 and its `long` is
64-bit; the `fcntl_flags_tbl` translation before it has set the same bit
already — the bugs entry has the mechanism) and the obvious
wrong fix if a probe ever went red here.  musl passes an F_GETFL return
through and glibc's wrapper is not read here, so the emulator is the one
supported source of the word that has been read — and it IS a supported
implementation, so 32770 is a real answer of a
supported implementation and this pin locks the arm to Linux's word alone.
Kept, with the record:
`bugs/fcntl-getfl-socket-arm-admits-linux-alone.md` names this pin as the
one a qemu-user run would fail and as the pin to flip when Rocq's
`socket_f_flags` arm moves.
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file; fs/open.c:openat; include/uapi/asm-generic/fcntl.h:O_RDWR,O_LARGEFILE@v6.18.46 -/
theorem getfl_on_socket_o_largefile_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 6 3 0) fcntl_model (Ok (mkEffect 32770 [] []) m' evs) := by
  sys_refute

/-- …and the four kinds it declines, each offered the word Linux really
holds for it and refused anyway.  fd 0, a channel: the environment's word.
fd 3, opened O_RDONLY: Linux holds O_RDONLY|O_LARGEFILE (32768) — or
O_RDONLY|O_LARGEFILE|O_NONBLOCK (34816), since `openat` accepted and
discarded that bit, which is exactly why the arm cannot choose.  fd 4,
O_WRONLY|O_CREAT|O_TRUNC: `do_dentry_open` clears O_CREAT and O_TRUNC
(fs/open.c:981, Linux v6.18.46), leaving O_WRONLY|O_LARGEFILE (32769).
fd 5, a
directory: O_RDONLY|O_LARGEFILE|O_DIRECTORY (98304).  `arg` is 0
throughout and not part of the question: the arm never reads `argi`.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem getfl_on_channel_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 0 3 0) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- The channel's own word is refused too — 32770, O_RDWR|O_LARGEFILE, what
a terminal fd holds under native Linux: the path open ORs O_LARGEFILE in
(fs/open.c:1466) and `do_dentry_open` keeps it, clearing only
O_CREAT|O_EXCL|O_NOCTTY|O_TRUNC (:981, Linux v6.18.46); it is also a
socket's word on fd 0 under a glibc-hosted qemu-user.  So the decline above
is not "declines unless the kernel happens to say the right thing": the
model records no word for a channel and takes none.
kernel: fs/fcntl.c:do_fcntl; fs/open.c:do_dentry_open@v6.18.46 -/
theorem getfl_on_channel_word_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 0 3 0) fcntl_model (Ok (mkEffect 32770 [] []) m' evs) := by
  sys_refute

/-- …and so is the word the harness's fd 0 really holds: under the tracer
fds 0/1/2 are pipes (testing/vm/README.md), and a pipe's read end is built
with `O_RDONLY | (flags & O_NONBLOCK)` (`create_pipe_files`, fs/pipe.c:956,
Linux v6.18.46), 0 for a plain one.  0 is also what a wildcard arm would
answer, so refusing it is what tells this decline from one.
kernel: fs/fcntl.c:do_fcntl; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem getfl_on_channel_pipe_word_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 0 3 0) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- F_GETFL on the O_RDONLY file declines.
kernel: fs/fcntl.c:do_fcntl; fs/open.c:build_open_flags@v6.18.46 -/
theorem getfl_on_file_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 3 0) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- F_GETFL on the write-created fd declines.
kernel: fs/fcntl.c:do_fcntl; fs/open.c:build_open_flags,do_dentry_open@v6.18.46 -/
theorem getfl_on_write_fd_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 4 3 0) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- F_GETFL on the directory fd declines.
kernel: fs/fcntl.c:do_fcntl; fs/open.c:build_open_flags@v6.18.46 -/
theorem getfl_on_directory_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 5 3 0) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- O_RDONLY|O_LARGEFILE (32768), the file's word under a plain open, is
refused.
kernel: fs/fcntl.c:do_fcntl; fs/open.c:openat,build_open_flags; include/uapi/asm-generic/fcntl.h:O_LARGEFILE@v6.18.46 -/
theorem getfl_on_file_largefile_word_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 3 0) fcntl_model (Ok (mkEffect 32768 [] []) m' evs) := by
  sys_refute

/-- …and O_RDONLY|O_LARGEFILE|O_NONBLOCK (34816), its word under the other
open the model admits, is refused.
kernel: fs/fcntl.c:do_fcntl; fs/open.c:openat,build_open_flags; include/uapi/asm-generic/fcntl.h:O_LARGEFILE,O_NONBLOCK@v6.18.46 -/
theorem getfl_on_file_nonblock_word_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 3 0) fcntl_model (Ok (mkEffect 34816 [] []) m' evs) := by
  sys_refute

/-- O_WRONLY|O_LARGEFILE (32769), the write fd's word after `do_dentry_open`'s
clear, is refused.
kernel: fs/fcntl.c:do_fcntl; fs/open.c:openat,do_dentry_open; include/uapi/asm-generic/fcntl.h:O_WRONLY,O_LARGEFILE@v6.18.46 -/
theorem getfl_on_write_fd_word_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 4 3 0) fcntl_model (Ok (mkEffect 32769 [] []) m' evs) := by
  sys_refute

/-- O_RDONLY|O_LARGEFILE|O_DIRECTORY (98304), the directory's word, is refused.
kernel: fs/fcntl.c:do_fcntl; fs/open.c:openat,build_open_flags; include/uapi/asm-generic/fcntl.h:O_LARGEFILE,O_DIRECTORY@v6.18.46 -/
theorem getfl_on_directory_word_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 5 3 0) fcntl_model (Ok (mkEffect 98304 [] []) m' evs) := by
  sys_refute

/-- BOTH PIPE ENDS, declined though derivable: on a real kernel the writer
holds O_WRONLY (1) and the reader O_RDONLY (0) — `create_pipe_files`,
fs/pipe.c:944-946 and :956-957, Linux v6.18.46 — and `pipe2` declines
every nonzero flag
word, so those ARE the words.  Each end is offered its true value and
refused: an arm added later without the `pipe2` change its comment names
would turn these green, which is the point of writing the true values.
kernel: fs/fcntl.c:do_fcntl; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem getfl_on_pipe_reader_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 7 3 0) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- The write end declines too.
kernel: fs/fcntl.c:do_fcntl; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem getfl_on_pipe_writer_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 8 3 0) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- The reader's true word, O_RDONLY (0), is refused.
kernel: fs/fcntl.c:do_fcntl; fs/pipe.c:create_pipe_files; include/uapi/asm-generic/fcntl.h:O_RDONLY@v6.18.46 -/
theorem getfl_on_pipe_reader_o_rdonly_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 7 3 0) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The writer's true word, O_WRONLY (1), is refused.
kernel: fs/fcntl.c:do_fcntl; fs/pipe.c:create_pipe_files; include/uapi/asm-generic/fcntl.h:O_WRONLY@v6.18.46 -/
theorem getfl_on_pipe_writer_o_wronly_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 8 3 0) fcntl_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-- /dev/null opened read-write: Linux holds O_RDWR|O_LARGEFILE (32770)
plus whatever O_NONBLOCK the open passed; the access mode is on the entry
and the bit is not, so the arm declines and the largefile word is
refused.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem getfl_on_devnull_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 11 3 0) fcntl_devnull_model o ↔ o = Unmodeled := by
  sys_norm

/-- O_RDWR|O_LARGEFILE (32770), /dev/null's word under a plain open, is
refused.
kernel: fs/fcntl.c:do_fcntl; fs/open.c:openat; include/uapi/asm-generic/fcntl.h:O_RDWR,O_LARGEFILE@v6.18.46 -/
theorem getfl_on_devnull_word_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 11 3 0) fcntl_devnull_model (Ok (mkEffect 32770 [] []) m' evs) := by
  sys_refute

/-- /dev/urandom, read-only by construction: Linux holds O_RDONLY|O_LARGEFILE
(32768) plus whatever O_NONBLOCK the open passed; the mode is fixed by the kind
and the bit is not recorded, so the arm declines and the largefile word is
refused — Linux's own word for a plain O_RDONLY open (`openat` ORs
O_LARGEFILE in, fs/open.c:1466-1467), so the refutations below pin the
decline, not an impossibility.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem getfl_on_urandom_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 12 3 0) fcntl_urandom_model o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem getfl_on_urandom_word_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 12 3 0) fcntl_urandom_model (Ok (mkEffect 32768 [] []) m' evs) := by
  sys_refute

/-- The word with O_NONBLOCK, 34816, is refused too: which of the two words
Linux holds is exactly what the entry does not record, so neither is
admitted.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem getfl_on_urandom_nonblock_word_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 12 3 0) fcntl_urandom_model (Ok (mkEffect 34816 [] []) m' evs) := by
  sys_refute

/-! ## F_GETFD: declined on the very kind F_GETFL answers

`case F_GETFD: err = get_close_on_exec(fd) ? FD_CLOEXEC : 0;` (`do_fcntl`,
fs/fcntl.c:465-467, Linux v6.18.46, commit 1f99e9ab748f): a bit of the fd
TABLE, whose three modeled setters — F_SETFD above, `openat`'s O_CLOEXEC
and `socket`'s SOCK_CLOEXEC — all discard it.  The pair with
`getfl_on_socket_is_o_rdwr` is the asymmetry read back as two values: a
socket's `f_flags` is a function of the constructor, its close-on-exec
bit is not, and an arm that answered F_GETFD "because the socket case
worked" fails here on both of the only two values it could give. -/

/-- F_GETFD on the socket declines.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:get_close_on_exec@v6.18.46 -/
theorem getfd_on_socket_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 6 1 0) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the 0 of a clear close-on-exec bit is refused…
kernel: fs/fcntl.c:do_fcntl; fs/file.c:get_close_on_exec@v6.18.46 -/
theorem getfd_on_socket_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 6 1 0) fcntl_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and so is FD_CLOEXEC (1), the only other value the bit can read back as.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:get_close_on_exec; include/uapi/asm-generic/fcntl.h:FD_CLOEXEC@v6.18.46 -/
theorem getfd_on_socket_fd_cloexec_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 6 1 0) fcntl_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-- …and on a file, right after an F_SETFD that set the bit: the model
recorded nothing, so it declines rather than answer the FD_CLOEXEC the
kernel now holds.  (The two calls are independent pins; the model is
unchanged by F_SETFD, which is the fact the second one rests on.)
kernel: fs/fcntl.c:do_fcntl; fs/file.c:get_close_on_exec@v6.18.46 -/
theorem getfd_on_file_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 1 0) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the FD_CLOEXEC (1) the kernel now holds is refused.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:get_close_on_exec; include/uapi/asm-generic/fcntl.h:FD_CLOEXEC@v6.18.46 -/
theorem getfd_on_file_fd_cloexec_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 1 0) fcntl_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-! ## F_DUPFD: dup in disguise -/

/-- `case F_DUPFD: err = f_dupfd(argi, filp, 0);` (fs/fcntl.c:456-458,
Linux v6.18.46, commit 1f99e9ab748f) calls `f_dupfd` (fs/file.c:1472-1484),
which hands back `alloc_fd(from, nofile, flags)`, the lowest free fd at or
above `from` — 2 here, the hole `fcntl_fds` leaves below fd 3 — onto the
SAME open file description.  The model's fd table cannot express two
entries sharing an offset, and the decline is load-bearing for
`State.pipe_end_live`; offering the fd Linux would return is refused.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:f_dupfd,alloc_fd@v6.18.46 -/
theorem dupfd_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 3 0 0) fcntl_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and fd 2, the lowest free descriptor `alloc_fd` would hand back, is
refused.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:f_dupfd,alloc_fd@v6.18.46 -/
theorem dupfd_lowest_free_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 3 0 0) fcntl_model (Ok (mkEffect 2 [] []) m' evs) := by
  sys_refute

/-! ## A17: FdFileRW and FdFileA -/

/-- Rocq: `Fcntl.setfl_noop_on`, Fcntl.v:181-183 at 96c2debdb.
Clearing no acted-on flag passes fs/fcntl.c, setfl, Linux v6.18.46;
an O_RDWR access mode does not itself require a status-flag change.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem a17_rdwr_setfl_zero_is_noop :
    setfl_noop_on (.FdFileRW [102] 0) 0 = true := by
  decide

/-- Rocq: `Fcntl.setfl_noop_on`, Fcntl.v:181-183 at 96c2debdb.
O_NONBLOCK changes f_flags in fs/fcntl.c, setfl, Linux v6.18.46;
the no-op helper must not call it inert.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem a17_rdwr_setfl_acted_on_declines :
    setfl_noop_on (.FdFileRW [102] 0) 2048 = false := by
  decide

/-- Rocq: `Fcntl.getfl_f_flags`, Fcntl.v:495-498 at 96c2debdb.
F_GETFL reads the retained f_flags in fs/fcntl.c, do_fcntl, Linux v6.18.46;
the entry lacks the complete open word, so access mode alone cannot answer.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem a17_rdwr_getfl_declines :
    getfl_f_flags (.FdFileRW [102] 0) = none := by
  rfl

/-- Rocq: `Fcntl.setfl_noop_on`, Fcntl.v:183 at 96c2debdb.
Not a no-op even for an arg naming no acted-on bit: the description
carries O_APPEND, so fs/fcntl.c, setfl, Linux v6.18.46 answers -EPERM on an
append-only inode and otherwise clears O_APPEND in its closing assignment.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem a17_append_setfl_zero_declines :
    setfl_noop_on (.FdFileA [102] 0) 0 = false := by
  decide

/-- Rocq: `Fcntl.setfl_noop_on`, Fcntl.v:183 at 96c2debdb.
O_NONBLOCK changes f_flags in fs/fcntl.c, setfl, Linux v6.18.46 on an
append-mode file as on any other; the no-op helper must not call it inert.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem a17_append_setfl_acted_on_declines :
    setfl_noop_on (.FdFileA [102] 0) 2048 = false := by
  decide

/-- Rocq: `Fcntl.getfl_f_flags`, Fcntl.v:499 at 96c2debdb.
F_GETFL reads the retained f_flags in fs/fcntl.c, do_fcntl, Linux v6.18.46;
the open may have passed an O_NONBLOCK the entry did not record, as for
every file kind, and answering F_GETFL on a kind `setfl_noop_on` declines
outright would be the mismatch Rocq's arm refuses.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem a17_append_getfl_declines :
    getfl_f_flags (.FdFileA [102] 0) = none := by
  rfl

/-- Rocq's `fcntl_append_model`: `fcntl_model`'s table with an append-mode
descriptor (from O_WRONLY|O_CREAT|O_APPEND) at fd 10, beside the ordinary
write-only one at fd 4.  Two kinds, one call, one model: that pairing is
what makes the contrast below a claim about the fd KIND rather than about
the argument. -/
def fcntl_append_model : Model :=
  fixture_of (fds := fcntl_fds ++ [(10, .FdFileA [104] 0)]) (fs := [([102], [104, 105])])

attribute [sys_simp low] fcntl_append_model.eq_1

/-- F_SETFL with `arg` 0 on the append fd declines, the first conjunct of
Rocq's `fcntl_flag_commands_decline_on_an_append_fd`.  The empty word
passes the acted-on test, so on every other file kind it is the cheapest
possible 0; here `f_flags` carries O_APPEND, so `setfl` answers -EPERM on
an append-only inode (fs/fcntl.c:48, Linux v6.18.46) and otherwise its
closing assignment (:83) CLEARS O_APPEND, after which every write lands
at `f_pos` instead of at end of file.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem setfl_zero_on_append_fd_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 10 4 0) fcntl_append_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the 0 Linux answers on an inode that is not append-only is
refused: no arm turns an `FdFileA` back into an `FdFileW`, so a model that
answered 0 would go on appending where the kernel's description no longer
does.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem setfl_zero_on_append_fd_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fcntl_in 10 4 0) fcntl_append_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The contrast, the second conjunct: the identical call on fd 4, the
ordinary write-only file in the same model, answers 0.  Its `f_flags`
holds no bit `setfl` reads, so the closing assignment (fs/fcntl.c:83,
Linux v6.18.46) stores the word it already had.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem setfl_zero_beside_append_fd_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 4 4 0) fcntl_append_model o
      ↔ o = Ok (mkEffect 0 [] []) fcntl_append_model [] := by
  sys_norm

/-- O_DSYNC (4096), a bit `setfl` never reads, declines on the append fd as
the empty word does, the third conjunct: O_APPEND is inside `SETFL_MASK`
(fs/fcntl.c:37, Linux v6.18.46), so a word without it clears the bit at
:83 whatever else it names.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem setfl_o_dsync_on_append_fd_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 10 4 4096) fcntl_append_model o ↔ o = Unmodeled := by
  sys_norm

/-- …while on fd 4 beside it the same word is 0, the fourth conjunct.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem setfl_o_dsync_beside_append_fd_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 4 4 4096) fcntl_append_model o
      ↔ o = Ok (mkEffect 0 [] []) fcntl_append_model [] := by
  sys_norm

/-- F_GETFL declines on the append fd, the fifth conjunct, for the reason
`a17_append_getfl_declines` above gives.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem getfl_on_append_fd_is_unmodeled (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 10 3 0) fcntl_append_model o ↔ o = Unmodeled := by
  sys_norm

/-- …while F_SETFD still answers 0 on the append fd, the sixth conjunct:
it sets the descriptor's close-on-exec bit in the fd table and never
reads `f_flags`, which is what keeps the declines above confined to the
flag word.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem setfd_on_append_fd_is_zero (o : outcome SyscallEffect) :
    syscall_spec (fcntl_in 10 2 1) fcntl_append_model o
      ↔ o = Ok (mkEffect 0 [] []) fcntl_append_model [] := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Fcntl
