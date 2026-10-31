import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Fs.Fcntl — fcntl (25)

Mirrors `theories/LinuxProcessSem/Sys/Fs/Fcntl.v`, which answers to Linux
`fs/fcntl.c`: it holds what the kernel defines there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Fs/Fcntl.lean`.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
Rocq pins `setfl`, `SETFL_MASK` and the four `F_GETFD`/`F_SETFD`/
`F_GETFL`/`F_SETFL` arms to "v6.10-v6.15, byte-identical over that range";
every line here was read at v6.18.46 instead.  Two facts of `setfl`'s
text there that Rocq's prose does not spell out, and that no decision
turns on: its parameter is `unsigned int arg` (still narrowed by
`do_fcntl`'s `int argi = (int)arg` before the call, fs/fcntl.c:448 and
:476, Linux v6.18.46), and its O_DIRECT test exempts FIFOs
(`!S_ISFIFO(inode->i_mode) && (arg & O_DIRECT) && …`, fs/fcntl.c:62-65).
Neither moves a bit into or out of the mask below.

One spelling differs from Rocq without changing a value: the mask test on
the flags word is done on the `word` (`bv_and`) where Rocq does it on
`bv_unsigned` in `Z` (`Z.land`) — the constant is below `2^64`, so the two
agree — and the `Z.eqb` Bool test is Lean's decidable `=` on `Int`.

Rocq imports `Fs.Open` and proves two remarks over it —
`modeled_open_flags_clear_of_setfl` and
`open_ignored_flags_clear_of_setfl_current`, the arithmetic behind the
`FdFile`/`FdFileW`/`FdDir` arms of `setfl_noop_on` — which cannot be
stated until the `Fs.Open` twin exists; they are lemmas, not definitions,
so they are not `unported:` entries, and they are the first thing that
file's port owes this one.  The two remarks that need nothing of `Open`
are twinned below, beside the definitions they are about. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Fcntl

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- The file STATUS flags `F_SETFL` acts on: the union of the five named
bits `setfl` (fs/fcntl.c:39-89, Linux v6.18.46, commit 1f99e9ab748f)
reads out of `arg` — O_APPEND (the `IS_APPEND` -EPERM test, :48-49),
O_NOATIME (the ownership -EPERM test, :52-54), O_DIRECT (the
`FMODE_CAN_ODIRECT` -EINVAL test, :62-65), O_NONBLOCK (only through
`SETFL_MASK`, :37, and the dead `O_NONBLOCK != O_NDELAY` fixup, :57-59)
and FASYNC (the `f_op->fasync` callback, :75-76).  FASYNC is NOT in
`SETFL_MASK` (fs/fcntl.c:37, Linux v6.18.46), so a constant copied from
that macro alone
would be the wrong set.

The sixth read, which no mask covers, is the whole `arg` handed to
`f_op->check_flags` (:67-68).  Exactly two `file_operations` in the tree
set it, `nfs_file_operations` (fs/nfs/file.c:965, Linux v6.18.46) and
`nfs4_file_operations` (fs/nfs/nfs4file.c:449), both to `nfs_check_flags`
(fs/nfs/file.c:50-56), whose only refusal is over `O_APPEND | O_DIRECT`
together — two bits inside this mask — so an `arg` clear of the mask
passes it.  Every other bit of `arg` is discarded by the closing
`f_flags = (arg & SETFL_MASK) | (f_flags & ~SETFL_MASK)` (:83) and there
is no `arg & ~valid` test anywhere in `setfl`, which is why the test is a
MASK and not an equality: musl ORs O_LARGEFILE into every `F_SETFL` it
issues.  The argument in full is on Rocq's `Fcntl.setfl_acted_on`. -/
def setfl_acted_on : Int :=
  O_APPEND + O_NONBLOCK + FASYNC + O_DIRECT + O_NOATIME

/-- Does this `F_SETFL` leave the open file description exactly as it
found it?  Two conditions, both needed: `arg` names none of the bits
`setfl` reads, AND the fd is one the model itself opened, so that the two
tests reading the file's CURRENT flags —
`((arg ^ f_flags) & O_APPEND) && IS_APPEND(inode)` (fs/fcntl.c:48, Linux
v6.18.46, commit 1f99e9ab748f) and
`((arg ^ f_flags) & FASYNC) && f_op->fasync` (:75) — are known to be
dead.  For a file, directory or write-created fd that is a theorem about
which words `Open.modeled_open_flags` admits (Rocq's
`modeled_open_flags_clear_of_setfl` and
`open_ignored_flags_clear_of_setfl_current`; the file header says why
neither can be stated here yet).  `do_fcntl` narrows `arg` to its low 32
bits (`int argi = (int)arg`, :448) before `setfl` sees it; masking the
full 64 agrees because no bit of the mask reaches the high half
(`setfl_acted_on_fits_32`).

The per-kind arms, each argued on Rocq's `Fcntl.setfl_noop_on`:

- `FdChannel`: `false`.  fds 0/1/2 carry the flags of whoever ran the
  binary, so "this changes nothing" is not the model's to say.
- `FdFileA`: `false`, the one kind whose `f_flags` provably CARRIES a bit
  `setfl` reads: the append word sets O_APPEND and `do_dentry_open`
  clears only `O_CREAT | O_EXCL | O_NOCTTY | O_TRUNC` (fs/open.c:981,
  Linux v6.18.46).  For an `arg` the mask test passes, the xor in
  `((arg ^ f_flags) & O_APPEND) && IS_APPEND(inode)` (fs/fcntl.c:48) is
  nonzero, so the answer turns on the inode's append-only attribute, which
  the model does not carry (-EPERM where it is set); where it is not set,
  the closing assignment (:83) CLEARS O_APPEND, and every later write
  through the fd lands at `f_pos` rather than at the end of file.
- `FdFile`, `FdFileW`, `FdFileRW`, `FdDir`, `FdSocket`: the mask test.
  O_NONBLOCK is admitted by `openat` and does reach `f_flags`, and it
  costs this arm nothing because `setfl` has no error path keyed on it:
  the bit appears only in `SETFL_MASK`, the dead SunOS fixup and the
  closing assignment (fs/fcntl.c:37, :57-59, :83, Linux v6.18.46).  A
  socket's word is `O_RDWR` exactly (`socket_f_flags`), disjoint from the
  mask.
- `FdDevNull`: `false`, fail-closed.  /dev/null is a character device,
  the case the O_NONBLOCK remark above excludes by name; a real answer
  would need the `f_flags` word this entry does not record and the fact
  that `null_fops` (drivers/char/mem.c:644-652, Linux v6.18.46) reads none
  of the bits
  `setfl` can set, and neither is written down here.
- `FdUrandom`: `false`, fail-closed for the /dev/null reason: a character
  device whose `f_flags` word the entry does not record.  A no-op answer
  for an `arg` naming none of `setfl_acted_on`'s bits is derivable — no
  branch of `setfl` fires on such a word — and is not written.  The device
  is NOT inert under `setfl` at large: `urandom_fops` carries `.fasync =
  random_fasync` (drivers/char/random.c:1577, Linux v6.18.46), which
  `setfl` calls on a FASYNC toggle (fs/fcntl.c:75-76, Linux v6.18.46), so
  an answer keyed on "the device reads none of the bits" would be wrong
  on `arg = FASYNC`; only the mask makes the no-op derivable.  Rocq's
  bullet for this kind (`Sys/Fs/Fcntl.v`, on `setfl_noop_on`) says the
  device reads none of the bits `setfl` can set, which is wrong about
  FASYNC and is owed a `comments:` PR; the pointer to Rocq above does not
  extend to that bullet.
- `FdPipe`: `false`, a CHOICE rather than a gap.  Every `FdPipe` the
  model can build was created with flags 0, so answering 0 would be sound
  today; it is not done because that fact is about the one shape `pipe2`
  admits rather than about the kind, and O_DIRECT is live on a pipe —
  it is the packet-mode bit, `is_packetized` being
  `(file->f_flags & O_DIRECT) != 0` (fs/pipe.c:415-418, Linux v6.18.46),
  inside `SETFL_MASK`, so an `arg` this predicate would call a no-op CLEARS
  it — and `pipeanon_fops` carries `.fasync = pipe_fasync` (fs/pipe.c:1264),
  so
  the FASYNC test is live too.

ENUMERATED, no wildcard: the wildcard this replaced in Rocq was
extensionally right for four kinds and silently wrong for the fifth to
fall into it. -/
def setfl_noop_on (e : FdEntry) (arg : word) : Bool :=
  match e with
  | .FdChannel _ => false
  | .FdFileA _ _ => false
  | .FdFile _ _ | .FdFileW _ _ | .FdFileRW _ _ | .FdDir | .FdSocket _ =>
      bv_unsigned (bv_and arg (Z_to_bv 64 setfl_acted_on)) = 0
  | .FdDevNull _ _ => false
  | .FdUrandom => false
  | .FdPipe _ _ => false

/-- The truncation half of `setfl_noop_on`'s argument: `do_fcntl` narrows
`arg` with `int argi = (int)arg` (fs/fcntl.c:448, Linux v6.18.46, commit
1f99e9ab748f) before `setfl(fd, filp, argi)` (:476), so the kernel reads
only the low 32 bits; the predicate masks the full 64.  The two agree
exactly because no bit of the mask reaches the high half, and a bit added
there later would silently break that.  Rocq: `setfl_acted_on_fits_32`. -/
theorem setfl_acted_on_fits_32 : setfl_acted_on < 2 ^ 32 := by decide

/-- THE WHOLE OF A SOCKET'S `f_flags`, which is what makes F_GETFL
answerable on one fd kind and no other.  `F_GETFL` is `err =
filp->f_flags`, verbatim and unmasked (`do_fcntl`, fs/fcntl.c:472-474,
Linux v6.18.46, commit 1f99e9ab748f), and for a socket the model knows
that word by a chain every link of which is at that commit:
`sock_alloc_file` (net/socket.c:476-501) builds the file with
`alloc_file_pseudo(…, O_RDWR | (flags & O_NONBLOCK), &socket_file_ops)`
(:483-485); `alloc_file_pseudo` (fs/file_table.c:408-432, Linux v6.18.46)
passes that
word to `alloc_file` (:386-395), which passes it to `alloc_empty_file`
(:239), which reaches `init_file`'s `f->f_flags = flags` (:198); and the
three writes on the way back — `file->f_mode |= FMODE_NOWAIT` (:491),
`stream_open` (:494) and `file_set_fsnotify_mode` (:499) — are all to
`f_mode`.  The `flags` reaching it is `__sys_socket`'s
`sock_map_fd(sock, flags & (O_CLOEXEC | O_NONBLOCK))` (net/socket.c:1757,
Linux v6.18.46) or the `accept4` argument, and O_CLOEXEC is dropped by the
`O_RDWR | (flags & O_NONBLOCK)` expression itself.  So a socket's
`f_flags` is `O_RDWR` plus O_NONBLOCK iff SOCK_NONBLOCK was asked for,
and the two specs that put a socket on a NEW fd both decline
SOCK_NONBLOCK (the gate count, and the `socketpair` arm that would falsify
it, are on Rocq's `Fcntl.socket_f_flags`).  In the Lean tree that sentence
holds vacuously — no `Sys/Net` arm exists yet — and it stops holding the
day a socket-creating arm admits SOCK_NONBLOCK, or an arm sets O_NONBLOCK
on a socket after the fact (this file's F_SETFL, `ioctl`'s FIONBIO, both
declined today; `socket_f_flags_clear_of_setfl` below); `socket_f_flags`
moves with that arm.

NOT HERE: O_LARGEFILE.  A path open gets it from the SYSCALL ENTRY
POINT, never from `build_open_flags` (fs/open.c:1238-1361, Linux
v6.18.46): `SYSCALL_DEFINE3(open)` (fs/open.c:1456-1461),
`SYSCALL_DEFINE4(openat)` (:1463-1469), `SYSCALL_DEFINE4(openat2)`
(:1471-1493, for a non-O_PATH open) and `SYSCALL_DEFINE2(creat)`
(:1524-1531) each do
`if (force_o_largefile()) flags |= O_LARGEFILE;` before calling it, and
`socket`/`accept4` are not those entry points.

NOT LINUX ALONE, THOUGH: QEMU's user-mode emulation, a supported
implementation, ORs the bit into EVERY F_GETFL answer on a 64-bit glibc
host.  Its `do_fcntl` (`TARGET_F_GETFL`, linux-user/syscall.c:7508-7517,
QEMU 11.1.1) runs the host `fcntl`, translates the word through
`fcntl_flags_tbl`, and then `if (O_LARGEFILE == 0 && HOST_LONG_BITS == 64)
ret |= TARGET_O_LARGEFILE;` — 0100000 (linux-user/generic/fcntl.h:44,
QEMU 11.1.1).  On such a host the translation has set the bit already:
the table's `O_LARGEFILE` row (syscall.c:475-476) then has host mask and
host bits both 0, and `host_to_target_bitmask_len` (linux-user/thunk.c:
453-465) sets a row's target bit whenever `(word & host_mask) ==
host_bits`, true of every word.  glibc defines `O_LARGEFILE` 0 on x86_64
(`__O_LARGEFILE 0`, glibc 2.41 `bits/fcntl.h`; other 64-bit glibc hosts
are not read here); musl defines it non-zero on every arch (0100000
generically), so a musl-linked qemu-user answers Linux's 2.  So a socket's
word under a glibc-hosted qemu-user is 32770 where Linux's is 2.  Whether
that is a real behavior turns on AGENTS.md's bug clause — a deviation from
the implementation's OWN documented semantics — and QEMU documents no
F_GETFL semantics this deviates from: the OR carries a stated purpose
("tell 32-bit guests it uses largefile on 64-bit hosts") and its condition
reads the host alone, so it reaches a riscv64 guest by construction.  That
the 64-bit-guest case is intended is an inference from the code, not a
QEMU statement; nothing in QEMU calls it a bug.  So 32770 is a real answer
of a supported implementation and `socket_f_flags`, proving Linux's word
alone, refuses it.  `bugs/fcntl-getfl-socket-arm-admits-linux-alone.md`
records that in the shape of the `getgroups` entry.  Rocq's comment on
`Fcntl.socket_f_flags` (`Sys/Fs/Fcntl.v`, "NOTE WHAT IS NOT HERE:
O_LARGEFILE") attributes the word to "a 64-bit libc wrapper", which is
wrong about libc — musl ORs `O_LARGEFILE` into F_SETFL's ARGUMENT
(src/fcntl/fcntl.c:14) and passes F_GETFL's return through; glibc's
wrapper is not read here and is assumed to pass the word through — so
qemu-user is the one supported source of 32770 that has been read. -/
def socket_f_flags : Int := O_RDWR

/-- …and the reason a word DERIVED from the constructor stays correct for
the life of the fd: the only modeled writer of a socket file's `f_flags`
is the empty `F_SETFL`, whose closing assignment
`f_flags = (arg & SETFL_MASK) | (f_flags & ~SETFL_MASK)` (`setfl`,
fs/fcntl.c:83, Linux v6.18.46, commit 1f99e9ab748f) is the identity on a
word disjoint from `setfl_acted_on`, a superset of `SETFL_MASK`.  The
other writers Linux has are out of reach rather than inert:
`ioctl_fionbio` (fs/ioctl.c:340-361) writes the field itself,
`ioctl_fioasync` (:363-383) calls `f_op->fasync` and the write happens
two frames down: the clear is `filp->f_flags &= ~FASYNC` in
`fasync_remove_entry` (fs/fcntl.c:988-1012, at :1005, Linux v6.18.46) and
the set is `filp->f_flags |= FASYNC` in `fasync_insert_entry`
(fs/fcntl.c:1036-1064, at :1058), which `fasync_add_entry`
(fs/fcntl.c:1070-1091, same version) calls.  Neither
ioctl is modeled.  ADDING A MODELED FIONBIO OR FIOASYNC ARM BREAKS
`getfl_f_flags`'s socket arm, not merely this remark.
Rocq: `socket_f_flags_clear_of_setfl`. -/
theorem socket_f_flags_clear_of_setfl :
    bv_unsigned (bv_and (Z_to_bv 64 socket_f_flags) (Z_to_bv 64 setfl_acted_on)) = 0 := by
  decide

/-- What `F_GETFL` answers, per fd kind: `some w` where the model can
derive `filp->f_flags` exactly, `none` where it cannot.  ENUMERATED so
that a new `FdEntry` constructor is a decision rather than an inherited
decline.  The `none` kinds decline for different reasons, each argued on
Rocq's `Fcntl.getfl_f_flags`:

- `FdChannel`: the environment chose the word; no change here can help.
- `FdFile`, `FdFileW`, `FdFileRW`, `FdDir`: `openat` accepts and IGNORES
  `Open.open_ignored_flags`, and one of its bits, O_NONBLOCK, REACHES
  `f_flags`: `build_open_flags` strips only O_CLOEXEC (`u64 strip =
  O_CLOEXEC; … flags &= ~strip;`, fs/open.c:1241 and :1251, Linux
  v6.18.46, commit 1f99e9ab748f), `op->open_flag = flags` (:1314) is what
  `alloc_empty_file(op->open_flag, …)` (fs/namei.c:4124) hands to
  `init_file` (fs/file_table.c:198), and `do_dentry_open` clears only
  `O_CREAT | O_EXCL | O_NOCTTY | O_TRUNC` (fs/open.c:981, Linux v6.18.46).
  So
  `openat(p, O_RDONLY)` and `openat(p, O_RDONLY|O_NONBLOCK)` mint the same
  entry with different answers; the word is not a function of the
  constructor.  CLOSABLE by recording the open flag word on the entry.
  Rocq's comment on its `FdFileRW` arm names O_LARGEFILE and O_CLOEXEC as
  the unrecorded bits instead, and neither is in doubt: `openat`'s
  `SYSCALL_DEFINE4` sets the first on a 64-bit kernel (fs/open.c:1466-1467,
  Linux v6.18.46) and `build_open_flags` strips the second.
- `FdFileA`: the `FdFile` reason and one more: `setfl_noop_on` declines
  this kind outright, and answering `F_GETFL` while declining `F_SETFL` on
  it is the mismatch the `FdPipe` bullet refuses to make.
- `FdDevNull`: the `FdFile` reason; the access mode IS on the entry, and
  a real answer would be it plus O_LARGEFILE, but only once the O_NONBLOCK
  bit is recorded too.
- `FdUrandom`: declined for the same reason.  The access mode is O_RDONLY
  by construction, so a real answer would be `O_RDONLY + O_LARGEFILE`
  plus the O_NONBLOCK bit the open did not record — the same missing
  bit, the same decline.
- `FdPipe`: DECLINED THOUGH DERIVABLE.  `create_pipe_files`
  (fs/pipe.c:926-980, Linux v6.18.46) builds the write end with
  `O_WRONLY | (flags & (O_NONBLOCK | O_DIRECT))` (:944-946) and the read
  end with `O_RDONLY | (flags & O_NONBLOCK)` (:956-957), and `pipe2`
  declines every nonzero flag word, so the answer is a function of the
  constructor today.  What separates it from the socket is how likely the
  premise is to move: a socket's rests on the model having no
  non-blocking mode at all, a pipe's on interim narrowness a later
  widening moves casually; and `setfl_noop_on` declines the same
  constructor, so answering here would make the pair read as a
  considered distinction when it is not one.  Closing this is a `pipe2`
  change, and the two arms move together when it lands. -/
def getfl_f_flags (e : FdEntry) : Option word :=
  match e with
  | .FdSocket _ => some (Z_to_bv 64 socket_f_flags)
  | .FdChannel _ | .FdFile _ _ | .FdFileW _ _ | .FdDir => none
  | .FdFileA _ _ => none
  | .FdFileRW _ _ => none
  | .FdDevNull _ _ => none
  | .FdUrandom => none
  | .FdPipe _ _ => none

/-- `fcntl fd cmd arg`: modeled for the three commands whose answer the
model can derive, and fail-closed on every other one.

THE FD IS RESOLVED FIRST, whatever `cmd` is: `SYSCALL_DEFINE3(fcntl,
unsigned int, fd, unsigned int, cmd, unsigned long, arg)`
(fs/fcntl.c:574-592, Linux v6.18.46, commit 1f99e9ab748f) resolves the
descriptor with `CLASS(fd_raw, f)(fd)` (:576) and returns -EBADF on
`fd_empty(f)` (:579-580) before `cmd` is looked at, so a closed fd is
-EBADF even for a command the kernel does not recognize.  `fd` and `cmd`
arrive truncated to 32 bits (`Syscall.fd32`, `Syscall.cmd32`); `arg` is
`unsigned long` and arrives whole.

The three arms, from `do_fcntl` (fs/fcntl.c:444-557, Linux v6.18.46):

- `F_SETFD` answers 0 for ANY `arg`: `err = 0; set_close_on_exec(fd, argi
  & FD_CLOEXEC);` (:468-471) has no error path and reads bit 0 alone, so
  `F_SETFD, 2` CLEARS the flag rather than being an unknown-flag error.
  The bit is not recorded, and that is sound: its readers are `F_GETFD`,
  the `execve` path and `/proc/<pid>/fdinfo`, none reachable in the
  model (Rocq's `Fcntl.fcntl_spec` walks all four).
- `F_SETFL` answers 0 exactly when `setfl_noop_on` says it provably
  changes nothing (`err = setfl(fd, filp, argi)`, :475-477), and declines
  otherwise — including Dropbear's `fl | O_NONBLOCK`, since the model has
  no non-blocking mode.
- `F_GETFL` answers `filp->f_flags` (:472-474) on the one kind
  `getfl_f_flags` can derive it for.

EVERY OTHER COMMAND DECLINES.  `F_GETFD` is `get_close_on_exec(fd) ?
FD_CLOEXEC : 0` (:465-467), a bit of the fd TABLE whose three modeled
setters all discard it, so no kind has it as a function of the model.
`F_DUPFD` / `F_DUPFD_CLOEXEC` (:456-461) mint a second descriptor onto one
open file description, which an `FdEntry` carrying its own offset cannot
express; that decline is load-bearing for `State.pipe_end_live`, which
counts pipe ends by scanning the table where Linux decrements
`pipe->readers` / `pipe->writers` in `pipe_release` (fs/pipe.c:724-733,
Linux v6.18.46),
and Rocq's `Fcntl.fcntl_spec` carries what a new arm would owe.  An
unrecognized `cmd` falls to `default: break` and returns the -EINVAL
`err` was initialised to (:450, :553-555); the model declines it rather
than answer it.

Outside the modeled resolutions: `security_file_fcntl` (:587) can fail
the call under an enforcing LSM, and this spec commits to its answers
absolutely, as `Ioctl.ioctl_spec` does; and an O_PATH fd answers -EBADF
for any command outside `check_fcntl_cmd` (:559-572, consulted at
:582-585), a branch no modeled open reaches. -/
def fcntl_spec (fd cmd arg : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some e =>
      if bv_eqb cmd F_SETFD then ret_only (Z_to_bv 64 0)
      else if bv_eqb cmd F_SETFL && setfl_noop_on e arg then ret_only (Z_to_bv 64 0)
      else if bv_eqb cmd F_GETFL then
        match getfl_f_flags e with
        | some fl => ret_only fl
        | none => unmodeled
      else unmodeled

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Fcntl
