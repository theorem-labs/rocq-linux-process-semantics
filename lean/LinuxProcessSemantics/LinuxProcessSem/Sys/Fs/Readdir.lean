import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Fs.Readdir — getdents64 (61)

Mirrors `theories/LinuxProcessSem/Sys/Fs/Readdir.v`, which answers to Linux
`fs/readdir.c`: it holds what the kernel defines there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) throughout; the Rocq file
cites the same functions at the same version and no line numbers.  Where
the Rocq argument is long (the three reasons the listing is declined, why
`-ENOTDIR` is weaker than what `fsync` needs) they point at it rather than
repeat it; the rest is stated here, with the citations, and a correction to
either file owes the other one.

One spelling differs from Rocq without changing a value: the `Z.ltb` Bool
test of `getdents64_no_room` is Lean's decidable `<` on `Int`.

FDFILERW AND FDFILEA DECLINE HERE, beyond Rocq.  `getdents64_spec` answers
`unmodeled` on a read-write or an append-mode file, where Rocq's arm answers
-ENOTDIR as for `FdFile` (access mode changes where a write lands, not
whether the inode has an `.iterate_shared`).  The base change that added the
two constructors ported Rocq's arm into every pure helper that names either
and declined both in every spec arm that does, so that each arm is ported
later against pins of its own; `Checks/Cases/Fs/Readdir.lean`'s
`a17_rdwr_getdents64_declines` and `a17_append_getdents64_declines` hold the
declines.  No run an example can reach is narrowed: none can hold either
kind yet (`State/Fd.lean`'s constructor notes say why, and when that stops
being true). -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Readdir

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

/-- getdents64's injectable failure: one environment condition the model
does not track.  `iterate_dir` (fs/readdir.c:105-106, Linux v6.18.46) sets
`res = -ENOENT` and skips the iteration when `IS_DEADDIR` (include/linux/fs.h:2565,
Linux v6.18.46) holds of the inode — a directory removed since the fd was
opened — and does so BEFORE it calls the filesystem's `.iterate_shared`
(fs/readdir.c:108), hence before the `-EINVAL` of `getdents64_spec` is
reached.  Why `-EBADF`, `-ENOTDIR` and `-EFAULT` are NOT in this list is the
Rocq `getdents64_errnos` note: the first two are decided from state the
model carries, and every admitted arm is settled before the kernel touches
the destination buffer. -/
def getdents64_errnos : List Int := [ENOENT]

/-- The SMALLEST record any directory entry can occupy in a
`struct linux_dirent64` buffer, in bytes.

`filldir64` (fs/readdir.c:355-356, Linux v6.18.46) computes
`reclen = ALIGN(offsetof(struct linux_dirent64, d_name) + namlen + 1, sizeof(u64))`,
and `linux_dirent64` (include/linux/dirent.h:5-11, Linux v6.18.46) is
`u64 d_ino; s64 d_off; unsigned short d_reclen; unsigned char d_type;
char d_name[]`, so the offset of `d_name` is 19.  `ALIGN(20 + namlen, 8)`
is 24 for every `namlen` from 0 to 4, so 24 is the floor over all
NON-NEGATIVE name lengths, and `dir_emit_dot`'s "." (namlen 1,
include/linux/fs.h:4016-4019, Linux v6.18.46) attains it.  What
`verify_dirent_name` (fs/readdir.c:148-151, Linux v6.18.46) buys is the
NEGATIVE side: it refuses `len <= 0` with `-EIO` (fs/readdir.c:363-365)
before the size test, and without it the `size_t` arithmetic of
`offsetof(...) + namlen + 1` would wrap a negative `namlen` to a `reclen`
under 24.  That `-EIO` is not an answer any admitted arm can reach:
`verify_dirent_name` sees the FIRST emitted name, which on each readdir
named at `getdents64_spec` is `dir_emit_dot`'s ".", and "." passes it.
The Rocq `dirent64_min_reclen` note says why a floor over ALL entries is
what lets the spec use it without knowing what the directory holds. -/
def dirent64_min_reclen : Int := 24

/-- The buffer size AS THE KERNEL COMPARES IT.  `count` arrives declared
`unsigned int` — `SYSCALL_DEFINE3(getdents64)` (fs/readdir.c:397-398,
Linux v6.18.46) — so the high half of the register is gone before anything
reads it, and is then stored into `ctx.count` (fs/readdir.c:403), which
`dir_context` (include/linux/fs.h:2210, Linux v6.18.46) declares `int`;
`filldir64`'s `reclen > ctx->count` (fs/readdir.c:367) is a SIGNED
comparison.  The two conversions compose into "the low 32 bits, read as
two's complement", which is `Syscall.sint32`.  The Rocq
`getdents64_ctx_count` note carries why the composition is observable: a
`count` at or above `2^31` is a NEGATIVE `ctx->count`, so
`getdents64(dirfd, buf, 0x80000000)` is `-EINVAL` on Linux. -/
def getdents64_ctx_count (count : word) : Int := sint32 count

/-- Is the buffer too small for the first entry, whatever that entry turns
out to be?  `filldir64`'s `reclen > ctx->count` (fs/readdir.c:367, Linux
v6.18.46) with `reclen` at its floor `dirent64_min_reclen`. -/
def getdents64_no_room (count : word) : Bool :=
  getdents64_ctx_count count < dirent64_min_reclen

/-- `getdents64 fd dirent count`: read directory entries into `dirent`.

THE SUCCESS ARM IS NOT MODELED, AND CANNOT BE FROM WHAT THIS MODEL CARRIES:
the Rocq `getdents64_spec` header gives the three independent reasons
(`FdDir` is nullary, `Fs.Fs` holds no metadata, and its key set is not the
directory), and why `dirent` is not an argument of this spec — no admitted
arm delivers a byte, so none can fault on the destination either:
`filldir64` reaches `user_write_access_begin` (include/linux/uaccess.h:569,
Linux v6.18.46) — the call is fs/readdir.c:374 — only AFTER the
`reclen > ctx->count` test (fs/readdir.c:367, Linux v6.18.46), so
`getdents64(dirfd, NULL, 0)` is `-EINVAL`, not `-EFAULT`.

ORDER, following the kernel's exactly (Linux v6.18.46):

- the fd first.  `SYSCALL_DEFINE3(getdents64)` (fs/readdir.c:400-410) takes
  `CLASS(fd_pos, f)(fd)` — the class wraps `fdget_pos` (fs/file.c:1225,
  Linux v6.18.46) — and returns `-EBADF` on `fd_empty` (include/linux/file.h:45,
  Linux v6.18.46) before `iterate_dir` is entered, so
  a closed fd is `-EBADF` whatever kind of object the number would have
  named.  `fd` arrives already truncated to 32 bits by the table's
  `Syscall.fd32`, so `getdents64(2^32, …)` names fd 0.
- then the fd's KIND.  `iterate_dir` (fs/readdir.c:88-91, Linux v6.18.46)
  opens with `int res = -ENOTDIR; if (!file->f_op->iterate_shared) goto out;`,
  so `-ENOTDIR` precedes the LSM hook `security_file_permission`
  (security/security.c:2944, Linux v6.18.46), which fs/readdir.c:93 calls,
  the fanotify hook `fsnotify_file_perm` (include/linux/fsnotify.h:204,
  Linux v6.18.46), which fs/readdir.c:97 calls, the inode lock
  (fs/readdir.c:101, Linux v6.18.46) and the `IS_DEADDIR`
  (include/linux/fs.h:2565, Linux v6.18.46) test, which fs/readdir.c:105-106
  makes, alike.
- then, on a directory, the buffer size, in `filldir64` (fs/readdir.c:366-368,
  Linux v6.18.46).

`-ENOTDIR` ON EVERY NON-DIRECTORY.  `.iterate_shared` is the directory
iterator, and no `file_operations` table for a non-directory object defines
one, so the answer does not turn on WHICH non-directory object a channel or
a file fd is attached to.  Checked at v6.18.46: `pipefifo_fops` and
`pipeanon_fops` (fs/pipe.c), `socket_file_ops` (net/socket.c),
`ext4_file_operations` (fs/ext4/file.c), `shmem_file_operations`
(mm/shmem.c), `null_fops` (drivers/char/mem.c), `urandom_fops`
(drivers/char/random.c) and `tty_fops` (drivers/tty/tty_io.c), all at Linux
v6.18.46 — not one of those seven files contains the token `iterate_shared`
at all.  The Rocq
header says why this is strictly weaker than what `Sync.fsync_spec` needs.

THE CHANNEL ARM RESTS ON A PREMISE THE MODEL DOES NOT CHECK: that the object
a launch placed on fd 0, 1 or 2 is not itself a directory.  `may_open`
(fs/namei.c:3540-3545, Linux v6.18.46) refuses a directory only for
`MAY_WRITE` and `MAY_EXEC`, so `prog < /some/dir` puts a directory on fd 0,
and `getdents64(0, buf, count)` then lists it or answers `filldir64`'s
`-EINVAL` where this arm commits to `-ENOTDIR`.  `State.ProcInput` carries
no fd table, so nothing the model holds can tell the two launches apart;
bugs/getdents64-channel-fd-assumed-not-a-directory.md records the premise,
the launch that falsifies it and the fix it waits on.

`-EINVAL` FOR A BUFFER TOO SMALL FOR THE FIRST ENTRY.  `filldir64`
(fs/readdir.c:366-368) sets `buf->error = -EINVAL` and returns false on
`reclen > ctx->count`; `dir_emit_dots` (include/linux/fs.h:4026-4039,
Linux v6.18.46) turns that into a zero-length iteration, and
`SYSCALL_DEFINE3(getdents64)` (fs/readdir.c:412-414) then reports
`buf.error` BECAUSE `iterate_dir` returned 0 and the report is guarded by
`if (error >= 0)`; `buf.prev_reclen` is still 0, so the
`count - buf.ctx.count` rewrite (fs/readdir.c:415-424, Linux v6.18.46) is
skipped too.
That guard is what keeps the `-ENOENT` above: `buf` is
designated-initialized (fs/readdir.c:401-406, Linux v6.18.46), so `buf.error`
is 0 on the
`IS_DEADDIR` path, and without the `error >= 0` test the syscall would
report that 0 instead of `iterate_dir`'s `-ENOENT`.

THAT ARM RESTS ON ONE PREMISE: THE ITERATION EMITS AT LEAST ONE ENTRY.
`dir_emit_dots` emits "." first at position 0 (include/linux/fs.h:4028-4031),
and it is the first thing that can emit an entry or return a value in the
readdir tmpfs and sysfs install: tmpfs's `offset_readdir` (fs/libfs.c:555-562,
Linux v6.18.46), reached through `simple_offset_dir_operations`
(fs/libfs.c:568-573), and sysfs's `kernfs_fop_readdir`
(fs/kernfs/dir.c:1884-1893, Linux v6.18.46) — what precedes it is a
`lockdep_assert_held` (fs/libfs.c:559) and five local initialisations
(fs/kernfs/dir.c:1886-1890), none of which can do either.  THIS IS THE
BOUND WORTH NAMING: it holds of THOSE TWO, not of every filesystem, and
PROCFS IS ALREADY OUTSIDE IT.  `proc_dir_operations` installs `proc_readdir`
(fs/proc/generic.c:330-339, Linux v6.18.46, registered at :349), not the
`proc_readdir_de` (fs/proc/generic.c:289-295) it tail-calls, and
`proc_readdir` returns 1 having emitted nothing when the superblock carries
`subset=pid` (`fs_info->pidonly == PROC_PIDONLY_ON`, fs/proc/generic.c:335-336,
Linux v6.18.46; Documentation/filesystems/proc.rst:2403, Linux v6.18.46):
`iterate_dir` hands that 1 back (fs/readdir.c:108,115, Linux v6.18.46),
`error >= 0` picks up an untouched `buf.error` (fs/readdir.c:413-414, Linux
v6.18.46), and getdents64 ANSWERS 0 where this arm says
`-EINVAL`.  A modeled run reaches it only with an fd opened on a generic
procfs directory before `mount -o remount,subset=pid` hid it — the model has
no `mount`, so the remount is another process's — and
bugs/getdents64-position-zero-premise-excludes-pidonly-procfs.md records
that residual.  And every `FdDir` a modeled run can hold IS at
position 0: the Rocq header walks the modeled syscalls that could advance
one and finds none does, and this arm does not either — `filldir64` writes
nothing on the size refusal, `dir_emit_dots` leaves `ctx->pos` at 0 when
`dir_emit_dot` returns false (include/linux/fs.h:4029-4030, Linux v6.18.46),
and `iterate_dir`'s `file->f_pos = ctx->pos` (fs/readdir.c:109, Linux
v6.18.46) writes back the 0 it read.  GIVE `FdDir` A POSITION, or give this spec a success arm that
advances one, and the `-EINVAL` has to be conditioned on the position.

APPROXIMATION, and it is a NARROWING rather than a wrong answer: the LSM
verdict of `security_file_permission` and the fanotify response of
`fsnotify_file_perm` sit between the `-ENOTDIR` and the `-EINVAL`, neither
errno is documented for getdents(2), and neither is offered here; under a
denying LSM or a `FAN_DENY` listener this spec REJECTS a conforming trace on
the directory arm.  bugs/getdents64-lsm-and-fanotify-denials-not-admitted.md
carries the cost, why widening `getdents64_errnos` is the worse trade, and
the two probe mutations that must stay red while it stands.  The `-EINTR` of
`down_read_killable` (kernel/locking/rwsem.c, Linux v6.18.46), which
fs/readdir.c:101 calls, is unreachable rather than approximated: a fatal
signal kills the task before any return value reaches userspace.

Nothing is written on any admitted arm, so every effect is a bare return,
and no arm reads user memory either — hence no copy-in ledger. -/
def getdents64_spec (fd count : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF                   -- fd not open: `fd_empty`, before `iterate_dir`
  | some (.FdChannel _) => err_ret ENOTDIR  -- no `.iterate_shared` on any non-directory
  | some (.FdFile _ _) => err_ret ENOTDIR
  | some (.FdFileW _ _) => err_ret ENOTDIR
  | some (.FdFileA _ _) => unmodeled -- declined: see the file header
  | some (.FdFileRW _ _) => unmodeled -- declined: see the file header
  | some (.FdPipe _ _) => err_ret ENOTDIR
  | some (.FdSocket _) => err_ret ENOTDIR
  | some (.FdDevNull _ _) => err_ret ENOTDIR -- `null_fops` (drivers/char/mem.c, Linux
                                             -- v6.18.46) has no `.iterate_shared` either
  | some .FdUrandom => err_ret ENOTDIR       -- and `urandom_fops` (drivers/char/random.c,
                                             -- Linux v6.18.46) has none: the same `-ENOTDIR`
  | some .FdDir =>
      if getdents64_no_room count
      then alt (e <- errno_from getdents64_errnos ;; err_ret e)  -- the removed directory
               (err_ret EINVAL)                                  -- `filldir64`'s own answer
      else unmodeled  -- the listing itself: the header's three reasons

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Readdir
