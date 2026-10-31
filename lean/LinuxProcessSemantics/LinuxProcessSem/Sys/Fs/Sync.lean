import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Fs.Sync — fsync (82), fdatasync (83)

Mirrors `theories/LinuxProcessSem/Sys/Fs/Sync.v`, which answers to Linux
`fs/sync.c`: it holds what the kernel defines there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Fs/Sync.lean`.

The definition keeps the Rocq name and shape.  The docstring carries the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and points at the Rocq
definition for the argument in full, so there is one place to correct it.
Rocq's own comment cites most of these functions over a v6.10-v6.15 window
with no line numbers; every line number below was read at v6.18.46 and is
labelled so.

FDFILERW AND FDFILEA DECLINE HERE, beyond Rocq.  `fsync_spec` answers
`unmodeled` on a read-write or an append-mode file, where Rocq's arm answers
0 as for `FdFile` (`vfs_fsync_range` reads `f_op->fsync`, never `f_flags` or
`f_mode`).  The base change that added the two constructors ported Rocq's
arm into every pure helper that names either and declined both in every spec
arm that does, so that each arm is ported later against pins of its own;
`Checks/Cases/Fs/Sync.lean`'s `a17_rdwr_fsync_declines` and
`a17_append_fsync_declines` hold the declines.  No run an example can reach
is narrowed: none can hold either kind yet (`State/Fd.lean`'s constructor
notes say why, and when that stops being true). -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Sync

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

/-- `fsync fd` / `fdatasync fd`: flush this file to stable storage.  The
model's file system has no page cache, no dirty state and no durability
notion, so a SUCCESSFUL call is observationally inert — 0, no memory
touched, no event — and the content of the spec is its error cases,
which are real kernel returns.  The argument in full, including why the
two syscalls share one spec and the condition under which they must stop
sharing it, is on Rocq's `Sync.fsync_spec`; what follows is the kernel
each arm rests on, read at Linux v6.18.46 (commit 1f99e9ab748f).

THE FD IS RESOLVED FIRST.  `do_fsync` (fs/sync.c:205-213) opens with
`CLASS(fd, f)(fd)` (:207) and returns -EBADF on `fd_empty(f)` (:209-210)
before `vfs_fsync` (:212) is entered, so -EBADF strictly precedes the
-EINVAL below, and a closed fd is -EBADF whatever object the number would
have named.  Both entry points are one call to it:
`SYSCALL_DEFINE1(fsync, unsigned int, fd)` is `do_fsync(fd, 0)`
(fs/sync.c:215-218, Linux v6.18.46) and `SYSCALL_DEFINE1(fdatasync,
unsigned int, fd)` is
`do_fsync(fd, 1)` (:220-223).

-EINVAL FOR A MISSING `.fsync`.  `vfs_fsync_range` (fs/sync.c:179-188,
Linux v6.18.46) takes `if (!file->f_op->fsync) return -EINVAL` (:183-184) before it reads
`datasync` (:185, :187), so fsync and fdatasync agree on every arm below,
and the errno comes from an ABSENT METHOD, not from a test on the file.
The tables the model's fd kinds stand for carry none:

- `FdChannel`: the model's channels are pipes, and `pipeanon_fops`
  (fs/pipe.c:1257-1266, Linux v6.18.46), the table `create_pipe_files`
  installs on both ends (:946, :957), has no `.fsync` line; nor do the
  tables of the other objects a channel is attached to in practice,
  `socket_file_ops` (net/socket.c:156, Linux v6.18.46) and `tty_fops`
  (drivers/tty/tty_io.c:459, same version).  That a
  channel is a pipe is a MODEL ASSUMPTION which shell redirection onto a
  regular file falsifies; Rocq's `Sync.fsync_spec` and
  `bugs/channel-fds-assume-unidirectional-stdio.md` carry it.
- `FdSocket`: `socket_file_ops` (net/socket.c:156, Linux v6.18.46), as above.
- `FdPipe`: `pipeanon_fops` (fs/pipe.c:1257-1266, Linux v6.18.46), on both
  ends and
  whatever the pipe holds; the FIFO table `pipefifo_fops` (:1246-1255),
  which a `pipe2` fd never gets, has none either.
- `FdDevNull`: `null_fops` (drivers/char/mem.c:644-652, Linux v6.18.46)
  lists `.llseek`,
  `.read`, `.write`, `.read_iter`, `.write_iter`, `.splice_write` and
  `.uring_cmd` and nothing else — a table the model knows exactly.
- `FdUrandom`: `urandom_fops` (drivers/char/random.c:1572-1581, v6.18.46)
  lists `.read_iter`, `.write_iter`, `.unlocked_ioctl`, `.compat_ioctl`,
  `.fasync`, `.llseek`, `.splice_read` and `.splice_write` and no
  `.fsync`, so `vfs_fsync_range`'s opening test (fs/sync.c:183-184)
  answers -EINVAL here as on /dev/null.

0 FOR A FILE, WHATEVER ITS ACCESS MODE.  fs/sync.c consults `f_mode`
nowhere, so an fd opened O_RDONLY (`FdFile`) succeeds exactly as one
opened for writing (`FdFileW`); copying `write`'s -EBADF-on-a-read-only-fd
here would be a confident wrong answer.  The one fd that defeats the
shorthand is an O_PATH one, and it defeats it EARLIER than the Rocq
comment says: `do_dentry_open` (fs/open.c:916-921, Linux v6.18.46) gives
it `f_mode = FMODE_PATH | FMODE_OPENED` (:917) and `empty_fops` (:919), and `do_fsync`
opens with `CLASS(fd, f)(fd)` (fs/sync.c:207), which is `fdget`
(include/linux/file.h:83) = `__fget_light(fd, FMODE_PATH)` (fs/file.c:1179-1182,
Linux v6.18.46), and that returns `EMPTY_FD` on `f_mode & FMODE_PATH` on
BOTH of its branches: the single-owner table at :1169-1170, and a table
shared through CLONE_FILES at :1173-1175, where `__fget_files_rcu` (:989,
the mask test at :1052-1055) has already answered NULL.  So an O_PATH fd
is -EBADF at fs/sync.c:209-210 (Linux v6.18.46), by a MODE test, and the
`.fsync` test never sees `empty_fops`.  Rocq's "-EINVAL rather than 0" is
wrong about the errno — a `comments:` change owed there, recorded in
`bugs/fsync-dirfd-premise-widened-by-dotdot.md` so a Rocq-side reader
finds it; `openat` models no O_PATH flag word, so no such fd exists in
either tree and no arm answers wrongly today — this is what the O_PATH
port will read.

0 FOR A DIRECTORY FD.  `ext4_dir_operations` (fs/ext4/dir.c:682-693, Linux
v6.18.46) sets `.fsync = ext4_sync_file`, and `ext4_fsync_journal`
(fs/ext4/fsync.c:109) routes the non-regular inode to `ext4_force_commit`
on `!S_ISREG` (:120-121; the function is fs/ext4/super.c:6342, Linux
v6.18.46).  tmpfs agrees: `__shmem_get_inode` (mm/shmem.c:3073) gives a
directory `simple_offset_dir_operations` (:3138), and that table
(fs/libfs.c:568-573, Linux v6.18.46) sets `.fsync = noop_fsync`, where
`noop_fsync` (fs/libfs.c:1629) returns 0.  The bound: `proc_dir_operations`
(fs/proc/generic.c:346-350, Linux v6.18.46) and `kernfs_dir_fops`
(fs/kernfs/dir.c:1924-1929) set no `.fsync`, so a directory fd on procfs
or sysfs really is -EINVAL, and a directory's PARENT can sit on a different
filesystem than the directory — debugfs gives its directories
`simple_dir_operations` (fs/debugfs/inode.c:601, Linux v6.18.46), whose
table (fs/libfs.c:230-237) sets `.fsync = noop_fsync` too, while
`..` from /sys/kernel/debug resolves into sysfs.  The widening and its cost are
`bugs/fsync-dirfd-premise-widened-by-dotdot.md`.

THE SAME BOUND HOLDS FOR THE FILE ARMS, and is recorded in the same entry:
`FdFile`/`FdFileW` answer 0 because ext4 and tmpfs regular files carry a
`.fsync` (`ext4_file_operations`, fs/ext4/file.c:963-983, the member at
:975; `shmem_file_operations`, mm/shmem.c:5255-5268, the member at :5263
under CONFIG_TMPFS; both Linux v6.18.46), and `Fs` has no filesystem
type to ask.  A read-only image filesystem's regular files carry none:
`generic_ro_fops` (fs/read_write.c:28-33, Linux v6.18.46) has no `.fsync`
and is the regular-file table of, among others, isofs
(fs/isofs/inode.c:1430), cramfs (fs/cramfs/inode.c:103; the
`cramfs_physmem_fops` it swaps in at :105-108 has none either, :482-491),
efs (fs/efs/inode.c:151, Linux v6.18.46) and romfs (as `romfs_ro_fops`,
fs/romfs/internal.h:32, Linux v6.18.46, installed at fs/romfs/super.c:330); squashfs
(`squashfs_file_operations`, fs/squashfs/file.c:774-779) and erofs
(`erofs_file_fops`, fs/erofs/data.c:475-485, Linux v6.18.46) define their
own, without `.fsync`, and their directories (`squashfs_dir_ops`,
fs/squashfs/dir.c:219-223; `erofs_dir_fops`, fs/erofs/dir.c:124-132; both
Linux v6.18.46) likewise.  On such a filesystem `vfs_fsync_range` answers
-EINVAL (fs/sync.c:183-184, Linux v6.18.46) where this spec
proves 0 as certain: a run whose `in_fs` file sits on a squashfs or erofs
root is a real Linux variant.  Only the `FdFile` arm can reach it: each
of these filesystems is read-only at the superblock (`isofs_fill_super`,
fs/isofs/inode.c:705-709, Linux v6.18.46, refuses a writable mount with
-EACCES, and the flag is set at fs/squashfs/super.c:319,
fs/erofs/super.c:642, fs/cramfs/inode.c:602 and fs/efs/super.c:301, same
version), and
`sb_permission` (fs/namei.c:544-554, Linux v6.18.46) answers -EROFS to a
write-mode open of a regular file on one (:550-551), so no `FdFileW`
ever sits there — a model `openat` granting it has diverged at the
open, not here.  The arms stay, for the reason the entry gives (the
answer is load-bearing for a corpus program on ext4/tmpfs); what would
close it is a filesystem type on `Fs`.

OUT OF SCOPE, unreachable rather than approximated: the deferred
writeback errors `ext4_sync_file` (fs/ext4/fsync.c:141, Linux v6.18.46)
can report, including the `file_check_and_advance_wb_err` consumption
(:184), and the `datasync`-dependent skips of `sync_inode_metadata` in
`__generic_file_fsync` (fs/libfs.c:1538, Linux v6.18.46, the test at
:1553) and `generic_buffers_fsync_noflush` (fs/buffer.c:602, the test at
:616), which `ext4_fsync_nojournal` (fs/ext4/fsync.c:82, same version)
reaches.  Each needs a
writeback error, an aborted journal or a shut-down mount, and the model
has no I/O error state for one to come from.

`fd` arrives ALREADY TRUNCATED to 32 bits (`Syscall.fd32`): the ABI
declares it `unsigned int` and the wrapper narrows it
(`__SYSCALL_DEFINEx`, arch/riscv/include/asm/syscall_wrapper.h:82-88,
through `__SC_CAST`, include/linux/syscalls.h:132, Linux v6.18.46), so
`fsync(2^32)` IS
`fsync(0)` — it aliases onto stdin and answers -EINVAL, not -EBADF.

The arms are enumerated rather than collapsed into a `some _` catch-all
on purpose: some kinds answer 0 and the others -EINVAL, and the split does
not follow "is it a file" — a directory succeeds, a pipe does not — so a
new `FdEntry` constructor must force a decision here
rather than inherit whichever answer the majority gives. -/
def fsync_spec (fd : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none                  => err_ret EBADF          -- closed: -EBADF, before the file is examined
  | some (.FdChannel _)   => err_ret EINVAL         -- no `.fsync` on a pipe, socket or terminal
  | some (.FdSocket _)    => err_ret EINVAL         -- nor on a socket
  | some (.FdPipe _ _)    => err_ret EINVAL         -- nor on either pipe end
  | some (.FdDevNull _ _) => err_ret EINVAL         -- nor on /dev/null
  | some .FdUrandom       => err_ret EINVAL         -- nor on /dev/urandom: no `.fsync` in `urandom_fops`
  | some (.FdFile _ _)    => ret_only (Z_to_bv 64 0) -- O_RDONLY is not an error: no `f_mode` check
  | some (.FdFileW _ _)   => ret_only (Z_to_bv 64 0)
  | some (.FdFileA _ _) => unmodeled -- declined: see the file header
  | some (.FdFileRW _ _) => unmodeled -- declined: see the file header
  | some .FdDir           => ret_only (Z_to_bv 64 0) -- a directory fsync succeeds

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Sync
