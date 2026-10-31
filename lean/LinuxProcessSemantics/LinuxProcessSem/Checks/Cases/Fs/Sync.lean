-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Fs/Sync.v
import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Fs.Sync — what `fsync` and `fdatasync` answer, read off against Linux

Worked examples over `Sys.Fs.Sync.fsync_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Fs/Sync.v`.  Not part of the trusted
specification: this file is QA on the definition, written to be READ, and
every claim in it is a claim about what the kernel does, with the citation
beside it.  Line numbers are Linux v6.18.46 (commit 1f99e9ab748f).

HOW THESE ARE STATED.  A check is stated on the relation itself, as an
`iff` over EVERY outcome `o`, so one theorem fixes what is admitted and
what is refused; beside it, the concrete lie a kernel could tell is refuted
on its own.  Every proof but two is `sys_norm` or `sys_refute`
(`Checks/Cases/Tactic.lean`), which read the spec off its primitives, look
the fd up in the fixture's table through the lemmas registered below, and
decide what is closed; the two that are not, `success_moves_no_offset` and
`fsync_never_unmodeled_on_kinds`, say why where they occur.

WHAT THE ROCQ FILE PINS AND WHAT IT PROBES.  Rocq's `Checks/Cases/Fs/Sync.v`
keeps three examples — the channel arm on fd 0, the `fd32` aliasing onto
it, and that success is inert — and sends everything else to a probe
against a real kernel (`linux-process-semantics@ff0313ba4f:testing/syscall-check/tests/fsync_spec.c`).  Its
stated reason for keeping the first two, that the harness makes fd 0 a
regular file no probe can reach, no longer holds: `linux-process-semantics@ff0313ba4f:testing/vm/tracer.c`
makes three pipes and `dup2`s them onto 0, 1 and 2, and `fsync_spec.c`'s
`chan0` selector probes fd 0 and fd 2^32 directly.  That is Rocq's comment
to correct, not a reason this file inherits.  This file pins every arm:
the three Rocq keeps, on Rocq's `fsync_model`, and the socket, pipe,
/dev/null and /dev/urandom arms on `fsync_kinds_model`, which extends it.
The pipe ends and /dev/null are probed on the Rocq side, and Rocq pins the
/dev/null and /dev/urandom arms in `Checks/Cases/Fs/Open.v` (the
`call 82` conjuncts of its /dev/null and urandom walks) and the pipe ends
in `Checks/Cases/Fs/Pipe.v`.  No probe calls `fsync` on /dev/urandom
(`dev_urandom_decline.c` stops at the open and the read) or on a socket,
and the socket arm is pinned nowhere on the Rocq side, so
`socket_is_einval` below is its only check.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins prove
is that this spec and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Sync

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Sync
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The fixtures

`fsync_model` is Rocq's: the three standard channels, a read-only file
(fd 3, path `f` = 102, offset 7), a file opened for writing (fd 4, path
`g` = 103, offset 9) and a directory fd (fd 5), over a file system holding
one byte in each file.  Rocq spells it through `mkModel`, whose overflow
credentials `fixture_of` replaces with the demo user's; `fsync_spec` reads
no credentials, so no pin here can see the difference.

`fsync_kinds_model` adds the kinds Rocq's file does not pin: a fresh
socket (fd 6), both ends of one pipe (fd 7 reads, fd 8 writes, over an
empty pipe buffer 0), /dev/null opened read-write (fd 9) and /dev/urandom
(fd 11; fd 10 stays closed for the -EBADF pin). -/

/-- The fd table of `fsync_model`, named so the lookups below are stated on
it (the file header of `Checks/Cases/Tactic.lean` says why a fixture enters
the normal form through its projections or its unfolding, never both). -/
def fsync_fds : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
    (3, .FdFile [102] 7), (4, .FdFileW [103] 9), (5, .FdDir) ]

def fsync_fs : Fs.Fs := [([102], [120]), ([103], [121])]

def fsync_model : Model := fixture_of (fds := fsync_fds) (fs := fsync_fs)

/-- `fsync_fds` with the descriptors Rocq's file does not pin: a socket, both
ends of one pipe, /dev/null and /dev/urandom. -/
def fsync_kinds_fds : List (word × FdEntry) :=
  fsync_fds ++
  [ (6, .FdSocket .SkFresh), (7, .FdPipe 0 false), (8, .FdPipe 0 true),
    (9, .FdDevNull true true), (11, .FdUrandom) ]

def fsync_kinds_model : Model :=
  fixture_of (fds := fsync_kinds_fds) (pipes := [(0, ([], 0))]) (fs := fsync_fs)

/-! ### The fixtures' readings

The fd tables are read off the fixtures by projection, and each lookup
the pins need is one closed fact.  Registered in `sys_simp` at the default
priority, ahead of the `m_fds` unfolding, so the fixture stays a name in
the normal form and an `iff` whose right-hand side names it closes by
`iff_self`. -/

/-- The fd table of Rocq's fixture, read off by projection.
model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fsync_model : m_fds fsync_model = fsync_fds := rfl
/-- The fd table of the wider fixture, read off by projection.
model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fsync_kinds_model : m_fds fsync_kinds_model = fsync_kinds_fds := rfl

/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_fsync_0 : fd_lookup fsync_fds 0 = some (.FdChannel 0) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_fsync_3 : fd_lookup fsync_fds 3 = some (.FdFile [102] 7) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_fsync_4 : fd_lookup fsync_fds 4 = some (.FdFileW [103] 9) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_fsync_5 : fd_lookup fsync_fds 5 = some .FdDir := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_fsync_6 : fd_lookup fsync_fds 6 = none := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_6 : fd_lookup fsync_kinds_fds 6 = some (.FdSocket .SkFresh) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_7 : fd_lookup fsync_kinds_fds 7 = some (.FdPipe 0 false) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_8 : fd_lookup fsync_kinds_fds 8 = some (.FdPipe 0 true) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_9 : fd_lookup fsync_kinds_fds 9 = some (.FdDevNull true true) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_10 : fd_lookup fsync_kinds_fds 10 = none := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_11 : fd_lookup fsync_kinds_fds 11 = some .FdUrandom := rfl

attribute [sys_simp]
  m_fds_fsync_model m_fds_fsync_kinds_model
  lookup_fsync_0 lookup_fsync_3 lookup_fsync_4 lookup_fsync_5 lookup_fsync_6
  lookup_kinds_6 lookup_kinds_7 lookup_kinds_8 lookup_kinds_9 lookup_kinds_10 lookup_kinds_11

-- Sys/Fs/Sync.lean: the spec's unfolding, at the priority every spec has.
attribute [sys_simp low] fsync_spec.eq_1

/-! ## `do_fsync`: the fd is resolved first

`do_fsync` (fs/sync.c:205-213, Linux v6.18.46) opens with `CLASS(fd, f)(fd)`
(:207) and
returns -EBADF on `fd_empty(f)` (:209-210) before `vfs_fsync` (:212) is
entered.  So a number with no open file is -EBADF, and it is -EBADF and not
the -EINVAL of the next section whatever kind of object the number would
have named: the `.fsync` test lives in `vfs_fsync_range` (:183-184), which
a closed fd never reaches.  The pair below fixes that precedence. -/

/-- A closed fd is -EBADF, and nothing else: not 0, not -EINVAL, not a
decline (`do_fsync`, fs/sync.c:209-210).
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem closed_fd_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    fsync_spec 6 i fsync_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) fsync_model [] := by
  sys_norm

/-- The errno precedence: a kernel answering -EINVAL on a closed fd would
have to have reached `vfs_fsync_range` (fs/sync.c:183-184) without a
`struct file`, which `do_fsync` (fs/sync.c:209-210) does not allow.
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem closed_fd_is_not_einval (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fsync_spec 6 i fsync_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The same on the wider table, at the hole fd 10 leaves before fd 11.
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem closed_fd_is_ebadf_on_kinds (i : SyscallInput) (o : outcome SyscallEffect) :
    fsync_spec 10 i fsync_kinds_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) fsync_kinds_model [] := by
  sys_norm

/-! ## `vfs_fsync_range`: -EINVAL for a missing `.fsync`

`vfs_fsync_range` (fs/sync.c:179-188, Linux v6.18.46) takes `if
(!file->f_op->fsync) return -EINVAL` (:183-184) before it reads `datasync` (:185, :187).  Each arm
below names the `file_operations` table its fd kind stands for and the
fact that the table has no `.fsync` member; the refutation beside it is
the answer a kernel with an `.fsync` there would give, 0. -/

/-- fd 0, a channel, is -EINVAL: the model's channels are pipes, and
`pipeanon_fops` (fs/pipe.c:1257-1266), the table `create_pipe_files`
installs on both ends (:946, :957), has no `.fsync` line.
kernel: fs/sync.c:vfs_fsync_range; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem channel_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    fsync_spec 0 i fsync_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_model [] := by
  sys_norm

/-- …and a kernel claiming SUCCESS on it is lying: what makes the pin above
non-vacuous, as Rocq's second conjunct does.
kernel: fs/sync.c:vfs_fsync_range; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem channel_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fsync_spec 0 i fsync_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A socket is -EINVAL: `socket_file_ops` (net/socket.c:156) has no
`.fsync` member.
kernel: fs/sync.c:vfs_fsync_range; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem socket_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    fsync_spec 6 i fsync_kinds_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model [] := by
  sys_norm

/-- A kernel reporting 0 on a socket has an `.fsync` `socket_file_ops` does not carry.
kernel: fs/sync.c:vfs_fsync_range; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem socket_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fsync_spec 6 i fsync_kinds_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The read end of a pipe is -EINVAL: `pipeanon_fops` (fs/pipe.c:1257-1266)
has no `.fsync`, and it is the table both ends get (:946, :957).
kernel: fs/sync.c:vfs_fsync_range; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem pipe_read_end_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    fsync_spec 7 i fsync_kinds_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model [] := by
  sys_norm

/-- The write end too, and whatever the pipe holds: the test at
fs/sync.c:183-184 reads `f_op`, not the buffer.
kernel: fs/sync.c:vfs_fsync_range; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem pipe_write_end_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    fsync_spec 8 i fsync_kinds_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model [] := by
  sys_norm

/-- The write end is the one a caller would expect to "flush"; a kernel
reporting 0 there has an `.fsync` `pipeanon_fops` does not carry.
kernel: fs/sync.c:vfs_fsync_range; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem pipe_write_end_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fsync_spec 8 i fsync_kinds_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- /dev/null is -EINVAL: `null_fops` (drivers/char/mem.c:644-652) lists
`.llseek`, `.read`, `.write`, `.read_iter`, `.write_iter`, `.splice_write`
and `.uring_cmd` and nothing else.  It does carry `.llseek`, which is why
this does not divide the way `lseek`'s channel surface does: seekable, not
syncable.
kernel: fs/sync.c:vfs_fsync_range; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem devnull_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    fsync_spec 9 i fsync_kinds_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model [] := by
  sys_norm

/-- A kernel reporting 0 on /dev/null has an `.fsync` `null_fops` does not carry.
kernel: fs/sync.c:vfs_fsync_range; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem devnull_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fsync_spec 9 i fsync_kinds_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- /dev/urandom is -EINVAL for the same reason: the device's file_operations
table (drivers/char/random.c:1572-1581, Linux v6.18.46) lists read_iter,
write_iter, unlocked_ioctl, compat_ioctl, fasync, llseek, splice_read and
splice_write and no fsync, so `vfs_fsync_range`'s opening test
(fs/sync.c:183-184) answers before the inode is examined.  Read-only by
construction, but the access mode plays no part: the test is on the table.
kernel: fs/sync.c:vfs_fsync_range; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem urandom_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    fsync_spec 11 i fsync_kinds_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model [] := by
  sys_norm

/-- A kernel reporting 0 on /dev/urandom has an fsync method the device's
table does not carry.
kernel: fs/sync.c:vfs_fsync_range; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem urandom_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fsync_spec 11 i fsync_kinds_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The errno is -EINVAL and no other.  -ENOENT is the answer an
`errno-swap` of the `FdUrandom` arm offers, and the one no pin refused
before this file ran the spec on the kind; fs/sync.c spells no ENOENT at
all — `vfs_fsync_range` has one errno, -EINVAL at :184, and `do_fsync`
one, -EBADF at :210 — so no path through the file returns it.
kernel: fs/sync.c:vfs_fsync_range,do_fsync@v6.18.46 -/
theorem urandom_enoent_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fsync_spec 11 i fsync_kinds_model (Ok (mkEffect (errno_ret ENOENT) [] []) m' evs) := by
  sys_refute

/-- Nor -EBADF: fd 11 is open, so `do_fsync`'s `fd_empty` test
(fs/sync.c:209-210) passes and the answer is the table's, not the
descriptor's.  The pair with `closed_fd_is_ebadf_on_kinds` (fd 10, one
below, closed) is the precedence read on this table: -EBADF is decided
before the table is looked at.  Linux decides it for two kinds of number
— one naming nothing, and one naming an O_PATH file, which `fdget`
(include/linux/file.h:83, Linux v6.18.46; `__fget_light(fd, FMODE_PATH)`,
fs/file.c:1169-1170 and :1179-1182) empties by a MODE test — and only the
first exists here, since `openat` accepts no O_PATH word;
`Sys/Fs/Sync.lean`'s header carries that reading.
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/file.c:fdget@v6.18.46 -/
theorem urandom_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fsync_spec 11 i fsync_kinds_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-! ## `f_op->fsync`: 0 for a file, whatever its access mode, and for a directory

Past the `.fsync` test the call is `file->f_op->fsync(file, start, end,
datasync)` (fs/sync.c:187, Linux v6.18.46).  fs/sync.c consults `f_mode`
nowhere, so the
access mode the open granted is not read; and the model's file system has
no dirty state, so the method's success is the whole observable outcome:
0, the model unchanged, no event. -/

/-- A file opened O_RDONLY is 0.  No `f_mode` test exists in fs/sync.c to
misattribute; `vfs_fsync_range` (:183-187) reads `f_op` and the inode, and
the `.fsync` it finds is the member of `ext4_file_operations`
(fs/ext4/file.c:975) or of `shmem_file_operations` (mm/shmem.c:5263) — the
filesystems a run sits on, the premise
`linux-process-semantics@ff0313ba4f:bugs/fsync-dirfd-premise-widened-by-dotdot.md` records for this arm.
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/ext4/fsync.c:ext4_sync_file; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem readonly_file_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    fsync_spec 3 i fsync_model o ↔ o = Ok (mkEffect 0 [] []) fsync_model [] := by
  sys_norm

/-- The confident wrong answer: `write`'s -EBADF on a read-only fd
(`vfs_write`'s `FMODE_WRITE` test, fs/read_write.c:670-671) copied into an
arm that has no such test.  A kernel answering -EBADF here is refused.
kernel: fs/sync.c:vfs_fsync_range; fs/read_write.c:vfs_write@v6.18.46 -/
theorem readonly_file_is_not_ebadf (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fsync_spec 3 i fsync_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The read-only image filesystem's answer — -EINVAL from a regular file
whose table has no `.fsync` (`generic_ro_fops`, fs/read_write.c:28-33;
`squashfs_file_operations`, fs/squashfs/file.c:774-779) — is refused: the
model's file sits on ext4 or tmpfs, and
`linux-process-semantics@ff0313ba4f:bugs/fsync-dirfd-premise-widened-by-dotdot.md` records what that premise
costs on the file arms, as `dir_is_not_einval` does for the directory.
kernel: fs/sync.c:vfs_fsync_range; fs/ext4/fsync.c:ext4_sync_file; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem readonly_file_is_not_einval (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fsync_spec 3 i fsync_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A file opened for writing is 0, by the same lines and on the same
premise — narrower here: a write-mode fd cannot sit on the read-only
filesystems the entry names, because `sb_permission` (fs/namei.c:544-554)
refuses the open with -EROFS (:550-551).
kernel: fs/sync.c:do_fsync,vfs_fsync_range; fs/ext4/fsync.c:ext4_sync_file; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem write_file_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    fsync_spec 4 i fsync_model o ↔ o = Ok (mkEffect 0 [] []) fsync_model [] := by
  sys_norm

/-- …and not -EINVAL: no fsync-less table holds a write-mode regular file a
run can open (the read-only mounts refuse the open, fs/namei.c:550-551).
kernel: fs/sync.c:vfs_fsync_range; fs/namei.c:sb_permission@v6.18.46 -/
theorem write_file_is_not_einval (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fsync_spec 4 i fsync_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- Success is inert on user memory: `do_fsync` (fs/sync.c:205-213) takes
an fd and returns an int, and nothing under it copies to user space.  A
kernel reporting a write is refused.
kernel: fs/sync.c:do_fsync,vfs_fsync@v6.18.46 -/
theorem success_writes_nothing (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fsync_spec 4 i fsync_model (Ok (mkEffect 0 [(4096, [0])] []) m' evs) := by
  sys_refute

/-- Success is inert on the model: the fd's offset (9) is not moved.  The
kernel does not touch `f_pos` on this path — `vfs_fsync` (fs/sync.c:199-202)
syncs the range `0..LLONG_MAX` of the file and reads no position — and the
model's `fsync_model` comes back unchanged.  The normal form leaves the one
entry that differs, and `FdEntry` derives no decidable equality, so the
moved entry is told apart by the constructor's injectivity and the two
offsets are decided.
kernel: fs/sync.c:do_fsync,vfs_fsync@v6.18.46 -/
theorem success_moves_no_offset (i : SyscallInput) (evs : List event) :
    ¬ fsync_spec 4 i fsync_model
        (Ok (mkEffect 0 [] [])
          (fixture_of (fds := [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
                                (3, .FdFile [102] 7), (4, .FdFileW [103] 10), (5, .FdDir) ])
                      (fs := fsync_fs))
          evs) := by
  intro h
  sys_norm at h
  exact absurd (FdEntry.FdFileW.inj h.1).2 (by decide)

/-- Success emits no event: the file system is observed only at exit, and
a sync writes nothing a channel would carry.
kernel: fs/sync.c:do_fsync,vfs_fsync@v6.18.46 -/
theorem success_emits_nothing (i : SyscallInput) (m' : Model) :
    ¬ fsync_spec 4 i fsync_model (Ok (mkEffect 0 [] []) m' [event.WriteEv 1 0]) := by
  sys_refute

/-- A directory fd is 0 on the filesystems a run sits on:
`ext4_dir_operations` (fs/ext4/dir.c:682-693) sets `.fsync =
ext4_sync_file`, and `ext4_fsync_journal` (fs/ext4/fsync.c:109) sends the
non-regular inode to `ext4_force_commit` on `!S_ISREG` (:120-121);
tmpfs directories carry `simple_offset_dir_operations` (mm/shmem.c:3138),
a table (fs/libfs.c:568-573) whose `.fsync` member is `noop_fsync`
(fs/libfs.c:1629), which returns 0.  dropbear's
key publish depends on this.
kernel: fs/sync.c:vfs_fsync_range; fs/ext4/fsync.c:ext4_fsync_journal; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem dir_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    fsync_spec 5 i fsync_model o ↔ o = Ok (mkEffect 0 [] []) fsync_model [] := by
  sys_norm

/-- The answer a procfs or sysfs directory would give — `proc_dir_operations`
(fs/proc/generic.c:346-350) and `kernfs_dir_fops` (fs/kernfs/dir.c:1924-1929)
set no `.fsync` — is refused: the model's directory fd is on the
filesystems above, and `linux-process-semantics@ff0313ba4f:bugs/fsync-dirfd-premise-widened-by-dotdot.md`
records what that premise costs.
kernel: fs/ext4/fsync.c:ext4_fsync_journal; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem dir_is_not_einval (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fsync_spec 5 i fsync_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- No arm declines on this fixture, and none declines anywhere: every fd
kind is answered and so is a number that names none, the four file kinds
included (`Sys/Fs/Sync.lean`'s header; `a17_append_fsync_is_zero`,
`a17_rdwr_fsync_is_zero`).  A decline would be a modeling gap, not a
kernel behaviour, and there is none.  The fd is symbolic, so the lookup
is case-split by hand before the normalizer reads each arm: `sys_norm`
reads a spec whose gates are decided, and a `match` on an open lookup is
not one.
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem fsync_never_unmodeled_on_kinds (fd : word) (i : SyscallInput) :
    ¬ fsync_spec fd i fsync_kinds_model Unmodeled := by
  intro h
  unfold fsync_spec at h
  rw [bind_get_model_iff, m_fds_fsync_kinds_model] at h
  generalize fd_lookup fsync_kinds_fds fd = r at h
  cases r with
  | none => sys_refute at h
  | some e =>
    cases e
    all_goals sys_refute at h

/-! ## The dispatcher: two numbers, one function, one 32-bit fd

`SYSCALL_DEFINE1(fsync, unsigned int, fd)` is `do_fsync(fd, 0)`
(fs/sync.c:215-218, Linux v6.18.46) and `SYSCALL_DEFINE1(fdatasync,
unsigned int, fd)` is
`do_fsync(fd, 1)` (:220-223); `datasync` is not read until
`vfs_fsync_range` :185, after both the -EBADF (:209-210) and the -EINVAL
(:183-184) decisions, so the two agree on every arm above.  The fd is
`unsigned int`, narrowed by `__SYSCALL_DEFINEx`
(arch/riscv/include/asm/syscall_wrapper.h:82-88, Linux v6.18.46) through
`__SC_CAST` (include/linux/syscalls.h:132, Linux v6.18.46). -/

/-- Syscall 82 on fd 0 reaches the channel arm.
kernel: include/uapi/asm-generic/unistd.h:__NR_fsync; fs/sync.c:fsync,do_fsync,vfs_fsync_range@v6.18.46 -/
theorem sysno_82_is_fsync (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 82 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        fsync_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_model [] := by
  sys_norm

/-- Syscall 83 on fd 0 answers identically: "the two are one function" on
the arm that is decided before `datasync` is read.
kernel: include/uapi/asm-generic/unistd.h:__NR_fdatasync; fs/sync.c:fdatasync,do_fsync,vfs_fsync_range@v6.18.46 -/
theorem sysno_83_is_fdatasync (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 83 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        fsync_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_model [] := by
  sys_norm

/-- …and a kernel whose fdatasync succeeds where its fsync is -EINVAL has
read `datasync` before the `.fsync` test, which fs/sync.c:183-185 does not.
kernel: include/uapi/asm-generic/unistd.h:__NR_fdatasync; fs/sync.c:fdatasync,do_fsync,vfs_fsync_range@v6.18.46 -/
theorem fdatasync_channel_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 83 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        fsync_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- Syscall 83 on the read-only file is 0, as 82 is (`readonly_file_is_zero`).
kernel: include/uapi/asm-generic/unistd.h:__NR_fdatasync; fs/sync.c:fdatasync,do_fsync,vfs_fsync_range; fs/ext4/fsync.c:ext4_sync_file; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem sysno_83_on_a_file_is_zero (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 83 [3, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        fsync_model o
      ↔ o = Ok (mkEffect 0 [] []) fsync_model [] := by
  sys_norm

/-- Syscall 82 on the /dev/urandom fd of the wider table reaches the
`FdUrandom` arm: -EINVAL through the dispatcher as on the spec.
kernel: include/uapi/asm-generic/unistd.h:__NR_fsync; fs/sync.c:fsync,do_fsync,vfs_fsync_range@v6.18.46 -/
theorem sysno_82_on_urandom_is_einval (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 82 [11, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        fsync_kinds_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model [] := by
  sys_norm

/-- Syscall 83 on the same fd answers identically: `fdatasync` is
`do_fsync(fd, 1)` (fs/sync.c:220-223), and `datasync` is not read until
`vfs_fsync_range` :185, after the `.fsync` test that answers here (:183-184).
kernel: include/uapi/asm-generic/unistd.h:__NR_fdatasync; fs/sync.c:fdatasync,do_fsync,vfs_fsync_range@v6.18.46 -/
theorem sysno_83_on_urandom_is_einval (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 83 [11, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        fsync_kinds_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_kinds_model [] := by
  sys_norm

/-- `fsync(2^32)` IS `fsync(0)`: the register's high half is dropped by the
`unsigned int` cast, so the call aliases onto stdin and answers its
-EINVAL.
kernel: include/uapi/asm-generic/unistd.h:__NR_fsync; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/sync.c:fsync,vfs_fsync_range@v6.18.46 -/
theorem fd_truncates_to_32_bits (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 82 [Z_to_bv 64 (2 ^ 32), 0, 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) fsync_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_model [] := by
  sys_norm

/-- Truncation ALIASES rather than REJECTS: a model comparing the full
64-bit register would find no such fd and answer -EBADF, which the kernel
never does here.
kernel: include/uapi/asm-generic/unistd.h:__NR_fsync; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/sync.c:fsync,do_fsync,vfs_fsync_range@v6.18.46 -/
theorem fd_2_pow_32_is_not_ebadf (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 82 [Z_to_bv 64 (2 ^ 32), 0, 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none)) fsync_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The alias lands on a SUCCESS arm too: `fsync(2^32 + 3)` is `fsync(3)`,
the read-only file, and answers 0.  `fd_truncates_to_32_bits` alone is
also satisfied by a model sending every fd at or above `2^32` to 0 (stdin's
-EINVAL); this pin is what says the low half is READ, not zeroed — and
`fd_bit_31_is_read` below, that all 32 of its bits are.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/sync.c:fsync,do_fsync,vfs_fsync_range; fs/ext4/fsync.c:ext4_sync_file; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem fd_alias_onto_file_is_zero (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 82 [Z_to_bv 64 (2 ^ 32 + 3), 0, 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) fsync_model o
      ↔ o = Ok (mkEffect 0 [] []) fsync_model [] := by
  sys_norm

/-- …and not stdin's -EINVAL, which a model zeroing the low half would give.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/sync.c:fsync,do_fsync,vfs_fsync_range@v6.18.46 -/
theorem fd_alias_onto_file_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 82 [Z_to_bv 64 (2 ^ 32 + 3), 0, 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none)) fsync_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- Syscall 83 truncates the same register the same way: `fdatasync(2^32)`
is `fdatasync(0)`, stdin's -EINVAL, so the `fd32` narrowing is pinned on
both numbers and not on 82 alone.
kernel: include/uapi/asm-generic/unistd.h:__NR_fdatasync; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/sync.c:fdatasync,do_fsync,vfs_fsync_range; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem sysno_83_fd_truncates_to_32_bits (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 83 [Z_to_bv 64 (2 ^ 32), 0, 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) fsync_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) fsync_model [] := by
  sys_norm

/-- …and not -EBADF: the full-register compare `fd_2_pow_32_is_not_ebadf`
refuses on 82, refused on 83 too.
kernel: include/uapi/asm-generic/unistd.h:__NR_fdatasync; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/sync.c:fdatasync,do_fsync,vfs_fsync_range@v6.18.46 -/
theorem sysno_83_fd_2_pow_32_is_not_ebadf (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 83 [Z_to_bv 64 (2 ^ 32), 0, 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none)) fsync_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- An all-ones register, `fsync(-1)` as C spells it: the narrowing
(`__SC_CAST` to `unsigned int`, include/linux/syscalls.h:132) keeps
`0xFFFFFFFF`, and no table holds that fd — `files_lookup_fd_raw`
(include/linux/fdtable.h:72-86, Linux v6.18.46) masks an fd at or above
the table's size to NULL (:75, :84-85), and no table reaches 2^32 slots
because `sysctl_nr_open_max` (fs/file.c:100-101) caps them below INT_MAX;
the shared-table path decides the same in `__fget_files_rcu` (:989) — so
`__fget_light` hands back `EMPTY_FD` (:1169-1170, :1174-1175) and
`do_fsync` answers -EBADF (fs/sync.c:209-210, Linux v6.18.46): the errno
a "negative fd" reaches by being a very large unsigned one.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; include/linux/fdtable.h:files_lookup_fd_raw; fs/file.c:__fget_light; fs/sync.c:do_fsync@v6.18.46 -/
theorem fd_all_ones_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 82 [Z_to_bv 64 (2 ^ 64 - 1), 0, 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) fsync_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) fsync_model [] := by
  sys_norm

/-- …and it is not -EINVAL: no fd resolves, so no `.fsync` test runs.
kernel: fs/sync.c:do_fsync@v6.18.46 -/
theorem fd_all_ones_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 82 [Z_to_bv 64 (2 ^ 64 - 1), 0, 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none)) fsync_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- Bit 31 is part of the fd.  `fsync(2^31 + 3)` is fd `0x80000003`: the
`unsigned int` narrowing keeps all 32 low bits, no table holds that fd
(`files_lookup_fd_raw`, include/linux/fdtable.h:72-86, over a table
`sysctl_nr_open_max` keeps below INT_MAX, fs/file.c:100-101), and
`do_fsync` answers -EBADF (fs/sync.c:209-210; all Linux v6.18.46).  Every
other width pin in this file uses a high half of the form 2^32·k or all
ones, which a WRONG narrowing keeping only the low 31 bits also satisfies;
this pair is what separates it here (the class Rocq's
`Checks/Cases/Fs/Open.v` header names for ioctl).
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; include/linux/fdtable.h:files_lookup_fd_raw; fs/sync.c:do_fsync@v6.18.46 -/
theorem fd_bit_31_is_read (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 82 [Z_to_bv 64 (2 ^ 31 + 3), 0, 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) fsync_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) fsync_model [] := by
  sys_norm

/-- …and the 31-bit model's answer — fd 3, the read-only file, 0 — is
refused.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/sync.c:do_fsync@v6.18.46 -/
theorem fd_bit_31_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 82 [Z_to_bv 64 (2 ^ 31 + 3), 0, 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none)) fsync_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- Syscall 83 reaches the -EBADF arm as 82 does: a closed fd (6) through
the dispatcher is -EBADF (fs/sync.c:209-210) before `datasync` is read.
kernel: include/uapi/asm-generic/unistd.h:__NR_fdatasync; fs/sync.c:fdatasync,do_fsync@v6.18.46 -/
theorem sysno_83_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 83 [6, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        fsync_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) fsync_model [] := by
  sys_norm

/-- Syscall 83 reaches the directory arm as 82 does (`dir_is_zero`):
`ext4_fsync_journal` (fs/ext4/fsync.c:109) sends a non-regular inode to
`ext4_force_commit` (:120-121) whatever `datasync` says, and tmpfs's
`noop_fsync` ignores it.
kernel: include/uapi/asm-generic/unistd.h:__NR_fdatasync; fs/sync.c:fdatasync,do_fsync,vfs_fsync_range; fs/ext4/fsync.c:ext4_fsync_journal; fs/libfs.c:noop_fsync@v6.18.46 -/
theorem sysno_83_on_a_dir_is_zero (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 83 [5, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        fsync_model o
      ↔ o = Ok (mkEffect 0 [] []) fsync_model [] := by
  sys_norm

/-! ## A17: FdFileRW and FdFileA -/

def a17_sync_model : Model :=
  fixture_of (fds := [(3, .FdFileRW [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_sync_model.eq_1

/-- `fsync` through a read-write file answers 0, as it does through an
`FdFile`: `vfs_fsync_range` (fs/sync.c:183-185, Linux v6.18.46) reads
`file->f_op->fsync` and then `datasync`, and consults neither `f_mode`
nor `f_flags`, so the access mode decides nothing here.  A mutant
declining this kind, or answering it -EINVAL as it answers a pipe, fails
here.
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem a17_rdwr_fsync_is_zero (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 82 [3, 0, 0, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_sync_model o
      ↔ o = Ok (mkEffect 0 [] []) a17_sync_model [] := by
  sys_norm

def a17_sync_append_model : Model :=
  fixture_of (fds := [(3, .FdFileA [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_sync_append_model.eq_1

/-- `fsync` through an append-mode file answers 0, as it does through an
`FdFileW`: append mode is a bit of `f_flags`, which `vfs_fsync_range`
(fs/sync.c:183-185, Linux v6.18.46) never reads — it reads
`file->f_op->fsync`, the inode's own operation table.  A mutant declining
this kind, or answering it -EINVAL, fails here.
kernel: fs/sync.c:do_fsync,vfs_fsync_range@v6.18.46 -/
theorem a17_append_fsync_is_zero (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 82 [3, 0, 0, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_sync_append_model o
      ↔ o = Ok (mkEffect 0 [] []) a17_sync_append_model [] := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Sync
