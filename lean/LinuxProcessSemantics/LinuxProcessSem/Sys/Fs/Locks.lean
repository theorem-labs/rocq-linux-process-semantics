-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Sys/Fs/Locks.v
import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! # LinuxProcessSem.Sys.Fs.Locks — flock (32)

Mirrors `theories/LinuxProcessSem/Sys/Fs/Locks.v`, which answers to Linux
`fs/locks.c`: it holds what the kernel defines there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.

Two spellings differ from Rocq without changing a value: bit tests on the
command word are done on the `word` (`bv_and`, `bv_not`) where Rocq does
them on `bv_unsigned` in `Z` (`Z.land`, `Z.ldiff`) — the constants are
below `2^64`, so the two agree — and Rocq's `Z.eqb` / `Nat.eqb` Bool tests
are Lean's decidable `==` on `Int` and `Nat`.

A lock request on a regular file whose path NO OTHER DESCRIPTOR NAMES is
answered 0, as Rocq answers it: an FLOCK lock's owner is the `struct file`
(`flock_make_lock` sets `flc_owner = filp`, and `flock_locks_conflict`
returns false when both locks name one file), so the only conflict the
model could build is a SECOND open of the same name, which
`flock_sole_opener` excludes.  The Rocq definition `flock_spec` carries the
argument in full, together with the assumption it rests on — no process
outside the model holds a conflicting flock — and the filesystem bound:
`f_op->flock` is NULL on the filesystems a run can sit on, which
`linux-process-semantics@ff0313ba4f:bugs/flock-answers-assume-no-flock-f-op.md`
records. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Locks

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- `cmd & LOCK_MAND` — the FIRST test `SYSCALL_DEFINE2(flock)` (fs/locks.c,
Linux v6.18.46, commit 1f99e9ab748f) performs, and the only one that
answers before the descriptor is looked up at all.  Mandatory flocks were
removed, and what replaced them is a SUCCESSFUL NO-OP: the syscall logs
`pr_warn_once` and returns 0, so `flock(-1, LOCK_MAND)` is 0 and not
-EBADF.  The bit is tested, not the whole word, so OR'ing another
operation keeps this path.  Rocq:
`Z.land (bv_unsigned cmd) LOCK_MAND ≠ 0`. -/
def flock_mand_b (cmd : word) : Bool :=
  !(bv_unsigned (bv_and cmd (Z_to_bv 64 LOCK_MAND)) == 0)

/-- `cmd & ~LOCK_NB` — the word `flock_translate_cmd` switches on:
`SYSCALL_DEFINE2(flock)` calls it as `flock_translate_cmd(cmd & ~LOCK_NB)`
(fs/locks.c:2153, Linux v6.18.46).  LOCK_NB is a MODIFIER, stripped before
the operation is recognized, which is why an unrecognized operation and a
recognized one differ only in these bits.  `cmd` arrives already narrowed
to 32 bits (`Syscall.cmd32`), so this is the kernel's own `unsigned int`
arithmetic.  Rocq: `Z.ldiff (bv_unsigned cmd) LOCK_NB`. -/
def flock_base (cmd : word) : Int :=
  bv_unsigned (bv_and cmd (bv_not (Z_to_bv 64 LOCK_NB)))

/-- The three operations `flock_translate_cmd` (fs/locks.c:452-462, Linux
v6.18.46) maps to a lock type — `LOCK_SH` to `F_RDLCK`, `LOCK_EX` to
`F_WRLCK`, `LOCK_UN` to `F_UNLCK`; every other word falls off the end of
its `switch` and is -EINVAL (:461), RETURNED BEFORE THE DESCRIPTOR IS
RESOLVED.  That ordering is behavior: `flock(-1, 0)` is -EINVAL and not
-EBADF. -/
def flock_cmd_ok_b (cmd : word) : Bool :=
  let b := flock_base cmd
  (b == LOCK_SH) || (b == LOCK_EX) || (b == LOCK_UN)

/-- Is this the UNLOCK operation?  Separated from the other two because it
is the one the model can answer unconditionally — see `flock_spec`. -/
def flock_unlock_b (cmd : word) : Bool := flock_base cmd == LOCK_UN

/-- How many descriptors in the table name the path `p`.

THIS IS THE WHOLE OF THE MODEL'S LOCK STATE, and it is a count of OPENERS
rather than a record of locks: the argument in `flock_spec` turns on there
being at most one `struct file` on the inode, not on which locks it holds.
Every `FdEntry` constructor is named rather than wildcarded, so a later
constructor able to name a file in `m_fs` stops the build here instead of
being counted as "not an opener".  The kinds skipped live on an inode that
is not a key of `Fs.Fs` at all; the Rocq definition `path_openers` argues
each one. -/
def path_openers (fds : List (word × FdEntry)) (p : path) : Nat :=
  match fds with
  | [] => 0
  | (_, .FdFile q _) :: r => (if path_eqb q p then 1 else 0) + path_openers r p
  | (_, .FdFileW q _) :: r => (if path_eqb q p then 1 else 0) + path_openers r p
  | (_, .FdFileA q _) :: r => (if path_eqb q p then 1 else 0) + path_openers r p
  | (_, .FdFileRW q _) :: r => (if path_eqb q p then 1 else 0) + path_openers r p
  | (_, .FdChannel _) :: r => path_openers r p
  | (_, .FdDir) :: r => path_openers r p
  | (_, .FdSocket _) :: r => path_openers r p
  | (_, .FdPipe _ _) :: r => path_openers r p
  | (_, .FdDevNull _ _) :: r => path_openers r p   -- a device node is not a key of `Fs.Fs`
  | (_, .FdUrandom) :: r => path_openers r p       -- nor is this one

/-- Exactly one descriptor names `p`.  Applied to a path just resolved out
of the table, so the count is at least one and this says "no OTHER
descriptor names it".  Rocq: `Nat.eqb (path_openers fds p) 1`. -/
def flock_sole_opener (fds : List (word × FdEntry)) (p : path) : Bool :=
  path_openers fds p == 1

/-- `flock fd cmd`: take, convert or release a whole-file advisory lock.

THE ORDER IS THE KERNEL'S, and here it decides two answers rather than
one.  `SYSCALL_DEFINE2(flock)` (fs/locks.c, Linux v6.18.46, commit
1f99e9ab748f) does, in this order: the `LOCK_MAND` test, the
`flock_translate_cmd` of `cmd & ~LOCK_NB` (:2153), the descriptor lookup
and its `fd_empty` test (:2157-2159), the `f_mode` test (:2161-2162), the
LSM hook, and only then the lock itself.  So `flock(-1, LOCK_MAND)` is 0,
`flock(-1, 0)` is -EINVAL, and `flock(-1, LOCK_EX)` is -EBADF.

WHAT IS ANSWERED, and the kernel line each answer rests on:

- `LOCK_MAND` (any word with bit 0x20 set): 0, unconditionally and before
  the fd is looked at; see `flock_mand_b`.
- an operation `flock_translate_cmd` does not recognize: -EINVAL, also
  before the fd.
- a descriptor that is not open: -EBADF.
- `LOCK_UN` on any open descriptor: 0, UNCONDITIONALLY.  The `f_mode` test
  is `type != F_UNLCK && …` (:2161), so an unlock skips it, and
  `locks_lock_file_wait` (include/linux/filelock.h:425-428, Linux
  v6.18.46) reaches `flock_lock_inode` (fs/locks.c:1074-1144) through
  `locks_lock_inode_wait` (:2103-2117) and `flock_lock_inode_wait`
  (:2079-2094).  There `locks_get_lock_context` (:176-206) returning NULL
  is `return (flc_flags & FL_EXISTS) ? -ENOENT : 0` for an unlock
  (:1084-1088), and `FL_EXISTS` is a flag `flock_make_lock` (:465-475)
  never sets; with a context, the first loop (:1101-1109) drops whatever
  THIS `struct file` held and `lock_is_unlock` takes `goto out` with
  `error` still 0 (:1111-1115).  Neither branch reads the locks OTHER
  files hold, so an unlock cannot -EAGAIN and cannot block.
- `LOCK_SH` or `LOCK_EX` (with or without `LOCK_NB`) on an `FdFile`,
  `FdFileW`, `FdFileA` or `FdFileRW` whose path NO OTHER DESCRIPTOR NAMES:
  0.  A lock's owner is the `struct file` (`flock_make_lock` sets
  `flc_owner = filp`, and `flock_locks_conflict` returns false when both
  locks name one file), so one description never conflicts with itself and
  the only conflict the model can build is a second opener, which
  `flock_sole_opener` excludes.  The grant assumes no process outside the
  model holds a conflicting flock, and that `f_op->flock` is NULL — the
  premise
  `linux-process-semantics@ff0313ba4f:bugs/flock-answers-assume-no-flock-f-op.md`
  records.  The Rocq definition `flock_spec` argues both, and argues why
  the other fd kinds decline — a pipe's two ends, two channels, two
  directory references, a device node and `/dev/urandom` each share an
  inode the path count cannot see, and a socket has no caller.

OUT OF SCOPE, unreachable rather than approximated, argued on the Rocq
definition: -ENOMEM from `locks_alloc_lock` / `locks_get_lock_context`;
the LSM hook; the -EBADF an O_PATH descriptor gets — at `fd_empty`
(:2158-2159), not at the `f_mode` test, and for `LOCK_UN` as much as for a
lock request.  `CLASS(fd, f)(fd)` (:2157) is the `fd` class of
include/linux/file.h:83 (Linux v6.18.46), whose constructor is `fdget`;
`fdget` is `__fget_light(fd, FMODE_PATH)` (fs/file.c:1179-1182) and hands
back `EMPTY_FD` for a file whose `f_mode` carries `FMODE_PATH` (:1169-1170
on the single-user fast path; `__fget_files_rcu` applies the same mask and
returns NULL on the shared-table path, :1052-1054); an O_PATH open sets
exactly `FMODE_PATH | FMODE_OPENED` (`do_dentry_open`, fs/open.c:916-917,
Linux v6.18.46).
So :2161-2162 returns -EBADF only for a file with neither `FMODE_READ` nor
`FMODE_WRITE`, the shape an access mode of 3 produces (`init_file`,
fs/file_table.c:199, through `OPEN_FMODE`, include/linux/fs.h:3981, both
Linux v6.18.46, where `(flag + 1) & O_ACCMODE` is 0).  No modeled open
produces either shape: Rocq's `Open.modeled_open_flags` admits access
modes 0, 1 and 2 and no `O_PATH` word.  THIS STOPS BEING
TRUE when an `openat` arm mints a descriptor for `O_PATH` or for access
mode 3: `FdEntry` carries no `f_mode`, so no match here can fail the build
on it, and that port owes an `↔ Unmodeled` pin for each of the two words.
And blocking, whose -EINTR (`wait_event_interruptible`, :2087-2088) only a
conflicting shape reaches, and every conflicting shape declines above. -/
def flock_spec (fd cmd : word) : Sys SyscallEffect :=
  m <- get_model ;;
  if flock_mand_b cmd then ret_only (Z_to_bv 64 0)
    -- the removed mandatory-lock request: a no-op that succeeds, decided
    -- before the fd is looked at
  else if !(flock_cmd_ok_b cmd) then err_ret EINVAL
    -- `flock_translate_cmd` fell off its switch — still before the fd
  else
    match fd_lookup (m_fds m) fd with
    | none => err_ret EBADF                        -- fd not open
    | some e =>
        if flock_unlock_b cmd then ret_only (Z_to_bv 64 0)
          -- an unlock reads no other file's locks: unconditionally 0
        else
          match e with
          | .FdFile p _ =>
              if flock_sole_opener (m_fds m) p
              then ret_only (Z_to_bv 64 0)         -- provably uncontended
              else unmodeled                       -- a second opener could hold it
          | .FdFileW p _ =>
              if flock_sole_opener (m_fds m) p
              then ret_only (Z_to_bv 64 0)
              else unmodeled
          | .FdFileA p _ =>
              -- O_APPEND decides where a WRITE lands; `flock` locks the
              -- inode and reads no `f_flags`, so the argument transfers
              if flock_sole_opener (m_fds m) p
              then ret_only (Z_to_bv 64 0)
              else unmodeled
          | .FdFileRW p _ =>
              -- `sys_flock` reads no `f_mode` and no `f_flags` on any path
              -- to `flock_lock_inode_wait`, so the access mode cannot
              -- change the count
              if flock_sole_opener (m_fds m) p
              then ret_only (Z_to_bv 64 0)
              else unmodeled
          | .FdChannel _ => unmodeled                -- the object is not in the model
          | .FdDir => unmodeled                      -- two dirrefs are indistinguishable
          | .FdSocket _ => unmodeled                 -- no caller, and a different argument
          | .FdPipe _ _ => unmodeled                 -- both ends share one inode
          | .FdDevNull _ _ => unmodeled
              -- FAIL-CLOSED: one inode, so an `FdDevNull` count would be
              -- needed the way `path_openers` counts a path
          | .FdUrandom => unmodeled
              -- FAIL-CLOSED, for the /dev/null reason: one inode

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Locks
