import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570
partial: flock_spec -- T202 declines every lock request on an open fd
drift-ticket: flock_spec R-Fs-Locks-rebase -- T139 declines version-dependent closed-fd commands; T149 also declines open LOCK_MAND and access-mode mismatches; T202 declines every lock request on an open fd -/

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

EVERY LOCK REQUEST ON AN OPEN FD DECLINES HERE, beyond Rocq (T202).  Rocq
grants `LOCK_SH` through `FdFile` or `FdFileRW`, and `LOCK_EX` through
`FdFileW`, `FdFileA` or `FdFileRW`, to a sole opener.  Two filesystems that install
`.flock` answer otherwise, with a healthy server and no other holder
(Linux v6.18.46, commit 1f99e9ab748f):

- AFS refuses `LOCK_SH` from an `O_RDONLY` opener whose ACL grants read
  but not lock: fs/afs/flock.c, `afs_do_setlk_check` (:431-443), which
  `afs_do_setlk` calls (:477) before its local-mode test (:491), while
  fs/afs/security.c (Linux v6.18.46), `afs_permission` (:483-503), lets the open succeed.
- CIFS without `nobrl` makes an exclusive relock through one `struct file`
  conflict with the lock that file holds: fs/smb/client/file.c (Linux v6.18.46),
  `cifs_find_fid_lock_conflict` (:1617-1627) exempts only a shared request
  or `FL_OFDLCK`, and `cifs_lock_add_if` (:1719-1739) answers -EACCES to a
  non-waiting request and waits on itself otherwise.  The model keeps no
  lock state, so it cannot tell a first `LOCK_EX` from a relock.

The fd records no filesystem, so neither grant is certain.
bugs/flock-answers-assume-no-flock-f-op.md carries both readings.
`Checks/Cases/Fs/Locks.lean`'s `sh_on_sole_opener_declines` and
`ex_on_sole_opener_declines` hold the declines, and
`Checks/Cases/Checks/Sys/Fs/Locks.lean`'s `t202_ro_sh_eacces_declines`
and `t202_wo_ex_eacces_declines` offer each one the -EACCES.  `LOCK_UN`
is still answered ahead of the kind match, under the premise that entry
records.  No example calls flock, so no example theorem is narrowed; an
example that calls it stops being provable at its first lock request.

`path_openers` and `flock_sole_opener` keep Rocq's name and shape.
Direct `path_openers` pins check the helper. `flock_spec` no longer calls
either helper; Rocq's does. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Locks

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- `cmd & LOCK_MAND`: `SYSCALL_DEFINE2(flock)` (fs/locks.c,
Linux v6.18.46, commit 1f99e9ab748f) returns 0 for the removed mandatory
lock request. The bit is tested, so OR'ing another operation keeps this
path. The descriptor lookup's position varies by kernel version; the
closed-fd arm of `flock_spec` gives the source argument. Rocq:
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
its `switch` and is -EINVAL (:461). -/
def flock_cmd_ok_b (cmd : word) : Bool :=
  let b := flock_base cmd
  (b == LOCK_SH) || (b == LOCK_EX) || (b == LOCK_UN)

/-- Is this the UNLOCK operation?  Separated from the other two because it
has its local-path argument on `flock_spec`. -/
def flock_unlock_b (cmd : word) : Bool := flock_base cmd == LOCK_UN

/-- Count descriptors that name `p`, kept for Rocq parity.
Lean's `flock_spec` no longer calls this helper; Rocq's still does.
Naming every constructor makes a new fd kind require an explicit choice
here. Direct helper pins check that choice independently of `flock_spec`. -/
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

/-- Exactly one descriptor names `p`, kept for Rocq parity.
Rocq applies it after resolving the path from the table. Lean
`flock_spec` no longer calls it. Rocq: `Nat.eqb (path_openers fds p) 1`. -/
def flock_sole_opener (fds : List (word × FdEntry)) (p : path) : Bool :=
  path_openers fds p == 1

/-- `flock fd cmd`: take, convert or release a whole-file advisory lock.

THE ORDER DIFFERS ACROSS SUPPORTED KERNELS. `SYSCALL_DEFINE2(flock)`
(fs/locks.c, Linux v6.18.46, commit 1f99e9ab748f) tests `LOCK_MAND`,
translates the operation, then looks up the fd. Through v5.19 the fd
lookup came first; the `none` arm below carries the versioned argument.

WHAT IS ANSWERED, and the kernel line each answer rests on:

- On the local lock path, an unlock returns 0.
  (The one open descriptor Linux refuses an unlock on is an O_PATH one,
  which `fdget` masks out — the OUT OF SCOPE paragraph — and no `FdEntry`
  is one.)  The `f_mode` test is
  `type != F_UNLCK && …` (:2161), so an unlock skips it, and
  `locks_lock_file_wait` (include/linux/filelock.h:425-428, Linux
  v6.18.46) reaches `flock_lock_inode` (fs/locks.c:1074-1144) through
  `locks_lock_inode_wait`
  (:2103-2117) and `flock_lock_inode_wait` (:2079-2094).  There
  `locks_get_lock_context` (:176-206) returning NULL is
  `return (flc_flags & FL_EXISTS) ? -ENOENT : 0` for an unlock (:1084-1088),
  and `FL_EXISTS` is a flag `flock_make_lock` (:465-475) never sets; with a
  context, the first loop (:1101-1109) drops whatever THIS `struct file`
  held and `lock_is_unlock` takes `goto out` with `error` still 0
  (:1111-1115).  Neither branch reads the locks OTHER files hold, so an
  unlock cannot -EAGAIN and cannot block.

Lock requests decline for every fd kind. The header gives the AFS and
CIFS counterexamples for regular files. Other kinds lack the object or
lock state needed to establish a grant. The retained unlock answer rests
on the premise in bugs/flock-answers-assume-no-flock-f-op.md.

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
modes 0, 1 and 2 and no `O_PATH` word, and this tree has no `openat` twin
yet.  THIS STOPS BEING
TRUE when an `openat` arm mints a descriptor for `O_PATH` or for access
mode 3: `FdEntry` carries no `f_mode`, so no match here can fail the build
on it, and that port owes an `↔ Unmodeled` pin for each of the two words.
And blocking, whose -EINTR (`wait_event_interruptible`, :2087-2088) only a
conflicting shape reaches, and every conflicting shape declines above. -/
def flock_spec (fd cmd : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none =>
      -- From v6.0, db4abb4a32ec moves LOCK_MAND and command translation
      -- before fdget: 0 / -EINVAL on a closed fd. Through v5.19 fdget
      -- comes first: -EBADF for either shape (fs/locks.c,
      -- SYSCALL_DEFINE2(flock), read at v4.17, v4.19, v5.4, v5.10,
      -- v5.15, v5.16, v5.19, v6.0, v6.1, v6.6, v6.12, v6.18.46).
      -- QEMU 11.1.1 linux-user/syscall.c, TARGET_NR_flock passes through
      -- to the host. Neither version-dependent answer is certain.
      if flock_mand_b cmd then unmodeled
      else if !(flock_cmd_ok_b cmd) then unmodeled
      else err_ret EBADF
  | some e =>
      if flock_mand_b cmd then unmodeled
        -- T149: fs/locks.c, SYSCALL_DEFINE2(flock), v5.15 dispatches to
        -- f_op->flock; fs/nfs/file.c, nfs_flock, v5.15 returns -EINVAL
        -- for LOCK_MAND. Since v5.16 (90f7d7a0d0d6), the syscall returns
        -- 0 before the hook. The fd does not record its filesystem.
      else if !(flock_cmd_ok_b cmd) then err_ret EINVAL
        -- No modeled fd fails the f_mode test older kernels run first.
      else
        if flock_unlock_b cmd then ret_only (Z_to_bv 64 0)
          -- fs/nfs/file.c, nfs_flock/do_unlk, v6.18.46 reach
          -- fs/nfs/nfs4proc.c, nfs4_proc_lock/nfs4_proc_unlck, v6.18.46
          -- before the FMODE check; unlock has no access-mode check.
        else
          match e with
          | .FdFile _ _ => unmodeled  -- T202: AFS can refuse LOCK_SH; see the file header
          | .FdFileW _ _ => unmodeled -- T202: CIFS can refuse a LOCK_EX relock; see the file header
          | .FdFileA _ _ => unmodeled -- declined: see the file header
          | .FdFileRW _ _ => unmodeled -- declined: see the file header
          | .FdChannel _ => unmodeled                -- the object is not in the model
          | .FdDir => unmodeled                      -- two dirrefs are indistinguishable
          | .FdSocket _ => unmodeled                 -- no caller, and a different argument
          | .FdPipe _ _ => unmodeled                 -- both ends share one inode
          | .FdDevNull _ _ => unmodeled              -- device lock state is not recorded
          | .FdUrandom => unmodeled                  -- device lock state is not recorded

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Locks
