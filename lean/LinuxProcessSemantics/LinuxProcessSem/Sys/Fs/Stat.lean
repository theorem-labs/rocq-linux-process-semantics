import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Fs.Stat — readlinkat (78), newfstatat (79), fstat (80)

Mirrors `theories/LinuxProcessSem/Sys/Fs/Stat.v`, which answers to Linux
`fs/stat.c, v6.18.46`: it holds what the kernel defines there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Fs/Stat.lean`.

The baseline named above is the day-branch commit that last changed the
Rocq file (`openat: answer /dev/urandom as a read-only device`, #712),
read at `origin/nightly/09-11-2026`; it differs from the port-wide
`f44244ad` baseline in the device arm alone, which it generalises from
/dev/null to a character device the model knows and instantiates twice.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
Rocq's comments cite `newfstatat` and `fstat` over a v6.10-v6.15 window
and quote no line numbers; every number below was read at v6.18.46 and is
labelled so, and where the Rocq prose describes a shape the window has
since left behind (`vfs_fstatat`'s pathname fetch, `vfs_fstat`'s
descriptor guard) the docstring says what v6.18.46 does instead.

Two spellings differ from Rocq without changing a value: Rocq's `Z.eqb`
on `bv_unsigned` is `==` on `Int`, and Rocq's section-free `negb` is `!`.

FDFILERW AND FDFILEA DECLINE HERE, beyond Rocq.  `fstat_spec` answers
`unmodeled` on a read-write or an append-mode file, where Rocq's arm answers
through `fstat_file_spec` as for `FdFile` (the file kinds share one inode,
and neither `f_mode` nor `f_flags` is a member of `struct stat`).  The base
change that added the two constructors ported Rocq's arm into every pure
helper that names either and declined both in every spec arm that does, so
that each arm is ported later against pins of its own;
`Checks/Cases/Fs/Stat.lean`'s `a17_rdwr_fstat_declines` and
`a17_append_fstat_declines` hold the declines.  No run an example can reach
is narrowed: none can hold either kind yet (`State/Fd.lean`'s constructor
notes say why, and when that stops being true). -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Stat

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- `readlinkat dirfd path buf bufsiz`: the modeled file system has no
symlinks (`Fs.lean`: paths are uninterpreted names, no symlink objects),
so no path a program can name resolves to one, and readlink(2) on
anything that is not a symlink is -EINVAL.  The argument in full — why
the buffer is not checked, and the deliberate coarsening of a missing
path's -ENOENT and a bad pointer's -EFAULT to -EINVAL that
bugs/readlinkat-path-not-interpreted.md records as false rejections — is
on Rocq's `Stat.readlinkat_spec`; what follows is the kernel each arm
rests on, read at Linux v6.18.46 (commit 1f99e9ab748f).

THE ENTRY POINT IS ONE CALL.  `SYSCALL_DEFINE4(readlinkat, int, dfd,
const char __user *, pathname, char __user *, buf, int, bufsiz)`
(fs/stat.c:604-608, v6.18.46) is `do_readlinkat(dfd, pathname, buf, bufsiz)`
(:607), and `do_readlinkat` (fs/stat.c:563-602) decides everything below:
`if (bufsiz <= 0) return -EINVAL` (:571-572) before any fetch — the gate
this spec subsumes rather than models, since its answer is the one every
arm below gives anyway; `getname_flags(pathname, LOOKUP_EMPTY)` (:569,
:575); `filename_lookup(dfd, name, lookup_flags, &path, NULL)` (:576),
whose error is returned as it is (:577-580); and for a resolved path that
is neither a symlink nor an inode with `->readlink`, `-EINVAL`, or
`-ENOENT` when the name was empty (:585-594).

WHERE THE -EINVAL IS LINUX'S AND WHERE IT IS NOT.  The spec reads no
argument but the dirfd, so under AT_FDCWD it answers -EINVAL for every
pathname, buffer and size.  Linux agrees wherever the name resolves to
something that is not a symlink (the `else` arm, fs/stat.c:593, v6.18.46)
and wherever `bufsiz <= 0` (fs/stat.c:571-572, v6.18.46).  It does not agree, and the
spec's -EINVAL is a FALSE REJECTION of a conforming trace, for a name the
walk cannot resolve (-ENOENT, or -ENOTDIR through a component that is not
a directory, `link_path_walk`, fs/namei.c:2529-2534, v6.18.46), for an
unreadable pointer (the negative length `getname_flags` returns as it is,
fs/namei.c:161-165, handed back by `filename_lookup`, :2702-2703), for a
name with no NUL within PATH_MAX (-ENAMETOOLONG, fs/namei.c:207-211,
v6.18.46), and for the EMPTY name: `do_readlinkat` passes LOOKUP_EMPTY
(fs/stat.c:569, v6.18.46), so "" resolves to the working directory and
fs/stat.c:593 (v6.18.46) answers -ENOENT for it.  bugs/readlinkat-path-not-interpreted.md records the missing
name, the unreadable pointer and the `bufsiz` gate; the empty name,
-ENOTDIR and -ENAMETOOLONG are the same coarsening and are not yet listed
there.  The pins in `Checks/Cases/Fs/Stat.lean` state the agreeing input
and the recorded false rejection separately.

THE DIRFD IS THE ONE ARGUMENT CHECKED, and only AT_FDCWD is modeled.
`filename_lookup` resolves a relative name's starting point in
`path_init` (fs/namei.c:2540-2645, v6.18.46): `nd->dfd == AT_FDCWD` takes the
working directory (:2590-2604), and any other number is looked up through
`CLASS(fd_raw, f)(nd->dfd)` and answers -EBADF when the descriptor is
empty (:2607-2611) or -ENOTDIR when it is not a directory (:2621-2622).
Asserting -EINVAL there would reject a conforming trace, so any other
dirfd is `unmodeled`, fail closed, exactly as `openat`'s is.  `dirfd`
arrives already truncated to 32 bits (`Syscall.fd32`): the parameter is
`int dfd` in the `SYSCALL_DEFINE4` above, narrowed by `__SYSCALL_DEFINEx`
(arch/riscv/include/asm/syscall_wrapper.h:82-88, v6.18.46) through `__SC_CAST`
(include/linux/syscalls.h:132), so `readlinkat(2^32 - 100, …)` names the
working directory as Linux does. -/
def readlinkat_spec (dirfd : word) : Sys SyscallEffect :=
  if !(bv_eqb dirfd AT_FDCWD32) then unmodeled   -- unmodeled dirfd: fail closed
  else err_ret EINVAL

/-- The flag WORDS `newfstatat_spec` interprets: 0 (plain `stat`) and
AT_SYMLINK_NOFOLLOW (`lstat`), the only two riscv64 musl ever puts on
syscall 79; the three-step walk through musl that establishes it is on
Rocq's `Stat.modeled_statat_flags`.  The two are also indistinguishable
IN the model — the interpreted file system has no symlink objects, so
following one is never different from not following one — and the kernel
reads the bit only to choose `LOOKUP_FOLLOW` (`statx_lookup_flags`,
fs/stat.c:284-294, v6.18.46, at :288-289).

Everything else — AT_EMPTY_PATH, AT_NO_AUTOMOUNT, the AT_STATX_SYNC_TYPE
bits, and every word `vfs_statx` (fs/stat.c:348-350) answers -EINVAL for
— is unmodeled and DECLINED, not answered; the ORDER paragraph on
`newfstatat_core_spec` says what that costs. -/
def modeled_statat_flags (flag : word) : Bool :=
  let fl := bv_unsigned flag
  (fl == 0) || (fl == AT_SYMLINK_NOFOLLOW)

/-- `newfstatat dirfd path statbuf flag` — `stat`/`lstat` as modern libc
issues them.  What is modeled is the FAILING side, which is exactly the
part of the call that writes nothing; every path that resolves is
declined, because the interpreted file system carries none of the 128
bytes a success delivers.  Why that is so, why "." and a resolved file
are declined rather than answered, the two deliberate approximations
(the -ENOENT asserted with no -ENOMEM alternative, and the flat
namespace's -ENOENT where Linux answers -ENOTDIR), and why the copy-in
ledger is on every answering arm, are argued on Rocq's
`Stat.newfstatat_core_spec` and in
bugs/newfstatat-flat-namespace-false-rejections.md; what follows is the
kernel each arm rests on, read at Linux v6.18.46 (commit 1f99e9ab748f),
where Rocq's comment describes a v6.10-v6.15 window.

THE ENTRY POINT.  `SYSCALL_DEFINE4(newfstatat, int, dfd, const char
__user *, filename, struct stat __user *, statbuf, int, flag)`
(fs/stat.c:536-547) calls `vfs_fstatat(dfd, filename, &stat, flag)`
(:542), returns its error as it is (:543-544), and reaches `cp_new_stat`
(:546) — the only writer of `statbuf` — on success alone.  So on every
arm below the kernel leaves `statbuf` untouched, which is why this spec
does not take the pointer at all: no modeled arm can deliver a byte, and
hence none can fault on the destination either.

THE ORDER IS THE KERNEL'S, and it is not chronological.  `vfs_fstatat`
(fs/stat.c:365-379, v6.18.46) fetches the pathname FIRST, in the initializer of its
`name` local (:370): `getname_maybe_null(filename, flags)`
(include/linux/fs.h:2950-2958) is plain `getname` for a flag word without
AT_EMPTY_PATH (:2952-2953), which is `getname_flags(name, 0)`
(:2944-2947).  A failure there is only STASHED as an `ERR_PTR` — the
`!name && dfd >= 0` shortcut to vfs_fstat (fs/stat.c:372-373, v6.18.46) does not fire on
one, since an `ERR_PTR` is not NULL — and `vfs_statx(dfd, name, flags |
AT_NO_AUTOMOUNT, …)` (fs/stat.c:369, :375) tests the flag word (fs/stat.c:348-350, v6.18.46,
-EINVAL for any bit outside AT_SYMLINK_NOFOLLOW | AT_NO_AUTOMOUNT |
AT_EMPTY_PATH | AT_STATX_SYNC_TYPE) before `filename_lookup` (:353) hands
the stashed value back (fs/namei.c:2697-2703, v6.18.46, `IS_ERR(name)` returns
`PTR_ERR(name)` before any walk).  So the priority of the errno the caller
sees is: the flag word, then the pathname, then the dirfd, then the file,
then -EFAULT on `statbuf`.  This spec follows that priority exactly, with
DECLINING substituted for the flag word's -EINVAL: a flag word the model
has not interpreted is one it cannot judge the call from.  `flag` arrives
already truncated to 32 bits (`Syscall.flag32`, the `int flag` above).

THE PATHNAME, with all three of `getname_flags`'s answers (fs/namei.c, v6.18.46:
136-216): `strncpy_from_user` (:157) returns -EFAULT for an unmapped byte
(lib/strncpy_from_user.c:113-155) and a negative length is returned as it
is (fs/namei.c:161-165, v6.18.46); an empty name is -ENOENT without LOOKUP_EMPTY (fs/namei.c:167-171, v6.18.46, and
:202-206), and no modeled flag word sets it, since `getname_maybe_null`
passes AT_EMPTY_PATH alone through to __getname_maybe_null
(`getname_maybe_null`, include/linux/fs.h:2955-2957, v6.18.46); a copy that fills EMBEDDED_NAME_MAX is
redone at PATH_MAX (fs/namei.c:180-195), and a PATH_MAX-long copy is -ENAMETOOLONG
(fs/namei.c:207-211).  All three preempt the dirfd, exactly as `Open.openat_spec`
has it.

THEN THE DIRFD, resolved by `path_init` (fs/namei.c:2540-2645, v6.18.46) inside the
walk: AT_FDCWD takes the working directory (:2590-2604); any other number
is looked up through `CLASS(fd_raw, f)(nd->dfd)` and is -EBADF when empty
(:2607-2611) or -ENOTDIR when not a directory (:2621-2622) — a directory
the model cannot name, so only AT_FDCWD is modeled and every other dirfd
is `unmodeled`.  `dirfd` arrives already truncated to 32 bits
(`Syscall.fd32`, the `int dfd` above), so `newfstatat(2^32 - 100, …)`
names the working directory as Linux does.

THEN THE FILE.  "." resolves to the working directory (`handle_dots`,
fs/namei.c:2096-2132, v6.18.46), whose metadata is as absent from `Fs` as a file's,
so it is declined.  Any other name the map does not hold is the walk's
own -ENOENT: `walk_component` (fs/namei.c:2134-2158, v6.18.46) steps into the last
component through `step_into` (:1984-2022), where `traverse_mounts`
(:1529-1542) answers -ENOENT for a negative dentry (:1537-1538) and the
RCU walk answers it at :2001-2002.  A name the map holds would succeed on
Linux — `vfs_statx_path` (fs/stat.c:296-315, v6.18.46) fills the `kstat` and
`cp_new_stat` (:470-507) delivers it — and is declined, since `Fs` holds
contents and no metadata.  A name the map does not hold is answered
-ENOENT even when it is a node the model's own device arms assume the
image holds — `Uapi.devnull_path` and `Uapi.urandom_path`, which
`Open.openat_spec` admits and Linux stats successfully — a sixth false
rejection beside the five bugs/newfstatat-flat-namespace-false-rejections.md
lists.  ".." is not declined and falls through to the
map's -ENOENT, which Linux never gives for it: the divergence
bugs/newfstatat-flat-namespace-false-rejections.md carries. -/
def newfstatat_core_spec (dirfd pathp flag : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  -- a flag word the model does not interpret: decline, never assert
  if !(modeled_statat_flags flag) then unmodeled
  else
    -- `getname_flags()`: all three of its answers are real errnos, and
    -- all three preempt the dirfd.
    match read_cstr i.in_mem pathp with
    | CstrTooLong => err_ret ENAMETOOLONG          -- no NUL within PATH_MAX
    | CstrFault => err_ret EFAULT                  -- unmapped byte in the path string
    | CstrOk p =>
        if path_eqb p [] then err_ret ENOENT       -- empty pathname: AT_EMPTY_PATH is not modeled
        else if !(bv_eqb dirfd AT_FDCWD32) then unmodeled  -- unmodeled dirfd: fail closed
        else if path_eqb p dot_path then unmodeled -- the working directory: no metadata in `Fs`
        else
        match fs_lookup (m_fs m) p with
        | none => err_ret ENOENT                   -- file absent: real -ENOENT, not a modeling gap
        | some _ => unmodeled                      -- resolves: 128 bytes `Fs` cannot supply

/-- The pathname fetch, recorded.  `vfs_fstatat` (fs/stat.c:365-379,
Linux v6.18.46, commit 1f99e9ab748f) fetches the pathname in the
initializer of its `name` local (:370), before it calls `vfs_statx` at
all; its callee `getname_maybe_null` (include/linux/fs.h:2950-2958, v6.18.46) is
plain `getname` (:2944-2947) for every flag word this spec answers, and
`getname_flags`'s call to strncpy_from_user (fs/namei.c:157, v6.18.46) is the
byte fetch itself.  Every outcome the core spec answers is downstream of that fetch,
so the range belongs to all of them: the bytes through the first NUL, the
first unreadable byte, or PATH_MAX (`State.cstr_access_len_aux`), the
same range `Open.openat_spec` records, short by up to seven bytes for the
reason bugs/openat-getname-word-at-a-time.md gives.  The wrapper sits
OUTSIDE the flag test, so every arm the spec ANSWERS carries the ledger —
the `CstrFault` one included, where the faulting byte itself is counted:
the kernel attempted that byte.  The declining arms cost nothing, because
`Syscall.record_copyins` carries `unmodeled` through untouched, so the
ORDER paragraph above is undisturbed.  Why the ledger is not bookkeeping —
`Run`'s backing budget charges exactly this list — is on Rocq's
`Stat.newfstatat_spec`. -/
def newfstatat_spec (dirfd pathp flag : word) : Sys SyscallEffect :=
  i <- input ;;
  record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    (newfstatat_core_spec dirfd pathp flag)

/-- THE SUCCESS ARM of `fstat`, for a descriptor on a file the interpreted
file system holds: the second of `SYSCALL_DEFINE2(newfstat)`'s two lines,
`cp_new_stat(&stat, statbuf)` (fs/stat.c:559), and everything below is
`cp_new_stat` (fs/stat.c:470-507, Linux v6.18.46, commit 1f99e9ab748f)
rather than `vfs_fstat`.  What the model determines and how it answers
what it does not — the padding and width it knows exactly, the one
member it derives under the kernel's own S_IFREG test, the members it
chooses once per file and holds fixed, the four it re-chooses at every
call and what that over-admits — is argued on Rocq's
`Stat.fstat_file_spec`, `Uapi.stat_buf_wf`, `Uapi.stat_size_ok` and
`Uapi.stat_stable_eqb`, and in bugs/fs-paths-assumed-regular-files.md
and the `bugs/` entry on fstat's unpinned members (its path is on Rocq's `stat_stable_eqb`).  The kernel lines:

- THE WIDTH AND THE PADDING.  `cp_new_stat` clears its whole stack copy
  through `INIT_STRUCT_STAT_PADDING(tmp)` (:483), the generic `memset`
  (fs/stat.c:466-468, v6.18.46; riscv64 has no `asm/stat.h` of its own, so it takes
  include/uapi/asm-generic/stat.h and leaves the macro at its default),
  assigns the members (fs/stat.c:484-505), and hands all `sizeof(tmp)` = 128 bytes
  to ONE copy_to_user call (fs/stat.c:506, v6.18.46).  So `__pad1`, `__pad2`, `__unused4` and
  `__unused5` are delivered as zero, and the write is exactly
  `Uapi.STAT_SIZE` bytes wide at `statbuf` (`Uapi.stat_buf_wf`).
- `st_size`, AND ONLY IF THE KERNEL SAYS THE FILE IS REGULAR.
  `vfs_fstat` (:276-282) reaches `vfs_getattr` (:254-263) and, for an
  inode without its own `->getattr`, `generic_fillattr` (:82-113, called
  from `vfs_getattr_nosec` at :218), which copies `i_size_read(inode)`
  into `stat->size` (:95); `cp_new_stat` copies that to `tmp.st_size`
  (:495).  For a regular file that is the file's length, and the model's
  length is the byte list `Fs` carries for the descriptor's path.  The
  IMPLICATION is the whole of the claim (`Uapi.stat_size_ok`): the model
  does NOT know the file is regular.
- THE FIVE -EOVERFLOW TESTS CANNOT FIRE ON RISCV64: the two `sizeof` tests
  on `st_dev`/`st_rdev` (:474-477) and the `st_ino`/`st_nlink` ones
  (:486-491) compare members at least as wide as their `kstat` source, and
  the `MAX_NON_LFS` one (:478-481) is inside `#if BITS_PER_LONG == 32`.

THE ORDER IS THE KERNEL'S.  `vfs_fstat` resolves the descriptor before
`cp_new_stat` runs, so -EBADF preempts everything here (`fstat_spec`);
then `copy_to_user` (include/linux/uaccess.h:216-227, v6.18.46) — which on
riscv64 with an MMU is `_copy_to_user` (lib/usercopy.c:24-27, v6.18.46),
since the `INLINE_COPY_TO_USER` of include/asm-generic/uaccess.h:95
(v6.18.46) is in force only where arch/riscv/include/asm/uaccess.h takes
that header, the no-MMU branch at :490-491, and `_copy_to_user` is
`_inline_copy_to_user` (include/linux/uaccess.h:190-200, v6.18.46) — asks
`access_ok(to, n)` (include/linux/uaccess.h:195, v6.18.46) over the whole
range before a byte moves — `__access_ok`
(include/asm-generic/access_ok.h:31-41, v6.18.46) is `(size <= limit) &&
(addr <= (limit - size))` (:40), `State.access_okb` — and `cp_new_stat`
turns its nonzero return into -EFAULT (fs/stat.c:506, v6.18.46); then the
range is either wholly writable, which is the modeled path, or partially
so, which is `unmodeled`: raw_copy_to_user (include/linux/uaccess.h:197,
v6.18.46) commits a prefix and then faults,
leaving a half-written struct this model has no vocabulary for, the shape
`Kernel.Sys.uname_spec` and `Time.gettimeofday_spec` decline for the same
reason.  Asking `access_ok` BEFORE the walk is load-bearing, for the
wrapping reason bugs/read-bytes-map-wraps-while-access-ok-over-sums-in-z.md
records.

THE CHOICE IS PINNED, per file, in `State.procst_statpins`: the first
stat of a file records the 128 bytes it delivered (`set_statpin`), and
every later stat of the same file must repeat its STABLE members
(`Uapi.stat_stable_eqb`), while `st_size`, `st_blocks` and the
timestamps are deliberately not held against the pin, because a write
moves all three.  A pin that is not `Uapi.stat_buf_wf` is declined, and
that branch is unreachable: the only writer is the branch below, which
has just checked the predicate.  It is written rather than argued away
because receptiveness is a statement about every `Model`, and an
unsatisfiable `choose` is the one way to write a non-receptive spec.

A PATH `Fs` NO LONGER HOLDS IS DECLINED.  `unlinkat` (35) removes a key
while a descriptor on it stays open, and Linux answers such an `fstat`
from the surviving inode with `st_nlink` 0 (`generic_fillattr` :91).  The
model has no contents to size and no link count to drop, so it declines —
which is also what keeps `st_nlink` among the members the pin holds
fixed. -/
def fstat_file_spec (p : path) (statbuf : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match fs_lookup (m_fs m) p with
  | none => unmodeled            -- unlinked under an open fd: no contents to size
  | some data =>
      if !(access_okb statbuf STAT_SIZE) then err_ret EFAULT
      else
        match read_bytes_map i.in_wmem statbuf (Z_to_bv 64 STAT_SIZE) with
        | none => unmodeled      -- a partial `copy_to_user` then -EFAULT
        | some _ =>
            match statpin_lookup (m_statpins m) p with
            | some b0 =>
                if !(stat_buf_wf b0) then unmodeled  -- no branch writes such a pin
                else
                  bs <- choose (fun bs : List byte =>
                                  stat_buf_wf bs = true
                                  ∧ stat_size_ok data.length bs = true
                                  ∧ stat_stable_eqb bs b0 = true) ;;
                  Monad.pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
            | none =>
                bs <- choose (fun bs : List byte =>
                                stat_buf_wf bs = true
                                ∧ stat_size_ok data.length bs = true) ;;
                set_statpin p bs ;;
                Monad.pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])

/-- THE SUCCESS ARM FOR A CHARACTER DEVICE THE MODEL KNOWS, in two
instances on the Rocq side: /dev/null (`fstat_devnull_spec`, under
`Uapi.devnull_path` and `Uapi.stat_devnull_ok`) and /dev/urandom
(`fstat_urandom_spec`, under `Uapi.urandom_path` and
`Uapi.stat_urandom_ok`).  It is
`fstat_file_spec`'s shape with the file's one implication replaced by
the device's assertions: the model KNOWS which device this descriptor is
— the assumption the openat arm states,
bugs/openat-devnull-assumed-null-device.md its cost — so `st_mode`'s type
bits, `st_rdev`, `st_size` and `st_blocks` are pinned outright, and the
members the kernel does not decide are chosen once and held in
`State.procst_statpins` under the device's path, exactly as a file's are
under its key.  `p` is that path and `ok` the device's assertions;
nothing below reads either for anything but the pin's key and the
delivery's test.  The kernel lines, at Linux v6.18.46 (commit
1f99e9ab748f): `generic_fillattr` (fs/stat.c:82-113) copies `i_mode`
(:90), `i_rdev` (:94), `i_size` (:95) and `i_blocks` (:106) off the
inode, and `cp_new_stat` (:470-507) delivers them (:488, :494, :495,
:504); `init_special_inode` (fs/inode.c:2552-2577, v6.18.46) set the S_IFCHR mode
and `i_rdev` when the node was made (:2554-2559), and `cp_new_stat`'s
`new_encode_dev` (include/linux/kdev_t.h:39-44) of the node's `MKDEV`
(:12) is what `st_rdev` carries — `Uapi.DEVNULL_RDEV` for `MKDEV(1, 3)`.

THE PIN IS CHECKED AGAINST BOTH PREDICATES before it is used, where the
file arm checks `stat_buf_wf` alone: the asserted members are INSIDE the
stable region (`st_mode` and `st_rdev`) or asserted constant (`st_size`,
`st_blocks`), so a pin that failed `ok` would leave the `choose` below
with no satisfying buffer — a non-receptive spec, the one shape `Monad`
forbids.  Declining such a pin keeps the arm receptive on every `Model`;
the branch is unreachable, since the only writer is the branch below,
which has just checked both predicates.

No `fs_lookup`: the device is not a key, and `unlinkat` cannot reach it,
so there is no unlinked-under-an-open-fd case to decline.  The rest —
-EBADF before anything, `access_ok`'s -EFAULT, the partial `copy_to_user`
decline — is `fstat_file_spec`'s argument unchanged. -/
def fstat_chrdev_spec (p : path) (ok : List byte → Bool) (statbuf : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if !(access_okb statbuf STAT_SIZE) then err_ret EFAULT
  else
    match read_bytes_map i.in_wmem statbuf (Z_to_bv 64 STAT_SIZE) with
    | none => unmodeled      -- a partial `copy_to_user` then -EFAULT
    | some _ =>
        match statpin_lookup (m_statpins m) p with
        | some b0 =>
            if !(stat_buf_wf b0 && ok b0) then unmodeled
              -- no branch writes such a pin: see above
            else
              bs <- choose (fun bs : List byte =>
                              stat_buf_wf bs = true
                              ∧ ok bs = true
                              ∧ stat_stable_eqb bs b0 = true) ;;
              Monad.pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
        | none =>
            bs <- choose (fun bs : List byte =>
                            stat_buf_wf bs = true
                            ∧ ok bs = true) ;;
            set_statpin p bs ;;
            Monad.pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])

/-- The null device: S_IFCHR, `st_rdev` 1:3 (`Uapi.DEVNULL_RDEV`, the
`new_encode_dev` of `MKDEV(1, 3)`, include/linux/kdev_t.h:39-44 and :12
at Linux v6.18.46), zero size and blocks (`Uapi.stat_devnull_ok`):
`write_null` (drivers/char/mem.c:418-422) returns without touching the
inode, so `i_size` and `i_blocks` stay what `mknod` left, and the pin is
keyed under `Uapi.devnull_path`. -/
def fstat_devnull_spec (statbuf : word) : Sys SyscallEffect :=
  fstat_chrdev_spec devnull_path stat_devnull_ok statbuf

/-- The random device: S_IFCHR, `st_rdev` 1:9 (`Uapi.URANDOM_RDEV`, the
`new_encode_dev` of `MKDEV(1, 9)`, include/linux/kdev_t.h:39-44 and :12
at Linux v6.18.46), zero size and blocks (`Uapi.stat_urandom_ok`), on the
assumption the openat arm states (Rocq's `Stat.fstat_urandom_spec` names
it) — that the image's /dev/urandom is the random device, major 1 minor
9, the `urandom` entry of the character-device table `memory_open`
(drivers/char/mem.c:707-727, v6.18.46) installs for minor 9 (:701).
`cp_new_stat` (fs/stat.c:470-507, v6.18.46) reads the same inode members
it reads for /dev/null, and the zero `st_size` and `st_blocks` rest on
the same premise about a node nothing ever resized: a write to the device
is `random_write_iter` (drivers/char/random.c:1448-1451, v6.18.46, the
write_iter of `urandom_fops` at :1572-1581), which is `write_pool_user`
(:1420-1446) — the bytes are mixed into the pool and counted, and the
inode is not touched.  The pin is keyed under `Uapi.urandom_path`. -/
def fstat_urandom_spec (statbuf : word) : Sys SyscallEffect :=
  fstat_chrdev_spec urandom_path stat_urandom_ok statbuf

/-- `fstat fd statbuf` — `newfstatat`'s descriptor-only sibling, and the
number riscv64 musl really reaches for `fstat()`.  THE SPEC IS THE ORDER,
AND THE ORDER IS TWO STEPS: `SYSCALL_DEFINE2(newfstat, unsigned int, fd,
struct stat __user *, statbuf)` (fs/stat.c:550-560, Linux v6.18.46,
commit 1f99e9ab748f) is `vfs_fstat(fd, &stat)` (:555), whose error is
returned as it is (:556-557), and then `cp_new_stat(&stat, statbuf)`
(:559).  Everything this spec answers itself is the first line, and
everything it delegates is the second.

`vfs_fstat` (fs/stat.c:276-282, v6.18.46) resolves the descriptor before it looks
at anything else — `CLASS(fd_raw, f)(fd)` (:278) and `if (fd_empty(f))
return -EBADF` (:279-280) — so a call that names a closed fd AND a bad
`statbuf` is -EBADF and never -EFAULT: `cp_new_stat`, which is where a
bad `statbuf` would be noticed, has not run.  Rocq's comment describes
the two earlier spellings of that guard (`fdget_raw` with `!f.file`, then
`!fd_file(f)`); at v6.18.46 it is the `CLASS(fd_raw, …)` form, and the
-EBADF is asserted with no alternative because nothing can fail before
it.  The errnos reachable past an open descriptor are `fstat_file_spec`'s
subject, and one is outside the model entirely: `vfs_getattr` (:254-263)
runs `security_inode_getattr` (:259-261) first, which an LSM may refuse,
and this model has no security module — a premise on the environment
rather than a claim about Linux.

WHERE riscv64 INHERITS 80: the generic table's `__NR3264_fstat` is 80
(include/uapi/asm-generic/unistd.h:212-213, v6.18.46, `__SC_3264(__NR3264_fstat,
sys_fstat64, sys_newfstat)`), and the table riscv generates has the entry
`80 64 fstat sys_newfstat` (scripts/syscall.tbl:104), whose `64` ABI token
comes from `syscall_abis_64 += common,64` (scripts/Makefile.asm-headers:19;
arch/riscv/kernel/Makefile.syscalls:4 appends only `riscv`, `rlimit` and
`memfd_secret`).  The definition is compiled because riscv defines
`__ARCH_WANT_NEW_STAT` (arch/riscv/include/asm/unistd.h:20, v6.18.46), the only
guard on it (fs/stat.c:464, closed at :561).

THE DESCRIPTOR IS 32 BITS, and the truncation is the syscall wrapper's:
`fd` is `unsigned int` above, `__SYSCALL_DEFINEx`
(arch/riscv/include/asm/syscall_wrapper.h:82-88, v6.18.46) widens it to a `long` on
the way in and `__SC_CAST` (include/linux/syscalls.h:132) discards the
high half at the call.  `Syscall.fd32` is that cast, so a register of all
ones is fd -1 and -EBADF, and a register of 2^32 is fd ZERO — a live
descriptor, not a rejected one.

THE MATCH BELOW IS TOTAL ON `FdEntry` ON PURPOSE, with no wildcard: a new
constructor is a new kind of file, and whoever adds it must decide what
`fstat` says about it.  The file kinds share one answer because they share
one inode — neither `f_mode` nor `f_flags` is a member of `struct stat`
(`generic_fillattr` reads the inode alone, fs/stat.c:88-106, v6.18.46), so how a
descriptor was opened is not something a stat can report.  /dev/null
answers through `fstat_devnull_spec` and /dev/urandom through
`fstat_urandom_spec`: the model minted both descriptors knowing which
device each is, so the type bits and the device number are asserted
where the file arm can only imply.  The four other kinds decline, and
why each is as far from an answer as it is — a channel's type bits are
undecidable, a directory's size and blocks are the filesystem's own
bookkeeping, a socket's `st_ino`/`st_dev`/timestamps are out of reach
though its mode is a constant (`sock_alloc`, net/socket.c, v6.18.46), a pipe's
size and blocks are not even the queue's length — is on Rocq's
`Stat.fstat_spec`. -/
def fstat_spec (fd statbuf : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none                  => err_ret EBADF          -- `vfs_fstat`'s own answer, before `statbuf` is touched
  | some (.FdChannel _)   => unmodeled              -- pipe, socket or terminal: even the type bits are undecided
  | some (.FdFile p _)    => fstat_file_spec p statbuf   -- `cp_new_stat` over the file's inode
  | some (.FdFileW p _)   => fstat_file_spec p statbuf   -- the same inode, opened for writing
  | some (.FdFileA _ _) => unmodeled -- declined: see the file header
  | some (.FdFileRW _ _) => unmodeled -- declined: see the file header
  | some .FdDir           => unmodeled              -- S_IFDIR is known; a directory's size and blocks are not
  | some (.FdSocket _)    => unmodeled              -- mode/uid/gid are known; ino, dev and the timestamps are not
  | some (.FdPipe _ _)    => unmodeled              -- S_IFIFO is known; a pipe's size and blocks are not the queue's length
  | some (.FdDevNull _ _) => fstat_devnull_spec statbuf
                                                    -- the null device: S_IFCHR, `st_rdev` 1:3, `st_size` and
                                                    -- `st_blocks` 0 asserted (`Uapi.stat_devnull_ok`), the rest
                                                    -- pinned once under `Uapi.devnull_path`
  | some .FdUrandom       => fstat_urandom_spec statbuf
                                                    -- the random device: S_IFCHR, `st_rdev` 1:9
                                                    -- (`Uapi.stat_urandom_ok`), the rest pinned once under
                                                    -- `Uapi.urandom_path`

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Stat
