import LinuxProcessSemantics.LinuxProcessSem.BvBase
import LinuxProcessSemantics.LinuxProcessSem.Fs
import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Uapi.Fs — the ABI constants a file descriptor reaches

One part of `theories/LinuxProcessSem/Sys/Uapi.v`, which is split by
subsystem here so that a spec PR edits the file of its own subsystem and
never a shared constants file.  `Sys/Uapi.lean` re-exports all six; every
definition keeps its Rocq name and lives in the one namespace
`Sys.Uapi`, so `open Sys.Uapi` reaches it whichever file it is in.

WHAT GOES HERE: what a program reaches through a file descriptor or a
pathname — the open, fcntl, flock and lseek words; the `AT_` flags; the
three paths the specs share; the terminal ioctls (the tty layer
is a driver, but the request arrives through `ioctl` on an fd); the
anon-inode create masks of eventfd and timerfd (fs/eventfd.c and
fs/timerfd.c); getrandom's flags (drivers/char/random.c is a character
device, like the /dev/null this file names); the descriptor-table floor;
and the `struct stat` layout with its predicates.

TRUST BOUNDARY: this file is part of the trusted specification.

Every header line below is read at Linux v6.18.46, commit
1f99e9ab748fc5c32120de9c4eca31abfe54a4d5, the citation baseline
AGENTS.md pins.  riscv64 takes the asm-generic fcntl.h, ioctls.h and
stat.h unchanged: arch/riscv/include/uapi/asm/Kbuild generates only
unistd_32.h and unistd_64.h, and include/uapi/asm-generic/Kbuild lists
ioctls.h among its `mandatory-y` headers (line 13), so the generic header
is the riscv64 ABI verbatim.

`Int` has no bitwise operators in Lean's core library, so the four
constants Rocq spells with `Z.lor` and the one predicate that uses
`Z.land` compute through `Nat`: every operand is non-negative, so the
`Nat` operation is the same value (the reading BvBase gives its own
`bytes_le_to_nat`).  The arguments in full are on the Rocq definitions of
the same names; what is kept here is the citation and the part of each
argument that decides a value. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

/-! ## The open flags (include/uapi/asm-generic/fcntl.h) -/

/-- `#define O_WRONLY 00000001` (include/uapi/asm-generic/fcntl.h:20, Linux
v6.18.46, commit 1f99e9ab748f). -/
def O_WRONLY : Int := 1

/-- `#define O_RDWR 00000002` (include/uapi/asm-generic/fcntl.h:21, Linux
v6.18.46, commit 1f99e9ab748f).

O_RDWR has TWO readers.  It is the access mode `Open.rdwr_open_word`
admits, minting a `State.FdFileRW`; and it is the WHOLE of a socket's
`f_flags`: `sock_alloc_file` (net/socket.c, Linux v6.18.46) builds the
file with `alloc_file_pseudo(..., O_RDWR | (flags & O_NONBLOCK), ...)`, so
a socket created without SOCK_NONBLOCK has exactly this word — no
O_LARGEFILE, which only the open syscall entry points add through
`force_o_largefile` (include/linux/fcntl.h, Linux v6.18.46).
`Fcntl.socket_f_flags` is that derivation; the Rocq `Uapi.O_RDWR` carries
it in full. -/
def O_RDWR : Int := 2

/-- `#define O_CREAT 00000100` (include/uapi/asm-generic/fcntl.h:23, Linux
v6.18.46, commit 1f99e9ab748f). -/
def O_CREAT : Int := 64

/-- `#define O_EXCL 00000200` (include/uapi/asm-generic/fcntl.h:26, Linux
v6.18.46, commit 1f99e9ab748f). -/
def O_EXCL : Int := 128

/-- `#define O_TRUNC 00001000` (include/uapi/asm-generic/fcntl.h:32, Linux
v6.18.46, commit 1f99e9ab748f). -/
def O_TRUNC : Int := 512

/-- `#define O_CLOEXEC 02000000` (include/uapi/asm-generic/fcntl.h:62,
Linux v6.18.46, commit 1f99e9ab748f). -/
def O_CLOEXEC : Int := 524288

/-- `#define O_LARGEFILE 00100000` (include/uapi/asm-generic/fcntl.h:50,
Linux v6.18.46, commit 1f99e9ab748f).  musl's syscall layer ORs it into
EVERY open it issues (src/internal/syscall.h); it is meaningless on a
64-bit ABI, so it is accepted and ignored like O_CLOEXEC. -/
def O_LARGEFILE : Int := 32768

/-- `#define O_NONBLOCK 00004000` (include/uapi/asm-generic/fcntl.h:38,
Linux v6.18.46, commit 1f99e9ab748f).  riscv supplies no asm/fcntl.h of
its own, so the asm-generic value is the ABI's; O_NDELAY is an alias of
it (line 95).

Accepted and IGNORED by the open arms, for a reason that is a property
of this model's FILE SYSTEM rather than of the flag, which is why the
argument has to be re-checked whenever that file system grows.  The bit
reaches `f_flags` and stays there — `build_open_flags` (fs/open.c, Linux
v6.18.46) strips only O_CLOEXEC, and `do_dentry_open` (fs/open.c) clears
O_CREAT, O_EXCL, O_NOCTTY and O_TRUNC but not O_NONBLOCK — and the three
ways a program could tell are closed: F_GETFL declines on every fd kind
`openat` mints; the -EAGAIN of `__break_lease` (fs/locks.c, Linux
v6.18.46) needs a lease
nothing in a one-process model can take; and a regular file's
`generic_file_read_iter` (mm/filemap.c) answers -EAGAIN only under
IOCB_NOWAIT, which `iocb_flags` (include/linux/fs.h) never derives from
O_NONBLOCK — a claim about v5.15 and later, since mandatory locking's
`locks_mandatory_area` read the bit directly before then.  Should
`Open.openat_spec` ever resolve a FIFO, a socket or a character device,
O_NONBLOCK stops being ignorable and comes back OUT of
`Open.open_ignored_flags`.  The argument in full, with its per-version
readings, is on the Rocq `Uapi.O_NONBLOCK`. -/
def O_NONBLOCK : Int := 2048

/-- `#define O_DIRECTORY 00200000` (include/uapi/asm-generic/fcntl.h:53,
Linux v6.18.46, commit 1f99e9ab748f).

THE ONE OPEN FLAG THIS MODEL INTERPRETS BEYOND THE ACCESS MODE: it
changes which answers the call gives rather than staying in `f_flags`.
`build_open_flags` (fs/open.c, Linux v6.18.46) turns it into the
LOOKUP_DIRECTORY lookup flag, and `do_open` (fs/namei.c) answers -ENOTDIR
for a resolved dentry `d_can_lookup` (include/linux/dcache.h) refuses —
after the O_CREAT block and before `may_open` (fs/namei.c, Linux
v6.18.46), which is itself before `vfs_open` (fs/open.c, same version), so
a FIFO, a device node and a
plain file all answer -ENOTDIR without either later step being
reached. -/
def O_DIRECTORY : Int := 65536

/-! ## The `AT_` words (include/uapi/linux/fcntl.h) -/

/-- `#define AT_FDCWD -100` (include/uapi/linux/fcntl.h:94, Linux
v6.18.46, commit 1f99e9ab748f), as the 64-bit two's-complement word a
program passes in a register. -/
def AT_FDCWD : word := Z_to_bv 64 (-100)

/-- AT_FDCWD as it reaches openat's dirfd test, i.e. after the `int dfd`
truncation the dispatcher applies (`Syscall.fd32`): the low 32 bits of
-100.  The kernel compares only the low half, so `openat(2^32 - 100, ...)`
names the working directory too. -/
def AT_FDCWD32 : word := fd32 AT_FDCWD

/-- `#define AT_SYMLINK_NOFOLLOW 0x100` (include/uapi/linux/fcntl.h:120,
Linux v6.18.46, commit 1f99e9ab748f): the flag that turns `stat` into
`lstat`. -/
def AT_SYMLINK_NOFOLLOW : Int := 256

/-- `#define AT_EACCESS 0x200` (include/uapi/linux/fcntl.h:165, Linux
v6.18.46, commit 1f99e9ab748f): asks `faccessat2` to answer with the
EFFECTIVE ids.  Read once, by `access_need_override_creds` (fs/open.c,
Linux v6.18.46), which returns false outright when it is set and so skips
the `access_override_creds` (fs/open.c) that copies uid/gid over
fsuid/fsgid.  Under F_OK the choice is unobservable, which is what lets
`Fs.Open.faccessat2_spec` answer with it set. -/
def AT_EACCESS : Int := 512

/-- `#define AT_EMPTY_PATH 0x1000` (include/uapi/linux/fcntl.h:126, Linux
v6.18.46, commit 1f99e9ab748f): makes `getname_flags` (fs/namei.c) accept
an empty pathname and resolve the dirfd itself; `do_faccessat` (fs/open.c,
Linux v6.18.46) turns it into LOOKUP_EMPTY.  One of the three flags
`faccessat2` accepts, so it is not an -EINVAL, and
`Fs.Open.modeled_access_flags` declines it rather than guessing. -/
def AT_EMPTY_PATH : Int := 4096

/-- `#define S_IRWXO 00007` (include/uapi/linux/stat.h:39, Linux v6.18.46,
commit 1f99e9ab748f): the mask `do_faccessat` (fs/open.c, Linux v6.18.46)
validates its `mode` against, in its FIRST statement — before the flag
word, the creds and the pathname.  Linux passes `mode` STRAIGHT THROUGH
as a permission mask, `inode_permission(..., mode | MAY_ACCESS)`, which
works only because R_OK, W_OK and X_OK have the same numeric values as
MAY_READ, MAY_WRITE and MAY_EXEC (4/2/1, include/linux/fs.h:100-102,
Linux v6.18.46). -/
def S_IRWXO : Int := 7

/-! ## The two paths more than one spec resolves -/

/-- "." (the working directory), one of the two paths that name a
directory without a lookup.  The other is `Fs.Namei.dotdot_path`;
`Fs.Open.path_is_dirref` is the pair.  The interpreted fs has no
directory structure, so no path OTHER than those two resolves to a
directory.  It sits here rather than with a syscall because `openat`
opens it as a directory fd and `newfstatat` declines it, and no file
under `Sys/` imports another. -/
def dot_path : path := [Z_to_bv 8 46]

/-- "/dev/null", the first of the two device paths the model answers:
`Fs.Open.openat_devnull_spec` opens it and `Fs.Stat.fstat_devnull_spec`
keys the descriptor's stat pin under it.  The assumption the name rests
on — the image's /dev/null is the null device, character major 1 minor
3 — is stated once, at the openat arm. -/
def devnull_path : path :=
  [Z_to_bv 8 47, Z_to_bv 8 100, Z_to_bv 8 101, Z_to_bv 8 118, Z_to_bv 8 47,
   Z_to_bv 8 110, Z_to_bv 8 117, Z_to_bv 8 108, Z_to_bv 8 108]

/-- "/dev/urandom", the second device path the model answers, here for the
reason `devnull_path` is: Rocq's `Fs.Open.openat_urandom_spec` opens it (the
Open twin is still to land under `Sys/Fs/`) and `Fs.Stat.fstat_urandom_spec`
keys the descriptor's stat pin under it.  The
assumption the name rests on — the image's /dev/urandom is the random
device, character major 1 minor 9, `devlist[9]` of `memory_open`
(drivers/char/mem.c, Linux v6.18.46) — is stated once, at the openat arm,
and recorded in bugs/openat-urandom-assumed-random-device.md. -/
def urandom_path : path :=
  [Z_to_bv 8 47, Z_to_bv 8 100, Z_to_bv 8 101, Z_to_bv 8 118, Z_to_bv 8 47,
   Z_to_bv 8 117, Z_to_bv 8 114, Z_to_bv 8 97, Z_to_bv 8 110, Z_to_bv 8 100,
   Z_to_bv 8 111, Z_to_bv 8 109]

/-! ## lseek (include/uapi/linux/fs.h) -/

/-- `#define SEEK_SET 0` (include/uapi/linux/fs.h:52, Linux v6.18.46,
commit 1f99e9ab748f). -/
def SEEK_SET : Int := 0

/-- `#define SEEK_CUR 1` (include/uapi/linux/fs.h:53, Linux v6.18.46,
commit 1f99e9ab748f). -/
def SEEK_CUR : Int := 1

/-- `#define SEEK_END 2` (include/uapi/linux/fs.h:54, Linux v6.18.46,
commit 1f99e9ab748f). -/
def SEEK_END : Int := 2

/-- The largest whence the kernel accepts at all: `#define SEEK_MAX
SEEK_HOLE` over `#define SEEK_HOLE 4` (include/uapi/linux/fs.h:56-57,
Linux v6.18.46, commit 1f99e9ab748f).  `ksys_lseek` (fs/read_write.c,
Linux v6.18.46) tests `whence <= SEEK_MAX` AFTER resolving the fd and
BEFORE `vfs_llseek` (fs/read_write.c), so the -EINVAL for a whence past
it precedes every per-file-kind answer — including a pipe's -ESPIPE. -/
def SEEK_MAX : Int := 4

/-! ## getrandom (include/uapi/linux/random.h) -/

/-- `#define GRND_NONBLOCK 0x0001` (include/uapi/linux/random.h:54, Linux
v6.18.46, commit 1f99e9ab748f). -/
def GRND_NONBLOCK : Int := 1

/-- `#define GRND_RANDOM 0x0002` (include/uapi/linux/random.h:55, Linux
v6.18.46, commit 1f99e9ab748f). -/
def GRND_RANDOM : Int := 2

/-! ## The ioctl requests only a terminal implements
(include/uapi/asm-generic/ioctls.h)

TIOCGWINSZ is the one a musl-linked binary reaches on its own: `__fdopen`,
`__stdout_write` and `isatty` probe the window size to pick stdio's
buffering mode.  The rest are what a program that expects to own a pty
asks for — `tcgetattr`/`tcsetattr(TCSANOW)`, the other half of the
window-size pair, the controlling-terminal pair, and the two requests
musl's `openpty` issues on /dev/ptmx.  The two `_IOR`/`_IOW` requests
encode direction 2/1 in bits 30-31, the 4-byte argument size in bits
16-29, the type `'T'` (0x54) in bits 8-15 and the number in bits 0-7
(include/uapi/asm-generic/ioctl.h:23-36 and :58-66, Linux v6.18.46).  Rocq
read the eight as byte-identical across Linux v5.10-v6.14; the line
numbers below are v6.18.46's. -/

/-- `#define TCGETS 0x5401` (include/uapi/asm-generic/ioctls.h:20, Linux
v6.18.46, commit 1f99e9ab748f). -/
def TCGETS : word := Z_to_bv 64 21505

/-- `#define TCSETS 0x5402` (include/uapi/asm-generic/ioctls.h:21, Linux
v6.18.46, commit 1f99e9ab748f). -/
def TCSETS : word := Z_to_bv 64 21506

/-- `#define TIOCSCTTY 0x540E` (include/uapi/asm-generic/ioctls.h:33,
Linux v6.18.46, commit 1f99e9ab748f). -/
def TIOCSCTTY : word := Z_to_bv 64 21518

/-- `#define TIOCGWINSZ 0x5413` (include/uapi/asm-generic/ioctls.h:38,
Linux v6.18.46, commit 1f99e9ab748f). -/
def TIOCGWINSZ : word := Z_to_bv 64 21523

/-- `#define TIOCSWINSZ 0x5414` (include/uapi/asm-generic/ioctls.h:39,
Linux v6.18.46, commit 1f99e9ab748f). -/
def TIOCSWINSZ : word := Z_to_bv 64 21524

/-- `#define TIOCNOTTY 0x5422` (include/uapi/asm-generic/ioctls.h:54,
Linux v6.18.46, commit 1f99e9ab748f). -/
def TIOCNOTTY : word := Z_to_bv 64 21538

/-- `#define TIOCGPTN _IOR('T', 0x30, unsigned int)`
(include/uapi/asm-generic/ioctls.h:69, Linux v6.18.46, commit
1f99e9ab748f). -/
def TIOCGPTN : word := Z_to_bv 64 2147767344

/-- `#define TIOCSPTLCK _IOW('T', 0x31, int)`
(include/uapi/asm-generic/ioctls.h:70, Linux v6.18.46, commit
1f99e9ab748f). -/
def TIOCSPTLCK : word := Z_to_bv 64 1074025521

/-! ## fcntl (include/uapi/asm-generic/fcntl.h)

riscv64 supplies no arch override, so these are its values.  `F_GETLK`
and friends are the 64-bit spellings (5/6/7); the 12/13/14 numbering is
guarded by `#if __BITS_PER_LONG == 32 || defined(__KERNEL__)`, so a
64-bit kernel does define those names — but `do_fcntl` (fs/fcntl.c, Linux
v6.18.46) has no arm for them and they fall to its `default: break`,
returning the -EINVAL its `long err` was initialised to.  Declining them
is therefore the same answer `Fcntl.fcntl_spec` gives every unrecognized
command. -/

/-- `#define F_GETFD 1` (include/uapi/asm-generic/fcntl.h:99, Linux
v6.18.46, commit 1f99e9ab748f). -/
def F_GETFD : word := Z_to_bv 64 1

/-- `#define F_SETFD 2` (include/uapi/asm-generic/fcntl.h:100, Linux
v6.18.46, commit 1f99e9ab748f). -/
def F_SETFD : word := Z_to_bv 64 2

/-- `#define F_GETFL 3` (include/uapi/asm-generic/fcntl.h:101, Linux
v6.18.46, commit 1f99e9ab748f). -/
def F_GETFL : word := Z_to_bv 64 3

/-- `#define F_SETFL 4` (include/uapi/asm-generic/fcntl.h:102, Linux
v6.18.46, commit 1f99e9ab748f). -/
def F_SETFL : word := Z_to_bv 64 4

/-! ## flock (include/uapi/asm-generic/fcntl.h)

A MIXED word rather than an enumeration: LOCK_NB is a modifier OR'd into
one of the other three, which is why `Fs.Locks.flock_base` strips it
before comparing.

LOCK_MAND is here because the kernel still READS it, not because anything
sets it.  Mandatory flocks were removed, and what replaced them is not a
rejection: `SYSCALL_DEFINE2(flock, ...)` (fs/locks.c:2135, Linux v6.18.46)
opens with `if (cmd & LOCK_MAND) ... return 0;` (line 2148), so the bit
turns the whole call into a no-op that succeeds — ahead of the operation
check, the descriptor lookup, and so every errno flock has.  LOCK_READ,
LOCK_WRITE and LOCK_RW sit beside it in the header and are not named
here: nothing in fs/locks.c reads them at v6.18.46, so they reach
`flock_translate_cmd`'s switch as ordinary unrecognized words and are
-EINVAL, which the general rule already gives. -/

/-- `#define LOCK_SH 1` (include/uapi/asm-generic/fcntl.h:176, Linux
v6.18.46, commit 1f99e9ab748f). -/
def LOCK_SH : Int := 1

/-- `#define LOCK_EX 2` (include/uapi/asm-generic/fcntl.h:177, Linux
v6.18.46, commit 1f99e9ab748f). -/
def LOCK_EX : Int := 2

/-- `#define LOCK_NB 4` (include/uapi/asm-generic/fcntl.h:178, Linux
v6.18.46, commit 1f99e9ab748f). -/
def LOCK_NB : Int := 4

/-- `#define LOCK_UN 8` (include/uapi/asm-generic/fcntl.h:180, Linux
v6.18.46, commit 1f99e9ab748f). -/
def LOCK_UN : Int := 8

/-- `#define LOCK_MAND 32` (include/uapi/asm-generic/fcntl.h:186, Linux
v6.18.46, commit 1f99e9ab748f). -/
def LOCK_MAND : Int := 32

/-! ## The file STATUS flag bits `setfl` reads
(include/uapi/asm-generic/fcntl.h)

`setfl` (fs/fcntl.c, Linux v6.18.46) is F_SETFL's body;
`Fcntl.setfl_acted_on` is the union of the bits it reads and carries the
argument for why each one is in it — in particular why FASYNC, which
`SETFL_MASK` omits, belongs there all the same.  O_NONBLOCK is one of
them and is defined above with the open flags, because it is one bit of
one ABI and so one constant. -/

/-- `#define O_APPEND 00002000` (include/uapi/asm-generic/fcntl.h:35,
Linux v6.18.46, commit 1f99e9ab748f).  Read by TWO things:
`Fcntl.setfl_acted_on`, for which it is a status bit F_SETFL really
changes, and `Open.append_create_flags`, the open shape that mints a
`State.FdFileA`; `Fcntl.setfl_noop_on`'s `FdFileA` arm is what keeps the
coupling sound. -/
def O_APPEND : Int := 1024

/-- `#define FASYNC 00020000` (include/uapi/asm-generic/fcntl.h:44, Linux
v6.18.46, commit 1f99e9ab748f). -/
def FASYNC : Int := 8192

/-- `#define O_DIRECT 00040000` (include/uapi/asm-generic/fcntl.h:47,
Linux v6.18.46, commit 1f99e9ab748f).  Read by TWO things:
`Fcntl.setfl_acted_on`, and `Fs.Pipe.pipe2_flags_mask`, which names it
among the bits pipe2 ACCEPTS — what separates a real -EINVAL from a
decline. -/
def O_DIRECT : Int := 16384

/-- `#define O_NOATIME 01000000` (include/uapi/asm-generic/fcntl.h:59,
Linux v6.18.46, commit 1f99e9ab748f). -/
def O_NOATIME : Int := 262144

/-! ## The anon-inode create masks: timerfd_create and eventfd2 -/

/-- `TFD_CREATE_FLAGS`, the only flag bits `timerfd_create` accepts:
`#define TFD_SHARED_FCNTL_FLAGS (TFD_CLOEXEC | TFD_NONBLOCK)` and
`#define TFD_CREATE_FLAGS TFD_SHARED_FCNTL_FLAGS` (include/linux/timerfd.h:14
and :16, Linux v6.18.46, commit 1f99e9ab748f) — the create mask IS the
shared-fcntl mask.  The two members are `O_CLOEXEC` and `O_NONBLOCK`
themselves (`#define TFD_CLOEXEC O_CLOEXEC`, `#define TFD_NONBLOCK
O_NONBLOCK`, include/uapi/linux/timerfd.h:32-33), which
`SYSCALL_DEFINE2(timerfd_create, ...)` (fs/timerfd.c:394, Linux v6.18.46)
asserts at build time: `BUILD_BUG_ON(TFD_CLOEXEC != O_CLOEXEC)` and
`BUILD_BUG_ON(TFD_NONBLOCK != O_NONBLOCK)` (lines 401-402).  Spelling the
value as the OR of the two `O_` constants rather than as 526336 is
therefore the kernel's own definition, and those two `BUILD_BUG_ON`s are
what license reusing the `O_` constants for it.  `TFD_TIMER_ABSTIME` and
`TFD_TIMER_CANCEL_ON_SET` belong to `TFD_SETTIME_FLAGS` (line 18) and are
NOT accepted here — passing either to `timerfd_create` is -EINVAL. -/
def TFD_CREATE_FLAGS : Int := ((O_CLOEXEC.toNat ||| O_NONBLOCK.toNat : Nat) : Int)

/-- `#define EFD_SEMAPHORE (1 << 0)` (include/uapi/linux/eventfd.h:7, Linux
v6.18.46, commit 1f99e9ab748f), the one flag bit `eventfd2` accepts that
no other anon-inode create call does.  `do_eventfd` (fs/eventfd.c, Linux
v6.18.46) asserts all three `EFD_` names at build time, lines 386-388:
`BUILD_BUG_ON(EFD_CLOEXEC != O_CLOEXEC)`, `BUILD_BUG_ON(EFD_NONBLOCK !=
O_NONBLOCK)`, `BUILD_BUG_ON(EFD_SEMAPHORE != (1 << 0))`.  At v6.1 and
earlier all three sat in include/linux/eventfd.h; the uapi header carries
them from at least v6.6, with identical values. -/
def EFD_SEMAPHORE : Int := 1

/-- `EFD_FLAGS_SET`, the only flag bits `eventfd2` accepts:
`#define EFD_SHARED_FCNTL_FLAGS (O_CLOEXEC | O_NONBLOCK)` and
`#define EFD_FLAGS_SET (EFD_SHARED_FCNTL_FLAGS | EFD_SEMAPHORE)`
(include/linux/eventfd.h:26-27, Linux v6.18.46, commit 1f99e9ab748f) — the
shared-fcntl mask WIDENED BY ONE BIT, which is the whole difference from
`TFD_CREATE_FLAGS`.  Bit 0 is `EFD_SEMAPHORE` to `eventfd2` and is
`TFD_TIMER_ABSTIME` — `timerfd_settime`'s flag — to `timerfd_create`,
which refuses it: `eventfd2(0, 1)` hands back a descriptor and
`timerfd_create(CLOCK_MONOTONIC, 1)` is -EINVAL, so a model that spelled
one gate with the other's mask would be wrong on exactly one input each
way.  testing/syscall-check/tests/eventfd2.c pins that input. -/
def EFD_FLAGS_SET : Int :=
  ((O_CLOEXEC.toNat ||| O_NONBLOCK.toNat ||| EFD_SEMAPHORE.toNat : Nat) : Int)

/-! ## unlinkat, names and the descriptor table -/

/-- `#define AT_REMOVEDIR 0x200` (include/uapi/linux/fcntl.h:168, Linux
v6.18.46, commit 1f99e9ab748f): the only flag `unlinkat` accepts.  Any
other bit is a deterministic -EINVAL, decided before the pathname is
fetched and before the dirfd is looked at — see `Fs.Namei.unlinkat_spec`.
The same number as `AT_EACCESS`, for a different syscall. -/
def AT_REMOVEDIR : Int := 512

/-- `#define NAME_MAX 255` (include/uapi/linux/limits.h:12, Linux
v6.18.46, commit 1f99e9ab748f): the longest single path COMPONENT every
Linux filesystem in reach accepts.  fs/namei.c itself has NO such check —
the bound is the filesystem's, raised by `dir->i_op->lookup`:
`simple_lookup` (fs/libfs.c, Linux v6.18.46) on tmpfs and `ext4_lookup`
(fs/ext4/namei.c, Linux v6.18.46) on ext4, both -ENAMETOOLONG at 255 in
their first statement, ext4 through its own `EXT4_NAME_LEN`.  So the
model, which represents no filesystem type, declines a longer name rather
than picking one filesystem's answer. -/
def NAME_MAX : Nat := 255

/-- `#define NR_OPEN_DEFAULT BITS_PER_LONG` (include/linux/fdtable.h:24,
Linux v6.18.46, commit 1f99e9ab748f): the number of descriptor slots
embedded in a `struct files_struct` — 64 on the LP64 target this model
compiles for, 32 on a 32-bit one.

WHY A SPEC READS IT: it is a FLOOR on the live descriptor table.  Every
`struct fdtable` a task can reach has `max_fds >= NR_OPEN_DEFAULT` — the
three producers in fs/file.c (Linux v6.18.46) are `init_files`, a static
initializer at exactly this value; `dup_fd`, which starts at the embedded
table and calls `alloc_fdtable` only for more; and `alloc_fdtable`, which
returns no less than asked; `sane_fdtable_size` cannot ask for less
either.  So `expand_files` (fs/file.c, Linux v6.18.46), which opens with
`if (nr < fdt->max_fds) return 0;` (line 299), allocates nothing for
`nr < NR_OPEN_DEFAULT`, and neither its -EMFILE nor its -ENOMEM is
reachable there.  `Fs.File.dup3_spec` reads it for `expand_files`, and
`Fs.Select.pselect_nfds_max` for `core_sys_select`'s clamp (fs/select.c).
It says nothing about whether an operation SUCCEEDS: RLIMIT_NOFILE is a
separate, earlier gate. -/
def NR_OPEN_DEFAULT : Int := 64

/-! ## struct stat, as fstat (80) and newfstatat (79) copy it out -/

/-- `sizeof(struct stat)` on riscv64.  riscv64 has no asm/stat.h of its
own, so it takes the generic 64-bit layout (`struct stat`,
include/uapi/asm-generic/stat.h:24-45, Linux v6.18.46, commit
1f99e9ab748f), whose members and offsets are

    unsigned long  st_dev         0
    unsigned long  st_ino         8
    unsigned int   st_mode       16
    unsigned int   st_nlink      20
    unsigned int   st_uid        24
    unsigned int   st_gid        28
    unsigned long  st_rdev       32
    unsigned long  __pad1        40
    long           st_size       48
    int            st_blksize    56
    int            __pad2        60
    long           st_blocks     64
    long           st_atime      72
    unsigned long  st_atime_nsec 80
    long           st_mtime      88
    unsigned long  st_mtime_nsec 96
    long           st_ctime     104
    unsigned long  st_ctime_nsec 112
    unsigned int   __unused4    120
    unsigned int   __unused5    124

ALL 128 BYTES ARE DELIVERED, padding included.  `cp_new_stat` (fs/stat.c,
Linux v6.18.46) zeroes its stack copy through `INIT_STRUCT_STAT_PADDING`
(fs/stat.c:466-467, the generic `memset`, which riscv64 leaves alone),
fills the members above, and hands the whole struct to a single
`copy_to_user`. -/
def STAT_SIZE : Int := 128

/-- Member offsets the predicates below read, named because three of
them are read twice and because a layout error is the one mistake a
reader cannot see in a numeral (`struct stat`,
include/uapi/asm-generic/stat.h:24-45, Linux v6.18.46). -/
def ST_MODE_OFF : Nat := 16
def ST_RDEV_OFF : Nat := 32
def ST_PAD1_OFF : Nat := 40
def ST_SIZE_OFF : Nat := 48
def ST_BLKSIZE_OFF : Nat := 56
def ST_PAD2_OFF : Nat := 60
def ST_BLOCKS_OFF : Nat := 64
def ST_UNUSED45_OFF : Nat := 120

/-- One little-endian member of a delivered `struct stat`, as the
unsigned value of its `n` bytes at `off`.  riscv64 is little-endian and
every member above is a plain integer, so a member is exactly this.  A
short buffer reads as the value of what bytes are there — the length is
checked separately, by `stat_buf_wf`. -/
def stat_field_le (off n : Nat) (bs : List byte) : Int :=
  bytes_le_to_Z ((bs.drop off).take n)

/-! `S_IFMT` and the seven file types it selects
(include/uapi/linux/stat.h:9-16, Linux v6.18.46, commit 1f99e9ab748f).
`S_IFMT` is the mask; the seven values are every type the mask can hold,
and an inode always has exactly one of them — `inode_init_always`
(include/linux/fs.h, Linux v6.18.46, a wrapper of `inode_init_always_gfp`,
fs/inode.c) is reached only through an allocation a
filesystem then gives a type, and every `init_special_inode` (fs/inode.c)
or `d_instantiate` path sets one. -/

/-- `#define S_IFMT 00170000` (include/uapi/linux/stat.h:9, Linux v6.18.46). -/
def S_IFMT : Int := 61440
/-- `#define S_IFSOCK 0140000` (include/uapi/linux/stat.h:10, Linux v6.18.46). -/
def S_IFSOCK : Int := 49152
/-- `#define S_IFLNK 0120000` (include/uapi/linux/stat.h:11, Linux v6.18.46). -/
def S_IFLNK : Int := 40960
/-- `#define S_IFREG 0100000` (include/uapi/linux/stat.h:12, Linux v6.18.46). -/
def S_IFREG : Int := 32768
/-- `#define S_IFBLK 0060000` (include/uapi/linux/stat.h:13, Linux v6.18.46). -/
def S_IFBLK : Int := 24576
/-- `#define S_IFDIR 0040000` (include/uapi/linux/stat.h:14, Linux v6.18.46). -/
def S_IFDIR : Int := 16384
/-- `#define S_IFCHR 0020000` (include/uapi/linux/stat.h:15, Linux v6.18.46). -/
def S_IFCHR : Int := 8192
/-- `#define S_IFIFO 0010000` (include/uapi/linux/stat.h:16, Linux v6.18.46). -/
def S_IFIFO : Int := 4096

/-- The `S_IFMT` bits of a delivered `struct stat`'s `st_mode`.  Computed
in `Nat` because `Int` has no `land` in core Lean; both operands are
non-negative, so the value is Rocq's `Z.land`. -/
def stat_ifmt (bs : List byte) : Int :=
  (((stat_field_le ST_MODE_OFF 4 bs).toNat &&& S_IFMT.toNat : Nat) : Int)

/-- Whether the kernel called the object a REGULAR FILE.  A question
ABOUT THE ANSWER, not a claim by the model: the model does not know a
path's type (bugs/fs-paths-assumed-regular-files.md), and
`Fs.Stat.fstat_spec` uses this only to decide whether its `st_size`
obligation applies. -/
def stat_is_reg (bs : List byte) : Bool :=
  stat_ifmt bs == S_IFREG

/-- Whether `st_mode` names one of the seven types at all.  An all-zero
`st_mode` is not one of them, which is what makes an all-zero
`struct stat` — the shape a kernel that wrote nothing but claimed to have
written would produce — inadmissible. -/
def stat_ifmt_valid (bs : List byte) : Bool :=
  stat_ifmt bs == S_IFSOCK || stat_ifmt bs == S_IFLNK || stat_ifmt bs == S_IFREG
    || stat_ifmt bs == S_IFBLK || stat_ifmt bs == S_IFDIR || stat_ifmt bs == S_IFCHR
    || stat_ifmt bs == S_IFIFO

/-- THE ENVELOPE EVERY DELIVERED `struct stat` MUST FALL IN, and it is
everything `cp_new_stat` (fs/stat.c, Linux v6.18.46) settles without
consulting the inode: the width is exactly `STAT_SIZE`, the single
`copy_to_user`'s; `__pad1`, `__pad2` and `__unused4`/`__unused5` are
ZERO, because `INIT_STRUCT_STAT_PADDING` cleared the whole struct and no
member assignment covers those bytes — the part of the answer the model
knows EXACTLY, and what makes a poisoned or invented buffer rejectable;
and `st_mode` names one of the seven file types.  Nothing else is
claimed here; the rest is the environment's (`Fs.Stat.fstat_spec`). -/
def stat_buf_wf (bs : List byte) : Bool :=
  (bs.length == 128)
   && stat_ifmt_valid bs
   && (stat_field_le ST_PAD1_OFF 8 bs == 0)
   && (stat_field_le ST_PAD2_OFF 4 bs == 0)
   && (stat_field_le ST_UNUSED45_OFF 8 bs == 0)

/-- THE ONE MEMBER THE MODEL DERIVES, and it is derived CONDITIONALLY.
For a regular file `st_size` is the file's length: `generic_fillattr`
(fs/stat.c, Linux v6.18.46) copies `inode->i_size` into `stat->size` and
`cp_new_stat` copies that to `tmp.st_size`, and for a path this model
resolves that is the length of the byte list `Fs` carries — the premise
`ReadWrite.read_spec` already makes, and no more.  The implication keeps
the arm from FALSELY REJECTING a path Linux calls a character device
(bugs/fs-paths-assumed-regular-files.md): there the true answer is
S_IFCHR with `st_size` 0, and the model says nothing.  The comparison
wraps at 2^64 because `stat_field_le` reads eight bytes and a length is
an unbounded `Nat`; a file that long is not constructible, so the wrap is
unreachable, and it is written this way so the predicate is TOTAL. -/
def stat_size_ok (n : Nat) (bs : List byte) : Bool :=
  !stat_is_reg bs
    || (stat_field_le ST_SIZE_OFF 8 bs == bv_unsigned (Z_to_bv 64 (n : Int)))

/-- THE `st_rdev` A `struct stat` OF /dev/null CARRIES: `new_encode_dev`
(include/linux/kdev_t.h:39-44, Linux v6.18.46, commit 1f99e9ab748f) of
`MKDEV(1, 3)` (line 12), i.e. `(3 & 0xff) | (1 << 8) | ((3 & ~0xff) <<
12)` = 259.  `cp_new_stat` (fs/stat.c) copies what `generic_fillattr`
read off the inode: `st_mode`'s type bits are S_IFCHR because
`init_special_inode` (fs/inode.c, Linux v6.18.46) set them when the node
was made;
`st_size` is `i_size`, 0 on a device inode nothing ever wrote through
(`write_null` returns without touching the inode, drivers/char/mem.c,
Linux v6.18.46), and `st_blocks` is `i_blocks`, 0 for the same reason.
The two zeros are a consequence of the environment premise rather than a
kernel invariant (bugs/openat-devnull-assumed-null-device.md).  NOT
asserted, and chosen once per descriptor by `Fs.Stat.fstat_devnull_spec`'s
pin: the permission bits and owner (devtmpfs takes 0666 and root from
`mem_devnode`, drivers/char/mem.c, Linux v6.18.46, but a container runtime
makes its own
node), the link count, the device and inode numbers, the block size and
the timestamps. -/
def DEVNULL_RDEV : Int := 259

/-- The members a `struct stat` of ANY of the model's character devices
carries from the kernel, parameterised by the device number:
`stat_devnull_ok` and `stat_urandom_ok` are its two instances, and the
argument on `DEVNULL_RDEV` is the argument for both. -/
def stat_chrdev_ok (rdev : Int) (bs : List byte) : Bool :=
  (stat_ifmt bs == S_IFCHR)
   && (stat_field_le ST_RDEV_OFF 8 bs == rdev)
   && (stat_field_le ST_SIZE_OFF 8 bs == 0)
   && (stat_field_le ST_BLOCKS_OFF 8 bs == 0)

/-- The members of a /dev/null `struct stat` that come from the kernel,
asserted outright rather than under an implication; see `DEVNULL_RDEV`. -/
def stat_devnull_ok (bs : List byte) : Bool := stat_chrdev_ok DEVNULL_RDEV bs

/-- /dev/urandom's device number as a stat delivers it in st_rdev:
`new_encode_dev(MKDEV(1, 9))` (include/linux/kdev_t.h:12 and :39-44, Linux
v6.18.46) — `(9 & 0xff) | (1 << 8)`.  The zero st_size and st_blocks rest on
the same environment premise the null device's do: a node made by mknod or
devtmpfs and never resized, and `random_write_iter` (drivers/char/random.c,
same version) mixes into the pool and touches no inode member; recorded in
bugs/openat-urandom-assumed-random-device.md. -/
def URANDOM_RDEV : Int := 265

/-- The members of a /dev/urandom `struct stat` that come from the kernel;
see `URANDOM_RDEV`. -/
def stat_urandom_ok (bs : List byte) : Bool := stat_chrdev_ok URANDOM_RDEV bs

/-- Byte-list equality, for comparing a delivered `struct stat` against a
pin.  `Fs.path_eqb` is the same function over the same type; a second
name is used because these bytes are not a path. -/
def stat_bytes_eqb : List byte → List byte → Bool
  | [], [] => true
  | a :: r1, b :: r2 => bv_eqb a b && stat_bytes_eqb r1 r2
  | _, _ => false

theorem stat_bytes_eqb_eq (l1 l2 : List byte) :
    stat_bytes_eqb l1 l2 = true ↔ l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons b r2 => exact ⟨fun h => (Bool.false_ne_true h).elim, fun h => nomatch h⟩
  | cons a r1 ih =>
    cases l2 with
    | nil => exact ⟨fun h => (Bool.false_ne_true h).elim, fun h => nomatch h⟩
    | cons b r2 =>
      simp only [stat_bytes_eqb, Bool.and_eq_true, bv_eqb_eq, ih, List.cons.injEq]

theorem stat_bytes_eqb_refl (l : List byte) : stat_bytes_eqb l l = true :=
  (stat_bytes_eqb_eq l l).2 rfl

/-- THE MEMBERS THAT MAY NOT CHANGE UNDER A RUN, so that two `fstat`s of
one file cannot disagree about which file it is: bytes 0..47 — `st_dev`,
`st_ino`, `st_mode`, `st_nlink`, `st_uid`, `st_gid`, `st_rdev` and
`__pad1` — and bytes 56..63, `st_blksize` and `__pad2`.  Each is settled
by the inode or its superblock, and no syscall in
`Sys.SyscallTable.spec_table` moves one; `unlinkat` (35) does drop
`st_nlink` but also removes the key, and `Fs.Stat.fstat_spec` declines a
descriptor whose path `Fs` no longer holds.  DELIBERATELY LEFT FREE:
`st_size` (constrained by `stat_size_ok` instead), `st_blocks` and the
three timestamp pairs, which every read and write moves; requiring them
to repeat would reject a conforming trace, and leaving them free lets
through a run Linux would not produce; the `bugs/` entry on fstat's
unpinned members over-admitting (its path is on the Rocq
`stat_stable_eqb`) is that trade. -/
def stat_stable_eqb (b1 b2 : List byte) : Bool :=
  stat_bytes_eqb (b1.take ST_PAD1_OFF) (b2.take ST_PAD1_OFF)
   && stat_bytes_eqb ((b1.drop ST_PAD1_OFF).take 8) ((b2.drop ST_PAD1_OFF).take 8)
   && stat_bytes_eqb ((b1.drop ST_BLKSIZE_OFF).take 8) ((b2.drop ST_BLKSIZE_OFF).take 8)

theorem stat_stable_eqb_refl (b : List byte) : stat_stable_eqb b b = true := by
  unfold stat_stable_eqb
  rw [stat_bytes_eqb_refl, stat_bytes_eqb_refl, stat_bytes_eqb_refl]
  rfl

/-! TWO SLICES OF A DELIVERED `struct stat` READ THE SAME out of two
buffers that agree on the region they fall in: wholly inside the first 48
bytes, or wholly at or past 56.  Those two regions are exactly what
`stat_stable_eqb` compares and where every member `stat_buf_wf` looks at
lives, so these carry both predicates across a change confined to bytes
48..55. -/

theorem stat_slice_head (off k : Nat) (x y : List byte)
    (hb : off + k ≤ 48) (heq : x.take 48 = y.take 48) :
    (x.drop off).take k = (y.drop off).take k := by
  have hx : ∀ z : List byte, (z.drop off).take k = ((z.take 48).drop off).take k := by
    intro z
    rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega : k ≤ 48 - off)]
  rw [hx x, hx y, heq]

theorem stat_slice_tail (off k : Nat) (x y : List byte)
    (hb : 56 ≤ off) (heq : x.drop 56 = y.drop 56) :
    (x.drop off).take k = (y.drop off).take k := by
  have hx : ∀ z : List byte, z.drop off = (z.drop 56).drop (off - 56) := by
    intro z
    rw [List.drop_drop, Nat.add_sub_cancel' hb]
  rw [hx x, hx y, heq]

theorem stat_field_le_head (off k : Nat) (x y : List byte)
    (hb : off + k ≤ 48) (heq : x.take 48 = y.take 48) :
    stat_field_le off k x = stat_field_le off k y :=
  congrArg bytes_le_to_Z (stat_slice_head off k x y hb heq)

theorem stat_field_le_tail (off k : Nat) (x y : List byte)
    (hb : 56 ≤ off) (heq : x.drop 56 = y.drop 56) :
    stat_field_le off k x = stat_field_le off k y :=
  congrArg bytes_le_to_Z (stat_slice_tail off k x y hb heq)

/-- THE SAME `struct stat` WITH A DIFFERENT `st_size`.  A file statted
twice with a write in between must answer with the same device, inode,
mode, link count, ids and block size and a NEW length, and this is one
buffer that does: it exists so a witness can name an admissible answer
on the pinned branch of `Fs.Stat.fstat_spec` without inventing the
members the pin fixes.  Not itself a claim about Linux — the spec
CHOOSES from a set this is one member of, and the timestamps and
`st_blocks` it copies over unchanged are exactly the members a real
kernel would have moved. -/
def stat_set_size (n : Nat) (bs : List byte) : List byte :=
  bs.take 48 ++ (Z_to_le_bytes 8 (n : Int) ++ bs.drop 56)

theorem stat_set_size_head (n : Nat) (bs : List byte) (hlen : 48 ≤ bs.length) :
    (stat_set_size n bs).take 48 = bs.take 48 := by
  unfold stat_set_size
  have h48 : (bs.take 48).length = 48 := List.length_take_of_le hlen
  rw [List.take_append_of_le_length (by omega), List.take_take, Nat.min_self]

theorem stat_set_size_tail (n : Nat) (bs : List byte) (hlen : 48 ≤ bs.length) :
    (stat_set_size n bs).drop 56 = bs.drop 56 := by
  unfold stat_set_size
  have h48 : (bs.take 48).length = 48 := List.length_take_of_le hlen
  have h8 : (Z_to_le_bytes 8 (n : Int)).length = 8 := length_Z_to_le_bytes 8 (n : Int)
  rw [List.drop_append, List.drop_of_length_le (by omega), List.nil_append, h48,
    List.drop_append, List.drop_of_length_le (by omega), List.nil_append, h8]
  rfl

theorem stat_set_size_field (n : Nat) (bs : List byte) (hlen : 48 ≤ bs.length) :
    ((stat_set_size n bs).drop 48).take 8 = Z_to_le_bytes 8 (n : Int) := by
  unfold stat_set_size
  have h48 : (bs.take 48).length = 48 := List.length_take_of_le hlen
  have h8 : (Z_to_le_bytes 8 (n : Int)).length = 8 := length_Z_to_le_bytes 8 (n : Int)
  rw [List.drop_append, List.drop_of_length_le (by omega), List.nil_append, h48,
    Nat.sub_self, List.drop_zero, List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega)]

/-! NOT PORTED: Rocq's `stat_set_size_size_ok` (`stat_size_ok n
(stat_set_size n bs) = true` for a 128-byte `bs`).  Its proof rewrites with
BvBase's `bytes_le_to_Z_of_le_bytes` and `Z_to_bv_unsigned`, neither of
which `BvBase.lean` has ported, and a bit-level round-trip lemma about
`Z_to_le_bytes` belongs in that file, not here.  It lands with them.  The
T4 parity check compares definitions and not lemmas, which is why this is
a note and not an `unported:` entry. -/

theorem stat_set_size_length (n : Nat) (bs : List byte) (hlen : bs.length = 128) :
    (stat_set_size n bs).length = 128 := by
  unfold stat_set_size
  rw [List.length_append, List.length_append, length_Z_to_le_bytes, List.length_take,
    List.length_drop, hlen]
  omega

theorem stat_set_size_wf (n : Nat) (bs : List byte) (h : stat_buf_wf bs = true) :
    stat_buf_wf (stat_set_size n bs) = true := by
  simp only [stat_buf_wf, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hlen, hifmt⟩, hp1⟩, hp2⟩, hu⟩ := h
  have hhead : (stat_set_size n bs).take 48 = bs.take 48 :=
    stat_set_size_head n bs (by omega)
  have htail : (stat_set_size n bs).drop 56 = bs.drop 56 :=
    stat_set_size_tail n bs (by omega)
  have hifmt' : stat_ifmt (stat_set_size n bs) = stat_ifmt bs := by
    unfold stat_ifmt
    rw [stat_field_le_head ST_MODE_OFF 4 _ _ (by decide) hhead]
  simp only [stat_buf_wf, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨stat_set_size_length n bs hlen, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold stat_ifmt_valid at hifmt ⊢
    rw [hifmt']
    exact hifmt
  · rw [stat_field_le_head ST_PAD1_OFF 8 _ _ (by decide) hhead]
    exact hp1
  · rw [stat_field_le_tail ST_PAD2_OFF 4 _ _ (by decide) htail]
    exact hp2
  · rw [stat_field_le_tail ST_UNUSED45_OFF 8 _ _ (by decide) htail]
    exact hu

theorem stat_set_size_stable (n : Nat) (bs : List byte) (hlen : bs.length = 128) :
    stat_stable_eqb (stat_set_size n bs) bs = true := by
  have hhead : (stat_set_size n bs).take 48 = bs.take 48 :=
    stat_set_size_head n bs (by omega)
  have htail : (stat_set_size n bs).drop 56 = bs.drop 56 :=
    stat_set_size_tail n bs (by omega)
  have h40 : (stat_set_size n bs).take 40 = bs.take 40 := by
    have hx : ∀ z : List byte, z.take 40 = (z.take 48).take 40 := by
      intro z
      rw [List.take_take, Nat.min_eq_left (by decide : 40 ≤ 48)]
    rw [hx (stat_set_size n bs), hx bs, hhead]
  have h4048 : ((stat_set_size n bs).drop 40).take 8 = (bs.drop 40).take 8 :=
    stat_slice_head 40 8 _ _ (by decide) hhead
  have h56 : ((stat_set_size n bs).drop 56).take 8 = (bs.drop 56).take 8 :=
    stat_slice_tail 56 8 _ _ (by decide) htail
  unfold stat_stable_eqb ST_PAD1_OFF ST_BLKSIZE_OFF
  rw [h40, h4048, h56, stat_bytes_eqb_refl, stat_bytes_eqb_refl, stat_bytes_eqb_refl]
  rfl

theorem stat_buf_wf_length (bs : List byte) (h : stat_buf_wf bs = true) :
    bs.length = 128 := by
  simp only [stat_buf_wf, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1

end LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
