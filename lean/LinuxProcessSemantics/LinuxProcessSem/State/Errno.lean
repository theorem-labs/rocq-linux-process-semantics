import LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! rocq-baseline: 7b4cf49586658ecbffbab14145ab0969272a0b23 -/

/-! # LinuxProcessSem.State.Errno — the errno values and `errno_ret`

One part of `State.v`'s twin, re-exported by `State.lean`, whose header
says how the ten parts divide the Rocq file, what a part may hold and
where the pins live.

WHAT GOES HERE: `errno_ret`, the a0 a failing syscall answers, and
every errno constant `State.v` defines, in the Rocq file's blocks.
The block headed "Ticket A1" says why the blocks are prose and what
the load-bearing facts are.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.State

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-- a0 for a failing syscall: `-errno`. -/
def errno_ret (e : Int) : word := Z_to_bv 64 (-e)

/-- `ECHILD` (include/uapi/asm-generic/errno-base.h), the one errno of the
block `Kernel.Exit.wait4_spec` will answer with once ported. -/
def ECHILD : Int := 10

/-- Errnos from include/uapi/asm-generic/errno-base.h that `Mm.Mmap` names:
`EINVAL` for its argument gates and `ENOMEM` as `mmap_errnos`' one
injectable failure are the two it ANSWERS; `EPERM` is Linux's answer at
address 0, which the arm declines rather than gives; `EBADF` and `EACCES`
are here for the checks that pin what mmap must NOT answer. -/
def EPERM  : Int := 1
def EBADF  : Int := 9
def ENOMEM : Int := 12
def EACCES : Int := 13
def EINVAL : Int := 22

/-! ### Ticket A1: the errno block

The errno constants of `theories/LinuxProcessSem/State.v` that the twin
lacked, in the Rocq file's blocks; the ones the twin already had stay
above them.  Every value is the riscv64 kernel's: arch/riscv has no
errno.h of its own at v6.18.46 and include/uapi/asm-generic/Kbuild:10
(`mandatory-y += errno.h`, Linux v6.18.46, commit 1f99e9ab748f) hands the
architecture the generic table, so include/uapi/asm-generic/errno-base.h
and include/uapi/asm-generic/errno.h are the headers cited below;
`Checks.Cases.State` holds each value to them.

Which block a value sits in is prose, not a fact anything reads: the
Rocq definitions carry the argument (values have already moved between
the "deterministic" and "injected" blocks, and `setsid_spec` is a shape
the split has no room for), and this twin keeps the blocks only so
a reader can find a name where the Rocq file has it.  The load-bearing
facts are the VALUE and the `*_errnos` list that names it, and the lists
are ported with their syscalls. -/

/-- Errno values the model returns deterministically
(include/uapi/asm-generic/errno-base.h:5-38 and
include/uapi/asm-generic/errno.h:8,20, Linux v6.18.46, commit
1f99e9ab748f). -/
def ENOENT : Int := 2
def ESRCH  : Int := 3
def EFAULT : Int := 14
def EEXIST : Int := 17
def ENOTDIR : Int := 20
def EISDIR : Int := 21
def ENOTTY : Int := 25
def ESPIPE : Int := 29
def EPIPE  : Int := 32
def ERANGE : Int := 34
def ENAMETOOLONG : Int := 36
def ENOTEMPTY : Int := 39

/-- Errno values the per-syscall failure-injection sets draw from
(`errno_from` and the `*_errnos` lists; the reason `EINVAL` is not among
them, and why the split is prose, is on the Rocq definitions).  All from
include/uapi/asm-generic/errno-base.h:8-34, Linux v6.18.46, commit
1f99e9ab748f. -/
def EINTR  : Int := 4
def EBUSY  : Int := 16
def ENFILE : Int := 23
def EMFILE : Int := 24
def EROFS  : Int := 30

/-- `EAGAIN` (include/uapi/asm-generic/errno-base.h:15, Linux v6.18.46,
commit 1f99e9ab748f).  Two Rocq lists draw it, neither with a Lean twin
yet: `Kernel.Sys.setid_errnos`, for a credential setter that moves the
real uid, where `set_user` (kernel/sys.c, Linux v6.18.46) and
`set_cred_ucounts` (kernel/cred.c, Linux v6.18.46) allocate and can
fail, and `Kernel.Fork.clone_errnos`, where `copy_process` (kernel/fork.c,
Linux v6.18.46) answers it for an unprivileged user's task count at
`RLIMIT_NPROC` (`is_rlimit_overlimit`, kernel/ucount.c:328, called at
kernel/fork.c:2058-2062) or for `nr_threads` at `max_threads`
(:2071-2072).  What is deliberately in NO list is a blocking-style
EAGAIN, the would-block answer of an `O_NONBLOCK` file: the model has no
non-blocking mode, and Rocq's `Sys/Fs/Fcntl.v` rests its `F_SETFL` decline
on that decision by this constant's name, and cites it for
`Sys/Net/Socket.v`'s `SOCK_NONBLOCK` decline too.
`FUTEX_WAIT`'s -EAGAIN (`Sys/Kernel/Futex/Syscalls.v`) is a deterministic
answer, not an injection.  Rocq's comment on `State.EAGAIN` says the
setter list is the ONLY one to draw it, which `clone_errnos` contradicts
— a `comments:` defect there.  This inventory stops being true when a
list gains or loses the constant. -/
def EAGAIN : Int := 11

/-- Socket errno values, all from include/uapi/asm-generic/errno.h:71-93
(Linux v6.18.46, commit 1f99e9ab748f); the Rocq comment reads the same
table at v6.12, and the two versions' headers are byte-identical. -/
def ENOTSOCK        : Int := 88
def EMSGSIZE        : Int := 90
def ENOPROTOOPT     : Int := 92
def EPROTONOSUPPORT : Int := 93
def ESOCKTNOSUPPORT : Int := 94
def EOPNOTSUPP      : Int := 95
def EAFNOSUPPORT    : Int := 97
def EADDRINUSE      : Int := 98
def ECONNRESET      : Int := 104
def EISCONN         : Int := 106
def ENOTCONN        : Int := 107
def ETIMEDOUT       : Int := 110

/-- `ECONNREFUSED` (include/uapi/asm-generic/errno.h:94, Linux v6.18.46,
commit 1f99e9ab748f): the one value in this block no spec returns.  It
names the canonical outcome of the connection attempt `connect_spec`
declines, so a check can pin that the declined arm answers `Unmodeled` to
a real errno rather than to a bare 111. -/
def ECONNREFUSED    : Int := 111

end LinuxProcessSemantics.LinuxProcessSem.State
