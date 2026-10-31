import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Fs.Timerfd — timerfd_create (85)

Mirrors `theories/LinuxProcessSem/Sys/Fs/Timerfd.v`, which answers to Linux
`fs/timerfd.c`: it holds what the kernel defines there, and nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.

One spelling differs from Rocq without changing a value: the bit test on
the flags word is done on the `word` (`bv_and` against the complement of
the mask) where Rocq does it on `bv_unsigned` in `Z` (`Z.ldiff`) — the
mask is below `2^64`, so the two agree — and the `Z.eqb` tests are Lean's
decidable `==` on `Int`.

THE ARM MODELS THE ARGUMENT REJECTION AND NOTHING ELSE.  Every input that
survives it creates a file descriptor, and `State.FdEntry` has no timer
kind to put one behind; the Rocq header carries the argument for why that
is a decline and not an approximation, and what it would take to lift it.
The one premise outside the call's own arguments is `CONFIG_TIMERFD=y`:
`kernel/sys_ni.c` carries `COND_SYSCALL(timerfd_create)` (Linux v6.18.46,
line 71), so a kernel built without it answers -ENOSYS to every input this
arm calls -EINVAL. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Timerfd

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- The -EINVAL gate of `timerfd_create`, written out of the kernel's own
single `if` (`SYSCALL_DEFINE2(timerfd_create)`, fs/timerfd.c:404-410,
Linux v6.18.46, commit 1f99e9ab748f):

    if ((flags & ~TFD_CREATE_FLAGS) ||
        (clockid != CLOCK_MONOTONIC && clockid != CLOCK_REALTIME &&
         clockid != CLOCK_REALTIME_ALARM && clockid != CLOCK_BOOTTIME &&
         clockid != CLOCK_BOOTTIME_ALARM))
      return -EINVAL;

The two halves are disjuncts of ONE condition, so neither orders before
the other; the ordering that matters is against the `capable(CAP_WAKE_ALARM)`
test in the NEXT `if` (fs/timerfd.c:412-415, Linux v6.18.46), which is why
an unknown flag
bit beside `CLOCK_REALTIME_ALARM` is -EINVAL and never -EPERM.  The flag
half is a truthiness test — `flags & ~TFD_CREATE_FLAGS` is the condition
itself — so bit 31 fails it like bit 0 does, which `bv_and` against the
complement keeps.  The clock half is stated over the unsigned low half
where the kernel compares a signed `int`; the two agree because every
target is a constant below `2^31` and the test is equality, not ordering.
Both arguments arrive already narrowed to 32 bits by the riscv64 wrapper
(`__SC_CAST`, include/linux/syscalls.h:132, applied by `__SYSCALL_DEFINEx`,
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46), which the
table arm does with `clockid32` and `flag32`; this predicate must not
narrow them again.  The argument in full, and why the two alarm ids stay
in the admitted set although the arm can never answer for them, is the
header of `theories/LinuxProcessSem/Sys/Fs/Timerfd.v` and the docstring
of its `timerfd_create_einval_b`, which this restates rather than shares. -/
def timerfd_create_einval_b (clkid flags : word) : Bool :=
  !(bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 TFD_CREATE_FLAGS))) == 0) ||
  !(bv_unsigned clkid == CLOCK_REALTIME ||
    bv_unsigned clkid == CLOCK_MONOTONIC ||
    bv_unsigned clkid == CLOCK_BOOTTIME ||
    bv_unsigned clkid == CLOCK_REALTIME_ALARM ||
    bv_unsigned clkid == CLOCK_BOOTTIME_ALARM)

/-- `timerfd_create clockid flags`: create a descriptor bound to a clock.

No `get_model`: the answer is a function of the two arguments alone.  The
-EINVAL arm touches no memory, emits no event and changes no state, which
is what the kernel does on that path too — `SYSCALL_DEFINE2(timerfd_create)`
(fs/timerfd.c:410, Linux v6.18.46, commit 1f99e9ab748f) returns before the
`kzalloc` at :417.  Everything past the gate is declined, and the decline
is a named list rather than "the rest": -EPERM from `capable` on the two
alarm ids (:412-415); -ENOMEM from the `kzalloc` (:417-419); -EMFILE or -ENOMEM
from `get_unused_fd_flags` (:435): its `alloc_fd` (fs/file.c:570-613,
Linux v6.18.46) sets -EMFILE itself (:591) and otherwise forwards
`expand_files` (:288-320), which is -EMFILE at :311 or, through
`expand_fdtable` (:252-279) and `alloc_fdtable` (:162-243), the latter's
-EMFILE (:197, :213) or -ENOMEM (:242); -ENOMEM or -ENFILE from
`anon_inode_getfile_fmode` (:441), through `__anon_inode_getfile`
(fs/anon_inodes.c:134-182, Linux v6.18.46) and its `alloc_file_pseudo`
(fs/file_table.c:408, same version), which forwards `alloc_path_pseudo`'s -ENOMEM (:402)
and `alloc_empty_file`'s -ENOMEM (:260), -ENFILE (:278) and whatever
`init_file`'s `security_file_alloc` returns (:180, forwarded at :265);
and the success, the descriptor
number.  No
-EINVAL is reachable on any of them — `timerfd_create` has one
`return -EINVAL` in its body, the gate's — so the decline costs coverage
and not precision.

The two errnos `__anon_inode_getfile` carries that this call CANNOT take
are worth naming as such, because the Rocq header lists them as if it
could: -ENOENT is the `try_module_get` failure (fs/anon_inodes.c:143-144,
Linux v6.18.46), which needs `fops->owner`, and `timerfd_fops`
(fs/timerfd.c:385-392, same version) sets
none; -ENODEV is `IS_ERR(anon_inode_inode)` (:154-156), and
`anon_inode_init` (:364-376) panics at :372 rather than leave that inode
an error.  `anon_inode_getfile_fmode` (:226-237) passes `make_inode =
false`, so the secure-inode leg is not taken either.  The rest of the
walk is the Rocq `timerfd_create_spec`'s header, which this corrects on
two points: that one, and `alloc_fd` carrying "-EMFILE as its only
errno", which `alloc_fdtable`'s -ENOMEM at fs/file.c:242 (Linux v6.18.46)
contradicts. -/
def timerfd_create_spec (clkid flags : word) : Sys SyscallEffect :=
  if timerfd_create_einval_b clkid flags
  then err_ret EINVAL      -- real -EINVAL, decided before anything is allocated
  else unmodeled           -- EPERM / ENOMEM / EMFILE / the descriptor: fail closed

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Timerfd
