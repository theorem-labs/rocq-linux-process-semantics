import LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Uapi.Sched — the ABI constants about the task itself

One part of `theories/LinuxProcessSem/Sys/Uapi.v` (see `Sys/Uapi.lean`
for the split).  WHAT GOES HERE: what is about the TASK rather than a
file, a socket, a clock, a signal or a mapping — the scheduling policies
and priorities (kernel/sched), the `clone` bit one argument depends on,
the futex words (kernel/futex), `wait4`'s option (kernel/exit.c), and the
identity, limit, uname, prctl and capability constants of kernel/sys.c
and kernel/groups.c.

TRUST BOUNDARY: this file is part of the trusted specification.

Every line below is read at Linux v6.18.46, commit
1f99e9ab748fc5c32120de9c4eca31abfe54a4d5. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

open LinuxProcessSemantics.Riscv.Prelude

/-! ## Scheduling policies (include/uapi/linux/sched.h)

4 is absent from the block on purpose — the header reserves it for an
unimplemented SCHED_ISO (line 118) and defines no name for it — so the
six numbers are not an interval and a membership test cannot be written
as a range.

`SCHED_EXT` is named for the opposite reason to the other five: no arm
ANSWERS it.  `Kernel.Sched.Syscalls.sched_setscheduler_spec` declines it,
and the constant exists so the decline can say which number it is
declining: whether kernel/sched/sched.h's `valid_policy` admits 7 at all
turns on CONFIG_SCHED_CLASS_EXT, and the model does not fix that
config. -/

/-- `#define SCHED_NORMAL 0` (include/uapi/linux/sched.h:114, Linux
v6.18.46, commit 1f99e9ab748f). -/
def SCHED_NORMAL : Int := 0

/-- `#define SCHED_FIFO 1` (include/uapi/linux/sched.h:115, Linux
v6.18.46, commit 1f99e9ab748f). -/
def SCHED_FIFO : Int := 1

/-- `#define SCHED_RR 2` (include/uapi/linux/sched.h:116, Linux v6.18.46,
commit 1f99e9ab748f). -/
def SCHED_RR : Int := 2

/-- `#define SCHED_BATCH 3` (include/uapi/linux/sched.h:117, Linux
v6.18.46, commit 1f99e9ab748f). -/
def SCHED_BATCH : Int := 3

/-- `#define SCHED_IDLE 5` (include/uapi/linux/sched.h:119, Linux
v6.18.46, commit 1f99e9ab748f). -/
def SCHED_IDLE : Int := 5

/-- `#define SCHED_DEADLINE 6` (include/uapi/linux/sched.h:120, Linux
v6.18.46, commit 1f99e9ab748f). -/
def SCHED_DEADLINE : Int := 6

/-- `#define SCHED_EXT 7` (include/uapi/linux/sched.h:121, Linux v6.18.46,
commit 1f99e9ab748f). -/
def SCHED_EXT : Int := 7

/-- `#define SCHED_RESET_ON_FORK 0x40000000` (include/uapi/linux/sched.h:124,
Linux v6.18.46, commit 1f99e9ab748f): the legacy "revert to SCHED_NORMAL
on fork" bit, ORed into the policy word rather than passed separately.
`_sched_setscheduler` (kernel/sched/syscalls.c, Linux v6.18.46) strips it
into `attr.sched_flags |= SCHED_FLAG_RESET_ON_FORK` before
`__sched_setscheduler` reads the policy, which is why it has to be masked
off a policy word before that word is compared against the six names
above. -/
def SCHED_RESET_ON_FORK : Int := 0x40000000

/-- `#define MAX_RT_PRIO 100` (include/linux/sched/prio.h:16, Linux
v6.18.46, commit 1f99e9ab748f): the first priority `__sched_setscheduler`
(kernel/sched/syscalls.c:567, Linux v6.18.46) refuses, with -EINVAL for
`attr->sched_priority > MAX_RT_PRIO-1` — so 1..99 are the RT priorities
and 0 is the only one a non-RT policy accepts.  Not a uapi constant: the
number a program is told to use is `sched_get_priority_max(SCHED_FIFO)`,
which computes it, but the comparison the model transcribes is against
this. -/
def MAX_RT_PRIO : Int := 100

/-- `#define CLONE_VM 0x00000100` (include/uapi/linux/sched.h:11, Linux
v6.18.46, commit 1f99e9ab748f): the bit that makes a new task share the
caller's address space.  Named for ONE reader, and it is not in `Sys/`:
it is the bit `Kernel.Futex.Syscalls`'s empty-waiter-set argument depends
on nobody ever granting, and `Checks.Cases.Kernel.Futex.Syscalls` turns
that dependency into a compile-time fact over both clone gates.
`Kernel.Fork` names the flag in prose and needs no constant, because its
gates are equalities on whole words rather than mask tests. -/
def CLONE_VM : Int := 256

/-! ## futex (include/uapi/linux/futex.h)

`SYSCALL_DEFINE6(futex, ...)` (kernel/futex/syscalls.c:188, Linux
v6.18.46) does not switch on `op` itself: `do_futex`
(kernel/futex/syscalls.c) splits it into a COMMAND, `op & FUTEX_CMD_MASK`,
and the two flag bits the mask removes, `FUTEX_PRIVATE_FLAG` and
`FUTEX_CLOCK_REALTIME` (`#define FUTEX_CMD_MASK ~(FUTEX_PRIVATE_FLAG |
FUTEX_CLOCK_REALTIME)`, line 28), so every OTHER bit of `op` is part of
the command and reaches the switch's `default: return -ENOSYS;`.

`FUTEX_PRIVATE_FLAG` is not decoration.  `futex_to_flags`
(kernel/futex/futex.h, Linux v6.18.46) sets `FLAGS_SHARED` exactly when
the bit is CLEAR, and that flag decides which key `get_futex_key`
(kernel/futex/core.c) builds — the private path keys on
`(current->mm, address)` and returns before it looks at a page at all,
the shared path can key on an inode two processes share.  So the bit
changes WHO can be waiting on the word, which is the whole of what
`Kernel.Futex.Syscalls.futex_spec` needs to decide. -/

/-- `#define FUTEX_WAIT 0` (include/uapi/linux/futex.h:11, Linux v6.18.46,
commit 1f99e9ab748f). -/
def FUTEX_WAIT : Int := 0

/-- `#define FUTEX_WAKE 1` (include/uapi/linux/futex.h:12, Linux v6.18.46,
commit 1f99e9ab748f). -/
def FUTEX_WAKE : Int := 1

/-- `#define FUTEX_PRIVATE_FLAG 128` (include/uapi/linux/futex.h:26, Linux
v6.18.46, commit 1f99e9ab748f). -/
def FUTEX_PRIVATE_FLAG : Int := 128

/-- `#define FUTEX_WAIT_PRIVATE (FUTEX_WAIT | FUTEX_PRIVATE_FLAG)`
(include/uapi/linux/futex.h:30, Linux v6.18.46, commit 1f99e9ab748f).
Computed through `Nat` because core Lean's `Int` has no `lor`; both
operands are non-negative. -/
def FUTEX_WAIT_PRIVATE : Int := ((FUTEX_WAIT.toNat ||| FUTEX_PRIVATE_FLAG.toNat : Nat) : Int)

/-- `#define FUTEX_WAKE_PRIVATE (FUTEX_WAKE | FUTEX_PRIVATE_FLAG)`
(include/uapi/linux/futex.h:31, Linux v6.18.46, commit 1f99e9ab748f). -/
def FUTEX_WAKE_PRIVATE : Int := ((FUTEX_WAKE.toNat ||| FUTEX_PRIVATE_FLAG.toNat : Nat) : Int)

/-- The width of a futex word, in bytes.  `futex_size`
(kernel/futex/futex.h, Linux v6.18.46) is `1 << (flags & FLAGS_SIZE_MASK)`,
and `futex_to_flags` (kernel/futex/futex.h) hands the legacy `futex`
entry point `FLAGS_SIZE_32` unconditionally — the size bits come only
from the `futex2` flag word, which reaches the kernel through
`futex_waitv`/`futex_wake`/`futex_wait` (449, 454, 455), none of which has
an arm here; `futex_flags_valid` (kernel/futex/futex.h:82, Linux
v6.18.46) refuses anything but `FLAGS_SIZE_32` anyway ("Only 32bit
futexes are implemented -- for now").  So 4 is the width for every call this spec can see, and it
is both things `get_futex_key` (kernel/futex/core.c, Linux v6.18.46) uses
it for: the alignment the address must have, and the length `access_ok`
is given. -/
def FUTEX_WORD_SIZE : Int := 4

/-! ## wait4 (include/uapi/linux/wait.h) -/

/-- `#define WNOHANG 0x00000001` (include/uapi/linux/wait.h:5, Linux
v6.18.46, commit 1f99e9ab748f): the one wait4 option this model accepts.
That header is where every `W*` macro lives, byte-identical in mainline
from v3.10 through v7.2; include/linux/wait.h is wait-queue types and
defines none of them.  WUNTRACED, WCONTINUED, __WNOTHREAD, __WCLONE and
__WALL are not named because no arm reads them: they select which
children are eligible and which state changes are reportable, questions
about children this model does not have.  Anything but WNOHANG declines;
see `Kernel.Exit.wait4_spec`. -/
def WNOHANG : Int := 1

/-! ## Identity and limits (kernel/sys.c, kernel/groups.c) -/

/-- `(uid_t)-1`, after the `Syscall.uid32` narrowing.  No process can hold
it — `make_kuid` maps it to `INVALID_UID` (include/linux/uidgid.h:50 and
:139, Linux v6.18.46, commit 1f99e9ab748f) and `Run.valid_id` excludes
it — so `setuid` and `setgid` reject it with -EINVAL, and `setresuid` and
`setresgid` read it as "leave this id alone". -/
def ID_MINUS_ONE : word := Z_to_bv 64 4294967295

/-- `#define RLIMIT_CORE 4` (include/uapi/asm-generic/resource.h:20, Linux
v6.18.46, commit 1f99e9ab748f; Rocq read it byte-identical at
v6.10-v6.15): the maximum size of a core dump. -/
def RLIMIT_CORE : Int := 4

/-- `#define NGROUPS_MAX 65536` (include/uapi/linux/limits.h:7, Linux
v6.18.46, commit 1f99e9ab748f): the ceiling on a process's supplementary
group list, standing since before v2.6.12.  Enforced where the list is
WRITTEN — `SYSCALL_DEFINE2(setgroups, ...)` (kernel/groups.c:198, Linux
v6.18.46) answers -EINVAL for a `gidsetsize` above it — so no
`struct group_info` a process can hold is longer.
`Kernel.Groups.getgroups_spec` reads it as the bound that makes its own
answer one an `int` return can carry. -/
def NGROUPS_MAX : Int := 65536

/-- `#define __NEW_UTS_LEN 64` (include/uapi/linux/utsname.h:15, Linux
v6.18.46, commit 1f99e9ab748f): the length of a `struct new_utsname`
field WITHOUT its terminator.  Every one of the struct's six members is
declared `char field[__NEW_UTS_LEN + 1]` (lines 25-32), so the field a
`uname` (160) copies out is 65 bytes wide and the string in it is at most
64 characters.  `Kernel.Sys.uname_spec` reads it as the field stride; the
+1 is what guarantees a terminator inside the field. -/
def NEW_UTS_LEN : Int := 64

/-- `sizeof(struct new_utsname)`: six 65-byte `char` arrays, so 390 bytes
with no padding anywhere — a struct of `char` arrays has alignment 1
(`struct new_utsname`, include/uapi/linux/utsname.h:25-32, Linux v6.18.46,
commit 1f99e9ab748f).  The width of the SINGLE
`copy_to_user(name, &tmp, sizeof(tmp))` in
`SYSCALL_DEFINE1(newuname, ...)` (kernel/sys.c:1351, Linux v6.18.46),
which is why `Kernel.Sys.uname_spec` gates one range of exactly this size
rather than six.  The member order is fixed by the same declaration:
`sysname`, `nodename`, `release`, `version`, `machine`, `domainname`, at
offsets 0, 65, 130, 195, 260 and 325. -/
def NEW_UTSNAME_SIZE : Int := 390

/-- `#define PR_CAPBSET_READ 23` (include/uapi/linux/prctl.h:71, Linux
v6.18.46, commit 1f99e9ab748f): the one `prctl` option this model
answers.  NOT handled in kernel/sys.c's own `switch`: the LSM hook
`security_task_prctl` runs first in `SYSCALL_DEFINE5(prctl, ...)`
(kernel/sys.c:2518), and capability's implementation of it,
`cap_task_prctl` (security/commoncap.c, Linux v6.18.46), answers this
option and returns before the syscall body's `switch` is reached.  See
`Kernel.Sys.prctl_spec`. -/
def PR_CAPBSET_READ : Int := 23

/-- `#define CAP_LAST_CAP CAP_CHECKPOINT_RESTORE` over
`#define CAP_CHECKPOINT_RESTORE 40` (include/uapi/linux/capability.h:421
and :423, Linux v6.18.46, commit 1f99e9ab748f).  `cap_valid`, defined in
the same header (line 425) as `((x) >= 0 && (x) <= CAP_LAST_CAP)`, is
what `cap_task_prctl` (security/commoncap.c) tests `PR_CAPBSET_READ`'s
`arg2` against, and it is the ONLY thing separating the option's answer
from -EINVAL.  A VERSION FACT, and the narrowest claim in
`Kernel.Sys.prctl_spec`: 40 has been the last capability since v5.9
added `CAP_CHECKPOINT_RESTORE`, and a kernel that adds a 41st moves the
-EINVAL boundary this model pins — a boundary programs SEARCH FOR
(libcap's `cap_max_bits` binary-searches it). -/
def CAP_LAST_CAP : Int := 40

end LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
