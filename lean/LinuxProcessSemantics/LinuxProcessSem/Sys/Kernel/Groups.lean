-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Sys/Kernel/Groups.v

import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi


/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Kernel.Groups — getgroups (158), setgroups (159)

Mirrors `theories/LinuxProcessSem/Sys/Kernel/Groups.v`, which answers to
Linux `kernel/groups.c`: it holds what the kernel defines there, and
nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Kernel/Groups.lean`.

Both definitions keep the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
Rocq's own comment argues `getgroups` over the whole v4.9-to-v6.18
interval without line numbers, and pins `setgroups` at v6.18.46 with the
file byte-identical at every mainline release tag from v6.10 through
v6.18 — an interval, not a point.  Every line number below was read at
v6.18.46 in the checkout linux-process-semantics@ff0313ba4f:AGENTS.md names, and is labelled so.

ONE SPELLING DIFFERS FROM ROCQ without changing a value: Rocq's
`Z.of_nat (length ...)` is Lean's `(... .length : Int)`, and Rocq's
`(x <? y)%Z` / `(x =? y)%Z` Bool tests are Lean's decidable `<` and `=`
on `Int`, which `sys_norm`'s `+decide` pass decides on a closed model
exactly as `vm_compute` decides the Bool. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Groups

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- `getgroups gidsetsize grouplist` (158): how many supplementary groups
the process has, and — on the one path this spec DECLINES — the groups
themselves.

THE WHOLE KERNEL FUNCTION, in its own order
(`SYSCALL_DEFINE2(getgroups, ...)`, kernel/groups.c:161-183, Linux
v6.18.46, commit 1f99e9ab748f, and the one helper it calls,
`groups_to_user`, kernel/groups.c:37-51):

    const struct cred *cred = current_cred();           /* :163     */
    int i;                                              /* :164     */
    if (gidsetsize < 0)            return -EINVAL;      /* :166-167 */
    i = cred->group_info->ngroups;                      /* :170     */
    if (gidsetsize) {                                   /* :171     */
      if (i > gidsetsize)          { i = -EINVAL; goto out; }  /* :172-175 */
      if (groups_to_user(grouplist, cred->group_info))
                                   { i = -EFAULT; goto out; }  /* :176-179 */
    }
    out: return i;                                      /* :181-182 */

ORDER IS THE POINT HERE, three times over, and the Rocq definition
`Kernel.Groups.getgroups_spec` carries the full argument, including the
evidence that both functions are byte-identical from v4.9 through v6.18.

- The NEGATIVE SIZE is refused at :166-167, before `current_cred()`'s
  `group_info` is read at :170, so a negative `gidsetsize` with a garbage
  `grouplist` is -EINVAL and never -EFAULT.
- A SIZE OF ZERO skips the whole `if (gidsetsize)` block (:171), so the
  pointer is not touched at any width and the call answers the count.
- A SIZE TOO SMALL is -EINVAL at :172-175, BEFORE any store, so
  `getgroups(1, <garbage>)` on a process with five groups is -EINVAL
  rather than -EFAULT.

`gidsetsize` is an `int`, so only the low half of a0 reaches these
comparisons and it is read as two's complement (`__SC_CAST`,
include/linux/syscalls.h:132, Linux v6.18.46, applied by
`__SYSCALL_DEFINEx`, arch/riscv/include/asm/syscall_wrapper.h:82-88,
Linux v6.18.46).  `Syscall.sint32` is that reading.  `grouplist` is a full 64-bit pointer and is NOT an
argument of this spec at all, which is the sharpest way to state what the
arms below share: no modeled path reads it.

LINUX HAS NO UPPER BOUND ON `gidsetsize`.  `SYSCALL_DEFINE2(setgroups,
...)` rejects a size above `Uapi.NGROUPS_MAX` (kernel/groups.c:205-206,
Linux v6.18.46); `getgroups` does not test it at all, so `getgroups(70000, buf)` is the
count on a process whose list fits, and would be the WRITE — the declined
arm below — on one whose list does not.  Nothing below compares `n` against
`NGROUPS_MAX` for that reason — the guard further down is on the STORED
list's length, not on the argument.  QEMU's user-mode emulation, a
supported implementation, DOES test it: `TARGET_NR_getgroups`
(linux-user/syscall.c:12589-12591, QEMU v11.1.1) answers -EINVAL above
`NGROUPS_MAX` before the host call is made.  What that costs is on the
zero-length arm below.

THE ZERO-LENGTH LIST IS THE SUBTLE ARM.  With `gidsetsize > 0` and no
supplementary groups, control does enter the block, but
`groups_to_user`'s loop (kernel/groups.c:44-49, Linux v6.18.46) runs
`ngroups` times — zero — and returns 0 at :50 without a single
`put_user`.  There is no
up-front `access_ok` over the array; validation is per element, inside
the loop at :47.  So `getgroups(64, <a garbage pointer>)` returns 0, not
-EFAULT, for a process with no supplementary groups.

THAT IS LINUX'S ANSWER, AND THE ARM ADMITS IT ALONE.  qemu-user
(`TARGET_NR_getgroups`, linux-user/syscall.c:12599-12604, QEMU v11.1.1)
locks the whole `gidsetsize * sizeof(target_id)` range for writing before
it copies anything, and `lock_user` returns NULL where `access_ok_untagged`
fails (linux-user/uaccess.c:8-15, QEMU v11.1.1), so the same call is
-EFAULT there even
at zero groups; the size above `NGROUPS_MAX` is -EINVAL there, as the
paragraph above says.  At those two shapes no answer lies in the
intersection of the supported implementations, and the sound arm would
decline.  This twin keeps Rocq's arm by the port's rules;
`linux-process-semantics@ff0313ba4f:bugs/getgroups-empty-list-arm-admits-linux-alone.md` records the defect
and what closes it, and the twin moves when Rocq does.

DECLINED: `gidsetsize >= ngroups > 0`, the path that WRITES.
`groups_to_user` stores `ngroups` 4-byte `gid_t`s ascending from
`grouplist`, each through its own `put_user` (:47), and a fault at
element k leaves elements 0..k-1 written — the kernel does not roll back.
The Rocq definition states the cost: a program that reads its own group
list leaves the modeled surface on that call; one that only asks HOW MANY
does not.  Not modeled either, and not the same kind of gap:
`from_kgid_munged` (:46, kernel/user_namespace.c:533-542, Linux v6.18.46)
answers an unmappable gid with `overflowgid` rather than an errno, so the element
values this spec does not hand out would depend on the caller's user
namespace, which `State.creds_privileged`'s standing assumptions fix to
the init one.

THE `NGROUPS_MAX` GUARD is a fail-closed answer to a state Linux cannot
build.  The allocator itself does NOT bound it — `groups_alloc`
(kernel/groups.c:15-25, Linux v6.18.46) sets `gi->ngroups = gidsetsize`
at :23 from
whatever its caller passes — so the bound is the caller's, and what makes
the state unreachable here is narrower than "the kernel never allocates
one": on riscv64 the only way the CALLING TASK's list is installed is
`setgroups` (159), whose `(unsigned)gidsetsize > NGROUPS_MAX` at
kernel/groups.c:205-206 (Linux v6.18.46) refuses a longer one.
`set_groups` (kernel/groups.c:118-123, Linux v6.18.46) holds the tree's
only assignment to a task credential's `group_info` (:122),
`set_current_groups` (kernel/groups.c:134-157, Linux v6.18.46) is what
this syscall reaches it through, and
`setgroups16` (kernel/uid16.c:177, Linux v6.18.46), which bounds it the
same way, has no number on this
architecture — riscv does not select `HAVE_UID16`.  So a longer
`State.cr_groups` describes no process; the count such a state would
report might not even fit the `int` this syscall returns (`ngroups` is an
`int`, include/linux/cred.h:30, Linux v6.18.46).  Rather than answer for
it, the spec declines — AFTER the negative-size check,
because that check comes first in the kernel and an impossible state must
not reorder a behavior. -/
def getgroups_spec (gidsetsize : word) : Sys SyscallEffect :=
  let n := sint32 gidsetsize
  if n < 0 then err_ret EINVAL
  else
    m <- get_model ;;
    let ng : Int := ((m_creds m).cr_groups).length
    if NGROUPS_MAX < ng then unmodeled
    else if n = 0 then ret_only (Z_to_bv 64 ng)
    else if n < ng then err_ret EINVAL
    else if ng = 0 then ret_only (Z_to_bv 64 0)
    else unmodeled

/-- `setgroups gidsetsize grouplist` (159): -EPERM for an unprivileged
caller, and FAIL CLOSED for a privileged one
(`SYSCALL_DEFINE2(setgroups, ...)`, kernel/groups.c:198-222, Linux
v6.18.46, commit 1f99e9ab748f).  `may_setgroups`
(kernel/groups.c:185-191, Linux v6.18.46) is TWO conjuncts, and `State.creds_privileged`
answers them for two different reasons, which is worth separating because
only one of them is a question about the caller:
`ns_capable_setid(user_ns, CAP_SETGID)` (kernel/capability.c:398, Linux
v6.18.46) is the capability question an effective uid stands in for,
while `userns_may_setgroups(user_ns)` (kernel/user_namespace.c:1293,
Linux v6.18.46) is a
per-namespace POLICY BIT that no uid answers — `gid_map.nr_extents != 0
&& (flags & USERNS_SETGROUPS_ALLOWED)` at :1301-1303, and a write of
"deny" to /proc/PID/setgroups clears that flag (:1279).  What discharges
it is instead `State.creds_privileged`'s standing INIT-NAMESPACE
assumption: `init_user_ns` is built with `.flags = USERNS_INIT_FLAGS`
(kernel/user.c:76, Linux v6.18.46), which IS `USERNS_SETGROUPS_ALLOWED`
(include/linux/user_namespace.h:38, :40, Linux v6.18.46), and with one
gid-map extent (kernel/user.c:48-56, Linux v6.18.46), so the bit holds
there.

The -EPERM half is exact GIVEN THOSE ASSUMPTIONS, and it is exact for a
reason worth naming: `may_setgroups()` is the FIRST thing the syscall
does (:203-204), before the `gidsetsize` bound at :205-206 and before the
pointer is touched at :211.  So an unprivileged caller gets -EPERM
whatever it passes — a negative size, a size past `NGROUPS_MAX`, an
unmapped list — and the spec needs neither argument.

THAT IS LINUX'S ORDER, AND THIS ARM ADMITS ITS ANSWER ALONE, at exactly
those three shapes.  qemu-user runs BOTH argument tests before the host
call `may_setgroups` is reached through: `TARGET_NR_setgroups`
(linux-user/syscall.c:12613-12639, QEMU v11.1.1) answers -EINVAL for a size
negative or above `NGROUPS_MAX` at :12620-12621, and -EFAULT for an
unreadable list at :12628-12631 — `lock_user` is NULL where
`access_ok_untagged` fails (linux-user/uaccess.c:8-15, QEMU v11.1.1) — and
only reaches
`sys_setgroups` at :12639.  QEMU's user-mode emulation is a supported
implementation, so at those shapes the intersection is EMPTY and the
sound arm would decline rather than answer -EPERM.  This twin keeps
Rocq's arm by the port's rules;
`linux-process-semantics@ff0313ba4f:bugs/setgroups-eperm-arm-admits-linux-alone.md` records the defect and
what closes it, and the twin moves when Rocq does.

The successful half is DECLINED rather than faked.  It writes the
supplementary group list — `State.cr_groups`, the list `getgroups` (158)
above reports the length of (`set_current_groups`,
kernel/groups.c:134-157, Linux v6.18.46) — so accepting the call while discarding what it wrote would make the
next `getgroups` answer for a list nobody set.  What is left to model is
the per-element import `groups_from_user` (kernel/groups.c:54-74, Linux
v6.18.46) does, with the kernel's index-ordered -EFAULT-before-EINVAL precedence (:64-70:
element k's `get_user` is tested before element k's `gid_valid`, and
both before element k+1 is read at all), and `groups_sort`'s ascending
reorder (:84-88, :217), which is observable because `getgroups` hands
back the STORED order and not the written one.  The Rocq definition
`Kernel.Groups.setgroups_spec` states the cost: a privilege drop of the
usual `setgroups`/`setgid`/`setuid` shape leaves the modeled surface at
the first of the three. -/
def setgroups_spec : Sys SyscallEffect :=
  m <- get_model ;;
  if creds_privileged (m_creds m) then unmodeled else err_ret EPERM

end LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Groups
