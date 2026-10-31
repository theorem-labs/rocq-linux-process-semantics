import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Kernel.Sys — getpid (172), gettid (178), setsid (157), uname (160), prctl (167), prlimit64 (261), and the eight id calls

Mirrors `theories/LinuxProcessSem/Sys/Kernel/Sys.v`.  This file answers to
Linux `kernel/sys.c`: it holds what the kernel defines there, and nothing
else.

TRUST BOUNDARY: this file is part of the trusted specification.

The baseline above is the squash that landed the 2026-09-11 work on
`main` (#794).  The definitions were read at
f44244ad6b8041aa83053d9ca91e090037ed743b, the commit the plan names, and
the file they were read from is the blob the baseline holds —
`git rev-parse a71fd38a:theories/LinuxProcessSem/Sys/Kernel/Sys.v` is
3455c9496e9859e7e2a206dd13a994484eba64f2 — so a reader needs no other
commit, and the header names the one the parity check accepts: it refuses
a baseline that is not an ancestor of the tree it runs in, and the
2026-09-11 commits survive in no history descending from `main`.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f), every one re-read there
— and point at the Rocq definition for the argument in full, so there is
one place to correct it.  Where the Rocq comment quotes a version RANGE
(`v6.10-v6.16` on `getpid_spec`, `v4.17..v7.2` on `setsid_spec`) the range
is Rocq's reading and is named as such; the lines cited here are the
pinned tree's.

Spellings that differ from Rocq without changing a value: `&&`, `||` and
`!` stand for `andb`, `orb` and `negb`; `==` on `Int` and `Nat` stands for
`Z.eqb` and `Nat.eqb`, and a `decide`d `≤` / a Prop `<` under `if` for
`Z.leb` / `Z.ltb`; a record field is read as `t.id_real` where Rocq writes
`id_real t`; the table applies `getid_spec` to the projection
`Creds.cr_uid` where Rocq writes `cr_uid`; `bs.take`, `bs.drop`,
`List.replicate`, `cs.map`, `l1.zip l2` with `.all`, and `l.getD 64 d`
stand for `firstn`, `skipn`, `repeat`, `map`, `forallb` over `combine`,
and `nth 64 l d`; and a `match` that Rocq writes bare under an `if` is
parenthesised here.

`getppid` (173) is declined by BOTH trees, for the reason on
`getid_spec`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sys

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork

/-- `getpid` (172): returns the caller's thread-group id.  It takes no
arguments and has no failure path — `SYSCALL_DEFINE0(getpid)`
(kernel/sys.c:999-1002, Linux v6.18.46, commit 1f99e9ab748f) is
`return task_tgid_vnr(current);` and nothing else.  riscv overrides the
generic zero-argument form with one whose `pt_regs` parameter is
`__unused` and that expands without `SC_RISCV_REGS_TO_ARGS`
(arch/riscv/include/asm/syscall_wrapper.h:99-103, Linux v6.18.46), so no
argument register is read on this path and the spec ignores all of them.

IT IS THE SAME NUMBER `set_tid_address` RETURNS, and the model shares the
relation rather than restating it, so the two can never drift apart.  The
argument in full is on the Rocq definition `Kernel.Sys.getpid_spec` and is
not repeated; what follows is the line each step of it rests on, re-read
at Linux v6.18.46.  `task_tgid_vnr` is `__task_pid_nr_ns(tsk, PIDTYPE_TGID,
NULL)` and `task_pid_vnr` is the same call at `PIDTYPE_PID`
(include/linux/pid.h:296-299 and :244-247); both resolve the NULL
namespace to `task_active_pid_ns(current)` in `__task_pid_nr_ns`
(kernel/pid.c:510-522, at :517, Linux v6.18.46), so no pid namespace can separate them.
They then differ only in which `struct pid` `task_pid_ptr` reads —
`&task->thread_pid` for `PIDTYPE_PID`, `&task->signal->pids[type]`
otherwise (kernel/pid.c:330-335, Linux v6.18.46) — and `copy_process` installs ONE
`struct pid` in both slots for a task that leads its thread group:
`init_task_pid(p, PIDTYPE_PID, pid)` and, under `thread_group_leader(p)`,
`init_task_pid(p, PIDTYPE_TGID, pid)` (kernel/fork.c:2379-2381, Linux v6.18.46).  The
precondition is therefore "the caller is its own thread-group leader",
which every task this model describes is: the Rocq argument rests on
`Checks.ProcessCreation.clone_sharing_flags_unmodeled`, which proves that
any `CLONE_THREAD` in a clone flag word forces `Unmodeled`.  The Lean
tree closes the same window on a CONDITION rather than on the table's
contents: no arm may accept a flag word carrying `CLONE_THREAD`.  While
`clone` (220) and `clone3` (435) have no arm the table declines them
outright; the arms ticket S-Kernel-Fork-clone gives them accept only the
plain-fork flag word and decline every word with a sharing flag, so the
premise holds in either merge order and is what a later widening of that
gate would have to re-argue.

The envelope the shared relation draws from is `PID_MAX_ENVELOPE`, argued
on that constant.  Residual infidelity, stated rather than modeled:
`SYSCALL_DEFINE0` emits `ALLOW_ERROR_INJECTION(..., ERRNO)`
(include/linux/syscalls.h:218-222, Linux v6.18.46, and the riscv form above), so a kernel
built with `CONFIG_FUNCTION_ERROR_INJECTION` and a BPF program calling
`bpf_override_return` can make this call return an errno; the model
describes a kernel with no such override attached. -/
def getpid_spec : Sys SyscallEffect := set_tid_address_spec

/-- `gettid` (178): returns the caller's THREAD id.  Like `getpid` it
takes no arguments and has no failure path — `SYSCALL_DEFINE0(gettid)`
(kernel/sys.c:1005-1008, Linux v6.18.46, commit 1f99e9ab748f) is
`return task_pid_vnr(current);` — and riscv's zero-argument override does
not read a register for it either (arch/riscv/include/asm/syscall_wrapper.h:99-103).

IT IS THE SAME NUMBER `set_tid_address` RETURNS, and the argument is
SHORTER than `getpid`'s and rests on less: `gettid` answers
`task_pid_vnr(current)` and so does `SYSCALL_DEFINE1(set_tid_address)`
(kernel/fork.c:1747-1752, at :1751, Linux v6.18.46) — one expression evaluated twice in
the same task, so no namespace argument and no `task_pid_ptr` case split
is needed to join them.  What it DOES rest on is the premise the state
carries: `State.m_tid` is one slot, so the model describes a process with
one task, and the fail-closed obligation that keeps that honest is the
absence of any thread-creating arm (the Rocq argument names
`Checks.ProcessCreation.clone_sharing_flags_unmodeled`; here it is the
condition stated on `getpid_spec`: no arm admits a `CLONE_THREAD` word).  The rest of the argument, and why widening the clone flag
word would break `getpid`'s claim and leave this one standing, is on the
Rocq definition `Kernel.Sys.gettid_spec`.  The error-injection residual
stated on `getpid_spec` covers this number too. -/
def gettid_spec : Sys SyscallEffect := set_tid_address_spec

/-- `setsid()` (157): makes the caller a session leader, or fails -EPERM.

`ksys_setsid` (kernel/sys.c:1268-1301, Linux v6.18.46, commit
1f99e9ab748f) seeds `int err = -EPERM;` (:1274) and returns it unless BOTH
tests pass: the caller must not already carry
`group_leader->signal->leader` (:1278), and `pid_task(sid, PIDTYPE_PGID)`
must find no live task whose process-group id is the caller's own pid
(:1284; `pid_task`, kernel/pid.c:414-425, Linux v6.18.46).  On success it sets that leader
bit (:1287), calls `set_special_pids(pids, sid)` (:1288;
kernel/sys.c:1257-1266, Linux v6.18.46) and answers `session`, which is `pid_vnr(sid)` of
`task_pid(group_leader)` (:1271-1273; `pid_vnr`, kernel/pid.c:504-507, Linux v6.18.46):
the caller's tgid, the value `getpid` returns and the value this model
keeps in `State.m_tid`.  `SYSCALL_DEFINE0(setsid)` (kernel/sys.c:1303-1306, Linux v6.18.46)
is `return ksys_setsid();`, so the wrapper adds nothing.  Rocq states the
version window in which the two tests, their order and the answer are
unchanged (mainline v4.17..v7.2) and names the one textual edit inside it;
that argument is on the Rocq definition `Kernel.Sys.setsid_spec`.

WHY EVERY CALL BUT THE FIRST SUCCESS ADMITS BOTH ANSWERS.  Whether either
test fires is a fact about the launching environment and about OTHER
PROCESSES, which `State.ProcInput` does not carry, so the model says so
the way it does everywhere an environment condition is untracked: with an
`alt`.  Admitting only success would be wrong rather than conservative.

WHY ONLY SUCCESS IS RECORDED.  A -EPERM is not always sticky (the group
that blocked the call can empty out), so recording a failure would forbid
a run Linux allows.  A success is sticky and permanent: `ksys_setsid` is
the only writer of `signal->leader` in the tree (kernel/sys.c:1287, Linux v6.18.46), it
never clears it, it tests it first, and `SYSCALL_DEFINE2(setpgid)`
refuses to move a session leader out of its group (kernel/sys.c:1114, Linux v6.18.46, the
`if (p->signal->leader)` refusal at :1157-1159).  So one bit,
`State.m_setsid_succeeded`, is what has to be carried.

THE SESSION ID is the caller's tgid, equal to the tid
`Fork.set_tid_address_spec` reports because this model has one thread, so
it is `State.m_tid`: drawn in the same envelope, and equal to any value
already observed.  The consistency is written into the `choose` rather
than read out of `State.m_tid` by a match, which keeps the two arms of the
`alt` disjoint for EVERY model: a return of `errno_ret EPERM` can never
satisfy the range.  No memory effect — setsid takes no arguments and
writes nothing.  What success also does and why it does not show
— the terminal hook `ksys_setsid` calls while it still holds the tasklist
lock (kernel/sys.c:1290, Linux v6.18.46) and the connector and autogroup
hooks it calls after the unlock (:1297-1298) — is argued on the Rocq
definition and recorded in
`bugs/setsid-clears-a-controlling-terminal-invisibly.md`. -/
def setsid_spec : Sys SyscallEffect :=
  m <- get_model ;;
  if m_setsid_succeeded m then err_ret EPERM
  else
    alt (err_ret EPERM)                       -- an untracked environment condition
        (tid <- choose (fun t =>
                  (0 < bv_unsigned t ∧ bv_unsigned t < PID_MAX_ENVELOPE) ∧
                  match m_tid m with
                  | none => True
                  | some t0 => t = t0) ;;
         set_tid tid ;;
         set_setsid_succeeded ;;
         ret_only tid)

/-! ## prlimit64 (261) -/

/-- A `struct rlimit64` as the sixteen bytes Linux moves through
`copy_to_user`: `__u64 rlim_cur` then `__u64 rlim_max`, little-endian,
8-byte aligned, no padding — `struct rlimit64`
(include/uapi/linux/resource.h:50-53, Linux v6.18.46, commit
1f99e9ab748f).  `rlim64_soft` is the first eight bytes as a word and
`rlim64_hard` the last eight.

The kernel stores a `struct rlimit` of `__kernel_ulong_t` and converts
with `rlim_to_rlim64` (kernel/sys.c:1682-1692, Linux v6.18.46) and
`rlim64_to_rlim` (kernel/sys.c:1694-1704, Linux v6.18.46), but on
riscv64 both are the IDENTITY: `BITS_PER_LONG` is 64, so the `~0UL` of
`RLIM_INFINITY` (include/uapi/asm-generic/resource.h:57-58, Linux
v6.18.46) and the `~0ULL` of `RLIM64_INFINITY`
(include/uapi/linux/resource.h:48, Linux v6.18.46) are one pattern and
`rlim64_is_infinity` (kernel/sys.c:1673-1680, Linux v6.18.46) collapses
nothing.  Every 64-bit pattern round-trips unchanged, which is why this
model stores the user's words verbatim and only ever PROJECTS out of
them; why it never decodes and re-encodes them is argued on the Rocq
definition `Kernel.Sys.rlim64_soft`. -/
def rlim64_soft (bs : List byte) : word := le_bytes_to_word (bs.take 8)

/-- The hard limit, `rlim_max`: bytes 8..15 of the pair as a word. -/
def rlim64_hard (bs : List byte) : word := le_bytes_to_word (bs.drop 8)

/-- The kernel's standing invariant on a limit pair: sixteen bytes wide,
and soft ≤ hard.  `do_prlimit` (kernel/sys.c:1500-1561, Linux v6.18.46,
commit 1f99e9ab748f) refuses to store a pair whose `rlim_cur` exceeds its
`rlim_max` with -EINVAL (:1511-1512), before any capability or LSM
question and before it reads the task's current pair, so no
`prlimit64` read reports soft > hard.  No other path creates such a pair
either — the Rocq definition `Kernel.Sys.rlim64_wf` asserts that without
the enumeration, so it is here.  At v6.18.46 the RLIMIT_CORE slot is
written by `do_prlimit`'s store (kernel/sys.c:1535-1536, Linux v6.18.46,
behind the -EINVAL above), by `umh_coredump_setup`, which stores the
pair {1, 1} (fs/coredump.c:660, Linux v6.18.46), by
`selinux_bprm_committing_creds`, which lowers every soft limit to the
minimum of its hard limit and the init task's soft one
(security/selinux/hooks.c:2536-2541, Linux v6.18.46), and by
`copy_signal`, which copies the parent's pairs whole (kernel/fork.c:1693,
Linux v6.18.46); `INIT_RLIMITS` starts the resource at {0, RLIM_INFINITY}
(include/asm-generic/resource.h:17, Linux v6.18.46).  None yields soft >
hard.  This is the predicate the first read's `choose` draws from, and
the whole of what that read admits. -/
def rlim64_wf (bs : List byte) : Bool :=
  (bs.length == 16)
  && decide (bv_unsigned (rlim64_soft bs) ≤ bv_unsigned (rlim64_hard bs))

/-- `prlimit64(pid, resource, new_rlim, old_rlim)` — syscall 261, which
riscv64 reaches through `__NR_prlimit64`
(include/uapi/asm-generic/unistd.h:635-636, Linux v6.18.46, commit
1f99e9ab748f).  The argument in full — why this number and not
`getrlimit` (163) / `setrlimit` (164), why only `RLIMIT_CORE`, why each
of the declines below is a decline rather than an answer, and what they
cost `Equivalence.strong_equiv` — is on the Rocq definition
`Kernel.Sys.prlimit64_spec` and is not repeated; what follows is the line
each decision rests on, re-read at Linux v6.18.46.

THE KERNEL'S ORDER IS NOT THIS SPEC'S.  `SYSCALL_DEFINE4(prlimit64)`
(kernel/sys.c:1729-1792, Linux v6.18.46) copies `new_rlim` in FIRST,
answering -EFAULT (:1744-1745); resolves `pid` next, 0 meaning
`current` and taking no lookup, anything else `find_task_by_vpid`
(:1751; kernel/pid.c:438-441, Linux v6.18.46) and -ESRCH when it names
nothing (:1752-1755); then `check_prlimit_permission`
(kernel/sys.c:1707-1727, Linux v6.18.46), whose first line returns 0 when
the task is the caller (:1713-1714); then, under a `need_tasklist` gate
that is `!same_thread_group(tsk, current)` (:1764) and so false for pid 0,
a second -ESRCH from `pid_alive` (:1772-1773); then `do_prlimit`
(kernel/sys.c:1500-1561, Linux v6.18.46): `resource >= RLIM_NLIMITS`
-EINVAL (:1506-1507), `rlim_cur > rlim_max` -EINVAL (:1511-1512), a
`RLIMIT_NOFILE` ceiling -EPERM (:1513-1515), `capable(CAP_SYS_RESOURCE)`
-EPERM only when the hard limit RISES (:1526-1528), then
`security_task_setrlimit` (:1530; security/security.c:3790-3794, Linux
v6.18.46), then the read of the old pair (:1533-1534) and the store of
the new one (:1535-1536); and last the copy-out of `old_rlim`, -EFAULT
(:1784-1787).  This spec tests pid, then resource, then the pointer
pairing, then read against write, and declines on every arm where the two
orders could be told apart, so nothing here depends on their agreeing;
what that costs — a `prlimit64(0, 9999, bad_ptr, NULL)` Linux answers
-EFAULT and this spec declines — is item (3) of the Rocq argument.  Two
more declines sit inside the first two gates: `pid` is a `pid_t` and
`resource` an `unsigned int` in that prototype, so Linux answers
`prlimit64(2^32, …)` as pid 0 and `prlimit64(0, 2^32 | RLIMIT_CORE, …)`
as `RLIMIT_CORE`, while this spec reads both registers whole and
declines them (the `pid-high` and `res-high` probe cases).

THE READ (`new_rlim` NULL).  With `old_rlim` wholly writable the pair
lands there and 0 is returned.  On the FIRST read the environment
chooses it, subject only to `rlim64_wf`, and the model records it in
`State.m_rlimit_core`; every later read repeats the record, and a
successful set REPLACES it.  Linux's own boot default is `{0,
RLIM_INFINITY}` for this resource — `INIT_RLIMITS`
(include/asm-generic/resource.h:17, Linux v6.18.46) — but a parent may
have set anything, so pinning that constant would be a narrower claim
than the truth.

THE WRITE (`old_rlim` NULL).  Once the sixteen bytes are readable they
are recorded as a copy-in — including when the pair is then refused —
because `_inline_copy_from_user` (include/linux/uaccess.h:159-185, Linux
v6.18.46) has already loaded them; the -EINVAL of `rlim_cur > rlim_max`
follows (kernel/sys.c:1511-1512).  Otherwise the new HARD limit must
equal the recorded one: raising it is the `capable(CAP_SYS_RESOURCE)`
question (:1526-1528) this model carries no credentials to decide, and
lowering it is a deliberate bound rather than a necessity, argued on the
Rocq definition.  The two LSM readings behind that argument, re-read:
`selinux_task_setrlimit` (security/selinux/hooks.c:4526-4540, Linux
v6.18.46) consults the AVC only when `rlim_max` changes (:4535-4536), so
an unchanged hard limit is unconditionally 0 there; AppArmor is the
COUNTEREXAMPLE — `apparmor_task_setrlimit` (security/apparmor/lsm.c:1000-1015,
Linux v6.18.46) reaches `profile_setrlimit` (security/apparmor/resource.c:88-100,
Linux v6.18.46), which answers -EACCES whenever the new hard limit is
above a confining profile's ceiling (:95-97), changed or not — and what
covers it is this model's standing position that it has no LSM at all,
not anything about the arm.  The unchanged-hard 0 below rests on that
position, as `prctl_spec`'s note on a second LSM says.  A write before
any read is declined: there is no recorded hard limit to compare
against.

THE POINTER, in the three bands every buffer in this tree is judged in.
`access_ok` refusing the sixteen bytes is -EFAULT with nothing moved —
`__access_ok` (include/asm-generic/access_ok.h:31-41, Linux v6.18.46,
the test at :40) is the gate `_inline_copy_from_user` asks at :168 and
`_inline_copy_to_user` (include/linux/uaccess.h:189-200, Linux v6.18.46)
at :195 — and `State.access_okb` is that test; a range `access_ok` admits
that is not wholly mapped is declined, for `old_rlim` because the copy-out
may be partial and for `new_rlim` because which bytes were read is not
something the ledger can state.  The spec asks the WALK first and the
range test only when the walk fails, the order
bugs/read-bytes-map-wraps-while-access-ok-over-sums-in-z.md records
against both arms; `uname_spec` below is written the other way round. -/
def prlimit64_spec (pid resource new_rlim old_rlim : word) : Sys SyscallEffect :=
  if !(w_is0 pid) then unmodeled                -- (1) no other task exists
  else if !(bv_unsigned resource == RLIMIT_CORE) then unmodeled  -- (2)
  else if w_is0 new_rlim && w_is0 old_rlim then unmodeled        -- (4)
  else if !(w_is0 new_rlim) && !(w_is0 old_rlim) then unmodeled  -- (4)
  else
  i <- input ;;
  m <- get_model ;;
  if w_is0 new_rlim then
    -- (5) the READ
    (match read_bytes_map i.in_wmem old_rlim (Z_to_bv 64 16) with
     | none =>
         if !(access_okb old_rlim 16) then err_ret EFAULT
         else unmodeled
     | some _ =>
         match m_rlimit_core m with
         | some bs => Monad.pure (mkEffect (Z_to_bv 64 0) [(old_rlim, bs)] [])
         | none =>
             bs <- choose (fun bs : List byte => rlim64_wf bs = true) ;;
             set_rlimit_core bs ;;
             Monad.pure (mkEffect (Z_to_bv 64 0) [(old_rlim, bs)] []))
  else
    -- (6) the WRITE
    (match m_rlimit_core m with
     | none => unmodeled          -- no recorded hard limit to compare against
     | some bs0 =>
         match read_bytes_map i.in_mem new_rlim (Z_to_bv 64 16) with
         | none =>
             if !(access_okb new_rlim 16) then err_ret EFAULT
             else unmodeled
         | some nb =>
             record_copyins [(new_rlim, 16)]
             (if bv_unsigned (rlim64_hard nb) < bv_unsigned (rlim64_soft nb)
              then err_ret EINVAL
              else if !(bv_eqb (rlim64_hard nb) (rlim64_hard bs0)) then unmodeled
              else set_rlimit_core nb ;; ret_only (Z_to_bv 64 0)))

/-! ## Credentials — the eight id calls

Every id these syscalls can INSTALL is one a real process could hold:
`Syscall.uid32` puts every argument below `2^32`, and the single 32-bit
value no process can hold, `(uid_t)-1`, is never written — `setid_spec`
rejects it with -EINVAL before it reaches `set_creds`, and `setresid_spec`
reads it as "leave this id alone".  The argument is on the Rocq file's
credentials preamble.

Three premises of that preamble make these specs exact, and each is a
condition on the KERNEL, not on the program.  THE INIT USER NAMESPACE:
`make_kuid` is then the identity on the value and the only invalid 32-bit
id is `(uid_t)-1` (`make_kuid`, kernel/user_namespace.c; `INVALID_UID`,
include/linux/uidgid.h, Linux v6.18.46), which is what makes `setresid_spec`'s
-EINVAL unreachable.  NO LSM ON `task_fix_setuid` BEYOND THE CAPABILITY
ONE: `cap_task_fix_setuid` (security/commoncap.c:1149-1186, Linux v6.18.46) returns 0
for every flag these calls pass, but SafeSetID's hook of the same name
(`safesetid_task_fix_setuid`, security/safesetid/lsm.c:191-213, Linux v6.18.46) kills a
caller that crosses a configured uid boundary with SIGKILL and answers
-EACCES, an errno no arm here admits — a kernel with that policy loaded
is outside the model.  And `State.creds_privileged`, whose docstring names
the conditions — default securebits among them — under which the
effective uid stands in for `CAP_SETUID` and `CAP_SETGID`. -/

/-- The three user ids, or the three group ids, of one `State.Creds` —
real, effective, saved.  `setuid`/`setgid` and `setresuid`/`setresgid`
are pairs of syscalls whose rules are identical once you say which triple
they act on, so the specs below are written once over this view and
applied twice.  What genuinely differs between the pair is one argument:
the user setters can fail with -EAGAIN and the group setters cannot (see
`setid_errnos`). -/
structure IdTriple where
  mkIdTriple ::
  id_real  : word
  id_eff   : word
  id_saved : word

/-- The uid triple of a credential record. -/
def cred_uids (c : Creds) : IdTriple :=
  IdTriple.mkIdTriple c.cr_uid c.cr_euid c.cr_suid
/-- The gid triple of a credential record. -/
def cred_gids (c : Creds) : IdTriple :=
  IdTriple.mkIdTriple c.cr_gid c.cr_egid c.cr_sgid

/-- Both setters CARRY THE SUPPLEMENTARY GROUP LIST OVER UNCHANGED, and
that is a kernel fact rather than a convenience: `__sys_setuid`
(kernel/sys.c:651-696, Linux v6.18.46, commit 1f99e9ab748f), `__sys_setgid`
(kernel/sys.c:479-513), `__sys_setresuid` (kernel/sys.c:708-781) and
`__sys_setresgid` (kernel/sys.c:810-870) each build the new credentials
with `prepare_creds`, which `memcpy`s the old
`struct cred` and takes another reference on the SAME supplementary
group list — `prepare_creds` (kernel/cred.c:206-250, at :219 and :223, Linux v6.18.46) — and then write only the id
fields.  Nothing on those four paths calls `set_groups`.  A setter that
dropped the list here would make a later `getgroups` (158) report 0 where
Linux reports the inherited count. -/
def set_cred_uids (t : IdTriple) (c : Creds) : Creds :=
  Creds.mkCreds t.id_real t.id_eff t.id_saved c.cr_gid c.cr_egid c.cr_sgid c.cr_groups
/-- The gid half of `set_cred_uids`: the three group ids replaced, the
user ids and the supplementary list carried over. -/
def set_cred_gids (t : IdTriple) (c : Creds) : Creds :=
  Creds.mkCreds c.cr_uid c.cr_euid c.cr_suid t.id_real t.id_eff t.id_saved c.cr_groups

/-- `getuid` (174), `geteuid` (175), `getgid` (176), `getegid` (177):
return one id.  TOTAL — no argument is read, no allocation happens, no
check can fail, and the value is a value even when it is large:
`SYSCALL_DEFINE0(getuid)` and its three siblings (kernel/sys.c:1027-1049,
Linux v6.18.46, commit 1f99e9ab748f) each return `from_kuid_munged` /
`from_kgid_munged` of one field of `current_cred()`, and those answer an
unmappable id with the overflow id — the `fs.overflowuid` and
`fs.overflowgid` sysctls (kernel/sys.c:167-203, Linux v6.18.46), 65534 by default
(`DEFAULT_OVERFLOWUID`, include/linux/highuid.h:41) — never with an errno
(`from_kuid_munged`, kernel/user_namespace.c:466-474, and
`from_kgid_munged`, :533-541, Linux v6.18.46).  In the init user namespace the mapping is the identity
— `init_user_ns.uid_map` and `.gid_map` are one extent from 0 to 0 of
count 4294967295 (kernel/user.c:38-56, Linux v6.18.46) — so the model returns the stored
id unchanged, and `Run.valid_id`'s 32-bit bound keeps it clear of the
`State.addr_is_error_b` error band.

The ANSWER is the run's, not a constant: `State.ProcInput` carries the
launching uid and gid, so a program is analysed under every user it could
have been launched as.  A constant would REJECT the truthful answer of any
kernel not running the process as root.

`getppid` (173) is deliberately absent and stays `unmodeled` via the
dispatcher's fallback: the model is single-process, and the parent's pid
genuinely CHANGES under the kernel at a moment the model cannot predict
(`find_new_reaper`, kernel/exit.c, Linux v6.18.46), so no recorded choice is faithful.
The argument in full is on the Rocq definition `Kernel.Sys.getid_spec`. -/
def getid_spec (sel : Creds → word) : Sys SyscallEffect :=
  m <- get_model ;;
  ret_only (sel (m_creds m))

/-- The environment failures the id setters can suffer, as opposed to the
answers their arguments and credentials determine.

-ENOMEM: `prepare_creds` allocates the new credential record and returns
NULL when it cannot (kernel/cred.c:206-250, at :212-214 and :238-249,
Linux v6.18.46, commit 1f99e9ab748f); every one of the four id setters
answers that NULL with -ENOMEM (`__sys_setuid` kernel/sys.c:663-665,
`__sys_setgid` :491-493, `__sys_setresuid` :749-751, `__sys_setresgid`
:849-851).

-EAGAIN: `set_user` (kernel/sys.c:523-534, Linux v6.18.46) swaps in the per-uid
`struct user_struct` through `alloc_uid` (kernel/user.c:204-244, Linux v6.18.46) and
answers its NULL with -EAGAIN (:527-529), and `set_cred_ucounts`
(kernel/cred.c:533-550, Linux v6.18.46) swaps in the per-uid `struct ucounts` through
`alloc_ucounts` (kernel/ucount.c:157-186, Linux v6.18.46) and answers ITS NULL with
-EAGAIN (:544-545).  `set_user` is CALLED only when the call changes the
real uid (`__sys_setuid` :671-672, `__sys_setresuid` :755-756);
`set_cred_ucounts` is called unconditionally (:686, :771) but returns 0
through a fast path unless `new->uid` differs from the ucounts already
held (kernel/cred.c:541-542, Linux v6.18.46), so it too can allocate, and therefore fail,
only then.  Neither exists on the group side: `__sys_setgid` and
`__sys_setresgid` call neither.  So the flag: -EAGAIN is admissible
exactly on a user-id setter that moves the real uid, and admitting it
more widely would let a target answer -EAGAIN to a call no kernel can
fail.

NOT an -EAGAIN source: `RLIMIT_NPROC`.  `flag_nproc_exceeded`
(kernel/sys.c:536-553, Linux v6.18.46) returns `void`, sets or clears
`PF_NPROC_EXCEEDED` and nothing else, and so defers enforcement to the
next `execve`; the limit is invisible to every syscall modeled here.  The
Rocq comment's "contrary to the pre-v5.17 shape" is about WHERE the test
sat — inline in `set_user`, until v5.17 moved it and the comment above it
into this helper — and is Rocq's reading; the comment itself, "We don't
fail in case of NPROC limit excess here", says the deferral is older than
the move, so no kernel this model supports fails a setter on it. -/
def setid_errnos (real_uid_changes : Bool) : List Int :=
  if real_uid_changes then [ENOMEM, EAGAIN] else [ENOMEM]

/-- `setuid uid` (146) and `setgid gid` (144), one spec over `IdTriple`;
`user` says which of the two, and reaches only `setid_errnos`.
`SYSCALL_DEFINE1(setuid)` (kernel/sys.c:698-701, Linux v6.18.46, commit
1f99e9ab748f) is `return __sys_setuid(uid);` and `SYSCALL_DEFINE1(setgid)`
(:515-518) is `return __sys_setgid(gid);`.

In kernel order (`__sys_setuid`, kernel/sys.c:651-696; `__sys_setgid`,
:479-513, the same shape line for line with the group helpers):

- `(uid_t)-1` is rejected -EINVAL before anything is allocated:
  `make_kuid` maps it to an id `uid_valid` refuses (:659-661;
  `uid_valid`, include/linux/uidgid.h:103-106, Linux v6.18.46), so that call can never
  answer -ENOMEM.
- `prepare_creds` runs NEXT (:663-665), before the capability test — so a
  call that would be refused -EPERM may instead answer -ENOMEM.  That
  ordering is the opposite of `setresuid`'s, which tests permission
  first; it is not a detail, it is observable.
- PRIVILEGED (`ns_capable_setid(old->user_ns, CAP_SETUID)`, :669;
  kernel/capability.c:398-401, Linux v6.18.46, which the model reads as
  `State.creds_privileged`): real, effective and saved all become the
  argument (:670 and :680), and `set_user` runs when the real uid moves
  (:671-674).  This is the transition that drops root for good — it takes
  all three ids away from 0, so `cap_emulate_setxuid`
  (security/commoncap.c:1110-1136, Linux v6.18.46) clears `cap_permitted` — under
  the default securebits `State.creds_privileged` assumes: `cap_task_fix_setuid`
  runs it only while `SECURE_NO_SETUID_FIXUP` is clear (:1157-1158), and
  the clear itself waits on `SECURE_KEEP_CAPS` being clear (:1120) — and
  no later call can come back.  It is also why a privilege-drop sequence
  must set the GROUP ids first.
- UNPRIVILEGED: the argument must already be the real or the saved id
  (:676-677), and only the effective id moves (:680).  Anything else is
  -EPERM (:668, :677).

The kernel also assigns `fsuid`/`fsgid` alongside the effective id on
every branch (:680, :498, :500).  The model does not carry them: they
differ from the effective ids only through `setfsuid`/`setfsgid`, which
are unmodeled, and nothing the model can observe consults them.

The state change is ATOMIC, as the kernel's is: it builds a whole new
`struct cred` and either commits it (:691, :508) or aborts it, so no
failing call leaves half its effect behind.  Here every failing branch
returns without reaching `set_creds`. -/
def setid_spec (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) : Sys SyscallEffect :=
  m <- get_model ;;
  let c := m_creds m
  let t := get c
  if bv_eqb v ID_MINUS_ONE then err_ret EINVAL
  else if creds_privileged c then
    alt (e <- errno_from (setid_errnos (user && !(bv_eqb v t.id_real))) ;; err_ret e)
        (set_creds (put (IdTriple.mkIdTriple v v v) c) ;; ret_only (Z_to_bv 64 0))
  else if bv_eqb v t.id_real || bv_eqb v t.id_saved then
    alt (e <- errno_from (setid_errnos false) ;; err_ret e)
        (set_creds (put (IdTriple.mkIdTriple t.id_real v t.id_saved) c) ;; ret_only (Z_to_bv 64 0))
  else
    alt (e <- errno_from (setid_errnos false) ;; err_ret e) (err_ret EPERM)

/-- `setresuid ruid euid suid` (147) and `setresgid` (149), again one
spec over `IdTriple`.  `SYSCALL_DEFINE3(setresuid)` (kernel/sys.c:783-786,
Linux v6.18.46, commit 1f99e9ab748f) is `return __sys_setresuid(ruid,
euid, suid);` and `SYSCALL_DEFINE3(setresgid)` (:872-875) the group twin;
neither has a `flags` parameter.

-EINVAL IS UNREACHABLE.  `__sys_setresuid` (kernel/sys.c:708-781) tests
`(ruid != (uid_t) -1) && !uid_valid(kruid)` for each of the three
(:721-728), and in the init user namespace the second conjunct is exactly
`ruid == (uid_t) -1` — the mapping is the identity there and only
`(uid_t) -1` is invalid (`make_kuid`, kernel/user_namespace.c:422-426, Linux v6.18.46;
`uid_valid`, include/linux/uidgid.h:103-106) — the negation of the first.  So the model
omits the arm rather than writing an arm nothing can reach.

The rest, in kernel order:

- `(uid_t)-1` in any position means LEAVE THAT ID ALONE.  It is read as
  the raw argument (:732-736, :753, :761, :763), before and independently
  of any validity question, which is why the same bit pattern is a
  rejected VALUE for `setuid` and a no-op REQUEST here.
- The NO-OP fast path returns 0 (:732-737) before `prepare_creds`, so a
  call that asks for nothing is total: it can answer neither -ENOMEM nor
  -EAGAIN.  The kernel's condition on the effective id is `keuid ==
  old->euid && keuid == old->fsuid`; the model's `fsuid` always equals its
  `euid` (`setid_spec`'s note), so the second conjunct is implied and the
  model tests the first.
- PERMISSION: each id the call would install must ALREADY be one of the
  three current ids — real, effective or saved — in any position
  (:739-744).  If any is new, the caller must be privileged, else -EPERM
  (:745-747).  This test runs BEFORE `prepare_creds` (:749-751), so
  unlike `setuid` a refused call here never answers -ENOMEM.  That
  ordering is why the two specs differ: commit 659c0ce1cb9e
  ("kernel/sys.c: fix and improve control flow in __sys_setres[ug]id()",
  v6.3) hoisted the capability check above `prepare_creds` here, and
  left `__sys_setuid` alone.
- Otherwise every named id is installed (:753-765), `set_user` running
  when the real uid moves (:755-758).  Unlike `setuid`, the saved id is
  NEVER touched implicitly: it changes if and only if the third argument
  names it.  That is what makes `setresgid(-1, -1, g)` — dropbear's way
  of parking the utmp group in the saved gid, to be picked up later with
  `setegid` — do exactly that and nothing else.
- `seteuid`/`setegid` are not syscalls: musl compiles them to
  `setresuid(-1, e, -1)` and `setresgid(-1, e, -1)` (musl 1.2.5,
  src/unistd/seteuid.c, src/unistd/setegid.c), so they are modeled here
  and nowhere else.

`__sys_setresgid` (kernel/sys.c:810-870, Linux v6.18.46) is the same shape with the group
helpers (:823-828, :832-837, :839-847, :849-851, :853-859) and, having no
`set_user`, no -EAGAIN. -/
def setresid_spec (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) : Sys SyscallEffect :=
  m <- get_model ;;
  let c := m_creds m
  let t := get c
  let pick (a cur : word) : word := if bv_eqb a ID_MINUS_ONE then cur else a
  let nr := pick r t.id_real
  let ne := pick e t.id_eff
  let ns := pick s t.id_saved
  if bv_eqb nr t.id_real && bv_eqb ne t.id_eff && bv_eqb ns t.id_saved then
    ret_only (Z_to_bv 64 0)                    -- no-op: 0, before any allocation
  else
    let is_old (x : word) : Bool :=
      bv_eqb x t.id_real || bv_eqb x t.id_eff || bv_eqb x t.id_saved
    if !(is_old nr && is_old ne && is_old ns) && !(creds_privileged c) then
      err_ret EPERM                            -- before `prepare_creds` since 659c0ce1cb9e: no -ENOMEM here
    else
      alt (en <- errno_from (setid_errnos (user && !(bv_eqb nr t.id_real))) ;; err_ret en)
          (set_creds (put (IdTriple.mkIdTriple nr ne ns) c) ;; ret_only (Z_to_bv 64 0))

/-! ## uname (160) -/

/-- The six members of `struct new_utsname`
(include/uapi/linux/utsname.h:25-32, Linux v6.18.46, commit
1f99e9ab748f), each `char[__NEW_UTS_LEN + 1]` with `__NEW_UTS_LEN` 64
(:15), as byte ranges of the 390 bytes the syscall copies out.
`uts_field k bs` is member `k`, 65 bytes wide, in declaration order:
0 `sysname`, 1 `nodename`, 2 `release`, 3 `version`, 4 `machine`,
5 `domainname`. -/
def uts_field (k : Nat) (bs : List byte) : List byte := (bs.drop (k * 65)).take 65

/-- The terminator. -/
def uts_nul : byte := Z_to_bv 8 0

/-- A member built from its C string literal: the characters, then NUL to
the full 65 bytes.  That is what a `char field[65]` initialised from a
string literal holds — C zero-fills the remainder — and it is how
`init_uts_ns` sets all six (init/version-timestamp.c:10-26, Linux
v6.18.46, commit 1f99e9ab748f, the six initialisers at :13-20). -/
def uts_literal (cs : List Int) : List byte :=
  cs.map (Z_to_bv 8) ++ List.replicate (65 - cs.length) uts_nul

/-- Byte-list equality: same length, and equal pairwise. -/
def uts_eqb (l1 l2 : List byte) : Bool :=
  (l1.length == l2.length) && (l1.zip l2).all (fun p => bv_eqb p.1 p.2)

/-- `UTS_SYSNAME`, "Linux" (include/linux/uts.h:8-9, Linux v6.18.46,
commit 1f99e9ab748f).  The definition is guarded by `#ifndef` and no
riscv header overrides it, so a riscv64 build has this string; nothing
writes `sysname` afterwards — `sethostname` (kernel/sys.c:1419-1443,
Linux v6.18.46) writes `nodename` (:1436-1437) and `setdomainname`
(kernel/sys.c:1473-1497, Linux v6.18.46) writes `domainname`
(:1490-1491), and kernel/sys.c defines no setter for any other member. -/
def uts_sysname_chars : List Int := [76, 105, 110, 117, 120]

/-- `UTS_MACHINE`, "riscv64": `UTS_MACHINE := riscv64` on the 64-bit
branch of arch/riscv/Makefile (arch/riscv/Makefile:31, Linux v6.18.46,
commit 1f99e9ab748f; the 32-bit branch at :42 says riscv32).

`override_architecture` IS COMPILED IN ON THIS ARCHITECTURE and does not
fire for the process this model describes.  riscv defines
`COMPAT_UTS_MACHINE` as "riscv32\0\0" (arch/riscv/include/asm/compat.h:5,
Linux v6.18.46), so kernel/sys.c takes the `#ifdef COMPAT_UTS_MACHINE`
arm of `override_architecture` (kernel/sys.c:1310-1317, Linux v6.18.46)
and `SYSCALL_DEFINE1(newuname)` (kernel/sys.c:1351-1366, Linux v6.18.46)
rewrites `machine` at :1363-1364 whenever the caller's personality is
PER_LINUX32 (include/uapi/linux/personality.h:56, Linux v6.18.46).  This
model runs an rv64 ELF started by an ordinary `execve`, whose
`SET_PERSONALITY` (arch/riscv/include/asm/elf.h:137-142, Linux v6.18.46)
sets PER_LINUX unless the inherited personality is already PER_LINUX32
(:139-141, under the `CONFIG_COMPAT` guard at :135; without it the generic
macro, include/linux/elf.h:15-18, Linux v6.18.46, sets PER_LINUX
unconditionally) — so only a personality a parent set before the `execve`
could survive it — and that is a PREMISE about the launcher, not a fact
about the image: an rv64 ELF exec'd from a PER_LINUX32 parent keeps that
personality and is told "riscv32".  So the `machine` conjunct of
`utsname_wf` holds for a process whose launcher runs PER_LINUX, as the
harness's does, and the modeled process cannot disturb its own, since
`personality` (92) has no arm. -/
def uts_machine_chars : List Int := [114, 105, 115, 99, 118, 54, 52]

/-- THE ENVELOPE OF UTS NAMES v6.18.46 CAN COPY OUT, as a predicate on the
390 bytes.  Everything the KERNEL SOURCE settles is pinned; everything
the BUILD or the boot settles is left free, and the free members carry
the one invariant the kernel does maintain.  The argument in full is on
the Rocq definition `Kernel.Sys.utsname_wf`; what follows is the line
each conjunct rests on, re-read at Linux v6.18.46 (commit 1f99e9ab748f).

PINNED: `sysname` and `machine`, each exactly its literal zero-filled to
65 bytes, for the reasons above their character lists.

FREE, WITH A TERMINATOR: `nodename`, `release`, `version` and
`domainname`.  Their values are not in the kernel tree — `UTS_RELEASE`
and `UTS_VERSION` come from include/generated/, and `UTS_NODENAME` is
`CONFIG_DEFAULT_HOSTNAME`, which the `hostname=` boot parameter and
`sethostname` then overwrite — so pinning any would be a claim about a
build rather than about Linux.  What IS true of all four is that BYTE 64
OF EACH IS NUL, which is what makes each a C string of at most 64
characters:

- the four are zero-filled by `init_uts_ns`'s initialiser
  (init/version-timestamp.c:13-20, Linux v6.18.46) — which for `release`
  and `version` is a string literal the BUILD bounds: the top-level
  Makefile refuses a KERNELRELEASE longer than 64 characters before it
  defines UTS_RELEASE (Makefile:1340-1346, Linux v6.18.46), and
  init/Makefile cuts UTS_VERSION to 64 bytes (init/Makefile:35-38, Linux
  v6.18.46), so each literal leaves its member's byte 64 to the zero
  fill;
- `early_hostname` (init/version.c:20-32, Linux v6.18.46) copies the
  boot parameter with `strscpy` into the whole 65-byte buffer (:26),
  which terminates;
- `sethostname` (kernel/sys.c:1419-1443, Linux v6.18.46) refuses a `len`
  above `__NEW_UTS_LEN` (:1427-1428) and then zeroes the member from
  `len` to its end (:1437), so at least its last byte is cleared;
  `setdomainname` (kernel/sys.c:1473-1497, Linux v6.18.46) is the same
  shape (:1480-1481, :1491);
- `override_release` (kernel/sys.c:1325-1349, Linux v6.18.46), the
  UNAME26 personality rewrite (include/uapi/linux/personality.h:12, Linux
  v6.18.46), writes `copy + 1` ≤ 65 bytes (:1346) out of a
  `char buf[65] = { 0 }` (:1331) filled by `scnprintf` under a `copy`
  clamped to 65 (:1344-1345), which never writes past index 64.

NOTHING STRONGER IS CLAIMED ABOUT THE FREE MEMBERS, and both weakenings
are real rather than defensive: `sethostname` copies `len` bytes VERBATIM
(:1436), embedded NULs included, so a member may hold bytes after its
terminator that a zero-filled member would not; and `override_release`
writes only a PREFIX over the existing `release` (:1346), so under
UNAME26 the tail of the previous release survives past the new
terminator.  A "NUL-padded" predicate would reject a real kernel's answer
on that path, which is the mistake this one is written to avoid. -/
def utsname_wf (bs : List byte) : Bool :=
  (bs.length == 390)
  && uts_eqb (uts_field 0 bs) (uts_literal uts_sysname_chars)
  && uts_eqb (uts_field 4 bs) (uts_literal uts_machine_chars)
  && bv_eqb ((uts_field 1 bs).getD 64 uts_nul) uts_nul
  && bv_eqb ((uts_field 2 bs).getD 64 uts_nul) uts_nul
  && bv_eqb ((uts_field 3 bs).getD 64 uts_nul) uts_nul
  && bv_eqb ((uts_field 5 bs).getD 64 uts_nul) uts_nul

/-- `uname name` — syscall 160, which riscv64 routes to sys_newuname
(`__NR_uname`, include/uapi/asm-generic/unistd.h:428-429, Linux v6.18.46,
commit 1f99e9ab748f).  THE WHOLE KERNEL FUNCTION is
`SYSCALL_DEFINE1(newuname)` (kernel/sys.c:1351-1366, Linux v6.18.46): a
`memcpy` of the current namespace's `utsname()` under `uts_sem`
(:1355-1357), `copy_to_user` of the 390 bytes answering -EFAULT
(:1358-1359), then `override_release` (:1361-1362) and
`override_architecture` (:1363-1364), neither of which fires for the
process this model describes (`uts_machine_chars` above says why for the
second; the first is the UNAME26 personality, outside the modeled
surface by the same argument), and 0 (:1365).  There is no argument to
validate, no flag word and no errno but -EFAULT, so the envelope is a
question about the pointer and about WHICH utsname, and nothing else.
The argument in full is on the Rocq definition `Kernel.Sys.uname_spec`.

THE POINTER, in the three bands every buffer in this tree is judged in:

- `access_ok` REFUSES the 390-byte range: -EFAULT, exact, with nothing
  moved.  `_inline_copy_to_user` (include/linux/uaccess.h:189-200, Linux
  v6.18.46) copies only under `access_ok` (:195) and otherwise returns
  the untouched count (:199), which `SYSCALL_DEFINE1(newuname)` turns
  into -EFAULT (kernel/sys.c:1358-1359); the test is `__access_ok`
  (include/asm-generic/access_ok.h:31-41, Linux v6.18.46), `addr <=
  limit - size` at :40, and `State.access_okb` is that test.
  IT IS ASKED FIRST, BEFORE THE WALK, and the order is load-bearing:
  `State.read_bytes_map` advances with WRAPPING word arithmetic while
  `State.access_okb` subtracts in `Int`, so a `name` near 2^64 whose 390
  bytes wrap round onto mapped low addresses reads as "wholly writable"
  to the walk and is refused by Linux.  Asking the walk first is the
  defect bugs/read-bytes-map-wraps-while-access-ok-over-sums-in-z.md
  records against both `prlimit64_spec` arms; this arm is written the
  repaired way, and `Checks/Cases/Kernel/Sys.lean`'s `uname_wrap_` group
  pins both directions.
- `access_ok` admits the range and it is WHOLLY WRITABLE: the modeled
  path.  390 bytes land at `name` and the call returns 0.
- `access_ok` admits it and it is NOT wholly writable: declined.  The
  riscv copy routine commits a prefix and then answers bytes-not-copied,
  so a struct straddling into an unmapped page is half written and then
  -EFAULT — the shape `Time.gettimeofday_spec` declines and cites down to
  arch/riscv/lib/uaccess.S — and here the prefix may end anywhere in 390
  bytes rather than at one of two fields.

WHICH UTSNAME: the environment's, recorded once.  On the first `uname`
of a run the model CHOOSES any buffer `utsname_wf` admits and pins it in
`State.m_utsname`; every later `uname` must deliver exactly those bytes,
because two calls that disagreed about the running kernel would be a
trace no Linux machine produces.  A program that branches on the content
of a free member is answered nondeterministically, and its equivalence
has to hold for every admissible answer. -/
def uname_spec (name : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if !(access_okb name NEW_UTSNAME_SIZE) then err_ret EFAULT
  else
    (match read_bytes_map i.in_wmem name (Z_to_bv 64 NEW_UTSNAME_SIZE) with
     | none => unmodeled       -- a partial `copy_to_user` then -EFAULT
     | some _ =>
         match m_utsname m with
         | some bs => Monad.pure (mkEffect (Z_to_bv 64 0) [(name, bs)] [])
         | none =>
             bs <- choose (fun bs : List byte => utsname_wf bs = true) ;;
             set_utsname bs ;;
             Monad.pure (mkEffect (Z_to_bv 64 0) [(name, bs)] []))

/-! ## prctl (167) -/

/-- THE OPTIONS THIS MODEL ANSWERS, as a closed list rather than as the
shape of a `match`.  `prctl` is a multiplexer, so the modeled surface
stops being a set of syscall NUMBERS the moment it gains an arm: what is
modeled is a set of (number, option) pairs, and no register of numbers
can say which.  This list is where that set is written down, so that
widening the multiplexer is a change a pin reports rather than one a
reader has to notice; the obligation the pin carries is on the Rocq
definition `Kernel.Sys.prctl_modeled_options`. -/
def prctl_modeled_options : List Int := [PR_CAPBSET_READ]

/-- `prctl(option, arg2, arg3, arg4, arg5)` — syscall 167 (`__NR_prctl`,
include/uapi/asm-generic/unistd.h:447-448, Linux v6.18.46, commit
1f99e9ab748f), answered for `PR_CAPBSET_READ`
(include/uapi/linux/prctl.h:71, Linux v6.18.46) and for nothing else.
The argument in full — why the answer is the LSM hook's and not
kernel/sys.c's, why 1 is THE answer rather than one of several, and what
declining every other option costs — is on the Rocq definition
`Kernel.Sys.prctl_spec`; what follows is the line each step rests on,
re-read at Linux v6.18.46.

WHERE THE ANSWER COMES FROM.  `SYSCALL_DEFINE5(prctl)`
(kernel/sys.c:2518-2877, Linux v6.18.46) opens by calling
`security_task_prctl` and returning its answer unless that is -ENOSYS
(:2525-2527), so the LSM hook runs BEFORE the syscall's own `switch`.
`security_task_prctl` (security/security.c:3871-3887, Linux v6.18.46)
walks every registered hook, keeps the first answer that is not the
-ENOSYS default (:3880-3881) and stops at the first nonzero one
(:3882-3883); the default is the `LSM_HOOK` line for `task_prctl`
(include/linux/lsm_hook_defs.h:263, Linux v6.18.46).  Capability's hook
is `cap_task_prctl` (security/commoncap.c:1291-1431, Linux v6.18.46),
whose first arm is `PR_CAPBSET_READ`: -EINVAL unless `cap_valid(arg2)`,
else `!!cap_raised(old->cap_bset, arg2)` with `old = current_cred()`
(:1298-1301).  It is registered by `LSM_HOOK_INIT(task_prctl,
cap_task_prctl)` (security/commoncap.c:1493, Linux v6.18.46) in the hook
table that `capability_init` (security/commoncap.c:1500-1505, Linux
v6.18.46) adds under `DEFINE_LSM(capability)` at `LSM_ORDER_FIRST`
(:1507-1511) — commoncap is the implementation of capabilities, not an
LSM a build may leave out — so this arm always runs and its 1 or its
-EINVAL is nonzero and ends the walk.  A kernel running a second LSM
that also claims this option is outside the model, as one whose AppArmor
refuses an unchanged rlimit is (`prlimit64_spec`).

ORDER IS BEHAVIOR, and this one has exactly two steps: `cap_valid(arg2)`
and nothing else before the bounding-set read; `arg3`, `arg4` and `arg5`
are not read on this arm at all (:1298-1301), so a caller that leaves
garbage in a2..a4 gets the same answer and this spec takes only the two
registers the kernel reads.

`cap_valid` IS AN UNSIGNED TEST ON THE FULL REGISTER.  It is
`((x) >= 0 && (x) <= CAP_LAST_CAP)` (include/uapi/linux/capability.h:425,
Linux v6.18.46) applied to an `unsigned long arg2`, so the left half is
vacuous and the right is a 64-bit unsigned comparison: `prctl
(PR_CAPBSET_READ, 2^32)` is -EINVAL, not the answer for capability 0.
That is the OPPOSITE of the `option` beside it, an `int` in the
`SYSCALL_DEFINE5` prototype that reaches the kernel already narrowed:
riscv's `__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:82-97,
Linux v6.18.46) applies `__SC_CAST` to each unpacked register (:88), and
`__SC_CAST` is `(__force t) a` (include/linux/syscalls.h:132, Linux
v6.18.46).  The table applies `Syscall.int32` to `option` in the arm, so
`prctl(2^32 | PR_CAPBSET_READ, 0)` answers 1 while
`prctl(PR_CAPBSET_READ, 2^32)` answers -EINVAL;
testing/syscall-check/tests/prctl_spec.c pins both against the kernel.
THE FIRST IS LINUX'S ANSWER ALONE: QEMU's user-mode emulation switches
`do_prctl` on the whole 64-bit `abi_long` and answers -EINVAL to it, so
at that shape the arm admits an answer outside the supported
intersection — bugs/prctl-capbset-read-arm-admits-linux-alone.md.

WHY 1 AND NOT A CHOICE.  `cap_raised` (include/linux/capability.h:75,
Linux v6.18.46) reads one bit of the caller's bounding set, which this
model does not carry and does not have to: it already ASSUMES an
unnarrowed bounding set, on `State.creds_privileged`, because
`handle_privileged_root` (security/commoncap.c:818-850, Linux v6.18.46)
grants legacy root `cap_combine(old->cap_bset, old->cap_inheritable)`
(:842-843), so an ancestor's `PR_CAPBSET_DROP` (include/uapi/linux/prctl.h:72,
Linux v6.18.46) of `CAP_SETUID` would break the biconditional `setid_spec`
rests on.  Under that standing assumption every valid capability is
raised and 1 is the answer; an `alt` or a first-observation `choose`
would let one model assert both "capability 0 is not in the bounding
set" and "a euid-0 caller has CAP_SETUID" in a single run.

THE BOUNDARY IS A VERSION CLAIM IN BOTH DIRECTIONS.  `CAP_LAST_CAP` is
`CAP_CHECKPOINT_RESTORE`, 40 (include/uapi/linux/capability.h:421-423,
Linux v6.18.46), and has been since v5.9; a kernel that defines a 41st
capability answers 1 where this spec answers -EINVAL.  The other
direction is inside the supported set: the same header ends at
CAP_AUDIT_READ, 37, at v4.17 and v5.7 and at CAP_BPF, 39, at v5.8, so a
supported kernel before v5.9 answers -EINVAL to capabilities 38, 39 and
40 where this spec proves 1.  The Rocq text names only the first
direction; bugs/prctl-capbset-read-arm-admits-linux-alone.md records the
second and what both cost.  See `Uapi.CAP_LAST_CAP`.

EVERY OTHER OPTION IS DECLINED, and one is load-bearing:
`PR_SET_TAGGED_ADDR_CTRL` (include/uapi/linux/prctl.h:244, Linux
v6.18.46) reaches riscv's `set_tagged_addr_ctrl`
(arch/riscv/kernel/process.c:285, Linux v6.18.46), and declining it is
half of why `State.access_okb` is exact — the other half being `ptrace`
(117), which has no arm.  That argument rests on `prctl_modeled_options`
being a closed list. -/
def prctl_spec (option_ arg2 : word) : Sys SyscallEffect :=
  if !(bv_unsigned option_ == PR_CAPBSET_READ) then unmodeled
  else if CAP_LAST_CAP < bv_unsigned arg2 then err_ret EINVAL
  else ret_only (Z_to_bv 64 1)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sys
