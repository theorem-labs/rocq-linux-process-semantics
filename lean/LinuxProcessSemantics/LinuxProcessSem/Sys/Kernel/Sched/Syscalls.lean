-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Sys/Kernel/Sched/Syscalls.v

import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi


-- The `rocq-baseline` below is the upstream port's own; this file's source
-- of truth is the `Ports` line at the top.
/-! rocq-baseline: 6e7c0d18ddbaa2d453318f0af4665958350a1871 -/

/-! # LinuxProcessSem.Sys.Kernel.Sched.Syscalls — sched_setscheduler (119), sched_getaffinity (123), sched_yield (124)

Mirrors `theories/LinuxProcessSem/Sys/Kernel/Sched/Syscalls.v`.  The
baseline is the day-branch commit whose whole Rocq closure the Lean tree
mirrors.  It moved from a71fd38a to 6e7c0d18d with the `sched_yield` arm
below, and the move accepts exactly that one definition: against a71fd38a
the whole 64-definition closure drifted in one place,
`Sys/Kernel/Sched/Syscalls.v:sched_yield_spec`, which is the definition
this file gained.  (The older note is still the reason a71fd38a was the
baseline rather than f44244ad6b80, the commit the ticket named: `State.v`'s
`FdEntry` and `IoState` gained the /dev/urandom arms in between, and the
two Rocq Sched files are byte-identical across it.)  This file
answers to Linux `kernel/sched/syscalls.c`: it holds what the kernel
defines there, and nothing else.  The scheduler syscalls moved out of
`kernel/sched/core.c` into that file at v6.11; the Rocq header records
which functions were compared across the move, and this file makes no
cross-version claim of its own — every line cited here was read at Linux
v6.18.46 (commit 1f99e9ab748f).

TRUST BOUNDARY: this file is part of the trusted specification.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function and the line
numbers at v6.18.46 — and point at the Rocq definition for the argument in
full, so there is one place to correct it.

Three spellings differ from Rocq without changing a value.  The `Z.eqb`,
`Z.ltb` and `Z.modulo` tests on `Int` are Lean's decidable `=` — spelled
`==`, `decide (… = …)`, `≠` or an `if … = …` as the position asks, all the
one `DecidableEq Int` — `<` and `%` (every divisor is a positive literal,
so Euclidean and floor division agree).  The one bit test, `Z.land pol SCHED_RESET_ON_FORK =? 0`, is done
on the `word` with `bv_and` as `Sys/Mm/Mmap.lean` does its flag tests:
`Z_to_bv 64` keeps every bit position below 2^64 of any `Int`, and the
constant is one such bit, so the two agree on every `Int`, negative
included.  `xorb` is `Bool.xor`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sched.Syscalls

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! ## sched_getaffinity (123)

`SYSCALL_DEFINE3(sched_getaffinity, pid_t, pid, unsigned int, len,
unsigned long __user *, user_mask_ptr)` (kernel/sched/syscalls.c:1329-1355,
Linux v6.18.46, commit 1f99e9ab748f) runs two gates before anything else:

    if ((len * BITS_PER_BYTE) < nr_cpu_ids)  return -EINVAL;   /* :1335-1336 */
    if (len & (sizeof(unsigned long)-1))     return -EINVAL;   /* :1337-1338 */

then `zalloc_cpumask_var` (:1340, -ENOMEM), the `sched_getaffinity` helper
(:1343; -ESRCH at :1308 from `find_process_by_pid`, an LSM's errno from
`security_task_getscheduler`, else 0 with `p->cpus_mask & cpu_active_mask`),
and on 0 a `copy_to_user` of `min(len, cpumask_size())` bytes (:1345-1350)
whose count is the return value.  Neither `pid` nor `user_mask_ptr` is
touched before the gates, which is why the spec takes neither.

Only the machine-independent half is modeled.  Both gates answer -EINVAL,
so a length either refuses is -EINVAL without knowing `nr_cpu_ids`, which
this model has no representation of; a length both gates let through
either succeeds, returning a byte count read off `cpumask_size()`, or is
refused by the first gate on `nr_cpu_ids`, and the model declines it.  The
argument — the `unsigned int` wrap of `len * 8` (`BITS_PER_BYTE`
is the plain `8`, include/linux/bits.h:12, Linux v6.18.46), why
`nr_cpu_ids >= 1` holds on
riscv64, why number 123's compat entry point (`COMPAT_SYSCALL_DEFINE3(sched_getaffinity)`,
kernel/compat.c:144-153, Linux v6.18.46, whose gate is `& 3` where the
native one is `& 7`) is
unreachable for the LP64 images this model loads, and what the decline
costs — is on the Rocq definition `Syscalls.sched_getaffinity_spec`. -/

/-- The two gates of `SYSCALL_DEFINE3(sched_getaffinity)`
(kernel/sched/syscalls.c:1335-1338, Linux v6.18.46), as one predicate over
the `unsigned int` the ABI delivers.  The disjunction's order is not the
kernel's (the size gate is first there) and need not be: both answer
-EINVAL.  `len * BITS_PER_BYTE` is computed in 32 bits, so the product is 0
exactly on the multiples of 2^29 and every one of them is refused since
`nr_cpu_ids >= 1`; a length that is not a multiple of 8 fails the second
gate.  The `abi_low32` is documentation rather than arithmetic — both
tests are unchanged by adding a multiple of 2^32 — as Rocq's
`Syscalls.affinity_len_einval_b` explains. -/
def affinity_len_einval_b (len : word) : Bool :=
  let l := bv_unsigned (abi_low32 len)
  decide ((l * 8) % 2 ^ 32 = 0) || !(decide (l % 8 = 0))

/-- `sched_getaffinity pid len user_mask_ptr` (123): -EINVAL for a length
either gate of `SYSCALL_DEFINE3(sched_getaffinity)`
(kernel/sched/syscalls.c:1335-1338, Linux v6.18.46) refuses, before the pid
or the pointer is looked at; everything else — a success returning
`min(len, cpumask_size())` (:1345-1350) or the first gate's -EINVAL on a
length below `nr_cpu_ids / 8` — declines, since both turn on the machine's
CPU count. -/
def sched_getaffinity_spec (len : word) : Sys SyscallEffect :=
  if affinity_len_einval_b len then err_ret EINVAL else unmodeled

/-! ## sched_setscheduler (119)

The call, in the order Linux makes its decisions, every line at
kernel/sched/syscalls.c, Linux v6.18.46 (commit 1f99e9ab748f):

    SYSCALL_DEFINE3(sched_setscheduler)             (:962-968)
      if (policy < 0) return -EINVAL;                 (:964-965)
    do_sched_setscheduler(pid, policy, param)       (:880-895)
      if (unlikely(!param || pid < 0)) return -EINVAL;   (:885-886)
      if (copy_from_user(&lparam, param, sizeof(struct sched_param)))
        return -EFAULT;                                  (:887-888)
      CLASS(find_get_task, p)(pid); if (!p) return -ESRCH;   (:890-892)
    _sched_setscheduler(p, policy, &lparam, true)   (:766-786)
      attr = { .sched_policy = policy, .sched_priority = param->sched_priority, … }
      if (policy & SCHED_RESET_ON_FORK) { flags |= …; policy &= ~SCHED_RESET_ON_FORK; }  (:779-783)
    __sched_setscheduler(p, &attr, user = true, pi = true)   (:531-764)
      if (!valid_policy(policy))                    return -EINVAL;   (:555-556)
      if (attr->sched_flags & ~(SCHED_FLAG_ALL | SCHED_FLAG_SUGOV)) return -EINVAL;  (:559-560)
      if (attr->sched_priority > MAX_RT_PRIO-1)      return -EINVAL;   (:567-568)
      if ((dl_policy(policy) && !__checkparam_dl(attr)) ||
          (rt_policy(policy) != (attr->sched_priority != 0))) return -EINVAL;  (:569-571)
      user_check_sched_setscheduler(...)            (:574, -EPERM at :525-526)
      security_task_setscheduler(p)                 (:581)
      scx_check_setscheduler(p, policy)             (:620)
      … the state change, return 0                  (:757)

`struct sched_param` is the single `int sched_priority`
(include/linux/sched.h:410-412, Linux v6.18.46), so the copy is four
bytes; the `attr`
field it lands in is a `__u32` (include/uapi/linux/sched/types.h:108), so
a negative `int` meets the `> MAX_RT_PRIO-1` gate as a large unsigned.

The two `sched_flags` gates, :559-560 and the `SCHED_FLAG_SUGOV` test at
:578-579, are absent from the modeled chain on purpose: from this entry
point `attr.sched_flags` is 0 or `SCHED_FLAG_RESET_ON_FORK` (:779-781),
which is inside `SCHED_FLAG_ALL` (include/uapi/linux/sched.h:143-148, Linux
v6.18.46) and is not `SCHED_FLAG_SUGOV`, so neither can fire — and the reset-on-fork word is
declined at the strip in any case.

Linux checks the arguments in the order above, and this file answers in
that order: a negative policy is -EINVAL before the NULL `param` test and
before any read of `param`.
The Rocq definition `Syscalls.sched_setscheduler_spec` explains the later SCHED_IDLE result and its scheduling-state premises.
It also explains the SCHED_EXT, SCHED_DEADLINE, and other-task limits. -/

/-- `valid_policy` (kernel/sched/sched.h:216-220, Linux v6.18.46) minus
SCHED_EXT, which is declined before this test is reached.  Written as a
membership test because the six numbers are not an interval: the header
leaves 4 to an unimplemented SCHED_ISO. -/
def sched_valid_policy_b (pol : Int) : Bool :=
  (pol == SCHED_NORMAL) || (pol == SCHED_FIFO) || (pol == SCHED_RR)
   || (pol == SCHED_BATCH) || (pol == SCHED_IDLE)
   || (pol == SCHED_DEADLINE)

/-- `rt_policy` (kernel/sched/sched.h:206-209, Linux v6.18.46), which is
config-independent. -/
def sched_rt_policy_b (pol : Int) : Bool :=
  (pol == SCHED_FIFO) || (pol == SCHED_RR)

/-- Whether the call names the CALLING task, which is the only task this
model represents.  `find_process_by_pid` (kernel/sched/syscalls.c:253-256,
Linux v6.18.46) is `pid ? find_task_by_vpid(pid) : current`, so a zero pid
always does; a positive one does exactly when it is the pinned tid.  The
pid is read at `pid32` width because it arrives as a `pid_t`, and the zero
test is on those low 32 bits for the same reason — a register whose low
half is zero IS a zero pid to the kernel. -/
def sched_targets_self_b (pid : word) (m : Model) : Bool :=
  w_is0 (pid32 pid)
   || match m_tid m with
      | some tid => bv_eqb (pid32 pid) tid
      | none => false

/-- Everything `__sched_setscheduler` decides once the task is in hand, as
one function of the policy word and the copied-in priority: `some r` is
the value `a0` takes, `none` is the decline.  The order is the kernel's,
and the two declines sit where Linux's decision does rather than at the
front: `SCHED_RESET_ON_FORK` is stripped by `_sched_setscheduler`
(kernel/sched/syscalls.c:779-783, Linux v6.18.46) before `valid_policy`
runs (:555-556), and SCHED_EXT is a `valid_policy` question, so both
precede every -EINVAL below them — the range gate (:567-568), the
DEADLINE gate (:569, always refused from this entry point) and the
RT-agreement gate (:570).  `prio` is the `__u32` the `int sched_priority`
was widened to, so the `> MAX_RT_PRIO-1` test catches a negative `int` as
well as 100 or more, and `prio ≠ 0` is the `attr->sched_priority != 0` the
agreement test compares against. -/
def sched_setscheduler_answer (pol prio : Int) : Option word :=
  if bv_and (Z_to_bv 64 pol) (Z_to_bv 64 SCHED_RESET_ON_FORK) ≠ Z_to_bv 64 0 then none
  else if pol = SCHED_EXT then none
  else if !(sched_valid_policy_b pol) then some (errno_ret EINVAL)
  else if MAX_RT_PRIO - 1 < prio then some (errno_ret EINVAL)
  else if pol = SCHED_DEADLINE then some (errno_ret EINVAL)
  else if Bool.xor (sched_rt_policy_b pol) (!(decide (prio = 0)))
       then some (errno_ret EINVAL)
  else if pol = SCHED_IDLE then some (Z_to_bv 64 0)
  else none

/-- Linux v6.18.46 rejects a negative policy in
`SYSCALL_DEFINE3(sched_setscheduler)` (kernel/sched/syscalls.c:962-968)
before `do_sched_setscheduler` is entered, and `do_sched_setscheduler`
(kernel/sched/syscalls.c:880-888) rejects a NULL `param` and a negative
pid before `copy_from_user`.  Both signed arguments are read at their low
32 bits, because both arrive as 32-bit kernel types.  So the two
pre-copy -EINVALs are answered here in the kernel's order: a negative
policy beats a NULL `param`, a negative pid, and the -EFAULT an
unreadable `param` would raise.

THE ORDER IS THE WHOLE POINT, and it is why this arm answers rather than
declines.  Every decision above `user_check_sched_setscheduler` is a
function of the ARGUMENTS alone, so the two -EINVALs, the -EFAULT and
the four -EINVALs `__sched_setscheduler` raises before it consults the
task are modeled exactly.  The argument in full is on the Rocq
definition `Sched.Syscalls.sched_setscheduler_spec` (f1006fe8,
`Sys/Kernel/Sched/Syscalls.v:213-400`, and the definition itself is at
`:462-487`).

UPSTREAM DECLINES THIS BAND AND THE TWIN DOES NOT.  linux-process-semantics'
Lean tree answers `unmodeled` for a non-NULL negative argument, because
QEMU v11.1.1 reads `param` through `lock_user_struct` before it tests the
signed arguments (linux-user/syscall.c:12091-12104) and so can answer
-EFAULT where Linux answers -EINVAL.  This model describes Linux
v6.18.46 and not the intersection with QEMU user mode
(dispatch://OSSV-266/ask/9128d2b8), so the twin follows the Rocq
definition and answers -EINVAL.

Linux v6.18.46 copies four bytes before the task lookup
(kernel/sched/syscalls.c:887-892) and the twin records each successful
copy on every later path.  A range `access_ok` refuses
(`_inline_copy_from_user`, include/linux/uaccess.h) produces -EFAULT with
no copy-in ledger; a permitted range whose bytes the memory fixture lacks
is declined, because the ledger cannot name the bytes Linux read before a
partial copy failed.  `find_get_task` (kernel/sched/syscalls.c:258-263)
resolves any other task, which this model does not represent, so a pid
that is neither 0 nor the pinned tid declines after the copy.  The
remaining decisions are `sched_setscheduler_answer`'s. -/
def sched_setscheduler_spec (pid policy param : word) : Sys SyscallEffect :=
  if decide (sint32 policy < 0) then err_ret EINVAL
  else if w_is0 param || decide (sint32 pid < 0) then err_ret EINVAL
  else
    i <- input ;;
    m <- get_model ;;
    match read_bytes_map i.in_mem param (Z_to_bv 64 4) with
    | none =>
        if !(access_okb param 4) then err_ret EFAULT else unmodeled
    | some bs =>
        record_copyins [(param, 4)]
          (if !(sched_targets_self_b pid m) then unmodeled
           else
             match sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
                     (bv_unsigned (le_bytes_to_word bs)) with
             | some r => ret_only r
             | none => unmodeled)

/-! ## sched_yield (124) -/

/-- `sched_yield` (124): 0, with nothing this model can see changed.
`SYSCALL_DEFINE0(sched_yield)` is `do_sched_yield(); return 0;`
(kernel/sched/syscalls.c:1382-1386, Linux v6.18.46) and its kernel-doc
says "Return: 0." (:1380).  Everything `do_sched_yield` touches is per-run-queue
scheduler bookkeeping — `rq->yld_count`, the run queue donor's
scheduling class's `yield_task`, the `schedule()` after them (:1357-1372)
— which this model
has no representation of, so no model state moves.  No argument word is
read either: riscv64 overrides `SYSCALL_DEFINE0`
(arch/riscv/include/asm/syscall_wrapper.h:99-103, Linux v6.18.46) with one
taking `const struct pt_regs *__unused`, expanding without
`SC_RISCV_REGS_TO_ARGS`, so none reaches the body.  The Rocq definition
carries the argument in full, including why the time `schedule()` costs
is invisible while the model has one process.  Rocq:
`Sys.Kernel.Sched.Syscalls.sched_yield_spec`.

THE VERSION IS THE PIN, AND NOT ROCQ'S.  The Rocq header pins this arm
"to what was read at v6.12.1" and cites it throughout.  Both functions
above were re-read at the pin linux-process-semantics@ff0313ba4f:AGENTS.md names, v6.18.46 commit
1f99e9ab748f, before these line numbers were written, and each says there
what Rocq says it says; this file's header claims exactly that of every
line it cites, so a v6.12.1 label here would have contradicted it.

Residual infidelity, stated rather than modeled, and shared with every
syscall wrapper — `__SYSCALL_DEFINEx` emits the same line
(arch/riscv/include/asm/syscall_wrapper.h:84, Linux v6.18.46), not the
zero-argument form alone: `SYSCALL_DEFINE0` emits
`ALLOW_ERROR_INJECTION(..., ERRNO)` (the riscv override above,
arch/riscv/include/asm/syscall_wrapper.h:102, Linux v6.18.46), which on a
kernel built with `CONFIG_FUNCTION_ERROR_INJECTION` puts
`__riscv_sys_sched_yield` on the error-injection list
(include/asm-generic/error-injection.h:20-40, Linux v6.18.46).  The list
opens two BPF routes to ANY return word with `do_sched_yield` never
running, and that option alone opens the first: a `BPF_MODIFY_RETURN`
program attaches to any listed address (kernel/bpf/verifier.c:23870-23877,
`check_attach_modify_return`, Linux v6.18.46), its return value is left
unconstrained (kernel/bpf/verifier.c:17558-17559, Linux v6.18.46), and
riscv's trampoline stores that value as the call's and branches past the
original call whenever it is nonzero (arch/riscv/net/bpf_jit_comp64.c:
1151-1189, Linux v6.18.46) — the option's own help says "BPF may also
modify the return value of these functions" (lib/Kconfig.debug:1993-1999,
Linux v6.18.46).  The second route, a kprobe program calling
`bpf_override_return`, needs `CONFIG_BPF_KPROBE_OVERRIDE` besides: the
helper is compiled under its `#ifdef` (kernel/trace/bpf_trace.c:155,
Linux v6.18.46), the option `depends on FUNCTION_ERROR_INJECTION`
(kernel/trace/Kconfig:825-829, Linux v6.18.46), the helper's value
argument is `ARG_ANYTHING` and `regs_set_return_value` writes it to `a0`
whole (kernel/trace/bpf_trace.c:156-168 and
arch/riscv/include/asm/ptrace.h:117-121, Linux v6.18.46).  So the gate on
the class is `CONFIG_FUNCTION_ERROR_INJECTION`, as the Rocq comment and
`Kernel.Sys.getpid_spec`'s note have it; what both understate is the
reach — "an errno", where any word is reachable — and an earlier version
of this paragraph, having found the helper's own option, moved the gate
there and was wrong about the first route.  The `ERRNO` in the annotation
bounds only the debugfs `fail_function` path, a third route on which
`do_sched_yield` never runs: `adjust_error_retval` maps a value outside
`[-MAX_ERRNO, -1]` to `-EINVAL` (kernel/fail_function.c:36-54 and
include/linux/err.h:18, Linux v6.18.46), the default return is that map
of 0 (kernel/fail_function.c:69, Linux v6.18.46), and `fei_retval_set`
refuses a write the map would change, answering `-EINVAL` to the writer
(kernel/fail_function.c:124-128, Linux v6.18.46), so the stored value is
always in the band; it says nothing about what a BPF program may return.
The model describes a kernel with none of the three attached, and EVERY
refusal pinned in `Checks/Cases/Kernel/Sched/Syscalls.lean` — the `¬`
pins' `1`, `-EINTR` and `-EPERM` no less than the right-hand side of each
`iff`, which refuses every word but 0 — rests on this premise rather than
on every kernel answering 0.  No `bugs/` entry is owed: the direction of
failure is the mild one, and
`linux-process-semantics@ff0313ba4f:bugs/clone-errnos-omits-three-environment-failures.md` records that
argument for the whole class. -/
def sched_yield_spec : Sys SyscallEffect :=
  ret_only (Z_to_bv 64 0)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sched.Syscalls
