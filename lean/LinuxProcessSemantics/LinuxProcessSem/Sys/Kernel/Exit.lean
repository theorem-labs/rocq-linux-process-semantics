import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Kernel.Exit — exit (93), exit_group (94), wait4 (260)

Mirrors `theories/LinuxProcessSem/Sys/Kernel/Exit.v`.  This file answers
to Linux `kernel/exit.c`: it holds what the kernel defines there, and
nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
The Rocq file read its kernel side at v6.12 and says so; every line cited
here was re-read at v6.18.46.

One spelling differs from Rocq without changing a value: the
`negb (Z.eqb (bv_unsigned w) c)` gates are Lean's decidable `≠` on `Int`.
The `w_is0` gate is the same Bool test Rocq makes. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- Halt the run.  The observed exit code is the low byte of the status,
as a waiting parent sees it: `SYSCALL_DEFINE1(exit, int, error_code)`
calls `do_exit((error_code&0xff)<<8)` and `exit_group` calls
`do_group_exit((error_code & 0xff) << 8)` (kernel/exit.c:1085-1088 and
:1129-1134, Linux v6.18.46, commit 1f99e9ab748f), so the seven high bytes
are gone before any status exists.  `wait_task_zombie` stores that word
in `wo_stat` (kernel/exit.c:1265-1267, Linux v6.18.46) and `kernel_wait4`'s
`put_user` (:1885) hands it to the parent, who reads the byte back from
bits 8..15.  The model records the BYTE, not the kernel-internal `<< 8`
status word.  The returned effect is never applied (`Run` ends the trace
with an `ExitEv` instead).

`exit_group` differs from `exit` only in taking the whole thread group
down: `do_group_exit` (kernel/exit.c:1094-1122, Linux v6.18.46) substitutes
`sig->group_exit_code` when another thread already set
`SIGNAL_GROUP_EXIT`, and 0 during an exec (`group_exec_task`).  Neither
branch is reachable in this model, and the reason is a premise rather
than the argument alone: `SIGNAL_GROUP_EXIT` is set by another thread's
`do_group_exit` (:1114); as a thread group's last quick thread exits, by
`synchronize_group_exit` (kernel/exit.c:882-885, Linux v6.18.46) — which
a single-threaded exit runs ITSELF from `do_exit` (:919), and which is
harmless on both paths: `exit_group` reaches `do_exit` (:1120) with the
flag already set at :1114, so the write is guarded out (:883), and `exit`
reaches it with the flag clear, so the write fires with `group_exit_code`
equal to the code `do_exit` was given (:885), the word `wait_task_zombie`
reads back either way (:1265-1267); by
`complete_signal` on a fatal signal to ANY process
(kernel/signal.c:1003-1018, Linux v6.18.46); and by `zap_process` when a
core dump starts (fs/coredump.c:486, Linux v6.18.46), which follows a
fatal signal and so rests on the same premise.  The model has no threads
(`Sys/Kernel/Fork.v`, "THE THREAD-CREATING WORDS ARE DECLINED");
`group_exec_task` needs an exec, and `execve` is unmodeled
(`Checks/ProcessCreation.v`, `execve_unmodeled`).  So the two numbers
share one spec. -/
def exit_spec (code : word) : Sys SyscallEffect :=
  set_halted (bv_and code (Z_to_bv 64 255)) ;; ret_only (Z_to_bv 64 0)

/-- `upid = -1` after the `int` truncation `Syscall.pid32` applies: "reap
any child".  `kernel_wait4` (kernel/exit.c:1864-1865, Linux v6.18.46)
reads it as `if (upid == -1) type = PIDTYPE_MAX;`, the one selector with
no `struct pid` behind it: `__do_wait`'s early exit (:1676-1678) and its
`do_wait_pid` branch (:1682-1685) are both keyed on `wo_type`, so -1 alone
walks `current->children` and `current->ptraced` (:1686-1700) whatever
the pid table holds.  It is the ONLY selector modeled — see `wait4_spec`. -/
def WAIT_ANY32 : Int := 2 ^ 32 - 1

set_option linter.unusedVariables false in
/-- `wait4 upid stat_addr options rusage` (260) — the whole call, for the
only caller it ANSWERS: one with no children.  The argument in full — why
-ECHILD is the one answer, why each other shape is declined rather than
answered, what a child-creating arm owes, and the launcher premise the
conformance harness asserts — is on the Rocq definition `Exit.wait4_spec`
and is not repeated here, with one exception: Rocq's `upid` paragraph
still routes a live pid's -ECHILD through the `pid_has_task` early exit,
which the `upid` bullet below corrects; a `comments:` change to Rocq is
owed.  What follows is the kernel line each gate rests on, re-read at
Linux v6.18.46 (commit 1f99e9ab748f).

Each of the three argument gates declines a call a real kernel answers:

- `upid`: `kernel_wait4` (kernel/exit.c:1864-1875) maps `upid < 0`,
  `upid == 0` and `upid > 0` to a `wo_type < PIDTYPE_MAX`, and the answer
  then rests on state this model does not carry.  A pid or group with no
  task exits early at `__do_wait` (:1676-1678, `pid_has_task`) with the
  -ECHILD seed; a LIVE pid has a task, so `do_wait_pid` (:1639-1663) runs
  and returns 0 for a stranger — the thread-group lookup (:1646-1647)
  finds no leader, or one that fails `is_effectively_child` (:1625), and
  the tracee lookup (:1654-1656) fails `target->ptrace` or the same test —
  leaving the seed to `notask:` (:1704-1705); `upid == 0` names the
  caller's own group, which always has a task, so the walk over
  `current->children` and `current->ptraced` (:1686-1700) decides, as it
  does for a live group under `upid < -1`.  Every route ends in -ECHILD
  for a caller with no children and no tracees, but which route is a fact
  about the pid table, so the shapes decline rather than answer by
  coincidence.  `upid == INT_MIN`
  is -ESRCH before the chain (:1860-1862), after the option mask
  (:1856-1858), so `wait4(INT_MIN, _, <unknown bit>, _)` is -EINVAL.
- `options`: an unknown bit is -EINVAL first of all (:1856-1858); without
  `WNOHANG`, `__do_wait` returns -ERESTARTSYS once a child exists but
  nothing is ready (:1704-1707) and `do_wait` sleeps in `schedule` until
  a signal or a child wakes it (:1722-1730), so the call can answer
  -EINTR; `WUNTRACED` and `WCONTINUED` ask about a child's stop and
  continue.
- `rusage`: never written at -ECHILD — `SYSCALL_DEFINE4(wait4, ...)`
  copies it out under `if (err > 0)` (:1913-1916) — so answering a
  non-NULL one would be sound; declined so that the arm need not be
  rewritten the day a reap becomes expressible.

The `State.m_has_children` gate: a caller the model gave a child
(`Kernel.Fork.clone_resolve`'s success branch applies
`State.with_children`) is declined rather than answered.

THE ANSWER.  `__do_wait` (kernel/exit.c:1665-1710, Linux v6.18.46) seeds
`wo->notask_error = -ECHILD` (:1675); with `wo_type = PIDTYPE_MAX` the
early exit at :1676-1678 is not taken and the walk at :1686-1700 runs
`do_wait_thread` (:1558-1579) and `ptrace_do_wait` (:1581-1593), list walks
over `current->children` and `current->ptraced` that return 0 on empty
lists, so `wait_consider_task` — the only caller that clears
`notask_error` (:1479, :1533, :1539) and the only route to the three
writers of `wo_stat`, `wait_task_zombie` (:1267), `wait_task_stopped`
(:1385) and `wait_task_continued` (:1436) — never runs.
`notask:` (:1704) returns the seed: the -ERESTARTSYS return at :1706-1707
is guarded on `!retval`, which -ECHILD fails, and `do_wait`'s loop
(:1722-1730) breaks on anything but -ERESTARTSYS before `signal_pending`
or `schedule` is reached.  No sleep, no interruption point, and WNOHANG's
bare 0 — what a CLEARED `notask_error` returns — is not admissible.

`stat_addr` IS NOT READ.  `kernel_wait4`'s copy-out is `if (ret > 0 &&
stat_addr && put_user(wo.wo_stat, stat_addr))` (:1885-1886) and C
short-circuits: at `ret = -ECHILD` the pointer is never dereferenced, so
an unmapped, unwritable or past-`TASK_SIZE` `stat_addr` answers -ECHILD
and faults on nothing, and a spec that judged it would reject calls
Linux answers.  The spec takes the argument to say so, and the
unused-variable linter is silenced on this one definition because the
unused argument is the claim. -/
def wait4_spec (upid stat_addr options rusage : word) : Sys SyscallEffect :=
  if bv_unsigned upid ≠ WAIT_ANY32 then unmodeled
  else if bv_unsigned options ≠ WNOHANG then unmodeled
  else if !(w_is0 rusage) then unmodeled
  else
    m <- get_model ;;
    if m_has_children m then unmodeled
    else err_ret ECHILD

end LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit
