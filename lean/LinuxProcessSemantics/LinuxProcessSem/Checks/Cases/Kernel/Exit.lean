import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Kernel.Exit — what `exit`, `exit_group` and `wait4` answer, read off against Linux

Worked examples over `Sys.Kernel.Exit.exit_spec` and
`Sys.Kernel.Exit.wait4_spec`.  Rocq keeps no worked-cases file for these
arms: its pins on them are stated over the executable checker, in
`Checks/ProcessCreation.v` (`wait4_not_unmodeled`,
`wait4_answers_only_echild`) and `Checks/Examples.v`
(`wait4_with_a_child_is_unmodeled`, `wait4_with_a_child_admits_no_answer`),
so this file mirrors no Rocq source.  Not part of the trusted
specification: this file is QA on the definitions, written to be READ, and
every claim in it is a claim about what the kernel does, with the citation
beside it.  Every kernel line below was read at Linux v6.18.46 (commit
1f99e9ab748f).

HOW THESE ARE STATED.  Each decision of a spec gets an `iff` over EVERY
outcome `o` — the positive half (what is admitted) and the negative half
(nothing else is) in one statement — and beside it the concrete mistake a
lying kernel could report, refuted on its own.  Both are closed by the
tactics of `Checks/Cases/Tactic.lean`: `sys_norm` reads the call off its
monad primitives and decides the closed gates, `sys_refute` is `sys_norm`
that must close the goal.  A check over a SYMBOLIC model states the
children gate as the spec has it, then reads the arm the hypothesis
selects: `sys_simp_pass +decide` (the first of `sys_norm`'s two passes)
leaves the gate as `(if m_has_children m = true then … else …) i m o`,
`split` cases on it, and the hypothesis closes the branch it excludes
while `sys_norm` reads the other.

`Checks/Examples.lean`'s `exit_dispatch_*` lemmas state the exit half by
hand through the dispatcher; the exit pins here are the same facts read
by the tactic, and the wait4 pins have no counterpart there.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Exit

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude

/-! The spec's unfolding.  `Checks/Cases/Tactic.lean`'s register is where a
spec's `.eq_1` line is owed (`exit_spec.eq_1` is there already); this
ticket leaves that file untouched, so the line sits here until the
register's next edit takes it. -/
attribute [sys_simp low] wait4_spec.eq_1

/-! ## The numbers these checks spell out

Kept as numerals in the statements so a reader sees the register value the
program passes; these pins say what each one is. -/

/-- `ECHILD` is 10.
kernel: include/uapi/asm-generic/errno-base.h:ECHILD@v6.18.46 -/
example : ECHILD = 10 := by decide
/-- `WNOHANG` is bit 0.
kernel: include/uapi/linux/wait.h:WNOHANG@v6.18.46 -/
example : WNOHANG = 1 := by decide

/-- The model's spelling of `(int) -1` as the unsigned low 32 bits.
model: the model's own constant at a numeral; the kernel reading is on the `pid32` pins below. -/
example : WAIT_ANY32 = 4294967295 := by decide

/-- `pid_t upid` is an `int` (`kernel_wait4`, kernel/exit.c:1848, Linux
v6.18.46): the register's low 32 bits.  -1 sign-extended to 64 bits and
0xffffffff zero-extended are the same `int`, and so is any value whose
high 32 bits differ.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
example : bv_unsigned (pid32 (Z_to_bv 64 (-1))) = 4294967295 := by decide
/-- ...zero-extended.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
example : bv_unsigned (pid32 4294967295) = 4294967295 := by decide
/-- ...with bit 32 set above the all-ones low half.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
example : bv_unsigned (pid32 8589934591) = 4294967295 := by decide
/-- `INT_MIN` as the low 32 bits: 0x80000000.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
example : bv_unsigned (pid32 2147483648) = 2147483648 := by decide
/-- ...and as the `intmin` probe passes it, sign-extended to 64 bits.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
example : bv_unsigned (pid32 (Z_to_bv 64 (-2147483648))) = 2147483648 := by decide
/-- -1234 sign-extended is the `int` -1234, 0xfffffb2e — not -1: a
negative `upid` below -1 keeps its own low half.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
example : bv_unsigned (pid32 (Z_to_bv 64 (-1234))) = 4294966062 := by decide

/-- `int options` likewise (kernel/exit.c:1848): bit 32 of a2 is not part
of what the kernel reads.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
example : bv_unsigned (waitopts32 4294967297) = WNOHANG := by decide

/-! ## `exit` (93) and `exit_group` (94)

`SYSCALL_DEFINE1(exit, int, error_code)` is `do_exit((error_code&0xff)<<8)`
and `SYSCALL_DEFINE1(exit_group, ...)` is `do_group_exit((error_code & 0xff)
<< 8)` (kernel/exit.c:1085-1088 and :1129-1134, Linux v6.18.46).  The
observed code is the low byte of the argument, and the status word Linux
carries internally is that byte shifted left by 8: what a parent's
`WEXITSTATUS` shifts back. -/

/-- Every call halts with the low byte of `code`, returns nothing the
program will see, moves no memory and emits no event: the one outcome.
kernel: kernel/exit.c:exit,exit_group@v6.18.46 -/
theorem exit_halts_with_low_byte (code : word) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    exit_spec code i m o ↔
      o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (bv_and code (Z_to_bv 64 255)) m) [] := by
  sys_norm

/-- `exit(256)` is observed as 0: `256 & 0xff`.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem exit_256_halts_with_zero (i : SyscallInput) (m : Model) :
    exit_spec 256 i m (Ok (mkEffect 0 [] []) (with_halted 0 m) []) := by
  sys_norm

/-- `exit(-1)` is observed as 255, whatever the 56 high bits of a0 hold:
the `int` parameter and the `& 0xff` together read one byte.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem exit_minus_one_halts_with_255 (i : SyscallInput) (m : Model) :
    exit_spec (Z_to_bv 64 (-1)) i m (Ok (mkEffect 0 [] []) (with_halted 255 m) []) := by
  sys_norm

/-- `exit(0x12345)` is observed as 0x45.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem exit_0x12345_halts_with_0x45 (i : SyscallInput) (m : Model) :
    exit_spec 0x12345 i m (Ok (mkEffect 0 [] []) (with_halted 0x45 m) []) := by
  sys_norm

/-- A kernel reporting the unmasked 256 is lying.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem exit_256_unmasked_rejected (i : SyscallInput) (m : Model) :
    ¬ exit_spec 256 i m (Ok (mkEffect 0 [] []) (with_halted 256 m) []) := by
  sys_refute

/-- …and so is one reporting the internal status word: `exit(255)` is
`do_exit(0xff00)`, and 0xff00 is what `wait_task_zombie` (kernel/exit.c,
Linux v6.18.46) hands a waiting parent, but the OBSERVED code is the byte
`WEXITSTATUS` reads back, 255, and the model records that.
kernel: kernel/exit.c:exit,wait_task_zombie@v6.18.46 -/
theorem exit_255_status_word_rejected (i : SyscallInput) (m : Model) :
    ¬ exit_spec 255 i m (Ok (mkEffect 0 [] []) (with_halted 65280 m) []) := by
  sys_refute

/-- `exit` never declines: there is no argument it fails closed on.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem exit_never_unmodeled (code : word) (i : SyscallInput) (m : Model) :
    ¬ exit_spec code i m Unmodeled := by
  sys_refute

/-- Syscall 93 with a0 = 0xffffffff (the `int` -1) halts with 255 through
the dispatcher.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem sysno_93_is_exit (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 93 [4294967295, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o
      ↔ o = Ok (mkEffect 0 [] []) (with_halted 255 m) [] := by
  sys_norm

/-- Syscall 94 (`exit_group`) takes the same byte: `do_group_exit`
(kernel/exit.c:1094-1122, Linux v6.18.46) substitutes `group_exit_code`
only under `SIGNAL_GROUP_EXIT`, whose four writers — another thread's
`do_group_exit` (:1114), `synchronize_group_exit` (:882-885), a fatal
signal's `complete_signal` (kernel/signal.c:1003-1018) and a core dump's
`zap_process` (fs/coredump.c:486) — need a second thread or a signal,
or store the very code `do_exit` was given; `exit_spec`'s docstring
takes each in turn.
kernel: kernel/exit.c:exit_group,do_group_exit@v6.18.46 -/
theorem sysno_94_is_exit_group (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 94 [0x12345, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o
      ↔ o = Ok (mkEffect 0 [] []) (with_halted 0x45 m) [] := by
  sys_norm

/-! ## `wait4` (260): the modeled shape

`wait4(-1, stat_addr, WNOHANG, NULL)` from a caller with no children.
`__do_wait` (kernel/exit.c:1665-1710, Linux v6.18.46) seeds
`notask_error = -ECHILD` (:1675); the -1 selector is `PIDTYPE_MAX`
(`kernel_wait4`, :1864-1865), so the `pid_has_task` early exit (:1676-1678)
is not taken and `do_wait_thread` (:1558-1579) and `ptrace_do_wait`
(:1581-1593) walk `current->children` and `current->ptraced`, both empty,
returning 0 without ever reaching `wait_consider_task`.  `notask:`
(:1704-1709) returns the seed unchanged — the -ERESTARTSYS assignment is guarded on `!retval` — and
`do_wait`'s loop (:1722-1730) breaks before `signal_pending` or `schedule`.
One answer, no sleep, no memory moved. -/

/-- The whole call, for ANY `stat_addr`: -ECHILD, the model untouched, no
write, no event.  `kernel_wait4`'s copy-out (kernel/exit.c:1885-1886,
Linux v6.18.46) is `if (ret > 0 && stat_addr && put_user(...))`, so at
-ECHILD the pointer is never dereferenced and its value cannot change the
answer — which is why the statement quantifies over it.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_childless_is_echild (stat_addr : word) (i : SyscallInput) (o : outcome SyscallEffect) :
    wait4_spec 4294967295 stat_addr 1 0 i demo_model o ↔
      o = Ok (mkEffect (errno_ret ECHILD) [] []) demo_model [] := by
  sys_norm

/-- The same over every model the gate lets through, on the one modeled
argument shape.  `Checks/ProcessCreation.v`'s `wait4_not_unmodeled` and
`wait4_answers_only_echild` quantify over the INPUT as well, through
`syscall_spec`; this pin is the model half of that claim.  The other half
has no single Lean statement: the argument gates' `_other_*_is_unmodeled`
pins below each free ONE argument on `wait4_spec` with the rest at the
modeled values, and every statement through the dispatcher is on a
literal register list.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_childless_is_echild_for_every_model (stat_addr : word) (i : SyscallInput)
    (m : Model) (hm : m_has_children m = false) (o : outcome SyscallEffect) :
    wait4_spec 4294967295 stat_addr 1 0 i m o ↔
      o = Ok (mkEffect (errno_ret ECHILD) [] []) m [] := by
  sys_simp_pass +decide
  split
  · rename_i hc
    exact absurd (hm.symm.trans hc) Bool.false_ne_true
  · sys_norm

/-- A `stat_addr` one past the address space, and a NULL one, are answered
alike: the pointer is dead at -ECHILD.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
example (i : SyscallInput) (o : outcome SyscallEffect) :
    wait4_spec 4294967295 (Z_to_bv 64 (-1)) 1 0 i demo_model o ↔
      o = Ok (mkEffect (errno_ret ECHILD) [] []) demo_model [] :=
  wait4_childless_is_echild _ i o

/-- ...and the NULL one.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
example (i : SyscallInput) (o : outcome SyscallEffect) :
    wait4_spec 4294967295 0 1 0 i demo_model o ↔
      o = Ok (mkEffect (errno_ret ECHILD) [] []) demo_model [] :=
  wait4_childless_is_echild _ i o

/-- WNOHANG's bare 0 is what a CLEARED `notask_error` returns
(kernel/exit.c:1704-1709, Linux v6.18.46), and only `wait_consider_task`
on a child that exists clears it: a childless caller cannot get it.
kernel: kernel/exit.c:__do_wait@v6.18.46 -/
theorem wait4_childless_bare_zero_rejected (i : SyscallInput) :
    ¬ wait4_spec 4294967295 0 1 0 i demo_model (Ok (mkEffect 0 [] []) demo_model []) := by
  sys_refute

/-- A pid is a reap.  On this shape — `WNOHANG` alone, so `wo_flags` is
`WNOHANG|WEXITED` — and for a caller with no children and no tracees,
only `wait_task_zombie` (kernel/exit.c:1175, Linux v6.18.46) could return
one: `wait_task_stopped` (:1331) returns 0 for an UNTRACED child without
`WUNTRACED` (:1342-1343; a stopped tracee is reported whatever the
options, :1340), and `wait_task_continued` (:1403) needs `WCONTINUED`.
All three sit behind `wait_consider_task`, which is never reached over
empty lists.
kernel: kernel/exit.c:wait_task_zombie,do_wait_thread@v6.18.46 -/
theorem wait4_childless_reap_rejected (i : SyscallInput) :
    ¬ wait4_spec 4294967295 0 1 0 i demo_model (Ok (mkEffect 42 [] []) demo_model []) := by
  sys_refute

/-- `EFAULT` (include/uapi/asm-generic/errno-base.h:18, Linux v6.18.46)
needs the `put_user` at kernel/exit.c:1885-1886, which `ret > 0` guards:
no -ECHILD reaches it, whatever `stat_addr` is.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem wait4_childless_efault_rejected (stat_addr : word) (i : SyscallInput) :
    ¬ wait4_spec 4294967295 stat_addr 1 0 i demo_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) demo_model []) := by
  sys_refute

/-- `EINTR` (errno-base.h:8) needs the sleep in `do_wait`
(kernel/exit.c:1722-1730, Linux v6.18.46), which -ECHILD breaks out of
before `signal_pending` is consulted.
kernel: kernel/exit.c:do_wait@v6.18.46 -/
theorem wait4_childless_eintr_rejected (i : SyscallInput) :
    ¬ wait4_spec 4294967295 0 1 0 i demo_model (Ok (mkEffect (errno_ret EINTR) [] []) demo_model []) := by
  sys_refute

/-- -ERESTARTSYS (512, include/linux/errno.h:14, Linux v6.18.46) is what
`__do_wait` returns to `do_wait`'s loop (kernel/exit.c:1704-1707 and
:1725), never to userspace, and never at all for the `PIDTYPE_MAX` walk
over empty lists.
kernel: kernel/exit.c:__do_wait,do_wait@v6.18.46 -/
theorem wait4_childless_erestartsys_rejected (i : SyscallInput) :
    ¬ wait4_spec 4294967295 0 1 0 i demo_model (Ok (mkEffect (errno_ret 512) [] []) demo_model []) := by
  sys_refute

/-- A status written through `stat_addr` is the copy-out the guard skips.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem wait4_childless_writes_nothing (stat_addr : word) (i : SyscallInput) :
    ¬ wait4_spec 4294967295 stat_addr 1 0 i demo_model
        (Ok (mkEffect (errno_ret ECHILD) [(stat_addr, [0, 0, 0, 0])] []) demo_model []) := by
  sys_refute

/-- Nothing is reaped, so nothing in the model changes: a -ECHILD that
lands in a model with a child recorded is refused on the model.
kernel: kernel/exit.c:__do_wait@v6.18.46 -/
theorem wait4_childless_model_untouched (i : SyscallInput) :
    ¬ wait4_spec 4294967295 0 1 0 i demo_model
        (Ok (mkEffect (errno_ret ECHILD) [] []) (with_children demo_model) []) := by
  sys_refute

/-- The modeled shape never declines.
kernel: kernel/exit.c:__do_wait@v6.18.46 -/
theorem wait4_childless_never_unmodeled (stat_addr : word) (i : SyscallInput) :
    ¬ wait4_spec 4294967295 stat_addr 1 0 i demo_model Unmodeled := by
  sys_refute

/-! ## The `upid` gate

`kernel_wait4` (kernel/exit.c:1864-1875, Linux v6.18.46) maps every
`upid` but -1 to a `wo_type < PIDTYPE_MAX` — `PIDTYPE_PGID` for `upid < 0`
and `upid == 0`, `PIDTYPE_PID` for `upid > 0`.  `__do_wait` (:1676-1678)
takes the early exit only for a pid or group with NO task; a live pid has
one, so `do_wait_pid` (:1639-1663) runs and returns 0 for a stranger —
its thread-group lookup (:1646-1647) finds no leader or one that fails
`is_effectively_child` (:1625), its tracee lookup (:1654-1656) fails
`target->ptrace` or the same test — leaving the -ECHILD seed to `notask:`
(:1704-1705); `upid == 0` is the caller's own group, which always has a
task, so the walk over `current->children` and `current->ptraced`
(:1686-1700) decides.  Every route ends in -ECHILD for a caller with no
children and no tracees, but which route is a fact about the pid table
the model does not carry, so the shapes decline rather than answer by
coincidence.  (The probe's own comments, `wait4_spec.c`'s `childpid`
mode, still give the `pid_has_task` route; its source is hashed into the
trace corpus, so that correction travels with the next re-recording.)
`upid == INT_MIN` is -ESRCH before the chain (:1860-1862), because negating
it would overflow; it declines with the rest. -/

/-- `upid = 0`: the caller's own process group.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_own_group_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    wait4_spec 0 0 1 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `upid = 1`: one pid.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_one_pid_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    wait4_spec 1 0 1 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `upid = -2`: process group 2.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_group_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    wait4_spec 4294967294 0 1 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `upid = INT_MIN`.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem wait4_int_min_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    wait4_spec 2147483648 0 1 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- EVERY other `upid` declines, not only the four sampled: the gate is
the whole complement of -1.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_other_upid_is_unmodeled (upid : word) (h : bv_unsigned upid ≠ WAIT_ANY32)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    wait4_spec upid 0 1 0 i m o ↔ o = Unmodeled := by
  sys_simp_pass +decide
  split
  · sys_norm
  · rename_i hc
    rw [show WAIT_ANY32 = 4294967295 from by decide] at h
    exact absurd (Decidable.of_not_not hc) h

/-- Linux's `ESRCH` (errno-base.h:7) for `INT_MIN` is NOT given: the
decline admits no answer at all.  This is not claimed to be an empty
intersection; it is the Rocq definition's declared narrowing — the `upid`
guard is on the argument, and this shape is declined with the other three
rather than answered as a fourth.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem wait4_int_min_esrch_rejected (i : SyscallInput) (m : Model) :
    ¬ wait4_spec 2147483648 0 1 0 i m (Ok (mkEffect (errno_ret ESRCH) [] []) m []) := by
  sys_refute

/-- …and -ECHILD for a named pid is not given either, though Linux answers
it to a childless caller when the pid is live: the model does not know
whether it is.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_one_pid_echild_rejected (i : SyscallInput) :
    ¬ wait4_spec 1 0 1 0 i demo_model (Ok (mkEffect (errno_ret ECHILD) [] []) demo_model []) := by
  sys_refute

/-! ## The `options` gate

`kernel_wait4` validates the mask first of all (kernel/exit.c:1856-1858,
Linux v6.18.46): a bit outside `WNOHANG|WUNTRACED|WCONTINUED|__WNOTHREAD|
__WCLONE|__WALL` is -EINVAL before `upid` is looked at.  Without `WNOHANG`
the call blocks once a child exists — `__do_wait` returns -ERESTARTSYS
(:1704-1707) and `do_wait` sleeps (:1722-1730) — and can answer -EINTR,
which no arm here produces; `WUNTRACED` (wait.h:6) and `WCONTINUED`
(wait.h:9) ask about a child's stop and continue.  Every option word but
`WNOHANG` alone declines. -/

/-- `options = 0`: a blocking wait.  A childless caller gets -ECHILD from
it too (`!retval` fails on -ECHILD, so no -ERESTARTSYS), but the guard is
on the ARGUMENT, so that the spec need not be re-argued the day a child is
expressible.
kernel: kernel/exit.c:__do_wait,do_wait@v6.18.46 -/
theorem wait4_blocking_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    wait4_spec 4294967295 0 0 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `WNOHANG|WUNTRACED` (3): a stopped child would be reportable.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem wait4_wuntraced_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    wait4_spec 4294967295 0 3 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- 4 is `WEXITED` (include/uapi/linux/wait.h:8), which `kernel_wait4`
ORs in itself (`wo.wo_flags = options | WEXITED`, kernel/exit.c:1879,
Linux v6.18.46) and refuses from userspace: outside the mask, so Linux's
-EINVAL, declined here.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem wait4_unknown_option_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    wait4_spec 4294967295 0 4 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- EVERY option word but `WNOHANG` alone declines — including the three
`kernel_wait4` accepts and a childless caller really gets -ECHILD for,
`WNOHANG|__WALL`, `WNOHANG|__WCLONE` and `WNOHANG|__WNOTHREAD`
(wait.h:12-14; `__WNOTHREAD` only stops the thread loop at
kernel/exit.c:1698-1699, Linux v6.18.46).
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_other_options_is_unmodeled (options : word) (h : bv_unsigned options ≠ WNOHANG)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    wait4_spec 4294967295 0 options 0 i m o ↔ o = Unmodeled := by
  sys_simp_pass +decide
  split
  · sys_norm
  · rename_i hc
    rw [show WNOHANG = 1 from by decide] at h
    exact absurd (Decidable.of_not_not hc) h

/-- The kernel's -EINVAL is not admitted: a decline answers nothing.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem wait4_unknown_option_einval_rejected (i : SyscallInput) (m : Model) :
    ¬ wait4_spec 4294967295 0 4 0 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  sys_refute

/-- Neither -ECHILD nor -EINTR is admitted for the blocking shape: the
first would be right only for a childless caller, the second only for one
with a child, and the model answers neither.
kernel: kernel/exit.c:__do_wait,do_wait@v6.18.46 -/
theorem wait4_blocking_echild_rejected (i : SyscallInput) :
    ¬ wait4_spec 4294967295 0 0 0 i demo_model (Ok (mkEffect (errno_ret ECHILD) [] []) demo_model []) := by
  sys_refute

/-- -EINTR is not given for the blocking shape either.
kernel: kernel/exit.c:__do_wait,do_wait@v6.18.46 -/
theorem wait4_blocking_eintr_rejected (i : SyscallInput) (m : Model) :
    ¬ wait4_spec 4294967295 0 0 0 i m (Ok (mkEffect (errno_ret EINTR) [] []) m []) := by
  sys_refute

/-! ## The `rusage` gate

A non-NULL `rusage` is never written at -ECHILD — `SYSCALL_DEFINE4(wait4,
...)` copies it out under `if (err > 0)` (kernel/exit.c:1913-1916, Linux
v6.18.46) — so answering it would be sound; it is declined because a
`struct rusage` of accounting is what the arm would have to fill the day a
reap becomes expressible. -/

/-- A non-NULL `rusage` declines.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem wait4_rusage_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    wait4_spec 4294967295 0 1 4096 i m o ↔ o = Unmodeled := by
  sys_norm

/-- EVERY non-NULL `rusage` declines; `w_is0` reads all 64 bits, so a
pointer with only high bits set (0x100000000) is non-NULL here as it is
to the kernel, which takes `struct rusage __user *ru` unnarrowed.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem wait4_other_rusage_is_unmodeled (rusage : word) (h : w_is0 rusage = false)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    wait4_spec 4294967295 0 1 rusage i m o ↔ o = Unmodeled := by
  sys_simp_pass +decide
  split
  · sys_norm
  · rename_i hc
    simp only [h, Bool.not_false, not_true_eq_false] at hc

/-- ...including one with only bit 32 set.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem wait4_rusage_high_bits_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    wait4_spec 4294967295 0 1 4294967296 i m o ↔ o = Unmodeled := by
  sys_norm

/-- -ECHILD is not given with a non-NULL `rusage`.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem wait4_rusage_echild_rejected (i : SyscallInput) :
    ¬ wait4_spec 4294967295 0 1 4096 i demo_model
        (Ok (mkEffect (errno_ret ECHILD) [] []) demo_model []) := by
  sys_refute

/-! ## The children gate

-ECHILD is the answer to EMPTY `children` and `ptraced` lists, and
`Kernel.Fork.clone_resolve`'s success branch is the modeled operation that
makes one non-empty (`State.with_children`).  For such a caller Linux gives
one of three answers — the child's pid from `wait_task_zombie`, WNOHANG's
bare 0 from a cleared `notask_error`, or -ECHILD if the child was reaped
already — and which one is a question about a child this model does not
carry, so the call declines.  `Checks/Examples.v`'s
`wait4_with_a_child_is_unmodeled` and `wait4_with_a_child_admits_no_answer`
are the Rocq statements. -/

/-- A recorded child declines.
kernel: kernel/exit.c:__do_wait,do_wait_thread,wait_task_zombie@v6.18.46 -/
theorem wait4_with_child_is_unmodeled (stat_addr : word) (i : SyscallInput) (o : outcome SyscallEffect) :
    wait4_spec 4294967295 stat_addr 1 0 i (with_children demo_model) o ↔ o = Unmodeled := by
  sys_norm

/-- ...for every model that records one.
kernel: kernel/exit.c:__do_wait,do_wait_thread,wait_task_zombie@v6.18.46 -/
theorem wait4_with_child_is_unmodeled_for_every_model (stat_addr : word) (i : SyscallInput)
    (m : Model) (hm : m_has_children m = true) (o : outcome SyscallEffect) :
    wait4_spec 4294967295 stat_addr 1 0 i m o ↔ o = Unmodeled := by
  sys_simp_pass +decide
  split
  · sys_norm
  · rename_i hc
    exact absurd hm hc

/-- None of Linux's three resolutions is admitted with a child recorded:
-ECHILD is the one the spec would have given without the gate.
kernel: kernel/exit.c:__do_wait,do_wait_thread@v6.18.46 -/
theorem wait4_with_child_echild_rejected (i : SyscallInput) :
    ¬ wait4_spec 4294967295 0 1 0 i (with_children demo_model)
        (Ok (mkEffect (errno_ret ECHILD) [] []) (with_children demo_model) []) := by
  sys_refute

/-- WNOHANG's bare 0 is not given with a child recorded.
kernel: kernel/exit.c:__do_wait,wait_consider_task@v6.18.46 -/
theorem wait4_with_child_bare_zero_rejected (i : SyscallInput) :
    ¬ wait4_spec 4294967295 0 1 0 i (with_children demo_model)
        (Ok (mkEffect 0 [] []) (with_children demo_model) []) := by
  sys_refute

/-- A reap is not given with a child recorded.
kernel: kernel/exit.c:wait_task_zombie@v6.18.46 -/
theorem wait4_with_child_reap_rejected (i : SyscallInput) :
    ¬ wait4_spec 4294967295 0 1 0 i (with_children demo_model)
        (Ok (mkEffect 42 [] []) demo_model []) := by
  sys_refute

/-! ## Two conditions at once

The model has one errno and four declines, so precedence between two
kernel errnos never arises inside an answer; what has to hold is that a
call two declines apply to answers NOTHING, whichever errno Linux would
pick.  `wait4(INT_MIN, _, 4, _)` is the pair the Rocq argument names: the
mask check (kernel/exit.c:1856-1858, Linux v6.18.46) precedes the
`INT_MIN` check (:1860-1862), so Linux says -EINVAL and not -ESRCH.
Neither is admitted. -/

/-- `wait4(INT_MIN, _, 4, _)` declines.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem wait4_int_min_unknown_option_is_unmodeled (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    wait4_spec 2147483648 0 4 0 i m o ↔ o = Unmodeled := by
  sys_norm

/-- ...and its kernel -EINVAL is not given.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem wait4_int_min_unknown_option_einval_rejected (i : SyscallInput) (m : Model) :
    ¬ wait4_spec 2147483648 0 4 0 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  sys_refute

/-- ...nor the -ESRCH the other order would give.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem wait4_int_min_unknown_option_esrch_rejected (i : SyscallInput) (m : Model) :
    ¬ wait4_spec 2147483648 0 4 0 i m (Ok (mkEffect (errno_ret ESRCH) [] []) m []) := by
  sys_refute

/-- A non-NULL `rusage` from a caller with a child: the argument gate fires
before the model is read, and the outcome is the same decline.
kernel: kernel/exit.c:wait4,__do_wait@v6.18.46 -/
theorem wait4_rusage_with_child_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    wait4_spec 4294967295 0 1 4096 i (with_children demo_model) o ↔ o = Unmodeled := by
  sys_norm

/-! ## The dispatcher, read through the table

Syscall 260 reaches `wait4_spec` with a0 through `pid32` and a2 through
`waitopts32`: `kernel_wait4`'s `pid_t upid` and `int options`
(kernel/exit.c:1848, Linux v6.18.46) are the low 32 bits of the registers. -/

/-- a0 = -1 sign-extended: the `int` is -1, the modeled selector.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem sysno_260_sign_extended_minus_one (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 260 [Z_to_bv 64 (-1), 0, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o
      ↔ o = Ok (mkEffect (errno_ret ECHILD) [] []) demo_model [] := by
  sys_norm

/-- a0 = 0xffffffff zero-extended: the same `int`.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem sysno_260_zero_extended_minus_one (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 260 [4294967295, 0, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o
      ↔ o = Ok (mkEffect (errno_ret ECHILD) [] []) demo_model [] := by
  sys_norm

/-- a0 = 0x1ffffffff: bit 32 set above an all-ones low half, the shape that
passes only through a 32-bit truncation and not through 2^32-1 itself.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem sysno_260_upid_high_bit_dropped (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 260 [8589934591, 0, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o
      ↔ o = Ok (mkEffect (errno_ret ECHILD) [] []) demo_model [] := by
  sys_norm

/-- Bit 32 of a2 is not part of `int options`: 0x100000001 is `WNOHANG`.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem sysno_260_option_high_bit_dropped (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 260 [4294967295, 0, 4294967297, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o
      ↔ o = Ok (mkEffect (errno_ret ECHILD) [] []) demo_model [] := by
  sys_norm

/-- …and neither is the whole high half: a2 = 0xffffffff00000001 is
`WNOHANG` too, which separates the 32-bit read from any wider mask.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem sysno_260_option_high_half_dropped (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 260 [4294967295, 0, 18446744069414584321, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o
      ↔ o = Ok (mkEffect (errno_ret ECHILD) [] []) demo_model [] := by
  sys_norm

/-- a1 is passed through untruncated and unread: a `stat_addr` at the top
of the address space answers like a NULL one.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem sysno_260_stat_addr_unread (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 260 [4294967295, Z_to_bv 64 (-1), 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o
      ↔ o = Ok (mkEffect (errno_ret ECHILD) [] []) demo_model [] := by
  sys_norm

/-! The three shape declines below are stated as the decline itself plus a
refutation of the answer, not as an `iff` with `Unmodeled`, and are named
`…_declines`: `tools/check_decline_registers.py` reads
`syscall_spec (SyscallInput.mkInput N …) m Unmodeled` in the direct shape
only, and reads a theorem so shaped and NAMED `…_unmodeled` as register
L3's claim that NUMBER `N` has no arm — which 260 now has.
`sysno_95_is_unmodeled` at the end is such a claim. -/

/-- a3 is NOT narrowed: `struct rusage __user *ru` is a pointer, and a
non-NULL one declines — including one with only bit 32 set, which a port
that narrowed a3 to an `int` would wrongly answer.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem sysno_260_rusage_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 260 [4294967295, 0, 1, 4096, 0, 0] (fun _ => none) (fun _ => none))
        m Unmodeled := by
  sys_norm

/-- ...and -ECHILD is not given through it.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem sysno_260_rusage_echild_rejected :
    ¬ syscall_spec (SyscallInput.mkInput 260 [4294967295, 0, 1, 4096, 0, 0] (fun _ => none) (fun _ => none))
        demo_model (Ok (mkEffect (errno_ret ECHILD) [] []) demo_model []) := by
  sys_refute

/-- a3 = 0x100000000 is non-NULL and declines.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem sysno_260_rusage_high_bits_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 260 [4294967295, 0, 1, 4294967296, 0, 0] (fun _ => none) (fun _ => none))
        m Unmodeled := by
  sys_norm

/-- ...and -ECHILD is not given through it.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem sysno_260_rusage_high_bits_echild_rejected :
    ¬ syscall_spec (SyscallInput.mkInput 260 [4294967295, 0, 1, 4294967296, 0, 0] (fun _ => none) (fun _ => none))
        demo_model (Ok (mkEffect (errno_ret ECHILD) [] []) demo_model []) := by
  sys_refute

/-- The children gate reaches the dispatcher unchanged, for every model
that records a child.
kernel: kernel/exit.c:__do_wait,do_wait_thread@v6.18.46 -/
theorem sysno_260_with_child_declines (m : Model) (hm : m_has_children m = true) :
    syscall_spec (SyscallInput.mkInput 260 [4294967295, 0, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        m Unmodeled := by
  sys_simp_pass +decide
  split
  · sys_norm
  · rename_i hc
    exact absurd hm hc

/-- ...and -ECHILD is not given with a child recorded.
kernel: kernel/exit.c:__do_wait,do_wait_thread@v6.18.46 -/
theorem sysno_260_with_child_echild_rejected :
    ¬ syscall_spec (SyscallInput.mkInput 260 [4294967295, 0, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        (with_children demo_model) (Ok (mkEffect (errno_ret ECHILD) [] []) (with_children demo_model) []) := by
  sys_refute

/-! ### The dispatcher's argument reads

`in_arg` is not in `sys_simp`, so a register list with a symbolic element
would keep `in_arg (mkInput …) k` stuck and the narrowing helpers
unapplied.  The four positions the wait4 arm reads, on any six-register
call, closed by `rfl`. -/

/-- model: the dispatcher's first register on a literal call, a rewrite for `sys_norm`. -/
theorem in_arg_0 (n a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 0 = a0 := rfl
/-- model: the dispatcher's second register on a literal call, a rewrite for `sys_norm`. -/
theorem in_arg_1 (n a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 1 = a1 := rfl
/-- model: the dispatcher's third register on a literal call, a rewrite for `sys_norm`. -/
theorem in_arg_2 (n a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 2 = a2 := rfl
/-- model: the dispatcher's fourth register on a literal call, a rewrite for `sys_norm`. -/
theorem in_arg_3 (n a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 3 = a3 := rfl

/- LOCAL: `Checks/Cases/Fs/Stat.lean` and `Checks/Cases/Kernel/Sched/Syscalls.lean`
state the same readings for their own pins; the one copy all three want is
a `lean: base:` line in `Checks/Cases/Tactic.lean` beside `bind_arg_iff`,
and until it lands none of them should widen the shared set. -/
attribute [local sys_simp] in_arg_0 in_arg_1 in_arg_2 in_arg_3

/-! ## The narrowing helpers carry the declines too

Every dispatcher pin above has a0 = -1 and a2 = WNOHANG after narrowing,
and the `pid32`/`waitopts32` examples at the top of the file pin the
helpers in isolation, so an ARM that ignored a0 or a2 — or wired the
modeled constants into `wait4_spec` directly — passed every pin through
`syscall_spec`.  These take the probe corpus's seven fail-closed inputs
through the dispatcher (`rusage` is `sysno_260_rusage_declines` above, at
a different pointer); the `_rejected` twins refuse the answer Linux gives
each probe, so the decline is not a coincidence of the fixture.  Every
cited probe passes `&status` in a1, and so do these: a1 is a binder the
`in_arg` rewrites above make reducible.  The arm never reads it
(`Sys/Kernel/Exit.lean`'s `wait4_spec` takes it and never inspects it),
and Linux's answer is the same at any pointer, `kernel_wait4`'s copy-out
being behind `ret > 0` (:1885).  Which route Linux takes to each -ECHILD
below is a fact about the guest's pid table — the early exit (:1676-1678)
for a pid or group with no task, `do_wait_pid` or the walk otherwise — and
every route returns `__do_wait`'s seed (:1675) at `notask:` (:1704-1705). -/

/-- `childpid`: a specific pid declines through the dispatcher.
probe: testing/syscall-check/tests/wait4_spec.c#fail-closed -- childpid -/
theorem sysno_260_childpid_declines (stat_addr : word) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 260 [1234, stat_addr, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- ...and the -ECHILD Linux answers the probe is not given through it.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem sysno_260_childpid_echild_rejected (stat_addr : word) :
    ¬ syscall_spec (SyscallInput.mkInput 260 [1234, stat_addr, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model (Ok (mkEffect (errno_ret ECHILD) [] []) demo_model []) := by
  sys_refute

/-- `pgrpself`: upid 0, the caller's own group, declines through the dispatcher.
probe: testing/syscall-check/tests/wait4_spec.c#fail-closed -- pgrpself -/
theorem sysno_260_pgrpself_declines (stat_addr : word) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 260 [0, stat_addr, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- ...and the -ECHILD Linux answers the probe — the walk over the
caller's empty lists (:1686-1700), its own group always having a task —
is not given through it.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem sysno_260_pgrpself_echild_rejected (stat_addr : word) :
    ¬ syscall_spec (SyscallInput.mkInput 260 [0, stat_addr, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model (Ok (mkEffect (errno_ret ECHILD) [] []) demo_model []) := by
  sys_refute

/-- `pgrpother`: a0 = -1234 sign-extended narrows to -1234 (the example at
the top of the file), not to -1, and declines through the dispatcher.
probe: testing/syscall-check/tests/wait4_spec.c#fail-closed -- pgrpother -/
theorem sysno_260_pgrpother_declines (stat_addr : word) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 260 [Z_to_bv 64 (-1234), stat_addr, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- ...and the -ECHILD Linux answers the probe is not given through it.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem sysno_260_pgrpother_echild_rejected (stat_addr : word) :
    ¬ syscall_spec (SyscallInput.mkInput 260 [Z_to_bv 64 (-1234), stat_addr, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model (Ok (mkEffect (errno_ret ECHILD) [] []) demo_model []) := by
  sys_refute

/-- `intmin`: a0 = INT_MIN sign-extended narrows to 0x80000000 (the
example at the top of the file) and declines through the dispatcher.
probe: testing/syscall-check/tests/wait4_spec.c#fail-closed -- intmin -/
theorem sysno_260_intmin_declines (stat_addr : word) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 260 [Z_to_bv 64 (-2147483648), stat_addr, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- ...and the -ESRCH Linux answers it (kernel/exit.c:1860-1862) is not
given through it.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem sysno_260_intmin_esrch_rejected (stat_addr : word) :
    ¬ syscall_spec (SyscallInput.mkInput 260 [Z_to_bv 64 (-2147483648), stat_addr, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model (Ok (mkEffect (errno_ret ESRCH) [] []) demo_model []) := by
  sys_refute

/-- `blocking`: options 0 declines through the dispatcher; a0 is the
probe's -1, sign-extended.
probe: testing/syscall-check/tests/wait4_spec.c#fail-closed -- blocking -/
theorem sysno_260_blocking_declines (stat_addr : word) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 260 [Z_to_bv 64 (-1), stat_addr, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- ...and -ECHILD is not given through it.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem sysno_260_blocking_echild_rejected (stat_addr : word) :
    ¬ syscall_spec (SyscallInput.mkInput 260 [Z_to_bv 64 (-1), stat_addr, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model (Ok (mkEffect (errno_ret ECHILD) [] []) demo_model []) := by
  sys_refute

/-- `badopt`: WNOHANG|WEXITED (5) declines through the dispatcher.
probe: testing/syscall-check/tests/wait4_spec.c#fail-closed -- badopt -/
theorem sysno_260_badopt_declines (stat_addr : word) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 260 [Z_to_bv 64 (-1), stat_addr, 5, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- ...and the -EINVAL Linux answers it (kernel/exit.c:1856-1858) is not
given through it.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem sysno_260_badopt_einval_rejected (stat_addr : word) :
    ¬ syscall_spec (SyscallInput.mkInput 260 [Z_to_bv 64 (-1), stat_addr, 5, 0, 0, 0] (fun _ => none) (fun _ => none))
        demo_model (Ok (mkEffect (errno_ret EINVAL) [] []) demo_model []) := by
  sys_refute

/-- `waitid` (95) has no arm in this table, nor in Rocq's: it declines by
absence.  A mis-wired `mkSpecArm 95 wait4_spec …` would pass every pin
above; this is the one it fails.  Read by `tools/check_decline_registers.py`
as register L3's claim on the number.
kernel: kernel/exit.c:waitid@v6.18.46 -/
theorem sysno_95_is_unmodeled (m : Model) :
    syscall_spec (SyscallInput.mkInput 95 [0, 4294967295, 0, 4, 0, 0] (fun _ => none) (fun _ => none)) m
      Unmodeled := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Exit
