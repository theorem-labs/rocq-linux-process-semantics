import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Futex.Syscalls
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Kernel.Futex.Syscalls — futex on the checked surface

The registration of `Checks/Sys/Kernel/Futex/Syscalls.lean`'s checker in
`checked_table`, in the one file that registration writes.
`tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files
under `Checks/Arms/`, one per checker twin, so that registering an arm
creates or edits no hub but this file; its docstring is the shape it reads
and what it refuses. The file holds three sections, each in the
namespace its declarations had when those three hubs were written by
hand, so that no name moved with the file:

- `Checks.Sys.Table`: the `CheckedArm` (`arm_futex`) and its four
  `arm_unfold` lemmas;
- `Checks.VmMapsDisjoint.Arms`: the arm's ledger fact,
  `arm_futex_preserves_vm`, which `checked_table_preserves_vm`'s
  alternation names;
- `Checks.Invariants`: one `<invariant>_arm_futex` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`, which
  `registry_preserves`'s alternation names, and the model frame lemma two
  of them are built from.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arms are the rows of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table`, read at that commit.  The ticket's brief quotes the
port's common baseline f44244ad instead; the futex definition
there, its four `arm_unfold` lemmas and their `Hint Rewrite` lines, and
`VmMapsDisjoint.v`'s `check_futex_frame` beside the alternative that
consumes it, are byte-identical at f44244ad, at a71fd38a and at the tip
this file was written against, so either commit names the text read. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### futex (98) -/

/-- futex (98).  FOUR REGISTERS, `a0` TO `a3`, EACH HANDED OVER WHOLE,
AND `a4` AND `a5` NOT READ.  riscv64's `__riscv_sys_futex` hands the
registers over in order, `orig_a0` then `a1` to `a5`
(`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24,
Linux v6.18.46), to the parameters `SYSCALL_DEFINE6(futex, u32 __user *,
uaddr, int, op, u32, val, const struct __kernel_timespec __user *, utime,
u32 __user *, uaddr2, u32, val3)` declares (kernel/futex/syscalls.c:188-190,
same version), so `uaddr`, `op`, `val` and `utime` are `in_arg i 0` to
`in_arg i 3`, as Rocq's `arm_futex` reads them.  No narrowing is applied
here, and each register's reason differs.  `uaddr` and `utime` are
pointers, 64 bits wide on riscv64.  `val` is `u32`, and `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46) narrows it
before `__do_sys_futex` sees it; `futex_spec` applies that narrowing
itself, `abi_low32 val` on the one arm that compares the word, so the arm
must hand it the whole register or the low word would be taken twice to
no effect and the spec's own reading would go unexercised.  `op` is
`int`, and the spec tests it WHOLE, stricter than the kernel's
`__SC_CAST` and deliberately: a register whose high half is not zero is
declined rather than answered, the fail-closed direction, which
`futex_spec`'s docstring (`Sys/Kernel/Futex/Syscalls.lean`) argues and
`testing/syscall-check/tests/unmodeled_futex.c`'s `wake_high` case
replays.  `uaddr2` and `val3` are the fifth and sixth parameters, and
neither private op reads them: `do_futex` overwrites `val3` on both
(kernel/futex/syscalls.c:127 and :132, Linux v6.18.46) and passes `uaddr2`
only to the commands outside them, which the spec declines.
`ca_arm` is the term `Sys/Registry/Kernel/Futex/Syscalls.lean`'s row
builds, which `checked_table_arms` checks.  The ledger fact this arm owes
`checked_table_preserves_vm` is `check_futex_frame`, beside the checker;
`Checks/Cases/Checks/Sys/Kernel/Futex/Syscalls.lean` pins the register
reading through `check_syscall`, since no field below can tell one
register from another. -/
def arm_futex : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 98 (fun i => Sys.Kernel.Futex.Syscalls.futex_spec (in_arg i 0)
    (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m => Checks.Sys.Kernel.Futex.Syscalls.check_futex i (in_arg i 0)
    (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m => Checks.Sys.Kernel.Futex.Syscalls.futex_witness (in_arg i 0)
    (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs h => Checks.Sys.Kernel.Futex.Syscalls.check_futex_sound_ok i
    (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Futex.Syscalls.check_futex_sound_unmodeled i (in_arg i 0) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Futex.Syscalls.check_futex_complete_ok i (in_arg i 0) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Futex.Syscalls.check_futex_complete_unmodeled i (in_arg i 0) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) m eff h
  ca_receptive := fun i m => Checks.Sys.Kernel.Futex.Syscalls.futex_witness_ok (in_arg i 0)
    (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

@[arm_unfold] theorem ca_check_arm_futex (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_futex.ca_check i eff m = Checks.Sys.Kernel.Futex.Syscalls.check_futex i (in_arg i 0)
      (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_futex (i : SyscallInput) (m : Model) :
    arm_futex.ca_witness i m = Checks.Sys.Kernel.Futex.Syscalls.futex_witness (in_arg i 0)
      (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := rfl
@[arm_unfold] theorem sa_spec_arm_futex (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_futex.ca_arm.sa_spec i m o = Sys.Kernel.Futex.Syscalls.futex_spec (in_arg i 0) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) i m o := rfl
@[arm_unfold] theorem ca_no_arm_futex : ca_no arm_futex = 98 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `futex` (98): every answer the checker accepts hands back the model it
was given — a wake's count or refusal, and a wait's -EAGAIN after the
four-byte read, which is a claim about what was READ and changes no
mapping: `futex_wait_setup` (kernel/futex/waitwake.c:591-664, Linux
v6.18.46) reads the word through `futex_get_value_locked` (a `static
inline` in kernel/futex/futex.h:332-341, same version) at :627 and
returns -EWOULDBLOCK on a mismatch at :642-645 having queued nothing and
written nothing — so the ledger is what it was.  The frame
lemma is `check_futex_frame`, the twin of Rocq's, stated beside the
checker in `Checks/Sys/Kernel/Futex/Syscalls.lean`, and this fact is
derived from it rather than re-proved, as that file's header asks. -/
theorem arm_futex_preserves_vm : arm_preserves_vm arm_futex :=
  arm_preserves_of_frame arm_futex (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Futex.Syscalls.check_futex_frame i _ _ _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## The model frame lemma

The two registry entries beside `vm_wf` read `m_fds` and `m_pipes`, which
`check_futex_frame` does not speak to.  What the checker does is stronger
than any per-field frame: it never builds a model at all, so the one it
accepts with IS the one it was handed, and both entries follow by
`congrArg`.  The tree's rule is that a checker's frame lemma lives beside
the checker, and this one belongs in `Checks/Sys/Kernel/Futex/Syscalls.lean`;
it is here because this ticket's edits under `lean/` are the arm file and
the Cases appends, and moving it there changes nothing but its home, as
`Checks/Arms/Kernel/Exit.lean` says of its own. -/

/-- `check_futex` accepts only with the model it was given.  Every leaf of
the checker, once its op, timeout, alignment, range, read and value tests
are split, is one of three things: a `check_ret_only … m []` or a
`check_ret_only_copyins … m []`, each accepting only with `m`
(`check_ret_only_model` and `check_ret_only_copyins_model`, beside the
checker), or `CheckUnmodeled`, which is no `CheckOk` at all.  The leaf
closer names the three and nothing else, so a checker branch that ever
built a model of its own would leave its goal open and fail this lemma
rather than pass it. -/
theorem check_futex_model_frame (i : SyscallInput) (uaddr op val utime : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Futex.Syscalls.check_futex i uaddr op val utime eff m
      = CheckOk m' evs) : m' = m := by
  unfold Checks.Sys.Kernel.Futex.Syscalls.check_futex
    Checks.Sys.Kernel.Futex.Syscalls.check_futex_wake_private
    Checks.Sys.Kernel.Futex.Syscalls.check_futex_wait_private at h
  repeat' split at h
  all_goals first
    | exact Checks.Sys.Kernel.Futex.Syscalls.check_ret_only_model _ _ _ _ _ _ h
    | exact Checks.Sys.Kernel.Futex.Syscalls.check_ret_only_copyins_model _ _ _ _ _ _ _ h
    | cases h

/-- `vm_wf` × `futex`: the ledger fact above. -/
theorem vm_wf_arm_futex : arm_preserves inv_vm_wf arm_futex :=
  Arms.arm_futex_preserves_vm

/-- `fd_table_unique` × `futex`: the accepted model is the one handed in,
so no descriptor is bound or dropped; a futex call touches no descriptor
(`SYSCALL_DEFINE6(futex)`, kernel/futex/syscalls.c:188-208, Linux
v6.18.46, takes none). -/
theorem fd_table_unique_arm_futex : arm_preserves inv_fd_table_unique arm_futex :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_futex (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg inv_fd_table_unique.inv_view (check_futex_model_frame i _ _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `futex`: likewise, no pipe is touched. -/
theorem pipes_within_capacity_arm_futex : arm_preserves inv_pipes_within_capacity arm_futex :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_futex (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg inv_pipes_within_capacity.inv_view
      (check_futex_model_frame i _ _ _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
