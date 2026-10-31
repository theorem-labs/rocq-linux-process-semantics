import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.EventFd
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Fs.EventFd — eventfd2 on the checked surface

The registration of `Checks/Sys/Fs/EventFd.lean`'s checker in
`checked_table`, in the one file that registration writes.
`tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files
under `Checks/Arms/`, one per checker twin, so that registering an arm
creates or edits no hub but this file; its docstring is the shape it reads
and what it refuses. The file holds three sections, each in the
namespace its declarations had when those three hubs were written by
hand, so that no name moved with the file:

- `Checks.Sys.Table`: the `CheckedArm` (`arm_eventfd2`) and its four
  `arm_unfold` lemmas;
- `Checks.VmMapsDisjoint.Arms`: the arm's ledger fact,
  `arm_<name>_preserves_vm`, which `checked_table_preserves_vm`'s
  alternation names;
- `Checks.Invariants`: one `<invariant>_arm_<name>` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`, which
  `registry_preserves`'s alternation names.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arms are the rows of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table`, read at that commit. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### eventfd2 (19) -/

/-- eventfd2 (19).  THE FLAG WORD IS REGISTER `a1`, CUT TO ITS LOW 32
BITS, AND THE COUNTER IN `a0` IS NOT READ.  riscv64's
`__riscv_sys_eventfd2` hands the registers over in order, `orig_a0` then
`a1` (`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24,
Linux v6.18.46), and the wrapper narrows each to the type
`SYSCALL_DEFINE2(eventfd2, unsigned int, count, int, flags)` declares
(fs/eventfd.c:423, same version) through `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46), so
`do_eventfd` gates the `int` it receives (fs/eventfd.c:390-391, Linux
v6.18.46) and stores the counter below the gate without testing it (line
399).  `Sys.Syscall.flag32 (in_arg i 1)` is
that reading, applied here at the boundary as Rocq's `arm_eventfd2`
applies it, so the checker and the witness receive the narrowed word and
neither narrows again — each gates the whole word it is handed, which
`Checks/Cases/Checks/Sys/Fs/EventFd.lean` pins.  Reading `a0` would not
be a decline but a wrong answer: `eventfd2(2, 0)` would have its counter
tested as bit 1 and take the -EINVAL, where Linux hands back a
descriptor.  (Rocq's docstring gives `eventfd2(1, 0)` for that example,
but 1 is `EFD_SEMAPHORE`, inside the mask, so a swapped arm would decline
that call rather than refuse it.)  `ca_arm` is the term
`Sys/Registry/Fs/EventFd.lean`'s row builds, which `checked_table_arms`
checks.  The ledger fact this arm owes `checked_table_preserves_vm`
is `check_eventfd2_frame`, beside the checker. -/
-- The host-subset decline is inside the checker and witness, after this
-- flag32 reading: 2^32 + 2^14 must reach the SPARC decline as 2^14.
-- Sys/Fs/EventFd.lean gives the source argument for the host-subset decline.
def arm_eventfd2 : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 19
    (fun i => Sys.Fs.EventFd.eventfd2_spec (Sys.Syscall.flag32 (in_arg i 1)) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.EventFd.check_eventfd2 (Sys.Syscall.flag32 (in_arg i 1)) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.EventFd.eventfd2_witness (Sys.Syscall.flag32 (in_arg i 1)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.EventFd.check_eventfd2_sound_ok (Sys.Syscall.flag32 (in_arg i 1)) eff m m' evs
      i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.EventFd.check_eventfd2_sound_unmodeled (Sys.Syscall.flag32 (in_arg i 1)) eff m
      i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.EventFd.check_eventfd2_complete_ok (Sys.Syscall.flag32 (in_arg i 1)) eff m m'
      evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.EventFd.check_eventfd2_complete_unmodeled (Sys.Syscall.flag32 (in_arg i 1)) m
      i eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.EventFd.eventfd2_witness_ok (Sys.Syscall.flag32 (in_arg i 1)) i m

@[arm_unfold] theorem ca_check_arm_eventfd2 (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_eventfd2.ca_check i eff m
      = Checks.Sys.Fs.EventFd.check_eventfd2 (Sys.Syscall.flag32 (in_arg i 1)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_eventfd2 (i : SyscallInput) (m : Model) :
    arm_eventfd2.ca_witness i m
      = Checks.Sys.Fs.EventFd.eventfd2_witness (Sys.Syscall.flag32 (in_arg i 1)) m := rfl
@[arm_unfold] theorem sa_spec_arm_eventfd2 (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_eventfd2.ca_arm.sa_spec i m o
      = Sys.Fs.EventFd.eventfd2_spec (Sys.Syscall.flag32 (in_arg i 1)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_eventfd2 : ca_no arm_eventfd2 = 19 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `eventfd2` (19): on either answer the checker accepts — the -EINVAL
`do_eventfd` returns before it allocates anything (fs/eventfd.c:390-393,
Linux v6.18.46), or the -ENOSYS kernel/sys_ni.c `sys_ni_syscall` returns
on a kernel without CONFIG_EVENTFD (Linux v6.18.46) — the accepted model
is the model handed in, so the ledger is what it was
(`check_eventfd2_frame`, stated beside the checker in
`Checks/Sys/Fs/EventFd.lean`). -/
theorem arm_eventfd2_preserves_vm : arm_preserves_vm arm_eventfd2 :=
  arm_preserves_of_frame arm_eventfd2 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Fs.EventFd.check_eventfd2_frame _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `vm_wf` × `eventfd2`: the ledger fact above. -/
theorem vm_wf_arm_eventfd2 : arm_preserves inv_vm_wf arm_eventfd2 :=
  Arms.arm_eventfd2_preserves_vm

/-- `fd_table_unique` × `eventfd2`: neither accepted answer reserves or
binds a descriptor — the -EINVAL `do_eventfd` returns before either
operation (fs/eventfd.c:390-391, :405 and :416, Linux v6.18.46), or the
-ENOSYS from kernel/sys_ni.c `sys_ni_syscall` (Linux v6.18.46), which
never enters fs/eventfd.c — and the gate-passing word that would bind
one is declined; the frame is stated beside the checker. -/
theorem fd_table_unique_arm_eventfd2 : arm_preserves inv_fd_table_unique arm_eventfd2 :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_eventfd2 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table
      (Checks.Sys.Fs.EventFd.check_eventfd2_fd_state_frame _ eff m m' evs h))

/-- `pipes_within_capacity` × `eventfd2`: no pipe is touched. -/
theorem pipes_within_capacity_arm_eventfd2 :
    arm_preserves inv_pipes_within_capacity arm_eventfd2 :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_eventfd2 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes
      (Checks.Sys.Fs.EventFd.check_eventfd2_fd_state_frame _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
