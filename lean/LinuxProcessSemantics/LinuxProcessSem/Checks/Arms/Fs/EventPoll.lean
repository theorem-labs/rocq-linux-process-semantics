import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.EventPoll
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Fs.EventPoll — epoll_create1, epoll_ctl and epoll_pwait on the checked surface

The registration of `Checks/Sys/Fs/EventPoll.lean`'s three checkers in
`checked_table`, in the one file that registration writes.
`tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files
under `Checks/Arms/`, one per checker twin, so that registering an arm
creates or edits no hub but this file; its docstring is the shape it reads
and what it refuses. The file holds three sections, each in the
namespace its declarations had when those three hubs were written by
hand, so that no name moved with the file:

- `Checks.Sys.Table`: the `CheckedArm`s (`arm_epoll_create1`,
  `arm_epoll_ctl` and `arm_epoll_pwait`)
  and their four `arm_unfold` lemmas each;
- `Checks.VmMapsDisjoint.Arms`: each arm's ledger fact,
  `arm_<name>_preserves_vm`, which `checked_table_preserves_vm`'s
  alternation names;
- `Checks.Invariants`: one `<invariant>_arm_<name>` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`, which
  `registry_preserves`'s alternation names.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arms are the rows of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table`, read at that commit, and it is the commit the checker
twin whose five theorems they are built from was read at. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### epoll_create1 (20) -/

/-- epoll_create1 (20).  THE FLAG WORD IS REGISTER `a0`, NARROWED TO
`int`.  riscv64's `__riscv_sys_epoll_create1` hands over `orig_a0`
(`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24,
Linux v6.18.46), and the wrapper casts it to the type
`SYSCALL_DEFINE1(epoll_create1, int, flags)` declares (fs/eventpoll.c:2473,
same version) through `__SC_CAST` (include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46); `do_epoll_create`
tests that `int` against `~EPOLL_CLOEXEC` (fs/eventpoll.c:2439-2440, same
version).  `Sys.Syscall.flag32 (in_arg i 0)` is that reading, applied here at
the boundary as Rocq's `arm_epoll_create1` applies it.  `ca_arm` is the term
`Sys/Registry/Fs/EventPoll.lean`'s row builds, which `checked_table_arms`
checks.  The ledger fact this arm owes `checked_table_preserves_vm` is
`check_epoll_create1_frame`, beside the checker. -/
def arm_epoll_create1 : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 20 (fun i => Sys.Fs.EventPoll.epoll_create1_spec
    (Sys.Syscall.flag32 (in_arg i 0)) i)
  ca_check := fun i eff m => Checks.Sys.Fs.EventPoll.check_epoll_create1
    (Sys.Syscall.flag32 (in_arg i 0)) eff m
  ca_witness := fun i m => Checks.Sys.Fs.EventPoll.epoll_create1_witness
    (Sys.Syscall.flag32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.EventPoll.check_epoll_create1_sound_ok
      (Sys.Syscall.flag32 (in_arg i 0)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.EventPoll.check_epoll_create1_sound_unmodeled
      (Sys.Syscall.flag32 (in_arg i 0)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.EventPoll.check_epoll_create1_complete_ok
      (Sys.Syscall.flag32 (in_arg i 0)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.EventPoll.check_epoll_create1_complete_unmodeled
      (Sys.Syscall.flag32 (in_arg i 0)) m eff i h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.EventPoll.epoll_create1_witness_ok (Sys.Syscall.flag32 (in_arg i 0)) i m

@[arm_unfold] theorem ca_check_arm_epoll_create1 (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_epoll_create1.ca_check i eff m
      = Checks.Sys.Fs.EventPoll.check_epoll_create1
          (Sys.Syscall.flag32 (in_arg i 0)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_epoll_create1 (i : SyscallInput) (m : Model) :
    arm_epoll_create1.ca_witness i m
      = Checks.Sys.Fs.EventPoll.epoll_create1_witness (Sys.Syscall.flag32 (in_arg i 0)) m := rfl
@[arm_unfold] theorem sa_spec_arm_epoll_create1 (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_epoll_create1.ca_arm.sa_spec i m o
      = Sys.Fs.EventPoll.epoll_create1_spec (Sys.Syscall.flag32 (in_arg i 0)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_epoll_create1 : ca_no arm_epoll_create1 = 20 := rfl

/- ### epoll_ctl (21) -/

/-- epoll_ctl (21).  `epfd`, `op` AND `fd` ARE REGISTERS `a0`, `a1` AND `a2`,
EACH NARROWED TO `int`; THE EVENT POINTER `a3` ARRIVES WHOLE.  The registers
come over in order (`SC_RISCV_REGS_TO_ARGS`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46), cast through
`__SC_CAST` (include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, same version) to the types
`SYSCALL_DEFINE4(epoll_ctl, int, epfd, int, op, int, fd, struct epoll_event
__user *, event)` declares (fs/eventpoll.c:2658-2659, Linux v6.18.46); the
pointer is 64 bits wide on riscv64, so the cast is the identity on it.
`Sys.Syscall.fd32` on `a0` and `a2` and `Sys.Syscall.int32` on `a1` are those
readings, applied here as Rocq's `arm_epoll_ctl` applies them.  The checker
and the witness take the input too, because the arm reads the event struct
through it.  `ca_arm` is the term `Sys/Registry/Fs/EventPoll.lean`'s row
builds, which `checked_table_arms` checks.  The ledger fact this arm owes
`checked_table_preserves_vm` is `check_epoll_ctl_frame`, beside the checker. -/
def arm_epoll_ctl : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 21 (fun i => Sys.Fs.EventPoll.epoll_ctl_spec
    (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1))
    (Sys.Syscall.fd32 (in_arg i 2)) (in_arg i 3) i)
  ca_check := fun i eff m => Checks.Sys.Fs.EventPoll.check_epoll_ctl
    i (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1))
    (Sys.Syscall.fd32 (in_arg i 2)) (in_arg i 3) eff m
  ca_witness := fun i m => Checks.Sys.Fs.EventPoll.epoll_ctl_witness
    (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1))
    (Sys.Syscall.fd32 (in_arg i 2)) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.EventPoll.check_epoll_ctl_sound_ok
      i (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1))
      (Sys.Syscall.fd32 (in_arg i 2)) (in_arg i 3) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.EventPoll.check_epoll_ctl_sound_unmodeled
      i (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1))
      (Sys.Syscall.fd32 (in_arg i 2)) (in_arg i 3) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.EventPoll.check_epoll_ctl_complete_ok
      i (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1))
      (Sys.Syscall.fd32 (in_arg i 2)) (in_arg i 3) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.EventPoll.check_epoll_ctl_complete_unmodeled
      i (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1))
      (Sys.Syscall.fd32 (in_arg i 2)) (in_arg i 3) m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.EventPoll.epoll_ctl_witness_ok (Sys.Syscall.fd32 (in_arg i 0))
      (Sys.Syscall.int32 (in_arg i 1))
      (Sys.Syscall.fd32 (in_arg i 2)) (in_arg i 3) i m

@[arm_unfold] theorem ca_check_arm_epoll_ctl (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_epoll_ctl.ca_check i eff m
      = Checks.Sys.Fs.EventPoll.check_epoll_ctl
          i (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1))
          (Sys.Syscall.fd32 (in_arg i 2)) (in_arg i 3) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_epoll_ctl (i : SyscallInput) (m : Model) :
    arm_epoll_ctl.ca_witness i m
      = Checks.Sys.Fs.EventPoll.epoll_ctl_witness (Sys.Syscall.fd32 (in_arg i 0))
          (Sys.Syscall.int32 (in_arg i 1))
          (Sys.Syscall.fd32 (in_arg i 2)) (in_arg i 3) i m := rfl
@[arm_unfold] theorem sa_spec_arm_epoll_ctl (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_epoll_ctl.ca_arm.sa_spec i m o
      = Sys.Fs.EventPoll.epoll_ctl_spec (Sys.Syscall.fd32 (in_arg i 0))
          (Sys.Syscall.int32 (in_arg i 1))
          (Sys.Syscall.fd32 (in_arg i 2)) (in_arg i 3) i m o := rfl
@[arm_unfold] theorem ca_no_arm_epoll_ctl : ca_no arm_epoll_ctl = 21 := rfl

/- ### epoll_pwait (22) -/

/-- epoll_pwait (22).  `epfd` (`a0`) AND `maxevents` (`a2`) ARE NARROWED TO
`int`; `events` (`a1`), `sigmask` (`a4`) AND `sigsetsize` (`a5`) ARRIVE
WHOLE; `timeout` (`a3`) IS NOT HANDED TO THE SPEC.  The registers come over in
order (`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24,
Linux v6.18.46), cast through `__SC_CAST` (include/linux/syscalls.h:132,
applied at arch/riscv/include/asm/syscall_wrapper.h:88, same version) to the
types `SYSCALL_DEFINE6(epoll_pwait, int, epfd, struct epoll_event __user *,
events, int, maxevents, int, timeout, const sigset_t __user *, sigmask,
size_t, sigsetsize)` declares (fs/eventpoll.c:2774-2776, Linux v6.18.46); the
two pointers and the `size_t` are 64 bits wide on riscv64.  `timeout` is
turned into a deadline by `ep_timeout_to_timespec` (fs/eventpoll.c:2118-2136,
same version), which has no error return, and that deadline is read only in
the last statement of `do_epoll_wait` (fs/eventpoll.c:2715-2738, Linux
v6.18.46), its call into `ep_poll`, past every check the spec answers.
`Sys.Syscall.fd32` on `a0` and `Sys.Syscall.int32` on `a2` are the readings
of the two `int`s, applied here as Rocq's `arm_epoll_pwait` applies them.
`ca_arm` is the term `Sys/Registry/Fs/EventPoll.lean`'s row builds, which
`checked_table_arms` checks.  The ledger fact this arm owes
`checked_table_preserves_vm` is `check_epoll_pwait_frame`, beside the checker. -/
def arm_epoll_pwait : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 22 (fun i => Sys.Fs.EventPoll.epoll_pwait_spec
    (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1)
    (Sys.Syscall.int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i)
  ca_check := fun i eff m => Checks.Sys.Fs.EventPoll.check_epoll_pwait
    i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1)
    (Sys.Syscall.int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) eff m
  ca_witness := fun i m => Checks.Sys.Fs.EventPoll.epoll_pwait_witness
    (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1)
    (Sys.Syscall.int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.EventPoll.check_epoll_pwait_sound_ok
      i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1)
      (Sys.Syscall.int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.EventPoll.check_epoll_pwait_sound_unmodeled
      i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1)
      (Sys.Syscall.int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.EventPoll.check_epoll_pwait_complete_ok
      i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1)
      (Sys.Syscall.int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.EventPoll.check_epoll_pwait_complete_unmodeled
      i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1)
      (Sys.Syscall.int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.EventPoll.epoll_pwait_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1)
      (Sys.Syscall.int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i m

@[arm_unfold] theorem ca_check_arm_epoll_pwait (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_epoll_pwait.ca_check i eff m
      = Checks.Sys.Fs.EventPoll.check_epoll_pwait
          i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1)
          (Sys.Syscall.int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_epoll_pwait (i : SyscallInput) (m : Model) :
    arm_epoll_pwait.ca_witness i m
      = Checks.Sys.Fs.EventPoll.epoll_pwait_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1)
          (Sys.Syscall.int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i m := rfl
@[arm_unfold] theorem sa_spec_arm_epoll_pwait (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_epoll_pwait.ca_arm.sa_spec i m o
      = Sys.Fs.EventPoll.epoll_pwait_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1)
          (Sys.Syscall.int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i m o := rfl
@[arm_unfold] theorem ca_no_arm_epoll_pwait : ca_no arm_epoll_pwait = 22 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `epoll_create1` (20): every answer the checker accepts is accepted with
the model it was handed — the spec's outcome is a return value alone — so
the ledger is what it was (`check_epoll_create1_frame`, stated beside the
checker in `Checks/Sys/Fs/EventPoll.lean`, Rocq's
`check_epoll_create1_frame`). -/
theorem arm_epoll_create1_preserves_vm : arm_preserves_vm arm_epoll_create1 :=
  arm_preserves_of_frame arm_epoll_create1 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Fs.EventPoll.check_epoll_create1_frame _ eff m m' evs h)

/-- `epoll_ctl` (21): likewise (`check_epoll_ctl_frame`, same file, Rocq's
`check_epoll_ctl_frame`). -/
theorem arm_epoll_ctl_preserves_vm : arm_preserves_vm arm_epoll_ctl :=
  arm_preserves_of_frame arm_epoll_ctl (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Fs.EventPoll.check_epoll_ctl_frame _ _ _ _ _ eff m m' evs h)

/-- `epoll_pwait` (22): likewise (`check_epoll_pwait_frame`, same file, Rocq's
`check_epoll_pwait_frame`). -/
theorem arm_epoll_pwait_preserves_vm : arm_preserves_vm arm_epoll_pwait :=
  arm_preserves_of_frame arm_epoll_pwait (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Fs.EventPoll.check_epoll_pwait_frame _ _ _ _ _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## The model frame the two descriptor-state facts rest on

The two registry entries beside `vm_wf` read the `m_fd` subsystem.  The
three checkers accept only `CheckOk m []`, through `check_ret_only`,
with the model handed in.  One lemma per
checker saying exactly that answers both entries.  The file
`Checks/Sys/Fs/EventPoll.lean` is not this registration's to edit, so the
lemmas stand here.  Rocq registers no `m_fd` invariant, so none has a twin. -/

/-- `check_epoll_create1` accepts only with the model it was handed. -/
theorem check_epoll_create1_keeps_the_model (flags32 : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.EventPoll.check_epoll_create1 flags32 eff m = CheckOk m' evs) :
    m' = m := by
  unfold Checks.Sys.Fs.EventPoll.check_epoll_create1 at h
  split at h
  · cases h
  · exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1

/-- `check_epoll_ctl` accepts only with the model it was handed. -/
theorem check_epoll_ctl_keeps_the_model (i : SyscallInput) (epfd op32 tfd ev : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.EventPoll.check_epoll_ctl i epfd op32 tfd ev eff m = CheckOk m' evs) :
    m' = m := by
  unfold Checks.Sys.Fs.EventPoll.check_epoll_ctl at h
  split at h
  · cases h
  · exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1

/-- `check_epoll_pwait` accepts only with the model it was handed. -/
theorem check_epoll_pwait_keeps_the_model (i : SyscallInput)
    (epfd events maxevents32 sigmask sigsetsize : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.EventPoll.check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize
      eff m = CheckOk m' evs) :
    m' = m := by
  unfold Checks.Sys.Fs.EventPoll.check_epoll_pwait at h
  split at h
  · cases h
  · exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1

/-- `vm_wf` × `epoll_create1`: the ledger fact above. -/
theorem vm_wf_arm_epoll_create1 : arm_preserves inv_vm_wf arm_epoll_create1 :=
  Arms.arm_epoll_create1_preserves_vm

/-- `fd_table_unique` × `epoll_create1`: the arm accepts only with the
model it was handed, so the table is the one handed in. -/
theorem fd_table_unique_arm_epoll_create1 :
    arm_preserves inv_fd_table_unique arm_epoll_create1 :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_epoll_create1 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    simp only [check_epoll_create1_keeps_the_model _ eff m m' evs h])

/-- `pipes_within_capacity` × `epoll_create1`: the arm accepts only with the
model it was handed, so the pipe state is the one handed in. -/
theorem pipes_within_capacity_arm_epoll_create1 :
    arm_preserves inv_pipes_within_capacity arm_epoll_create1 :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_epoll_create1 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    simp only [check_epoll_create1_keeps_the_model _ eff m m' evs h])

/-- `vm_wf` × `epoll_ctl`: the ledger fact above. -/
theorem vm_wf_arm_epoll_ctl : arm_preserves inv_vm_wf arm_epoll_ctl :=
  Arms.arm_epoll_ctl_preserves_vm

/-- `fd_table_unique` × `epoll_ctl`: the arm accepts only with the
model it was handed, so the table is the one handed in. -/
theorem fd_table_unique_arm_epoll_ctl :
    arm_preserves inv_fd_table_unique arm_epoll_ctl :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_epoll_ctl (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    simp only [check_epoll_ctl_keeps_the_model _ _ _ _ _ eff m m' evs h])

/-- `pipes_within_capacity` × `epoll_ctl`: the arm accepts only with the
model it was handed, so the pipe state is the one handed in. -/
theorem pipes_within_capacity_arm_epoll_ctl :
    arm_preserves inv_pipes_within_capacity arm_epoll_ctl :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_epoll_ctl (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    simp only [check_epoll_ctl_keeps_the_model _ _ _ _ _ eff m m' evs h])

/-- `vm_wf` × `epoll_pwait`: the ledger fact above. -/
theorem vm_wf_arm_epoll_pwait : arm_preserves inv_vm_wf arm_epoll_pwait :=
  Arms.arm_epoll_pwait_preserves_vm

/-- `fd_table_unique` × `epoll_pwait`: the arm accepts only with the
model it was handed, so the table is the one handed in. -/
theorem fd_table_unique_arm_epoll_pwait :
    arm_preserves inv_fd_table_unique arm_epoll_pwait :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_epoll_pwait (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    simp only [check_epoll_pwait_keeps_the_model _ _ _ _ _ _ eff m m' evs h])

/-- `pipes_within_capacity` × `epoll_pwait`: the arm accepts only with the
model it was handed, so the pipe state is the one handed in. -/
theorem pipes_within_capacity_arm_epoll_pwait :
    arm_preserves inv_pipes_within_capacity arm_epoll_pwait :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_epoll_pwait (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    simp only [check_epoll_pwait_keeps_the_model _ _ _ _ _ _ eff m m' evs h])

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
