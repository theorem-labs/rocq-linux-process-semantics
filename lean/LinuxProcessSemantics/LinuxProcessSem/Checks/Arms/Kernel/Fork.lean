import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Fork
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Kernel.Fork — kernel/fork.c's arms on the checked surface

The registration of `Checks/Sys/Kernel/Fork.lean`'s checkers in
`checked_table`, in the one file that registration writes: each arm of
that checker twin is registered here by the ticket that registers it.
`tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files
under `Checks/Arms/`, one per checker twin, so that registering an arm
creates or edits no hub but this file; its docstring is the shape it reads
and what it refuses. The file holds three sections, each in the
namespace its declarations had when those three hubs were written by
hand, so that no name moved with the file:

- `Checks.Sys.Table`: each `CheckedArm` (`arm_<name>`) and its four
  `arm_unfold` lemmas;
- `Checks.VmMapsDisjoint.Arms`: the arm's ledger fact,
  `arm_<name>_preserves_vm`, which `checked_table_preserves_vm`'s
  alternation names;
- `Checks.Invariants`: one `<invariant>_arm_<name>` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`, which
  `registry_preserves`'s alternation names.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains, and
`arm_set_tid_address` was read at it rather than at the `f44244ad6b80` the
ticket that registered 96 names, for the reason given there. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### set_tid_address (96) -/

/-- set_tid_address (96).  THE ARM READS NO REGISTER.  The one argument,
`tidptr` in `a0`, is stored in `current->clear_child_tid` and nothing
else is done with it before the call returns `task_pid_vnr(current)`
(`SYSCALL_DEFINE1(set_tid_address, int __user *, tidptr)`,
kernel/fork.c:1747-1752, Linux v6.18.46): no check, no dereference, no
path that depends on its value.  So the spec, the checker and the witness
are applied with no argument of the input, as Rocq's `arm_set_tid_address`
applies them, and a trace's `tidptr` cannot move the verdict — which
`Checks/Cases/Checks/Sys/Kernel/Fork.lean` pins through `check_syscall`
at every input numbered 96.  The stored pointer is read back
in two places.  `mm_release` writes 0 through it and wakes a futex there
when the task exits or execs (kernel/fork.c:1436-1447, Linux v6.18.46),
behind `atomic_read(&mm->mm_users) > 1`; the model keeps no
`clear_child_tid`.  The write can fire on a task that holds this arm's
tid, although the spec's docstring (`set_tid_address_spec`,
`Sys/Kernel/Fork.lean`) says `mm_users` is 1 and it cannot:
`get_task_mm` takes an `mmget` (kernel/fork.c:1330-1344, Linux v6.18.46),
which a read of /proc/<pid>/cmdline (`get_task_cmdline`, fs/proc/base.c,
Linux v6.18.46) and process_vm_readv (`mm_access`, kernel/fork.c, Linux
v6.18.46) reach, and MGLRU (`get_next_mm`, mm/vmscan.c, Linux v6.18.46)
and swapoff (`try_to_unuse`, mm/swapfile.c, Linux v6.18.46) raise
`mm_users` too.  It stays out of the model because no trace the model
judges can show it, for a reason on each branch.  On exit the store and
the wake run in `exit_mm` (kernel/exit.c:556-560, Linux v6.18.46), called
from `do_exit` (kernel/exit.c:965, Linux v6.18.46), which never returns,
so the task makes no syscall after them.  On exec they run inside the
exec, on the old mm, before the task switches to the new one
(`exec_mmap`, fs/exec.c:853-854 and 879, Linux v6.18.46); the model has no
exec, since 221 and 281 have no arm (`Checks/ProcessCreation.lean` pins
both declines), so the checker declines the exec itself and judges nothing
after it, and the arm that registers either number reopens this branch.
And the wake is a shared one: `mm_release` passes `FUTEX_WAKE` with no
`FUTEX_PRIVATE_FLAG` (kernel/fork.c:1443-1444), so `futex_to_flags` sets
`FLAGS_SHARED` (kernel/futex/futex.h:49-50, Linux v6.18.46), and
`get_futex_key` keys a page that is not anonymous on its inode
(kernel/futex/core.c:730-765, Linux v6.18.46), so a waiter in another
process that maps the page can be woken.  That waiter is never this task,
which is inside its own exit or exec, and the model judges this task's
trace alone.  And
`prctl(PR_GET_TID_ADDRESS)` copies it out to the caller
(`prctl_get_tid_address`, kernel/sys.c:2336-2339, reached at 2676-2677,
Linux v6.18.46, under `CONFIG_CHECKPOINT_RESTORE`; the stub at 2341-2344
answers `-EINVAL` without it), which the model cannot answer without the
pointer it drops here.  It does not have to, because `prctl_spec`
declines every option but `PR_CAPBSET_READ` (`Sys/Kernel/Sys.lean`).  An
arm that models `PR_GET_TID_ADDRESS` (40) is what ends that argument,
and it would have to thread `tidptr` through this one.
`ca_arm` is the term `Sys/Registry/Kernel/Fork.lean`'s row builds, which
`checked_table_arms` checks. -/
def arm_set_tid_address : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 96 (fun i => Sys.Kernel.Fork.set_tid_address_spec i)
  ca_check := fun _ eff m => Checks.Sys.Kernel.Fork.check_set_tid_address eff m
  ca_witness := fun _ m => Checks.Sys.Kernel.Fork.set_tid_address_witness m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Fork.check_set_tid_address_sound_ok i eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Fork.check_set_tid_address_sound_unmodeled i eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Fork.check_set_tid_address_complete_ok i eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Fork.check_set_tid_address_complete_unmodeled i m eff h
  ca_receptive := fun i m => Checks.Sys.Kernel.Fork.set_tid_address_witness_ok i m

@[arm_unfold] theorem ca_check_arm_set_tid_address (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    arm_set_tid_address.ca_check i eff m = Checks.Sys.Kernel.Fork.check_set_tid_address eff m :=
  rfl
@[arm_unfold] theorem ca_witness_arm_set_tid_address (i : SyscallInput) (m : Model) :
    arm_set_tid_address.ca_witness i m = Checks.Sys.Kernel.Fork.set_tid_address_witness m := rfl
@[arm_unfold] theorem sa_spec_arm_set_tid_address (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_set_tid_address.ca_arm.sa_spec i m o = Sys.Kernel.Fork.set_tid_address_spec i m o := rfl
@[arm_unfold] theorem ca_no_arm_set_tid_address : ca_no arm_set_tid_address = 96 := rfl

/- ### clone (220) -/

/-- clone (220).  The argument is register `a0`, READ WHOLE.  riscv64
selects `CLONE_BACKWARDS` (arch/riscv/Kconfig:97, Linux v6.18.46), so the
prototype is `SYSCALL_DEFINE5(clone, unsigned long, clone_flags, unsigned
long, newsp, int __user *, parent_tidptr, unsigned long, tls, int __user
*, child_tidptr)` (kernel/fork.c:2720-2723, Linux v6.18.46), and the
wrapper hands it `orig_a0` first (`SC_RISCV_REGS_TO_ARGS`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46).  The
body keeps only `lower_32_bits(clone_flags)` (kernel/fork.c:2743, :2747,
Linux v6.18.46), so a register whose low 32 bits are `SIGCHLD` is a fork
to Linux whatever its upper half holds; the checker's gate,
`clone_fork_flags_b`, compares the whole 64-bit word and declines every
such word but `SIGCHLD` itself.  That is the fail-closed direction, and
handing the checker the register unnarrowed is what keeps the arm on it:
an arm passing the low 32 bits would answer a word the spec declines,
and `ca_complete_unmodeled` would not close.  The other four registers
are not read.  With the one word the gate admits, no flag names
`parent_tidptr`, `tls` or `child_tidptr` — `kernel_clone`'s
`CLONE_PARENT_SETTID` store (kernel/fork.c:2626, Linux v6.18.46) and
`copy_process`'s `CLONE_CHILD_SETTID` pointer (:2040) are behind flags
the word does not carry — and `newsp` reaches the CHILD's `sp` alone
(`copy_thread`, arch/riscv/kernel/process.c:251-252, Linux v6.18.46),
which the parent's answer cannot show.
`Checks/Cases/Checks/Sys/Kernel/Fork.lean` pins both halves through
`check_syscall`.  The five proof fields are the C ticket's theorems
applied at `in_arg i 0`; `ca_arm` is the term
`Sys/Registry/Kernel/Fork.lean`'s row builds, which `checked_table_arms`
checks. -/
def arm_clone : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 220 (fun i => Sys.Kernel.Fork.clone_spec (in_arg i 0) i)
  ca_check := fun i eff m => Checks.Sys.Kernel.Fork.check_clone (in_arg i 0) eff m
  ca_witness := fun i m => Checks.Sys.Kernel.Fork.clone_witness (in_arg i 0) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Fork.check_clone_sound_ok i (in_arg i 0) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Fork.check_clone_sound_unmodeled i (in_arg i 0) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Fork.check_clone_complete_ok i (in_arg i 0) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Fork.check_clone_complete_unmodeled i (in_arg i 0) m eff h
  ca_receptive := fun i m => Checks.Sys.Kernel.Fork.clone_witness_ok i (in_arg i 0) m

@[arm_unfold] theorem ca_check_arm_clone (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_clone.ca_check i eff m = Checks.Sys.Kernel.Fork.check_clone (in_arg i 0) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_clone (i : SyscallInput) (m : Model) :
    arm_clone.ca_witness i m = Checks.Sys.Kernel.Fork.clone_witness (in_arg i 0) m := rfl
@[arm_unfold] theorem sa_spec_arm_clone (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_clone.ca_arm.sa_spec i m o = Sys.Kernel.Fork.clone_spec (in_arg i 0) i m o := rfl
@[arm_unfold] theorem ca_no_arm_clone : ca_no arm_clone = 220 := rfl

/- ### clone3 (435) -/

/-- clone3 (435).  The arguments are `a0` and `a1`, in that order:
`SYSCALL_DEFINE2(clone3, struct clone_args __user *, uargs, size_t, size)`
(kernel/fork.c:2892, Linux v6.18.46) takes `uargs` from `orig_a0` and
`size` from `a1` (`SC_RISCV_REGS_TO_ARGS`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46), and
both are 64-bit, so neither is narrowed on the way in and the checker
reads each register whole.  The arm also hands the checker the input
itself, for the struct: `check_clone3` reads the 88 bytes at `uargs`
from `in_mem`, the read `copy_clone_args_from_user` makes
(kernel/fork.c:2756-2823, Linux v6.18.46).  The five proof fields are the
C ticket's theorems applied at `i`, `in_arg i 0` and `in_arg i 1`;
`ca_arm` is the term `Sys/Registry/Kernel/Fork.lean`'s row builds. -/
def arm_clone3 : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 435
    (fun i => Sys.Kernel.Fork.clone3_spec (in_arg i 0) (in_arg i 1) i)
  ca_check := fun i eff m =>
    Checks.Sys.Kernel.Fork.check_clone3 i (in_arg i 0) (in_arg i 1) eff m
  ca_witness := fun i m =>
    Checks.Sys.Kernel.Fork.clone3_witness i (in_arg i 0) (in_arg i 1) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Fork.check_clone3_sound_ok i (in_arg i 0) (in_arg i 1) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Kernel.Fork.check_clone3_sound_unmodeled i (in_arg i 0) (in_arg i 1) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Kernel.Fork.check_clone3_complete_ok i (in_arg i 0) (in_arg i 1) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Kernel.Fork.check_clone3_complete_unmodeled i (in_arg i 0) (in_arg i 1) m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Kernel.Fork.clone3_witness_ok i (in_arg i 0) (in_arg i 1) m

@[arm_unfold] theorem ca_check_arm_clone3 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_clone3.ca_check i eff m
      = Checks.Sys.Kernel.Fork.check_clone3 i (in_arg i 0) (in_arg i 1) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_clone3 (i : SyscallInput) (m : Model) :
    arm_clone3.ca_witness i m
      = Checks.Sys.Kernel.Fork.clone3_witness i (in_arg i 0) (in_arg i 1) m := rfl
@[arm_unfold] theorem sa_spec_arm_clone3 (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_clone3.ca_arm.sa_spec i m o
      = Sys.Kernel.Fork.clone3_spec (in_arg i 0) (in_arg i 1) i m o := rfl
@[arm_unfold] theorem ca_no_arm_clone3 : ca_no arm_clone3 = 435 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `set_tid_address` (96): the accepted model is the model handed in, or
`with_tid ret` of it on a first call, which rebuilds the process state
alone, so the ledger is what it was (`check_set_tid_address_frame`, stated
beside the checker in `Checks/Sys/Kernel/Fork.lean`; Rocq's
`VmMapsDisjoint.check_set_tid_address_frame`). -/
theorem arm_set_tid_address_preserves_vm : arm_preserves_vm arm_set_tid_address :=
  arm_preserves_of_frame arm_set_tid_address (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Fork.check_set_tid_address_frame eff m m' evs h)

/-- `clone` (220): the accepted model is the model handed in (an errno)
or `with_children` of it (a pid), which rebuilds the process state alone,
so the ledger is what it was (`check_clone_frame`, stated beside the
checker in `Checks/Sys/Kernel/Fork.lean`; Rocq's
`VmMapsDisjoint.check_clone_frame`). -/
theorem arm_clone_preserves_vm : arm_preserves_vm arm_clone :=
  arm_preserves_of_frame arm_clone (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Fork.check_clone_frame _ eff m m' evs h)

/-- `clone3` (435): the same two models past the struct gates
(`check_clone3_frame`; Rocq's `VmMapsDisjoint.check_clone3_frame`). -/
theorem arm_clone3_preserves_vm : arm_preserves_vm arm_clone3 :=
  arm_preserves_of_frame arm_clone3 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Kernel.Fork.check_clone3_frame i _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## The descriptor-state frame lemma

The two registry entries beside `vm_wf` read the `m_fd` subsystem, so one
frame lemma over the whole record answers both.  The tree's rule is that a
checker's frame lemma lives beside the checker, in
`Checks/Sys/Kernel/Fork.lean`, which this ticket does not edit, so it is
stated here, as `check_exit_fd_state_frame` is in
`Checks/Arms/Kernel/Exit.lean` (written beside the registry in
`Checks/Invariants.lean` by the registry ticket, I3 (#1096), and moved
into the arm file by T80's file split, #1255; neither is a conformance
ticket).  Moving it beside the checker would change nothing but its home
only if it kept its `Checks.Invariants` name, which the two entries
below call it by; the arms that register 172 and 178 reuse this checker
and so would reuse the lemma from wherever it lives.  The Rocq tree
registers no `m_fd` invariant, so the lemma has no Rocq twin. -/

/-- `check_set_tid_address` hands back the model it was handed, or
`with_tid ret` of it, and `with_tid` rebuilds the process state and
nothing else (`State/Model.lean`), so the descriptor subsystem is the one
it was handed. -/
theorem check_set_tid_address_fd_state_frame (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Kernel.Fork.check_set_tid_address eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Fork.check_set_tid_address at h
  vm_frame h

/-- `vm_wf` × `set_tid_address`: the ledger fact above. -/
theorem vm_wf_arm_set_tid_address : arm_preserves inv_vm_wf arm_set_tid_address :=
  Arms.arm_set_tid_address_preserves_vm

/-- `fd_table_unique` × `set_tid_address`: the call opens and closes no
descriptor — it stores a pointer and returns a pid (kernel/fork.c:1747-1752,
Linux v6.18.46) — and the checker's accepted model keeps the table. -/
theorem fd_table_unique_arm_set_tid_address :
    arm_preserves inv_fd_table_unique arm_set_tid_address :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_set_tid_address
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_table (check_set_tid_address_fd_state_frame eff m m' evs h))

/-- `pipes_within_capacity` × `set_tid_address`: no pipe is touched. -/
theorem pipes_within_capacity_arm_set_tid_address :
    arm_preserves inv_pipes_within_capacity arm_set_tid_address :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_set_tid_address
    (fun i eff m m' evs h => by
      simp only [arm_unfold] at h
      exact congrArg FdState.fdst_pipes (check_set_tid_address_fd_state_frame eff m m' evs h))

/-! ### clone and clone3

The frame lemmas below are stated here for the reason the section above
gives for `check_set_tid_address_fd_state_frame`, and have no Rocq twin
for the same reason.  Each is `check_clone_answer_frame`'s,
`check_clone_frame`'s or `check_clone3_frame`'s proof
(`Checks/Sys/Kernel/Fork.lean`) with `m_fd` where those lemmas read the
VM ledger, reusing the inversion lemmas stated there. -/

/-- The answer both checkers end in hands back `m` or `with_children m`,
and `with_children` rebuilds the process state and nothing else
(`State/Model.lean`), so the descriptor subsystem is the one it was
handed. -/
theorem check_clone_answer_fd_state_frame (ret : word) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Fork.check_clone_answer ret m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold Checks.Sys.Kernel.Fork.check_clone_answer at h
  cases hin : errno_ret_in Sys.Kernel.Fork.clone_errnos ret with
  | true =>
      simp only [hin, ↓reduceIte, check_result.CheckOk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl
  | false =>
      simp only [hin, Bool.false_eq_true, ↓reduceIte] at h
      cases hv : Sys.Kernel.Fork.clone_pid_ok_b m ret with
      | false => simp only [hv, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
          simp only [hv, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          rfl

/-- An accepted `check_clone` keeps the descriptor subsystem: past the
flag gate it is `check_clone_resolve`, whose accepted answer is
`check_clone_answer`'s. -/
theorem check_clone_fd_state_frame (flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Kernel.Fork.check_clone flags eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  cases hf : Sys.Kernel.Fork.clone_fork_flags_b flags with
  | false =>
      simp only [Checks.Sys.Kernel.Fork.check_clone, hf, Bool.false_eq_true, ↓reduceIte,
        reduceCtorEq] at h
  | true =>
      simp only [Checks.Sys.Kernel.Fork.check_clone, hf, ↓reduceIte] at h
      obtain ⟨-, ret, -, h⟩ := Checks.Sys.Kernel.Fork.check_clone_resolve_ok_inv eff m m' evs h
      exact check_clone_answer_fd_state_frame ret m m' evs h

/-- An accepted `check_clone3` keeps the descriptor subsystem: past the
size, read and image gates it is `check_clone3_resolve`, whose accepted
answer is `check_clone_answer`'s. -/
theorem check_clone3_fd_state_frame (i : SyscallInput) (uargs size : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Kernel.Fork.check_clone3 i uargs size eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  obtain ⟨-, bs, -, -, h⟩ :=
    Checks.Sys.Kernel.Fork.check_clone3_ok_inv i uargs size eff m m' evs h
  obtain ⟨-, ret, -, h⟩ :=
    Checks.Sys.Kernel.Fork.check_clone3_resolve_ok_inv uargs eff m m' evs h
  exact check_clone_answer_fd_state_frame ret m m' evs h

/-- `vm_wf` × `clone`: the ledger fact above. -/
theorem vm_wf_arm_clone : arm_preserves inv_vm_wf arm_clone :=
  Arms.arm_clone_preserves_vm

/-- `vm_wf` × `clone3`: likewise. -/
theorem vm_wf_arm_clone3 : arm_preserves inv_vm_wf arm_clone3 :=
  Arms.arm_clone3_preserves_vm

/-- `fd_table_unique` × `clone`: the caller's table is the one it had.
Under the one word the gate admits, a fork gives the CHILD a copy
(`copy_files`, kernel/fork.c:1579-1607, Linux v6.18.46) and leaves the
caller's alone, and the model follows only the caller. -/
theorem fd_table_unique_arm_clone : arm_preserves inv_fd_table_unique arm_clone :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_clone (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_clone_fd_state_frame _ eff m m' evs h))

/-- `fd_table_unique` × `clone3`: the same resolution. -/
theorem fd_table_unique_arm_clone3 : arm_preserves inv_fd_table_unique arm_clone3 :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_clone3 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_clone3_fd_state_frame i _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `clone`: no pipe is touched. -/
theorem pipes_within_capacity_arm_clone : arm_preserves inv_pipes_within_capacity arm_clone :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_clone (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_clone_fd_state_frame _ eff m m' evs h))

/-- `pipes_within_capacity` × `clone3`: likewise. -/
theorem pipes_within_capacity_arm_clone3 :
    arm_preserves inv_pipes_within_capacity arm_clone3 :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_clone3 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_clone3_fd_state_frame i _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
