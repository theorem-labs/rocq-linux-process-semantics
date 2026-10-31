import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Select
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Fs.Select — pselect6 and ppoll on the checked surface

The registration of `Checks/Sys/Fs/Select.lean`'s two checkers in
`checked_table`, in the one file that registration writes.
`tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files
under `Checks/Arms/`, one per checker twin, so that registering an arm
creates or edits no hub but this file; its docstring is the shape it reads
and what it refuses. The file holds three sections, each in the
namespace its declarations had when those three hubs were written by
hand, so that no name moved with the file:

- `Checks.Sys.Table`: the `CheckedArm`s (`arm_pselect6` and `arm_ppoll`)
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
twin whose five theorems they are built from was read at.  The two rows
for 72 and 73 read the same at f44244ad6b80, the commit the ticket's brief
names, but the spec twin those theorems are over carries the
`FdUrandom` declines that `theories/LinuxProcessSem/Sys/Fs/Select.v` lacks
there, so that commit is not the one this registration was read against. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### pselect6 (72) -/

/-- pselect6 (72).  THE FIRST REGISTER IS NARROWED TO `int`; THE OTHER
FIVE ARRIVE WHOLE.  riscv64's `__riscv_sys_pselect6` hands the registers
over in order, `orig_a0` then `a1` to `a5` (`SC_RISCV_REGS_TO_ARGS`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46), and the
wrapper casts each to the type `SYSCALL_DEFINE6(pselect6, int, n, fd_set
__user *, inp, fd_set __user *, outp, fd_set __user *, exp, struct
__kernel_timespec __user *, tsp, void __user *, sig)` declares
(fs/select.c:793-795, same version) through `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46).  Only `n`
is narrower than the register: the four pointers and `sig` are 64 bits
wide on riscv64, so the cast is the identity on them.
`Sys.Syscall.nfds32 (in_arg i 0)` is that reading of `n`, applied here at
the boundary as Rocq's `arm_pselect6` applies it, so the checker and the
witness receive the narrowed word, and read it as the signed `int` it is
through `nfds_signed` inside the spec.  That reading subtracts one
`2^32` from a word it expects to be 32 bits wide, so an arm handing the
checker the whole register would read `n = 2^33` as `2^32`, above
`pselect_nfds_max`, and decline the call, where Linux sees `n = 0` and
answers it; `Checks/Cases/Checks/Sys/Fs/Select.lean` pins the difference
through `check_syscall`.  `ca_arm` is the term `Sys/Registry/Fs/Select.lean`'s
row builds, which `checked_table_arms` checks.  The ledger fact this arm
owes `checked_table_preserves_vm` is `check_pselect6_frame`, beside the
checker. -/
def arm_pselect6 : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 72 (fun i => Sys.Fs.Select.pselect6_spec
    (Sys.Syscall.nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4)
    (in_arg i 5) i)
  ca_check := fun i eff m => Checks.Sys.Fs.Select.check_pselect6 i
    (Sys.Syscall.nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4)
    (in_arg i 5) eff m
  ca_witness := fun i m => Checks.Sys.Fs.Select.pselect6_witness i m
    (Sys.Syscall.nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4)
    (in_arg i 5)
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Select.check_pselect6_sound_ok i (Sys.Syscall.nfds32 (in_arg i 0))
      (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Select.check_pselect6_sound_unmodeled i (Sys.Syscall.nfds32 (in_arg i 0))
      (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Select.check_pselect6_complete_ok i (Sys.Syscall.nfds32 (in_arg i 0))
      (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Select.check_pselect6_complete_unmodeled i (Sys.Syscall.nfds32 (in_arg i 0))
      (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.Select.pselect6_witness_ok (Sys.Syscall.nfds32 (in_arg i 0)) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m

@[arm_unfold] theorem ca_check_arm_pselect6 (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_pselect6.ca_check i eff m
      = Checks.Sys.Fs.Select.check_pselect6 i (Sys.Syscall.nfds32 (in_arg i 0)) (in_arg i 1)
          (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_pselect6 (i : SyscallInput) (m : Model) :
    arm_pselect6.ca_witness i m
      = Checks.Sys.Fs.Select.pselect6_witness i m (Sys.Syscall.nfds32 (in_arg i 0)) (in_arg i 1)
          (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) := rfl
@[arm_unfold] theorem sa_spec_arm_pselect6 (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_pselect6.ca_arm.sa_spec i m o
      = Sys.Fs.Select.pselect6_spec (Sys.Syscall.nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)
          (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o := rfl
@[arm_unfold] theorem ca_no_arm_pselect6 : ca_no arm_pselect6 = 72 := rfl

/- ### ppoll (73) -/

/-- ppoll (73).  THE SECOND REGISTER IS NARROWED TO `unsigned int`; THE
OTHER FOUR ARRIVE WHOLE.  The registers come over in order as for
pselect6 (`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24,
Linux v6.18.46), cast through `__SC_CAST` (include/linux/syscalls.h:132,
applied at arch/riscv/include/asm/syscall_wrapper.h:88, same version) to
the types `SYSCALL_DEFINE5(ppoll, struct pollfd __user *, ufds, unsigned
int, nfds, struct __kernel_timespec __user *, tsp, const sigset_t __user *,
sigmask, size_t, sigsetsize)` declares (fs/select.c:1095-1097, Linux
v6.18.46): `nfds` alone is narrower than the register, and `sigsetsize`
is a `size_t`, 64 bits wide, so it is compared with eight whole by
`set_user_sigmask` (kernel/signal.c:3281-3297, same version) and handed
over unnarrowed.  `Sys.Syscall.unfds32 (in_arg i 1)` is the reading of
`nfds`, applied here as Rocq's `arm_ppoll` applies it.  An arm handing
the checker the whole register would read `nfds = 2^32` as a count
above the soft descriptor limit and, under a zero timeout, accept the
-EINVAL `do_sys_poll` gives such a count (fs/select.c:981-982, Linux
v6.18.46), where Linux sees `nfds = 0` and answers 0;
`Checks/Cases/Checks/Sys/Fs/Select.lean` pins the difference through
`check_syscall`.  `ca_arm` is the term `Sys/Registry/Fs/Select.lean`'s
row builds, which `checked_table_arms` checks.  The ledger fact this arm
owes `checked_table_preserves_vm` is `check_ppoll_frame`, beside the
checker. -/
def arm_ppoll : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 73 (fun i => Sys.Fs.Select.ppoll_spec (in_arg i 0)
    (Sys.Syscall.unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i)
  ca_check := fun i eff m => Checks.Sys.Fs.Select.check_ppoll i (in_arg i 0)
    (Sys.Syscall.unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m
  ca_witness := fun i m => Checks.Sys.Fs.Select.ppoll_witness i m (in_arg i 0)
    (Sys.Syscall.unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4)
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Select.check_ppoll_sound_ok i (in_arg i 0) (Sys.Syscall.unfds32 (in_arg i 1))
      (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Select.check_ppoll_sound_unmodeled i (in_arg i 0)
      (Sys.Syscall.unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Select.check_ppoll_complete_ok i (in_arg i 0)
      (Sys.Syscall.unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Select.check_ppoll_complete_unmodeled i (in_arg i 0)
      (Sys.Syscall.unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.Select.ppoll_witness_ok (in_arg i 0) (Sys.Syscall.unfds32 (in_arg i 1))
      (in_arg i 2) (in_arg i 3) (in_arg i 4) i m

@[arm_unfold] theorem ca_check_arm_ppoll (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_ppoll.ca_check i eff m
      = Checks.Sys.Fs.Select.check_ppoll i (in_arg i 0) (Sys.Syscall.unfds32 (in_arg i 1))
          (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_ppoll (i : SyscallInput) (m : Model) :
    arm_ppoll.ca_witness i m
      = Checks.Sys.Fs.Select.ppoll_witness i m (in_arg i 0) (Sys.Syscall.unfds32 (in_arg i 1))
          (in_arg i 2) (in_arg i 3) (in_arg i 4) := rfl
@[arm_unfold] theorem sa_spec_arm_ppoll (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_ppoll.ca_arm.sa_spec i m o
      = Sys.Fs.Select.ppoll_spec (in_arg i 0) (Sys.Syscall.unfds32 (in_arg i 1)) (in_arg i 2)
          (in_arg i 3) (in_arg i 4) i m o := rfl
@[arm_unfold] theorem ca_no_arm_ppoll : ca_no arm_ppoll = 73 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `pselect6` (72): every answer the checker accepts is accepted with the
model it was handed — the spec's outcome is a return value and the set
and timespec write-backs, never a new model — so the ledger is what it
was (`check_pselect6_frame`, stated beside the checker in
`Checks/Sys/Fs/Select.lean`, Rocq's `check_pselect6_frame`). -/
theorem arm_pselect6_preserves_vm : arm_preserves_vm arm_pselect6 :=
  arm_preserves_of_frame arm_pselect6 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Fs.Select.check_pselect6_frame _ _ _ _ _ _ _ eff m m' evs h)

/-- `ppoll` (73): likewise, the return value and the `revents` and
timespec write-backs, with the model handed in (`check_ppoll_frame`, same
file, Rocq's `check_ppoll_frame`). -/
theorem arm_ppoll_preserves_vm : arm_preserves_vm arm_ppoll :=
  arm_preserves_of_frame arm_ppoll (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Fs.Select.check_ppoll_frame _ _ _ _ _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## The model frame the two descriptor-state facts rest on

The two registry entries beside `vm_wf` read the `m_fd` subsystem.  Both
checkers accept only `CheckOk m []`, the model they were handed, so one
lemma per checker saying exactly that answers both entries.  The tree's
rule is that a checker's frame lemma lives beside the checker, in
`Checks/Sys/Fs/Select.lean`; that file is not this registration's to
edit, so the lemmas stand here, as `check_exit_fd_state_frame` stands in
`Checks/Arms/Kernel/Exit.lean` for the same reason.  Rocq registers no
`m_fd` invariant, so neither lemma has a twin; the proof is
`check_pselect6_frame`'s with the whole model as the conclusion. -/

/-- `check_pselect6` accepts only with the model it was handed. -/
theorem check_pselect6_keeps_the_model (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.Select.check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs) :
    m' = m := by
  unfold Checks.Sys.Fs.Select.check_pselect6 at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h

/-- `check_ppoll` accepts only with the model it was handed. -/
theorem check_ppoll_keeps_the_model (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : Checks.Sys.Fs.Select.check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs) :
    m' = m := by
  unfold Checks.Sys.Fs.Select.check_ppoll at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h

/-- `vm_wf` × `pselect6`: the ledger fact above. -/
theorem vm_wf_arm_pselect6 : arm_preserves inv_vm_wf arm_pselect6 :=
  Arms.arm_pselect6_preserves_vm

/-- `vm_wf` × `ppoll`: the ledger fact above. -/
theorem vm_wf_arm_ppoll : arm_preserves inv_vm_wf arm_ppoll :=
  Arms.arm_ppoll_preserves_vm

/-- `fd_table_unique` × `pselect6`: polling installs and closes nothing,
so the table is the one handed in. -/
theorem fd_table_unique_arm_pselect6 : arm_preserves inv_fd_table_unique arm_pselect6 :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_pselect6 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    rw [check_pselect6_keeps_the_model _ _ _ _ _ _ _ eff m m' evs h])

/-- `fd_table_unique` × `ppoll`: likewise. -/
theorem fd_table_unique_arm_ppoll : arm_preserves inv_fd_table_unique arm_ppoll :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_ppoll (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    rw [check_ppoll_keeps_the_model _ _ _ _ _ _ eff m m' evs h])

/-- `pipes_within_capacity` × `pselect6`: no pipe is read or written. -/
theorem pipes_within_capacity_arm_pselect6 :
    arm_preserves inv_pipes_within_capacity arm_pselect6 :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_pselect6 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    rw [check_pselect6_keeps_the_model _ _ _ _ _ _ _ eff m m' evs h])

/-- `pipes_within_capacity` × `ppoll`: likewise. -/
theorem pipes_within_capacity_arm_ppoll :
    arm_preserves inv_pipes_within_capacity arm_ppoll :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_ppoll (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    rw [check_ppoll_keeps_the_model _ _ _ _ _ _ eff m m' evs h])

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
