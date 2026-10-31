import LinuxProcessSemantics.LinuxProcessSem.Checks.Arms.Fs.ReadWrite
import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Net.Socket
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # LinuxProcessSem.Checks.Arms.Net.Socket — socket checker registration

Registrations of the checkers in `Checks/Sys/Net/Socket.lean`.
`tools/gen_lean_checked.py`'s docstring defines the arm-file contract and
the tables generated from it.

Rocq's `arm_setsockopt` and `arm_getsockopt` in
`theories/LinuxProcessSem/Checks/Sys/Dispatch.v` read the same at
f44244ad6b80 and at 753eaff8c. The checker docstrings explain their gates;
the registration supplies the ABI argument reading.

The frame lemmas live here because the checker belongs to its C ticket
and `Checks/VmMapsDisjoint.lean` is frozen. They are Lean-only twins of
Rocq's `VmMapsDisjoint.check_setsockopt_frame` and
`VmMapsDisjoint.check_getsockopt_frame`, obtained from the stronger
`check_setsockopt_ok_model` and `check_getsockopt_ok_model` below. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/-- `SYSCALL_DEFINE5(setsockopt, int, fd, int, level, int, optname,
char __user *, optval, int, optlen)` (net/socket.c:2389-2392,
Linux v6.18.46, commit 1f99e9ab748f) calls `__sys_setsockopt` (net/socket.c:2372-2387), then
`do_sock_setsockopt` (net/socket.c:2328-2366, same version).
The gates are justified beside `Checks.Sys.Net.Socket.check_setsockopt`.
`SC_RISCV_REGS_TO_ARGS` passes a0 through a4 in order
(arch/riscv/include/asm/syscall_wrapper.h:21-24), and
`__SYSCALL_DEFINEx` casts them at :82-96 through `__SC_CAST`
(include/linux/syscalls.h:132), read at Linux v6.18.46, commit 1f99e9ab748f.
An `int` keeps the register's low 32 bits: `fd32` and `int32` compute
that reading through `abi_low32` in `Sys/Syscall.lean`.
The a4 parameter is an `int`, so its low half goes to the checker
and witness, as in Rocq's `arm_setsockopt`. -/
def arm_setsockopt : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 208 (fun i => Sys.Net.Socket.setsockopt_spec (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (Sys.Syscall.int32 (in_arg i 4)) i)
  ca_check := fun i eff m => Checks.Sys.Net.Socket.check_setsockopt (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (Sys.Syscall.int32 (in_arg i 4)) eff m
  ca_witness := fun i m => Checks.Sys.Net.Socket.setsockopt_witness (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (Sys.Syscall.int32 (in_arg i 4)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Net.Socket.check_setsockopt_sound_ok (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (Sys.Syscall.int32 (in_arg i 4)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Net.Socket.check_setsockopt_sound_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (Sys.Syscall.int32 (in_arg i 4)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Net.Socket.check_setsockopt_complete_ok (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (Sys.Syscall.int32 (in_arg i 4)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Net.Socket.check_setsockopt_complete_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (Sys.Syscall.int32 (in_arg i 4)) m i eff h
  ca_receptive := fun i m => Checks.Sys.Net.Socket.setsockopt_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (Sys.Syscall.int32 (in_arg i 4)) i m

@[arm_unfold] theorem ca_check_arm_setsockopt (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_setsockopt.ca_check i eff m = Checks.Sys.Net.Socket.check_setsockopt (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (Sys.Syscall.int32 (in_arg i 4)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_setsockopt (i : SyscallInput) (m : Model) :
    arm_setsockopt.ca_witness i m = Checks.Sys.Net.Socket.setsockopt_witness (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (Sys.Syscall.int32 (in_arg i 4)) m := rfl
@[arm_unfold] theorem sa_spec_arm_setsockopt (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_setsockopt.ca_arm.sa_spec i m o = Sys.Net.Socket.setsockopt_spec (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (Sys.Syscall.int32 (in_arg i 4)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_setsockopt : ca_no arm_setsockopt = 208 := rfl

/-- `SYSCALL_DEFINE5(getsockopt, int, fd, int, level, int, optname,
char __user *, optval, int __user *, optlen)` (net/socket.c:2455-2458,
Linux v6.18.46, commit 1f99e9ab748f) calls `__sys_getsockopt` (net/socket.c:2439-2453), then
`do_sock_getsockopt` (net/socket.c:2398-2432, same version).
The gates are justified beside `Checks.Sys.Net.Socket.check_getsockopt`.
`SC_RISCV_REGS_TO_ARGS` passes a0 through a4 in order
(arch/riscv/include/asm/syscall_wrapper.h:21-24), and
`__SYSCALL_DEFINEx` casts them at :82-96 through `__SC_CAST`
(include/linux/syscalls.h:132), read at Linux v6.18.46, commit 1f99e9ab748f.
An `int` keeps the register's low 32 bits: `fd32` and `int32` compute
that reading through `abi_low32` in `Sys/Syscall.lean`.
The a4 parameter is a pointer, so its address goes whole to the checker
and witness, as in Rocq's `arm_getsockopt`. -/
def arm_getsockopt : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 209 (fun i => Sys.Net.Socket.getsockopt_spec (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (in_arg i 4) i)
  ca_check := fun i eff m => Checks.Sys.Net.Socket.check_getsockopt i (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (in_arg i 4) eff m
  ca_witness := fun i m => Checks.Sys.Net.Socket.getsockopt_witness (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (in_arg i 4) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Net.Socket.check_getsockopt_sound_ok i (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (in_arg i 4) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Net.Socket.check_getsockopt_sound_unmodeled i (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (in_arg i 4) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Net.Socket.check_getsockopt_complete_ok i (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (in_arg i 4) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Net.Socket.check_getsockopt_complete_unmodeled i (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (in_arg i 4) m eff h
  ca_receptive := fun i m => Checks.Sys.Net.Socket.getsockopt_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (in_arg i 4) i m

@[arm_unfold] theorem ca_check_arm_getsockopt (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_getsockopt.ca_check i eff m = Checks.Sys.Net.Socket.check_getsockopt i (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (in_arg i 4) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_getsockopt (i : SyscallInput) (m : Model) :
    arm_getsockopt.ca_witness i m = Checks.Sys.Net.Socket.getsockopt_witness (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (in_arg i 4) i m := rfl
@[arm_unfold] theorem sa_spec_arm_getsockopt (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_getsockopt.ca_arm.sa_spec i m o = Sys.Net.Socket.getsockopt_spec (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) (in_arg i 4) i m o := rfl
@[arm_unfold] theorem ca_no_arm_getsockopt : ca_no arm_getsockopt = 209 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Net.Socket

/-- Lean-only strengthening of Rocq's `VmMapsDisjoint.check_setsockopt_frame`:
accepted answers leave the model and events unchanged, as this theorem pins. -/
theorem check_setsockopt_ok_model (fd level optlen : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_setsockopt fd level optlen eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  unfold check_setsockopt at h
  split at h
  · exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
  · split at h
    · exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
    · split at h
      · exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
      · cases h

/-- Lean-only twin of Rocq's `VmMapsDisjoint.check_setsockopt_frame`,
projected from `check_setsockopt_ok_model`. -/
theorem check_setsockopt_frame (fd level optlen : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_setsockopt fd level optlen eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨rfl, -⟩ := check_setsockopt_ok_model fd level optlen eff m m' evs h
  rfl

/-- The VM frame supplied by `check_setsockopt_frame`. -/
theorem arm_setsockopt_preserves_vm : arm_preserves_vm arm_setsockopt :=
  arm_preserves_of_frame arm_setsockopt (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_setsockopt_frame _ _ _ eff m m' evs h)

/-- Lean-only strengthening of Rocq's `VmMapsDisjoint.check_getsockopt_frame`:
accepted answers leave the model and events unchanged, as this theorem pins. -/
theorem check_getsockopt_ok_model (i : SyscallInput) (fd level optlenp : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_getsockopt i fd level optlenp eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  unfold check_getsockopt at h
  split at h
  · exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2
  · split at h
    · exact ((check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h).2
    · cases h

/-- Lean-only twin of Rocq's `VmMapsDisjoint.check_getsockopt_frame`,
projected from `check_getsockopt_ok_model`. -/
theorem check_getsockopt_frame (i : SyscallInput) (fd level optlenp : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_getsockopt i fd level optlenp eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨rfl, -⟩ := check_getsockopt_ok_model i fd level optlenp eff m m' evs h
  rfl

/-- The VM frame supplied by `check_getsockopt_frame`. -/
theorem arm_getsockopt_preserves_vm : arm_preserves_vm arm_getsockopt :=
  arm_preserves_of_frame arm_getsockopt (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_getsockopt_frame i _ _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- Lean-only: transport an invariant once using `check_setsockopt_ok_model`. -/
theorem setsockopt_preserves_invariant (inv : Invariant) : arm_preserves inv arm_setsockopt := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  obtain ⟨rfl, -⟩ := Arms.check_setsockopt_ok_model _ _ _ eff m m' evs h
  exact hold

/-- `vm_wf` transported by `setsockopt_preserves_invariant`. -/
theorem vm_wf_arm_setsockopt : arm_preserves inv_vm_wf arm_setsockopt :=
  setsockopt_preserves_invariant inv_vm_wf

/-- `fd_table_unique` transported by `setsockopt_preserves_invariant`. -/
theorem fd_table_unique_arm_setsockopt : arm_preserves inv_fd_table_unique arm_setsockopt :=
  setsockopt_preserves_invariant inv_fd_table_unique

/-- `pipes_within_capacity` transported by `setsockopt_preserves_invariant`. -/
theorem pipes_within_capacity_arm_setsockopt : arm_preserves inv_pipes_within_capacity arm_setsockopt :=
  setsockopt_preserves_invariant inv_pipes_within_capacity

/-- Lean-only: transport an invariant once using `check_getsockopt_ok_model`. -/
theorem getsockopt_preserves_invariant (inv : Invariant) : arm_preserves inv arm_getsockopt := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  obtain ⟨rfl, -⟩ := Arms.check_getsockopt_ok_model i _ _ _ eff m m' evs h
  exact hold

/-- `vm_wf` transported by `getsockopt_preserves_invariant`. -/
theorem vm_wf_arm_getsockopt : arm_preserves inv_vm_wf arm_getsockopt :=
  getsockopt_preserves_invariant inv_vm_wf

/-- `fd_table_unique` transported by `getsockopt_preserves_invariant`. -/
theorem fd_table_unique_arm_getsockopt : arm_preserves inv_fd_table_unique arm_getsockopt :=
  getsockopt_preserves_invariant inv_fd_table_unique

/-- `pipes_within_capacity` transported by `getsockopt_preserves_invariant`. -/
theorem pipes_within_capacity_arm_getsockopt : arm_preserves inv_pipes_within_capacity arm_getsockopt :=
  getsockopt_preserves_invariant inv_pipes_within_capacity

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

/-! ## V-Net-Socket-lifecycle: dispatcher registration -/

-- The nested validation and effect matches exceed the default elaborator
-- recursion depth when the frame eliminators split them.
set_option maxRecDepth 4096

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Net.Socket

/-- Rocq: `Checks.Sys.Dispatch.arm_socket` at f44244ad6b80.
The ABI argument reading is shared with the existing registry row. -/
def arm_socket : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 198 (fun i => Sys.Net.Socket.socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_socket (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => socket_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) m
  ca_sound_ok := fun i eff m m' evs h => check_socket_sound_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h => check_socket_sound_unmodeled (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m i h
  ca_complete_ok := fun i eff m m' evs h => check_socket_complete_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h => check_socket_complete_unmodeled (in_arg i 0) (in_arg i 1) (in_arg i 2) m i eff h
  ca_receptive := fun i m => socket_witness_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_socket (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_socket.ca_check i eff m = check_socket (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_socket (i : SyscallInput) (m : Model) :
    arm_socket.ca_witness i m = socket_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) m := rfl
@[arm_unfold] theorem sa_spec_arm_socket (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_socket.ca_arm.sa_spec i m o = Sys.Net.Socket.socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_socket : ca_no arm_socket = 198 := rfl

/-- Rocq: `Checks.Sys.Dispatch.arm_socketpair` at f44244ad6b80.
The ABI argument reading is shared with the existing registry row. -/
def arm_socketpair : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 199 (fun i => Sys.Net.Socket.socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m => check_socketpair i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m => socketpair_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs h => check_socketpair_sound_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h => check_socketpair_sound_unmodeled i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m h
  ca_complete_ok := fun i eff m m' evs h => check_socketpair_complete_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h => check_socketpair_complete_unmodeled i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m eff h
  ca_receptive := fun i m => socketpair_witness_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

@[arm_unfold] theorem ca_check_arm_socketpair (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_socketpair.ca_check i eff m = check_socketpair i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_socketpair (i : SyscallInput) (m : Model) :
    arm_socketpair.ca_witness i m = socketpair_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := rfl
@[arm_unfold] theorem sa_spec_arm_socketpair (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_socketpair.ca_arm.sa_spec i m o = Sys.Net.Socket.socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o := rfl
@[arm_unfold] theorem ca_no_arm_socketpair : ca_no arm_socketpair = 199 := rfl

/-- Rocq: `Checks.Sys.Dispatch.arm_bind` at f44244ad6b80.
The ABI argument reading is shared with the existing registry row. -/
def arm_bind : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 200 (fun i => Sys.Net.Socket.bind_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_bind i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => bind_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs h => check_bind_sound_ok i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h => check_bind_sound_unmodeled i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m h
  ca_complete_ok := fun i eff m m' evs h => check_bind_complete_ok i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h => check_bind_complete_unmodeled i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff h
  ca_receptive := fun i m => bind_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_bind (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_bind.ca_check i eff m = check_bind i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_bind (i : SyscallInput) (m : Model) :
    arm_bind.ca_witness i m = bind_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl
@[arm_unfold] theorem sa_spec_arm_bind (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_bind.ca_arm.sa_spec i m o = Sys.Net.Socket.bind_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_bind : ca_no arm_bind = 200 := rfl

/-- Rocq: `Checks.Sys.Dispatch.arm_listen` at f44244ad6b80.
The ABI argument reading is shared with the existing registry row. -/
def arm_listen : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 201 (fun i => Sys.Net.Socket.listen_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) i)
  ca_check := fun i eff m => check_listen (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) eff m
  ca_witness := fun i m => listen_witness (Sys.Syscall.fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs h => check_listen_sound_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h => check_listen_sound_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) eff m i h
  ca_complete_ok := fun i eff m m' evs h => check_listen_complete_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h => check_listen_complete_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) m i eff h
  ca_receptive := fun i m => listen_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) i m

@[arm_unfold] theorem ca_check_arm_listen (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_listen.ca_check i eff m = check_listen (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_listen (i : SyscallInput) (m : Model) :
    arm_listen.ca_witness i m = listen_witness (Sys.Syscall.fd32 (in_arg i 0)) m := rfl
@[arm_unfold] theorem sa_spec_arm_listen (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_listen.ca_arm.sa_spec i m o = Sys.Net.Socket.listen_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) i m o := rfl
@[arm_unfold] theorem ca_no_arm_listen : ca_no arm_listen = 201 := rfl

/-- Rocq: `Checks.Sys.Dispatch.arm_accept` at f44244ad6b80.
The ABI argument reading is shared with the existing registry row. -/
def arm_accept : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 202 (fun i => Sys.Net.Socket.accept4_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i)
  ca_check := fun i eff m => check_accept4 (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) eff m
  ca_witness := fun i m => accept4_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (Z_to_bv 64 0) m
  ca_sound_ok := fun i eff m m' evs h => check_accept4_sound_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h => check_accept4_sound_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) eff m i h
  ca_complete_ok := fun i eff m m' evs h => check_accept4_complete_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h => check_accept4_complete_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) m i eff h
  ca_receptive := fun i m => accept4_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i m

@[arm_unfold] theorem ca_check_arm_accept (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_accept.ca_check i eff m = check_accept4 (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_accept (i : SyscallInput) (m : Model) :
    arm_accept.ca_witness i m = accept4_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (Z_to_bv 64 0) m := rfl
@[arm_unfold] theorem sa_spec_arm_accept (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_accept.ca_arm.sa_spec i m o = Sys.Net.Socket.accept4_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i m o := rfl
@[arm_unfold] theorem ca_no_arm_accept : ca_no arm_accept = 202 := rfl

/-- Rocq: `Checks.Sys.Dispatch.arm_connect` at f44244ad6b80.
The ABI argument reading is shared with the existing registry row. -/
def arm_connect : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 203 (fun i => Sys.Net.Socket.connect_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_connect i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => connect_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs h => check_connect_sound_ok i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h => check_connect_sound_unmodeled i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m h
  ca_complete_ok := fun i eff m m' evs h => check_connect_complete_ok i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h => check_connect_complete_unmodeled i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff h
  ca_receptive := fun i m => connect_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_connect (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_connect.ca_check i eff m = check_connect i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_connect (i : SyscallInput) (m : Model) :
    arm_connect.ca_witness i m = connect_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl
@[arm_unfold] theorem sa_spec_arm_connect (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_connect.ca_arm.sa_spec i m o = Sys.Net.Socket.connect_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_connect : ca_no arm_connect = 203 := rfl

/-- Rocq: `Checks.Sys.Dispatch.arm_getsockname` at f44244ad6b80.
The ABI argument reading is shared with the existing registry row. -/
def arm_getsockname : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 204 (fun i => Sys.Net.Socket.getsockname_spec (Sys.Syscall.fd32 (in_arg i 0)) i)
  ca_check := fun i eff m => check_getsockname (Sys.Syscall.fd32 (in_arg i 0)) eff m
  ca_witness := fun i m => getsockname_witness (Sys.Syscall.fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs h => check_getsockname_sound_ok (Sys.Syscall.fd32 (in_arg i 0)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h => check_getsockname_sound_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) eff m i h
  ca_complete_ok := fun i eff m m' evs h => check_getsockname_complete_ok (Sys.Syscall.fd32 (in_arg i 0)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h => check_getsockname_complete_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) m i eff h
  ca_receptive := fun i m => getsockname_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) i m

@[arm_unfold] theorem ca_check_arm_getsockname (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_getsockname.ca_check i eff m = check_getsockname (Sys.Syscall.fd32 (in_arg i 0)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_getsockname (i : SyscallInput) (m : Model) :
    arm_getsockname.ca_witness i m = getsockname_witness (Sys.Syscall.fd32 (in_arg i 0)) m := rfl
@[arm_unfold] theorem sa_spec_arm_getsockname (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_getsockname.ca_arm.sa_spec i m o = Sys.Net.Socket.getsockname_spec (Sys.Syscall.fd32 (in_arg i 0)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_getsockname : ca_no arm_getsockname = 204 := rfl

/-- Rocq: `Checks.Sys.Dispatch.arm_getpeername` at f44244ad6b80.
The ABI argument reading is shared with the existing registry row. -/
def arm_getpeername : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 205 (fun i => Sys.Net.Socket.getpeername_spec (Sys.Syscall.fd32 (in_arg i 0)) i)
  ca_check := fun i eff m => check_getpeername (Sys.Syscall.fd32 (in_arg i 0)) eff m
  ca_witness := fun i m => getpeername_witness (Sys.Syscall.fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs h => check_getpeername_sound_ok (Sys.Syscall.fd32 (in_arg i 0)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h => check_getpeername_sound_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) eff m i h
  ca_complete_ok := fun i eff m m' evs h => check_getpeername_complete_ok (Sys.Syscall.fd32 (in_arg i 0)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h => check_getpeername_complete_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) m i eff h
  ca_receptive := fun i m => getpeername_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) i m

@[arm_unfold] theorem ca_check_arm_getpeername (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_getpeername.ca_check i eff m = check_getpeername (Sys.Syscall.fd32 (in_arg i 0)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_getpeername (i : SyscallInput) (m : Model) :
    arm_getpeername.ca_witness i m = getpeername_witness (Sys.Syscall.fd32 (in_arg i 0)) m := rfl
@[arm_unfold] theorem sa_spec_arm_getpeername (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_getpeername.ca_arm.sa_spec i m o = Sys.Net.Socket.getpeername_spec (Sys.Syscall.fd32 (in_arg i 0)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_getpeername : ca_no arm_getpeername = 205 := rfl

/-- Rocq: `Checks.Sys.Dispatch.arm_shutdown` at f44244ad6b80.
The ABI argument reading is shared with the existing registry row. -/
def arm_shutdown : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 210 (fun i => Sys.Net.Socket.shutdown_spec (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) i)
  ca_check := fun i eff m => check_shutdown (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) eff m
  ca_witness := fun i m => shutdown_witness (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) m
  ca_sound_ok := fun i eff m m' evs h => check_shutdown_sound_ok (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h => check_shutdown_sound_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) eff m i h
  ca_complete_ok := fun i eff m m' evs h => check_shutdown_complete_ok (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h => check_shutdown_complete_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) m i eff h
  ca_receptive := fun i m => shutdown_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) i m

@[arm_unfold] theorem ca_check_arm_shutdown (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_shutdown.ca_check i eff m = check_shutdown (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_shutdown (i : SyscallInput) (m : Model) :
    arm_shutdown.ca_witness i m = shutdown_witness (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) m := rfl
@[arm_unfold] theorem sa_spec_arm_shutdown (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_shutdown.ca_arm.sa_spec i m o = Sys.Net.Socket.shutdown_spec (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.int32 (in_arg i 1)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_shutdown : ca_no arm_shutdown = 210 := rfl

/-- Rocq: `Checks.Sys.Dispatch.arm_accept4` at f44244ad6b80.
The ABI argument reading is shared with the existing registry row. -/
def arm_accept4 : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 242 (fun i => Sys.Net.Socket.accept4_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m => check_accept4 (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m => accept4_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 3) m
  ca_sound_ok := fun i eff m m' evs h => check_accept4_sound_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h => check_accept4_sound_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m i h
  ca_complete_ok := fun i eff m m' evs h => check_accept4_complete_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h => check_accept4_complete_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) m i eff h
  ca_receptive := fun i m => accept4_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

@[arm_unfold] theorem ca_check_arm_accept4 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_accept4.ca_check i eff m = check_accept4 (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_accept4 (i : SyscallInput) (m : Model) :
    arm_accept4.ca_witness i m = accept4_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 3) m := rfl
@[arm_unfold] theorem sa_spec_arm_accept4 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_accept4.ca_arm.sa_spec i m o = Sys.Net.Socket.accept4_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o := rfl
@[arm_unfold] theorem ca_no_arm_accept4 : ca_no arm_accept4 = 242 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Net.Socket
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket

/-- Lean-only strengthening of Rocq's `VmMapsDisjoint.check_socket_frame`:
the accepted model is unchanged or contains one inserted descriptor.
The validation splits follow `check_socket_sound_ok`; the allocation
leaf uses its existing inversion lemma instead of unfolding the effect. -/
theorem check_socket_ok_post (domain type protocol : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_socket domain type protocol eff m = CheckOk m' evs) :
    m' = m ∨ ∃ fd e, m' = with_fds (fd_insert (m_fds m) fd e) m := by
  unfold check_socket at h
  generalize sint32 domain = fam at h
  generalize sint32 protocol = pro at h
  generalize abi_low32 type = tu at h
  simp only [] at h
  by_cases h1 : bv_unsigned (bv_and (bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK)))
      (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0
  case neg =>
    simp only [h1, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
  simp only [h1, not_true_eq_false, ↓reduceIte] at h
  by_cases h2 : bv_unsigned (bv_and (bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK)))
      (Z_to_bv 64 SOCK_NONBLOCK)) = 0
  case neg =>
    simp only [h2, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
  simp only [h2, not_true_eq_false, ↓reduceIte] at h
  generalize bv_unsigned (bv_and tu (Z_to_bv 64 SOCK_TYPE_MASK)) = ty at h
  by_cases h3 : fam < 0 ∨ NPROTO ≤ fam
  · simp only [h3, ↓reduceIte] at h
    obtain ⟨-, hm, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact Or.inl hm
  simp only [h3, ↓reduceIte] at h
  by_cases h4 : SOCK_MAX ≤ ty
  · simp only [h4, ↓reduceIte] at h
    by_cases h4n : AF_MAX_V4_17 ≤ fam ∨ (fam = AF_NETLINK ∧ ¬ (pro = NETLINK_AUDIT ∨ pro = NETLINK_KOBJECT_UEVENT))
    · simp only [h4n, ↓reduceIte, reduceCtorEq] at h
    simp only [h4n, ↓reduceIte] at h
    obtain ⟨-, hm, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact Or.inl hm
  simp only [h4, ↓reduceIte] at h
  by_cases h5 : fam = AF_INET
  case neg =>
    simp only [h5, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
  simp only [h5, not_true_eq_false, ↓reduceIte] at h
  by_cases h6 : ty = SOCK_PACKET
  · simp only [h6, ↓reduceIte, reduceCtorEq] at h
  simp only [h6, ↓reduceIte] at h
  by_cases h7 : pro < 0 ∨ IPPROTO_MAX ≤ pro
  · simp only [h7, ↓reduceIte] at h
    obtain ⟨hm, -⟩ := check_errno_only_ok_inv _ _ _ _ _ h
    exact Or.inl hm
  simp only [h7, ↓reduceIte] at h
  by_cases h7r : IPPROTO_MAX_PRE_V5_6 ≤ pro
  · simp only [h7r, ↓reduceIte, reduceCtorEq] at h
  simp only [h7r, ↓reduceIte] at h
  by_cases h8 : ty = SOCK_STREAM
  · simp only [h8, ↓reduceIte] at h
    by_cases h9 : pro = IPPROTO_SCTP
    · simp only [h9, ↓reduceIte, reduceCtorEq] at h
    simp only [h9, ↓reduceIte] at h
    by_cases h10 : pro = IPPROTO_IP ∨ pro = IPPROTO_TCP
    case neg =>
      simp only [h10, not_false_eq_true, ↓reduceIte] at h
      obtain ⟨hm, -⟩ := check_errno_only_ok_inv _ _ _ _ _ h
      exact Or.inl hm
    simp only [h10, not_true_eq_false, ↓reduceIte] at h
    obtain ⟨-, ret, -, hcase⟩ := Checks.Sys.Fs.Open.check_new_fd_result_ok_inv socket_errnos eff m _ m' evs h
    rcases hcase with ⟨-, hm⟩ | ⟨-, -, hm⟩
    · exact Or.inl hm
    · exact Or.inr ⟨ret, .FdSocket .SkFresh, hm⟩
  simp only [h8, ↓reduceIte] at h
  by_cases h11 : ty = SOCK_DGRAM ∨ ty = SOCK_RAW
  · simp only [h11, ↓reduceIte, reduceCtorEq] at h
  simp only [h11, ↓reduceIte] at h
  by_cases h12 : ty = SOCK_SEQPACKET ∨ ty = SOCK_DCCP
  · simp only [h12, ↓reduceIte, reduceCtorEq] at h
  simp only [h12, ↓reduceIte] at h
  obtain ⟨hm, -⟩ := check_errno_only_ok_inv _ _ _ _ _ h
  exact Or.inl hm

/-- Rocq's `VmMapsDisjoint.check_socket_frame`, projected from
`check_socket_ok_post` without reopening the validation gates. -/
theorem arm_socket_preserves_vm : arm_preserves_vm arm_socket :=
  arm_preserves_of_frame arm_socket (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    rcases check_socket_ok_post _ _ _ eff m m' evs h with rfl | ⟨fd, e, rfl⟩ <;> rfl)

/-- Lean-only frame for Rocq's `VmMapsDisjoint.check_socketpair_frame`:
opening result wrappers lets the existing frame eliminators recover the
accepted model without changing any syscall decision. -/
theorem arm_socketpair_preserves_vm : arm_preserves_vm arm_socketpair :=
  arm_preserves_of_frame arm_socketpair (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    unfold check_socketpair at h
    simp only [check_socketpair_written, check_socketpair_faulted] at h
    vm_frame h)

/-- An accepted errno keeps the model; an accepted success installs
exactly the supplied table. Lean-only, for the lifecycle frame proofs. -/
theorem check_errno_or_success_ok_post (es : List Int) (fds : List (word × FdEntry))
    (r : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_errno_or_success es fds r eff m = CheckOk m' evs) :
    m' = m ∨ m' = with_fds fds m := by
  unfold check_errno_or_success at h
  split at h
  · split at h
    · cases h
      exact Or.inl rfl
    · split at h
      · cases h
        exact Or.inr rfl
      · cases h
  · cases h

/-- Lean-only strengthening of Rocq's `VmMapsDisjoint.check_bind_frame`.
The copy-in acceptor changes no state; only the successful bind inserts
an entry. Explicit validation splits avoid unfolding address-byte reads
while proving this structural property. -/
theorem check_bind_ok_post (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_bind i fd addrp addrlen eff m = CheckOk m' evs) :
    m' = m ∨ ∃ fd e, m' = with_fds (fd_insert (m_fds m) fd e) m := by
  unfold check_bind at h
  generalize sint32 addrlen = al at h
  generalize fd_lookup (m_fds m) fd = r at h
  cases r with
  | none =>
    obtain ⟨-, hm, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact Or.inl hm
  | some e =>
    cases e
    case FdSocket sk =>
      simp only [] at h
      by_cases h1 : al < 0 ∨ SOCKADDR_STORAGE_SIZE < al
      · simp only [h1, ↓reduceIte] at h
        obtain ⟨-, hm, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
        exact Or.inl hm
      · simp only [h1, ↓reduceIte] at h
        by_cases h2 : al = 0
        · simp only [h2, ↓reduceIte] at h
          obtain ⟨-, hm, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
          exact Or.inl hm
        · simp only [h2, ↓reduceIte] at h
          rcases hr : read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with _ | bs
          · simp only [hr] at h
            obtain ⟨-, hm, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
            exact Or.inl hm
          · simp only [hr] at h
            by_cases h3 : al < SOCKADDR_IN_SIZE
            · simp only [h3, ↓reduceIte] at h
              obtain ⟨-, hm, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
              exact Or.inl hm
            · simp only [h3, ↓reduceIte] at h
              by_cases h4 : sa_family_of bs = AF_INET
                  ∨ (sa_family_of bs = AF_UNSPEC ∧ sin_addr_of bs = INADDR_ANY)
              · simp only [h4, not_true_eq_false, ↓reduceIte] at h
                by_cases h5 : sin_addr_of bs = INADDR_ANY
                · simp only [h5, not_true_eq_false, ↓reduceIte] at h
                  by_cases h6 : sin_port_of bs = 0
                  · simp only [h6, not_true_eq_false, ↓reduceIte] at h
                    cases sk
                    case SkFresh =>
                      have hb := check_copyins_model h
                      rcases check_errno_or_success_ok_post _ _ _ _ _ _ _ hb with hm | hm
                      · exact Or.inl hm
                      · exact Or.inr ⟨fd, .FdSocket .SkBound, hm⟩
                    case SkConnected peer ch rx => simp only [reduceCtorEq] at h
                    case SkReset peer ch => simp only [reduceCtorEq] at h
                    all_goals
                      obtain ⟨-, hm, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
                      exact Or.inl hm
                  · simp only [h6, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
                · simp only [h5, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
              · simp only [h4, not_false_eq_true, ↓reduceIte] at h
                obtain ⟨-, hm, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
                exact Or.inl hm
    all_goals
      obtain ⟨-, hm, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact Or.inl hm

/-- Rocq's `VmMapsDisjoint.check_bind_frame`, projected from
`check_bind_ok_post` without reopening the validation gates. -/
theorem arm_bind_preserves_vm : arm_preserves_vm arm_bind :=
  arm_preserves_of_frame arm_bind (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    rcases check_bind_ok_post i _ _ _ eff m m' evs h with rfl | ⟨fd, e, rfl⟩ <;> rfl)

/-- Lean-only frame for Rocq's `VmMapsDisjoint.check_listen_frame`:
opening result wrappers lets the existing frame eliminators recover the
accepted model without changing any syscall decision. -/
theorem arm_listen_preserves_vm : arm_preserves_vm arm_listen :=
  arm_preserves_of_frame arm_listen (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    unfold check_listen at h
    simp only [check_errno_or_success] at h
    vm_frame h)

/-- Lean-only frame for Rocq's `VmMapsDisjoint.check_accept4_frame`:
opening result wrappers lets the existing frame eliminators recover the
accepted model without changing any syscall decision. -/
theorem arm_accept_preserves_vm : arm_preserves_vm arm_accept :=
  arm_preserves_of_frame arm_accept (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    unfold check_accept4 at h
    simp only [check_errno_only, Checks.Sys.Fs.Open.check_new_fd_result] at h
    vm_frame h)

/-- Lean-only frame for Rocq's `VmMapsDisjoint.check_connect_frame`:
opening result wrappers lets the existing frame eliminators recover the
accepted model without changing any syscall decision. -/
theorem arm_connect_preserves_vm : arm_preserves_vm arm_connect :=
  arm_preserves_of_frame arm_connect (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    unfold check_connect at h
    generalize Sys.Syscall.sint32 (in_arg i 2) = al at h
    vm_frame h)

/-- Lean-only frame for Rocq's `VmMapsDisjoint.check_getsockname_frame`:
opening result wrappers lets the existing frame eliminators recover the
accepted model without changing any syscall decision. -/
theorem arm_getsockname_preserves_vm : arm_preserves_vm arm_getsockname :=
  arm_preserves_of_frame arm_getsockname (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    unfold check_getsockname at h
    vm_frame h)

/-- Lean-only frame for Rocq's `VmMapsDisjoint.check_getpeername_frame`:
opening result wrappers lets the existing frame eliminators recover the
accepted model without changing any syscall decision. -/
theorem arm_getpeername_preserves_vm : arm_preserves_vm arm_getpeername :=
  arm_preserves_of_frame arm_getpeername (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    unfold check_getpeername at h
    vm_frame h)

/-- Lean-only frame for Rocq's `VmMapsDisjoint.check_shutdown_frame`:
opening result wrappers lets the existing frame eliminators recover the
accepted model without changing any syscall decision. -/
theorem arm_shutdown_preserves_vm : arm_preserves_vm arm_shutdown :=
  arm_preserves_of_frame arm_shutdown (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    unfold check_shutdown at h
    vm_frame h)

/-- Lean-only frame for Rocq's `VmMapsDisjoint.check_accept4_frame`:
opening result wrappers lets the existing frame eliminators recover the
accepted model without changing any syscall decision. -/
theorem arm_accept4_preserves_vm : arm_preserves_vm arm_accept4 :=
  arm_preserves_of_frame arm_accept4 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    unfold check_accept4 at h
    simp only [check_errno_only, Checks.Sys.Fs.Open.check_new_fd_result] at h
    vm_frame h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Net.Socket
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- The VM frame above transports `vm_wf`. -/
theorem vm_wf_arm_socket : arm_preserves inv_vm_wf arm_socket :=
  Arms.arm_socket_preserves_vm

/-- Accepted results retain the descriptor table or install one entry
through `fd_insert`, which preserves unique descriptor keys. -/
theorem fd_table_unique_arm_socket : arm_preserves inv_fd_table_unique arm_socket := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  rcases Arms.check_socket_ok_post _ _ _ eff m m' evs h with rfl | ⟨fd, e, rfl⟩
  · exact hold
  · exact fd_table_unique_fd_insert _ _ _ hold

/-- The accepted model retains the pipe buffers. -/
theorem pipes_within_capacity_arm_socket : arm_preserves inv_pipes_within_capacity arm_socket := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  rcases Arms.check_socket_ok_post _ _ _ eff m m' evs h with rfl | ⟨fd, e, rfl⟩ <;> exact hold

/-- The VM frame above transports `vm_wf`. -/
theorem vm_wf_arm_socketpair : arm_preserves inv_vm_wf arm_socketpair :=
  Arms.arm_socketpair_preserves_vm

/-- Accepted results retain the descriptor table or install one entry
through `fd_insert`, which preserves unique descriptor keys. -/
theorem fd_table_unique_arm_socketpair : arm_preserves inv_fd_table_unique arm_socketpair := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_socketpair at h
  simp only [check_socketpair_written, check_socketpair_faulted] at h
  (repeat' vm_step h) <;>
    first
      | exact hold
      | exact fd_table_unique_fd_insert _ _ _ hold

/-- The accepted model retains the pipe buffers. -/
theorem pipes_within_capacity_arm_socketpair : arm_preserves inv_pipes_within_capacity arm_socketpair := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_socketpair at h
  simp only [check_socketpair_written, check_socketpair_faulted] at h
  (repeat' vm_step h) <;> exact hold

/-- The VM frame above transports `vm_wf`. -/
theorem vm_wf_arm_bind : arm_preserves inv_vm_wf arm_bind :=
  Arms.arm_bind_preserves_vm

/-- Accepted results retain the descriptor table or install one entry
through `fd_insert`, which preserves unique descriptor keys. -/
theorem fd_table_unique_arm_bind : arm_preserves inv_fd_table_unique arm_bind := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  rcases Arms.check_bind_ok_post i _ _ _ eff m m' evs h with rfl | ⟨fd, e, rfl⟩
  · exact hold
  · exact fd_table_unique_fd_insert _ _ _ hold

/-- The accepted model retains the pipe buffers. -/
theorem pipes_within_capacity_arm_bind : arm_preserves inv_pipes_within_capacity arm_bind := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  rcases Arms.check_bind_ok_post i _ _ _ eff m m' evs h with rfl | ⟨fd, e, rfl⟩ <;> exact hold

/-- The VM frame above transports `vm_wf`. -/
theorem vm_wf_arm_listen : arm_preserves inv_vm_wf arm_listen :=
  Arms.arm_listen_preserves_vm

/-- Accepted results retain the descriptor table or install one entry
through `fd_insert`, which preserves unique descriptor keys. -/
theorem fd_table_unique_arm_listen : arm_preserves inv_fd_table_unique arm_listen := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_listen at h
  simp only [check_errno_or_success] at h
  (repeat' vm_step h) <;>
    first
      | exact hold
      | exact fd_table_unique_fd_insert _ _ _ hold

/-- The accepted model retains the pipe buffers. -/
theorem pipes_within_capacity_arm_listen : arm_preserves inv_pipes_within_capacity arm_listen := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_listen at h
  simp only [check_errno_or_success] at h
  (repeat' vm_step h) <;> exact hold

/-- The VM frame above transports `vm_wf`. -/
theorem vm_wf_arm_accept : arm_preserves inv_vm_wf arm_accept :=
  Arms.arm_accept_preserves_vm

/-- Accepted results retain the descriptor table or install one entry
through `fd_insert`, which preserves unique descriptor keys. -/
theorem fd_table_unique_arm_accept : arm_preserves inv_fd_table_unique arm_accept := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_accept4 at h
  simp only [check_errno_only, Checks.Sys.Fs.Open.check_new_fd_result] at h
  (repeat' vm_step h) <;>
    first
      | exact hold
      | exact fd_table_unique_fd_insert _ _ _ hold

/-- The accepted model retains the pipe buffers. -/
theorem pipes_within_capacity_arm_accept : arm_preserves inv_pipes_within_capacity arm_accept := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_accept4 at h
  simp only [check_errno_only, Checks.Sys.Fs.Open.check_new_fd_result] at h
  (repeat' vm_step h) <;> exact hold

/-- The VM frame above transports `vm_wf`. -/
theorem vm_wf_arm_connect : arm_preserves inv_vm_wf arm_connect :=
  Arms.arm_connect_preserves_vm

/-- Accepted results retain the descriptor table or install one entry
through `fd_insert`, which preserves unique descriptor keys. -/
theorem fd_table_unique_arm_connect : arm_preserves inv_fd_table_unique arm_connect := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_connect at h
  generalize Sys.Syscall.sint32 (in_arg i 2) = al at h
  (repeat' vm_step h) <;>
    first
      | exact hold
      | exact fd_table_unique_fd_insert _ _ _ hold

/-- The accepted model retains the pipe buffers. -/
theorem pipes_within_capacity_arm_connect : arm_preserves inv_pipes_within_capacity arm_connect := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_connect at h
  generalize Sys.Syscall.sint32 (in_arg i 2) = al at h
  (repeat' vm_step h) <;> exact hold

/-- The VM frame above transports `vm_wf`. -/
theorem vm_wf_arm_getsockname : arm_preserves inv_vm_wf arm_getsockname :=
  Arms.arm_getsockname_preserves_vm

/-- Accepted results retain the descriptor table or install one entry
through `fd_insert`, which preserves unique descriptor keys. -/
theorem fd_table_unique_arm_getsockname : arm_preserves inv_fd_table_unique arm_getsockname := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_getsockname at h
  (repeat' vm_step h) <;>
    first
      | exact hold
      | exact fd_table_unique_fd_insert _ _ _ hold

/-- The accepted model retains the pipe buffers. -/
theorem pipes_within_capacity_arm_getsockname : arm_preserves inv_pipes_within_capacity arm_getsockname := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_getsockname at h
  (repeat' vm_step h) <;> exact hold

/-- The VM frame above transports `vm_wf`. -/
theorem vm_wf_arm_getpeername : arm_preserves inv_vm_wf arm_getpeername :=
  Arms.arm_getpeername_preserves_vm

/-- Accepted results retain the descriptor table or install one entry
through `fd_insert`, which preserves unique descriptor keys. -/
theorem fd_table_unique_arm_getpeername : arm_preserves inv_fd_table_unique arm_getpeername := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_getpeername at h
  (repeat' vm_step h) <;>
    first
      | exact hold
      | exact fd_table_unique_fd_insert _ _ _ hold

/-- The accepted model retains the pipe buffers. -/
theorem pipes_within_capacity_arm_getpeername : arm_preserves inv_pipes_within_capacity arm_getpeername := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_getpeername at h
  (repeat' vm_step h) <;> exact hold

/-- The VM frame above transports `vm_wf`. -/
theorem vm_wf_arm_shutdown : arm_preserves inv_vm_wf arm_shutdown :=
  Arms.arm_shutdown_preserves_vm

/-- Accepted results retain the descriptor table or install one entry
through `fd_insert`, which preserves unique descriptor keys. -/
theorem fd_table_unique_arm_shutdown : arm_preserves inv_fd_table_unique arm_shutdown := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_shutdown at h
  (repeat' vm_step h) <;>
    first
      | exact hold
      | exact fd_table_unique_fd_insert _ _ _ hold

/-- The accepted model retains the pipe buffers. -/
theorem pipes_within_capacity_arm_shutdown : arm_preserves inv_pipes_within_capacity arm_shutdown := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_shutdown at h
  (repeat' vm_step h) <;> exact hold

/-- The VM frame above transports `vm_wf`. -/
theorem vm_wf_arm_accept4 : arm_preserves inv_vm_wf arm_accept4 :=
  Arms.arm_accept4_preserves_vm

/-- Accepted results retain the descriptor table or install one entry
through `fd_insert`, which preserves unique descriptor keys. -/
theorem fd_table_unique_arm_accept4 : arm_preserves inv_fd_table_unique arm_accept4 := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_accept4 at h
  simp only [check_errno_only, Checks.Sys.Fs.Open.check_new_fd_result] at h
  (repeat' vm_step h) <;>
    first
      | exact hold
      | exact fd_table_unique_fd_insert _ _ _ hold

/-- The accepted model retains the pipe buffers. -/
theorem pipes_within_capacity_arm_accept4 : arm_preserves inv_pipes_within_capacity arm_accept4 := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_accept4 at h
  simp only [check_errno_only, Checks.Sys.Fs.Open.check_new_fd_result] at h
  (repeat' vm_step h) <;> exact hold

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

/-! ## V-Net-Socket-io: dispatcher registration

The four I/O checkers of `Checks/Sys/Net/Socket.lean`'s "sendto (206),
sendmsg (211), recvfrom (207), recvmsg (212)" section.  Their gates, and
the kernel functions they follow, are justified beside the checkers; the
registrations supply the ABI argument reading, which is Rocq's
`arm_sendto`, `arm_recvfrom`, `arm_sendmsg` and `arm_recvmsg` in
`theories/LinuxProcessSem/Checks/Sys/Dispatch.v` at f44244ad6b80, word for
word.  Every accepting leaf of the four checkers is `check_ret_only` or
`check_ret_only_copyins` over the model it was handed, so the frame and
invariant facts below are the `vm_step` loop with nothing to transport. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Net.Socket

/-- Rocq: `Checks.Sys.Dispatch.arm_sendto` at f44244ad6b80.
The ABI argument reading is shared with the existing registry row:
the fd is an `int`, read through `fd32`, and the other five words go
whole to the spec. -/
def arm_sendto : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 206 (fun i => Sys.Net.Socket.sendto_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)
  ca_check := fun i eff m => check_sendto i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m
  ca_witness := fun i m => sendto_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m
  ca_sound_ok := fun i eff m m' evs h => check_sendto_sound_ok i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h => check_sendto_sound_unmodeled i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m h
  ca_complete_ok := fun i eff m m' evs h => check_sendto_complete_ok i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h => check_sendto_complete_unmodeled i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m eff h
  ca_receptive := fun i m => sendto_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m

@[arm_unfold] theorem ca_check_arm_sendto (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_sendto.ca_check i eff m = check_sendto i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_sendto (i : SyscallInput) (m : Model) :
    arm_sendto.ca_witness i m = sendto_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m := rfl
@[arm_unfold] theorem sa_spec_arm_sendto (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_sendto.ca_arm.sa_spec i m o = Sys.Net.Socket.sendto_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o := rfl
@[arm_unfold] theorem ca_no_arm_sendto : ca_no arm_sendto = 206 := rfl

/-- Rocq: `Checks.Sys.Dispatch.arm_recvfrom` at f44244ad6b80.
The ABI argument reading is shared with the existing registry row. -/
def arm_recvfrom : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 207 (fun i => Sys.Net.Socket.recvfrom_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_recvfrom i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => recvfrom_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs h => check_recvfrom_sound_ok i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h => check_recvfrom_sound_unmodeled i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m h
  ca_complete_ok := fun i eff m m' evs h => check_recvfrom_complete_ok i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h => check_recvfrom_complete_unmodeled i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff h
  ca_receptive := fun i m => recvfrom_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_recvfrom (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_recvfrom.ca_check i eff m = check_recvfrom i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_recvfrom (i : SyscallInput) (m : Model) :
    arm_recvfrom.ca_witness i m = recvfrom_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl
@[arm_unfold] theorem sa_spec_arm_recvfrom (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_recvfrom.ca_arm.sa_spec i m o = Sys.Net.Socket.recvfrom_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_recvfrom : ca_no arm_recvfrom = 207 := rfl

/-- Rocq: `Checks.Sys.Dispatch.arm_sendmsg` at f44244ad6b80.
The ABI argument reading is shared with the existing registry row. -/
def arm_sendmsg : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 211 (fun i => Sys.Net.Socket.sendmsg_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_sendmsg i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => sendmsg_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs h => check_sendmsg_sound_ok i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h => check_sendmsg_sound_unmodeled i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m h
  ca_complete_ok := fun i eff m m' evs h => check_sendmsg_complete_ok i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h => check_sendmsg_complete_unmodeled i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff h
  ca_receptive := fun i m => sendmsg_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_sendmsg (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_sendmsg.ca_check i eff m = check_sendmsg i (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_sendmsg (i : SyscallInput) (m : Model) :
    arm_sendmsg.ca_witness i m = sendmsg_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl
@[arm_unfold] theorem sa_spec_arm_sendmsg (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_sendmsg.ca_arm.sa_spec i m o = Sys.Net.Socket.sendmsg_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_sendmsg : ca_no arm_sendmsg = 211 := rfl

/-- Rocq: `Checks.Sys.Dispatch.arm_recvmsg` at f44244ad6b80.
The ABI argument reading is shared with the existing registry row: the
`msg` pointer in a1 is not read (`check_recvmsg`'s docstring), so the
flag word in a2 is the second word passed. -/
def arm_recvmsg : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 212 (fun i => Sys.Net.Socket.recvmsg_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 2) i)
  ca_check := fun i eff m => check_recvmsg (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 2) eff m
  ca_witness := fun i m => recvmsg_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 2) m
  ca_sound_ok := fun i eff m m' evs h => check_recvmsg_sound_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 2) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h => check_recvmsg_sound_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 2) eff m i h
  ca_complete_ok := fun i eff m m' evs h => check_recvmsg_complete_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 2) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h => check_recvmsg_complete_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 2) m eff i h
  ca_receptive := fun i m => recvmsg_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_recvmsg (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_recvmsg.ca_check i eff m = check_recvmsg (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 2) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_recvmsg (i : SyscallInput) (m : Model) :
    arm_recvmsg.ca_witness i m = recvmsg_witness (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 2) m := rfl
@[arm_unfold] theorem sa_spec_arm_recvmsg (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_recvmsg.ca_arm.sa_spec i m o = Sys.Net.Socket.recvmsg_spec (Sys.Syscall.fd32 (in_arg i 0)) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_recvmsg : ca_no arm_recvmsg = 212 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Net.Socket

/-- Lean-only frame for Rocq's `VmMapsDisjoint.check_sendto_frame`:
the range verdict and the socket half are opened, and every accepting
leaf hands the model back. -/
theorem arm_sendto_preserves_vm : arm_preserves_vm arm_sendto :=
  arm_preserves_of_frame arm_sendto (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    unfold check_sendto Checks.Sys.Uaccess.check_access_ok_zero check_send_on_socket at h
    vm_frame h)

/-- Lean-only frame for Rocq's `VmMapsDisjoint.check_recvfrom_frame`. -/
theorem arm_recvfrom_preserves_vm : arm_preserves_vm arm_recvfrom :=
  arm_preserves_of_frame arm_recvfrom (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    unfold check_recvfrom Checks.Sys.Uaccess.check_access_ok_zero check_recv_fd_answer at h
    vm_frame h)

/-- Lean-only frame for Rocq's `VmMapsDisjoint.check_sendmsg_frame`. -/
theorem arm_sendmsg_preserves_vm : arm_preserves_vm arm_sendmsg :=
  arm_preserves_of_frame arm_sendmsg (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    unfold check_sendmsg check_send_on_socket at h
    vm_frame h)

/-- Lean-only frame for Rocq's `VmMapsDisjoint.check_recvmsg_frame`. -/
theorem arm_recvmsg_preserves_vm : arm_preserves_vm arm_recvmsg :=
  arm_preserves_of_frame arm_recvmsg (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    unfold check_recvmsg check_recv_fd_answer at h
    vm_frame h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Net.Socket
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- The VM frame above transports `vm_wf`. -/
theorem vm_wf_arm_sendto : arm_preserves inv_vm_wf arm_sendto :=
  Arms.arm_sendto_preserves_vm

/-- The accepted model is the model handed in, so its descriptor table is. -/
theorem fd_table_unique_arm_sendto : arm_preserves inv_fd_table_unique arm_sendto := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_sendto Checks.Sys.Uaccess.check_access_ok_zero check_send_on_socket at h
  (repeat' vm_step h) <;> exact hold

/-- The accepted model is the model handed in, so its pipe buffers are. -/
theorem pipes_within_capacity_arm_sendto : arm_preserves inv_pipes_within_capacity arm_sendto := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_sendto Checks.Sys.Uaccess.check_access_ok_zero check_send_on_socket at h
  (repeat' vm_step h) <;> exact hold

/-- The VM frame above transports `vm_wf`. -/
theorem vm_wf_arm_recvfrom : arm_preserves inv_vm_wf arm_recvfrom :=
  Arms.arm_recvfrom_preserves_vm

/-- The accepted model is the model handed in, so its descriptor table is. -/
theorem fd_table_unique_arm_recvfrom : arm_preserves inv_fd_table_unique arm_recvfrom := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_recvfrom Checks.Sys.Uaccess.check_access_ok_zero check_recv_fd_answer at h
  (repeat' vm_step h) <;> exact hold

/-- The accepted model is the model handed in, so its pipe buffers are. -/
theorem pipes_within_capacity_arm_recvfrom : arm_preserves inv_pipes_within_capacity arm_recvfrom := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_recvfrom Checks.Sys.Uaccess.check_access_ok_zero check_recv_fd_answer at h
  (repeat' vm_step h) <;> exact hold

/-- The VM frame above transports `vm_wf`. -/
theorem vm_wf_arm_sendmsg : arm_preserves inv_vm_wf arm_sendmsg :=
  Arms.arm_sendmsg_preserves_vm

/-- The accepted model is the model handed in, so its descriptor table is. -/
theorem fd_table_unique_arm_sendmsg : arm_preserves inv_fd_table_unique arm_sendmsg := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_sendmsg check_send_on_socket at h
  (repeat' vm_step h) <;> exact hold

/-- The accepted model is the model handed in, so its pipe buffers are. -/
theorem pipes_within_capacity_arm_sendmsg : arm_preserves inv_pipes_within_capacity arm_sendmsg := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_sendmsg check_send_on_socket at h
  (repeat' vm_step h) <;> exact hold

/-- The VM frame above transports `vm_wf`. -/
theorem vm_wf_arm_recvmsg : arm_preserves inv_vm_wf arm_recvmsg :=
  Arms.arm_recvmsg_preserves_vm

/-- The accepted model is the model handed in, so its descriptor table is. -/
theorem fd_table_unique_arm_recvmsg : arm_preserves inv_fd_table_unique arm_recvmsg := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_recvmsg check_recv_fd_answer at h
  (repeat' vm_step h) <;> exact hold

/-- The accepted model is the model handed in, so its pipe buffers are. -/
theorem pipes_within_capacity_arm_recvmsg : arm_preserves inv_pipes_within_capacity arm_recvmsg := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  unfold check_recvmsg check_recv_fd_answer at h
  (repeat' vm_step h) <;> exact hold

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
