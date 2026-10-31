import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Stat
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Fs.Stat — stat checkers on the checked surface

The registration follows `tools/gen_lean_checked.py`'s ARM-1 through ARM-7.
The frame lemmas live here because the checker twin belongs to the C ticket
and `Checks/VmMapsDisjoint.lean` is frozen: registration supplies the facts
its generated ledger and invariant alternations consume.

The Rocq dispatch rows are byte-identical at f44244ad6b80, a71fd38a and
HEAD, but the full `check_fstat_chrdev_frame` / `check_fstat_devnull_frame` /
`check_fstat_urandom_frame` family in `Checks/VmMapsDisjoint.v` exists only
from a71fd38a on (f44244ad6b80 already has the standalone devnull lemma),
hence the checker twin's baseline above.

A successful fstat can record a stat pin: `State.with_statpin` rebuilds
only `m_proc`'s `procst_statpins`, carrying `m_fd` and `m_vm` through.
The frame proofs must account for that update, not assume the model is
unchanged. No spec or checker behavior is changed by registration. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/-- readlinkat (78). `SYSCALL_DEFINE4(readlinkat, ...)`
(fs/stat.c:604-605, Linux v6.18.46, commit 1f99e9ab748f):
`int dfd` is a0, `pathname` is a1, `buf` is a2 and `int bufsiz` is a3.
The checker consumes only dfd; its other registers remain unread.
`__NR_readlinkat` (include/uapi/asm-generic/unistd.h:206-207, Linux v6.18.46)
selects `sys_readlinkat` on riscv64 through `__SYSCALL`.
`SC_RISCV_REGS_TO_ARGS` (arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46)
passes the registers in order, and `__SYSCALL_DEFINEx` applies `__SC_CAST`
(include/linux/syscalls.h:132, Linux v6.18.46) at syscall_wrapper.h:88, all at that commit.
Both `int` and `unsigned int` are 32-bit, so `fd32` retains the low half
of a0; pointers retain the whole register. The spec, checker and witness
receive the same decoded arguments, as Rocq's row does. -/
def arm_readlinkat : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 78 (fun i => Sys.Fs.Stat.readlinkat_spec (fd32 (in_arg i 0)) i)
  ca_check := fun i eff m => Checks.Sys.Fs.Stat.check_readlinkat (fd32 (in_arg i 0)) eff m
  ca_witness := fun i m => Checks.Sys.Fs.Stat.readlinkat_witness (fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Stat.check_readlinkat_sound_ok (fd32 (in_arg i 0)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Stat.check_readlinkat_sound_unmodeled (fd32 (in_arg i 0)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Stat.check_readlinkat_complete_ok (fd32 (in_arg i 0)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Stat.check_readlinkat_complete_unmodeled (fd32 (in_arg i 0)) m i eff h
  ca_receptive := fun i m => Checks.Sys.Fs.Stat.readlinkat_witness_ok (fd32 (in_arg i 0)) i m

@[arm_unfold] theorem ca_check_arm_readlinkat (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_readlinkat.ca_check i eff m = Checks.Sys.Fs.Stat.check_readlinkat (fd32 (in_arg i 0)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_readlinkat (i : SyscallInput) (m : Model) :
    arm_readlinkat.ca_witness i m = Checks.Sys.Fs.Stat.readlinkat_witness (fd32 (in_arg i 0)) m := rfl
@[arm_unfold] theorem sa_spec_arm_readlinkat (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_readlinkat.ca_arm.sa_spec i m o = Sys.Fs.Stat.readlinkat_spec (fd32 (in_arg i 0)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_readlinkat : ca_no arm_readlinkat = 78 := rfl

/-- newfstatat (79). `SYSCALL_DEFINE4(newfstatat, ...)`
(fs/stat.c:536-537, Linux v6.18.46, commit 1f99e9ab748f):
`int dfd` is a0, `filename` is a1, `statbuf` is a2 and `int flag` is a3.
The arm passes the pathname pointer whole and narrows flag with `flag32`;
the checker never delivers to statbuf on its modeled surface.
`__NR3264_fstatat` (include/uapi/asm-generic/unistd.h:210-211, Linux v6.18.46)
selects `sys_newfstatat` on riscv64 (`__SC_3264`, :19-23).
`SC_RISCV_REGS_TO_ARGS` (arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46)
passes the registers in order, and `__SYSCALL_DEFINEx` applies `__SC_CAST`
(include/linux/syscalls.h:132, Linux v6.18.46) at syscall_wrapper.h:88, all at that commit.
Both `int` and `unsigned int` are 32-bit, so `fd32` retains the low half
of a0; pointers retain the whole register. The spec, checker and witness
receive the same decoded arguments, as Rocq's row does. -/
def arm_newfstatat : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 79 (fun i => Sys.Fs.Stat.newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i)
  ca_check := fun i eff m => Checks.Sys.Fs.Stat.check_newfstatat i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) eff m
  ca_witness := fun i m => Checks.Sys.Fs.Stat.newfstatat_witness (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Stat.check_newfstatat_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Stat.check_newfstatat_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Stat.check_newfstatat_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Stat.check_newfstatat_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) m eff h
  ca_receptive := fun i m => Checks.Sys.Fs.Stat.newfstatat_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i m

@[arm_unfold] theorem ca_check_arm_newfstatat (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_newfstatat.ca_check i eff m = Checks.Sys.Fs.Stat.check_newfstatat i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_newfstatat (i : SyscallInput) (m : Model) :
    arm_newfstatat.ca_witness i m = Checks.Sys.Fs.Stat.newfstatat_witness (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i m := rfl
@[arm_unfold] theorem sa_spec_arm_newfstatat (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_newfstatat.ca_arm.sa_spec i m o = Sys.Fs.Stat.newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_newfstatat : ca_no arm_newfstatat = 79 := rfl

/-- fstat (80). `SYSCALL_DEFINE2(newfstat, ...)`
(fs/stat.c:550, Linux v6.18.46, commit 1f99e9ab748f):
`unsigned int fd` is a0 and `statbuf` is a1.
The arm passes the destination pointer whole.
`__NR3264_fstat` (include/uapi/asm-generic/unistd.h:212-213, Linux v6.18.46)
selects `sys_newfstat` on riscv64 (`__SC_3264`, :19-23).
`SC_RISCV_REGS_TO_ARGS` (arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46)
passes the registers in order, and `__SYSCALL_DEFINEx` applies `__SC_CAST`
(include/linux/syscalls.h:132, Linux v6.18.46) at syscall_wrapper.h:88, all at that commit.
Both `int` and `unsigned int` are 32-bit, so `fd32` retains the low half
of a0; pointers retain the whole register. The spec, checker and witness
receive the same decoded arguments, as Rocq's row does. -/
def arm_fstat : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 80 (fun i => Sys.Fs.Stat.fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i)
  ca_check := fun i eff m => Checks.Sys.Fs.Stat.check_fstat i (fd32 (in_arg i 0)) (in_arg i 1) eff m
  ca_witness := fun i m => Checks.Sys.Fs.Stat.fstat_witness (fd32 (in_arg i 0)) (in_arg i 1) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Stat.check_fstat_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Stat.check_fstat_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Stat.check_fstat_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Stat.check_fstat_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) m eff h
  ca_receptive := fun i m => Checks.Sys.Fs.Stat.fstat_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) i m

@[arm_unfold] theorem ca_check_arm_fstat (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_fstat.ca_check i eff m = Checks.Sys.Fs.Stat.check_fstat i (fd32 (in_arg i 0)) (in_arg i 1) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_fstat (i : SyscallInput) (m : Model) :
    arm_fstat.ca_witness i m = Checks.Sys.Fs.Stat.fstat_witness (fd32 (in_arg i 0)) (in_arg i 1) i m := rfl
@[arm_unfold] theorem sa_spec_arm_fstat (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_fstat.ca_arm.sa_spec i m o = Sys.Fs.Stat.fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i m o := rfl
@[arm_unfold] theorem ca_no_arm_fstat : ca_no arm_fstat = 80 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Stat
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- Lean-only: every accepted readlinkat leaf returns the input model. -/
theorem check_readlinkat_ok_model (dirfd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_readlinkat dirfd eff m = CheckOk m' evs) : m' = m := by
  simp only [check_readlinkat] at h
  split at h
  · cases h
  · exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1

/-- Lean-only: the pathname ledger changes the effect, never the model. -/
theorem check_newfstatat_ok_model (i : SyscallInput) (dirfd pathp flag : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs) : m' = m := by
  simp only [check_newfstatat] at h
  split at h
  · cases h
  · split at h
    · exact ((check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h).2.1
    · exact ((check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h).2.1
    · split at h
      · exact ((check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h).2.1
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · exact ((check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h).2.1
            · cases h

/-- Lean-only: a file delivery either preserves the model or records its
first stat pin; the delivery inversion is the checker's theorem. -/
theorem check_fstat_file_ok_post (i : SyscallInput) (p : path) (statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_fstat_file i p statbuf eff m = CheckOk m' evs) :
    m' = m ∨ ∃ bs, m' = with_statpin p bs m := by
  simp only [check_fstat_file] at h
  split at h
  · cases h
  · rename_i data _
    split at h
    · exact Or.inl ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1
    · split at h
      · cases h
      · have delivery : ∃ pin, check_fstat_deliver statbuf data.length p pin eff m = CheckOk m' evs := by
          split at h
          · split at h
            · cases h
            · exact ⟨_, h⟩
          · exact ⟨_, h⟩
        obtain ⟨pin, hd⟩ := delivery
        obtain ⟨bs, -, -, -, -, hp⟩ := check_fstat_deliver_ok _ _ _ pin _ _ _ _ hd
        cases hp with
        | inl hp =>
          obtain ⟨_, -, -, hm⟩ := hp
          exact Or.inl hm
        | inr hp => exact Or.inr ⟨bs, hp.2⟩

/-- Lean-only: the character-device delivery has the same two post-models. -/
theorem check_fstat_chrdev_ok_post (ok : List byte → Bool) (p : path)
    (i : SyscallInput) (statbuf : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_fstat_chrdev ok p i statbuf eff m = CheckOk m' evs) :
    m' = m ∨ ∃ bs, m' = with_statpin p bs m := by
  simp only [check_fstat_chrdev] at h
  split at h
  · exact Or.inl ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1
  · split at h
    · cases h
    · have delivery : ∃ pin, check_fstat_deliver_by ok statbuf p pin eff m = CheckOk m' evs := by
        split at h
        · split at h
          · cases h
          · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      obtain ⟨pin, hd⟩ := delivery
      obtain ⟨bs, -, -, -, -, hp⟩ := check_fstat_deliver_by_ok _ _ _ pin _ _ _ _ hd
      cases hp with
      | inl hp =>
        obtain ⟨_, -, -, hm⟩ := hp
        exact Or.inl hm
      | inr hp => exact Or.inr ⟨bs, hp.2⟩

/-- Rocq: `VmMapsDisjoint.check_readlinkat_frame`. Every accepted errno
returns the original model, so the memory ledger is preserved. -/
theorem check_readlinkat_frame (dirfd : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_readlinkat dirfd eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  obtain rfl := check_readlinkat_ok_model dirfd eff m m' evs h
  rfl

/-- Rocq: `VmMapsDisjoint.check_newfstatat_frame`. Every accepted errno
returns the original model, so the memory ledger is preserved. -/
theorem check_newfstatat_frame (i : SyscallInput) (dirfd pathp flag : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  obtain rfl := check_newfstatat_ok_model i dirfd pathp flag eff m m' evs h
  rfl

/-- Rocq: `VmMapsDisjoint.check_fstat_file_frame`. The memory ledger is
preserved, including when a successful delivery records a stat pin. -/
theorem check_fstat_file_frame (i : SyscallInput) (p : path) (statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_fstat_file i p statbuf eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  cases check_fstat_file_ok_post i p statbuf eff m m' evs h with
  | inl hm => simp only [hm]
  | inr hp =>
    obtain ⟨bs, rfl⟩ := hp
    exact m_vmmaps_with_statpin p bs m

/-- Rocq: `VmMapsDisjoint.check_fstat_chrdev_frame`. The memory ledger is
preserved, including when a successful delivery records a stat pin. -/
theorem check_fstat_chrdev_frame (ok : List byte → Bool) (p : path) (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_fstat_chrdev ok p i statbuf eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  cases check_fstat_chrdev_ok_post ok p i statbuf eff m m' evs h with
  | inl hm => simp only [hm]
  | inr hp =>
    obtain ⟨bs, rfl⟩ := hp
    exact m_vmmaps_with_statpin p bs m

/-- Rocq: `VmMapsDisjoint.check_fstat_devnull_frame`. Specialize the
character-device frame to this device's predicate and pin key. -/
theorem check_fstat_devnull_frame (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_fstat_devnull i statbuf eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m :=
  check_fstat_chrdev_frame _ _ i statbuf eff m m' evs h

/-- Rocq: `VmMapsDisjoint.check_fstat_urandom_frame`. Specialize the
character-device frame to this device's predicate and pin key. -/
theorem check_fstat_urandom_frame (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_fstat_urandom i statbuf eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m :=
  check_fstat_chrdev_frame _ _ i statbuf eff m m' evs h

/-- Rocq: `VmMapsDisjoint.check_fstat_frame`. The descriptor selects a
file or device frame; an absent descriptor returns the original model. -/
theorem check_fstat_frame (i : SyscallInput) (fd statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_fstat i fd statbuf eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  simp only [check_fstat] at h
  split at h
  · obtain rfl := ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1
    rfl
  · cases h
  · exact check_fstat_file_frame _ _ _ _ _ _ _ h
  · exact check_fstat_file_frame _ _ _ _ _ _ _ h
  -- `FdFileA` and `FdFileRW` go through `check_fstat_file` with the other
  -- two file kinds, so they take the file frame, not a decline.
  · exact check_fstat_file_frame _ _ _ _ _ _ _ h
  · exact check_fstat_file_frame _ _ _ _ _ _ _ h
  · cases h
  · cases h
  · cases h
  · exact check_fstat_devnull_frame _ _ _ _ _ _ h
  · exact check_fstat_urandom_frame _ _ _ _ _ _ h

/-- The ledger frame supplies the arm's VM invariant. -/
theorem arm_readlinkat_preserves_vm : arm_preserves_vm arm_readlinkat :=
  arm_preserves_of_frame arm_readlinkat (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_readlinkat_frame _ eff m m' evs h)

/-- The ledger frame supplies the arm's VM invariant. -/
theorem arm_newfstatat_preserves_vm : arm_preserves_vm arm_newfstatat :=
  arm_preserves_of_frame arm_newfstatat (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_newfstatat_frame _ _ _ _ eff m m' evs h)

/-- The ledger frame supplies the arm's VM invariant. -/
theorem arm_fstat_preserves_vm : arm_preserves_vm arm_fstat :=
  arm_preserves_of_frame arm_fstat (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_fstat_frame _ _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Stat
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- Lean-only: the checker returns the same model, hence the same fd state. -/
theorem check_readlinkat_fd_state_frame (dirfd : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_readlinkat dirfd eff m = CheckOk m' evs) : m'.m_fd = m.m_fd := by
  obtain rfl := Arms.check_readlinkat_ok_model dirfd eff m m' evs h
  rfl

/-- Lean-only: the checker returns the same model, hence the same fd state. -/
theorem check_newfstatat_fd_state_frame (i : SyscallInput) (dirfd pathp flag : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs) : m'.m_fd = m.m_fd := by
  obtain rfl := Arms.check_newfstatat_ok_model i dirfd pathp flag eff m m' evs h
  rfl

/-- Lean-only: `with_statpin` carries `m_fd` unchanged (State/Model.lean);
the file and character-device post-model lemmas cover every successful leaf. -/
theorem check_fstat_fd_state_frame (i : SyscallInput) (fd statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_fstat i fd statbuf eff m = CheckOk m' evs) : m'.m_fd = m.m_fd := by
  simp only [check_fstat] at h
  split at h
  · obtain rfl := ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1
    rfl
  · cases h
  · cases Arms.check_fstat_file_ok_post _ _ _ _ _ _ _ h with
    | inl hm => simp only [hm]
    | inr hp => obtain ⟨_, rfl⟩ := hp; rfl
  · cases Arms.check_fstat_file_ok_post _ _ _ _ _ _ _ h with
    | inl hm => simp only [hm]
    | inr hp => obtain ⟨_, rfl⟩ := hp; rfl
  -- The two file kinds added to `check_fstat`'s file arm: same post-model
  -- case split as `FdFile` and `FdFileW` above.
  · cases Arms.check_fstat_file_ok_post _ _ _ _ _ _ _ h with
    | inl hm => simp only [hm]
    | inr hp => obtain ⟨_, rfl⟩ := hp; rfl
  · cases Arms.check_fstat_file_ok_post _ _ _ _ _ _ _ h with
    | inl hm => simp only [hm]
    | inr hp => obtain ⟨_, rfl⟩ := hp; rfl
  · cases h
  · cases h
  · cases h
  · cases Arms.check_fstat_chrdev_ok_post _ _ _ _ _ _ _ _ h with
    | inl hm => simp only [hm]
    | inr hp => obtain ⟨_, rfl⟩ := hp; rfl
  · cases Arms.check_fstat_chrdev_ok_post _ _ _ _ _ _ _ _ h with
    | inl hm => simp only [hm]
    | inr hp => obtain ⟨_, rfl⟩ := hp; rfl

/-- The VM invariant follows from the ledger frame. -/
theorem vm_wf_arm_readlinkat : arm_preserves inv_vm_wf arm_readlinkat :=
  Arms.arm_readlinkat_preserves_vm

/-- The descriptor-state frame preserves this registry view. -/
theorem fd_table_unique_arm_readlinkat : arm_preserves inv_fd_table_unique arm_readlinkat :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_readlinkat (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_readlinkat_fd_state_frame _ eff m m' evs h))

/-- The descriptor-state frame preserves this registry view. -/
theorem pipes_within_capacity_arm_readlinkat : arm_preserves inv_pipes_within_capacity arm_readlinkat :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_readlinkat (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_readlinkat_fd_state_frame _ eff m m' evs h))

/-- The VM invariant follows from the ledger frame. -/
theorem vm_wf_arm_newfstatat : arm_preserves inv_vm_wf arm_newfstatat :=
  Arms.arm_newfstatat_preserves_vm

/-- The descriptor-state frame preserves this registry view. -/
theorem fd_table_unique_arm_newfstatat : arm_preserves inv_fd_table_unique arm_newfstatat :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_newfstatat (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_newfstatat_fd_state_frame _ _ _ _ eff m m' evs h))

/-- The descriptor-state frame preserves this registry view. -/
theorem pipes_within_capacity_arm_newfstatat : arm_preserves inv_pipes_within_capacity arm_newfstatat :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_newfstatat (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_newfstatat_fd_state_frame _ _ _ _ eff m m' evs h))

/-- The VM invariant follows from the ledger frame. -/
theorem vm_wf_arm_fstat : arm_preserves inv_vm_wf arm_fstat :=
  Arms.arm_fstat_preserves_vm

/-- The descriptor-state frame preserves this registry view. -/
theorem fd_table_unique_arm_fstat : arm_preserves inv_fd_table_unique arm_fstat :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_fstat (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_fstat_fd_state_frame _ _ _ eff m m' evs h))

/-- The descriptor-state frame preserves this registry view. -/
theorem pipes_within_capacity_arm_fstat : arm_preserves inv_pipes_within_capacity arm_fstat :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_fstat (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_fstat_fd_state_frame _ _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
