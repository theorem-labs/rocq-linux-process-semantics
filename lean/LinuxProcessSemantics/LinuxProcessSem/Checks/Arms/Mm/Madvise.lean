import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Madvise
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Mm.Madvise — madvise on the checked surface

The registration of `Checks/Sys/Mm/Madvise.lean`'s checker in
`checked_table`, in the one file that registration writes.
`tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files
under `Checks/Arms/`, one per checker twin, so that registering an arm
creates or edits no hub but this file; its docstring is the shape it reads
and what it refuses. The file holds three sections, each in the
namespace its declarations had when those three hubs were written by
hand, so that no name moved with the file:

- `Checks.Sys.Table`: the `CheckedArm` (`arm_madvise`) and its four
  `arm_unfold` lemmas;
- `Checks.VmMapsDisjoint.Arms`: the arm's ledger fact,
  `arm_madvise_preserves_vm`, which `checked_table_preserves_vm`'s
  alternation names;
- `Checks.Invariants`: one `<invariant>_arm_madvise` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`, which
  `registry_preserves`'s alternation names, and the descriptor frame
  the two `m_fd` entries rest on.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arm is the row of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table`, read at that commit. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### madvise (233) -/

/-- madvise (233).  THE ADDRESS AND LENGTH ARE `a0` AND `a1` WHOLE, THE
ADVICE IS `a2` CUT TO ITS LOW 32 BITS.  riscv64's `__riscv_sys_madvise`
hands the registers over in order, `orig_a0`, `a1`, `a2`
(`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24,
Linux v6.18.46), and the wrapper narrows each to the type
`SYSCALL_DEFINE3(madvise, unsigned long, start, size_t, len_in, int,
behavior)` declares (mm/madvise.c:1990-1993, same version) through
`__SC_CAST` (include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46): the two
64-bit types keep the register, and `int behavior` keeps its low word.
`do_madvise` (mm/madvise.c:1967-1988, same version) hands all three to
`madvise_should_skip` before anything else, so the gates the spec models
read `start` as the register holds it; the `get_untagged_addr` applied
after them (mm/madvise.c:1883) is the identity while the process's
pointer-masking length is zero (`__untagged_addr_remote`,
arch/riscv/include/asm/uaccess.h:16-29, Linux v6.18.46): `activate_mm`
zeroes it (arch/riscv/include/asm/mmu_context.h:19-27, same version), and
`exec_mmap` calls it on `execve` (fs/exec.c:890, same version); only
`set_tagged_addr_ctrl` (arch/riscv/kernel/process.c:285, same version)
sets it again.
`Sys.Syscall.int32 (in_arg i 2)` is the narrowing, applied here at the
boundary as Rocq's `arm_madvise` applies it, so the checker and the
witness receive the narrowed word and neither narrows again.  Reading the
advice whole would not be a decline but a wrong answer: an advice of
`2^32 + MADV_DONTNEED` is `MADV_DONTNEED` to the kernel and would fail the
spec's advice gate as garbage.  `ca_arm` is the term
`Sys/Registry/Mm/Madvise.lean`'s row builds, which `checked_table_arms`
checks.  The ledger fact this arm owes `checked_table_preserves_vm` is
`check_madvise_frame`, beside the checker. -/
def arm_madvise : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 233 (fun i => Sys.Mm.Madvise.madvise_spec (in_arg i 0)
    (in_arg i 1) (Sys.Syscall.int32 (in_arg i 2)) i)
  ca_check := fun i eff m => Checks.Sys.Mm.Madvise.check_madvise (in_arg i 0) (in_arg i 1)
    (Sys.Syscall.int32 (in_arg i 2)) eff m
  ca_witness := fun i m => Checks.Sys.Mm.Madvise.madvise_witness (in_arg i 0) (in_arg i 1)
    (Sys.Syscall.int32 (in_arg i 2)) m
  ca_sound_ok := fun i eff m m' evs h => Checks.Sys.Mm.Madvise.check_madvise_sound_ok
    (in_arg i 0) (in_arg i 1) (Sys.Syscall.int32 (in_arg i 2)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h => Checks.Sys.Mm.Madvise.check_madvise_sound_unmodeled
    (in_arg i 0) (in_arg i 1) (Sys.Syscall.int32 (in_arg i 2)) eff m i h
  ca_complete_ok := fun i eff m m' evs h => Checks.Sys.Mm.Madvise.check_madvise_complete_ok
    (in_arg i 0) (in_arg i 1) (Sys.Syscall.int32 (in_arg i 2)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Mm.Madvise.check_madvise_complete_unmodeled (in_arg i 0) (in_arg i 1)
      (Sys.Syscall.int32 (in_arg i 2)) m i eff h
  ca_receptive := fun i m => Checks.Sys.Mm.Madvise.madvise_witness_ok (in_arg i 0)
    (in_arg i 1) (Sys.Syscall.int32 (in_arg i 2)) i m

@[arm_unfold] theorem ca_check_arm_madvise (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_madvise.ca_check i eff m = Checks.Sys.Mm.Madvise.check_madvise (in_arg i 0)
      (in_arg i 1) (Sys.Syscall.int32 (in_arg i 2)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_madvise (i : SyscallInput) (m : Model) :
    arm_madvise.ca_witness i m = Checks.Sys.Mm.Madvise.madvise_witness (in_arg i 0)
      (in_arg i 1) (Sys.Syscall.int32 (in_arg i 2)) m := rfl
@[arm_unfold] theorem sa_spec_arm_madvise (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_madvise.ca_arm.sa_spec i m o
      = Sys.Mm.Madvise.madvise_spec (in_arg i 0) (in_arg i 1)
          (Sys.Syscall.int32 (in_arg i 2)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_madvise : ca_no arm_madvise = 233 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `madvise` (233): every answer the checker accepts leaves `vm_maps`
where they were — the three return-only answers hand back the model they
were given, and the zap moves the materialized-page ledger alone
(`check_madvise_frame`, stated beside the checker in
`Checks/Sys/Mm/Madvise.lean`, Rocq's `VmMapsDisjoint.check_madvise_frame`). -/
theorem arm_madvise_preserves_vm : arm_preserves_vm arm_madvise :=
  arm_preserves_of_frame arm_madvise (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Mm.Madvise.check_madvise_frame _ _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Madvise
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## The descriptor-state frame

The two registry entries beside `vm_wf` read the `m_fd` subsystem, so one
frame lemma over the whole record answers both.  The tree's rule is that a
checker's frame lemma lives beside the checker, in
`Checks/Sys/Mm/Madvise.lean`; it is here because the checker file is not
the registration's to edit, the placement `Checks/Arms/Mm/Mmap.lean`
gives its own `check_mmap_fd_state_frame` for the same reason, and moving
it beside the checker changes nothing but its home.  Lean-only: the Rocq
tree registers no `m_fd` invariant, so there is no twin. -/

/-- `check_madvise` writes the materialized-page ledger and nothing else,
so the descriptor subsystem is the one it was handed.  The walk is
`check_madvise_frame`'s, gate for gate: three of the accepted answers are
`check_ret_only`'s, whose model is the one handed in, and the fourth is
`madvise_dontneed_next`, a `with_vm_backing` that carries `m.m_fd` across
(`State/Model.lean`), so each branch closes by `rfl`.  A gate added to the
checker and not here leaves an unsolved `if` rather than passing. -/
theorem check_madvise_fd_state_frame (addr len advice : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_madvise addr len advice eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold check_madvise at h
  cases halign : (bv_unsigned addr % page_size == 0)
  · simp only [halign, Bool.not_false, ↓reduceIte] at h
    rw [check_ret_only_model h]
  simp only [halign, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hadv : madvise_dontneed_b advice
  · simp only [hadv, Bool.not_false, ↓reduceIte] at h
    cases h
  simp only [hadv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hlen : w_is0 len
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at h
    cases hbig : decide (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len))
    · have hnb : ¬ (two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)) :=
        of_decide_eq_false hbig
      simp only [hnb, ↓reduceIte] at h
      cases hok : madvise_dontneed_ok (m_vmmaps m) addr
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
      · simp only [hok, Bool.false_eq_true, ↓reduceIte] at h
        cases h
      simp only [hok, ↓reduceIte] at h
      obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
      cases ws <;> cases us <;> cases cs <;> cases ci <;> simp only [reduceCtorEq] at h
      split at h
      · simp only [check_result.CheckOk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rfl
      · simp only [reduceCtorEq] at h
    have hb : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) :=
      of_decide_eq_true hbig
    simp only [hb, ↓reduceIte] at h
    rw [check_ret_only_model h]
  · simp only [hlen, ↓reduceIte] at h
    rw [check_ret_only_model h]

/-- `vm_wf` × `madvise`: the ledger fact above. -/
theorem vm_wf_arm_madvise : arm_preserves inv_vm_wf arm_madvise :=
  Arms.arm_madvise_preserves_vm

/-- `fd_table_unique` × `madvise`: advice over anonymous memory binds and
closes no descriptor; the frame is the one above. -/
theorem fd_table_unique_arm_madvise : arm_preserves inv_fd_table_unique arm_madvise :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_madvise (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_madvise_fd_state_frame _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `madvise`: no pipe is touched. -/
theorem pipes_within_capacity_arm_madvise :
    arm_preserves inv_pipes_within_capacity arm_madvise :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_madvise (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_madvise_fd_state_frame _ _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
