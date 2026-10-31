import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mprotect
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Mm.Mprotect — mprotect on the checked surface

The registration of `Checks/Sys/Mm/Mprotect.lean`'s checker in
`checked_table`, in the one file that registration writes;
`tools/gen_lean_checked.py`'s docstring is the shape it reads and what it
refuses.  The file holds four sections:

- `Checks.Sys.Table`: the `CheckedArm` `arm_mprotect` and its four
  `arm_unfold` lemmas;
- `Checks.Sys.Mm.Mprotect`: the two checker facts the arm's obligations
  are built from, which the checker's own file could not carry (below);
- `Checks.VmMapsDisjoint.Arms`: the ledger fact
  `arm_mprotect_preserves_vm`;
- `Checks.Invariants`: one `<invariant>_arm_mprotect` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`.

WHY TWO CHECKER FACTS LIVE HERE AND NOT BESIDE THE CHECKER.  The tree's
rule is that a checker's frame and `_preserves` lemmas arrive with it, in
its own file (`Checks/VmMapsDisjoint.lean`, "WHAT IS NOT HERE").  The
mprotect checker landed on a base that predated the ledger module, so it
states the one projection Rocq's `check_mprotect_preserves` turns on —
`check_mprotect_vm_maps`, an accepting run keeps `vm_maps` — and leaves
the `vm_wf` statement to the registration (its header, "WHAT IS NOT HERE,
AND WHOSE IT IS").  The registration writes this file and no other Lean
file outside `Checks/Cases/`, so the twin of Rocq's lemma is stated here,
in the checker's namespace, under its Rocq name; so is the descriptor
frame the two `m_fd` entries need, which Rocq has no counterpart for
because the Rocq tree registers no `m_fd` invariant.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arm is the row of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table`, read at that commit, and `check_mprotect_preserves` is
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`'s, identical there and
at the day branch this was written on. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### mprotect (226) -/

/-- mprotect (226).  The three registers are read whole, in order, as
`mprotect_spec` reads them: `SYSCALL_DEFINE3(mprotect, unsigned long,
start, size_t, len, unsigned long, prot)` (mm/mprotect.c, Linux v6.18.46)
declares three 64-bit types on riscv64, which riscv's wrapper takes from
`orig_a0`, `a1` and `a2` in that order (`SC_RISCV_REGS_TO_ARGS` under
`CONFIG_64BIT`, arch/riscv/include/asm/syscall_wrapper.h, Linux v6.18.46),
so no narrowing is owed; `do_mprotect_pkey` (mm/mprotect.c, Linux
v6.18.46) applies `untagged_addr` to `start`, the identity while the
process's pointer-masking length is zero, the argument `arm_munmap`'s
docstring (`Checks/Arms/Mm/Mmap.lean`) carries.  `ca_arm` is the term
`Sys/Registry/Mm/Mprotect.lean`'s row builds, which `checked_table_arms`
checks.  The ledger fact this arm owes `checked_table_preserves_vm` is
`check_mprotect_preserves`, below. -/
def arm_mprotect : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 226 (fun i => Sys.Mm.Mprotect.mprotect_spec (in_arg i 0)
    (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => Checks.Sys.Mm.Mprotect.check_mprotect (in_arg i 0) (in_arg i 1)
    (in_arg i 2) eff m
  ca_witness := fun i m => Checks.Sys.Mm.Mprotect.mprotect_witness (in_arg i 0) (in_arg i 1)
    (in_arg i 2) m
  ca_sound_ok := fun i eff m m' evs h => Checks.Sys.Mm.Mprotect.check_mprotect_sound_ok
    (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h => Checks.Sys.Mm.Mprotect.check_mprotect_sound_unmodeled
    (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m i h
  ca_complete_ok := fun i eff m m' evs h => Checks.Sys.Mm.Mprotect.check_mprotect_complete_ok
    (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Mm.Mprotect.check_mprotect_complete_unmodeled (in_arg i 0) (in_arg i 1)
      (in_arg i 2) m i eff h
  ca_receptive := fun i m => Checks.Sys.Mm.Mprotect.mprotect_witness_ok (in_arg i 0)
    (in_arg i 1) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_mprotect (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_mprotect.ca_check i eff m = Checks.Sys.Mm.Mprotect.check_mprotect (in_arg i 0)
      (in_arg i 1) (in_arg i 2) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_mprotect (i : SyscallInput) (m : Model) :
    arm_mprotect.ca_witness i m = Checks.Sys.Mm.Mprotect.mprotect_witness (in_arg i 0)
      (in_arg i 1) (in_arg i 2) m := rfl
@[arm_unfold] theorem sa_spec_arm_mprotect (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    arm_mprotect.ca_arm.sa_spec i m o = Sys.Mm.Mprotect.mprotect_spec (in_arg i 0) (in_arg i 1)
      (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_mprotect : ca_no arm_mprotect = 226 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mprotect

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- Every `CheckOk` the checker returns keeps the ledger well formed.
Rocq: `VmMapsDisjoint.check_mprotect_preserves`, whose proof walks the
checker's branches to the one projection it needs — `vm_maps` is what it
was (`rewrite vmm_mprotect_next; cbn [vm_maps]`) — and `vm_wf` reads
nothing else.  The checker's file states that projection for every
accepting run as `check_mprotect_vm_maps`, so this is one rewrite of it. -/
theorem check_mprotect_preserves (addr len prot : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_mprotect addr len prot eff m = CheckOk m' evs)
    (hwf : vm_wf (m_vmmaps m)) : vm_wf (m_vmmaps m') := by
  unfold vm_wf at hwf ⊢
  rw [check_mprotect_vm_maps addr len prot eff m m' evs h]
  exact hwf

/-- Every `CheckOk` the checker returns leaves the descriptor subsystem as
it was.  Every accepting branch but the exposure hands back the model it
was given; the exposure's `mprotect_model_next` rebuilds the model through
`with_vmmaps`, which carries `m.m_fd` across (`State/Model.lean`), so its
projection is `rfl`.  The branch walk is `check_mprotect_vm_maps`'s, with
`rfl` at each leaf where that proof reads `vm_maps`.  Lean-only: the Rocq tree
registers no `m_fd` invariant, so it has no descriptor frame to twin. -/
theorem check_mprotect_fd_state_frame (addr len prot : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_mprotect addr len prot eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold check_mprotect at h
  generalize bv_unsigned addr + page_round_up_Z (bv_unsigned len) = X at h
  split at h
  · obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  split at h
  · obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  split at h
  · obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  by_cases hg4 : two_pow_64 ≤ X
  · rw [ite_eq_left hg4] at h
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  rw [ite_eq_right hg4] at h
  cases hp : mprotect_modeled_b prot
  · rw [hp] at h
    rw [Bool.not_false, ite_eq_left rfl] at h
    cases h
  · rw [hp] at h
    rw [Bool.not_true, ite_eq_right Bool.false_ne_true] at h
    dsimp only at h
    split at h
    · split at h
      · split at h
        · split at h
          · cases h
            rfl
          · cases h
        · split at h
          · cases h
            rfl
          · cases h
      · cases h
    · split at h
      · split at h
        · split at h
          · cases h
            rfl
          · cases h
        · cases h
      · cases h

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mprotect

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `mprotect` (226): no frame lemma — the exposure moves a range out of
`vm_noaccess`, a field of the ledger — so the preserves lemma directly
(`check_mprotect_preserves`, above). -/
theorem arm_mprotect_preserves_vm : arm_preserves_vm arm_mprotect :=
  fun i eff m m' evs h hwf => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Mm.Mprotect.check_mprotect_preserves _ _ _ eff m m' evs h hwf

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `vm_wf` × `mprotect`: the ledger fact above. -/
theorem vm_wf_arm_mprotect : arm_preserves inv_vm_wf arm_mprotect :=
  Arms.arm_mprotect_preserves_vm

/-- `fd_table_unique` × `mprotect`: a protection change binds and closes
no descriptor (`check_mprotect_fd_state_frame`, above). -/
theorem fd_table_unique_arm_mprotect : arm_preserves inv_fd_table_unique arm_mprotect :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_mprotect (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table
      (Checks.Sys.Mm.Mprotect.check_mprotect_fd_state_frame _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `mprotect`: no pipe is touched. -/
theorem pipes_within_capacity_arm_mprotect :
    arm_preserves inv_pipes_within_capacity arm_mprotect :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_mprotect (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes
      (Checks.Sys.Mm.Mprotect.check_mprotect_fd_state_frame _ _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
