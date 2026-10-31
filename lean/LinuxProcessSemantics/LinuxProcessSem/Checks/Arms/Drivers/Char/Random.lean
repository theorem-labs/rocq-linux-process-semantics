import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Drivers.Char.Random
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Drivers.Char.Random — getrandom on the checked surface

The registration of `Checks/Sys/Drivers/Char/Random.lean`'s checker in
`checked_table`, in the one file that registration writes.
`tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files
under `Checks/Arms/`, one per checker twin; its docstring is the shape it
reads and what it refuses. The file holds three sections, each in the
namespace the other arm files use for it:

- `Checks.Sys.Table`: the `CheckedArm` (`arm_getrandom`) and its four
  `arm_unfold` lemmas;
- `Checks.VmMapsDisjoint.Arms`: the arm's ledger fact,
  `arm_getrandom_preserves_vm`, which `checked_table_preserves_vm`'s
  alternation names;
- `Checks.Invariants`: one `<invariant>_arm_getrandom` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`, which
  `registry_preserves`'s alternation names, and the descriptor-state frame
  the two `m_fd` entries rest on.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arm is the row of `theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s
`checked_table` for 278, read at that commit, where it is byte-identical
to the day tip's. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### getrandom (278) -/

/-- getrandom (278).  THE THREE REGISTERS ARE READ IN ORDER AND WHOLE:
`a0` is the destination, `a1` the length and `a2` the flag word.
riscv64's `__riscv_sys_getrandom` hands the registers over in order,
`orig_a0`, `a1`, then `a2` (`SC_RISCV_REGS_TO_ARGS`,
arch/riscv/include/asm/syscall_wrapper.h:21-24, Linux v6.18.46), and the
wrapper narrows each to the type
`SYSCALL_DEFINE3(getrandom, char __user *, ubuf, size_t, len, unsigned int, flags)`
declares (drivers/char/random.c:1385, same version) through `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46).  A pointer
and a `size_t` are the register's width on riscv64, so the cast keeps
all of `a0` and `a1`.  `flags` is `unsigned int`, so Linux drops bits
32-63 of `a2` before the mask test at drivers/char/random.c:1390; this
arm hands the checker, the witness and the spec the whole register, as
Rocq's `arm_getrandom` does, and the three compare the whole word with 0
and GRND_NONBLOCK, so a word with a set high half is declined where
Linux reads its low half.  That is a narrowing and fails closed: the
checker's first gate declines such a word whatever the effect
(`check_getrandom_high_half_flags_decline` pins it at bit 32, and
`getrandom_high_half_flags_decline_over_the_real_table` through this
arm), and `getrandom_spec`'s docstring in `Sys/Drivers/Char/Random.lean`
carries the argument.  The registers after `a2` are not read: the syscall
declares three.  `ca_arm` is the term `Sys/Registry/Drivers/Char/Random.lean`'s
row builds, which `checked_table_arms` checks.  The ledger fact this arm
owes `checked_table_preserves_vm` is `check_getrandom_frame`, beside the
checker. -/
def arm_getrandom : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 278
    (fun i => Sys.Drivers.Char.Random.getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m =>
    Checks.Sys.Drivers.Char.Random.check_getrandom i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m =>
    Checks.Sys.Drivers.Char.Random.getrandom_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Drivers.Char.Random.check_getrandom_sound_ok i (in_arg i 0) (in_arg i 1)
      (in_arg i 2) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Drivers.Char.Random.check_getrandom_sound_unmodeled i (in_arg i 0) (in_arg i 1)
      (in_arg i 2) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Drivers.Char.Random.check_getrandom_complete_ok i (in_arg i 0) (in_arg i 1)
      (in_arg i 2) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Drivers.Char.Random.check_getrandom_complete_unmodeled i (in_arg i 0) (in_arg i 1)
      (in_arg i 2) m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Drivers.Char.Random.getrandom_witness_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_getrandom (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_getrandom.ca_check i eff m
      = Checks.Sys.Drivers.Char.Random.check_getrandom i (in_arg i 0) (in_arg i 1) (in_arg i 2)
          eff m := rfl
@[arm_unfold] theorem ca_witness_arm_getrandom (i : SyscallInput) (m : Model) :
    arm_getrandom.ca_witness i m
      = Checks.Sys.Drivers.Char.Random.getrandom_witness (in_arg i 0) (in_arg i 1) (in_arg i 2)
          i m := rfl
@[arm_unfold] theorem sa_spec_arm_getrandom (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_getrandom.ca_arm.sa_spec i m o
      = Sys.Drivers.Char.Random.getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_getrandom : ca_no arm_getrandom = 278 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `getrandom` (278): an answer the checker accepts leaves the ledger as
it was — the delivered bytes are the effect's write, not a field of the
model (`check_getrandom_frame`, stated beside the checker in
`Checks/Sys/Drivers/Char/Random.lean`). -/
theorem arm_getrandom_preserves_vm : arm_preserves_vm arm_getrandom :=
  arm_preserves_of_frame arm_getrandom (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Drivers.Char.Random.check_getrandom_frame i _ _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## The descriptor-state frame

The two registry entries beside `vm_wf` read the `m_fd` subsystem, so one
frame lemma over the whole record answers both.  The tree's rule is that
a checker's frame lemma lives beside the checker, and this one belongs in
`Checks/Sys/Drivers/Char/Random.lean` beside `check_getrandom_frame`; it
is written here because that file is the checker ticket's and this
ticket's brief does not name the checker file among its registration
points, and moving it there changes nothing but its home.  Rocq registers no `m_fd` invariant, which is why
it has no Rocq twin.

The proof is `check_getrandom_frame`'s, gate for gate, with the goal
read one field over: each accepting leaf of the checker hands back the
model it was given — `CheckOk m []` itself, or `check_getrandom_zero`,
whose `check_getrandom_zero_sound` gives `m' = m` — and `rfl` closes
the field. -/

open LinuxProcessSemantics.LinuxProcessSem.BvBase
  LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
  LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
  LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
  LinuxProcessSemantics.LinuxProcessSem.Sys.Drivers.Char.Random
  LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Drivers.Char.Random in
/-- The descriptor subsystem `check_getrandom` hands back is the one it
was handed. -/
theorem check_getrandom_fd_state_frame (i : SyscallInput) (buf cap flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_getrandom i buf cap flags eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold check_getrandom at h
  generalize (!(bv_unsigned flags == 0 || bv_unsigned flags == GRND_NONBLOCK)) = f at h
  cases f with
  | true => simp only [↓reduceIte] at h; cases h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  generalize (!(modeled_rw_count cap)) = n at h
  cases n with
  | true => simp only [↓reduceIte] at h; cases h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  generalize read_bytes_map i.in_wmem buf cap = w at h
  cases w with
  | none => cases h
  | some _ =>
  dsimp only at h
  generalize (!(w_is0 cap)) = c at h
  cases c with
  | true =>
    simp only [↓reduceIte] at h
    by_cases hsm : bv_unsigned cap ≤ getrandom_small_max
    · simp only [hsm, ↓reduceIte] at h
      split at h
      · split at h
        · obtain ⟨rfl, -⟩ := check_result.CheckOk.inj h; rfl
        · cases h
      · cases h
    · simp only [hsm, ↓reduceIte] at h
      split at h
      · split at h
        · obtain ⟨rfl, -⟩ := check_result.CheckOk.inj h; rfl
        · cases h
      · split at h
        · obtain ⟨rfl, -⟩ := check_result.CheckOk.inj h; rfl
        · cases h
      · cases h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize access_okb buf (bv_unsigned cap) = s at h
    cases s with
    | true =>
      simp only [↓reduceIte] at h
      obtain ⟨rfl, -, -⟩ := check_getrandom_zero_sound _ _ _ _ _ h; rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨rfl, -, -⟩ := check_getrandom_zero_sound _ _ _ _ _ h; rfl

/-- `vm_wf` × `getrandom`: the ledger fact above. -/
theorem vm_wf_arm_getrandom : arm_preserves inv_vm_wf arm_getrandom :=
  Arms.arm_getrandom_preserves_vm

/-- `fd_table_unique` × `getrandom`: the syscall touches no descriptor —
`SYSCALL_DEFINE3(getrandom, …)` (drivers/char/random.c:1385-1412, Linux
v6.18.46) tests the flag word, may wait for the pool, imports the
destination and copies bytes into it — and the checker hands back the
model it was given; the frame is above. -/
theorem fd_table_unique_arm_getrandom : arm_preserves inv_fd_table_unique arm_getrandom :=
  arm_preserves_of_view_frame inv_fd_table_unique arm_getrandom (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_table (check_getrandom_fd_state_frame i _ _ _ eff m m' evs h))

/-- `pipes_within_capacity` × `getrandom`: no pipe is touched. -/
theorem pipes_within_capacity_arm_getrandom :
    arm_preserves inv_pipes_within_capacity arm_getrandom :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_getrandom (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact congrArg FdState.fdst_pipes (check_getrandom_fd_state_frame i _ _ _ eff m m' evs h))

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
