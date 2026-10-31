-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/RiscvAtomicAlignment.v
import LinuxProcessSemantics.LinuxProcessSem.BvBase
import LinuxProcessSemantics.LinuxProcessSem.MemImageType
import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics

/-! # LinuxProcessSem.Checks.RiscvAtomicAlignment — misaligned atomics fault

Regression checks for the A-extension alignment gate in `Sem.exec`:
lr/sc/amo at an address that is not naturally aligned to the operand
width (4 for .w, 8 for .d) is `Sem.EFault`, which `interp_eff` turns
into `MachineFault` — the SIGBUS the real process takes.  Plain loads
and stores are deliberately NOT gated (the model permits misaligned
ones, as the emulated hart and Linux on real hardware do), so these
checks pin the split.

Anti-vacuity: every misaligned case below differs from a green aligned
twin ONLY in the low bits of the address register, and the data window
is readable and writable at both addresses — so only the alignment gate
can make the misaligned one fault.

Rocq proves each case by `vm_compute`; the Lean twin states the same
equations and closes them by `with_unfolding_all rfl`, the Lean
evaluation that reduces the interpreter's definitions to the same
result. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.RiscvAtomicAlignment

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics

/-- Six atomics, one per instruction word, all using x11 as the address
and x12 as the source, rd = x10:

      0x100  lr.w     x10, (x11)        2fa50510
      0x104  lr.d     x10, (x11)        2fb50510
      0x108  sc.w     x10, x12, (x11)   2fa5c518
      0x10c  sc.d     x10, x12, (x11)   2fb5c518
      0x110  amoadd.w x10, x12, (x11)   2fa5c500
      0x114  amoadd.d x10, x12, (x11)   2fb5c500

(Rocq: `atomic_code_segment`.) -/
def atomic_code_segment : Segment :=
  { seg_base := 0x100, seg_size := 24, seg_perms := "r-x",
    seg_bytes := ["2fa505102fb505102fa5c5182fb5c5182fa5c5002fb5c500"] }

/-- (Rocq: `atomic_segments`.) -/
def atomic_segments : List Segment := [atomic_code_segment]

/-- A 32-byte writable data window at `0x200`, present in the overlay:
`ov_read_bytes` answers loads from it and `store_ok` accepts stores into
it, so an atomic aimed anywhere inside is otherwise fully executable.
Rocq tests the window with `Z.leb`/`Z.ltb` on booleans; the Lean twin
uses the decidable `Int` comparisons, which compute the same window.
(Rocq: `atomic_data`.) -/
def atomic_data (a : word) : Option byte :=
  if 0x200 ≤ bv_unsigned a ∧ bv_unsigned a < 0x220
  then some (Z_to_bv 8 0x5a) else none

/-- (Rocq: `atomic_state`.) -/
def atomic_state (pc : word) (addr : Int) (resv : Option word)
    : machine_state :=
  { ms_regs := bvmap_set (Z_to_bv 5 11) (Z_to_bv 64 addr)
                 (bvmap_set (Z_to_bv 5 12) (Z_to_bv 64 0x1122334455667788)
                    bvmap_empty),
    ms_fregs := bvmap_empty,
    ms_pc_val := pc,
    ms_svc_pending := none,
    ms_resv := resv, ms_fcsr := Z_to_bv 32 0,
    ms_mem := atomic_data,
    ms_rom := fun _ => none }

/-- (Rocq: `pc_lr_w`.) -/
def pc_lr_w : word := Z_to_bv 64 0x100
/-- (Rocq: `pc_lr_d`.) -/
def pc_lr_d : word := Z_to_bv 64 0x104
/-- (Rocq: `pc_sc_w`.) -/
def pc_sc_w : word := Z_to_bv 64 0x108
/-- (Rocq: `pc_sc_d`.) -/
def pc_sc_d : word := Z_to_bv 64 0x10c
/-- (Rocq: `pc_amo_w`.) -/
def pc_amo_w : word := Z_to_bv 64 0x110
/-- (Rocq: `pc_amo_d`.) -/
def pc_amo_d : word := Z_to_bv 64 0x114

/-- (Rocq: `steps_ok`.) -/
def steps_ok (st : machine_state) : Prop :=
  match step atomic_segments st with | MachineOk _ => True | _ => False

/-! ### lr: the aligned twin retires, every misaligned residue faults. -/

/-- (Rocq: `lr_w_aligned`.) -/
theorem lr_w_aligned : steps_ok (atomic_state pc_lr_w 0x204 none) := by
  with_unfolding_all exact True.intro

/-- (Rocq: `lr_w_mod_2`.) -/
theorem lr_w_mod_2 :
    step atomic_segments (atomic_state pc_lr_w 0x206 none) = MachineFault := by
  with_unfolding_all rfl

/-- (Rocq: `lr_w_mod_1`.) -/
theorem lr_w_mod_1 :
    step atomic_segments (atomic_state pc_lr_w 0x205 none) = MachineFault := by
  with_unfolding_all rfl

/-- (Rocq: `lr_d_aligned`.) -/
theorem lr_d_aligned : steps_ok (atomic_state pc_lr_d 0x200 none) := by
  with_unfolding_all exact True.intro

/-- 4 mod 8: aligned for lr.w (green above), misaligned for lr.d.
(Rocq: `lr_d_mod_4`.) -/
theorem lr_d_mod_4 :
    step atomic_segments (atomic_state pc_lr_d 0x204 none) = MachineFault := by
  with_unfolding_all rfl

/-! ### amo: same split, and the aligned twin's store retires. -/

/-- (Rocq: `amo_w_aligned`.) -/
theorem amo_w_aligned : steps_ok (atomic_state pc_amo_w 0x204 none) := by
  with_unfolding_all exact True.intro

/-- (Rocq: `amo_w_mod_2`.) -/
theorem amo_w_mod_2 :
    step atomic_segments (atomic_state pc_amo_w 0x206 none) = MachineFault := by
  with_unfolding_all rfl

/-- (Rocq: `amo_d_aligned`.) -/
theorem amo_d_aligned : steps_ok (atomic_state pc_amo_d 0x200 none) := by
  with_unfolding_all exact True.intro

/-- (Rocq: `amo_d_mod_4`.) -/
theorem amo_d_mod_4 :
    step atomic_segments (atomic_state pc_amo_d 0x204 none) = MachineFault := by
  with_unfolding_all rfl

/-! ### sc: the alignment check runs BEFORE the reservation check.

A misaligned sc faults even with NO live reservation — without the gate
(or with it placed after the reservation test) this case would retire
cleanly with rd = 1, never touching memory.  With a live matching
reservation the aligned twin stores and retires. -/

/-- (Rocq: `sc_w_aligned_success`.) -/
theorem sc_w_aligned_success : steps_ok (atomic_state pc_sc_w 0x204 (some (Z_to_bv 64 0x204))) := by
  with_unfolding_all exact True.intro

/-- (Rocq: `sc_w_aligned_fail_retires`.) -/
theorem sc_w_aligned_fail_retires : steps_ok (atomic_state pc_sc_w 0x204 none) := by
  with_unfolding_all exact True.intro

/-- (Rocq: `sc_w_mod_2_no_resv`.) -/
theorem sc_w_mod_2_no_resv :
    step atomic_segments (atomic_state pc_sc_w 0x206 none) = MachineFault := by
  with_unfolding_all rfl

/-- (Rocq: `sc_w_mod_2_live_resv`.) -/
theorem sc_w_mod_2_live_resv :
    step atomic_segments
      (atomic_state pc_sc_w 0x206 (some (Z_to_bv 64 0x206))) = MachineFault := by
  with_unfolding_all rfl

/-- (Rocq: `sc_d_aligned_success`.) -/
theorem sc_d_aligned_success : steps_ok (atomic_state pc_sc_d 0x200 (some (Z_to_bv 64 0x200))) := by
  with_unfolding_all exact True.intro

/-- 4 mod 8 with a matching reservation: only the width's own alignment
can be what faults here.  (Rocq: `sc_d_mod_4_live_resv`.) -/
theorem sc_d_mod_4_live_resv :
    step atomic_segments
      (atomic_state pc_sc_d 0x204 (some (Z_to_bv 64 0x204))) = MachineFault := by
  with_unfolding_all rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.RiscvAtomicAlignment
