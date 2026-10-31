-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/RiscvAccessReporting.v
import LinuxProcessSemantics.LinuxProcessSem.BvBase
import LinuxProcessSemantics.LinuxProcessSem.MemImageType
import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics

/-! # LinuxProcessSem.Checks.RiscvAccessReporting — exact data-access reports

Instruction access reporting is an observation of the authoritative
interpreter, not a second instruction semantics.  These executable checks
pin the report emitted for each instruction family that can touch data
memory: every integer width, both floating-point widths, LR/SC, and AMOs.
The cross-page checks use deliberately misaligned eight-byte operations;
each report retains the one architectural range rather than rounding or
splitting it.

Rocq proves each case by `vm_compute`; the Lean twin states the same
equations and closes them by `with_unfolding_all rfl`, the Lean
evaluation that reduces the interpreter's definitions to the same
result. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.RiscvAccessReporting

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics

-- The Rocq proofs are `vm_compute`; the Lean twin evaluates the same terms
-- in the kernel, which needs more than the default recursion depth and
-- heartbeats for the segment-byte decoding.
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Nineteen 32-bit instructions, all using x11 as the address register and,
where needed, x12/f12 as the source:

      0x100  lb       x10, 0(x11)       03850500
      0x104  lh       x10, 0(x11)       03950500
      0x108  lw       x10, 0(x11)       03a50500
      0x10c  ld       x10, 0(x11)       03b50500
      0x110  sb       x12, 0(x11)       2380c500
      0x114  sh       x12, 0(x11)       2390c500
      0x118  sw       x12, 0(x11)       23a0c500
      0x11c  sd       x12, 0(x11)       23b0c500
      0x120  flw      f10, 0(x11)       07a50500
      0x124  fld      f10, 0(x11)       07b50500
      0x128  fsw      f12, 0(x11)       27a0c500
      0x12c  fsd      f12, 0(x11)       27b0c500
      0x130  lr.w     x10, (x11)        2fa50510
      0x134  lr.d     x10, (x11)        2fb50510
      0x138  sc.w     x10, x12, (x11)   2fa5c518
      0x13c  sc.d     x10, x12, (x11)   2fb5c518
      0x140  amoadd.w x10, x12, (x11)   2fa5c500
      0x144  amoadd.d x10, x12, (x11)   2fb5c500
      0x148  addi     x0, x0, 0         13000000

(Rocq: `access_code_segment`.) -/
def access_code_segment : Segment :=
  { seg_base := 0x100, seg_size := 76, seg_perms := "r-x",
    seg_bytes :=
      ["038505000395050003a5050003b505002380c5002390c50023a0c50023b0c50007a5050007b5050027a0c50027b0c5002fa505102fb505102fa5c5182fb5c5182fa5c5002fb5c50013000000"] }

/-- (Rocq: `access_segments`.) -/
def access_segments : List Segment := [access_code_segment]

/-- Two writable windows.  The first holds aligned ordinary accesses.  The
second straddles `0x1000`, allowing successful eight-byte operations to
exercise cross-page ranges without changing instruction semantics.
Rocq tests the windows with `Z.leb`/`Z.ltb` on booleans; the Lean twin
uses the decidable `Int` comparisons, which compute the same windows.
(Rocq: `access_data`.) -/
def access_data (a : word) : Option byte :=
  let z := bv_unsigned a
  if (0x200 ≤ z ∧ z < 0x220) ∨ (0xffc ≤ z ∧ z < 0x1004)
  then some (Z_to_bv 8 0x5a) else none

/-- (Rocq: `access_state`.) -/
def access_state (pc : Int) (addr : Int) (resv : Option word) : machine_state :=
  { ms_regs := bvmap_set (Z_to_bv 5 11) (Z_to_bv 64 addr)
                 (bvmap_set (Z_to_bv 5 12) (Z_to_bv 64 0x1122334455667788)
                    bvmap_empty),
    ms_fregs := bvmap_set (Z_to_bv 5 12) (Z_to_bv 64 0x8877665544332211)
                  bvmap_empty,
    ms_pc_val := Z_to_bv 64 pc,
    ms_svc_pending := none,
    ms_resv := resv,
    ms_fcsr := Z_to_bv 32 0,
    ms_mem := access_data,
    ms_rom := fun _ => none }

/-- (Rocq: `reported_ranges`.) -/
def reported_ranges (st : machine_state) : Option (List memory_access) :=
  match step_accesses access_segments st with
  | MachineOk report => some report.accessed_ranges
  | MachineFault => none
  | MachineUnmodeled => none

/-- (Rocq: `access_at`.) -/
def access_at (addr : Int) (bytes : Nat) : List memory_access :=
  [(Z_to_bv 64 addr, bytes)]

/-- (Rocq: `access_pair`.) -/
def access_pair (addr : Int) (bytes : Nat) : List memory_access :=
  List.append (access_at addr bytes) (access_at addr bytes)

/-- (Rocq: `integer_load_reports`.) -/
theorem integer_load_reports :
    reported_ranges (access_state 0x100 0x200 none) = some (access_at 0x200 1) ∧
    reported_ranges (access_state 0x104 0x200 none) = some (access_at 0x200 2) ∧
    reported_ranges (access_state 0x108 0x200 none) = some (access_at 0x200 4) ∧
    reported_ranges (access_state 0x10c 0x200 none) = some (access_at 0x200 8) := by
  with_unfolding_all exact ⟨rfl, rfl, rfl, rfl⟩

/-- (Rocq: `integer_store_reports`.) -/
theorem integer_store_reports :
    reported_ranges (access_state 0x110 0x200 none) = some (access_at 0x200 1) ∧
    reported_ranges (access_state 0x114 0x200 none) = some (access_at 0x200 2) ∧
    reported_ranges (access_state 0x118 0x200 none) = some (access_at 0x200 4) ∧
    reported_ranges (access_state 0x11c 0x200 none) = some (access_at 0x200 8) := by
  with_unfolding_all exact ⟨rfl, rfl, rfl, rfl⟩

/-- (Rocq: `floating_load_reports`.) -/
theorem floating_load_reports :
    reported_ranges (access_state 0x120 0x200 none) = some (access_at 0x200 4) ∧
    reported_ranges (access_state 0x124 0x200 none) = some (access_at 0x200 8) := by
  with_unfolding_all exact ⟨rfl, rfl⟩

/-- (Rocq: `floating_store_reports`.) -/
theorem floating_store_reports :
    reported_ranges (access_state 0x128 0x200 none) = some (access_at 0x200 4) ∧
    reported_ranges (access_state 0x12c 0x200 none) = some (access_at 0x200 8) := by
  with_unfolding_all exact ⟨rfl, rfl⟩

/-- (Rocq: `load_reserved_reports`.) -/
theorem load_reserved_reports :
    reported_ranges (access_state 0x130 0x200 none) = some (access_at 0x200 4) ∧
    reported_ranges (access_state 0x134 0x200 none) = some (access_at 0x200 8) := by
  with_unfolding_all exact ⟨rfl, rfl⟩

/-- (Rocq: `store_conditional_reports`.) -/
theorem store_conditional_reports :
    reported_ranges (access_state 0x138 0x200 (some (Z_to_bv 64 0x200))) =
        some (access_at 0x200 4) ∧
    reported_ranges (access_state 0x13c 0x200 (some (Z_to_bv 64 0x200))) =
        some (access_at 0x200 8) := by
  with_unfolding_all exact ⟨rfl, rfl⟩

/-- (Rocq: `failed_store_conditionals_report_no_access`.) -/
theorem failed_store_conditionals_report_no_access :
    reported_ranges (access_state 0x138 0x200 none) = some [] ∧
    reported_ranges (access_state 0x13c 0x200 none) = some [] := by
  with_unfolding_all exact ⟨rfl, rfl⟩

/-- (Rocq: `atomic_read_modify_write_reports`.) -/
theorem atomic_read_modify_write_reports :
    reported_ranges (access_state 0x140 0x200 none) = some (access_pair 0x200 4) ∧
    reported_ranges (access_state 0x144 0x200 none) = some (access_pair 0x200 8) := by
  with_unfolding_all exact ⟨rfl, rfl⟩

/-- (Rocq: `cross_page_reports`.) -/
theorem cross_page_reports :
    reported_ranges (access_state 0x10c 0xffc none) = some (access_at 0xffc 8) ∧
    reported_ranges (access_state 0x11c 0xffc none) = some (access_at 0xffc 8) := by
  with_unfolding_all exact ⟨rfl, rfl⟩

/-- Instruction fetches are deliberately absent: callers account only for
successful DATA effects, while code remains governed by segment execute
permissions.  (Rocq: `register_only_instruction_reports_no_access`.) -/
theorem register_only_instruction_reports_no_access :
    reported_ranges (access_state 0x148 0x200 none) = some [] := by
  with_unfolding_all rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.RiscvAccessReporting
