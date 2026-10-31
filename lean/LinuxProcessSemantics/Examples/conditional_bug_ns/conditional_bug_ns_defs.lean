import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.StreamExec
import LinuxProcessSemantics.Common.WallSim
import LinuxProcessSemantics.Common.StreamSim
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_code
import LinuxProcessSemantics.Examples.conditional_bug_ns.SourceMemImage
import LinuxProcessSemantics.Examples.conditional_bug_ns.TargetMemImage

/-! rocq-baseline: 36031418350290d5d51fae6e71cbf0b73d7cc91e -/

/-! Shared definitions and image facts for conditional-bug-ns.
Proof-side: dispatch on argv[1]'s first byte, with a source fault at address 64.
Bytes are bitvectors; unbounded address bookkeeping uses Int. -/

namespace LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_defs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Examples.conditional_bug_ns.SourceMemImage
open LinuxProcessSemantics.Examples.conditional_bug_ns.TargetMemImage
open LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_code

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def hello : List byte := [Z_to_bv 8 104, Z_to_bv 8 101, Z_to_bv 8 108,
  Z_to_bv 8 108, Z_to_bv 8 111, Z_to_bv 8 10]

theorem hello_modeled : buf_modeled hello := by
  unfold buf_modeled hello rw_bytes_max
  decide +kernel

theorem hello_bufs_modeled : bufs_modeled [hello] :=
  bufs_modeled_single hello hello_modeled

theorem nil_bufs_modeled : bufs_modeled [] := by
  intro b hb
  exact False.elim (List.not_mem_nil hb)

theorem source_avoids_ro (a : word) (n : Int) (ha : 0x13000 ≤ bv_unsigned a) :
    range_avoids_ro_segs source_segs (bv_unsigned a) n = true :=
  range_avoids_ro_above source_segs 0x13000 _ n (by decide +kernel) ha

theorem target_avoids_ro (a : word) (n : Int) (ha : 0x1002000 ≤ bv_unsigned a) :
    range_avoids_ro_segs target_segs (bv_unsigned a) n = true :=
  range_avoids_ro_above target_segs 0x1002000 _ n (by decide +kernel) ha

theorem source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true := by
  apply wseg_ok_backed source_segs SourceMemImage_segment_003 _ _
    [SourceMemImage_seg_bytes_003_chars]
  · rfl
  · decide +kernel
  · exact congrArg (fun x => [x]) SourceMemImage_seg_bytes_003_chars_eq
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    exact SourceMemImage_seg_bytes_003_ascii
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    exact SourceMemImage_seg_bytes_003_hex
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    simp only [SourceMemImage_seg_bytes_003_chars, List.length_replicate]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      SourceMemImage_seg_bytes_003_chars, List.length_replicate]
    decide +kernel
  · decide +kernel

theorem source_store_ok (m : word → Option byte) (a : word) (n : Nat)
    (hlo : 0x13000 ≤ bv_unsigned a) (hhi : bv_unsigned a + (n : Int) ≤ 0x14000) :
    store_ok source_segs m a n = true :=
  store_ok_window source_segs m 0x13000 a 4096 n 0x13000 0x14000
    rfl rfl (by decide +kernel) source_data_wseg hlo hhi

private theorem cbn_memory_read (segs : List Segment) (seg : Segment) (a : word)
    (bs : List byte) (hf : find_segment segs (bv_unsigned a) ((1 : Nat) : Int) = some seg)
    (hr : seg_readable seg = true)
    (hb : segment_read_bytes seg.seg_bytes (bv_unsigned a - seg.seg_base).toNat 1 = some bs) :
    memory_read segs a 1 = some bs := by
  simp only [memory_read, hf, hr, ↓reduceIte]
  exact hb

private theorem cbn_rdn_cons (segs : List Segment) (a : word) (n : Nat) (b : byte)
    (bs : List byte) (hb : memory_read segs a 1 = some [b])
    (ht : rdn segs (fun _ => none) (a + 1) n = some bs) :
    rdn segs (fun _ => none) a (n + 1) = some (b :: bs) := by
  simp only [rdn, seg_rom, hb, ht]

theorem srom_hello : rdn source_segs (fun _ => none) 0x12000 6 = some hello := by
  have h0 : memory_read source_segs (0x12000 : word) 1 = some [Z_to_bv 8 104] :=
    cbn_memory_read source_segs SourceMemImage_segment_002 _ _ rfl (by decide +kernel)
      ((SourceMemImage_segment_002_read_ascii 0 1).trans (by decide +kernel))
  have h1 : memory_read source_segs (0x12001 : word) 1 = some [Z_to_bv 8 101] :=
    cbn_memory_read source_segs SourceMemImage_segment_002 _ _ rfl (by decide +kernel)
      ((SourceMemImage_segment_002_read_ascii 1 1).trans (by decide +kernel))
  have h2 : memory_read source_segs (0x12002 : word) 1 = some [Z_to_bv 8 108] :=
    cbn_memory_read source_segs SourceMemImage_segment_002 _ _ rfl (by decide +kernel)
      ((SourceMemImage_segment_002_read_ascii 2 1).trans (by decide +kernel))
  have h3 : memory_read source_segs (0x12003 : word) 1 = some [Z_to_bv 8 108] :=
    cbn_memory_read source_segs SourceMemImage_segment_002 _ _ rfl (by decide +kernel)
      ((SourceMemImage_segment_002_read_ascii 3 1).trans (by decide +kernel))
  have h4 : memory_read source_segs (0x12004 : word) 1 = some [Z_to_bv 8 111] :=
    cbn_memory_read source_segs SourceMemImage_segment_002 _ _ rfl (by decide +kernel)
      ((SourceMemImage_segment_002_read_ascii 4 1).trans (by decide +kernel))
  have h5 : memory_read source_segs (0x12005 : word) 1 = some [Z_to_bv 8 10] :=
    cbn_memory_read source_segs SourceMemImage_segment_002 _ _ rfl (by decide +kernel)
      ((SourceMemImage_segment_002_read_ascii 5 1).trans (by decide +kernel))
  exact cbn_rdn_cons _ _ _ _ _ h0 (cbn_rdn_cons _ _ _ _ _ h1
    (cbn_rdn_cons _ _ _ _ _ h2 (cbn_rdn_cons _ _ _ _ _ h3
      (cbn_rdn_cons _ _ _ _ _ h4 (cbn_rdn_cons _ _ _ _ _ h5 rfl)))))

theorem arom_hello : rdn target_segs (fun _ => none) 0x1000158 6 = some hello := by
  have h0 : memory_read target_segs (0x1000158 : word) 1 = some [Z_to_bv 8 104] :=
    cbn_memory_read target_segs TargetMemImage_segment_000 _ _ rfl (by decide +kernel)
      ((TargetMemImage_segment_000_read_ascii 344 1).trans (by decide +kernel))
  have h1 : memory_read target_segs (0x1000159 : word) 1 = some [Z_to_bv 8 101] :=
    cbn_memory_read target_segs TargetMemImage_segment_000 _ _ rfl (by decide +kernel)
      ((TargetMemImage_segment_000_read_ascii 345 1).trans (by decide +kernel))
  have h2 : memory_read target_segs (0x100015a : word) 1 = some [Z_to_bv 8 108] :=
    cbn_memory_read target_segs TargetMemImage_segment_000 _ _ rfl (by decide +kernel)
      ((TargetMemImage_segment_000_read_ascii 346 1).trans (by decide +kernel))
  have h3 : memory_read target_segs (0x100015b : word) 1 = some [Z_to_bv 8 108] :=
    cbn_memory_read target_segs TargetMemImage_segment_000 _ _ rfl (by decide +kernel)
      ((TargetMemImage_segment_000_read_ascii 347 1).trans (by decide +kernel))
  have h4 : memory_read target_segs (0x100015c : word) 1 = some [Z_to_bv 8 111] :=
    cbn_memory_read target_segs TargetMemImage_segment_000 _ _ rfl (by decide +kernel)
      ((TargetMemImage_segment_000_read_ascii 348 1).trans (by decide +kernel))
  have h5 : memory_read target_segs (0x100015d : word) 1 = some [Z_to_bv 8 10] :=
    cbn_memory_read target_segs TargetMemImage_segment_000 _ _ rfl (by decide +kernel)
      ((TargetMemImage_segment_000_read_ascii 349 1).trans (by decide +kernel))
  exact cbn_rdn_cons _ _ _ _ _ h0 (cbn_rdn_cons _ _ _ _ _ h1
    (cbn_rdn_cons _ _ _ _ _ h2 (cbn_rdn_cons _ _ _ _ _ h3
      (cbn_rdn_cons _ _ _ _ _ h4 (cbn_rdn_cons _ _ _ _ _ h5 rfl)))))

theorem srom_64_none : rdn source_segs (fun _ => none) (Z_to_bv 64 64) 1 = none := by
  decide +kernel

theorem source_init_pc_val : SourceMemImage_init_pc = 0x110a4 := rfl

theorem target_init_pc_val : TargetMemImage_init_pc = 0x1001160 := rfl

end LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_defs
