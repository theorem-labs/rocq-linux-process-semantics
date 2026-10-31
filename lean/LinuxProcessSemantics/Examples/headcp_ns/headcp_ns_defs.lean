import LinuxProcessSemantics.Common.FileSim.Algebra
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_code
import LinuxProcessSemantics.Examples.headcp_ns.SourceMemImage
import LinuxProcessSemantics.Examples.headcp_ns.TargetMemImage

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # headcp-ns: shared specification and image probes

PROOF-SIDE FILE (not part of the trusted specification).
Mirrors `theories/Examples/headcp_ns/headcp_ns_defs.v`. Rocq `Z` becomes
`Int`, `N` and `nat` become `Nat`, and bytes and words use `BitVec`.
-/

namespace LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_defs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
open LinuxProcessSemantics.Common.ImageBytes
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.FileSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Examples.headcp_ns.SourceMemImage
open LinuxProcessSemantics.Examples.headcp_ns.TargetMemImage
open LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_code

set_option maxRecDepth 65536
set_option maxHeartbeats 200000

theorem source_init_pc_val : SourceMemImage_init_pc = 0x11100 := rfl

theorem target_init_pc_val : TargetMemImage_init_pc = 0x1001190 := rfl

private theorem source_wseg_window (n : Nat) (a : word)
    (hlo : 0x13000 ≤ bv_unsigned a)
    (hhi : bv_unsigned a + (n : Int) ≤ 0x14000) :
    wseg_ok source_segs a n = true := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have hf : find_segment source_segs (bv_unsigned a) 1 = some SourceMemImage_segment_003 := by
      change (if decide (0x10000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x11000)
        then some SourceMemImage_segment_000 else
        if decide (0x11000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x12000)
        then some SourceMemImage_segment_001 else
        if decide (0x12000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x13000)
        then some SourceMemImage_segment_002 else
        if decide (0x13000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x14000)
        then some SourceMemImage_segment_003 else none) = _
      simp only [show ¬ bv_unsigned a + 1 ≤ 0x11000 by omega,
        show ¬ bv_unsigned a + 1 ≤ 0x13000 by omega,
        show ¬ bv_unsigned a + 1 ≤ 0x12000 by omega,
        show bv_unsigned a + 1 ≤ 0x14000 by omega,
        hlo, decide_false, decide_true, Bool.and_false, Bool.true_and, Bool.false_eq_true,
        ↓reduceIte]
    have hl : SourceMemImage_seg_bytes_003_chars.length = 8192 := by
      simp only [SourceMemImage_seg_bytes_003_chars, List.length_replicate]
    have hb : (segment_byte_at SourceMemImage_segment_003.seg_bytes
        (bv_unsigned a - (SourceMemImage_segment_003.seg_base : Int)).toNat).isSome = true := by
      rw [SourceMemImage_segment_003_byte_ascii]
      change (LinuxProcessSemantics.Common.ImageBytes.ascii_segment_byte_at
        [SourceMemImage_seg_bytes_003_chars] (bv_unsigned a - 0x13000).toNat).isSome = true
      rw [LinuxProcessSemantics.Common.ImageBytes.ascii_segment_byte_at,
        ite_eq_left (by rw [hl]; omega)]
      apply LinuxProcessSemantics.Common.ImageBytes.hex_chars_byte_at_isSome
      · exact SourceMemImage_seg_bytes_003_hex
      · rw [hl]; omega
    have hu := u_add1 a (by omega)
    simp only [wseg_ok, hf]
    change (true && (match segment_byte_at SourceMemImage_segment_003.seg_bytes
      (bv_unsigned a - (SourceMemImage_segment_003.seg_base : Int)).toNat with
      | some _ => true | none => false) && wseg_ok source_segs (a + 1) n) = true
    cases he : segment_byte_at SourceMemImage_segment_003.seg_bytes
        (bv_unsigned a - (SourceMemImage_segment_003.seg_base : Int)).toNat with
    | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hb
    | some b =>
      simp only [Bool.true_and]
      exact ih (a + 1) (by omega) (by omega)



private theorem target_wseg_window (n : Nat) (a : word)
    (hlo : 0x1002000 ≤ bv_unsigned a)
    (hhi : bv_unsigned a + (n : Int) ≤ 0x1003000) :
    wseg_ok target_segs a n = true := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have hf : find_segment target_segs (bv_unsigned a) 1 = some TargetMemImage_segment_002 := by
      change (if decide (0x1000000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x1001000)
        then some TargetMemImage_segment_000 else
        if decide (0x1001000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x1002000)
        then some TargetMemImage_segment_001 else
        if decide (0x1002000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x1003000)
        then some TargetMemImage_segment_002 else none) = _
      simp only [show ¬ bv_unsigned a + 1 ≤ 0x1001000 by omega,
        show ¬ bv_unsigned a + 1 ≤ 0x1002000 by omega,
        show bv_unsigned a + 1 ≤ 0x1003000 by omega,
        hlo, decide_false, decide_true, Bool.and_false, Bool.true_and, Bool.false_eq_true,
        ↓reduceIte]
    have hl : TargetMemImage_seg_bytes_002_chars.length = 8192 := by
      simp only [TargetMemImage_seg_bytes_002_chars, List.length_replicate]
    have hb : (segment_byte_at TargetMemImage_segment_002.seg_bytes
        (bv_unsigned a - (TargetMemImage_segment_002.seg_base : Int)).toNat).isSome = true := by
      rw [TargetMemImage_segment_002_byte_ascii]
      change (LinuxProcessSemantics.Common.ImageBytes.ascii_segment_byte_at
        [TargetMemImage_seg_bytes_002_chars] (bv_unsigned a - 0x1002000).toNat).isSome = true
      rw [LinuxProcessSemantics.Common.ImageBytes.ascii_segment_byte_at,
        ite_eq_left (by rw [hl]; omega)]
      apply LinuxProcessSemantics.Common.ImageBytes.hex_chars_byte_at_isSome
      · exact TargetMemImage_seg_bytes_002_hex
      · rw [hl]; omega
    have hu := u_add1 a (by omega)
    simp only [wseg_ok, hf]
    change (true && (match segment_byte_at TargetMemImage_segment_002.seg_bytes
      (bv_unsigned a - (TargetMemImage_segment_002.seg_base : Int)).toNat with
      | some _ => true | none => false) && wseg_ok target_segs (a + 1) n) = true
    cases he : segment_byte_at TargetMemImage_segment_002.seg_bytes
        (bv_unsigned a - (TargetMemImage_segment_002.seg_base : Int)).toNat with
    | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hb
    | some b =>
      simp only [Bool.true_and]
      exact ih (a + 1) (by omega) (by omega)


theorem source_buf_wseg :
    wseg_ok source_segs 0x13008 (word_to_nat (Z_to_bv 64 128)) = true :=
  source_wseg_window 128 0x13008 (by decide +kernel) (by decide +kernel)

theorem target_buf_wseg :
    wseg_ok target_segs 0x1002290 (word_to_nat (Z_to_bv 64 128)) = true :=
  target_wseg_window 128 0x1002290 (by decide +kernel) (by decide +kernel)

/-- Content seen after the destination has been truncated, including when
source and destination are the same path. -/
def hc_data (fs0 : Fs) (src dst : path) : List byte :=
  match fs_lookup (fs_set fs0 dst []) src with
  | some d => d
  | none => []

def hc_final_fs (fs0 : Fs) (src dst : path) : Fs :=
  fs_set fs0 dst (file_read (hc_data fs0 src dst) (Z_to_bv 64 0) (Z_to_bv 64 128))

def hc_outcomes (fs0 : Fs) (src dst : path) : (word × Fs) → Prop :=
  fun o =>
    match fs_lookup fs0 src with
    | none => o = (Z_to_bv 64 3, fs0)
    | some _ =>
        o = (Z_to_bv 64 3, fs0) ∨ o = (Z_to_bv 64 4, fs0) ∨
        (fs_under fs0 dst = false ∧ o = (Z_to_bv 64 0, hc_final_fs fs0 src dst))

theorem path_eqb_false_neq (p q : path) (h : path_eqb p q = false) : p ≠ q := by
  intro heq
  subst q
  rw [path_eqb_refl] at h
  cases h

theorem hc_data_lookup (fs0 : Fs) (src dst : path) (d0 : List byte)
    (h0 : fs_lookup fs0 src = some d0) :
    fs_lookup (fs_set fs0 dst []) src = some (hc_data fs0 src dst) := by
  unfold hc_data
  by_cases heq : src = dst
  · subst dst
    rw [fs_lookup_set_eq]
  · rw [fs_lookup_set_neq fs0 dst [] src heq, h0]

theorem hc_final_collapse (fs0 : Fs) (src dst : path) :
    fs_set (fs_set fs0 dst []) dst
      (file_write [] (Z_to_bv 64 0)
        (file_read (hc_data fs0 src dst) (Z_to_bv 64 0) (Z_to_bv 64 128))) =
      hc_final_fs fs0 src dst := by
  unfold hc_final_fs
  rw [fs_set_set, file_write_append _ _ _ rfl]
  rfl

theorem hc_chunk_le (d : List byte) :
    (file_read d (Z_to_bv 64 0) (Z_to_bv 64 128)).length ≤ 128 := by
  rw [length_file_read]
  exact Nat.min_le_left _ _

theorem source_avoids_ro (a : word) (n : Int) (ha : 0x13000 ≤ bv_unsigned a) :
    range_avoids_ro_segs source_segs (bv_unsigned a) n = true := by
  change ((false || !(decide (0x10000 < bv_unsigned a + n) && decide (bv_unsigned a < 0x11000))) &&
    ((false || !(decide (0x11000 < bv_unsigned a + n) && decide (bv_unsigned a < 0x12000))) &&
    ((false || !(decide (0x12000 < bv_unsigned a + n) && decide (bv_unsigned a < 0x13000))) &&
    ((true || _) && true)))) = true
  have h0 : ¬ bv_unsigned a < 0x11000 := by omega
  have h1 : ¬ bv_unsigned a < 0x12000 := by omega
  have h2 : ¬ bv_unsigned a < 0x13000 := by omega
  simp only [h0, h1, h2, decide_false, Bool.and_false, Bool.not_false,
    Bool.false_or, Bool.true_or, Bool.and_true]

theorem source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true :=
  source_wseg_window 4096 0x13000 (by decide +kernel) (by decide +kernel)

theorem source_store_ok (m : word → Option byte) (a : word) (n : Nat)
    (hlo : 0x13000 ≤ bv_unsigned a) (hhi : bv_unsigned a + (n : Int) ≤ 0x14000) :
    store_ok source_segs m a n = true := by
  exact store_ok_window source_segs m 0x13000 a 4096 n 0x13000 0x14000
    (by decide +kernel) (by decide +kernel) (by decide +kernel) source_data_wseg hlo hhi

theorem target_avoids_ro (a : word) (n : Int) (ha : 0x1002000 ≤ bv_unsigned a) :
    range_avoids_ro_segs target_segs (bv_unsigned a) n = true := by
  change ((false || !(decide (0x1000000 < bv_unsigned a + n) && decide (bv_unsigned a < 0x1001000))) &&
    ((false || !(decide (0x1001000 < bv_unsigned a + n) && decide (bv_unsigned a < 0x1002000))) &&
    ((true || _) && true))) = true
  have h0 : ¬ bv_unsigned a < 0x1001000 := by omega
  have h1 : ¬ bv_unsigned a < 0x1002000 := by omega
  simp only [h0, h1, decide_false, Bool.and_false, Bool.not_false,
    Bool.false_or, Bool.true_or, Bool.and_true]

theorem target_data_wseg : wseg_ok target_segs (0x1002000 : word) 4096 = true :=
  target_wseg_window 4096 0x1002000 (by decide +kernel) (by decide +kernel)

theorem target_store_ok (m : word → Option byte) (a : word) (n : Nat)
    (hlo : 0x1002000 ≤ bv_unsigned a) (hhi : bv_unsigned a + (n : Int) ≤ 0x1003000) :
    store_ok target_segs m a n = true := by
  exact store_ok_window target_segs m 0x1002000 a 4096 n 0x1002000 0x1003000
    (by decide +kernel) (by decide +kernel) (by decide +kernel) target_data_wseg hlo hhi

theorem c_ltu_x0 (x : word) : c_ltu x (Z_to_bv 64 0) = false := by
  change decide (x.toNat < 0) = false
  simp only [Nat.not_lt_zero, decide_false]

theorem u_len_word {A : Type} (l : List A) (hl : (l.length : Int) < 2 ^ 64) :
    bv_unsigned (len_word l) = (l.length : Int) := by
  exact u_Z2bv _ (by omega) hl

end LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_defs
