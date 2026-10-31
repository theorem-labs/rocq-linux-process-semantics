import LinuxProcessSemantics.Common.NumPrint
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_code

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # modprint-ns: output buffers, arithmetic and image facts

PROOF-SIDE, not trusted spec. Rocq `Z` is `Int`, `N` and `nat` are `Nat`,
`byte` and `word` use `BitVec`, and `Some` is `some`. The positive divisor
7 makes Lean's Euclidean `%` agree with Rocq's floor remainder.
-/

namespace LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_defs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.ImageBytes
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.NumPrint
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Examples.modprint_ns.SourceMemImage
open LinuxProcessSemantics.Examples.modprint_ns.TargetMemImage
open LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_code

set_option maxRecDepth 65536
set_option maxHeartbeats 200000

def nl : byte := Z_to_bv 8 10

def mod_buf (argc : Int) : List byte := udec (argc % 7) ++ [nl]

def mod_bufs (argc : Int) : List (List byte) := [mod_buf argc]

theorem udec_digit (r : Int) (hr : 0 ≤ r ∧ r < 10) :
    udec r = [Z_to_bv 8 (48 + r)] := by
  by_cases hz : r = 0
  · subst r
    rfl
  · exact udec_single r (by omega)

theorem mod_buf_bytes (argc : Int) (_hargc : 0 ≤ argc) :
    mod_buf argc = [Z_to_bv 8 (48 + argc % 7), nl] := by
  rw [mod_buf, udec_digit (argc % 7) (by omega)]
  rfl

theorem mod_rem_range (argc : Int) (_hargc : 0 ≤ argc) :
    0 ≤ argc % 7 ∧ argc % 7 < 7 := by omega

theorem v_addiw_zero_7 : v_addiw (Z_to_bv 64 0) 7 = Z_to_bv 64 7 := by
  decide +kernel

theorem v_remu_7 (n : Int) (hlo : 0 ≤ n) (hhi : n < 2 ^ 64) :
    v_remu (Z_to_bv 64 n) (Z_to_bv 64 7) = Z_to_bv 64 (n % 7) := by
  apply bv_eq_of_unsigned
  rw [v_remu_small _ _ (by decide +kernel)]
  have hn : bv_unsigned (Z_to_bv 64 n) = n := by
    rw [Z_to_bv_unsigned, bv_wrap64_mod]
    exact Int.emod_eq_of_lt hlo hhi
  rw [hn, show bv_unsigned (Z_to_bv 64 7) = 7 from rfl,
    Z_to_bv_unsigned, bv_wrap64_mod]
  exact (Int.emod_eq_of_lt (by omega) (by omega)).symm

theorem v_addiw_digit (r : Int) (hr : 0 ≤ r ∧ r < 7) :
    v_addiw (Z_to_bv 64 r) 48 = Z_to_bv 64 (48 + r) := by
  have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem v_addi_digit (r : Int) (hr : 0 ≤ r ∧ r < 7) :
    v_addi (Z_to_bv 64 r) 48 = Z_to_bv 64 (48 + r) := by
  have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem stored_digit (r : Int) (hr : 0 ≤ r ∧ r < 7) :
    Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (48 + r))) = Z_to_bv 8 (48 + r) := by
  have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

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

theorem source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true := by
  have hchars := SourceMemImage_seg_bytes_003_hex
  have hlen : SourceMemImage_seg_bytes_003_chars.length = 8192 := by
    simp only [SourceMemImage_seg_bytes_003_chars, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
  have window (n : Nat) (a : word) (hlo : 0x13000 ≤ bv_unsigned a)
      (hhi : bv_unsigned a + (n : Int) ≤ 0x14000) :
      wseg_ok source_segs a n = true := by
    induction n generalizing a with
    | zero => rfl
    | succ n ih =>
      have hf : find_segment source_segs (bv_unsigned a) 1 = some SourceMemImage_segment_003 := by
        simp only [source_segs, Source.loaded_segments, SourceMemImage_loaded_segments,
          find_segment, SourceMemImage_segment_000, SourceMemImage_segment_001, SourceMemImage_segment_002, SourceMemImage_segment_003]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        repeat
          first | split | omega | rfl
      have hoff : (bv_unsigned a - 0x13000).toNat < 4096 := by omega
      have hb : (segment_byte_at SourceMemImage_segment_003.seg_bytes
          (bv_unsigned a - 0x13000).toNat).isSome = true := by
        rw [SourceMemImage_segment_003_byte_ascii]
        simp only [ascii_segment_byte_at, hlen]
        rw [ite_eq_left (by omega)]
        exact hex_chars_byte_at_isSome _ _ hchars (by omega)
      have hu : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 a (by omega)
      have ht := ih (a + 1) (by omega) (by omega)
      have hw : seg_writable SourceMemImage_segment_003 = true := by decide +kernel
      rw [wseg_ok]
      simp only [hf, hw, ht, Bool.true_and, Bool.and_true]
      have hb' : (segment_byte_at SourceMemImage_segment_003.seg_bytes
          (bv_unsigned a - (SourceMemImage_segment_003.seg_base : Int)).toNat).isSome = true := hb
      cases he : segment_byte_at SourceMemImage_segment_003.seg_bytes
          (bv_unsigned a - (SourceMemImage_segment_003.seg_base : Int)).toNat with
      | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hb'
      | some b => rfl
  exact window 4096 0x13000 (by decide +kernel) (by decide +kernel)

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

theorem target_data_wseg : wseg_ok target_segs (0x1002000 : word) 4096 = true := by
  have hchars := TargetMemImage_seg_bytes_002_hex
  have hlen : TargetMemImage_seg_bytes_002_chars.length = 8192 := by
    simp only [TargetMemImage_seg_bytes_002_chars, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
  have window (n : Nat) (a : word) (hlo : 0x1002000 ≤ bv_unsigned a)
      (hhi : bv_unsigned a + (n : Int) ≤ 0x1003000) :
      wseg_ok target_segs a n = true := by
    induction n generalizing a with
    | zero => rfl
    | succ n ih =>
      have hf : find_segment target_segs (bv_unsigned a) 1 = some TargetMemImage_segment_002 := by
        simp only [target_segs, Target.loaded_segments, TargetMemImage_loaded_segments,
          find_segment, TargetMemImage_segment_000, TargetMemImage_segment_001, TargetMemImage_segment_002]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        repeat
          first | split | omega | rfl
      have hoff : (bv_unsigned a - 0x1002000).toNat < 4096 := by omega
      have hb : (segment_byte_at TargetMemImage_segment_002.seg_bytes
          (bv_unsigned a - 0x1002000).toNat).isSome = true := by
        rw [TargetMemImage_segment_002_byte_ascii]
        simp only [ascii_segment_byte_at, hlen]
        rw [ite_eq_left (by omega)]
        exact hex_chars_byte_at_isSome _ _ hchars (by omega)
      have hu : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 a (by omega)
      have ht := ih (a + 1) (by omega) (by omega)
      have hw : seg_writable TargetMemImage_segment_002 = true := by decide +kernel
      rw [wseg_ok]
      simp only [hf, hw, ht, Bool.true_and, Bool.and_true]
      have hb' : (segment_byte_at TargetMemImage_segment_002.seg_bytes
          (bv_unsigned a - (TargetMemImage_segment_002.seg_base : Int)).toNat).isSome = true := hb
      cases he : segment_byte_at TargetMemImage_segment_002.seg_bytes
          (bv_unsigned a - (TargetMemImage_segment_002.seg_base : Int)).toNat with
      | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hb'
      | some b => rfl
  exact window 4096 0x1002000 (by decide +kernel) (by decide +kernel)

theorem target_store_ok (m : word → Option byte) (a : word) (n : Nat)
    (hlo : 0x1002000 ≤ bv_unsigned a) (hhi : bv_unsigned a + (n : Int) ≤ 0x1003000) :
    store_ok target_segs m a n = true := by
  exact store_ok_window target_segs m 0x1002000 a 4096 n 0x1002000 0x1003000
    (by decide +kernel) (by decide +kernel) (by decide +kernel) target_data_wseg hlo hhi

-- Keep the image bytes opaque until the generated ASCII-access equality applies.
private theorem rdn_image_cons (segs : List Segment) (seg : Segment) (a : word)
    (n off : Nat) (b : byte) (bs : List byte)
    (hf : find_segment segs (bv_unsigned a) 1 = some seg)
    (hr : seg_readable seg = true)
    (ho : (bv_unsigned a - (seg.seg_base : Int)).toNat = off)
    (hb : segment_read_bytes seg.seg_bytes off 1 = some [b])
    (ht : rdn segs (fun _ => none) (a + 1) n = some bs) :
    rdn segs (fun _ => none) a (n + 1) = some (b :: bs) := by
  rw [rdn]
  simp only [seg_rom, memory_read, Int.natCast_one, hf, hr, ↓reduceIte, ho, hb, ht]

theorem srom_zero4 : rdn source_segs (fun _ => none) 0x13008 4 =
    some [Z_to_bv 8 0, Z_to_bv 8 0, Z_to_bv 8 0, Z_to_bv 8 0] := by
  refine rdn_image_cons source_segs SourceMemImage_segment_003 0x13008 3 8
    (Z_to_bv 8 0) _ rfl (by decide +kernel) (by decide +kernel) ?_ ?_
  · rw [SourceMemImage_segment_003_read_ascii]
    decide +kernel
  refine rdn_image_cons source_segs SourceMemImage_segment_003 0x13009 2 9
    (Z_to_bv 8 0) _ rfl (by decide +kernel) (by decide +kernel) ?_ ?_
  · rw [SourceMemImage_segment_003_read_ascii]
    decide +kernel
  refine rdn_image_cons source_segs SourceMemImage_segment_003 0x1300a 1 10
    (Z_to_bv 8 0) _ rfl (by decide +kernel) (by decide +kernel) ?_ ?_
  · rw [SourceMemImage_segment_003_read_ascii]
    decide +kernel
  refine rdn_image_cons source_segs SourceMemImage_segment_003 0x1300b 0 11
    (Z_to_bv 8 0) _ rfl (by decide +kernel) (by decide +kernel) ?_ ?_
  · rw [SourceMemImage_segment_003_read_ascii]
    decide +kernel
  rfl

theorem srom_nl : rdn source_segs (fun _ => none) 0x13001 1 =
    some [nl] := by
  refine rdn_image_cons source_segs SourceMemImage_segment_003 0x13001 0 1
    (Z_to_bv 8 10) _ rfl (by decide +kernel) (by decide +kernel) ?_ ?_
  · rw [SourceMemImage_segment_003_read_ascii]
    decide +kernel
  rfl

theorem arom_zero4 : rdn target_segs (fun _ => none) 0x10021f0 4 =
    some [Z_to_bv 8 0, Z_to_bv 8 0, Z_to_bv 8 0, Z_to_bv 8 0] := by
  refine rdn_image_cons target_segs TargetMemImage_segment_002 0x10021f0 3 496
    (Z_to_bv 8 0) _ rfl (by decide +kernel) (by decide +kernel) ?_ ?_
  · rw [TargetMemImage_segment_002_read_ascii]
    decide +kernel
  refine rdn_image_cons target_segs TargetMemImage_segment_002 0x10021f1 2 497
    (Z_to_bv 8 0) _ rfl (by decide +kernel) (by decide +kernel) ?_ ?_
  · rw [TargetMemImage_segment_002_read_ascii]
    decide +kernel
  refine rdn_image_cons target_segs TargetMemImage_segment_002 0x10021f2 1 498
    (Z_to_bv 8 0) _ rfl (by decide +kernel) (by decide +kernel) ?_ ?_
  · rw [TargetMemImage_segment_002_read_ascii]
    decide +kernel
  refine rdn_image_cons target_segs TargetMemImage_segment_002 0x10021f3 0 499
    (Z_to_bv 8 0) _ rfl (by decide +kernel) (by decide +kernel) ?_ ?_
  · rw [TargetMemImage_segment_002_read_ascii]
    decide +kernel
  rfl

theorem arom_nl : rdn target_segs (fun _ => none) 0x10021ed 1 =
    some [nl] := by
  refine rdn_image_cons target_segs TargetMemImage_segment_002 0x10021ed 0 493
    (Z_to_bv 8 10) _ rfl (by decide +kernel) (by decide +kernel) ?_ ?_
  · rw [TargetMemImage_segment_002_read_ascii]
    decide +kernel
  rfl

theorem source_init_pc_val : SourceMemImage_init_pc = 0x11044 := by decide +kernel

theorem target_init_pc_val : TargetMemImage_init_pc = 0x1001190 := by decide +kernel

end LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_defs
