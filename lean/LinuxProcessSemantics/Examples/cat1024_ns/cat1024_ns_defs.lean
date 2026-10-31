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
import LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_code
import LinuxProcessSemantics.Examples.cat1024_ns.SourceMemImage
import LinuxProcessSemantics.Examples.cat1024_ns.TargetMemImage

/-! rocq-baseline: 8bef2933e7063c3b77d628343969f2352008c3ca -/

/-! Mirrors `theories/Examples/cat1024_ns/cat1024_ns_defs.v` at the baseline
above; see that Rocq file for the argument. `source_avoids_ro` and
`target_avoids_ro` are not ported: no cat1024_ns file uses them, and the
first needs `range_avoids_ro_above`, which `Common/StepTac.lean` leaves
unported. Rocq `Z` becomes `Int`, and `nat` and `N` become `Nat`. The
closed-equation tactic `bveq` is replaced by conversion and `decide` in the
proofs below.
-/

namespace LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_defs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Examples.cat1024_ns.SourceMemImage
open LinuxProcessSemantics.Examples.cat1024_ns.TargetMemImage
open LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_code

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem source_init_pc_val : SourceMemImage_init_pc = 0x11078 := rfl

theorem target_init_pc_val : TargetMemImage_init_pc = 0x1001190 := rfl

theorem source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true := by
  have hlen : SourceMemImage_seg_bytes_003_chars.length = 8192 := by
    simp only [SourceMemImage_seg_bytes_003_chars, List.length_replicate]
  have hbyte (i : Nat) (hi : i < 4096) :
      (segment_byte_at SourceMemImage_segment_003.seg_bytes i).isSome = true := by
    rw [SourceMemImage_segment_003_byte_ascii]
    simp only [LinuxProcessSemantics.Common.ImageBytes.ascii_segment_byte_at,
      hlen, show 8192 / 2 = (4096 : Nat) from rfl, ite_eq_left hi]
    exact LinuxProcessSemantics.Common.ImageBytes.hex_chars_byte_at_isSome
      _ i SourceMemImage_seg_bytes_003_hex (by omega)
  have window (n : Nat) (a : word) (hlo : 0x13000 ≤ bv_unsigned a)
      (hhi : bv_unsigned a + (n : Int) ≤ 0x14000) :
      wseg_ok source_segs a n = true := by
    induction n generalizing a with
    | zero => rfl
    | succ n ih =>
      have hf : find_segment source_segs (bv_unsigned a) 1 =
          some SourceMemImage_segment_003 := by
        change (if decide (0x10000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x11000)
          then some SourceMemImage_segment_000 else
          if decide (0x11000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x12000)
          then some SourceMemImage_segment_001 else
          if decide (0x12000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x13000)
          then some SourceMemImage_segment_002 else
          if decide (0x13000 ≤ bv_unsigned a) && decide (bv_unsigned a + 1 ≤ 0x14000)
          then some SourceMemImage_segment_003 else none) = _
        simp only [show ¬ bv_unsigned a + 1 ≤ 0x11000 by omega,
          show ¬ bv_unsigned a + 1 ≤ 0x12000 by omega,
          show ¬ bv_unsigned a + 1 ≤ 0x13000 by omega,
          show bv_unsigned a + 1 ≤ 0x14000 by omega,
          hlo, decide_false, decide_true, Bool.and_false, Bool.true_and,
          Bool.false_eq_true, ↓reduceIte]
      have hb := hbyte (bv_unsigned a - 0x13000).toNat (by omega)
      have ha : bv_unsigned (a + 1) = bv_unsigned a + 1 :=
        u_add1 a (by omega)
      have ht := ih (a + 1) (by omega) (by omega)
      simp only [wseg_ok, hf]
      change (true && (match segment_byte_at SourceMemImage_segment_003.seg_bytes
        (bv_unsigned a - 0x13000).toNat with
        | some _ => true | none => false) && wseg_ok source_segs (a + 1) n) = true
      cases he : segment_byte_at SourceMemImage_segment_003.seg_bytes
          (bv_unsigned a - 0x13000).toNat with
      | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hb
      | some b => exact ht
  exact window 4096 0x13000 (by decide) (by decide)

theorem source_store_ok (m : word → Option byte) (a : word) (n : Nat)
    (hlo : 0x13000 ≤ bv_unsigned a) (hhi : bv_unsigned a + (n : Int) ≤ 0x14000) :
    store_ok source_segs m a n = true :=
  store_ok_window source_segs m 0x13000 a 4096 n 0x13000 0x14000
    rfl rfl (by decide) source_data_wseg hlo hhi

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
    have hl : TargetMemImage_seg_bytes_002_chars.length = 8192 := by decide +kernel
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

theorem target_data_wseg : wseg_ok target_segs (0x1002000 : word) 4096 = true :=
  target_wseg_window 4096 0x1002000 (by decide) (by decide)

theorem target_store_ok (m : word → Option byte) (a : word) (n : Nat)
    (hlo : 0x1002000 ≤ bv_unsigned a) (hhi : bv_unsigned a + (n : Int) ≤ 0x1003000) :
    store_ok target_segs m a n = true :=
  store_ok_window target_segs m 0x1002000 a 4096 n 0x1002000 0x1003000
    rfl rfl (by decide) target_data_wseg hlo hhi

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
    have hl : SourceMemImage_seg_bytes_003_chars.length = 8192 := by decide +kernel
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


theorem source_buf_wseg :
    wseg_ok source_segs 0x13008 (word_to_nat (Z_to_bv 64 1024)) = true :=
  source_wseg_window _ _ (by decide) (by decide)

theorem target_buf_wseg :
    wseg_ok target_segs 0x1002208 (word_to_nat (Z_to_bv 64 1024)) = true :=
  target_wseg_window _ _ (by decide) (by decide)

theorem c_ltu_x0 (x : word) : c_ltu x (Z_to_bv 64 0) = false := by
  change decide (x.toNat < 0) = false
  simp only [Nat.not_lt_zero, decide_false]

theorem cat_Hcnt : 0 < bv_unsigned (Z_to_bv 64 1024) ∧
    bv_unsigned (Z_to_bv 64 1024) ≤ rw_bytes_max := by decide

theorem trd_here_rec (segs : List Segment) (LH : machine_state → Prop)
    (regs : bvmap 5 word) (pc : word) (mem rom : word → Option byte) (buf : word)
    (h17 : bv_unsigned (getr regs 17) = 63)
    (h10 : reg_get regs 10 = Z_to_bv 64 0)
    (h11 : reg_get regs 11 = buf) (h12 : reg_get regs 12 = Z_to_bv 64 1024)
    (hw : wseg_ok segs buf (word_to_nat (Z_to_bv 64 1024)) = true)
    (haok : access_okb buf (bv_unsigned (Z_to_bv 64 1024)) = true)
    (hexit : to_exit segs (Z_to_bv 64 0)
      (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom))
    (hbytes : ∀ bs, 1 ≤ (bs.length : Int) → (bs.length : Int) ≤ 1024 →
      to_wr segs LH bs (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
        (write_to_mem mem buf bs) rom)) :
    to_rd segs LH (Z_to_bv 64 1024)
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom } := by
  apply to_rd.trd_here
  refine ⟨buf, getr regs 17, rfl, h17, h10, h11, h12,
    wseg_ok_wdef segs buf (Z_to_bv 64 1024) _ hw, haok, ?_, ?_⟩
  · rw [adv_set]
    exact hexit
  · intro bs hlo hhi
    rw [adv_apply_write]
    exact hbytes bs hlo hhi

theorem twr_here_rec (segs : List Segment) (LH : machine_state → Prop)
    (bs : List byte) (regs : bvmap 5 word) (pc : word) (mem rom : word → Option byte)
    (h17 : bv_unsigned (getr regs 17) = 64)
    (h10 : reg_get regs 10 = Z_to_bv 64 1)
    (hr : ms_read_bytes
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some bs)
    (hnb : 1 ≤ bs.length)
    (hcont : ∀ n, 1 ≤ n → n ≤ bs.length →
      to_wall_tail segs (Z_to_bv 64 1)
        (mkst (regupd regs 10 (len_word (bs.take n))) (v_addi pc 4) mem rom)
        (bs.drop n) (lh_next segs LH)) :
    to_wr segs LH bs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom } := by
  exact to_wr.twr_here _ ⟨hnb,
    twl_write_rec segs (Z_to_bv 64 1) (lh_next segs LH) bs regs pc mem rom
      h17 h10 hr hnb hcont⟩

theorem te_here_rec0 (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (h17 : bv_unsigned (getr regs 17) = 93)
    (h10 : reg_get regs 10 = Z_to_bv 64 0) :
    to_exit segs (Z_to_bv 64 0)
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom } := by
  exact to_exit.te_here _ (getr regs 17) rfl (Or.inl h17) h10

end LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_defs
