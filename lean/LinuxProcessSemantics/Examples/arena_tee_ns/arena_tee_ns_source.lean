import LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_defs
import LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_code
import LinuxProcessSemantics.Common.ArgvEnv
import LinuxProcessSemantics.Common.SymTac
import LinuxProcessSemantics.Common.SymSide
import LinuxProcessSemantics.Common.SymBranch
import LinuxProcessSemantics.Common.WallSim

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b
unported: argcN -- the identical definition is imported from Common.ArgvEnv
unported: u_argcN -- the identical lemma is imported from Common.ArgvEnv
-/

namespace LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_source

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Run.config
open LinuxProcessSemantics.LinuxProcessSem.State.FdEntry
open LinuxProcessSemantics.LinuxProcessSem.State.ProcInput
open LinuxProcessSemantics.Common.ArgvEnv
open LinuxProcessSemantics.Common.ShapeAlg
open LinuxProcessSemantics.Common.DrainAlg
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.Footprint
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.MmapSim
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Examples.arena_tee_ns.SourceMemImage
open LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_code
open LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_defs

set_option maxRecDepth 65536
set_option maxHeartbeats 400000

theorem source_init_pc_val : SourceMemImage_init_pc = 0x110fc := by rfl

theorem source_avoids_data (a n : Int) (ha : 0x13000 ≤ a) :
    range_avoids_ro_segs source_segs a n = true :=
  range_avoids_ro_above source_segs 0x13000 a n (by decide) ha

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

theorem source_store_ok (m : word → Option byte) (a : word) (k : Nat)
    (hlo : 0x13000 ≤ bv_unsigned a) (hhi : bv_unsigned a + (k : Int) ≤ 0x14000) :
    store_ok source_segs m a k = true :=
  store_ok_window source_segs m 0x13000 a 4096 k 0x13000 0x14000
    rfl rfl (by decide) source_data_wseg hlo hhi

theorem source_reserved_val : segments_reserved source_segs =
    [(Z_to_bv 64 0x10000, Z_to_bv 64 0x1000), (Z_to_bv 64 0x11000, Z_to_bv 64 0x1000),
     (Z_to_bv 64 0x12000, Z_to_bv 64 0x1000), (Z_to_bv 64 0x13000, Z_to_bv 64 0x1000)] := by
  decide +kernel

theorem source_grant_witness (inp : ProcInput) (hint brk0 mb sp : word)
    (hsp : sp_window_lo ≤ bv_unsigned sp) :
    grant_ok hint (init_model (segments_reserved source_segs) brk0 mb sp source_alloc_limit inp)
      (Z_to_bv 64 0x2aaaaab000) 4096 = true := by
  rw [source_reserved_val]
  unfold grant_ok
  have he : decide (0x2aaaaab000 + 4096 ≤ bv_unsigned sp - stack_max_size) = true := by
    apply decide_eq_true
    unfold sp_window_lo at hsp
    unfold stack_max_size
    omega
  change ((((true && true) && decide (0x2aaaaab000 + 4096 ≤ bv_unsigned sp - stack_max_size)) && true) && _) = true
  rw [he]
  simp only [Bool.true_and, decide_eq_true_eq]
  change (0 : Int) + 4096 ≤ 0x400000000
  omega

theorem source_grant_unpack (inp : ProcInput) (hint brk0 mb sp aG : word)
    (hg : grant_ok hint (init_model (segments_reserved source_segs) brk0 mb sp source_alloc_limit inp) aG 4096 = true) :
    0 < bv_unsigned aG ∧ bv_unsigned aG % page_size = 0 ∧
    bv_unsigned aG + 4096 ≤ bv_unsigned sp - stack_max_size ∧
    (bv_unsigned aG + 4096 ≤ 0x10000 ∨ 0x11000 ≤ bv_unsigned aG) ∧
    (bv_unsigned aG + 4096 ≤ 0x11000 ∨ 0x12000 ≤ bv_unsigned aG) ∧
    (bv_unsigned aG + 4096 ≤ 0x12000 ∨ 0x13000 ≤ bv_unsigned aG) := by
  obtain ⟨hal, hpos, hceil, hfree, _⟩ := grant_ok_unpack _ _ _ _ hg
  change bv_unsigned aG + 4096 ≤ bv_unsigned sp - stack_max_size at hceil
  change region_free (segments_reserved source_segs ++ []) aG (Z_to_bv 64 4096) = true at hfree
  rw [List.append_nil, source_reserved_val] at hfree
  obtain ⟨ha, hfree⟩ := region_free_cons _ _ _ _ _ hfree
  obtain ⟨hb, hfree⟩ := region_free_cons _ _ _ _ _ hfree
  obtain ⟨hc, _⟩ := region_free_cons _ _ _ _ _ hfree
  exact ⟨hpos, hal, hceil, ha, hb, hc⟩

theorem source_grant_avoids (aGZ x k : Int)
    (hd1 : aGZ + 4096 ≤ 0x10000 ∨ 0x11000 ≤ aGZ)
    (hd2 : aGZ + 4096 ≤ 0x11000 ∨ 0x12000 ≤ aGZ)
    (hd3 : aGZ + 4096 ≤ 0x12000 ∨ 0x13000 ≤ aGZ)
    (hx1 : aGZ ≤ x) (hx2 : x + k ≤ aGZ + 4096) :
    range_avoids_ro_segs source_segs x k = true := by
  have hc : x + k ≤ 0x10000 ∨ 0x13000 ≤ x := by omega
  rcases hc with hb | ha
  · have h0 : decide (0x10000 < x + k) = false := decide_eq_false (by omega)
    have h1 : decide (0x11000 < x + k) = false := decide_eq_false (by omega)
    have h2 : decide (0x12000 < x + k) = false := decide_eq_false (by omega)
    change ((false || !(decide (0x10000 < x + k) && _)) &&
      ((false || !(decide (0x11000 < x + k) && _)) &&
      ((false || !(decide (0x12000 < x + k) && _)) && (true && true)))) = true
    rw [h0, h1, h2]
    rfl
  · exact source_avoids_data x k ha

theorem v_and_15 (x : word) : v_and x (Z_to_bv 64 15) = v_andi x 15 := rfl

def hw4 (n oq : Nat) : Nat → Int
  | 0 => 0
  | k + 1 => hw4 n oq k + digZ n (oq + 3 - k) * Z_pow 2 (8 * (k : Int))

theorem hw4_range (n oq k : Nat) (hk : k ≤ 4) :
    0 ≤ hw4 n oq k ∧ hw4 n oq k < Z_pow 2 (8 * (k : Int)) := by
  have h0 := digZ_range n (oq + 3 - 0)
  have h1 := digZ_range n (oq + 3 - 1)
  have h2 := digZ_range n (oq + 3 - 2)
  have h3 := digZ_range n (oq + 3 - 3)
  match k with
  | 0 | 1 | 2 | 3 | 4 => simp only [hw4,
    show Z_pow 2 (8 * ((0 : Nat) : Int)) = 1 from rfl,
    show Z_pow 2 (8 * ((1 : Nat) : Int)) = 256 from rfl,
    show Z_pow 2 (8 * ((2 : Nat) : Int)) = 65536 from rfl,
    show Z_pow 2 (8 * ((3 : Nat) : Int)) = 16777216 from rfl,
    show Z_pow 2 (8 * ((4 : Nat) : Int)) = 4294967296 from rfl]; constructor <;> omega
  | k + 5 => omega

theorem lor_mul_pow2 (d a k : Int) (hk : 0 ≤ k)
    (ha : 0 ≤ a ∧ a < Z_pow 2 k) (hd : 0 ≤ d) :
    Z_lor (d * Z_pow 2 k) a = d * Z_pow 2 k + a := by
  cases k with
  | negSucc k => omega
  | ofNat k =>
    cases a with
    | negSucc a => omega
    | ofNat a =>
      cases d with
      | negSucc d => omega
      | ofNat d =>
        have ha := ha.2
        change (a : Int) < (2 : Int)^k at ha
        rw [show (2 : Int)^k = ((2^k : Nat) : Int) from (Int.natCast_pow 2 k).symm] at ha
        have hal : a < 2^k := by omega
        change Z_lor ((d : Int) * (2 : Int)^k) (a : Int) = (d : Int) * (2 : Int)^k + (a : Int)
        rw [show (2 : Int)^k = ((2^k : Nat) : Int) from (Int.natCast_pow 2 k).symm, ← Int.natCast_mul, ← Int.natCast_add]
        change ((d * 2^k ||| a : Nat) : Int) = ((d * 2^k + a : Nat) : Int)
        rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hal]

theorem hw4_expand (n oq : Nat) :
    hw4 n oq 4 = digZ n (oq + 3) +
      (digZ n (oq + 2) + (digZ n (oq + 1) + digZ n oq * 256) * 256) * 256 := by
  simp only [hw4,
    show Z_pow 2 (8 * ((0 : Nat) : Int)) = 1 from rfl,
    show Z_pow 2 (8 * ((1 : Nat) : Int)) = 256 from rfl,
    show Z_pow 2 (8 * ((2 : Nat) : Int)) = 65536 from rfl,
    show Z_pow 2 (8 * ((3 : Nat) : Int)) = 16777216 from rfl]
  rw [show oq + 3 - 0 = oq + 3 by omega,
    show oq + 3 - 1 = oq + 2 by omega,
    show oq + 3 - 2 = oq + 1 by omega,
    show oq + 3 - 3 = oq by omega]
  omega

theorem arena_tee_src_swrap32 (z : Int) (hlo : -(2^31) ≤ z) (hhi : z < 2^31) :
    bv_swrap 32 z = z := by
  change (z + 2147483648) % 4294967296 - 2147483648 = z
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem arena_tee_src_addiw (z i : Int) (hz0 : 0 ≤ z) (hz1 : z < 2^64)
    (hs0 : -(2^31) ≤ z + i) (hs1 : z + i < 2^31) :
    v_addiw (Z_to_bv 64 z) i = Z_to_bv 64 (z + i) := by
  unfold v_addiw
  rw [u_Z2bv z hz0 hz1, arena_tee_src_swrap32 _ hs0 hs1]

theorem hw4_bytes (n oq : Nat) :
    word_to_le_bytes 4 (Z_to_bv 64 (hw4 n oq 4)) =
      [hex_digit (nib n (oq + 3)), hex_digit (nib n (oq + 2)),
       hex_digit (nib n (oq + 1)), hex_digit (nib n oq)] := by
  have h0 := digZ_range n (oq + 3)
  have h1 := digZ_range n (oq + 2)
  have h2 := digZ_range n (oq + 1)
  have h3 := digZ_range n oq
  have hr := hw4_range n oq 4 (by omega)
  have he := hw4_expand n oq
  unfold word_to_le_bytes
  rw [u_Z2bv _ hr.1 (by have h := hr.2; change _ < 4294967296 at h; omega)]
  rw [he]
  simp only [Z_to_le_bytes, Int.shiftRight_eq_div_pow, hex_digit_digZ]
  have d1 : (digZ n (oq + 3) + (digZ n (oq + 2) + (digZ n (oq + 1) + digZ n oq * 256) * 256) * 256) / 256 =
      digZ n (oq + 2) + (digZ n (oq + 1) + digZ n oq * 256) * 256 := by omega
  have d2 : (digZ n (oq + 2) + (digZ n (oq + 1) + digZ n oq * 256) * 256) / 256 =
      digZ n (oq + 1) + digZ n oq * 256 := by omega
  have d3 : (digZ n (oq + 1) + digZ n oq * 256) / 256 = digZ n oq := by omega
  simp only [show ((2^8 : Nat) : Int) = 256 from rfl]
  rw [d1, d2, d3]
  simp only [List.cons.injEq]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | rfl
    | (apply bv_eq_of_unsigned
       simp only [Z_to_bv_unsigned, bv_wrap]
       change _ % 256 = _ % 256
       omega)

theorem arena_tee_src_pow8 (k : Nat) (hk : k < 4) :
    0 ≤ Z_pow 2 (8 * (k : Int)) ∧ Z_pow 2 (8 * (k : Int)) ≤ 16777216 := by
  match k with
  | 0 => change 0 ≤ (1 : Int) ∧ 1 ≤ 16777216; omega
  | 1 => change 0 ≤ (256 : Int) ∧ 256 ≤ 16777216; omega
  | 2 => change 0 ≤ (65536 : Int) ∧ 65536 ≤ 16777216; omega
  | 3 => change 0 ≤ (16777216 : Int) ∧ 16777216 ≤ 16777216; omega
  | k + 4 => omega

theorem arena_tee_src_pack (n oq k : Nat) (hk : k < 4) :
    v_or (v_sllw (Z_to_bv 64 (digZ n (oq + 3 - k))) (Z_to_bv 64 (8 * (k : Int))))
      (Z_to_bv 64 (hw4 n oq k)) = Z_to_bv 64 (hw4 n oq (k + 1)) := by
  have hd := digZ_range n (oq + 3 - k)
  have ha := hw4_range n oq k (by omega)
  have hp8 := arena_tee_src_pow8 k hk
  have hp0 := Int.mul_nonneg (show 0 ≤ digZ n (oq + 3 - k) by omega) hp8.1
  have hp1 := Int.mul_le_mul_of_nonneg_left hp8.2 (show 0 ≤ digZ n (oq + 3 - k) by omega)
  have hp : 0 ≤ digZ n (oq + 3 - k) * Z_pow 2 (8 * (k : Int)) ∧
      digZ n (oq + 3 - k) * Z_pow 2 (8 * (k : Int)) < 2^31 := ⟨hp0, by omega⟩
  have hau : hw4 n oq k < 2^64 := by omega
  have hs : Z_shiftl (digZ n (oq + 3 - k)) (8 * (k : Int)) =
      digZ n (oq + 3 - k) * Z_pow 2 (8 * (k : Int)) := by
    rw [show 8 * (k : Int) = ((8 * k : Nat) : Int) by omega]
    change (digZ n (oq + 3 - k)) <<< (8 * k) = (digZ n (oq + 3 - k)) * (2 : Int)^(8 * k)
    rw [Int.shiftLeft_eq]
  unfold v_sllw
  rw [u_Z2bv _ (by omega) (by omega), u_Z2bv _ (by omega) (by omega),
    Int.emod_eq_of_lt (show 0 ≤ 8 * (k : Int) by omega) (show 8 * (k : Int) < 32 by omega),
    hs, arena_tee_src_swrap32 _ (by omega) hp.2]
  unfold v_or
  rw [u_Z2bv _ hp.1 (by omega), u_Z2bv _ ha.1 hau, lor_mul_pow2 _ _ _ (by omega) ha (by omega)]
  change Z_to_bv 64 (digZ n (oq + 3 - k) * Z_pow 2 (8 * (k : Int)) + hw4 n oq k) =
    Z_to_bv 64 (hw4 n oq k + digZ n (oq + 3 - k) * Z_pow 2 (8 * (k : Int)))
  exact congrArg (Z_to_bv 64) (Int.add_comm _ _)

theorem hex_step_lo (n oq k : Nat) (hn : n ≤ cap) (hoq : oq ≤ 4) (hk : k < 4)
    (hd : nib n (oq + 3 - k) < 10) :
    v_or (v_sllw (v_addiw (v_and (v_srl (nat_to_word n)
      (Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)))) (Z_to_bv 64 15)) 48)
      (Z_to_bv 64 (8 * (k : Int)))) (Z_to_bv 64 (hw4 n oq k)) =
      Z_to_bv 64 (hw4 n oq (k + 1)) := by
  rw [v_and_15, dig_val n (oq + 3 - k) _ hn (by omega) rfl,
    arena_tee_src_addiw _ 48 (by omega) (by omega) (by omega) (by omega)]
  have he : (nib n (oq + 3 - k) : Int) + 48 = digZ n (oq + 3 - k) := by
    unfold digZ
    rw [ite_eq_left hd]
    omega
  rw [he]
  exact arena_tee_src_pack n oq k hk

theorem hex_step_hi (n oq k : Nat) (hn : n ≤ cap) (hoq : oq ≤ 4) (hk : k < 4)
    (hd : 10 ≤ nib n (oq + 3 - k)) :
    v_or (v_sllw (v_addiw (v_and (v_srl (nat_to_word n)
      (Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)))) (Z_to_bv 64 15)) 87)
      (Z_to_bv 64 (8 * (k : Int)))) (Z_to_bv 64 (hw4 n oq k)) =
      Z_to_bv 64 (hw4 n oq (k + 1)) := by
  have h16 := nib_lt16 n (oq + 3 - k)
  rw [v_and_15, dig_val n (oq + 3 - k) _ hn (by omega) rfl,
    arena_tee_src_addiw _ 87 (by omega) (by omega) (by omega) (by omega)]
  have he : (nib n (oq + 3 - k) : Int) + 87 = digZ n (oq + 3 - k) := by
    unfold digZ
    rw [ite_eq_right (by omega)]
    omega
  rw [he]
  exact arena_tee_src_pack n oq k hk

theorem word_to_nat_ntw (n : Nat) (hn : (n : Int) < 2^64) :
    word_to_nat (nat_to_word n) = n := by
  have hu := u_ntw n hn
  change ((nat_to_word n).toNat : Int) = (n : Int) at hu
  change (nat_to_word n).toNat = n
  omega

theorem c_eq_sub_self (x : word) : bv_eqb (v_sub x x) (Z_to_bv 64 0) = true := by
  unfold v_sub
  rw [Int.sub_self]
  rfl

section SourceProof
variable (inp : ProcInput)
variable (Hva : valid_argv (in_argv inp)) (Hve : valid_envp (in_envp inp))
variable (rsp : word) (rrnd : EntryDraw)
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)

local notation "av" => in_argv inp
local notation "ev" => in_envp inp

include Hsp_lo in
theorem rsp_lo_num : 0x7fff80000000 ≤ bv_unsigned rsp := Hsp_lo

include Hsp_hi in
theorem rsp_hi_num : bv_unsigned rsp ≤ 0x800000000000 := Hsp_hi

def rwmem : word → Option byte := wrap_mem source_phdrs rsp av ev (in_uid inp) (in_hwcap inp) rrnd

def rrom : word → Option byte := seg_rom source_segs

include Hva Hve Hsp_hi in
theorem source_bsb_nw :
    bv_unsigned rsp + ((build_stack_bytes source_phdrs rsp av ev (in_uid inp) (in_hwcap inp) rrnd).length : Int) < 2 ^ 64 := by
  have hb := bsb_bound source_phdrs rsp av ev (in_uid inp) (in_hwcap inp) rrnd Hva Hve
  have hh := rsp_hi_num rsp Hsp_hi
  omega

theorem v_sll_3 (x : word) : v_sll x (Z_to_bv 64 3) = v_slli x 3 := by rfl

def envval : word := Z_to_bv 64 (bv_unsigned rsp + 16 + 8 * ((av).length : Int))

include Hva Hsp_lo Hsp_hi in
theorem envval_eq : v_addi (v_add (v_addi rsp 8) (v_slli (argcN av) 3)) 8 = envval inp rsp := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hl := valid_argv_len av Hva
  have hu := u_argcN av Hva
  have hs := v_slli_3 (argcN av) (by omega)
  have hp := u_Z2bv (bv_unsigned rsp + 8) (by omega) (by omega)
  have ha := v_add_small (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN av) 3)
    (by rw [hp, hs, hu]; omega)
  unfold v_addi envval
  rw [ha, hp, hs, hu]
  congr 1
  omega

include Hva Hsp_lo Hsp_hi in
theorem envval_sym :
    Z_to_bv 64 (bv_unsigned (alu64 .ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
      (v_sll (argcN av) (Z_to_bv 64 3))) + 8) = envval inp rsp := by
  rw [alu_add, v_sll_3]
  exact envval_eq inp Hva rsp Hsp_lo Hsp_hi

def emem : word → Option byte := wbytes (rwmem inp rsp rrnd) 0x13000 (word_to_le_bytes 8 (envval inp rsp))

def fmem : word → Option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (emem inp rsp rrnd)
    (Z_to_bv 64 (bv_unsigned rsp - 0x18)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x8)) (word_to_le_bytes 8 (0x11128 : word)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x10)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x20)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x28)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x30)) (word_to_le_bytes 8 (Z_to_bv 64 0))

include Hsp_lo Hsp_hi in
theorem fread_slot_ra :
    rdn source_segs (fmem inp rsp rrnd) (Z_to_bv 64 (bv_unsigned rsp - 0x8)) 8 =
    some (word_to_le_bytes 8 (0x11128 : word)) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  unfold fmem
  repeat first
    | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
    | rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
    | rw [rdn_wbytes_below _ _ _ _ _ _ (by u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]

include Hsp_lo Hsp_hi in
theorem fread_slot_0 (a : word)
    (ha : a ∈ [Z_to_bv 64 (bv_unsigned rsp - 0x30), Z_to_bv 64 (bv_unsigned rsp - 0x28),
      Z_to_bv 64 (bv_unsigned rsp - 0x20), Z_to_bv 64 (bv_unsigned rsp - 0x18),
      Z_to_bv 64 (bv_unsigned rsp - 0x10)]) :
    rdn source_segs (fmem inp rsp rrnd) a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> unfold fmem
  all_goals repeat first
    | rw [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
    | rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
    | rw [rdn_wbytes_below _ _ _ _ _ _ (by u_norm; omega) (by rw [length_N_to_le_bytes]; u_norm; omega)]

def src_mmap_ms (regs : bvmap 5 word) : machine_state :=
  { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := 0x1114c,
    ms_svc_pending := some (getr regs 17), ms_resv := none,
    ms_fcsr := Z_to_bv 32 0, ms_mem := fmem inp rsp rrnd, ms_rom := rrom }

include Hva Hve Hsp_lo Hsp_hi in
theorem src_to_mmap :
    ∃ regs, getr regs 1 = (0x1103c : word) ∧
      getr regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ∧
      getr regs 11 = Z_to_bv 64 4096 ∧ getr regs 12 = Z_to_bv 64 3 ∧
      getr regs 13 = Z_to_bv 64 34 ∧ getr regs 14 = Z_to_bv 64 (2^64 - 1) ∧
      getr regs 15 = Z_to_bv 64 0 ∧ bv_unsigned (getr regs 17) = 222 ∧
      msteps source_segs
        (init_machine_state source_segs SourceMemImage_init_pc source_phdrs
          rsp rrnd av ev (in_uid inp) (in_hwcap inp)) (src_mmap_ms inp rsp rrnd regs) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hsms := stack_max_size_val
  have arena_tee_neg4096 : bv_unsigned (Z_to_bv 64 (-4096)) = 18446744073709547520 := rfl
  have hlen := valid_argv_len av Hva
  have hu := u_argcN av Hva
  rw [source_init_pc_val, init_mkst]
  sym_block_ex source_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
      (Z_to_bv 64 0x110fc)
      (wrap_mem source_phdrs rsp av ev (in_uid inp) (in_hwcap inp) rrnd) (seg_rom source_segs))
    40 [] [] [(2, EVar 32), (8, ELit 0), (9, ELit 0),
      (18, ELit 0), (19, ELit 0), (20, ELit 0)] [rsp] [argcN av] RA HRA Hms
  · repeat' apply And.intro
    all_goals first
      | rfl
      | omega
      | solve_store_ok
      | (apply source_store_ok <;> (u_norm; omega))
      | (have he : Z_to_bv 64 (bv_unsigned rsp + 0) = rsp := by
           apply bv_eq_of_unsigned; u_norm; omega
         rw [he]
         refine ⟨word_le8 (argcN av), ?_, bytes_le_n_to_le_8 _⟩
         rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
         exact read_argc _ _ _ _ _ _ _ _ (source_bsb_nw inp Hva Hve rsp rrnd Hsp_hi))
  all_goals first | (getr_resolve; rfl) | skip
  refine ⟨RA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | (sym_regs HRA <;> first | rfl | assumption | (congr 1 <;> omega) | bveq) | skip
  unfold src_mmap_ms
  apply msteps_trans (ms' := mkst RA (Z_to_bv 64 0x1114c) (fmem inp rsp rrnd) rrom)
  · unfold fmem emem rwmem rrom
    revert Hms
    sym_mem_norm
    have henv := envval_eq inp Hva rsp Hsp_lo Hsp_hi
    unfold v_addi at henv
    rw [v_sll_3, henv]
    exact fun x => x
  · norm_pc; sym_pc_lit
    exact msteps.mst_step _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1114c rfl) (msteps.mst_refl _)

include Hsp_lo Hsp_hi in
theorem src_fail_wexit (regs : bvmap 5 word) (e : Int) (he1 : 1 ≤ e) (he2 : e ≤ 4095)
    (hr1 : getr regs 1 = (0x1103c : word))
    (hr2 : getr regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30)) :
    to_wexit source_segs
      (advance_past_svc (set_gpr0 (src_mmap_ms inp rsp rrnd regs) (errno_ret e)))
      [] (Z_to_bv 64 1) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hsms := stack_max_size_val
  have arena_tee_neg4096 : bv_unsigned (Z_to_bv 64 (-4096)) = 18446744073709547520 := rfl
  obtain ⟨her1, her2⟩ := errno_ret_range e he1 he2
  unfold src_mmap_ms
  rw [adv_set]
  norm_pc
  sym_block source_segs 13 [true]
    [ELit 0x11128, ELit 0, ELit 0, ELit 0, ELit 0, ELit 0]
    [(1, ELit 0x1103c), (2, EVar 32), (10, EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x30), errno_ret e] [] RA HRA
  · repeat' apply And.intro
    all_goals first
      | rfl
      | omega
      | exact c_lts_neg_0 (errno_ret e) (by omega)
      | (refine ⟨word_to_le_bytes 8 (Z_to_bv 64 0), ?_, bytes_le_to_Z_8 _⟩
         apply fread_slot_0 inp rsp rrnd Hsp_lo Hsp_hi
         simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true])
      | exact ⟨word_to_le_bytes 8 (0x11128 : word), fread_slot_ra inp rsp rrnd Hsp_lo Hsp_hi, bytes_le_to_Z_8 _⟩
  · getr_resolve; regupd_resolve; exact hr1
  · getr_resolve; regupd_resolve; exact hr2
  · getr_resolve; regupd_resolve; rfl
  · refine to_wexit.tw_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1112c rfl) ?_
    apply tw_exit_coden
    · sym_regs HRA <;> rfl
    · sym_regs HRA <;> rfl
    · decide

def gbounds (aG : word) : Prop :=
  0 < bv_unsigned aG ∧ bv_unsigned aG % page_size = 0 ∧
  bv_unsigned aG + 4096 ≤ bv_unsigned rsp - stack_max_size ∧
  (bv_unsigned aG + 4096 ≤ 0x10000 ∨ 0x11000 ≤ bv_unsigned aG) ∧
  (bv_unsigned aG + 4096 ≤ 0x11000 ∨ 0x12000 ≤ bv_unsigned aG) ∧
  (bv_unsigned aG + 4096 ≤ 0x12000 ∨ 0x13000 ≤ bv_unsigned aG)

def gmem (aG : word) : word → Option byte := zfill aG (Z_to_bv 64 4096) (fmem inp rsp rrnd)

def mem_ok (aG : word) (mem : word → Option byte) : Prop :=
  mem_grows (gmem inp rsp rrnd aG) mem ∧
  (∀ (a : word) (n : Nat), bv_unsigned a + (n : Int) ≤ 2^64 →
    (bv_unsigned rsp - 0x30 ≤ bv_unsigned a ∨ bv_unsigned a + (n : Int) ≤ bv_unsigned rsp - 0x38) →
    (bv_unsigned aG + 4096 ≤ bv_unsigned a ∨ bv_unsigned a + (n : Int) ≤ bv_unsigned aG) →
    rdn source_segs mem a n = rdn source_segs (fmem inp rsp rrnd) a n)

theorem mem_ok_grows_w (aG : word) (mem : word → Option byte)
    (hm : mem_ok inp rsp rrnd aG mem) : mem_grows (rwmem inp rsp rrnd) mem := by
  apply mem_grows_trans _ _ _ ?_ hm.1
  unfold gmem zfill fmem emem
  solve_mem_grows

theorem gmem_ok (aG : word) (_hb : gbounds rsp aG) :
    mem_ok inp rsp rrnd aG (gmem inp rsp rrnd aG) := by
  refine ⟨mem_grows_refl _, ?_⟩
  intro a n hnw _ hd
  apply rdn_zfill_out _ _ _ _ _ _ hnw
  rcases hd with h | h
  · right; exact h
  · left; exact h

theorem grant_below_stack (aG : word) (hb : gbounds rsp aG) :
    bv_unsigned aG + 4096 ≤ bv_unsigned rsp - 0x800000 := hb.2.2.1

include Hsp_hi in
theorem grant_store_ok (aG : word) (mem : word → Option byte) (a : word) (k : Nat)
    (hm : mem_ok inp rsp rrnd aG mem) (hb : gbounds rsp aG)
    (hlo : bv_unsigned aG ≤ bv_unsigned a)
    (hhi : bv_unsigned a + (k : Int) ≤ bv_unsigned aG + 4096) :
    store_ok source_segs mem a k = true := by
  have hc := grant_below_stack rsp aG hb
  have hh := rsp_hi_num rsp Hsp_hi
  apply store_ok_mono _ _ _ _ _ hm.1
  apply store_ok_zmem
  · omega
  · exact hlo
  · exact hhi

include Hsp_hi in
theorem mem_ok_scratch8 (aG : word) (mem : word → Option byte) (a v : word)
    (hm : mem_ok inp rsp rrnd aG mem) (_hb : gbounds rsp aG)
    (hlo : bv_unsigned rsp - 0x38 ≤ bv_unsigned a)
    (hhi : bv_unsigned a + 8 ≤ bv_unsigned rsp - 0x30) :
    mem_ok inp rsp rrnd aG (wbytes mem a (word_to_le_bytes 8 v)) := by
  have hh := rsp_hi_num rsp Hsp_hi
  refine ⟨mem_grows_trans _ _ _ hm.1 (wbytes_grows _ _ _), ?_⟩
  intro a' n hnw hd hdg
  rw [rdn_wbytes_out _ _ _ _ _ _
    (by rw [length_N_to_le_bytes]; omega) hnw
    (by rw [length_N_to_le_bytes]; omega)]
  exact hm.2 a' n hnw hd hdg

include Hsp_hi in
theorem mem_ok_grant (aG : word) (mem : word → Option byte) (a : word) (bs : List byte)
    (hm : mem_ok inp rsp rrnd aG mem) (hb : gbounds rsp aG)
    (hlo : bv_unsigned aG ≤ bv_unsigned a)
    (hhi : bv_unsigned a + (bs.length : Int) ≤ bv_unsigned aG + 4096) :
    mem_ok inp rsp rrnd aG (wbytes mem a bs) := by
  have hh := rsp_hi_num rsp Hsp_hi
  have hc := grant_below_stack rsp aG hb
  refine ⟨mem_grows_trans _ _ _ hm.1 (wbytes_grows _ _ _), ?_⟩
  intro a' n hnw hd hdg
  rw [rdn_wbytes_out _ _ _ _ _ _ (by omega) hnw (by omega)]
  exact hm.2 a' n hnw hd hdg

include Hsp_hi in
theorem mem_ok_buf (aG : word) (mem : word → Option byte) (buf : word) (bs : List byte)
    (hm : mem_ok inp rsp rrnd aG mem) (hb : gbounds rsp aG)
    (hlo : bv_unsigned aG ≤ bv_unsigned buf)
    (hhi : bv_unsigned buf + (bs.length : Int) ≤ bv_unsigned aG + 4096) :
    mem_ok inp rsp rrnd aG (write_to_mem mem buf bs) := by
  rw [write_to_mem_wbytes]
  exact mem_ok_grant inp rsp rrnd Hsp_hi aG mem buf bs hm hb hlo hhi

def src_inv (fs0 : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (acc : List byte)
    (pc : word) (c : config) : Prop :=
  ∃ (aG : word) (regs : bvmap 5 word) (mem : word → Option byte),
    gbounds rsp aG ∧ m_halted (cfg_model c) = none ∧ m_vm_lazy (cfg_model c) = [] ∧
    m_fs (cfg_model c) = fs0 ∧
    fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0) = some (FdChannel (Z_to_bv 64 0)) ∧
    fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) (cfg_model c) ∧
    msteps source_segs (cfg_ms c) (mkst regs pc mem rrom) ∧
    getr regs 9 = aG ∧ getr regs 18 = aG ∧ getr regs 20 = Z_to_bv 64 4088 ∧
    getr regs 19 = Z_to_bv 64 4087 ∧ getr regs 8 = nat_to_word acc.length ∧
    getr regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ∧ acc.length ≤ cap ∧
    mem_ok inp rsp rrnd aG mem ∧
    rdn source_segs mem (Z_to_bv 64 (bv_unsigned aG + 8)) acc.length = some acc

def src_LH (fs0 : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (acc : List byte) (c : config) : Prop :=
  src_inv inp rsp rrnd fs0 acc (if cap ≤ acc.length then 0x11084 else 0x11060) c

def bufA (aG : word) (k : Nat) : word := Z_to_bv 64 (bv_unsigned aG + 8 + (k : Int))

def scr : word := Z_to_bv 64 (bv_unsigned rsp - 0x38)

include Hsp_hi in
theorem bufA_split (aG : word) (k : Nat) (hb : gbounds rsp aG) (_hk : k ≤ cap) :
    Z_to_bv 64 (bv_unsigned aG + 8) + nat_to_word k = bufA aG k := by
  have hc := grant_below_stack rsp aG hb
  have hh := rsp_hi_num rsp Hsp_hi
  have hr := u64_range aG
  unfold bufA
  rw [word_add_nat, u_Z2bv _ (by omega) (by omega)]

theorem bufA_calc (aG : word) (k : Nat) (_hb : gbounds rsp aG) (hk : k ≤ cap) :
    Z_to_bv 64 (bv_unsigned aG + (bv_unsigned (nat_to_word k) + 8)) = bufA aG k := by
  unfold bufA
  rw [u_ntw k (by unfold cap at hk; omega)]
  congr 1
  omega

theorem dcnt_src (_aG : word) (k : Nat) (hk : k ≤ cap) :
    v_sub (Z_to_bv 64 4088) (nat_to_word k) = Z_to_bv 64 ((cap - k : Nat) : Int) := by
  unfold v_sub
  rw [u_ntw k (by unfold cap at hk; omega)]
  congr 1
  change (4088 : Int) - (k : Int) = _
  unfold cap at *
  omega

theorem ntw_add_len (k : Nat) (bs : List byte) (h : k + bs.length ≤ cap) :
    v_add (nat_to_word k) (len_word bs) = nat_to_word (k + bs.length) := by
  unfold v_add
  rw [u_ntw k (by unfold cap at h; omega), u_len_word bs (by unfold cap at h; omega)]
  unfold nat_to_word
  congr 1

include Hsp_lo Hsp_hi in
theorem src_grant_LH (rbrk rmb : word) (regs : bvmap 5 word) (hint a : word)
    (hr1 : getr regs 1 = (0x1103c : word))
    (hr2 : getr regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30))
    (h11 : getr regs 11 = Z_to_bv 64 4096)
    (hg : grant_ok hint (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) a
      (page_round_up_Z (bv_unsigned (ms_gpr (src_mmap_ms inp rsp rrnd regs) 1))) = true) :
    src_LH inp rsp rrnd (in_fs inp) []
      (mkCfg (advance_past_svc (apply_effect (src_mmap_ms inp rsp rrnd regs)
        (mkEffect a [] [(a, page_round_up (ms_gpr (src_mmap_ms inp rsp rrnd regs) 1))])))
        (mmap_model a (page_round_up (ms_gpr (src_mmap_ms inp rsp rrnd regs) 1))
          (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hsms := stack_max_size_val
  have arena_tee_neg4096 : bv_unsigned (Z_to_bv 64 (-4096)) = 18446744073709547520 := rfl
  have hga : ms_gpr (src_mmap_ms inp rsp rrnd regs) 1 = Z_to_bv 64 4096 := by
    unfold ms_gpr src_mmap_ms
    rw [arg_reg_1, ← getr_nz regs 11 (by decide)]
    exact h11
  rw [hga] at hg ⊢
  change grant_ok _ _ a 4096 = true at hg
  obtain ⟨hpos, hal, hceil, hda, hdb, hdc⟩ := source_grant_unpack inp hint rbrk rmb rsp a hg
  have hb : gbounds rsp a := ⟨hpos, hal, hceil, hda, hdb, hdc⟩
  rw [pru_4096]
  unfold src_mmap_ms
  rw [adv_apply]
  norm_pc
  sym_block_ex source_segs
    (mkst (regupd regs 10 a) (Z_to_bv 64 0x11150) (zfill a (Z_to_bv 64 4096) (fmem inp rsp rrnd)) rrom)
    10 [false] [] [(1, ELit 0x1103c), (2, EVar 32), (10, EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x30), a] [] RA HRA Hms
  · exact c_lts_pos_0 a (by unfold stack_max_size at hceil; omega)
  · getr_resolve; regupd_resolve; exact hr1
  · getr_resolve; regupd_resolve; exact hr2
  · getr_resolve; regupd_resolve; rfl
  · refine ⟨a, RA, gmem inp rsp rrnd a, hb, rfl, ?_, rfl, rfl, ?_, Hms, ?_⟩
    · rw [mmap_model_lazy]; rfl
    · exact ⟨rfl, rfl⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, gmem_ok inp rsp rrnd a hb, rfl⟩
      all_goals sym_regs HRA
      all_goals first | rfl | exact v_addi_0 _ | sym_close

include Hsp_lo Hsp_hi in
theorem src_read_block (aG : word) (regs : bvmap 5 word) (mem : word → Option byte) (k : Nat)
    (hb : gbounds rsp aG) (hk : k ≤ cap) (hm : mem_ok inp rsp rrnd aG mem)
    (h2 : getr regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30))
    (h8 : getr regs 8 = nat_to_word k) (h9 : getr regs 9 = aG) (h18 : getr regs 18 = aG)
    (h19 : getr regs 19 = Z_to_bv 64 4087) (h20 : getr regs 20 = Z_to_bv 64 4088) :
    ∃ R1, getr R1 1 = (0x111c4 : word) ∧
      getr R1 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ∧ getr R1 8 = nat_to_word k ∧
      getr R1 9 = aG ∧ getr R1 18 = aG ∧ getr R1 19 = Z_to_bv 64 4087 ∧
      getr R1 20 = Z_to_bv 64 4088 ∧ bv_unsigned (getr R1 17) = 63 ∧
      getr R1 10 = Z_to_bv 64 0 ∧ getr R1 11 = bufA aG k ∧
      getr R1 12 = Z_to_bv 64 ((cap - k : Nat) : Int) ∧
      msteps source_segs (mkst regs (Z_to_bv 64 0x11060) mem rrom)
        (mkst R1 (Z_to_bv 64 0x11258) (wbytes mem (scr rsp) (word_to_le_bytes 8 (0x11074 : word))) rrom) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hsms := stack_max_size_val
  have arena_tee_neg4096 : bv_unsigned (Z_to_bv 64 (-4096)) = 18446744073709547520 := rfl
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 0x11060) mem rrom)
    30 [] [] [(2, EVar 32), (8, EVar 33), (9, EVar 34),
      (18, EVar 34), (19, ELit 4087), (20, ELit 4088)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x30), nat_to_word k, aG] [] R1 HR1 Hms
  · refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
    apply store_ok_mono _ _ _ _ _ (mem_ok_grows_w inp rsp rrnd aG mem hm)
    unfold rwmem
    apply store_ok_wrap_window
    · change bv_unsigned rsp - 8388608 ≤ _
      u_norm
      omega
    · u_norm
      omega
  · exact h2
  · exact h8
  · exact h9
  · exact h18
  · exact h19
  · exact h20
  · refine ⟨R1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sym_regs HR1 <;> rfl
    · sym_regs HR1
      change Z_to_bv 64 (bv_unsigned rsp - 48 - 16) = Z_to_bv 64 (bv_unsigned rsp - 64)
      congr 1
      omega
    · sym_regs HR1 <;> rfl
    · sym_regs HR1 <;> rfl
    · sym_regs HR1 <;> rfl
    · sym_regs HR1 <;> rfl
    · sym_regs HR1 <;> rfl
    · sym_regs HR1 <;> rfl
    · sym_regs HR1 <;> rfl
    · sym_regs HR1
      change v_addi (Z_to_bv 64 (bv_unsigned aG + (bv_unsigned (nat_to_word k) + 8))) 0 = _
      rw [v_addi_0]
      exact bufA_calc rsp aG k hb hk
    · sym_regs HR1
      change v_addi (v_sub (Z_to_bv 64 4088) (nat_to_word k)) 0 = _
      rw [v_addi_0]
      exact dcnt_src aG k hk
    · unfold scr
      revert Hms
      sym_mem_norm
      exact fun x => x

def src_rd_ms (R1 : bvmap 5 word) (mem : word → Option byte) : machine_state :=
  { ms_regs := R1, ms_fregs := bvmap_empty, ms_pc_val := 0x11258,
    ms_svc_pending := some (getr R1 17), ms_resv := none,
    ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rrom }

include Hsp_lo Hsp_hi in
theorem src_ret_eof (aG : word) (R1 : bvmap 5 word) (mem : word → Option byte) (k : Nat)
    (h1 : getr R1 1 = (0x111c4 : word))
    (h2 : getr R1 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40))
    (h8 : getr R1 8 = nat_to_word k) (h9 : getr R1 9 = aG) (h18 : getr R1 18 = aG)
    (h19 : getr R1 19 = Z_to_bv 64 4087) (h20 : getr R1 20 = Z_to_bv 64 4088)
    (hra : rdn source_segs mem (scr rsp) 8 = some (word_to_le_bytes 8 (0x11074 : word))) :
    ∃ R2, getr R2 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ∧
      getr R2 8 = nat_to_word k ∧
      getr R2 9 = aG ∧ getr R2 18 = aG ∧
      getr R2 19 = Z_to_bv 64 4087 ∧ getr R2 20 = Z_to_bv 64 4088 ∧
      msteps source_segs (mkst (regupd R1 10 (Z_to_bv 64 0)) (Z_to_bv 64 0x1125c) mem rrom)
        (mkst R2 (Z_to_bv 64 0x11084) mem rrom) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hsms := stack_max_size_val
  have arena_tee_neg4096 : bv_unsigned (Z_to_bv 64 (-4096)) = 18446744073709547520 := rfl
  sym_block_ex source_segs
    (mkst (regupd R1 10 (Z_to_bv 64 0)) (Z_to_bv 64 0x1125c) mem rrom)
    9 [false, false, true] [ELit 0x11074]
    [(1, ELit 0x111c4), (2, EVar 32), (8, EVar 33), (9, EVar 34),
     (18, EVar 34), (19, ELit 4087), (20, ELit 4088), (10, ELit 0)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x40), nat_to_word k, aG] [] R2 HR2 Hms
  · repeat' apply And.intro
    all_goals first
      | rfl
      | exact ⟨word_to_le_bytes 8 (0x11074 : word), hra, bytes_le_to_Z_8 _⟩
      | (unfold cap at *; sym_br)
  · getr_resolve; regupd_resolve; exact h1
  · getr_resolve; regupd_resolve; exact h2
  · getr_resolve; regupd_resolve; exact h8
  · getr_resolve; regupd_resolve; exact h9
  · getr_resolve; regupd_resolve; exact h18
  · getr_resolve; regupd_resolve; exact h19
  · getr_resolve; regupd_resolve; exact h20
  · getr_resolve; regupd_resolve; rfl
  · refine ⟨R2, ?_, ?_, ?_, ?_, ?_, ?_, Hms⟩
    all_goals sym_regs HR2
    all_goals first | rfl | assumption | exact v_addi_0 _ | (change Z_to_bv 64 (bv_unsigned rsp - 64 + 16) = Z_to_bv 64 (bv_unsigned rsp - 48); congr 1; omega)

include Hsp_lo Hsp_hi in
theorem src_ret_blk (aG : word) (R1 : bvmap 5 word) (mem : word → Option byte) (k : Nat) (bs : List byte)
    (h1 : getr R1 1 = (0x111c4 : word))
    (h2 : getr R1 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40))
    (h8 : getr R1 8 = nat_to_word k) (h9 : getr R1 9 = aG) (h18 : getr R1 18 = aG)
    (h19 : getr R1 19 = Z_to_bv 64 4087) (h20 : getr R1 20 = Z_to_bv 64 4088)
    (hra : rdn source_segs mem (scr rsp) 8 = some (word_to_le_bytes 8 (0x11074 : word)))
    (hblo : 1 ≤ bs.length) (hbhi : k + bs.length ≤ cap) :
    ∃ R2, getr R2 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ∧
      getr R2 8 = nat_to_word (k + bs.length) ∧
      getr R2 9 = aG ∧ getr R2 18 = aG ∧
      getr R2 19 = Z_to_bv 64 4087 ∧ getr R2 20 = Z_to_bv 64 4088 ∧
      msteps source_segs (mkst (regupd R1 10 (len_word bs)) (Z_to_bv 64 0x1125c) mem rrom)
        (mkst R2 (if cap ≤ k + bs.length then Z_to_bv 64 0x11084 else Z_to_bv 64 0x11060) mem rrom) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have hsms := stack_max_size_val
  have arena_tee_neg4096 : bv_unsigned (Z_to_bv 64 (-4096)) = 18446744073709547520 := rfl
  have huk := u_ntw k (by unfold cap at hbhi; omega)
  have hul := u_len_word bs (by unfold cap at hbhi; omega)
  have hus : bv_unsigned (v_add (nat_to_word k) (len_word bs)) = (k + bs.length : Nat) := by
    rw [ntw_add_len k bs hbhi, u_ntw _ (by unfold cap at hbhi; omega)]
  by_cases hfull : cap ≤ k + bs.length
  · rw [ite_eq_left hfull]
    sym_block_ex source_segs
      (mkst (regupd R1 10 (len_word bs)) (Z_to_bv 64 0x1125c) mem rrom)
      11 [false, false, false, false] [ELit 0x11074]
      [(1, ELit 0x111c4), (2, EVar 32), (8, EVar 33), (9, EVar 34),
       (18, EVar 34), (19, ELit 4087), (20, ELit 4088), (10, EVar 35)]
      [Z_to_bv 64 (bv_unsigned rsp - 0x40), nat_to_word k, aG, len_word bs] [] R2 HR2 Hms
    · repeat' apply And.intro
      all_goals first
        | rfl
        | exact ⟨word_to_le_bytes 8 (0x11074 : word), hra, bytes_le_to_Z_8 _⟩
        | (unfold cap at *; sym_br)
    · getr_resolve; regupd_resolve; exact h1
    · getr_resolve; regupd_resolve; exact h2
    · getr_resolve; regupd_resolve; exact h8
    · getr_resolve; regupd_resolve; exact h9
    · getr_resolve; regupd_resolve; exact h18
    · getr_resolve; regupd_resolve; exact h19
    · getr_resolve; regupd_resolve; exact h20
    · getr_resolve; regupd_resolve; rfl
    · refine ⟨R2, ?_, ?_, ?_, ?_, ?_, ?_, Hms⟩
      all_goals sym_regs HR2
      all_goals first | rfl | assumption | exact v_addi_0 _ | exact ntw_add_len k bs hbhi | (change Z_to_bv 64 (bv_unsigned rsp - 64 + 16) = Z_to_bv 64 (bv_unsigned rsp - 48); congr 1; omega)

  · rw [ite_eq_right hfull]
    sym_block_ex source_segs
      (mkst (regupd R1 10 (len_word bs)) (Z_to_bv 64 0x1125c) mem rrom)
      11 [false, false, false, true] [ELit 0x11074]
      [(1, ELit 0x111c4), (2, EVar 32), (8, EVar 33), (9, EVar 34),
       (18, EVar 34), (19, ELit 4087), (20, ELit 4088), (10, EVar 35)]
      [Z_to_bv 64 (bv_unsigned rsp - 0x40), nat_to_word k, aG, len_word bs] [] R2 HR2 Hms
    · repeat' apply And.intro
      all_goals first
        | rfl
        | exact ⟨word_to_le_bytes 8 (0x11074 : word), hra, bytes_le_to_Z_8 _⟩
        | (unfold cap at *; sym_br)
    · getr_resolve; regupd_resolve; exact h1
    · getr_resolve; regupd_resolve; exact h2
    · getr_resolve; regupd_resolve; exact h8
    · getr_resolve; regupd_resolve; exact h9
    · getr_resolve; regupd_resolve; exact h18
    · getr_resolve; regupd_resolve; exact h19
    · getr_resolve; regupd_resolve; exact h20
    · getr_resolve; regupd_resolve; rfl
    · refine ⟨R2, ?_, ?_, ?_, ?_, ?_, ?_, Hms⟩
      all_goals sym_regs HR2
      all_goals first | rfl | assumption | exact v_addi_0 _ | exact ntw_add_len k bs hbhi | (change Z_to_bv 64 (bv_unsigned rsp - 64 + 16) = Z_to_bv 64 (bv_unsigned rsp - 48); congr 1; omega)

theorem arena_tee_src_hex_more_lo (R : bvmap 5 word) (mem : word → Option byte) (n oq k : Nat)
    (hn : n ≤ cap) (hoq : oq ≤ 4) (hk : k < 4)
    (h10 : getr R 10 = nat_to_word n)
    (h11 : getr R 11 = Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)))
    (h12 : getr R 12 = Z_to_bv 64 32) (h13 : getr R 13 = Z_to_bv 64 (hw4 n oq k))
    (h14 : getr R 14 = Z_to_bv 64 (8 * (k : Int))) (h16 : getr R 16 = Z_to_bv 64 9)
    (hmore : k + 1 < 4) (hd : nib n (oq + 3 - k) < 10) :
    ∃ R', getr R' 1 = getr R 1 ∧ getr R' 2 = getr R 2 ∧
      getr R' 8 = getr R 8 ∧ getr R' 9 = getr R 9 ∧ getr R' 18 = getr R 18 ∧
      getr R' 10 = nat_to_word n ∧
      (k + 1 < 4 → getr R' 11 = Z_to_bv 64 (4 * ((oq + 3 - (k + 1) : Nat) : Int))) ∧
      getr R' 12 = Z_to_bv 64 32 ∧ getr R' 13 = Z_to_bv 64 (hw4 n oq (k + 1)) ∧
      getr R' 14 = Z_to_bv 64 (8 * ((k + 1 : Nat) : Int)) ∧ getr R' 16 = Z_to_bv 64 9 ∧
      msteps source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
        (mkst R' (Z_to_bv 64 (if k + 1 < 4 then 0x11168 else 0x1118c)) mem rrom) := by
  have h16n := nib_lt16 n (oq + 3 - k)
  have hinc := arena_tee_src_addiw (8 * (k : Int)) 8 (by omega) (by omega) (by omega) (by omega)
  have hdec := arena_tee_src_addiw (4 * ((oq + 3 - k : Nat) : Int)) (-4)
    (by omega) (by omega) (by omega) (by omega)
  have h14' : v_addiw (Z_to_bv 64 (8 * (k : Int))) 8 = Z_to_bv 64 (8 * ((k + 1 : Nat) : Int)) :=
    hinc.trans (congrArg (Z_to_bv 64) (by omega))
  have h11' (hm : k + 1 < 4) : v_addiw (Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int))) (-4) =
      Z_to_bv 64 (4 * ((oq + 3 - (k + 1) : Nat) : Int)) :=
    hdec.trans (congrArg (Z_to_bv 64) (by omega))
  have hloop : (!bv_eqb (v_addiw (Z_to_bv 64 (8 * (k : Int))) 8) (Z_to_bv 64 32)) = decide (k + 1 < 4) := by
    rw [h14', LinuxProcessSemantics.Common.SymBranch.bv_eqb_Z]
    u_norm
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega
  have hdigit : bv_ltu (Z_to_bv 64 9)
      (v_and (v_srl (nat_to_word n) (Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)))) (Z_to_bv 64 15)) =
      decide (10 ≤ nib n (oq + 3 - k)) := by
    rw [v_and_15, dig_val n (oq + 3 - k) _ hn (by omega) rfl,
      LinuxProcessSemantics.Common.SymBranch.bv_ltu_Z]
    u_norm
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  rw [ite_eq_left hmore]
  sym_block_ex source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
    9 [false, true] []
    [(10, EVar 32), (11, EVar 33), (12, ELit 32),
      (13, EVar 34), (14, EVar 35), (16, ELit 9)]
    [nat_to_word n, Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)),
      Z_to_bv 64 (hw4 n oq k), Z_to_bv 64 (8 * (k : Int))] [] R' HR Hms
  · constructor
    · exact hloop.trans (by simp only [decide_eq_true_eq]; omega)
    · exact hdigit.trans (by simp only [decide_eq_false_iff_not]; omega)
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h16
  · refine ⟨R', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Hms⟩
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · intro hm
      sym_regs HR
      exact h11' hm
    · sym_regs HR <;> rfl
    · sym_regs HR
      rw [w_sllw]
      exact hex_step_lo n oq k hn hoq hk hd
    · sym_regs HR
      exact h14' 
    · sym_regs HR <;> rfl

theorem arena_tee_src_hex_more_hi (R : bvmap 5 word) (mem : word → Option byte) (n oq k : Nat)
    (hn : n ≤ cap) (hoq : oq ≤ 4) (hk : k < 4)
    (h10 : getr R 10 = nat_to_word n)
    (h11 : getr R 11 = Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)))
    (h12 : getr R 12 = Z_to_bv 64 32) (h13 : getr R 13 = Z_to_bv 64 (hw4 n oq k))
    (h14 : getr R 14 = Z_to_bv 64 (8 * (k : Int))) (h16 : getr R 16 = Z_to_bv 64 9)
    (hmore : k + 1 < 4) (hd : ¬nib n (oq + 3 - k) < 10) :
    ∃ R', getr R' 1 = getr R 1 ∧ getr R' 2 = getr R 2 ∧
      getr R' 8 = getr R 8 ∧ getr R' 9 = getr R 9 ∧ getr R' 18 = getr R 18 ∧
      getr R' 10 = nat_to_word n ∧
      (k + 1 < 4 → getr R' 11 = Z_to_bv 64 (4 * ((oq + 3 - (k + 1) : Nat) : Int))) ∧
      getr R' 12 = Z_to_bv 64 32 ∧ getr R' 13 = Z_to_bv 64 (hw4 n oq (k + 1)) ∧
      getr R' 14 = Z_to_bv 64 (8 * ((k + 1 : Nat) : Int)) ∧ getr R' 16 = Z_to_bv 64 9 ∧
      msteps source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
        (mkst R' (Z_to_bv 64 (if k + 1 < 4 then 0x11168 else 0x1118c)) mem rrom) := by
  have h16n := nib_lt16 n (oq + 3 - k)
  have hinc := arena_tee_src_addiw (8 * (k : Int)) 8 (by omega) (by omega) (by omega) (by omega)
  have hdec := arena_tee_src_addiw (4 * ((oq + 3 - k : Nat) : Int)) (-4)
    (by omega) (by omega) (by omega) (by omega)
  have h14' : v_addiw (Z_to_bv 64 (8 * (k : Int))) 8 = Z_to_bv 64 (8 * ((k + 1 : Nat) : Int)) :=
    hinc.trans (congrArg (Z_to_bv 64) (by omega))
  have h11' (hm : k + 1 < 4) : v_addiw (Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int))) (-4) =
      Z_to_bv 64 (4 * ((oq + 3 - (k + 1) : Nat) : Int)) :=
    hdec.trans (congrArg (Z_to_bv 64) (by omega))
  have hloop : (!bv_eqb (v_addiw (Z_to_bv 64 (8 * (k : Int))) 8) (Z_to_bv 64 32)) = decide (k + 1 < 4) := by
    rw [h14', LinuxProcessSemantics.Common.SymBranch.bv_eqb_Z]
    u_norm
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega
  have hdigit : bv_ltu (Z_to_bv 64 9)
      (v_and (v_srl (nat_to_word n) (Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)))) (Z_to_bv 64 15)) =
      decide (10 ≤ nib n (oq + 3 - k)) := by
    rw [v_and_15, dig_val n (oq + 3 - k) _ hn (by omega) rfl,
      LinuxProcessSemantics.Common.SymBranch.bv_ltu_Z]
    u_norm
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  rw [ite_eq_left hmore]
  sym_block_ex source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
    10 [true, true] []
    [(10, EVar 32), (11, EVar 33), (12, ELit 32),
      (13, EVar 34), (14, EVar 35), (16, ELit 9)]
    [nat_to_word n, Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)),
      Z_to_bv 64 (hw4 n oq k), Z_to_bv 64 (8 * (k : Int))] [] R' HR Hms
  · constructor
    · exact hloop.trans (by simp only [decide_eq_true_eq]; omega)
    · exact hdigit.trans (by simp only [decide_eq_true_eq]; omega)
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h16
  · refine ⟨R', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Hms⟩
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · intro hm
      sym_regs HR
      exact h11' hm
    · sym_regs HR <;> rfl
    · sym_regs HR
      rw [w_sllw]
      exact hex_step_hi n oq k hn hoq hk (by omega)
    · sym_regs HR
      exact h14' 
    · sym_regs HR <;> rfl

theorem arena_tee_src_hex_last_lo (R : bvmap 5 word) (mem : word → Option byte) (n oq k : Nat)
    (hn : n ≤ cap) (hoq : oq ≤ 4) (hk : k < 4)
    (h10 : getr R 10 = nat_to_word n)
    (h11 : getr R 11 = Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)))
    (h12 : getr R 12 = Z_to_bv 64 32) (h13 : getr R 13 = Z_to_bv 64 (hw4 n oq k))
    (h14 : getr R 14 = Z_to_bv 64 (8 * (k : Int))) (h16 : getr R 16 = Z_to_bv 64 9)
    (hmore : ¬k + 1 < 4) (hd : nib n (oq + 3 - k) < 10) :
    ∃ R', getr R' 1 = getr R 1 ∧ getr R' 2 = getr R 2 ∧
      getr R' 8 = getr R 8 ∧ getr R' 9 = getr R 9 ∧ getr R' 18 = getr R 18 ∧
      getr R' 10 = nat_to_word n ∧
      (k + 1 < 4 → getr R' 11 = Z_to_bv 64 (4 * ((oq + 3 - (k + 1) : Nat) : Int))) ∧
      getr R' 12 = Z_to_bv 64 32 ∧ getr R' 13 = Z_to_bv 64 (hw4 n oq (k + 1)) ∧
      getr R' 14 = Z_to_bv 64 (8 * ((k + 1 : Nat) : Int)) ∧ getr R' 16 = Z_to_bv 64 9 ∧
      msteps source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
        (mkst R' (Z_to_bv 64 (if k + 1 < 4 then 0x11168 else 0x1118c)) mem rrom) := by
  have h16n := nib_lt16 n (oq + 3 - k)
  have hinc := arena_tee_src_addiw (8 * (k : Int)) 8 (by omega) (by omega) (by omega) (by omega)
  have hdec := arena_tee_src_addiw (4 * ((oq + 3 - k : Nat) : Int)) (-4)
    (by omega) (by omega) (by omega) (by omega)
  have h14' : v_addiw (Z_to_bv 64 (8 * (k : Int))) 8 = Z_to_bv 64 (8 * ((k + 1 : Nat) : Int)) :=
    hinc.trans (congrArg (Z_to_bv 64) (by omega))
  have h11' (hm : k + 1 < 4) : v_addiw (Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int))) (-4) =
      Z_to_bv 64 (4 * ((oq + 3 - (k + 1) : Nat) : Int)) :=
    hdec.trans (congrArg (Z_to_bv 64) (by omega))
  have hloop : (!bv_eqb (v_addiw (Z_to_bv 64 (8 * (k : Int))) 8) (Z_to_bv 64 32)) = decide (k + 1 < 4) := by
    rw [h14', LinuxProcessSemantics.Common.SymBranch.bv_eqb_Z]
    u_norm
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega
  have hdigit : bv_ltu (Z_to_bv 64 9)
      (v_and (v_srl (nat_to_word n) (Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)))) (Z_to_bv 64 15)) =
      decide (10 ≤ nib n (oq + 3 - k)) := by
    rw [v_and_15, dig_val n (oq + 3 - k) _ hn (by omega) rfl,
      LinuxProcessSemantics.Common.SymBranch.bv_ltu_Z]
    u_norm
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  rw [ite_eq_right hmore]
  sym_block_ex source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
    9 [false, false] []
    [(10, EVar 32), (11, EVar 33), (12, ELit 32),
      (13, EVar 34), (14, EVar 35), (16, ELit 9)]
    [nat_to_word n, Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)),
      Z_to_bv 64 (hw4 n oq k), Z_to_bv 64 (8 * (k : Int))] [] R' HR Hms
  · constructor
    · exact hloop.trans (by simp only [decide_eq_false_iff_not]; omega)
    · exact hdigit.trans (by simp only [decide_eq_false_iff_not]; omega)
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h16
  · refine ⟨R', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Hms⟩
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · intro hm
      sym_regs HR
      exact h11' hm
    · sym_regs HR <;> rfl
    · sym_regs HR
      rw [w_sllw]
      exact hex_step_lo n oq k hn hoq hk hd
    · sym_regs HR
      exact h14' 
    · sym_regs HR <;> rfl

theorem arena_tee_src_hex_last_hi (R : bvmap 5 word) (mem : word → Option byte) (n oq k : Nat)
    (hn : n ≤ cap) (hoq : oq ≤ 4) (hk : k < 4)
    (h10 : getr R 10 = nat_to_word n)
    (h11 : getr R 11 = Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)))
    (h12 : getr R 12 = Z_to_bv 64 32) (h13 : getr R 13 = Z_to_bv 64 (hw4 n oq k))
    (h14 : getr R 14 = Z_to_bv 64 (8 * (k : Int))) (h16 : getr R 16 = Z_to_bv 64 9)
    (hmore : ¬k + 1 < 4) (hd : ¬nib n (oq + 3 - k) < 10) :
    ∃ R', getr R' 1 = getr R 1 ∧ getr R' 2 = getr R 2 ∧
      getr R' 8 = getr R 8 ∧ getr R' 9 = getr R 9 ∧ getr R' 18 = getr R 18 ∧
      getr R' 10 = nat_to_word n ∧
      (k + 1 < 4 → getr R' 11 = Z_to_bv 64 (4 * ((oq + 3 - (k + 1) : Nat) : Int))) ∧
      getr R' 12 = Z_to_bv 64 32 ∧ getr R' 13 = Z_to_bv 64 (hw4 n oq (k + 1)) ∧
      getr R' 14 = Z_to_bv 64 (8 * ((k + 1 : Nat) : Int)) ∧ getr R' 16 = Z_to_bv 64 9 ∧
      msteps source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
        (mkst R' (Z_to_bv 64 (if k + 1 < 4 then 0x11168 else 0x1118c)) mem rrom) := by
  have h16n := nib_lt16 n (oq + 3 - k)
  have hinc := arena_tee_src_addiw (8 * (k : Int)) 8 (by omega) (by omega) (by omega) (by omega)
  have hdec := arena_tee_src_addiw (4 * ((oq + 3 - k : Nat) : Int)) (-4)
    (by omega) (by omega) (by omega) (by omega)
  have h14' : v_addiw (Z_to_bv 64 (8 * (k : Int))) 8 = Z_to_bv 64 (8 * ((k + 1 : Nat) : Int)) :=
    hinc.trans (congrArg (Z_to_bv 64) (by omega))
  have h11' (hm : k + 1 < 4) : v_addiw (Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int))) (-4) =
      Z_to_bv 64 (4 * ((oq + 3 - (k + 1) : Nat) : Int)) :=
    hdec.trans (congrArg (Z_to_bv 64) (by omega))
  have hloop : (!bv_eqb (v_addiw (Z_to_bv 64 (8 * (k : Int))) 8) (Z_to_bv 64 32)) = decide (k + 1 < 4) := by
    rw [h14', LinuxProcessSemantics.Common.SymBranch.bv_eqb_Z]
    u_norm
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega
  have hdigit : bv_ltu (Z_to_bv 64 9)
      (v_and (v_srl (nat_to_word n) (Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)))) (Z_to_bv 64 15)) =
      decide (10 ≤ nib n (oq + 3 - k)) := by
    rw [v_and_15, dig_val n (oq + 3 - k) _ hn (by omega) rfl,
      LinuxProcessSemantics.Common.SymBranch.bv_ltu_Z]
    u_norm
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  rw [ite_eq_right hmore]
  sym_block_ex source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
    10 [true, false] []
    [(10, EVar 32), (11, EVar 33), (12, ELit 32),
      (13, EVar 34), (14, EVar 35), (16, ELit 9)]
    [nat_to_word n, Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)),
      Z_to_bv 64 (hw4 n oq k), Z_to_bv 64 (8 * (k : Int))] [] R' HR Hms
  · constructor
    · exact hloop.trans (by simp only [decide_eq_false_iff_not]; omega)
    · exact hdigit.trans (by simp only [decide_eq_true_eq]; omega)
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h16
  · refine ⟨R', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Hms⟩
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · intro hm
      sym_regs HR
      exact h11' hm
    · sym_regs HR <;> rfl
    · sym_regs HR
      rw [w_sllw]
      exact hex_step_hi n oq k hn hoq hk (by omega)
    · sym_regs HR
      exact h14' 
    · sym_regs HR <;> rfl

theorem src_hex_iter (R : bvmap 5 word) (mem : word → Option byte) (n oq k : Nat)
    (hn : n ≤ cap) (hoq : oq ≤ 4) (hk : k < 4)
    (h10 : getr R 10 = nat_to_word n)
    (h11 : getr R 11 = Z_to_bv 64 (4 * ((oq + 3 - k : Nat) : Int)))
    (h12 : getr R 12 = Z_to_bv 64 32) (h13 : getr R 13 = Z_to_bv 64 (hw4 n oq k))
    (h14 : getr R 14 = Z_to_bv 64 (8 * (k : Int))) (h16 : getr R 16 = Z_to_bv 64 9) :
    ∃ R', getr R' 1 = getr R 1 ∧ getr R' 2 = getr R 2 ∧
      getr R' 8 = getr R 8 ∧ getr R' 9 = getr R 9 ∧ getr R' 18 = getr R 18 ∧
      getr R' 10 = nat_to_word n ∧
      (k + 1 < 4 → getr R' 11 = Z_to_bv 64 (4 * ((oq + 3 - (k + 1) : Nat) : Int))) ∧
      getr R' 12 = Z_to_bv 64 32 ∧ getr R' 13 = Z_to_bv 64 (hw4 n oq (k + 1)) ∧
      getr R' 14 = Z_to_bv 64 (8 * ((k + 1 : Nat) : Int)) ∧ getr R' 16 = Z_to_bv 64 9 ∧
      msteps source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
        (mkst R' (Z_to_bv 64 (if k + 1 < 4 then 0x11168 else 0x1118c)) mem rrom) := by
  by_cases hmore : k + 1 < 4 <;> by_cases hd : nib n (oq + 3 - k) < 10
  · exact arena_tee_src_hex_more_lo R mem n oq k hn hoq hk h10 h11 h12 h13 h14 h16 hmore hd
  · exact arena_tee_src_hex_more_hi R mem n oq k hn hoq hk h10 h11 h12 h13 h14 h16 hmore hd
  · exact arena_tee_src_hex_last_lo R mem n oq k hn hoq hk h10 h11 h12 h13 h14 h16 hmore hd
  · exact arena_tee_src_hex_last_hi R mem n oq k hn hoq hk h10 h11 h12 h13 h14 h16 hmore hd

theorem src_hdr_entry (regs : bvmap 5 word) (mem : word → Option byte) (n : Nat) (aG : word)
    (_hn : n ≤ cap) (h2 : getr regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30))
    (h8 : getr regs 8 = nat_to_word n) (h9 : getr regs 9 = aG) (h18 : getr regs 18 = aG) :
    ∃ R, getr R 1 = (0x11090 : word) ∧
      getr R 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ∧ getr R 8 = nat_to_word n ∧
      getr R 9 = aG ∧ getr R 18 = aG ∧ getr R 10 = nat_to_word n ∧
      getr R 11 = Z_to_bv 64 (4 * ((4 + 3 - 0 : Nat) : Int)) ∧
      getr R 12 = Z_to_bv 64 32 ∧ getr R 13 = Z_to_bv 64 (hw4 n 4 0) ∧
      getr R 14 = Z_to_bv 64 (8 * ((0 : Nat) : Int)) ∧ getr R 16 = Z_to_bv 64 9 ∧
      msteps source_segs (mkst regs (Z_to_bv 64 0x11084) mem rrom)
        (mkst R (Z_to_bv 64 0x11168) mem rrom) := by
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 0x11084) mem rrom)
    8 [] [] [(8, EVar 32)] [nat_to_word n] [] R HR Hms
  · exact h8
  · refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Hms⟩
    · sym_regs HR <;> rfl
    · sym_regs HR <;> exact h2
    · sym_regs HR <;> rfl
    · sym_regs HR <;> exact h9
    · sym_regs HR <;> exact h18
    · sym_regs HR <;> exact v_addi_0 _
    · sym_regs HR
      exact arena_tee_src_addiw 16 12 (by omega) (by omega) (by omega) (by omega)
    · sym_regs HR <;> rfl
    · change getr _ 13 = Z_to_bv 64 0
      sym_regs HR <;> rfl
    · change getr _ 14 = Z_to_bv 64 0
      sym_regs HR <;> rfl
    · sym_regs HR <;> rfl

theorem src_hdr_mid (R : bvmap 5 word) (mem : word → Option byte) (n : Nat) (aG : word)
    (_hn : n ≤ cap) (hab : bv_unsigned aG + 8 ≤ 2^64) (hso : store_ok source_segs mem aG 4 = true)
    (h1 : getr R 1 = (0x11090 : word)) (h2 : getr R 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30))
    (h8 : getr R 8 = nat_to_word n) (h9 : getr R 9 = aG) (h18 : getr R 18 = aG)
    (h13 : getr R 13 = Z_to_bv 64 (hw4 n 4 4)) :
    ∃ R', getr R' 1 = (0x110a0 : word) ∧
      getr R' 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ∧ getr R' 8 = nat_to_word n ∧
      getr R' 9 = aG ∧ getr R' 18 = aG ∧ getr R' 10 = nat_to_word n ∧
      getr R' 11 = Z_to_bv 64 (4 * ((0 + 3 - 0 : Nat) : Int)) ∧
      getr R' 12 = Z_to_bv 64 32 ∧ getr R' 13 = Z_to_bv 64 (hw4 n 0 0) ∧
      getr R' 14 = Z_to_bv 64 (8 * ((0 : Nat) : Int)) ∧ getr R' 16 = Z_to_bv 64 9 ∧
      msteps source_segs (mkst R (Z_to_bv 64 0x1118c) mem rrom)
        (mkst R' (Z_to_bv 64 0x11168)
          (wbytes mem aG (word_to_le_bytes 4 (Z_to_bv 64 (hw4 n 4 4)))) rrom) := by
  have har := u64_range aG
  sym_block_ex source_segs (mkst R (Z_to_bv 64 0x1118c) mem rrom)
    11 [] [] [(1, ELit 0x11090), (8, EVar 32), (9, EVar 33), (13, EVar 34)]
    [nat_to_word n, aG, Z_to_bv 64 (hw4 n 4 4)] [] R' HR Hms
  · repeat' apply And.intro
    all_goals first | omega | (rw [Int.add_zero, (show Z_to_bv 64 (bv_unsigned aG) = aG from by apply bv_eq_of_unsigned; u_norm; omega)]; exact hso)
  · exact h1
  · exact h8
  · exact h9
  · exact h13
  · refine ⟨R', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sym_regs HR <;> rfl
    · sym_regs HR <;> exact h2
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> exact h18
    · sym_regs HR <;> exact v_addi_0 _
    · sym_regs HR
      exact arena_tee_src_addiw 0 12 (by omega) (by omega) (by omega) (by omega)
    · sym_regs HR <;> rfl
    · change getr _ 13 = Z_to_bv 64 0
      sym_regs HR <;> rfl
    · change getr _ 14 = Z_to_bv 64 0
      sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · revert Hms
      sym_mem_norm
      rw [Int.add_zero, show Z_to_bv 64 (bv_unsigned aG) = aG from by apply bv_eq_of_unsigned; u_norm; omega]
      exact fun h => h

include Hsp_lo Hsp_hi in
theorem src_put2_ecall (R : bvmap 5 word) (mem : word → Option byte) (n : Nat) (aG : word)
    (hn : n ≤ cap) (hab : bv_unsigned aG + 8 ≤ 2^64)
    (hso : store_ok source_segs mem (Z_to_bv 64 (bv_unsigned aG + 4)) 4 = true)
    (hsc : store_ok source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8 = true)
    (h1 : getr R 1 = (0x110a0 : word)) (h2 : getr R 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30))
    (h8 : getr R 8 = nat_to_word n) (h9 : getr R 9 = aG) (h18 : getr R 18 = aG)
    (h13 : getr R 13 = Z_to_bv 64 (hw4 n 0 4)) :
    ∃ R', getr R' 1 = (0x111f8 : word) ∧
      getr R' 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ∧ getr R' 8 = nat_to_word (8 + n) ∧
      getr R' 9 = aG ∧ getr R' 18 = aG ∧ getr R' 10 = Z_to_bv 64 2 ∧
      getr R' 11 = aG ∧ getr R' 12 = nat_to_word (8 + n) ∧ getr R' 17 = Z_to_bv 64 64 ∧
      msteps source_segs (mkst R (Z_to_bv 64 0x1118c) mem rrom)
        (mkst R' (Z_to_bv 64 0x11258)
          (wbytes (wbytes mem (Z_to_bv 64 (bv_unsigned aG + 4))
            (word_to_le_bytes 4 (Z_to_bv 64 (hw4 n 0 4))))
            (scr rsp) (word_to_le_bytes 8 (0x110b8 : word))) rrom) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have har := u64_range aG
  have hun := u_ntw n (by unfold cap at hn; omega)
  have h8n : v_addi (nat_to_word n) 8 = nat_to_word (8 + n) := by
    unfold v_addi nat_to_word at *
    rw [hun]
    congr 1
    omega
  sym_block_ex source_segs (mkst R (Z_to_bv 64 0x1118c) mem rrom)
    26 [] [] [(1, ELit 0x110a0), (2, EVar 32), (8, EVar 33),
      (9, EVar 34), (18, EVar 34), (13, EVar 35)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x30), nat_to_word n, aG, Z_to_bv 64 (hw4 n 0 4)] [] R' HR Hms
  · exact h1
  · exact h2
  · exact h8
  · exact h9
  · exact h18
  · exact h13
  · refine ⟨R', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sym_regs HR <;> rfl
    · sym_regs HR
      change Z_to_bv 64 (bv_unsigned rsp - 48 - 16) = Z_to_bv 64 (bv_unsigned rsp - 64)
      congr 1
      omega
    · sym_regs HR
      exact h8n
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> rfl
    · sym_regs HR <;> exact v_addi_0 aG
    · sym_regs HR
      exact h8n
    · sym_regs HR <;> rfl
    · unfold scr
      revert Hms
      sym_mem_norm
      exact fun h => h

theorem arena_tee_src_hex4 (R : bvmap 5 word) (mem : word → Option byte) (n oq : Nat)
    (hn : n ≤ cap) (hoq : oq ≤ 4) (h10 : getr R 10 = nat_to_word n)
    (h11 : getr R 11 = Z_to_bv 64 (4 * ((oq + 3 : Nat) : Int)))
    (h12 : getr R 12 = Z_to_bv 64 32) (h13 : getr R 13 = Z_to_bv 64 0)
    (h14 : getr R 14 = Z_to_bv 64 0) (h16 : getr R 16 = Z_to_bv 64 9) :
    ∃ R', getr R' 1 = getr R 1 ∧ getr R' 2 = getr R 2 ∧ getr R' 8 = getr R 8 ∧
      getr R' 9 = getr R 9 ∧ getr R' 18 = getr R 18 ∧
      getr R' 13 = Z_to_bv 64 (hw4 n oq 4) ∧
      msteps source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
        (mkst R' (Z_to_bv 64 0x1118c) mem rrom) := by
  obtain ⟨R1, p11, p12, p18, p19, p118, q110, q111, q112, q113, q114, q116, hm1⟩ :=
    src_hex_iter R mem n oq 0 hn hoq (by omega) h10 h11 h12 h13 h14 h16
  obtain ⟨R2, p21, p22, p28, p29, p218, q210, q211, q212, q213, q214, q216, hm2⟩ :=
    src_hex_iter R1 mem n oq 1 hn hoq (by omega) q110 (q111 (by omega)) q112 q113 q114 q116
  obtain ⟨R3, p31, p32, p38, p39, p318, q310, q311, q312, q313, q314, q316, hm3⟩ :=
    src_hex_iter R2 mem n oq 2 hn hoq (by omega) q210 (q211 (by omega)) q212 q213 q214 q216
  obtain ⟨R4, p41, p42, p48, p49, p418, q410, q411, q412, q413, q414, q416, hm4⟩ :=
    src_hex_iter R3 mem n oq 3 hn hoq (by omega) q310 (q311 (by omega)) q312 q313 q314 q316
  refine ⟨R4, ?_, ?_, ?_, ?_, ?_, q413, ?_⟩
  · rw [p41, p31, p21, p11]
  · rw [p42, p32, p22, p12]
  · rw [p48, p38, p28, p18]
  · rw [p49, p39, p29, p19]
  · rw [p418, p318, p218, p118]
  · exact msteps_trans _ _ _ _ hm1 (msteps_trans _ _ _ _ hm2 (msteps_trans _ _ _ _ hm3 hm4))

include Hsp_lo Hsp_hi in
theorem src_put2_ret (R : bvmap 5 word) (mem : word → Option byte) (rest : List byte) (p : word)
    (hne : 1 ≤ rest.length) (hn : rest.length ≤ 8 + cap)
    (hscr : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8 = some (word_to_le_bytes 8 (0x110b8 : word)))
    (hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 = some (word_to_le_bytes 8 (0x11128 : word)))
    (hframe : ∀ a, a ∈ [Z_to_bv 64 (bv_unsigned rsp - 0x30), Z_to_bv 64 (bv_unsigned rsp - 0x28),
      Z_to_bv 64 (bv_unsigned rsp - 0x20), Z_to_bv 64 (bv_unsigned rsp - 0x18), Z_to_bv 64 (bv_unsigned rsp - 0x10)] →
      rdn source_segs mem a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (h1 : getr R 1 = (0x111f8 : word)) (h2 : getr R 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40))
    (h8 : getr R 8 = len_word rest) (h18 : getr R 18 = p) :
    ∃ R2, getr R2 17 = Z_to_bv 64 93 ∧ getr R2 10 = Z_to_bv 64 0 ∧
      msteps source_segs (mkst (regupd R 10 (len_word rest)) (Z_to_bv 64 0x1125c) mem rrom)
        (mkst R2 (Z_to_bv 64 0x1112c) mem rrom) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  have huc := u_len_word rest (by unfold cap at hn; omega)
  have arena_tee_neg4096 : bv_unsigned (Z_to_bv 64 (-4096)) = 18446744073709547520 := rfl
  have hzero : bv_unsigned (v_sub (len_word rest) (len_word rest)) = 0 := by
    unfold v_sub
    rw [Int.sub_self]
    rfl
  sym_block_ex source_segs (mkst (regupd R 10 (len_word rest)) (Z_to_bv 64 0x1125c) mem rrom)
    21 [false, false, false] [ELit 0x110b8, ELit 0x11128, ELit 0, ELit 0, ELit 0, ELit 0, ELit 0]
    [(1, ELit 0x111f8), (2, EVar 32), (8, EVar 33), (10, EVar 33), (18, EVar 34)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x40), len_word rest, p] [] R2 HR Hms
  · repeat' apply And.intro
    all_goals first
      | rfl
      | exact ⟨word_to_le_bytes 8 (0x110b8 : word), hscr, bytes_le_to_Z_8 _⟩
      | exact ⟨word_to_le_bytes 8 (0x11128 : word), hra, bytes_le_to_Z_8 _⟩
      | (refine ⟨word_to_le_bytes 8 (Z_to_bv 64 0), ?_, bytes_le_to_Z_8 _⟩
         apply hframe
         simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true])
      | (rw [c_eq_sub_self]; rfl)
      | (unfold cap at *; sym_br)
  · getr_resolve; regupd_resolve; exact h1
  · getr_resolve; regupd_resolve; exact h2
  · getr_resolve; regupd_resolve; exact h8
  · getr_resolve; regupd_resolve; rfl
  · getr_resolve; regupd_resolve; exact h18
  · refine ⟨R2, ?_, ?_, Hms⟩ <;> (sym_regs HR <;> rfl)

include Hsp_lo Hsp_hi in
theorem src_put_wall (fuel : Nat) (rest : List byte) (p : word) (n : Nat)
    (R : bvmap 5 word) (mem : word → Option byte)
    (hfuel : rest.length ≤ fuel) (hn1 : 1 ≤ n) (hn2 : n ≤ rest.length)
    (hlen : rest.length ≤ 8 + cap) (hplo : 0 < bv_unsigned p)
    (hstk : bv_unsigned p + (rest.length : Int) ≤ bv_unsigned rsp - 0x800000)
    (hscr : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8 = some (word_to_le_bytes 8 (0x110b8 : word)))
    (hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 = some (word_to_le_bytes 8 (0x11128 : word)))
    (hframe : ∀ a, a ∈ [Z_to_bv 64 (bv_unsigned rsp - 0x30), Z_to_bv 64 (bv_unsigned rsp - 0x28),
      Z_to_bv 64 (bv_unsigned rsp - 0x20), Z_to_bv 64 (bv_unsigned rsp - 0x18), Z_to_bv 64 (bv_unsigned rsp - 0x10)] →
      rdn source_segs mem a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (hsc : store_ok source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8 = true)
    (hread : rdn source_segs mem p rest.length = some rest)
    (h1 : getr R 1 = (0x111f8 : word)) (h2 : getr R 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40))
    (h8 : getr R 8 = len_word rest) (h18 : getr R 18 = p) :
    to_wall_tail source_segs (Z_to_bv 64 2)
      (mkst (regupd R 10 (len_word (rest.take n))) (Z_to_bv 64 0x1125c) mem rrom)
      (rest.drop n) (fun ms => to_wexit source_segs ms [] (Z_to_bv 64 0)) := by
  induction fuel generalizing rest p n R mem with
  | zero => omega
  | succ fuel ih =>
    have hlo := rsp_lo_num rsp Hsp_lo
    have hhi := rsp_hi_num rsp Hsp_hi
    have huc := u_len_word rest (by unfold cap at hlen; omega)
    have arena_tee_neg4096 : bv_unsigned (Z_to_bv 64 (-4096)) = 18446744073709547520 := rfl
    have hud := u_len_word_firstn n rest hn2 (by unfold cap at hlen; omega)
    by_cases hfull : n = rest.length
    · subst n
      rw [List.drop_length, List.take_length]
      apply to_wall_tail.twt_done
      obtain ⟨R2, m17, m10, hms⟩ := src_put2_ret rsp Hsp_lo Hsp_hi R mem rest p (by omega) hlen hscr hra hframe h1 h2 h8 h18
      apply msteps_to_wexit _ _ _ _ _ hms
      refine to_wexit.tw_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_1112c rfl) ?_
      apply tw_exit_coden
      · rw [m17]; rfl
      · getr_resolve; exact m10
      · decide
    · have hlt : n < rest.length := by omega
      have hsub := v_sub_len_firstn n rest hn2 (by unfold cap at hlen; omega)
      have hus : bv_unsigned (v_sub (len_word rest) (len_word (rest.take n))) = ((rest.drop n).length : Int) := by
        rw [hsub, u_len_word _ (by rw [List.length_drop]; unfold cap at hlen; omega)]
      sym_block source_segs 33 [false, false, true] [ELit 0x110b8]
        [(1, ELit 0x111f8), (2, EVar 32), (8, EVar 33), (10, EVar 34), (18, EVar 35)]
        [Z_to_bv 64 (bv_unsigned rsp - 0x40), len_word rest, len_word (rest.take n), p] [] R' HR
      · repeat' apply And.intro
        all_goals first
          | omega
          | rfl
          | exact hsc
          | exact ⟨word_to_le_bytes 8 (0x110b8 : word), hscr, bytes_le_to_Z_8 _⟩
          | (rw [List.length_drop] at hus; unfold cap at *; sym_br)
      · getr_resolve; regupd_resolve; exact h1
      · getr_resolve; regupd_resolve; exact h2
      · getr_resolve; regupd_resolve; exact h8
      · getr_resolve; regupd_resolve; rfl
      · getr_resolve; regupd_resolve; exact h18
      · have n1 : getr R' 1 = (0x111f8 : word) := by sym_regs HR <;> rfl
        have n2 : getr R' 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) := by
          sym_regs HR
          change Z_to_bv 64 (bv_unsigned rsp - 64 + 0) = Z_to_bv 64 (bv_unsigned rsp - 64)
          congr 1
          omega
        have n8 : getr R' 8 = len_word (rest.drop n) := by sym_regs HR <;> exact hsub
        have n10 : getr R' 10 = Z_to_bv 64 2 := by sym_regs HR <;> rfl
        have n11 : getr R' 11 = p + nat_to_word n := by
          sym_regs HR
          change v_addi (v_add p (len_word (rest.take n))) 0 = _
          rw [v_addi_0]
          exact v_add_len_firstn p n rest hn2
        have n12 : getr R' 12 = len_word (rest.drop n) := by
          sym_regs HR
          change v_addi (v_sub (len_word rest) (len_word (rest.take n))) 0 = _
          rw [v_addi_0]
          exact hsub
        have n17 : getr R' 17 = Z_to_bv 64 64 := by sym_regs HR <;> rfl
        have n18 : getr R' 18 = p + nat_to_word n := by sym_regs HR <;> exact v_add_len_firstn p n rest hn2
        have hu56 : bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 0x38)) = bv_unsigned rsp - 0x38 := u_Z2bv _ (by omega) (by omega)
        have hup : bv_unsigned (p + nat_to_word n) = bv_unsigned p + (n : Int) := by
          rw [word_add_nat]
          exact u_Z2bv _ (by omega) (by omega)
        have hout (a : word) (k : Nat)
            (ha : bv_unsigned a + (k : Int) ≤ bv_unsigned rsp - 0x38 ∨ bv_unsigned rsp - 0x30 ≤ bv_unsigned a)
            (hk : bv_unsigned a + (k : Int) ≤ 2^64) :
            rdn source_segs (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) (word_to_le_bytes 8 (0x110b8 : word))) a k = rdn source_segs mem a k := by
          apply rdn_wbytes_out
          · rw [length_N_to_le_bytes, hu56]; omega
          · exact hk
          · rw [length_N_to_le_bytes, hu56]; omega
        have hscr' := rdn_wbytes_hit8 source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) (0x110b8 : word) (by rw [hu56]; omega)
        have hra' : rdn source_segs (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) (word_to_le_bytes 8 (0x110b8 : word)))
            (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 = some (word_to_le_bytes 8 (0x11128 : word)) := by
          rw [hout _ _ (by u_norm; omega) (by u_norm; omega)]
          exact hra
        have hframe' (a : word) (ha : a ∈ [Z_to_bv 64 (bv_unsigned rsp - 0x30), Z_to_bv 64 (bv_unsigned rsp - 0x28),
            Z_to_bv 64 (bv_unsigned rsp - 0x20), Z_to_bv 64 (bv_unsigned rsp - 0x18), Z_to_bv 64 (bv_unsigned rsp - 0x10)]) :
            rdn source_segs (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) (word_to_le_bytes 8 (0x110b8 : word))) a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
          have hb : bv_unsigned rsp - 0x30 ≤ bv_unsigned a ∧ bv_unsigned a + 8 ≤ bv_unsigned rsp := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl | rfl <;> (u_norm; constructor <;> omega)
          rw [hout _ _ (by omega) (by omega)]
          exact hframe a ha
        have hsc' := store_ok_mono source_segs 8 _ _ (Z_to_bv 64 (bv_unsigned rsp - 0x38)) (wbytes_grows (word_to_le_bytes 8 (0x110b8 : word)) mem (Z_to_bv 64 (bv_unsigned rsp - 0x38))) hsc
        have hsk : rdn source_segs (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) (word_to_le_bytes 8 (0x110b8 : word)))
            (p + nat_to_word n) (rest.length - n) = some (rest.drop n) := by
          rw [hout _ _ (by rw [hup]; omega) (by rw [hup]; omega)]
          exact LinuxProcessSemantics.Common.SeqExec.rdn_skipn source_segs mem rest.length p rest n hread hn2
        refine to_wall_tail.twt_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_11258 rfl) ?_
        apply to_wall_tail.twt_more
        · rw [List.length_drop]; omega
        · apply twl_write_rec
          · rw [n17]; rfl
          · getr_resolve; exact n10
          · rw [ms_read_bytes_rdn source_segs _ _ _ rfl]
            change rdn source_segs _ (reg_get R' 11) (word_to_nat (reg_get R' 12)) = _
            rw [← getr_nz R' 11 (by decide), ← getr_nz R' 12 (by decide), n11, n12]
            change rdn source_segs _ _ (word_to_nat (nat_to_word (rest.drop n).length)) = _
            rw [word_to_nat_ntw _ (by rw [List.length_drop]; unfold cap at hlen; omega), List.length_drop]
            exact hsk
          · rw [List.length_drop]; omega
          · intro m hm1 hm2
            norm_pc
            apply ih (rest.drop n) (p + nat_to_word n) m R'
            · rw [List.length_drop]; omega
            · exact hm1
            · exact hm2
            · rw [List.length_drop]; omega
            · rw [hup]; omega
            · rw [hup, List.length_drop]; omega
            · exact hscr'
            · exact hra'
            · exact hframe'
            · exact hsc'
            · rw [List.length_drop]; exact hsk
            · exact n1
            · exact n2
            · exact n8
            · exact n18

include Hsp_lo Hsp_hi in
theorem src_tail (fs0 : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (acc : List byte) (c : config)
    (hi : src_inv inp rsp rrnd fs0 acc (0x11084 : word) c) :
    realizes source_segs c (arena_tail fs0 acc) := by
  obtain ⟨aG, regs, mem, hb, hh, hlazy, hfs, hfd0, hfd2, hms0, h9, h18, h20, h19, h8, h2, hle, hm, hrdn⟩ := hi
  cases c with | mkCfg ms0 model =>
    have hlo := rsp_lo_num rsp Hsp_lo
    have hhi := rsp_hi_num rsp Hsp_hi
    have hbs := grant_below_stack rsp aG hb
    have hpos := hb.1
    have hab : bv_unsigned aG + 8 ≤ 2^64 := by omega
    unfold arena_tail
    rw [← hfs]
    apply wall_realizes_ch source_segs (Z_to_bv 64 2) ch2 ms0 model [arena_out acc] (Z_to_bv 64 0) hh hlazy hfd2 fd32_2
    rotate_left
    · exact arena_out_modeled acc hle
    refine ⟨by rw [arena_out_length]; omega, ?_⟩
    apply msteps_to_wall_tail _ _ _ _ _ _ hms0
    obtain ⟨Ra, a1, a2, a8, a9, a18, a10, a11, a12, a13, a14, a16, hmsa⟩ :=
      src_hdr_entry rsp regs mem acc.length aG hle h2 h8 h9 h18
    apply msteps_to_wall_tail _ _ _ _ _ _ hmsa
    obtain ⟨Re, e1, e2, e8, e9, e18, e13, hmse⟩ :=
      arena_tee_src_hex4 Ra mem acc.length 4 hle (by omega) a10 a11 a12 a13 a14 a16
    apply msteps_to_wall_tail _ _ _ _ _ _ hmse
    have hso1 := grant_store_ok inp rsp rrnd Hsp_hi aG mem aG 4 hm hb (by omega) (by omega)
    obtain ⟨Rf, f1, f2, f8, f9, f18, f10, f11, f12, f13, f14, f16, hmsf⟩ :=
      src_hdr_mid rsp Re mem acc.length aG hle hab hso1
        (e1.trans a1) (e2.trans a2) (e8.trans a8) (e9.trans a9) (e18.trans a18) e13
    apply msteps_to_wall_tail _ _ _ _ _ _ hmsf
    let h1 := word_to_le_bytes 4 (Z_to_bv 64 (hw4 acc.length 4 4))
    let mem1 := wbytes mem aG h1
    have hm1 : mem_ok inp rsp rrnd aG mem1 :=
      mem_ok_grant inp rsp rrnd Hsp_hi aG mem aG h1 hm hb (by omega)
        (by dsimp only [h1]; rw [length_N_to_le_bytes]; omega)
    obtain ⟨Rj, j1, j2, j8, j9, j18, j13, hmsj⟩ :=
      arena_tee_src_hex4 Rf mem1 acc.length 0 hle (by omega) f10 f11 f12 f13 f14 f16
    apply msteps_to_wall_tail _ _ _ _ _ _ hmsj
    have hso2 := grant_store_ok inp rsp rrnd Hsp_hi aG mem1 (Z_to_bv 64 (bv_unsigned aG + 4)) 4 hm1 hb
      (by u_norm; omega) (by u_norm; omega)
    have hsc : store_ok source_segs mem1 (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8 = true := by
      apply store_ok_mono _ _ _ _ _ (mem_ok_grows_w inp rsp rrnd aG mem1 hm1)
      unfold rwmem
      apply store_ok_wrap_window
      · change bv_unsigned rsp - 8388608 ≤ _
        u_norm
        omega
      · u_norm
        omega
    obtain ⟨Rk, k1, k2, k8, k9, k18, k10, k11, k12, k17, hmsk⟩ :=
      src_put2_ecall rsp Hsp_lo Hsp_hi Rj mem1 acc.length aG hle hab hso2 hsc
        (j1.trans f1) (j2.trans f2) (j8.trans f8) (j9.trans f9) (j18.trans f18) j13
    apply msteps_to_wall_tail _ _ _ _ _ _ hmsk
    let h2b := word_to_le_bytes 4 (Z_to_bv 64 (hw4 acc.length 0 4))
    let mem3 := wbytes (wbytes mem1 (Z_to_bv 64 (bv_unsigned aG + 4)) h2b) (scr rsp) (word_to_le_bytes 8 (0x110b8 : word))
    have hm3 : mem_ok inp rsp rrnd aG mem3 := by
      apply mem_ok_scratch8 inp rsp rrnd Hsp_hi
      · apply mem_ok_grant inp rsp rrnd Hsp_hi _ _ _ _ hm1 hb
        · u_norm; omega
        · dsimp only [h2b]; rw [length_N_to_le_bytes]; u_norm; omega
      · exact hb
      · unfold scr; u_norm; omega
      · unfold scr; u_norm; omega
    have hscr3 : rdn source_segs mem3 (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8 = some (word_to_le_bytes 8 (0x110b8 : word)) := by
      exact rdn_wbytes_hit8 _ _ _ _ (by unfold scr; u_norm; omega)
    have hra3 : rdn source_segs mem3 (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 = some (word_to_le_bytes 8 (0x11128 : word)) := by
      rw [hm3.2 _ _ (by u_norm; omega) (by u_norm; omega) (by u_norm; omega)]
      exact fread_slot_ra inp rsp rrnd Hsp_lo Hsp_hi
    have hframe3 (a : word) (ha : a ∈ [Z_to_bv 64 (bv_unsigned rsp - 0x30), Z_to_bv 64 (bv_unsigned rsp - 0x28),
        Z_to_bv 64 (bv_unsigned rsp - 0x20), Z_to_bv 64 (bv_unsigned rsp - 0x18), Z_to_bv 64 (bv_unsigned rsp - 0x10)]) :
        rdn source_segs mem3 a 8 = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
      have habs : bv_unsigned rsp - 0x30 ≤ bv_unsigned a ∧ bv_unsigned a + 8 ≤ bv_unsigned rsp := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl <;> (u_norm; constructor <;> omega)
      rw [hm3.2 _ _ (by omega) (by omega) (by omega)]
      exact fread_slot_0 inp rsp rrnd Hsp_lo Hsp_hi a ha
    have hsc3 : store_ok source_segs mem3 (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8 = true := by
      apply store_ok_mono _ _ _ _ _ (mem_ok_grows_w inp rsp rrnd aG mem3 hm3)
      unfold rwmem
      apply store_ok_wrap_window
      · change bv_unsigned rsp - 8388608 ≤ _
        u_norm
        omega
      · u_norm
        omega
    have hlen1 : h1.length = 4 := length_N_to_le_bytes _ _
    have hlen2 : h2b.length = 4 := length_N_to_le_bytes _ _
    have hbuf : rdn source_segs mem3 aG (8 + acc.length) = some (arena_out acc) := by
      have he : hdr8 acc.length = h1 ++ h2b := by
        dsimp only [h1, h2b]
        rw [hw4_bytes, hw4_bytes]
        rfl
      unfold arena_out
      rw [he]
      apply rdn_app
      · unfold mem3
        rw [rdn_wbytes_out _ _ _ _ _ _
          (by rw [length_N_to_le_bytes]; unfold scr; u_norm; omega)
          (by omega) (by rw [length_N_to_le_bytes]; unfold scr; u_norm; omega)]
        change rdn source_segs _ aG (4 + 4) = _
        apply rdn_app
        · rw [rdn_wbytes_out _ _ _ _ _ _ (by rw [hlen2]; u_norm; omega) (by omega) (by rw [hlen2]; u_norm; omega)]
          rw [← hlen1]
          exact rdn_wbytes_hit _ _ _ _ (by rw [hlen1]; omega)
        · rw [word_add_nat]
          rw [← hlen2]
          exact rdn_wbytes_hit _ _ _ _ (by rw [hlen2]; u_norm; omega)
      · rw [word_add_nat]
        unfold mem3
        rw [rdn_wbytes_out _ _ _ _ _ _
          (by rw [length_N_to_le_bytes]; unfold scr; u_norm; unfold cap at hle; omega)
          (by u_norm; unfold cap at hle; omega) (by rw [length_N_to_le_bytes]; unfold scr; u_norm; omega)]
        rw [rdn_wbytes_out _ _ _ _ _ _ (by rw [hlen2]; u_norm; omega)
          (by u_norm; unfold cap at hle; omega) (by rw [hlen2]; u_norm; omega)]
        unfold mem1
        rw [rdn_wbytes_out _ _ _ _ _ _ (by rw [hlen1]; u_norm; omega)
          (by u_norm; unfold cap at hle; omega) (by rw [hlen1]; omega)]
        exact hrdn
    refine to_wall_tail.twt_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_11258 rfl) ?_
    apply to_wall_tail.twt_more
    · rw [arena_out_length]; omega
    · apply twl_write_rec
      · rw [k17]; rfl
      · getr_resolve; exact k10
      · rw [ms_read_bytes_rdn source_segs _ _ _ rfl]
        change rdn source_segs _ (reg_get Rk 11) (word_to_nat (reg_get Rk 12)) = _
        rw [← getr_nz Rk 11 (by decide), ← getr_nz Rk 12 (by decide), k11, k12,
          word_to_nat_ntw _ (by unfold cap at hle; omega)]
        exact hbuf
      · rw [arena_out_length]; omega
      · intro n hn1 hn2
        norm_pc
        apply src_put_wall rsp Hsp_lo Hsp_hi (arena_out acc).length (arena_out acc) aG n Rk mem3
        · omega
        · exact hn1
        · exact hn2
        · rw [arena_out_length]; omega
        · exact hpos
        · rw [arena_out_length]; unfold cap at hle; omega
        · exact hscr3
        · exact hra3
        · exact hframe3
        · exact hsc3
        · rw [arena_out_length]; exact hbuf
        · exact k1
        · exact k2
        · unfold len_word
          rw [arena_out_length]
          exact k8
        · exact k18

include Hsp_lo Hsp_hi in
theorem src_Hfull (fs0 : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (acc : List byte) (c : config)
    (hh : src_LH inp rsp rrnd fs0 acc c) (hfull : cap ≤ acc.length) :
    realizes source_segs c (arena_tail fs0 acc) := by
  apply src_tail inp rsp rrnd Hsp_lo Hsp_hi fs0 acc c
  unfold src_LH at hh
  rw [ite_eq_left hfull] at hh
  exact hh

include Hsp_lo Hsp_hi in
theorem src_Hread (fs0 : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (acc : List byte) (c : config)
    (hlh : src_LH inp rsp rrnd fs0 acc c) (hlt : acc.length < cap) :
    ∃ ms1 buf x8 w,
      m_halted (cfg_model c) = none ∧ m_vm_lazy (cfg_model c) = [] ∧
      fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0) = some (FdChannel (Z_to_bv 64 0)) ∧
      msteps source_segs (cfg_ms c) ms1 ∧ ms1.ms_svc_pending = some x8 ∧ bv_unsigned x8 = 63 ∧
      ms_gpr ms1 0 = Z_to_bv 64 0 ∧ ms_gpr ms1 1 = buf ∧ ms_gpr ms1 2 = dcnt cap acc ∧
      read_bytes_map (ms_writable_byte source_segs ms1) buf (dcnt cap acc) = some w ∧
      access_okb buf (bv_unsigned (dcnt cap acc)) = true ∧
      realizes source_segs (rd_next ms1 (cfg_model c) buf []) (arena_tail fs0 acc) ∧
      (∀ bs, rd_adm (m_stdin (cfg_model c)) (dcnt cap acc) bs → bs ≠ [] →
        src_LH inp rsp rrnd fs0 (acc ++ bs) (rd_next ms1 (cfg_model c) buf bs)) := by
  have hlo := rsp_lo_num rsp Hsp_lo
  have hhi := rsp_hi_num rsp Hsp_hi
  unfold src_LH at hlh
  rw [ite_eq_right (by omega)] at hlh
  obtain ⟨aG, regs, mem, hb, hh, hlazy, hfs, hfd0, hfd2, hms0, h9, h18, h20, h19, h8, h2, hle, hm, hrdn⟩ := hlh
  have hpos := hb.1
  have hbs := grant_below_stack rsp aG hb
  obtain ⟨R1, k1, k2, k8, k9, k18, k19, k20, k17, k10, k11, k12, hms1⟩ :=
    src_read_block inp rsp rrnd Hsp_lo Hsp_hi aG regs mem acc.length hb hle hm h2 h8 h9 h18 h19 h20
  let mem1 := wbytes mem (scr rsp) (word_to_le_bytes 8 (0x11074 : word))
  have hm1 : mem_ok inp rsp rrnd aG mem1 :=
    mem_ok_scratch8 inp rsp rrnd Hsp_hi aG mem (scr rsp) (0x11074 : word) hm hb
      (by unfold scr; u_norm; omega) (by unfold scr; u_norm; omega)
  have hra1 : rdn source_segs mem1 (scr rsp) 8 = some (word_to_le_bytes 8 (0x11074 : word)) :=
    rdn_wbytes_hit8 _ _ _ _ (by unfold scr; u_norm; omega)
  have hrdn1 : rdn source_segs mem1 (Z_to_bv 64 (bv_unsigned aG + 8)) acc.length = some acc := by
    unfold mem1
    rw [rdn_wbytes_below _ _ _ _ _ _
      (by unfold scr; u_norm; unfold cap at hle; omega)
      (by rw [length_N_to_le_bytes]; unfold scr; u_norm; omega)]
    exact hrdn
  have hdc := dcnt_val cap Hcap_lt acc hle
  obtain ⟨w, hwb⟩ := zmem_wbuf source_segs (src_rd_ms R1 mem1) (fmem inp rsp rrnd) aG (Z_to_bv 64 4096)
    (bufA aG acc.length) (dcnt cap acc) hm1.1
    (by change bv_unsigned aG + 4096 ≤ 2^64; omega)
    (by unfold bufA; unfold cap at *; u_norm; omega)
    (by unfold bufA; rw [hdc]; unfold cap at *; u_norm; omega)
  refine ⟨src_rd_ms R1 mem1, bufA aG acc.length, getr R1 17, w,
    hh, hlazy, hfd0, ?_, rfl, k17, ?_, ?_, ?_, hwb, ?_, ?_, ?_⟩
  · apply msteps_trans _ _ _ _ hms0
    apply msteps_trans _ _ _ _ hms1
    exact msteps.mst_step _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_11258 rfl) (msteps.mst_refl _)
  · unfold ms_gpr src_rd_ms
    rw [arg_reg_0, ← getr_nz R1 10 (by decide)]
    exact k10
  · unfold ms_gpr src_rd_ms
    rw [arg_reg_1, ← getr_nz R1 11 (by decide)]
    exact k11
  · unfold ms_gpr src_rd_ms
    rw [arg_reg_2, ← getr_nz R1 12 (by decide)]
    exact k12
  · apply LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.access_okb_intro
    unfold bufA
    rw [u_Z2bv _ (by omega) (by unfold cap at hle; omega), hdc]
    unfold TASK_SIZE cap at *
    omega
  · simp only [rd_next]
    unfold src_rd_ms
    rw [adv_set]
    apply src_tail inp rsp rrnd Hsp_lo Hsp_hi
    obtain ⟨R2, l2, l8, l9, l18, l19, l20, hms2⟩ :=
      src_ret_eof rsp Hsp_lo Hsp_hi aG R1 mem1 acc.length k1 k2 k8 k9 k18 k19 k20 hra1
    exact ⟨aG, R2, mem1, hb, hh, hlazy, hfs, hfd0, hfd2, hms2,
      l9, l18, l20, l19, l8, l2, hle, hm1, hrdn1⟩
  · intro bs hadm hne
    have hbl : acc.length + bs.length ≤ cap := by
      rcases hadm with ⟨he, _⟩ | ⟨_, hhi, _⟩
      · exact False.elim (hne he)
      · rw [hdc] at hhi
        omega
    have hb1 : 1 ≤ bs.length := by
      cases bs with
      | nil => exact False.elim (hne rfl)
      | cons b bs => simp only [List.length_cons]; omega
    cases bs with
    | nil => exact False.elim (hne rfl)
    | cons b0 bs0 =>
      let bs := b0 :: bs0
      have hbl' : acc.length + bs.length ≤ cap := hbl
      have hb1' : 1 ≤ bs.length := hb1
      simp only [rd_next]
      unfold src_rd_ms
      rw [adv_write]
      let mem2 := write_to_mem mem1 (bufA aG acc.length) bs
      have hm2 : mem_ok inp rsp rrnd aG mem2 := by
        apply mem_ok_buf inp rsp rrnd Hsp_hi _ _ _ _ hm1 hb
        · unfold bufA; unfold cap at *; u_norm; omega
        · unfold bufA; unfold cap at *; u_norm; omega
      have hra2 : rdn source_segs mem2 (scr rsp) 8 = some (word_to_le_bytes 8 (0x11074 : word)) := by
        unfold mem2
        rw [write_to_mem_wbytes, rdn_wbytes_disjoint _ _ _ _ _ _
          (by unfold bufA scr; unfold cap at *; u_norm; omega)
          (by unfold scr; u_norm; omega)]
        exact hra1
      have hrdn2 : rdn source_segs mem2 (Z_to_bv 64 (bv_unsigned aG + 8)) (acc.length + bs.length) = some (acc ++ bs) := by
        apply rdn_app
        · unfold mem2
          rw [write_to_mem_wbytes, rdn_wbytes_below _ _ _ _ _ _
            (by unfold bufA; unfold cap at *; u_norm; omega)
            (by unfold bufA; unfold cap at *; u_norm; omega)]
          exact hrdn1
        · rw [bufA_split rsp Hsp_hi aG acc.length hb hle]
          apply LinuxProcessSemantics.Common.StreamExec.rdn_write_to_mem
          unfold bufA
          unfold cap at *
          u_norm
          omega
      obtain ⟨R2, l2, l8, l9, l18, l19, l20, hms2⟩ :=
        src_ret_blk rsp Hsp_lo Hsp_hi aG R1 mem2 acc.length bs k1 k2 k8 k9 k18 k19 k20 hra2 hb1 hbl
      unfold src_LH src_inv
      rw [List.length_append]
      refine ⟨aG, R2, mem2, hb, ?_, ?_, ?_, ?_, ?_, ?_, l9, l18, l20, l19, l8, l2, hbl, hm2, hrdn2⟩
      · rw [m_halted_with_stdin]; exact hh
      · rw [m_vm_lazy_with_stdin]; exact hlazy
      · rw [m_fs_with_stdin]; exact hfs
      · rw [LinuxProcessSemantics.Common.DrainSim.m_fds_with_stdin]; exact hfd0
      · unfold fdchan at *; rw [LinuxProcessSemantics.Common.DrainSim.m_fds_with_stdin]; exact hfd2
      · exact hms2

include Hva Hve Hsp_lo Hsp_hi in
theorem source_realizes (rbrk rmb : word) :
    realizes source_segs
      (init_config source_segs SourceMemImage_init_pc source_phdrs rsp rbrk rmb rrnd source_alloc_limit inp)
      (arena_outcomes (in_fs inp) (in_stdin inp)) := by
  obtain ⟨regs, hra, hsp, h11, h12, h13, h14, h15, hno, hms⟩ :=
    src_to_mmap inp Hva Hve rsp rrnd Hsp_lo Hsp_hi
  unfold init_config arena_outcomes arena_fail
  apply rz_mmap_drain source_segs cap Hcap_lt Hcap_mod (src_LH inp rsp rrnd (in_fs inp)) (arena_tail (in_fs inp))
    (src_Hfull inp rsp rrnd Hsp_lo Hsp_hi (in_fs inp))
    (src_Hread inp rsp rrnd Hsp_lo Hsp_hi (in_fs inp)) _ (src_mmap_ms inp rsp rrnd regs)
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) (getr regs 17) [] (Z_to_bv 64 1)
  · rfl
  · rfl
  · apply init_model_fd1chan
  · exact hms
  · rfl
  · exact hno
  · unfold mmap_args_ok ms_gpr src_mmap_ms
    change reg_get regs 11 ≠ Z_to_bv 64 0 ∧ reg_get regs 12 = Z_to_bv 64 3 ∧
      reg_get regs 13 = Z_to_bv 64 34 ∧ reg_get regs 14 = Z_to_bv 64 (-1) ∧ reg_get regs 15 = Z_to_bv 64 0
    rw [← getr_nz regs 11 (by decide), ← getr_nz regs 12 (by decide),
      ← getr_nz regs 13 (by decide), ← getr_nz regs 14 (by decide), ← getr_nz regs 15 (by decide)]
    refine ⟨?_, h12, h13, ?_, h15⟩
    · rw [h11]; decide
    · rw [h14]; rfl
  · intro e he
    simp only [LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_errnos, List.mem_singleton] at he
    subst e
    exact src_fail_wexit inp rsp rrnd Hsp_lo Hsp_hi regs _ (by decide) (by decide) hra hsp
  · intro a ha
    exact src_grant_LH inp rsp rrnd Hsp_lo Hsp_hi rbrk rmb regs _ a hra hsp h11 ha
  · refine ⟨Z_to_bv 64 0x2aaaaab000, ?_⟩
    have hlen : ms_gpr (src_mmap_ms inp rsp rrnd regs) 1 = Z_to_bv 64 4096 := by
      unfold ms_gpr src_mmap_ms
      rw [arg_reg_1, ← getr_nz regs 11 (by decide)]
      exact h11
    rw [hlen]
    exact source_grant_witness inp _ rbrk rmb rsp Hsp_lo
  · intro b hb
    exact False.elim (List.not_mem_nil hb)

end SourceProof
end LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_source
