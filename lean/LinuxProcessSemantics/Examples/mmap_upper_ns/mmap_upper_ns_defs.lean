import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.MmapSim
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.ListFacts
import LinuxProcessSemantics.Common.MuslStrlen
import LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_code
import LinuxProcessSemantics.Examples.mmap_upper_ns.SourceMemImage
import LinuxProcessSemantics.Examples.mmap_upper_ns.TargetMemImage

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b
-/

/-! # mmap-upper-ns: shared definitions, tactics and value lemmas

PROOF-SIDE FILE (not part of the trusted specification).

Both binaries implement mmap-upper. With `s = argv[1]`, `n = |s|`:
`argc < 2` exits 2 without output; `n > 4095` exits 3 without output;
mmap failure exits 4 without output; a granted page leads to ONE write of
`upper s ++ '\n'`, munmap, and exit 0.

The mmap branch point is handled by Common.MmapSim (`tmw`/`twm` and
`mmap_strong_equiv_te`); this file carries the shared pure spec
(`upperb`/`upperv`/`out_buf`) and value lemmas for both uppercase idioms.

String bytes are `byte = BitVec 8`, machine values `word = BitVec 64`;
unbounded bookkeeping uses `Int` over `bv_unsigned`. Computed sp-relative
values use `Z_to_bv 64 (...)`, pc values use numeral literals, and loop
indices use `nat_to_word`. The Rocq step-chaining tactics live in
Common/StepTac.v; this Rocq file defines no Ltac tactics. Closed equations
that Rocq proves with `bveq` use `decide`, as in the cat1024_ns port.
-/

namespace LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_defs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.ListFacts
open LinuxProcessSemantics.Common.MuslStrlen
open LinuxProcessSemantics.Examples.mmap_upper_ns.SourceMemImage
open LinuxProcessSemantics.Examples.mmap_upper_ns.TargetMemImage
open LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_code

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-! ## Small generic helpers (candidates for a Common lift) -/

theorem word_to_nat_ntw (n : Nat) (hn : (n : Int) < 2 ^ 64) :
    word_to_nat (nat_to_word n) = n := by
  have h := u_ntw n hn
  unfold bv_unsigned at h
  unfold word_to_nat
  omega

-- `c_eq_0_of_u` lives in Common/PropExec.v.
theorem c_eq_refl (x : word) : c_eq x x = true :=
  (bv_eqb_eq x x).2 rfl

/-- Signed comparison of two small (below 2^63) words is the unsigned
`Int` comparison: the composition of `c_lts_small` and `c_ltu_ltb`. -/
theorem c_lts_small_ltb (x y : word)
    (hx : bv_unsigned x < 2 ^ 63) (hy : bv_unsigned y < 2 ^ 63) :
    c_lts x y = decide (bv_unsigned x < bv_unsigned y) := by
  rw [c_lts_small x y hx hy]
  exact c_ltu_ltb x y

/-- Loop-index word bridges. -/
theorem v_addi_word_Sj (a : word) (j : Nat) :
    v_addi (a + nat_to_word j) 1 = a + nat_to_word (j + 1) := by
  rw [word_add_nat, word_add_nat]
  apply bv_eq_of_unsigned
  simp only [v_addi, Z_to_bv_unsigned, bv_wrap64_mod, Int.emod_add_emod]
  congr 1

theorem v_addi_ntw_pred (j : Nat) (hj : (j : Int) + 1 < 2 ^ 64) :
    v_addi (nat_to_word (j + 1)) (-1) = nat_to_word j := by
  unfold v_addi nat_to_word
  rw [u_Z2bv _ (by omega) (by omega)]
  congr 1
  omega

/-! ## The shared observable-behavior spec

`byte_at` (byte `k` of string `s` laid out as `s` then a NUL) lives in CatExec.
-/

def islower (b : byte) : Bool :=
  decide (97 ≤ bv_unsigned b) && decide (bv_unsigned b ≤ 122)

def upperb (b : byte) : byte :=
  if islower b then Z_to_bv 8 (bv_unsigned b - 32) else b

def upperv (s : List byte) : List byte := s.map upperb

/-- The single written buffer: uppercased string plus '\n'. -/
def out_buf (s : List byte) : List byte := upperv s ++ [Z_to_bv 8 10]

theorem length_upperv (s : List byte) : (upperv s).length = s.length := by
  exact List.length_map upperb

theorem length_out_buf (s : List byte) : (out_buf s).length = s.length + 1 := by
  simp only [out_buf, List.length_append, length_upperv, List.length_singleton]

theorem islower_bounds (b : byte) (hl : islower b = true) :
    97 ≤ bv_unsigned b ∧ bv_unsigned b ≤ 122 := by
  simpa only [islower, Bool.and_eq_true, decide_eq_true_eq] using hl

/-! ## Shared small facts

`valid_argv_str_len`/`str_nz`/`str_bytes`, `byte_at_bound`/`len`/`nz`,
and `nth_lt_byte_at` live in Rocq's CatExec.
-/

/-- Peeling one element off the uppercased prefix. -/
theorem upperv_firstn_S (s : List byte) (i : Nat) (hi : i < s.length) :
    upperv (s.take (i + 1)) = upperv (s.take i) ++ [upperb (byte_at s i)] := by
  rw [nth_lt_byte_at s i hi, firstn_S_nth byte s i (Z_to_bv 8 0) hi]
  simp only [upperv, List.map_append, List.map_cons, List.map_nil]

theorem length_upperv_firstn (s : List byte) (i : Nat) (hi : i ≤ s.length) :
    (upperv (s.take i)).length = i := by
  rw [length_upperv]
  exact List.length_take_of_le hi

/-! ## Value lemmas: the uppercase idioms -/

/-- Low byte of `b - 97` (source: addiw -97 + andi 255; target:
addi -97 + andi 255). -/
def usub97 (b : byte) : word :=
  Z_to_bv 64 (if decide (97 ≤ bv_unsigned b)
    then bv_unsigned b - 97 else bv_unsigned b + 159)

theorem u_usub97 (b : byte) :
    bv_unsigned (usub97 b) =
      (if decide (97 ≤ bv_unsigned b) then bv_unsigned b - 97 else bv_unsigned b + 159) := by
  have hb := u8_range b
  unfold usub97
  split <;> apply u_Z2bv <;> simp only [decide_eq_true_eq] at * <;> omega

theorem usub97_le25 (b : byte) (hl : islower b = true) :
    bv_unsigned (usub97 b) ≤ 25 := by
  have hb := islower_bounds b hl
  rw [u_usub97, ite_eq_left (by exact decide_eq_true hb.1)]
  omega

theorem usub97_gt25 (b : byte) (hl : islower b = false) :
    25 < bv_unsigned (usub97 b) := by
  have hb := u8_range b
  simp only [islower, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hl
  rw [u_usub97]
  split <;> simp only [decide_eq_true_eq] at * <;> omega

theorem land255_mod_Z (z : Int) (_hz : 0 ≤ z) : Z_land z 255 = z % 256 :=
  Z_land_255 z

/-- `andi 255` as a mod-256 truncation. -/
theorem v_andi_255 (x : word) :
    v_andi x 255 = Z_to_bv 64 (bv_unsigned x % 256) := by
  unfold v_andi
  change Z_to_bv 64 (Z_land (bv_unsigned x) 255) = _
  rw [land255_mod_Z _ (u64_range x).1]

/-- Small negative immediates on a zero-extended byte. -/
theorem v_addiw_m97 (b : byte) :
    v_addiw (Z_to_bv 64 (bv_unsigned b)) (-97) = Z_to_bv 64 (bv_unsigned b - 97) := by
  have hb := u8_range b
  rw [v_addiw, u_zext8]
  unfold bv_swrap bv_wrap bv_half_modulus bv_modulus
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  congr 1
  omega

theorem v_addiw_m32 (b : byte) :
    v_addiw (Z_to_bv 64 (bv_unsigned b)) (-32) = Z_to_bv 64 (bv_unsigned b - 32) := by
  have hb := u8_range b
  rw [v_addiw, u_zext8]
  unfold bv_swrap bv_wrap bv_half_modulus bv_modulus
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  congr 1
  omega

theorem v_addi_byte_m97 (b : byte) :
    v_addi (Z_to_bv 64 (bv_unsigned b)) (-97) = Z_to_bv 64 (bv_unsigned b - 97) := by
  rw [v_addi, u_zext8]
  rfl

/-- Shared tail: `andi 255` of the wrapped `b - 97`. -/
theorem usub97_andi (b : byte) :
    v_andi (Z_to_bv 64 (bv_unsigned b - 97)) 255 = usub97 b := by
  have hb := u8_range b
  rw [v_andi_255, Z_to_bv_unsigned, bv_wrap64_mod]
  unfold usub97
  congr 1
  split <;> simp only [decide_eq_true_eq] at * <;> omega

/-- Source form: addiw -97 followed by andi 255. -/
theorem usub97_addiw (b : byte) :
    v_andi (v_addiw (Z_to_bv 64 (bv_unsigned b)) (-97)) 255 = usub97 b := by
  rw [v_addiw_m97, usub97_andi]

/-- Target form: addi -97 followed by andi 255. -/
theorem usub97_addi (b : byte) :
    v_andi (v_addi (Z_to_bv 64 (bv_unsigned b)) (-97)) 255 = usub97 b := by
  rw [v_addi_byte_m97, usub97_andi]

/-- Source lowercase path. -/
theorem upper_addiw (b : byte) (hl : islower b = true) :
    v_andi (v_addiw (Z_to_bv 64 (bv_unsigned b)) (-32)) 255 =
      Z_to_bv 64 (bv_unsigned b - 32) := by
  have hb := islower_bounds b hl
  rw [v_addiw_m32, v_andi_255, u_Z2bv _ (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)]

/-- Stored-byte normalizations (`step_sb_at`'s
`Z_to_bv 8 (bv_unsigned v)` hypothesis). -/
theorem sb_upper_lo (b : byte) (hl : islower b = true) :
    Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b - 32))) = upperb b := by
  have hb := islower_bounds b hl
  rw [upperb, hl, ite_eq_left rfl, u_Z2bv _ (by omega) (by omega)]

theorem sb_id (b : byte) :
    Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) = b :=
  zext8_byte b

theorem sb_upper_hi (b : byte) (hl : islower b = false) :
    Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) = upperb b := by
  rw [sb_id, upperb, hl]
  rfl

/-- Target sltiu flag on the shifted byte. -/
theorem v_sltiu_26 (x : word) :
    v_sltiu x 26 =
      (if decide (bv_unsigned x < 26) then Z_to_bv 64 1 else Z_to_bv 64 0) := rfl

/-- Target negw of the flag. -/
theorem negw_1 :
    v_subw (Z_to_bv 64 0) (Z_to_bv 64 1) = Z_to_bv 64 (2 ^ 64 - 1) := by decide

theorem negw_0 : v_subw (Z_to_bv 64 0) (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide

theorem andi_m1_224 :
    v_andi (Z_to_bv 64 (2 ^ 64 - 1)) 224 = Z_to_bv 64 224 := by decide

theorem andi_0_224 : v_andi (Z_to_bv 64 0) 224 = Z_to_bv 64 0 := by decide

/-- Target stored byte on the lowercase branch: low 8 bits of b + 224. -/
theorem target_upper_lo (b : byte) (hl : islower b = true) :
    Z_to_bv 8 (bv_unsigned (v_add (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 224))) =
      upperb b := by
  have hb := islower_bounds b hl
  rw [v_add, u_zext8]
  change Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b + 224))) = _
  rw [u_Z2bv _ (by omega) (by omega), upperb, hl, ite_eq_left rfl]
  apply bv_eq_of_unsigned
  simp only [Z_to_bv_unsigned, bv_wrap]
  omega

theorem target_upper_hi (b : byte) (hl : islower b = false) :
    Z_to_bv 8 (bv_unsigned (v_add (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0))) =
      upperb b := by
  rw [v_add, u_zext8]
  change Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b + 0))) = _
  rw [Int.add_zero]
  exact sb_upper_hi b hl

/-! ## musl strlen's word-at-a-time zero detection

The arithmetic (zero iff no byte is zero, with the borrow-chain caveat)
lives in Common/MuslStrlen: `HZ.Tz_nozero`/`HZ.Tz_haszero`, the byte bridge
`zb_of_bytes`, and the instruction-shape bridge `v_haszero`.
-/

/-- The machine-level zero-detection value computed by musl's strlen
word loop: `(w + 0xfefefefefefefeff) & ~w & 0x8080808080808080`. -/
def hzw (v : word) : word :=
  v_and (v_and (v_add v (Z_to_bv 64 18374403900871474943))
    (v_xori v (-1))) (Z_to_bv 64 9259542123273814144)

theorem u_hzw (v : word) : bv_unsigned (hzw v) = HZ.Tz (bv_unsigned v) :=
  v_haszero v

/-- `step_ld`'s value side condition for an arbitrary 8-byte read. -/
theorem u_le_bytes_to_word8 (bs : List byte) (hlen : bs.length = 8) :
    bytes_le_to_Z bs = bv_unsigned (le_bytes_to_word bs) := by
  have hb := bytes_le_to_Z_range bs hlen
  exact (u_Z2bv _ hb.1 hb.2).symm

theorem hzw_miss (bs : List byte) (hlen : bs.length = 8)
    (hnz : ∀ b, b ∈ bs → bv_unsigned b ≠ 0) :
    hzw (le_bytes_to_word bs) = Z_to_bv 64 0 := by
  apply bv_eq_of_unsigned
  rw [u_hzw, ← u_le_bytes_to_word8 bs hlen]
  have hz : ∀ i : Nat, i < 8 → HZ.zb (bytes_le_to_Z bs) i ≠ 0 := by
    intro i hi
    have hib : i < bs.length := by omega
    rw [zb_of_bytes bs i hib, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hib, Option.getD_some]
    exact hnz _ (List.getElem_mem hib)
  rw [HZ.Tz_nozero _ (bytes_le_to_Z_range bs hlen) hz]
  rfl

theorem hzw_hit (pre : List byte) (z : byte) (post : List byte)
    (hlen : (pre ++ z :: post).length = 8)
    (hnz : ∀ b, b ∈ pre → bv_unsigned b ≠ 0) (hz : bv_unsigned z = 0) :
    bv_unsigned (hzw (le_bytes_to_word (pre ++ z :: post))) ≠ 0 := by
  rw [u_hzw, ← u_le_bytes_to_word8 _ hlen]
  have hpre : pre.length < 8 := by
    simp only [List.length_append, List.length_cons] at hlen
    omega
  apply HZ.Tz_haszero _ pre.length (bytes_le_to_Z_range _ hlen) hpre
  · rw [zb_of_bytes _ _ (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
    exact hz
  · intro j hj
    rw [zb_of_bytes _ _ (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_left hj, List.getElem?_eq_getElem hj, Option.getD_some]
    exact hnz _ (List.getElem_mem hj)

/-! ## Misc numeric facts -/

theorem page_round_up_Z_4096 : page_round_up_Z 4096 = 4096 := by decide

theorem pru_4096 :
    LinuxProcessSemantics.Common.MmapSim.page_round_up (Z_to_bv 64 4096) =
      Z_to_bv 64 4096 := by decide

-- `errno_ret_range`/`errno_ret_signed` live in PropExec;
-- `v_addi_0` is hypothesis-free.

end LinuxProcessSemantics.Examples.mmap_upper_ns.mmap_upper_ns_defs
