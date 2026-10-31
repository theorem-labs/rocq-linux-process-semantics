import LinuxProcessSemantics.Common.AllocSim
import LinuxProcessSemantics.Common.MmapSim
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.ListFacts
import LinuxProcessSemantics.Common.AllocSim2
import LinuxProcessSemantics.Common.CatExec
/-! rocq-baseline: b89fd3aefa642f07b01c02ead422e3cebfce5549 -/

/-! # alloc-join-ns: shared definitions and helper lemmas

PROOF-SIDE FILE (not part of the trusted specification).

Shared observable-behavior spec of both binaries (`argv = av`):
- `argc < 2`: no output, exit 2
- `total = |join(av[1..])| + 1 > 65536`: no output, exit 3
- otherwise: the outcome SET
  `{ ([], 4) } ∪ { ([join(av[1..]) ++ '\n'], 0) }`
  — the SOURCE reaches it through two brk resolutions, the TARGET
  through the two mmap resolution families; allocation emits no
  events, so the sets coincide.

This file: the join-list theory, the brk resolution-set algebra
(parametric in the total byte count `t`), argv/byte helpers, byte
stores of arbitrary bytes, and shared word/nat bridge lemmas.

Rocq's file also restates `of_nat_word_to_nat` (`Common/StoreOk`) and
`region_free_above`/`region_free_below` (`Common/AllocSim`); here the
library's lemmas serve, since a same-named copy makes an unqualified use
ambiguous wherever both namespaces are open.

Bytes are `byte = BitVec 8`, machine values `word = BitVec 64`; unbounded
bookkeeping is in `Int` over `bv_unsigned`; the brk resolution-set
algebra (`growable`/`T1`/`T2`/...) lives in `Common.AllocSim` over words
with `Int` bounds. -/

namespace LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_defs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.MmapSim
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.AllocSim
open LinuxProcessSemantics.Common.AllocSim2
open LinuxProcessSemantics.Common.CatExec

/-- Join with single interior spaces (byte 32). -/
def join1 (l : List (List byte)) : List byte :=
  match l with
  | [] => []
  | [s] => s
  | s :: r@(_ :: _) => s ++ Z_to_bv 8 32 :: join1 r

/-- Join with a TRAILING space after every element. -/
def wjoin (l : List (List byte)) : List byte :=
  match l with
  | [] => []
  | s :: r => s ++ Z_to_bv 8 32 :: wjoin r

/-- The single written buffer on a successful run. -/
def jout (av : List (List byte)) : List byte :=
  join1 av.tail ++ [Z_to_bv 8 10]

theorem join1_cons (s : List byte) (l : List (List byte)) (Hl : l ≠ []) :
    join1 (s :: l) = s ++ Z_to_bv 8 32 :: join1 l := by
  cases l with
  | nil => exact False.elim (Hl rfl)
  | cons a l => simp only [join1]

theorem join1_snoc (l : List (List byte)) (s : List byte) :
    join1 (l ++ [s]) = wjoin l ++ s := by
  induction l with
  | nil => simp only [List.nil_append, join1, wjoin]
  | cons a l ih =>
    rw [List.cons_append, join1_cons a (l ++ [s]) (by
      cases l <;> exact List.cons_ne_nil _ _)]
    rw [ih]
    simp only [wjoin, List.append_assoc, List.cons_append]

theorem wjoin_join1 (l : List (List byte)) (Hl : l ≠ []) :
    wjoin l = join1 l ++ [Z_to_bv 8 32] := by
  induction l with
  | nil => exact False.elim (Hl rfl)
  | cons a l ih =>
    cases l with
    | nil => simp only [wjoin, join1]
    | cons b l =>
      change a ++ Z_to_bv 8 32 :: wjoin (b :: l) = _
      rw [ih (List.cons_ne_nil b l), join1_cons a (b :: l) (List.cons_ne_nil b l)]
      simp only [List.append_assoc, List.cons_append]

theorem length_wjoin (l : List (List byte)) :
    (wjoin l).length = total_arg_bytes_nat l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [wjoin, List.length_append, List.length_cons]
    change a.length + ((wjoin l).length + 1) = a.length + 1 + total_arg_bytes_nat l
    rw [ih]
    omega

theorem length_join1 (l : List (List byte)) (Hl : l ≠ []) :
    (join1 l).length + 1 = total_arg_bytes_nat l := by
  rw [← length_wjoin, wjoin_join1 l Hl]
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem tab_app (l1 l2 : List (List byte)) :
    total_arg_bytes_nat (l1 ++ l2) = total_arg_bytes_nat l1 + total_arg_bytes_nat l2 := by
  induction l1 with
  | nil => exact Nat.zero_add (total_arg_bytes_nat l2) |>.symm
  | cons a l1 ih =>
    simp only [List.cons_append, total_arg_bytes_nat, List.foldr_cons] at ih ⊢
    rw [ih]
    omega

theorem nth_tl (l : List (List byte)) (i : Nat) :
    l.tail.getD i [] = l.getD (i + 1) [] := by
  cases l with
  | nil => cases i <;> rfl
  | cons a l => rfl

theorem length_tl_list (l : List (List byte)) : l.tail.length = l.length - 1 := by
  cases l <;> rfl

theorem firstn_nonnil (l : List (List byte)) (i : Nat) (Hi : 1 ≤ i) (Hl : l ≠ []) :
    l.take i ≠ [] := by
  cases l with
  | nil => exact False.elim (Hl rfl)
  | cons a l =>
    cases i with
    | zero => omega
    | succ i => exact List.cons_ne_nil a (l.take i)

theorem v_slli3_nat (i : Nat) (Hi : (i : Int) ≤ 1024) :
    v_slli (nat_to_word i) 3 = Z_to_bv 64 (8 * (i : Int)) := by
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned]
  rw [v_slli_3 _ (by rw [u_ntw i (by omega)]; omega)]
  rw [u_ntw i (by omega), bv_wrap64_mod, Int.emod_eq_of_lt (by omega) (by omega)]

theorem word_to_nat_ntw (n : Nat) (Hn : (n : Int) < 2 ^ 64) :
    word_to_nat (nat_to_word n) = n := by
  unfold word_to_nat
  change (bv_unsigned (nat_to_word n)).toNat = n
  rw [u_ntw n Hn]
  rfl

/-- Successor step of a `nat_to_word` index as a wrapping bitvector add
(hypothesis-free: both sides wrap identically). -/
theorem ntw_S (n : Nat) : nat_to_word (n + 1) = nat_to_word n + 1 := by
  apply bv_eq_of_unsigned
  rw [nat_to_word, bv_unsigned_add, nat_to_word, Z_to_bv_unsigned, Z_to_bv_unsigned]
  change ((n + 1 : Nat) : Int) % 2 ^ 64 = (((n : Int) % 2 ^ 64) + 1) % 2 ^ 64
  rw [Int.emod_add_emod]
  rfl

/-- `v_sub` on in-range `nat_to_word` operands. -/
theorem ntw_sub (m k : Nat) (Hk : k ≤ m) (Hm : (m : Int) < 2 ^ 64) :
    v_sub (nat_to_word m) (nat_to_word k) = nat_to_word (m - k) := by
  apply bv_eq_of_unsigned
  unfold v_sub
  rw [u_ntw m Hm, u_ntw k (by omega), u_ntw (m - k) (by omega)]
  rw [u_Z2bv _ (by omega) (by omega)]
  omega

/-- The first brk node: brk(0) is DETERMINISTIC — it reports the
quantified ASLR base `b` — so the resolution set is the singleton
{b} and the branch outcome set is `T1` AT `b`. `growable` at `b`
(from `Run.valid_brk`'s window bounds) makes both outcomes live. -/
theorem twoU_iff_T1 (reserved : List (word × word)) (lim top : Int) (t : word)
    (wbuf : List byte) (b : word) (P : word → Prop)
    (HP : ∀ r, P r ↔ r = b) (Hg : growable reserved lim top t b)
    (Ht : t ≠ Z_to_bv 64 0) (o : List (List byte) × word) :
    two_outcomes [] (Z_to_bv 64 4) [wbuf] (Z_to_bv 64 0) o ↔
      ∃ r, P r ∧ T1 reserved lim top t [wbuf] r o := by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨b, (HP b).mpr rfl, Or.inl ⟨rfl, Or.inr (Or.inr Ht)⟩⟩
    · exact ⟨b, (HP b).mpr rfl, Or.inr ⟨Hg, rfl⟩⟩
  · rintro ⟨r, _, (⟨Ho, _⟩ | ⟨_, Ho⟩)⟩
    · exact Or.inl Ho
    · exact Or.inr Ho

theorem pru_Z_bounds (n : Int) (_Hn : 0 ≤ n) :
    n ≤ page_round_up_Z n ∧ page_round_up_Z n ≤ n + 4095 := by
  unfold page_round_up_Z page_size
  have H := Int.emod_add_ediv_mul (n + 4095) 4096
  have Hm := Int.emod_nonneg (n + 4095) (by decide : (4096 : Int) ≠ 0)
  have Hm' := Int.emod_lt_of_pos (n + 4095) (by decide : (0 : Int) < 4096)
  omega

/-- `bv_unsigned` of the word-level page round-up, for small lengths. -/
theorem pru_u (w : word) (Hw : bv_unsigned w ≤ 2097152) :
    bv_unsigned (page_round_up w) = page_round_up_Z (bv_unsigned w) := by
  unfold page_round_up
  have Hr := u64_range w
  obtain ⟨H1, H2⟩ := pru_Z_bounds (bv_unsigned w) Hr.1
  exact u_Z2bv _ (by omega) (by omega)

theorem valid_argv_tab (av : List (List byte)) (Hav : valid_argv av) :
    total_arg_bytes_nat av ≤ 2097152 := by
  obtain ⟨_, Htot, _⟩ := Hav
  rw [total_arg_bytes_Z] at Htot
  apply Int.ofNat_le.mp
  rw [of_nat_2097152]
  exact Htot

/-- `v_add`/`v_sub` agree with the wrapping bitvector operators
(hypothesis-free: both sides wrap identically). -/
theorem v_add_word (x y : word) : v_add x y = x + y := by
  apply bv_eq_of_unsigned
  rw [v_add, Z_to_bv_unsigned, bv_unsigned_add]

theorem v_sub_word (x y : word) : v_sub x y = x - y := by
  apply bv_eq_of_unsigned
  rw [v_sub, Z_to_bv_unsigned, bv_unsigned_sub]

theorem word_add_comm (x y : word) : x + y = y + x := by
  apply bv_eq_of_unsigned
  rw [bv_unsigned_add, bv_unsigned_add, Int.add_comm]

/-- Unsigned value of a wrapping `v_add` (single wraparound).
NOTE: this is the `bv_unsigned`-level variant of StepTac's
`v_add_wrap` (which equates the `v_add` value to a `Z_to_bv`);
kept here under a non-shadowing name. -/
theorem v_add_wrap_u (x y : word) (Hw : 2 ^ 64 ≤ bv_unsigned x + bv_unsigned y) :
    bv_unsigned (v_add x y) = bv_unsigned x + bv_unsigned y - 2 ^ 64 := by
  unfold v_add
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  have Hx := u64_range x
  have Hy := u64_range y
  have E : bv_unsigned x + bv_unsigned y =
      (bv_unsigned x + bv_unsigned y - 2 ^ 64) + 2 ^ 64 := by omega
  calc
    _ = ((bv_unsigned x + bv_unsigned y - 2 ^ 64) + 2 ^ 64) % 2 ^ 64 :=
      congrArg (fun z : Int => z % 2 ^ 64) E
    _ = _ := by rw [Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Signed-vs-2 comparison for the `sltiu ., ., 2` separator test. -/
theorem v_sltiu_2 (x : word) :
    v_sltiu x 2 = (if decide (bv_unsigned x < 2) then Z_to_bv 64 1 else Z_to_bv 64 0) := by
  unfold v_sltiu
  rfl

theorem v_xori_1_1 : v_xori (Z_to_bv 64 1) 1 = Z_to_bv 64 0 := by decide

theorem v_xori_0_1 : v_xori (Z_to_bv 64 0) 1 = Z_to_bv 64 1 := by decide

/-- Signed comparison as an `Int` test on small operands (`c_lts_small`
composed with the `bv_ltu`-is-unsigned-less-than equation). -/
theorem c_lts_ltb (x y : word) (Hx : bv_unsigned x < 2 ^ 63)
    (Hy : bv_unsigned y < 2 ^ 63) :
    c_lts x y = decide (bv_unsigned x < bv_unsigned y) := by
  rw [c_lts_small x y Hx Hy]
  unfold bv_ltu bv_unsigned
  rw [Bool.eq_iff_iff, BitVec.ult_iff_lt, BitVec.lt_def, decide_eq_true_eq]
  exact Int.ofNat_lt.symm

/-- Store byte, address and BYTE value pre-normalized: the register
holds the zero-extension of the byte `b` (an `lbu` writeback).
`step_sb256`-era value hypotheses are typed away; this is
`MmapSim.step_sb_at` with the low-byte equation discharged. -/
theorem step_sb_atv (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (a : word) (b : byte)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decode_any w = some (.Store .SZ1 rs1 rs2 imm, 4))
    (Ha : v_addi (getr regs rs1) (bv_signed imm) = a)
    (Hv : getr regs rs2 = Z_to_bv 64 (bv_unsigned b))
    (Hok : RiscvSemantics.store_ok segs mem a 1 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom) := by
  apply step_sb_at segs regs pc mem rom w rs1 rs2 imm a
    (Z_to_bv 64 (bv_unsigned b)) b Hf He Hd Ha Hv
  · rw [u_zext8]
    apply bv_eq_of_unsigned
    rw [Z_to_bv_unsigned]
    have H := u8_range b
    change bv_unsigned b % 256 = bv_unsigned b
    exact Int.emod_eq_of_lt H.1 H.2
  · exact Hok

end LinuxProcessSemantics.Examples.alloc_join_ns.alloc_join_ns_defs
