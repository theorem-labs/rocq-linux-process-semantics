-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Prog/memset.v
-- and the proof it applies, oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/R_memset.v
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.memset_c
import OssFuzzTheorems.libreac.fuzz_knock.Image.PlainCode
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.MmapSim
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Riscv.DecodeC

/-! `lib/Prog/memset.v` (5 lines) and the proof it applies, `lib/R_memset.v`
(316 lines): musl's `memset`, at `0x1ac04` of `fuzz_knock.plain`, 62
instructions with three byte-at-a-time tails, a 4-byte body, an 8-byte loop and
seven early returns.

Paths without a repository are in theorem-labs/oss-verify-proofs-internal
`ossv/recipes` `9b0ac6f0e6`, under `projects/libreac/fuzz_knock/proofs/`;
`linux-process-semantics@ff0313ba4f:…` names the Lean model.

## What the Rocq proof carries that this one does not

`R_memset.v` states its invariant over `lib/Lib/Arr.v`'s `u8arr`, the
`list byte` the destination holds, together with `lib/Spec/StrFun.v`'s
`filled`, which records the indices of that list already holding the byte.
Neither file has a Lean twin. Here the same invariant is `Fill` below: the `n`
writable bytes at `A`, a SET `Q` of offsets known to hold `c`, and the three
frame facts the post-state needs. No byte list appears, because nothing in the
contract reads one: the post-state's `rw_cells` is recovered from `Q` covering
`[0, n)` (`Fill.finish`), which is what Rocq's `filled_all` does.
`Fill.store` is the twin of Rocq's `mst` tactic, and `sb_step`, `sw_step` and
`sd_step` are one store instruction each: the machine step and the invariant
update in one move.

The walk itself follows `R_memset.v` instruction for instruction. It is cut at
the seven branch targets into `blk_1ac04` … `blk_1acc8`, each of which takes
the next block as a hypothesis, and `loop_body`, the twin of `R_memset.v`'s
`memset_loop` (`:190-220`), which keeps its invariant and its `4 ∣ r`
premise. `memset_walk` chains them; `codeOk` is the one place the real image is
read, through the generated `F_<pc>`/`D_<pc>` of
`OssFuzzTheorems.libreac.fuzz_knock.Image.PlainCode`.

Everything but `memset_holds` is `private`: this file proves one contract. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.memset

open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StoreOk
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Cells
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Step (rw_cells)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState (ret_pc)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.memset_c




/-! ## Addresses -/

private theorem wa_unsigned (x : Int) (h0 : 0 ≤ x) (h1 : x < 2 ^ 64) :
    bv_unsigned (wa x) = x := bv_unsigned_Z_to_bv_small x h0 h1

private theorem v_addi_wa (x d : Int) : v_addi (wa x) d = wa (x + d) := by
  apply bv_eq_of_unsigned
  simp only [v_addi, wa, Z_to_bv_unsigned, bv_wrap]
  omega

private theorem v_add_wa (x y : Int) : v_add (wa x) (wa y) = wa (x + y) := by
  apply bv_eq_of_unsigned
  simp only [v_add, wa, Z_to_bv_unsigned, bv_wrap]
  omega

private theorem wa_succ (x : Int) : wa x + 1 = wa (x + 1) := by
  apply bv_eq_of_unsigned
  have h1 : bv_unsigned (1 : word) = 1 := rfl
  simp only [bv_unsigned_add, wa, Z_to_bv_unsigned, bv_wrap, h1]
  omega

/-! ## Bytes -/

private theorem le_bytes_length (n : Nat) (z : Int) : (Z_to_le_bytes n z).length = n :=
  length_Z_to_le_bytes n z

private theorem Z_to_bv8_mod (z : Int) : Z_to_bv 8 (z % 256) = Z_to_bv 8 z := by
  apply bv_eq_of_unsigned
  simp only [Z_to_bv_unsigned, bv_wrap]
  omega

private theorem shiftr8 (z : Int) : z >>> (8 : Nat) = z / 256 := by
  rw [Int.shiftRight_eq_div_pow]
  omega

/-- `splatZ k c` is the `k`-byte little-endian word whose every byte is `c`. -/
private def splatZ : Nat → Int → Int
  | 0, _ => 0
  | k + 1, c => c + 256 * splatZ k c

private theorem splatZ_nonneg (k : Nat) (c : Int) (h : 0 ≤ c) : 0 ≤ splatZ k c := by
  induction k with
  | zero => exact Int.le_refl 0
  | succ k ih => simp only [splatZ]; omega

private theorem le_bytes_splat (k : Nat) (c : Int) (h0 : 0 ≤ c) (h1 : c < 256) :
    Z_to_le_bytes k (splatZ k c) = List.replicate k (Z_to_bv 8 c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hs : 0 ≤ splatZ k c := splatZ_nonneg k c h0
    have hval : splatZ (k + 1) c = c + 256 * splatZ k c := rfl
    show Z_to_bv 8 (splatZ (k + 1) c) :: Z_to_le_bytes k (splatZ (k + 1) c >>> (8 : Nat))
      = _
    rw [hval, shiftr8,
      show (c + 256 * splatZ k c) / 256 = splatZ k c by omega,
      show Z_to_bv 8 (c + 256 * splatZ k c) = Z_to_bv 8 c by
        rw [← Z_to_bv8_mod (c + 256 * splatZ k c), ← Z_to_bv8_mod c]
        congr 1
        omega,
      ih, List.replicate_succ]

private theorem splat1 (c : Int) : splatZ 1 c = c := by simp only [splatZ]; omega
private theorem splat4 (c : Int) : splatZ 4 c = c * 0x01010101 := by simp only [splatZ]; omega
private theorem splat8 (c : Int) : splatZ 8 c = c * 0x0101010101010101 := by
  simp only [splatZ]; omega

private theorem word_bytes_splat (k : Nat) (v : word) (c : Int) (h0 : 0 ≤ c) (h1 : c < 256)
    (hv : bv_unsigned v = splatZ k c) :
    word_to_le_bytes k v = List.replicate k (Z_to_bv 8 c) := by
  unfold word_to_le_bytes
  rw [hv]
  exact le_bytes_splat k c h0 h1

/-- The byte a `sb` leaves: `step_sb_at` spells it `Z_to_bv 8 (bv_unsigned v)`,
the contract spells the same byte `Z_to_bv 8 (bv_unsigned v % 256)`. -/
private theorem word_bytes_one (v : word) :
    word_to_le_bytes 1 v = List.replicate 1 (Z_to_bv 8 (bv_unsigned v % 256)) := by
  show [Z_to_bv 8 (bv_unsigned v)] = _
  rw [Z_to_bv8_mod]
  rfl

/-! ## `wbytes` -/

private theorem wbytes_out (bs : List byte) (m : word → Option byte) (base : Int) (x : word)
    (hb : 0 ≤ base) (hnw : base + (bs.length : Int) ≤ 2 ^ 64)
    (hx : bv_unsigned x < base ∨ base + (bs.length : Int) ≤ bv_unsigned x) :
    wbytes m (wa base) bs x = m x := by
  match bs with
  | [] => rfl
  | b :: rest =>
    have hlen : (0 : Int) < ((b :: rest).length : Int) := by
      simp only [List.length_cons]; omega
    have hbase : bv_unsigned (wa base) = base := wa_unsigned base hb (by omega)
    rcases hx with hx | hx
    · exact wbytes_below (b :: rest) m (wa base) x (by rw [hbase]; omega)
        (by rw [hbase]; omega)
    · exact wbytes_above (b :: rest) m (wa base) x (by rw [hbase]; omega)

private theorem wbytes_get (bs : List byte) (m : word → Option byte) (base : Int) (j : Nat)
    (hb : 0 ≤ base) (hnw : base + (bs.length : Int) ≤ 2 ^ 64) (hj : j < bs.length) :
    wbytes m (wa base) bs (wa (base + (j : Int))) = bs[j]? := by
  induction bs generalizing m base j with
  | nil => simp only [List.length_nil] at hj; omega
  | cons b rest ih =>
    have hlen : ((b :: rest).length : Int) = (rest.length : Int) + 1 := by
      simp only [List.length_cons]; omega
    rw [hlen] at hnw
    match j with
    | 0 =>
      have h0 : base + ((0 : Nat) : Int) = base := by omega
      rw [h0]
      show wbytes (fun a => if bv_eqb a (wa base) then some b else m a) (wa base + 1) rest
          (wa base) = _
      rw [wa_succ,
        wbytes_out rest _ (base + 1) (wa base) (by omega) (by omega)
          (by rw [wa_unsigned base hb (by omega)]; left; omega)]
      simp [bv_eqb]
    | j' + 1 =>
      have hj' : j' < rest.length := by simp only [List.length_cons] at hj; omega
      have hstep : base + ((j' + 1 : Nat) : Int) = (base + 1) + (j' : Int) := by omega
      show wbytes (fun a => if bv_eqb a (wa base) then some b else m a) (wa base + 1) rest
          (wa (base + ((j' + 1 : Nat) : Int))) = _
      rw [wa_succ, hstep,
        ih (fun a => if bv_eqb a (wa base) then some b else m a) (base + 1) j'
          (by omega) (by omega) hj']
      simp only [List.getElem?_cons_succ]

/-! ## `store_ok` and `mem_inv` -/

private theorem store_ok_of_wview (segs : List Segment) (m : word → Option byte) (base : Int)
    (k : Nat)
    (h : ∀ i : Int, 0 ≤ i → i < (k : Int) → wview segs m (wa (base + i)) ≠ none) :
    store_ok segs m (wa base) k = true := by
  induction k generalizing base with
  | zero => rfl
  | succ k ih =>
    have h0 : wview segs m (wa base) ≠ none := by
      have hh := h 0 (Int.le_refl 0) (by omega)
      rwa [Int.add_zero] at hh
    show (match wview segs m (wa base) with
          | some _ => store_ok segs m (wa base + 1) k
          | none => false) = true
    cases hv : wview segs m (wa base) with
    | none => exact absurd hv h0
    | some b =>
      simp only
      rw [wa_succ]
      refine ih (base + 1) ?_
      intro i hi hik
      have hh := h (1 + i) (by omega) (by omega)
      rwa [show base + (1 + i) = base + 1 + i by omega] at hh

private theorem ro_false_of_wview (segs : List Segment) (m : word → Option byte) (x : word)
    (hmi : mem_inv segs m) (h : wview segs m x ≠ none) : ro_addr segs x = false := by
  cases hm : m x with
  | some b => exact hmi x b hm
  | none =>
    unfold ro_addr
    cases hf : find_segment segs (bv_unsigned x) 1 with
    | none => rfl
    | some seg =>
      cases hws : seg_writable seg with
      | true => simp [hws]
      | false =>
        exact absurd
          (by simp only [wview, hm, hf, hws, Bool.false_eq_true, ite_false]) h

private theorem mem_inv_wbytes (segs : List Segment) (m : word → Option byte) (a : word)
    (bs : List byte) (hmi : mem_inv segs m) (hok : store_ok segs m a bs.length = true) :
    mem_inv segs (wbytes m a bs) := by
  induction bs generalizing m a with
  | nil => exact hmi
  | cons b rest ih =>
    have hok' : (match wview segs m a with
                 | some _ => store_ok segs m (a + 1) rest.length
                 | none => false) = true := hok
    cases hv : wview segs m a with
    | none => rw [hv] at hok'; exact absurd hok' (by simp)
    | some bb =>
      rw [hv] at hok'
      simp only at hok'
      have hro : ro_addr segs a = false :=
        ro_false_of_wview segs m a hmi (by rw [hv]; simp)
      have hmi' : mem_inv segs (fun y => if bv_eqb y a then some b else m y) := by
        intro y bz hy
        by_cases hya : y = a
        · rw [hya]; exact hro
        · have hfa : bv_eqb y a = false := by simp [bv_eqb, hya]
          simp only [hfa, Bool.false_eq_true, ite_false] at hy
          exact hmi y bz hy
      have hgrow : mem_grows m (fun y => if bv_eqb y a then some b else m y) := by
        intro y hy
        by_cases hya : y = a
        · subst hya; simp [bv_eqb]
        · have hfa : bv_eqb y a = false := by simp [bv_eqb, hya]
          simpa [hfa] using hy
      exact ih (fun y => if bv_eqb y a then some b else m y) (a + 1) hmi'
        (store_ok_mono segs rest.length m _ (a + 1) hgrow hok')

private theorem wview_wbytes_grows (segs : List Segment) (m : word → Option byte) (a : word)
    (bs : List byte) (x : word) (h : wview segs m x ≠ none) :
    wview segs (wbytes m a bs) x ≠ none :=
  wview_grows segs m (wbytes m a bs) x (wbytes_grows bs m a) h

/-! ## The invariant -/

private structure Fill (segs : List Segment) (A n : Int) (c : byte)
    (m0 m1 : word → Option byte) (Q : Int → Prop) : Prop where
  dom : ∀ j : Int, Q j → 0 ≤ j ∧ j < n
  fill : ∀ j : Int, Q j → mrd segs m1 (wa (A + j)) = some c
  wr : wr_at segs m1 A n
  mi : mem_inv segs m1
  mu : munch [(A, A + n)] m0 m1
  wm : wmono segs m0 m1

private theorem Fill.init (segs : List Segment) (A n : Int) (c : byte) (m : word → Option byte)
    (hwr : wr_at segs m A n) (hmi : mem_inv segs m) :
    Fill segs A n c m m (fun _ => False) where
  dom := fun _ h => absurd h not_false
  fill := fun _ h => absurd h not_false
  wr := hwr
  mi := hmi
  mu := munch_refl _ m
  wm := wmono_refl segs m

private theorem Fill.ok {segs : List Segment} {A n : Int} {c : byte} {m0 m1 : word → Option byte}
    {Q : Int → Prop} (h : Fill segs A n c m0 m1 Q) (p : Int) (k : Nat)
    (hp : 0 ≤ p) (hpk : p + (k : Int) ≤ n) :
    store_ok segs m1 (wa (A + p)) k = true := by
  refine store_ok_of_wview segs m1 (A + p) k ?_
  intro i hi hik
  have h2 := h.wr.2.2 (p + i) (by omega) (by omega)
  rwa [show A + (p + i) = A + p + i by omega] at h2

private theorem Fill.store {segs : List Segment} {A n : Int} {c : byte}
    {m0 m1 : word → Option byte} {Q : Int → Prop} (h : Fill segs A n c m0 m1 Q)
    (p : Int) (k : Nat) (v : word)
    (hp : 0 ≤ p) (hpk : p + (k : Int) ≤ n)
    (hv : word_to_le_bytes k v = List.replicate k c) :
    Fill segs A n c m0 (wbytes m1 (wa (A + p)) (word_to_le_bytes k v))
      (fun j => Q j ∨ (p ≤ j ∧ j < p + (k : Int))) := by
  have hA : 0 ≤ A := h.wr.1
  have hAn : A + n ≤ 2 ^ 64 := h.wr.2.1
  have hlen : (word_to_le_bytes k v).length = k := le_bytes_length k (bv_unsigned v)
  have hk0 : (0 : Int) ≤ (k : Int) := by omega
  have hok : store_ok segs m1 (wa (A + p)) (word_to_le_bytes k v).length = true := by
    rw [hlen]; exact h.ok p k hp hpk
  refine ⟨?dom, ?fill, ?wr, ?mi, ?mu, ?wm⟩
  case dom =>
    rintro j (hj | ⟨hj1, hj2⟩)
    · exact h.dom j hj
    · omega
  case fill =>
    intro j hj
    by_cases hin : p ≤ j ∧ j < p + (k : Int)
    · have hjd : ((j - p).toNat : Int) = j - p := Int.toNat_of_nonneg (by omega)
      have hidx : (j - p).toNat < (word_to_le_bytes k v).length := by
        rw [hlen]; omega
      have hget := wbytes_get (word_to_le_bytes k v) m1 (A + p) (j - p).toNat
        (by omega) (by rw [hlen]; omega) hidx
      rw [show A + p + ((j - p).toNat : Int) = A + j by omega] at hget
      have hval : (word_to_le_bytes k v)[(j - p).toNat]? = some c := by
        rw [hv, List.getElem?_replicate]
        rw [hlen] at hidx
        simp only [hidx, ite_true]
      unfold mrd
      rw [hget, hval]
    · have hjQ : Q j := by rcases hj with hj | hj; exact hj; exact absurd hj hin
      have hdom := h.dom j hjQ
      have hx : bv_unsigned (wa (A + j)) = A + j :=
        wa_unsigned (A + j) (by omega) (by omega)
      have hout := wbytes_out (word_to_le_bytes k v) m1 (A + p) (wa (A + j))
        (by omega) (by rw [hlen]; omega) (by rw [hx, hlen]; omega)
      unfold mrd
      rw [hout]
      have hf := h.fill j hjQ
      unfold mrd at hf
      exact hf
  case wr =>
    exact ⟨h.wr.1, h.wr.2.1, fun i hi hin =>
      wview_wbytes_grows segs m1 (wa (A + p)) (word_to_le_bytes k v) _ (h.wr.2.2 i hi hin)⟩
  case mi => exact mem_inv_wbytes segs m1 (wa (A + p)) (word_to_le_bytes k v) h.mi hok
  case mu =>
    intro x hx
    have hx1 : bv_unsigned x < A ∨ A + n ≤ bv_unsigned x := hx.1
    rw [wbytes_out (word_to_le_bytes k v) m1 (A + p) x (by omega) (by rw [hlen]; omega)
      (by rw [hlen]; omega)]
    exact h.mu x hx
  case wm => exact fun x hx => wview_wbytes_grows segs m1 _ _ x (h.wm x hx)

private theorem Fill.finish {segs : List Segment} {A n : Int} {c : byte}
    {m0 m1 : word → Option byte} {Q : Int → Prop} (h : Fill segs A n c m0 m1 Q)
    (hn : 0 ≤ n) (hcov : ∀ j : Int, 0 ≤ j → j < n → Q j) :
    rw_cells segs m1 A [.CB n.toNat (List.replicate n.toNat c)] := by
  have hnt : (n.toNat : Int) = n := Int.toNat_of_nonneg hn
  have hA : 0 ≤ A := h.wr.1
  have hAn : A + n ≤ 2 ^ 64 := h.wr.2.1
  have hbs : cells_bytes [(.CB n.toNat (List.replicate n.toNat c) : cell)]
      = List.replicate n.toNat c := by simp [cells_bytes, cbytes]
  have hcs : cells_size [(.CB n.toNat (List.replicate n.toNat c) : cell)] = n.toNat := by
    simp [cells_size, csize]
  refine ⟨⟨⟨hA, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [hbs, List.length_replicate]; omega
  · intro i hi
    rw [hbs] at hi ⊢
    rw [List.length_replicate] at hi
    rw [List.getElem?_replicate]
    simp only [hi, ite_true]
    exact h.fill (i : Int) (hcov (i : Int) (by omega) (by omega))
  · exact ⟨List.length_replicate, trivial⟩
  · rw [hcs, hnt]
    exact h.wr





/-! ## Helpers

The bit-level facts the `memset` walk needs that the model does not state. -/

/-- Helper: `Z_shiftl` at a non-negative literal amount, the `slli` arm. -/
private theorem Z_shiftl_cast (a : Int) (k : Nat) : Z_shiftl a (k : Int) = a * 2 ^ k :=
  Int.shiftLeft_eq a k

/-- Helper: `Z_shiftl` at a negative amount, the `srli`/`mulhu` arm. -/
private theorem Z_shiftl_neg (a : Int) (k : Nat) : Z_shiftl a (-(k : Int)) = a / 2 ^ k := by
  cases k with
  | zero =>
    show a <<< (0 : Nat) = a / 2 ^ 0
    rw [Int.shiftLeft_eq]
    omega
  | succ m =>
    show a >>> (m + 1) = a / 2 ^ (m + 1)
    rw [Int.shiftRight_eq_div_pow]
    simp only [Int.natCast_pow, Int.cast_ofNat_Int]

/-- Helper: `0x1acc8 slli a2, a2, 32`'s shift amount, as a literal. -/
private theorem Z_shiftl_32 (a : Int) : Z_shiftl a 32 = a * 2 ^ 32 :=
  Int.shiftLeft_eq a 32

/-- Helper: `0x1ac48 slli a6, a1, 56`'s shift amount, as a literal. -/
private theorem Z_shiftl_56 (a : Int) : Z_shiftl a 56 = a * 2 ^ 56 :=
  Int.shiftLeft_eq a 56

/-- Helper: `0x1acd0 srli a3, a2, 32`'s shift amount, as a literal. -/
private theorem Z_shiftr_32 (a : Int) : Z_shiftl a (-32) = a / 2 ^ 32 :=
  Z_shiftl_neg a 32

/-- Helper: the `-64` of `mulhu`'s high half, as a literal. -/
private theorem Z_shiftr_64 (a : Int) : Z_shiftl a (-64) = a / 2 ^ 64 :=
  Z_shiftl_neg a 64

/-- Helper: `Z_land` against the two-bit mask, for `0x1ac50 andi a3, a3, 3`. -/
private theorem Z_land_3 (y : Int) : Z_land y 3 = y % 4 := by
  have e3 : (2 : Nat) ^ 2 - 1 = 3 := by decide
  have e4 : (2 : Nat) ^ 2 = 4 := by decide
  cases y with
  | ofNat y =>
    have h : y &&& 3 = y % 4 := by
      have hh := Nat.and_two_pow_sub_one_eq_mod y 2
      rw [e3, e4] at hh
      exact hh
    show Int.ofNat (y &&& 3) = Int.ofNat y % 4
    rw [h, Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]
    omega
  | negSucc y =>
    have h : 3 &&& y = y % 4 := by
      rw [Nat.and_comm]
      have hh := Nat.and_two_pow_sub_one_eq_mod y 2
      rw [e3, e4] at hh
      exact hh
    show Int.ofNat (3 - (3 &&& y)) = Int.negSucc y % 4
    rw [h, Int.negSucc_eq, Int.ofNat_eq_natCast]
    omega

/-- Helper: the single bit 2 of a value below 8, for `0x1aca4 andi a5, a1, 4`. -/
private theorem nat_land_small4 (r : Nat) (hr : r < 8) : r &&& 4 = r - r % 4 := by
  have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Helper: bit 2 of any natural number, for `0x1aca4 andi a5, a1, 4`. -/
private theorem nat_land_4 (n : Nat) : n &&& 4 = n % 8 - n % 4 := by
  have e7 : (2 : Nat) ^ 3 - 1 = 7 := by decide
  have e8 : (2 : Nat) ^ 3 = 8 := by decide
  have h7 : n &&& 7 = n % 8 := by
    have hh := Nat.and_two_pow_sub_one_eq_mod n 3
    rw [e7, e8] at hh
    exact hh
  have hassoc : n &&& 7 &&& 4 = n &&& 4 := by
    rw [Nat.and_assoc, show (7 : Nat) &&& 4 = 4 from by decide]
  rw [← hassoc, h7, nat_land_small4 (n % 8) (by omega)]
  omega

/-- Helper: the 64-bit mask `2^64 - 4` clears bits 0 and 1, for
`0x1ac64 andi a4, a2, -4`. -/
private theorem nat_land_m4_64 (p : Nat) (hp : p < 2 ^ 64) :
    p &&& (2 ^ 64 - 4) = p - p % 4 := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h1 : 2 ^ 64 - 4 = 2 ^ 2 * (2 ^ 62 - 1) + 0 := by decide
  have h2 : p - p % 4 = 2 ^ 2 * (p / 4) + 0 := by omega
  have h4 : p.testBit j = (2 ^ 2 * (p / 4) + p % 4).testBit j := by
    rw [← (by omega : p = 2 ^ 2 * (p / 4) + p % 4)]
  rw [Nat.testBit_and, h1, h2, h4,
    Nat.testBit_two_pow_mul_add _ (by omega : p % 4 < 2 ^ 2) j,
    Nat.testBit_two_pow_mul_add _ (by decide : 0 < 2 ^ 2) j,
    Nat.testBit_two_pow_mul_add _ (by decide : 0 < 2 ^ 2) j]
  by_cases hj : j < 2
  · simp only [hj, ↓reduceIte, Nat.zero_testBit, Bool.and_false]
  · simp only [hj, ↓reduceIte, Nat.testBit_two_pow_sub_one]
    by_cases hk : j - 2 < 62
    · simp only [hk, decide_true, Bool.and_true]
    · have h62 : p / 4 < 2 ^ 62 := by omega
      have hlt : p / 4 < 2 ^ (j - 2) :=
        Nat.lt_of_lt_of_le h62 (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow hlt, Bool.false_and]

/-- Helper: `Z_lor` of disjoint halves is addition, for
`0x1acd4 or a2, a2, a3`. -/
private theorem Z_lor_split32 (q b : Int) (hq : 0 ≤ q) (hb : 0 ≤ b) (hb2 : b < 2 ^ 32) :
    Z_lor (2 ^ 32 * q) b = 2 ^ 32 * q + b := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  have hs : s < 2 ^ 32 := by omega
  have hcast : (2 : Int) ^ 32 * (p : Int) = ((2 ^ 32 * p : Nat) : Int) := by
    simp only [Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int]
  rw [hcast]
  show Int.ofNat (2 ^ 32 * p ||| s) = _
  rw [← Nat.two_pow_add_eq_or_of_lt hs p, Int.ofNat_eq_natCast]
  omega

/-- Helper: `z % 2 ^ 64` is idempotent, used to move a `wa` through a shift. -/
private theorem mod64_mod64 (z : Int) : z % 2 ^ 64 % 2 ^ 64 = z % 2 ^ 64 := by
  omega

/-! ## The bridges the walk calls -/

/-- `v_sub` on two in-range addresses. -/
private theorem v_sub_wa (x y : Int) : v_sub (wa x) (wa y) = wa (x - y) := by
  apply bv_eq_of_unsigned
  simp only [v_sub, wa, Z_to_bv_unsigned, bv_wrap]
  omega

/-- `slli` by a literal shift. -/
private theorem v_slli_wa (x s : Int) (hs : 0 ≤ s) (hs6 : s < 64) :
    v_slli (wa x) s = wa (x * 2 ^ s.toNat) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hs
  have htn : ((k : Nat) : Int).toNat = k := rfl
  rw [htn]
  apply bv_eq_of_unsigned
  simp only [v_slli, wa, Z_to_bv_unsigned, bv_wrap, Z_shiftl_cast]
  rw [Int.mul_emod, mod64_mod64, ← Int.mul_emod]

/-- `srli` by a literal shift, on an in-range value. -/
private theorem v_srli_wa (x s : Int) (hx : 0 ≤ x) (hx2 : x < 2 ^ 64) (hs : 0 ≤ s)
    (hs6 : s < 64) : v_srli (wa x) s = wa (x / 2 ^ s.toNat) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hs
  have htn : ((k : Nat) : Int).toNat = k := rfl
  rw [htn]
  apply bv_eq_of_unsigned
  simp only [v_srli, wa, Z_to_bv_unsigned, bv_wrap, Z_shiftl_neg]
  rw [show x % 2 ^ 64 = x from by omega]

/-- The `beq` test on two in-range values. -/
private theorem beq_wa (x y : Int) (hx : 0 ≤ x) (hx2 : x < 2 ^ 64) (hy : 0 ≤ y)
    (hy2 : y < 2 ^ 64) :
    branch_taken branch_cond.BC_EQ (wa x) (wa y) = decide (x = y) := by
  show bv_eqb (wa x) (wa y) = decide (x = y)
  by_cases hxy : x = y
  · subst hxy
    rw [(bv_eqb_eq (wa x) (wa x)).2 rfl, decide_eq_true rfl]
  · rw [bv_eqb_neq _ _ ?ne, decide_eq_false hxy]
    case ne =>
      intro h
      apply hxy
      rw [← wa_unsigned x hx hx2, ← wa_unsigned y hy hy2, h]

set_option linter.unusedVariables false in
/-- `0x1ac44 subw a3, x0, a0` then `0x1ac50 andi a3, a3, 3`: the alignment
slack `k` of the destination. The Rocq twin is `R_memset.v:255-261`. -/
private theorem k_val (A : Int) (hA : 0 ≤ A) (hA2 : A < 2 ^ 64) :
    ∃ k : Int, 0 ≤ k ∧ k ≤ 3 ∧ (A + k) % 4 = 0 ∧
      v_andi (v_subw (Z_to_bv 64 0) (wa A)) 3 = wa k := by
  refine ⟨(4 - A % 4) % 4, by omega, by omega, by omega, ?_⟩
  have hmask : bv_wrap 64 3 = 3 := by simp only [bv_wrap]; omega
  apply bv_eq_of_unsigned
  rw [v_andi, hmask, Z_to_bv_unsigned, Z_land_3]
  simp only [v_subw, wa, Z_to_bv_unsigned, bv_wrap, bv_swrap, bv_half_modulus, bv_modulus]
  omega

/-- `0x1ac64 andi a4, a2, -4`: rounding the remaining length down to a
multiple of 4. The Rocq twin is `R_memset.v:263-267`. -/
private theorem n4_val (x : Int) (hx : 0 ≤ x) (hx2 : x < 2 ^ 64) :
    v_andi (wa x) (-4) = wa (x - x % 4) := by
  have hmask : bv_wrap 64 (-4) = ((2 ^ 64 - 4 : Nat) : Int) := by decide
  obtain ⟨p, rfl⟩ : ∃ p : Nat, x = (p : Int) := ⟨x.toNat, (Int.toNat_of_nonneg hx).symm⟩
  apply bv_eq_of_unsigned
  rw [v_andi, hmask, Z_to_bv_unsigned, wa_unsigned _ hx hx2,
    show Z_land ((p : Nat) : Int) ((2 ^ 64 - 4 : Nat) : Int)
        = ((p &&& (2 ^ 64 - 4) : Nat) : Int) from rfl,
    nat_land_m4_64 p (by omega)]
  simp only [wa, Z_to_bv_unsigned, bv_wrap]
  omega

/-- `0x1aca4 andi a5, a1, 4` at a 4-aligned address. The Rocq twin is
`R_memset.v:139-147` (`land4_of_aligned`) and `:285-288`. -/
private theorem k4_val (y : Int) (hy : 0 ≤ y) (hy2 : y < 2 ^ 64) (h4 : y % 4 = 0) :
    ∃ k4 : Int, (k4 = 0 ∨ k4 = 4) ∧ (y + k4 + 24) % 8 = 0 ∧
      v_andi (wa y) 4 = wa k4 := by
  refine ⟨y % 8, by omega, by omega, ?_⟩
  have hmask : bv_wrap 64 4 = 4 := by simp only [bv_wrap]; omega
  obtain ⟨p, rfl⟩ : ∃ p : Nat, y = (p : Int) := ⟨y.toNat, (Int.toNat_of_nonneg hy).symm⟩
  apply bv_eq_of_unsigned
  rw [v_andi, hmask, Z_to_bv_unsigned, wa_unsigned _ hy hy2,
    show Z_land ((p : Nat) : Int) (4 : Int) = ((p &&& 4 : Nat) : Int) from rfl,
    nat_land_4 p]
  simp only [wa, Z_to_bv_unsigned, bv_wrap]
  omega

/-- `0x1ac48 slli a6, a1, 56` and `0x1ac68 mulhu a2, a6, a3`: musl's way of
splatting the byte over 4 bytes. The Rocq twin is `R_memset.v:268`
(`brute256_ok` on `BC4`). -/
private theorem mulhu_splat (v : word) :
    v_mulhu (v_slli v 56) (wa 0x101010100) = wa (splatZ 4 (bv_unsigned v % 256)) := by
  have hv := u64_range v
  have hsl : bv_unsigned (v_slli v 56) = bv_unsigned v % 256 * 2 ^ 56 := by
    simp only [v_slli, Z_to_bv_unsigned, bv_wrap, Z_shiftl_56]
    omega
  apply bv_eq_of_unsigned
  simp only [v_mulhu, Z_to_bv_unsigned, bv_wrap, hsl, Z_shiftr_64, wa, splat4]
  omega

/-- `0x1acc8 slli a2, a2, 32`, `0x1acd0 srli a3, a2, 32`, `0x1acd4 or a2, a2, a3`:
the splat from 4 bytes to 8. The Rocq twin is `R_memset.v:296` (`BC8`). -/
private theorem splat8_or (c : Int) (h0 : 0 ≤ c) (h1 : c < 256) :
    v_or (v_slli (wa (splatZ 4 c)) 32) (v_srli (v_slli (wa (splatZ 4 c)) 32) 32)
      = wa (splatZ 8 c) := by
  have hA : bv_unsigned (v_slli (wa (splatZ 4 c)) 32) = 2 ^ 32 * (c * 0x01010101) := by
    simp only [v_slli, wa, Z_to_bv_unsigned, bv_wrap, Z_shiftl_32, splat4]
    omega
  have hB : bv_unsigned (v_srli (v_slli (wa (splatZ 4 c)) 32) 32) = c * 0x01010101 := by
    simp only [v_srli, Z_to_bv_unsigned, bv_wrap, Z_shiftr_32, hA]
    omega
  apply bv_eq_of_unsigned
  simp only [v_or, Z_to_bv_unsigned, bv_wrap, hA, hB]
  rw [Z_lor_split32 (c * 0x01010101) (c * 0x01010101) (by omega) (by omega) (by omega)]
  simp only [wa, Z_to_bv_unsigned, bv_wrap, splat8]
  omega






/-- The 62 instruction words of `memset`, as `Image/PlainCode.lean` certifies
them: one field per `F_<pc>` and per `D_<pc>`. The walk is proved against this
structure, so it does not have to elaborate the image. -/
private structure Code (segs : List Segment) : Prop where
  f_1ac04 : fetch_word segs (wa 0x1ac04) = some 0x0e060a63
  d_1ac04 : decode_any 0x0e060a63 = some (.Branch .BC_EQ 12 0 0xf4, 4)
  f_1ac08 : fetch_word segs (wa 0x1ac08) = some 0x00b50023
  d_1ac08 : decode_any 0x00b50023 = some (.Store .SZ1 10 11 0x0, 4)
  f_1ac0c : fetch_word segs (wa 0x1ac0c) = some 0x00c506b3
  d_1ac0c : decode_any 0x00c506b3 = some (.Op .ALU_ADD 13 10 12, 4)
  f_1ac10 : fetch_word segs (wa 0x1ac10) = some 0x00300713
  d_1ac10 : decode_any 0x00300713 = some (.OpImm .ALU_ADD 14 0 0x3, 4)
  f_1ac14 : fetch_word segs (wa 0x1ac14) = some 0xfeb68fa3
  d_1ac14 : decode_any 0xfeb68fa3 = some (.Store .SZ1 13 11 0xfff, 4)
  f_1ac18 : fetch_word segs (wa 0x1ac18) = some 0x0ee66063
  d_1ac18 : decode_any 0x0ee66063 = some (.Branch .BC_LTU 12 14 0xe0, 4)
  f_1ac1c : fetch_word segs (wa 0x1ac1c) = some 0x00b500a3
  d_1ac1c : decode_any 0x00b500a3 = some (.Store .SZ1 10 11 0x1, 4)
  f_1ac20 : fetch_word segs (wa 0x1ac20) = some 0x00b50123
  d_1ac20 : decode_any 0x00b50123 = some (.Store .SZ1 10 11 0x2, 4)
  f_1ac24 : fetch_word segs (wa 0x1ac24) = some 0x00700713
  d_1ac24 : decode_any 0x00700713 = some (.OpImm .ALU_ADD 14 0 0x7, 4)
  f_1ac28 : fetch_word segs (wa 0x1ac28) = some 0xfeb68ea3
  d_1ac28 : decode_any 0xfeb68ea3 = some (.Store .SZ1 13 11 0xffd, 4)
  f_1ac2c : fetch_word segs (wa 0x1ac2c) = some 0xfeb68f23
  d_1ac2c : decode_any 0xfeb68f23 = some (.Store .SZ1 13 11 0xffe, 4)
  f_1ac30 : fetch_word segs (wa 0x1ac30) = some 0x0ce66463
  d_1ac30 : decode_any 0x0ce66463 = some (.Branch .BC_LTU 12 14 0xc8, 4)
  f_1ac34 : fetch_word segs (wa 0x1ac34) = some 0x00b501a3
  d_1ac34 : decode_any 0x00b501a3 = some (.Store .SZ1 10 11 0x3, 4)
  f_1ac38 : fetch_word segs (wa 0x1ac38) = some 0x00900793
  d_1ac38 : decode_any 0x00900793 = some (.OpImm .ALU_ADD 15 0 0x9, 4)
  f_1ac3c : fetch_word segs (wa 0x1ac3c) = some 0xfeb68e23
  d_1ac3c : decode_any 0xfeb68e23 = some (.Store .SZ1 13 11 0xffc, 4)
  f_1ac40 : fetch_word segs (wa 0x1ac40) = some 0x0af66c63
  d_1ac40 : decode_any 0x0af66c63 = some (.Branch .BC_LTU 12 15 0xb8, 4)
  f_1ac44 : fetch_word segs (wa 0x1ac44) = some 0x40a006bb
  d_1ac44 : decode_any 0x40a006bb = some (.Op32 .ALU_SUB 13 0 10, 4)
  f_1ac48 : fetch_word segs (wa 0x1ac48) = some 0x03859813
  d_1ac48 : decode_any 0x03859813 = some (.ShiftImm .ALU_SLL 16 11 56, 4)
  f_1ac4c : fetch_word segs (wa 0x1ac4c) = some 0x101015b7
  d_1ac4c : decode_any 0x101015b7 = some (.Lui 11 0x10101, 4)
  f_1ac50 : fetch_word segs (wa 0x1ac50) = some 0x0036f693
  d_1ac50 : decode_any 0x0036f693 = some (.OpImm .ALU_AND 13 13 0x3, 4)
  f_1ac54 : fetch_word segs (wa 0x1ac54) = some 0x00459713
  d_1ac54 : decode_any 0x00459713 = some (.ShiftImm .ALU_SLL 14 11 4, 4)
  f_1ac58 : fetch_word segs (wa 0x1ac58) = some 0x40d60633
  d_1ac58 : decode_any 0x40d60633 = some (.Op .ALU_SUB 12 12 13, 4)
  f_1ac5c : fetch_word segs (wa 0x1ac5c) = some 0x00d505b3
  d_1ac5c : decode_any 0x00d505b3 = some (.Op .ALU_ADD 11 10 13, 4)
  f_1ac60 : fetch_word segs (wa 0x1ac60) = some 0x10070693
  d_1ac60 : decode_any 0x10070693 = some (.OpImm .ALU_ADD 13 14 0x100, 4)
  f_1ac64 : fetch_word segs (wa 0x1ac64) = some 0xffc67713
  d_1ac64 : decode_any 0xffc67713 = some (.OpImm .ALU_AND 14 12 0xffc, 4)
  f_1ac68 : fetch_word segs (wa 0x1ac68) = some 0x02d83633
  d_1ac68 : decode_any 0x02d83633 = some (.Mul .M_MULHU 12 16 13, 4)
  f_1ac6c : fetch_word segs (wa 0x1ac6c) = some 0x00c5a023
  d_1ac6c : decode_any 0x00c5a023 = some (.Store .SZ4 11 12 0x0, 4)
  f_1ac70 : fetch_word segs (wa 0x1ac70) = some 0x00e586b3
  d_1ac70 : decode_any 0x00e586b3 = some (.Op .ALU_ADD 13 11 14, 4)
  f_1ac74 : fetch_word segs (wa 0x1ac74) = some 0xfec6ae23
  d_1ac74 : decode_any 0xfec6ae23 = some (.Store .SZ4 13 12 0xffc, 4)
  f_1ac78 : fetch_word segs (wa 0x1ac78) = some 0x08f76063
  d_1ac78 : decode_any 0x08f76063 = some (.Branch .BC_LTU 14 15 0x80, 4)
  f_1ac7c : fetch_word segs (wa 0x1ac7c) = some 0x00c5a223
  d_1ac7c : decode_any 0x00c5a223 = some (.Store .SZ4 11 12 0x4, 4)
  f_1ac80 : fetch_word segs (wa 0x1ac80) = some 0x00c5a423
  d_1ac80 : decode_any 0x00c5a423 = some (.Store .SZ4 11 12 0x8, 4)
  f_1ac84 : fetch_word segs (wa 0x1ac84) = some 0x01900793
  d_1ac84 : decode_any 0x01900793 = some (.OpImm .ALU_ADD 15 0 0x19, 4)
  f_1ac88 : fetch_word segs (wa 0x1ac88) = some 0xfec6aa23
  d_1ac88 : decode_any 0xfec6aa23 = some (.Store .SZ4 13 12 0xff4, 4)
  f_1ac8c : fetch_word segs (wa 0x1ac8c) = some 0xfec6ac23
  d_1ac8c : decode_any 0xfec6ac23 = some (.Store .SZ4 13 12 0xff8, 4)
  f_1ac90 : fetch_word segs (wa 0x1ac90) = some 0x06f76463
  d_1ac90 : decode_any 0x06f76463 = some (.Branch .BC_LTU 14 15 0x68, 4)
  f_1ac94 : fetch_word segs (wa 0x1ac94) = some 0x00c5a623
  d_1ac94 : decode_any 0x00c5a623 = some (.Store .SZ4 11 12 0xc, 4)
  f_1ac98 : fetch_word segs (wa 0x1ac98) = some 0x00c5a823
  d_1ac98 : decode_any 0x00c5a823 = some (.Store .SZ4 11 12 0x10, 4)
  f_1ac9c : fetch_word segs (wa 0x1ac9c) = some 0x00c5aa23
  d_1ac9c : decode_any 0x00c5aa23 = some (.Store .SZ4 11 12 0x14, 4)
  f_1aca0 : fetch_word segs (wa 0x1aca0) = some 0x00c5ac23
  d_1aca0 : decode_any 0x00c5ac23 = some (.Store .SZ4 11 12 0x18, 4)
  f_1aca4 : fetch_word segs (wa 0x1aca4) = some 0x0045f793
  d_1aca4 : decode_any 0x0045f793 = some (.OpImm .ALU_AND 15 11 0x4, 4)
  f_1aca8 : fetch_word segs (wa 0x1aca8) = some 0x02000813
  d_1aca8 : decode_any 0x02000813 = some (.OpImm .ALU_ADD 16 0 0x20, 4)
  f_1acac : fetch_word segs (wa 0x1acac) = some 0x01878793
  d_1acac : decode_any 0x01878793 = some (.OpImm .ALU_ADD 15 15 0x18, 4)
  f_1acb0 : fetch_word segs (wa 0x1acb0) = some 0x40f70733
  d_1acb0 : decode_any 0x40f70733 = some (.Op .ALU_SUB 14 14 15, 4)
  f_1acb4 : fetch_word segs (wa 0x1acb4) = some 0xfec6a223
  d_1acb4 : decode_any 0xfec6a223 = some (.Store .SZ4 13 12 0xfe4, 4)
  f_1acb8 : fetch_word segs (wa 0x1acb8) = some 0xfec6a423
  d_1acb8 : decode_any 0xfec6a423 = some (.Store .SZ4 13 12 0xfe8, 4)
  f_1acbc : fetch_word segs (wa 0x1acbc) = some 0xfec6a623
  d_1acbc : decode_any 0xfec6a623 = some (.Store .SZ4 13 12 0xfec, 4)
  f_1acc0 : fetch_word segs (wa 0x1acc0) = some 0xfec6a823
  d_1acc0 : decode_any 0xfec6a823 = some (.Store .SZ4 13 12 0xff0, 4)
  f_1acc4 : fetch_word segs (wa 0x1acc4) = some 0x03076a63
  d_1acc4 : decode_any 0x03076a63 = some (.Branch .BC_LTU 14 16 0x34, 4)
  f_1acc8 : fetch_word segs (wa 0x1acc8) = some 0x02061613
  d_1acc8 : decode_any 0x02061613 = some (.ShiftImm .ALU_SLL 12 12 32, 4)
  f_1accc : fetch_word segs (wa 0x1accc) = some 0x00f585b3
  d_1accc : decode_any 0x00f585b3 = some (.Op .ALU_ADD 11 11 15, 4)
  f_1acd0 : fetch_word segs (wa 0x1acd0) = some 0x02065693
  d_1acd0 : decode_any 0x02065693 = some (.ShiftImm .ALU_SRL 13 12 32, 4)
  f_1acd4 : fetch_word segs (wa 0x1acd4) = some 0x00d66633
  d_1acd4 : decode_any 0x00d66633 = some (.Op .ALU_OR 12 12 13, 4)
  f_1acd8 : fetch_word segs (wa 0x1acd8) = some 0x01f00693
  d_1acd8 : decode_any 0x01f00693 = some (.OpImm .ALU_ADD 13 0 0x1f, 4)
  f_1acdc : fetch_word segs (wa 0x1acdc) = some 0x00c5b023
  d_1acdc : decode_any 0x00c5b023 = some (.Store .SZ8 11 12 0x0, 4)
  f_1ace0 : fetch_word segs (wa 0x1ace0) = some 0x00c5b423
  d_1ace0 : decode_any 0x00c5b423 = some (.Store .SZ8 11 12 0x8, 4)
  f_1ace4 : fetch_word segs (wa 0x1ace4) = some 0x00c5b823
  d_1ace4 : decode_any 0x00c5b823 = some (.Store .SZ8 11 12 0x10, 4)
  f_1ace8 : fetch_word segs (wa 0x1ace8) = some 0x00c5bc23
  d_1ace8 : decode_any 0x00c5bc23 = some (.Store .SZ8 11 12 0x18, 4)
  f_1acec : fetch_word segs (wa 0x1acec) = some 0xfe070713
  d_1acec : decode_any 0xfe070713 = some (.OpImm .ALU_ADD 14 14 0xfe0, 4)
  f_1acf0 : fetch_word segs (wa 0x1acf0) = some 0x02058593
  d_1acf0 : decode_any 0x02058593 = some (.OpImm .ALU_ADD 11 11 0x20, 4)
  f_1acf4 : fetch_word segs (wa 0x1acf4) = some 0xfee6e4e3
  d_1acf4 : decode_any 0xfee6e4e3 = some (.Branch .BC_LTU 13 14 0x1fe8, 4)
  f_1acf8 : fetch_word segs (wa 0x1acf8) = some 0x00008067
  d_1acf8 : decode_any 0x00008067 = some (.Jalr 0 1 0x0, 4)

/-! ## What the contract says, with the segment list still open -/



private def dstA (regs0 : bvmap 5 word) : Int := bv_unsigned (getr regs0 10)
private def dstN (regs0 : bvmap 5 word) : Int := bv_unsigned (getr regs0 12)
private def fillCz (regs0 : bvmap 5 word) : Int := bv_unsigned (getr regs0 11) % 256
private def fillC (regs0 : bvmap 5 word) : byte := Z_to_bv 8 (fillCz regs0)

private def Post (segs : List Segment) (regs0 : bvmap 5 word) (m0 : word → Option byte) :
    machine_state → Prop :=
  fun ms' => ∃ (regs' : bvmap 5 word) (m' : word → Option byte),
    ms' = mkst regs' (ret_pc (getr regs0 1)) m' (seg_rom segs)
    ∧ (∀ r : reg, r ∉ memset_clobber → getr regs' r = getr regs0 r)
    ∧ munch [(dstA regs0, dstA regs0 + dstN regs0)] m0 m'
    ∧ wmono segs m0 m'
    ∧ mem_inv segs m'
    ∧ rw_cells segs m' (dstA regs0)
        [.CB (dstN regs0).toNat (List.replicate (dstN regs0).toNat (fillC regs0))]

private theorem fillCz_range (regs0 : bvmap 5 word) : 0 ≤ fillCz regs0 ∧ fillCz regs0 < 256 := by
  unfold fillCz
  have := u64_range (getr regs0 11)
  omega

/-- The value a `sb` of `a1` stores, as `Fill.store` wants it. -/
private theorem sb_bytes (regs0 : bvmap 5 word) (v : word) (hv : v = getr regs0 11) :
    word_to_le_bytes 1 v = List.replicate 1 (fillC regs0) := by
  rw [hv]
  exact word_bytes_one (getr regs0 11)

private theorem btgt_wa (x d : Int) : btgt (wa x) d = wa (x + d) := v_addi_wa x d

/-! ## The return

`0x1acf8  jalr x0, 0(ra)`: the twin of the Rocq `fin` tactic
(`R_memset.v:178-186`), which closes every exit of the walk. -/

private theorem exit_ret (segs : List Segment) (hc : Code segs) (regs0 regs : bvmap 5 word)
    (m0 m1 : word → Option byte) (Q : Int → Prop)
    (hfr : ∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r)
    (h : Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q)
    (hcov : ∀ j : Int, 0 ≤ j → j < dstN regs0 → Q j) :
    evt segs (Post segs regs0 m0) (mkst regs (wa 0x1acf8) m1 (seg_rom segs)) := by
  have hra : getr regs 1 = getr regs0 1 := hfr 1 (by decide)
  have hn : 0 ≤ dstN regs0 := (u64_range (getr regs0 12)).1
  refine evt_step (mstep_mkst (step_jalr_x0 segs regs (wa 0x1acf8) m1 (seg_rom segs)
    0x00008067 1 0x0 (getr regs0 1) hc.f_1acf8 (by decide) hc.d_1acf8 hra)) ?_
  have hpc : v_jalr (getr regs0 1) (bv_signed (0x0 : BitVec 12)) = ret_pc (getr regs0 1) := by
    have h0 : bv_signed (0x0 : BitVec 12) = 0 := by decide
    rw [h0]
    unfold v_jalr ret_pc jalr_tgtZ
    apply bv_eq_of_unsigned
    rw [bv_unsigned_and, Z_to_bv_unsigned]
    have hm : bv_unsigned (bv_not (Z_to_bv 64 1)) = bv_wrap 64 (-2) := by decide
    rw [hm, Int.add_zero]
    have hw : bv_wrap 64 (bv_unsigned (getr regs0 1)) = bv_unsigned (getr regs0 1) := by
      have hr := u64_range (getr regs0 1)
      unfold bv_wrap
      omega
    rw [← Z_land_m2_wrap, hw]
  rw [hpc]
  exact evt_done ⟨regs, m1, rfl, hfr, h.mu, h.wm, h.mi, h.finish hn hcov⟩

/-! ## One instruction of the walk

Three store helpers, one per width, each doing what the Rocq `mst` tactic does:
take the machine step and update the invariant in one move. -/

private theorem wa_dstA (regs0 : bvmap 5 word) : wa (dstA regs0) = getr regs0 10 :=
  Z_to_bv_bv_unsigned64 _

private theorem wa_dstN (regs0 : bvmap 5 word) : wa (dstN regs0) = getr regs0 12 :=
  Z_to_bv_bv_unsigned64 _

private theorem dstN_range (regs0 : bvmap 5 word) : 0 ≤ dstN regs0 ∧ dstN regs0 < 2 ^ 64 :=
  u64_range _

private theorem dstA_range (regs0 : bvmap 5 word) : 0 ≤ dstA regs0 ∧ dstA regs0 < 2 ^ 64 :=
  u64_range _

/-- A register write inside the caller-saved set keeps the frame claim. -/
private theorem fr_upd {regs0 regs : bvmap 5 word} (rd : reg) (v : word)
    (hrd : rd ∈ memset_clobber)
    (h : ∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r) :
    ∀ r : reg, r ∉ memset_clobber → getr (regupd regs rd v) r = getr regs0 r := by
  intro r hr
  have hne : r ≠ rd := fun hh => hr (hh ▸ hrd)
  rw [getr_other regs rd v r hne]
  exact h r hr

/-- `sb a1, off(rs1)`: one byte of the fill value into the destination. -/
private theorem sb_step (segs : List Segment) (regs0 regs : bvmap 5 word)
    (pc : Int) (w : BitVec 32) (rs1 : reg) (imm : BitVec 12) (base p : Int)
    (m0 m1 : word → Option byte) (Q : Int → Prop)
    (hf : fetch_word segs (wa pc) = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Store .SZ1 rs1 11 imm, 4))
    (hbase : getr regs rs1 = wa base)
    (hoff : base + bv_signed imm = dstA regs0 + p)
    (h11 : getr regs 11 = getr regs0 11)
    (hfl : Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q)
    (hp : 0 ≤ p) (hpk : p + 1 ≤ dstN regs0) :
    mstep segs (mkst regs (wa pc) m1 (seg_rom segs))
      (mkst regs (wa (pc + 4))
        (wbytes m1 (wa (dstA regs0 + p)) (word_to_le_bytes 1 (getr regs0 11)))
        (seg_rom segs))
    ∧ Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0
        (wbytes m1 (wa (dstA regs0 + p)) (word_to_le_bytes 1 (getr regs0 11)))
        (fun j => Q j ∨ (p ≤ j ∧ j < p + ((1 : Nat) : Int))) := by
  have haddr : v_addi (getr regs rs1) (bv_signed imm) = wa (dstA regs0 + p) := by
    rw [hbase, v_addi_wa, hoff]
  have hok : store_ok segs m1 (v_addi (getr regs rs1) (bv_signed imm)) 1 = true := by
    rw [haddr]; exact hfl.ok p 1 hp (by omega)
  have hstep := step_sb segs regs (wa pc) m1 (seg_rom segs) w rs1 11 imm hf he hd hok
  rw [haddr, h11, v_addi_wa] at hstep
  exact ⟨mstep_mkst hstep,
    hfl.store p 1 (getr regs0 11) hp (by omega) (sb_bytes regs0 _ rfl)⟩

/-- `sw a2, off(rs1)`, with `a2` already holding the 4-byte splat. -/
private theorem sw_step (segs : List Segment) (regs0 regs : bvmap 5 word)
    (pc : Int) (w : BitVec 32) (rs1 : reg) (imm : BitVec 12) (base p : Int)
    (m0 m1 : word → Option byte) (Q : Int → Prop)
    (hf : fetch_word segs (wa pc) = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Store .SZ4 rs1 12 imm, 4))
    (hbase : getr regs rs1 = wa base)
    (hoff : base + bv_signed imm = dstA regs0 + p)
    (h12 : getr regs 12 = wa (splatZ 4 (fillCz regs0)))
    (hfl : Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q)
    (hp : 0 ≤ p) (hpk : p + 4 ≤ dstN regs0) :
    mstep segs (mkst regs (wa pc) m1 (seg_rom segs))
      (mkst regs (wa (pc + 4))
        (wbytes m1 (wa (dstA regs0 + p))
          (word_to_le_bytes 4 (wa (splatZ 4 (fillCz regs0))))) (seg_rom segs))
    ∧ Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0
        (wbytes m1 (wa (dstA regs0 + p))
          (word_to_le_bytes 4 (wa (splatZ 4 (fillCz regs0)))))
        (fun j => Q j ∨ (p ≤ j ∧ j < p + ((4 : Nat) : Int))) := by
  have hc := fillCz_range regs0
  have haddr : v_addi (getr regs rs1) (bv_signed imm) = wa (dstA regs0 + p) := by
    rw [hbase, v_addi_wa, hoff]
  have hok : store_ok segs m1 (v_addi (getr regs rs1) (bv_signed imm)) 4 = true := by
    rw [haddr]; exact hfl.ok p 4 hp (by omega)
  have hstep := step_sw_val segs regs (wa pc) m1 (seg_rom segs) w rs1 12 imm hf he hd hok
  rw [haddr, h12, v_addi_wa] at hstep
  refine ⟨mstep_mkst hstep, hfl.store p 4 _ hp (by omega) ?_⟩
  refine word_bytes_splat 4 _ (fillCz regs0) hc.1 hc.2 ?_
  exact wa_unsigned _ (splatZ_nonneg 4 _ hc.1) (by rw [splat4]; omega)

/-- `sd a2, off(rs1)`, with `a2` already holding the 8-byte splat. -/
private theorem sd_step (segs : List Segment) (regs0 regs : bvmap 5 word)
    (pc : Int) (w : BitVec 32) (rs1 : reg) (imm : BitVec 12) (base p : Int)
    (m0 m1 : word → Option byte) (Q : Int → Prop)
    (hf : fetch_word segs (wa pc) = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Store .SZ8 rs1 12 imm, 4))
    (hbase : getr regs rs1 = wa base)
    (hoff : base + bv_signed imm = dstA regs0 + p)
    (h12 : getr regs 12 = wa (splatZ 8 (fillCz regs0)))
    (hfl : Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q)
    (hp : 0 ≤ p) (hpk : p + 8 ≤ dstN regs0) :
    mstep segs (mkst regs (wa pc) m1 (seg_rom segs))
      (mkst regs (wa (pc + 4))
        (wbytes m1 (wa (dstA regs0 + p))
          (word_to_le_bytes 8 (wa (splatZ 8 (fillCz regs0))))) (seg_rom segs))
    ∧ Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0
        (wbytes m1 (wa (dstA regs0 + p))
          (word_to_le_bytes 8 (wa (splatZ 8 (fillCz regs0)))))
        (fun j => Q j ∨ (p ≤ j ∧ j < p + ((8 : Nat) : Int))) := by
  have hc := fillCz_range regs0
  have haddr : v_addi (getr regs rs1) (bv_signed imm) = wa (dstA regs0 + p) := by
    rw [hbase, v_addi_wa, hoff]
  have hok : store_ok segs m1 (v_addi (getr regs rs1) (bv_signed imm)) 8 = true := by
    rw [haddr]; exact hfl.ok p 8 hp (by omega)
  have hstep := step_sd_val segs regs (wa pc) m1 (seg_rom segs) w rs1 12 imm hf he hd hok
  rw [haddr, h12, v_addi_wa] at hstep
  refine ⟨mstep_mkst hstep, hfl.store p 8 _ hp (by omega) ?_⟩
  refine word_bytes_splat 8 _ (fillCz regs0) hc.1 hc.2 ?_
  exact wa_unsigned _ (splatZ_nonneg 8 _ hc.1) (by rw [splat8]; omega)

/-- The `bltu` test on two in-range values. -/
private theorem bltu_wa (x y : Int) (hx : 0 ≤ x) (hx2 : x < 2 ^ 64) (hy : 0 ≤ y) (hy2 : y < 2 ^ 64) :
    branch_taken branch_cond.BC_LTU (wa x) (wa y) = decide (x < y) := by
  show c_ltu (wa x) (wa y) = _
  rw [c_ltu_ltb, wa_unsigned x hx hx2, wa_unsigned y hy hy2]

/-! ## `0x1ac04` … `0x1ac18`: the entry, the first two bytes and the `n < 3` exit

The twin of `R_memset.v:235-240`. -/

private theorem blk_1ac04 (segs : List Segment) (hc : Code segs) (regs0 : bvmap 5 word)
    (m0 : word → Option byte)
    (hwr : wr_at segs m0 (dstA regs0) (dstN regs0))
    (hmi : mem_inv segs m0)
    (next : ∀ (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop),
      (∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r) →
      Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q →
      getr regs 11 = getr regs0 11 →
      getr regs 12 = getr regs0 12 →
      getr regs 13 = wa (dstA regs0 + dstN regs0) →
      3 ≤ dstN regs0 →
      (∀ j : Int, j = 0 ∨ j = dstN regs0 - 1 → Q j) →
      evt segs (Post segs regs0 m0) (mkst regs (wa 0x1ac1c) m1 (seg_rom segs))) :
    evt segs (Post segs regs0 m0) (mkst regs0 (wa 0x1ac04) m0 (seg_rom segs)) := by
  have hz : getr regs0 0 = wa 0 := getr_zero regs0
  have hnr := dstN_range regs0
  have hAr := dstA_range regs0
  have hfl0 : Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m0 (fun _ => False) :=
    Fill.init segs _ _ _ m0 hwr hmi
  have hfr0 : ∀ r : reg, r ∉ memset_clobber → getr regs0 r = getr regs0 r := fun _ _ => rfl
  have hwrA : dstA regs0 + dstN regs0 ≤ 2 ^ 64 := hwr.2.1
  -- 0x1ac04  beq a2, x0, +0xf4
  cases hb : branch_taken branch_cond.BC_EQ (getr regs0 12) (getr regs0 0) with
  | true =>
    have heq : getr regs0 12 = getr regs0 0 := (bv_eqb_eq _ _).1 hb
    have hn0 : dstN regs0 = 0 := by
      unfold dstN
      rw [heq, hz]
      exact wa_unsigned 0 (by omega) (by omega)
    refine evt_step (mstep_mkst (step_branch_tk_gen segs regs0 (wa 0x1ac04) m0
      (seg_rom segs) 0x0e060a63 .BC_EQ 12 0 0xf4 hc.f_1ac04 (by decide) hc.d_1ac04 hb)) ?_
    rw [show bv_signed (0xf4 : BitVec 13) = 244 from by decide, btgt_wa,
      show (0x1ac04 : Int) + 244 = 0x1acf8 from by omega]
    exact exit_ret segs hc regs0 regs0 m0 m0 _ hfr0 hfl0 (fun j h1 h2 => absurd h2 (by omega))
  | false =>
    have hn1 : 1 ≤ dstN regs0 := by
      rcases Int.lt_or_le 0 (dstN regs0) with h | h
      · omega
      · exfalso
        have h0 : dstN regs0 = 0 := by omega
        have heq : getr regs0 12 = getr regs0 0 := by rw [← wa_dstN regs0, h0, hz]
        rw [heq] at hb
        simp [branch_taken, bv_eqb] at hb
    refine evt_step (mstep_mkst (step_branch_ft_gen segs regs0 (wa 0x1ac04) m0
      (seg_rom segs) 0x0e060a63 .BC_EQ 12 0 0xf4 hc.f_1ac04 (by decide) hc.d_1ac04 hb)) ?_
    rw [v_addi_wa, show (0x1ac04 : Int) + 4 = 0x1ac08 from by omega]
    -- 0x1ac08  sb a1, 0(a0)
    obtain ⟨hs1, hfl1⟩ := sb_step segs regs0 regs0 0x1ac08 0x00b50023 10 0x0
      (dstA regs0) 0 m0 m0 _ hc.f_1ac08 (by decide) hc.d_1ac08 (wa_dstA regs0).symm
      (by rw [show bv_signed (0x0 : BitVec 12) = 0 from by decide]) rfl hfl0
      (by omega) (by omega)
    refine evt_step hs1 ?_
    rw [show (0x1ac08 : Int) + 4 = 0x1ac0c from by omega]
    -- 0x1ac0c  add a3, a0, a2
    refine evt_step (mstep_mkst (step_add_at segs regs0 (wa 0x1ac0c) _ (seg_rom segs)
      0x00c506b3 13 10 12 (wa (dstA regs0 + dstN regs0)) hc.f_1ac0c (by decide) hc.d_1ac0c
      (by decide) (by rw [← wa_dstA regs0, ← wa_dstN regs0, v_add_wa]))) ?_
    rw [v_addi_wa, show (0x1ac0c : Int) + 4 = 0x1ac10 from by omega]
    -- 0x1ac10  addi a4, x0, 3
    refine evt_step (mstep_mkst (step_addi_at segs _ (wa 0x1ac10) _ (seg_rom segs)
      0x00300713 14 0 0x3 (wa 3) hc.f_1ac10 (by decide) hc.d_1ac10 (by decide)
      (by rw [getr_other regs0 13 _ 0 (by decide), hz, v_addi_wa,
        show bv_signed (0x3 : BitVec 12) = 3 from by decide,
        show (0 : Int) + 3 = 3 from by omega]))) ?_
    rw [v_addi_wa, show (0x1ac10 : Int) + 4 = 0x1ac14 from by omega]
    -- 0x1ac14  sb a1, -1(a3)
    have h13 : getr (regupd (regupd regs0 13 (wa (dstA regs0 + dstN regs0))) 14 (wa 3)) 13
        = wa (dstA regs0 + dstN regs0) := by
      rw [getr_other _ 14 _ 13 (by decide), getr_same regs0 13 _ (by decide)]
    have h11 : getr (regupd (regupd regs0 13 (wa (dstA regs0 + dstN regs0))) 14 (wa 3)) 11
        = getr regs0 11 := by
      rw [getr_other _ 14 _ 11 (by decide), getr_other regs0 13 _ 11 (by decide)]
    have h12 : getr (regupd (regupd regs0 13 (wa (dstA regs0 + dstN regs0))) 14 (wa 3)) 12
        = getr regs0 12 := by
      rw [getr_other _ 14 _ 12 (by decide), getr_other regs0 13 _ 12 (by decide)]
    have h14 : getr (regupd (regupd regs0 13 (wa (dstA regs0 + dstN regs0))) 14 (wa 3)) 14
        = wa 3 := getr_same _ 14 _ (by decide)
    obtain ⟨hs2, hfl2⟩ := sb_step segs regs0 _ 0x1ac14 0xfeb68fa3 13 0xfff
      (dstA regs0 + dstN regs0) (dstN regs0 - 1) m0 _ _ hc.f_1ac14 (by decide) hc.d_1ac14
      h13 (by rw [show bv_signed (0xfff : BitVec 12) = -1 from by decide]; omega) h11 hfl1
      (by omega) (by omega)
    refine evt_step hs2 ?_
    rw [show (0x1ac14 : Int) + 4 = 0x1ac18 from by omega]
    -- 0x1ac18  bltu a2, a4, +0xe0
    have hbr : branch_taken branch_cond.BC_LTU
        (getr (regupd (regupd regs0 13 (wa (dstA regs0 + dstN regs0))) 14 (wa 3)) 12)
        (getr (regupd (regupd regs0 13 (wa (dstA regs0 + dstN regs0))) 14 (wa 3)) 14)
        = decide (dstN regs0 < 3) := by
      rw [h12, h14, ← wa_dstN regs0, bltu_wa _ _ (by omega) (by omega) (by omega) (by omega)]
    have hfrA : ∀ r : reg, r ∉ memset_clobber →
        getr (regupd (regupd regs0 13 (wa (dstA regs0 + dstN regs0))) 14 (wa 3)) r
          = getr regs0 r :=
      fr_upd 14 _ (by decide) (fr_upd 13 _ (by decide) hfr0)
    have hcovA : ∀ j : Int, j = 0 ∨ j = dstN regs0 - 1 →
        (fun j => (fun j => (fun _ => False) j ∨ (0 ≤ j ∧ j < 0 + ((1 : Nat) : Int))) j
          ∨ (dstN regs0 - 1 ≤ j ∧ j < dstN regs0 - 1 + ((1 : Nat) : Int))) j := by
      intro j hj
      simp only []
      omega
    cases hlt : decide (dstN regs0 < 3) with
    | true =>
      have hn3 : dstN regs0 < 3 := of_decide_eq_true hlt
      refine evt_step (mstep_mkst (step_branch_tk_gen segs _ (wa 0x1ac18) _ (seg_rom segs)
        0x0ee66063 .BC_LTU 12 14 0xe0 hc.f_1ac18 (by decide) hc.d_1ac18
        (by rw [hbr, hlt]))) ?_
      rw [show bv_signed (0xe0 : BitVec 13) = 224 from by decide, btgt_wa,
        show (0x1ac18 : Int) + 224 = 0x1acf8 from by omega]
      refine exit_ret segs hc regs0 _ m0 _ _ hfrA hfl2 ?_
      intro j h1 h2
      exact hcovA j (by omega)
    | false =>
      have hn3 : 3 ≤ dstN regs0 := by
        have := of_decide_eq_false hlt
        omega
      refine evt_step (mstep_mkst (step_branch_ft_gen segs _ (wa 0x1ac18) _ (seg_rom segs)
        0x0ee66063 .BC_LTU 12 14 0xe0 hc.f_1ac18 (by decide) hc.d_1ac18
        (by rw [hbr, hlt]))) ?_
      rw [v_addi_wa, show (0x1ac18 : Int) + 4 = 0x1ac1c from by omega]
      exact next _ _ _ hfrA hfl2 h11 h12 h13 hn3 hcovA





/-! ## `0x1ac34` … `0x1ac40`: byte 3, byte `n-4`, and the `n < 9` exit

The twin of `R_memset.v:247-250`. -/

private theorem blk_1ac34 (segs : List Segment) (hc : Code segs) (regs0 : bvmap 5 word)
    (m0 : word → Option byte)
    (next : ∀ (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop),
      (∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r) →
      Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q →
      getr regs 11 = getr regs0 11 →
      getr regs 12 = getr regs0 12 →
      getr regs 15 = wa 9 →
      9 ≤ dstN regs0 →
      (∀ j : Int, (0 ≤ j ∧ j < 4) ∨ (dstN regs0 - 4 ≤ j ∧ j < dstN regs0) → Q j) →
      evt segs (Post segs regs0 m0) (mkst regs (wa 0x1ac44) m1 (seg_rom segs)))
    (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop)
    (hfr : ∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r)
    (hfl : Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q)
    (h11 : getr regs 11 = getr regs0 11)
    (h12 : getr regs 12 = getr regs0 12)
    (h13 : getr regs 13 = wa (dstA regs0 + dstN regs0))
    (hn : 7 ≤ dstN regs0)
    (hcov : ∀ j : Int, (0 ≤ j ∧ j < 3) ∨ (dstN regs0 - 3 ≤ j ∧ j < dstN regs0) → Q j) :
    evt segs (Post segs regs0 m0) (mkst regs (wa 0x1ac34) m1 (seg_rom segs)) := by
  have hnr := dstN_range regs0
  have hAr := dstA_range regs0
  have hz : getr regs 0 = wa 0 := getr_zero regs
  have h10 : getr regs 10 = wa (dstA regs0) := (hfr 10 (by decide)).trans (wa_dstA regs0).symm
  -- 0x1ac34  sb a1, 3(a0)
  obtain ⟨hs1, hfl1⟩ := sb_step segs regs0 regs 0x1ac34 0x00b501a3 10 0x3
    (dstA regs0) 3 m0 m1 Q hc.f_1ac34 (by decide) hc.d_1ac34 h10
    (by rw [show bv_signed (0x3 : BitVec 12) = 3 from by decide]) h11 hfl
    (by omega) (by omega)
  refine evt_step hs1 ?_
  rw [show (0x1ac34 : Int) + 4 = 0x1ac38 from by omega]
  -- 0x1ac38  addi a5, x0, 9
  refine evt_step (mstep_mkst (step_addi_at segs _ (wa 0x1ac38) _ (seg_rom segs)
    0x00900793 15 0 0x9 (wa 9) hc.f_1ac38 (by decide) hc.d_1ac38 (by decide)
    (by rw [hz, v_addi_wa,
      show bv_signed (0x9 : BitVec 12) = 9 from by decide,
      show (0 : Int) + 9 = 9 from by omega]))) ?_
  rw [v_addi_wa, show (0x1ac38 : Int) + 4 = 0x1ac3c from by omega]
  have h13' : getr (regupd regs 15 (wa 9)) 13 = wa (dstA regs0 + dstN regs0) := by
    rw [getr_other regs 15 _ 13 (by decide)]; exact h13
  have h11' : getr (regupd regs 15 (wa 9)) 11 = getr regs0 11 := by
    rw [getr_other regs 15 _ 11 (by decide)]; exact h11
  have h12' : getr (regupd regs 15 (wa 9)) 12 = getr regs0 12 := by
    rw [getr_other regs 15 _ 12 (by decide)]; exact h12
  have h15' : getr (regupd regs 15 (wa 9)) 15 = wa 9 := getr_same regs 15 _ (by decide)
  -- 0x1ac3c  sb a1, -4(a3)
  obtain ⟨hs2, hfl2⟩ := sb_step segs regs0 _ 0x1ac3c 0xfeb68e23 13 0xffc
    (dstA regs0 + dstN regs0) (dstN regs0 - 4) m0 _ _ hc.f_1ac3c (by decide) hc.d_1ac3c
    h13' (by rw [show bv_signed (0xffc : BitVec 12) = -4 from by decide]; omega) h11' hfl1
    (by omega) (by omega)
  refine evt_step hs2 ?_
  rw [show (0x1ac3c : Int) + 4 = 0x1ac40 from by omega]
  -- 0x1ac40  bltu a2, a5, +0xb8
  have hbr : branch_taken branch_cond.BC_LTU
      (getr (regupd regs 15 (wa 9)) 12) (getr (regupd regs 15 (wa 9)) 15)
      = decide (dstN regs0 < 9) := by
    rw [h12', h15', ← wa_dstN regs0, bltu_wa _ _ (by omega) (by omega) (by omega) (by omega)]
  have hfrA : ∀ r : reg, r ∉ memset_clobber →
      getr (regupd regs 15 (wa 9)) r = getr regs0 r :=
    fr_upd 15 _ (by decide) hfr
  cases hlt : decide (dstN regs0 < 9) with
  | true =>
    have h9 : dstN regs0 < 9 := of_decide_eq_true hlt
    refine evt_step (mstep_mkst (step_branch_tk_gen segs _ (wa 0x1ac40) _ (seg_rom segs)
      0x0af66c63 .BC_LTU 12 15 0xb8 hc.f_1ac40 (by decide) hc.d_1ac40
      (by rw [hbr, hlt]))) ?_
    rw [show bv_signed (0xb8 : BitVec 13) = 184 from by decide, btgt_wa,
      show (0x1ac40 : Int) + 184 = 0x1acf8 from by omega]
    refine exit_ret segs hc regs0 _ m0 _ _ hfrA hfl2 ?_
    intro j hj0 hjn
    rcases (show (0 ≤ j ∧ j < 3) ∨ (3 ≤ j ∧ j < 4) ∨
        (dstN regs0 - 4 ≤ j ∧ j < dstN regs0 - 3) ∨
        (dstN regs0 - 3 ≤ j ∧ j < dstN regs0) from by omega) with h | h | h | h
    · exact Or.inl (Or.inl (hcov j (Or.inl h)))
    · exact Or.inl (Or.inr (by omega))
    · exact Or.inr (by omega)
    · exact Or.inl (Or.inl (hcov j (Or.inr h)))
  | false =>
    have h9 : 9 ≤ dstN regs0 := by
      have := of_decide_eq_false hlt
      omega
    refine evt_step (mstep_mkst (step_branch_ft_gen segs _ (wa 0x1ac40) _ (seg_rom segs)
      0x0af66c63 .BC_LTU 12 15 0xb8 hc.f_1ac40 (by decide) hc.d_1ac40
      (by rw [hbr, hlt]))) ?_
    rw [v_addi_wa, show (0x1ac40 : Int) + 4 = 0x1ac44 from by omega]
    refine next _ _ _ hfrA hfl2 h11' h12' h15' h9 ?_
    intro j hj
    rcases (show (0 ≤ j ∧ j < 3) ∨ (3 ≤ j ∧ j < 4) ∨
        (dstN regs0 - 4 ≤ j ∧ j < dstN regs0 - 3) ∨
        (dstN regs0 - 3 ≤ j ∧ j < dstN regs0) from by omega) with h | h | h | h
    · exact Or.inl (Or.inl (hcov j (Or.inl h)))
    · exact Or.inl (Or.inr (by omega))
    · exact Or.inr (by omega)
    · exact Or.inl (Or.inl (hcov j (Or.inr h)))

/-! ## `0x1ac1c` … `0x1ac30`: bytes 1, 2, `n-3`, `n-2` and the `n < 7` exit

The twin of `R_memset.v:241-246`. -/

private theorem blk_1ac1c (segs : List Segment) (hc : Code segs) (regs0 : bvmap 5 word)
    (m0 : word → Option byte)
    (next : ∀ (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop),
      (∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r) →
      Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q →
      getr regs 11 = getr regs0 11 →
      getr regs 12 = getr regs0 12 →
      getr regs 13 = wa (dstA regs0 + dstN regs0) →
      7 ≤ dstN regs0 →
      (∀ j : Int, (0 ≤ j ∧ j < 3) ∨ (dstN regs0 - 3 ≤ j ∧ j < dstN regs0) → Q j) →
      evt segs (Post segs regs0 m0) (mkst regs (wa 0x1ac34) m1 (seg_rom segs)))
    (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop)
    (hfr : ∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r)
    (hfl : Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q)
    (h11 : getr regs 11 = getr regs0 11)
    (h12 : getr regs 12 = getr regs0 12)
    (h13 : getr regs 13 = wa (dstA regs0 + dstN regs0))
    (hn : 3 ≤ dstN regs0)
    (hcov : ∀ j : Int, j = 0 ∨ j = dstN regs0 - 1 → Q j) :
    evt segs (Post segs regs0 m0) (mkst regs (wa 0x1ac1c) m1 (seg_rom segs)) := by
  have hnr := dstN_range regs0
  have hAr := dstA_range regs0
  have hz : getr regs 0 = wa 0 := getr_zero regs
  have h10 : getr regs 10 = wa (dstA regs0) := (hfr 10 (by decide)).trans (wa_dstA regs0).symm
  -- 0x1ac1c  sb a1, 1(a0)
  obtain ⟨hs1, hfl1⟩ := sb_step segs regs0 regs 0x1ac1c 0x00b500a3 10 0x1
    (dstA regs0) 1 m0 m1 Q hc.f_1ac1c (by decide) hc.d_1ac1c h10
    (by rw [show bv_signed (0x1 : BitVec 12) = 1 from by decide]) h11 hfl
    (by omega) (by omega)
  refine evt_step hs1 ?_
  rw [show (0x1ac1c : Int) + 4 = 0x1ac20 from by omega]
  -- 0x1ac20  sb a1, 2(a0)
  obtain ⟨hs2, hfl2⟩ := sb_step segs regs0 regs 0x1ac20 0x00b50123 10 0x2
    (dstA regs0) 2 m0 _ _ hc.f_1ac20 (by decide) hc.d_1ac20 h10
    (by rw [show bv_signed (0x2 : BitVec 12) = 2 from by decide]) h11 hfl1
    (by omega) (by omega)
  refine evt_step hs2 ?_
  rw [show (0x1ac20 : Int) + 4 = 0x1ac24 from by omega]
  -- 0x1ac24  addi a4, x0, 7
  refine evt_step (mstep_mkst (step_addi_at segs _ (wa 0x1ac24) _ (seg_rom segs)
    0x00700713 14 0 0x7 (wa 7) hc.f_1ac24 (by decide) hc.d_1ac24 (by decide)
    (by rw [hz, v_addi_wa,
      show bv_signed (0x7 : BitVec 12) = 7 from by decide,
      show (0 : Int) + 7 = 7 from by omega]))) ?_
  rw [v_addi_wa, show (0x1ac24 : Int) + 4 = 0x1ac28 from by omega]
  have h13' : getr (regupd regs 14 (wa 7)) 13 = wa (dstA regs0 + dstN regs0) := by
    rw [getr_other regs 14 _ 13 (by decide)]; exact h13
  have h11' : getr (regupd regs 14 (wa 7)) 11 = getr regs0 11 := by
    rw [getr_other regs 14 _ 11 (by decide)]; exact h11
  have h12' : getr (regupd regs 14 (wa 7)) 12 = getr regs0 12 := by
    rw [getr_other regs 14 _ 12 (by decide)]; exact h12
  have h14' : getr (regupd regs 14 (wa 7)) 14 = wa 7 := getr_same regs 14 _ (by decide)
  -- 0x1ac28  sb a1, -3(a3)
  obtain ⟨hs3, hfl3⟩ := sb_step segs regs0 _ 0x1ac28 0xfeb68ea3 13 0xffd
    (dstA regs0 + dstN regs0) (dstN regs0 - 3) m0 _ _ hc.f_1ac28 (by decide) hc.d_1ac28
    h13' (by rw [show bv_signed (0xffd : BitVec 12) = -3 from by decide]; omega) h11' hfl2
    (by omega) (by omega)
  refine evt_step hs3 ?_
  rw [show (0x1ac28 : Int) + 4 = 0x1ac2c from by omega]
  -- 0x1ac2c  sb a1, -2(a3)
  obtain ⟨hs4, hfl4⟩ := sb_step segs regs0 _ 0x1ac2c 0xfeb68f23 13 0xffe
    (dstA regs0 + dstN regs0) (dstN regs0 - 2) m0 _ _ hc.f_1ac2c (by decide) hc.d_1ac2c
    h13' (by rw [show bv_signed (0xffe : BitVec 12) = -2 from by decide]; omega) h11' hfl3
    (by omega) (by omega)
  refine evt_step hs4 ?_
  rw [show (0x1ac2c : Int) + 4 = 0x1ac30 from by omega]
  -- 0x1ac30  bltu a2, a4, +0xc8
  have hbr : branch_taken branch_cond.BC_LTU
      (getr (regupd regs 14 (wa 7)) 12) (getr (regupd regs 14 (wa 7)) 14)
      = decide (dstN regs0 < 7) := by
    rw [h12', h14', ← wa_dstN regs0, bltu_wa _ _ (by omega) (by omega) (by omega) (by omega)]
  have hfrA : ∀ r : reg, r ∉ memset_clobber →
      getr (regupd regs 14 (wa 7)) r = getr regs0 r :=
    fr_upd 14 _ (by decide) hfr
  cases hlt : decide (dstN regs0 < 7) with
  | true =>
    have h7 : dstN regs0 < 7 := of_decide_eq_true hlt
    refine evt_step (mstep_mkst (step_branch_tk_gen segs _ (wa 0x1ac30) _ (seg_rom segs)
      0x0ce66463 .BC_LTU 12 14 0xc8 hc.f_1ac30 (by decide) hc.d_1ac30
      (by rw [hbr, hlt]))) ?_
    rw [show bv_signed (0xc8 : BitVec 13) = 200 from by decide, btgt_wa,
      show (0x1ac30 : Int) + 200 = 0x1acf8 from by omega]
    refine exit_ret segs hc regs0 _ m0 _ _ hfrA hfl4 ?_
    intro j hj0 hjn
    rcases (show j = 0 ∨ (1 ≤ j ∧ j < 2) ∨ (2 ≤ j ∧ j < 3) ∨
        (dstN regs0 - 3 ≤ j ∧ j < dstN regs0 - 2) ∨
        (dstN regs0 - 2 ≤ j ∧ j < dstN regs0 - 1) ∨
        j = dstN regs0 - 1 from by omega) with h | h | h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (hcov j (Or.inl h)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (by omega))))
    · exact Or.inl (Or.inl (Or.inr (by omega)))
    · exact Or.inl (Or.inr (by omega))
    · exact Or.inr (by omega)
    · exact Or.inl (Or.inl (Or.inl (Or.inl (hcov j (Or.inr h)))))
  | false =>
    have h7 : 7 ≤ dstN regs0 := by
      have := of_decide_eq_false hlt
      omega
    refine evt_step (mstep_mkst (step_branch_ft_gen segs _ (wa 0x1ac30) _ (seg_rom segs)
      0x0ce66463 .BC_LTU 12 14 0xc8 hc.f_1ac30 (by decide) hc.d_1ac30
      (by rw [hbr, hlt]))) ?_
    rw [v_addi_wa, show (0x1ac30 : Int) + 4 = 0x1ac34 from by omega]
    refine next _ _ _ hfrA hfl4 h11' h12' h13' h7 ?_
    intro j hj
    rcases (show j = 0 ∨ (1 ≤ j ∧ j < 2) ∨ (2 ≤ j ∧ j < 3) ∨
        (dstN regs0 - 3 ≤ j ∧ j < dstN regs0 - 2) ∨
        (dstN regs0 - 2 ≤ j ∧ j < dstN regs0 - 1) ∨
        j = dstN regs0 - 1 from by omega) with h | h | h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (hcov j (Or.inl h)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (by omega))))
    · exact Or.inl (Or.inl (Or.inr (by omega)))
    · exact Or.inl (Or.inr (by omega))
    · exact Or.inr (by omega)
    · exact Or.inl (Or.inl (Or.inl (Or.inl (hcov j (Or.inr h)))))




/-! `0x1ac44` … `0x1ac78` of musl `memset`: the alignment slack `k`, the
4-byte splat of the fill byte, the rounded length `n4`, the two unaligned
4-byte stores and the `n4 < 9` exit. The twin of `R_memset.v:251-272`. -/



/-- `subw` with the writeback value named: the `_at` form `SeqExec` has for
`add`, `sub` and `addi` but not for `subw`. -/
private theorem step_subw_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op32 .ALU_SUB rd rs1 rs2, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_subw (getr regs rs1) (getr regs rs2) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_subw segs regs pc mem rom w rd rs1 rs2 hf he hd, hrd, hv]
  rfl

/-- `mulhu` with the writeback value named. -/
private theorem step_mulhu_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul .M_MULHU rd rs1 rs2, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_mulhu (getr regs rs1) (getr regs rs2) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_mulhu segs regs pc mem rom w rd rs1 rs2 hf he hd, hrd, hv]
  rfl

private theorem blk_1ac44 (segs : List Segment) (hc : Code segs) (regs0 : bvmap 5 word)
    (m0 : word → Option byte)
    (next : ∀ (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop) (k n4 : Int),
      (∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r) →
      Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q →
      getr regs 11 = wa (dstA regs0 + k) →
      getr regs 12 = wa (splatZ 4 (fillCz regs0)) →
      getr regs 14 = wa n4 →
      getr regs 15 = wa 9 →
      0 ≤ k → k ≤ 3 → (dstA regs0 + k) % 4 = 0 →
      (∃ q : Int, n4 = 4 * q) → 4 ≤ n4 →
      k + n4 ≤ dstN regs0 → dstN regs0 - k - 3 ≤ n4 →
      (∀ j : Int, (0 ≤ j ∧ j < 4) ∨ (dstN regs0 - 4 ≤ j ∧ j < dstN regs0) → Q j) →
      evt segs (Post segs regs0 m0) (mkst regs (wa 0x1ac6c) m1 (seg_rom segs)))
    (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop)
    (hfr : ∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r)
    (hfl : Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q)
    (h11 : getr regs 11 = getr regs0 11)
    (h12 : getr regs 12 = getr regs0 12)
    (h15 : getr regs 15 = wa 9)
    (hn : 9 ≤ dstN regs0)
    (hcov : ∀ j : Int, (0 ≤ j ∧ j < 4) ∨ (dstN regs0 - 4 ≤ j ∧ j < dstN regs0) → Q j) :
    evt segs (Post segs regs0 m0) (mkst regs (wa 0x1ac44) m1 (seg_rom segs)) := by
  have hA := dstA_range regs0
  have hNr := dstN_range regs0
  have hAn : dstA regs0 + dstN regs0 ≤ 2 ^ 64 := hfl.wr.2.1
  have h10 : getr regs 10 = wa (dstA regs0) := by
    rw [hfr 10 (by decide)]; exact (wa_dstA regs0).symm
  have h12' : getr regs 12 = wa (dstN regs0) := by
    rw [h12]; exact (wa_dstN regs0).symm
  -- the same three equations in the `reg_get` form `getr_resolve` leaves behind
  have g10 : reg_get regs 10 = wa (dstA regs0) := h10
  have g11 : reg_get regs 11 = reg_get regs0 11 := h11
  have g12 : reg_get regs 12 = wa (dstN regs0) := h12'
  have g15 : reg_get regs 15 = wa 9 := h15
  obtain ⟨k, hk0, hk3, hal, hkv⟩ := k_val (dstA regs0) hA.1 hA.2
  obtain ⟨n4, hn4def⟩ : ∃ x : Int, x = (dstN regs0 - k) - (dstN regs0 - k) % 4 := ⟨_, rfl⟩
  have hn4q : ∃ q : Int, n4 = 4 * q := ⟨(dstN regs0 - k) / 4, by omega⟩
  have hn4lo : dstN regs0 - k - 3 ≤ n4 := by omega
  have hn4hi : n4 ≤ dstN regs0 - k := by omega
  have hn44 : 4 ≤ n4 := by omega
  -- 0x1ac44  subw a3, x0, a0
  refine evt_step (mstep_mkst (step_subw_at segs regs (wa 0x1ac44) m1 (seg_rom segs)
    0x40a006bb 13 0 10 (v_subw (Z_to_bv 64 0) (wa (dstA regs0))) hc.f_1ac44 (by decide)
    hc.d_1ac44 (by decide) (by rw [getr_zero, h10]))) ?_
  rw [v_addi_wa, show (0x1ac44 : Int) + 4 = 0x1ac48 from by omega]
  -- 0x1ac48  slli a6, a1, 56
  refine evt_step (mstep_mkst (step_slli_at segs _ (wa 0x1ac48) m1 (seg_rom segs)
    0x03859813 16 11 56 (v_slli (getr regs0 11) 56) hc.f_1ac48 (by decide) hc.d_1ac48
    (by decide)
    (by rw [show bv_unsigned (56 : BitVec 6) = (56 : Int) from by decide]
        getr_resolve
        rw [g11]))) ?_
  rw [v_addi_wa, show (0x1ac48 : Int) + 4 = 0x1ac4c from by omega]
  -- 0x1ac4c  lui a1, 0x10101
  refine evt_step (mstep_mkst (step_lui_at segs _ (wa 0x1ac4c) m1 (seg_rom segs)
    0x101015b7 11 0x10101 (wa 0x10101000) hc.f_1ac4c (by decide) hc.d_1ac4c
    (by decide) (by decide +kernel))) ?_
  rw [v_addi_wa, show (0x1ac4c : Int) + 4 = 0x1ac50 from by omega]
  -- 0x1ac50  andi a3, a3, 3
  refine evt_step (mstep_mkst (step_andi_at segs _ (wa 0x1ac50) m1 (seg_rom segs)
    0x0036f693 13 13 0x3 (wa k) hc.f_1ac50 (by decide) hc.d_1ac50 (by decide)
    (by rw [show bv_signed (0x3 : BitVec 12) = (3 : Int) from by decide]
        getr_resolve
        exact hkv))) ?_
  rw [v_addi_wa, show (0x1ac50 : Int) + 4 = 0x1ac54 from by omega]
  -- 0x1ac54  slli a4, a1, 4
  refine evt_step (mstep_mkst (step_slli_at segs _ (wa 0x1ac54) m1 (seg_rom segs)
    0x00459713 14 11 4 (wa 0x101010000) hc.f_1ac54 (by decide) hc.d_1ac54 (by decide)
    (by getr_resolve; decide +kernel))) ?_
  rw [v_addi_wa, show (0x1ac54 : Int) + 4 = 0x1ac58 from by omega]
  -- 0x1ac58  sub a2, a2, a3
  refine evt_step (mstep_mkst (step_sub_at segs _ (wa 0x1ac58) m1 (seg_rom segs)
    0x40d60633 12 12 13 (wa (dstN regs0 - k)) hc.f_1ac58 (by decide) hc.d_1ac58
    (by decide) (by getr_resolve; rw [g12, v_sub_wa]))) ?_
  rw [v_addi_wa, show (0x1ac58 : Int) + 4 = 0x1ac5c from by omega]
  -- 0x1ac5c  add a1, a0, a3
  refine evt_step (mstep_mkst (step_add_at segs _ (wa 0x1ac5c) m1 (seg_rom segs)
    0x00d505b3 11 10 13 (wa (dstA regs0 + k)) hc.f_1ac5c (by decide) hc.d_1ac5c
    (by decide) (by getr_resolve; rw [g10, v_add_wa]))) ?_
  rw [v_addi_wa, show (0x1ac5c : Int) + 4 = 0x1ac60 from by omega]
  -- 0x1ac60  addi a3, a4, 0x100
  refine evt_step (mstep_mkst (step_addi_at segs _ (wa 0x1ac60) m1 (seg_rom segs)
    0x10070693 13 14 0x100 (wa 0x101010100) hc.f_1ac60 (by decide) hc.d_1ac60
    (by decide) (by getr_resolve; decide +kernel))) ?_
  rw [v_addi_wa, show (0x1ac60 : Int) + 4 = 0x1ac64 from by omega]
  -- 0x1ac64  andi a4, a2, -4
  refine evt_step (mstep_mkst (step_andi_at segs _ (wa 0x1ac64) m1 (seg_rom segs)
    0xffc67713 14 12 0xffc (wa n4) hc.f_1ac64 (by decide) hc.d_1ac64 (by decide)
    (by rw [show bv_signed (0xffc : BitVec 12) = (-4 : Int) from by decide]
        getr_resolve
        rw [n4_val (dstN regs0 - k) (by omega) (by omega), hn4def]))) ?_
  rw [v_addi_wa, show (0x1ac64 : Int) + 4 = 0x1ac68 from by omega]
  -- 0x1ac68  mulhu a2, a6, a3
  refine evt_step (mstep_mkst (step_mulhu_at segs _ (wa 0x1ac68) m1 (seg_rom segs)
    0x02d83633 12 16 13 (wa (splatZ 4 (fillCz regs0))) hc.f_1ac68 (by decide) hc.d_1ac68
    (by decide) (by getr_resolve; exact mulhu_splat (getr regs0 11)))) ?_
  rw [v_addi_wa, show (0x1ac68 : Int) + 4 = 0x1ac6c from by omega]
  exact next _ _ _ k n4
    (fr_upd 12 _ (by decide) (fr_upd 14 _ (by decide) (fr_upd 13 _ (by decide)
      (fr_upd 11 _ (by decide) (fr_upd 12 _ (by decide) (fr_upd 14 _ (by decide)
        (fr_upd 13 _ (by decide) (fr_upd 11 _ (by decide) (fr_upd 16 _ (by decide)
          (fr_upd 13 _ (by decide) hfr)))))))))) hfl
    (by getr_resolve; rfl) (by getr_resolve; rfl) (by getr_resolve; rfl)
    (by getr_resolve; exact g15) hk0 hk3 hal hn4q hn44 (by omega) (by omega) hcov

/-- `0x1ac6c` … `0x1ac78`: the two unaligned 4-byte stores and the `n4 < 9`
exit. The twin of `R_memset.v:270-272`. -/
private theorem blk_1ac6c (segs : List Segment) (hc : Code segs) (regs0 : bvmap 5 word)
    (m0 : word → Option byte) (k n4 : Int)
    (next : ∀ (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop),
      (∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r) →
      Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q →
      getr regs 11 = wa (dstA regs0 + k) →
      getr regs 12 = wa (splatZ 4 (fillCz regs0)) →
      getr regs 13 = wa (dstA regs0 + k + n4) →
      getr regs 14 = wa n4 →
      getr regs 15 = wa 9 →
      9 ≤ n4 →
      (∀ j : Int, (0 ≤ j ∧ j < 4) ∨ (dstN regs0 - 4 ≤ j ∧ j < dstN regs0)
        ∨ (k ≤ j ∧ j < k + 4) ∨ (k + n4 - 4 ≤ j ∧ j < k + n4) → Q j) →
      evt segs (Post segs regs0 m0) (mkst regs (wa 0x1ac7c) m1 (seg_rom segs)))
    (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop)
    (hfr : ∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r)
    (hfl : Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q)
    (h11 : getr regs 11 = wa (dstA regs0 + k))
    (h12 : getr regs 12 = wa (splatZ 4 (fillCz regs0)))
    (h14 : getr regs 14 = wa n4)
    (h15 : getr regs 15 = wa 9)
    (hk0 : 0 ≤ k) (hk3 : k ≤ 3) (hal : (dstA regs0 + k) % 4 = 0)
    (hn4q : ∃ q : Int, n4 = 4 * q) (hn44 : 4 ≤ n4)
    (hkn : k + n4 ≤ dstN regs0) (hn4lo : dstN regs0 - k - 3 ≤ n4)
    (hcov : ∀ j : Int, (0 ≤ j ∧ j < 4) ∨ (dstN regs0 - 4 ≤ j ∧ j < dstN regs0) → Q j) :
    evt segs (Post segs regs0 m0) (mkst regs (wa 0x1ac6c) m1 (seg_rom segs)) := by
  have hNr := dstN_range regs0
  have g15 : reg_get regs 15 = wa 9 := h15
  -- 0x1ac6c  sw a2, 0(a1)
  obtain ⟨hs1, hfl1⟩ := sw_step segs regs0 regs 0x1ac6c 0x00c5a023 11 0x0
    (dstA regs0 + k) k m0 m1 Q hc.f_1ac6c (by decide) hc.d_1ac6c h11
    (by rw [show bv_signed (0x0 : BitVec 12) = (0 : Int) from by decide]; omega)
    h12 hfl hk0 (by omega)
  refine evt_step hs1 ?_
  rw [show (0x1ac6c : Int) + 4 = 0x1ac70 from by omega]
  -- 0x1ac70  add a3, a1, a4
  refine evt_step (mstep_mkst (step_add_at segs regs (wa 0x1ac70) _ (seg_rom segs)
    0x00e586b3 13 11 14 (wa (dstA regs0 + k + n4)) hc.f_1ac70 (by decide) hc.d_1ac70
    (by decide) (by rw [h11, h14, v_add_wa]))) ?_
  rw [v_addi_wa, show (0x1ac70 : Int) + 4 = 0x1ac74 from by omega]
  -- 0x1ac74  sw a2, -4(a3)
  obtain ⟨hs2, hfl2⟩ := sw_step segs regs0 (regupd regs 13 (wa (dstA regs0 + k + n4)))
    0x1ac74 0xfec6ae23 13 0xffc
    (dstA regs0 + k + n4) (k + n4 - 4) m0 _ _ hc.f_1ac74 (by decide) hc.d_1ac74
    (getr_same regs 13 _ (by decide))
    (by rw [show bv_signed (0xffc : BitVec 12) = (-4 : Int) from by decide]; omega)
    (by rw [getr_other regs 13 _ 12 (by decide), h12]) hfl1 (by omega) (by omega)
  refine evt_step hs2 ?_
  rw [show (0x1ac74 : Int) + 4 = 0x1ac78 from by omega]
  -- 0x1ac78  bltu a4, a5, +0x80
  have g14' : getr (regupd regs 13 (wa (dstA regs0 + k + n4))) 14 = wa n4 := by
    rw [getr_other regs 13 _ 14 (by decide), h14]
  have g15' : getr (regupd regs 13 (wa (dstA regs0 + k + n4))) 15 = wa 9 := by
    rw [getr_other regs 13 _ 15 (by decide), h15]
  have g11' : getr (regupd regs 13 (wa (dstA regs0 + k + n4))) 11 = wa (dstA regs0 + k) := by
    rw [getr_other regs 13 _ 11 (by decide), h11]
  have g12' : getr (regupd regs 13 (wa (dstA regs0 + k + n4))) 12
      = wa (splatZ 4 (fillCz regs0)) := by
    rw [getr_other regs 13 _ 12 (by decide), h12]
  have g13' : getr (regupd regs 13 (wa (dstA regs0 + k + n4))) 13
      = wa (dstA regs0 + k + n4) := getr_same regs 13 _ (by decide)
  have hbr : branch_taken branch_cond.BC_LTU
      (getr (regupd regs 13 (wa (dstA regs0 + k + n4))) 14)
      (getr (regupd regs 13 (wa (dstA regs0 + k + n4))) 15) = decide (n4 < 9) := by
    rw [g14', g15', bltu_wa _ _ (by omega) (by omega) (by omega) (by omega)]
  cases hlt : decide (n4 < 9) with
  | true =>
    have h9 : n4 < 9 := of_decide_eq_true hlt
    refine evt_step (mstep_mkst (step_branch_tk_gen segs _ (wa 0x1ac78) _ (seg_rom segs)
      0x08f76063 .BC_LTU 14 15 0x80 hc.f_1ac78 (by decide) hc.d_1ac78
      (by rw [hbr, hlt]))) ?_
    rw [show bv_signed (0x80 : BitVec 13) = (128 : Int) from by decide, btgt_wa,
      show (0x1ac78 : Int) + 128 = 0x1acf8 from by omega]
    refine exit_ret segs hc regs0 _ m0 _ _ (fr_upd 13 _ (by decide) hfr) hfl2 ?_
    intro j hj1 hj2
    rcases Int.lt_or_le j 4 with h | h
    · exact Or.inl (Or.inl (hcov j (Or.inl ⟨hj1, h⟩)))
    rcases Int.lt_or_le j (dstN regs0 - 4) with h2 | h2
    · rcases Int.lt_or_le j (k + n4 - 4) with h3 | h3
      · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inl (Or.inl (hcov j (Or.inr ⟨h2, hj2⟩)))
  | false =>
    have h9 : 9 ≤ n4 := by have hd := of_decide_eq_false hlt; omega
    refine evt_step (mstep_mkst (step_branch_ft_gen segs _ (wa 0x1ac78) _ (seg_rom segs)
      0x08f76063 .BC_LTU 14 15 0x80 hc.f_1ac78 (by decide) hc.d_1ac78
      (by rw [hbr, hlt]))) ?_
    rw [v_addi_wa, show (0x1ac78 : Int) + 4 = 0x1ac7c from by omega]
    refine next _ _ _ (fr_upd 13 _ (by decide) hfr) hfl2 g11' g12' g13' g14' g15' h9 ?_
    intro j hj
    rcases hj with h | h | h | h
    · exact Or.inl (Or.inl (hcov j (Or.inl h)))
    · exact Or.inl (Or.inl (hcov j (Or.inr h)))
    · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inr ⟨by omega, by omega⟩






/-! ## `0x1ac7c` … `0x1ac90`: four word stores and the `n4 < 25` exit

The twin of `R_memset.v:273-278`. -/

private theorem blk_1ac7c (segs : List Segment) (hc : Code segs) (regs0 : bvmap 5 word)
    (m0 : word → Option byte) (k n4 : Int)
    (next : ∀ (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop),
      (∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r) →
      Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q →
      getr regs 11 = wa (dstA regs0 + k) →
      getr regs 12 = wa (splatZ 4 (fillCz regs0)) →
      getr regs 13 = wa (dstA regs0 + k + n4) →
      getr regs 14 = wa n4 →
      getr regs 15 = wa 25 →
      25 ≤ n4 →
      (∀ j : Int, (0 ≤ j ∧ j < 4) ∨ (dstN regs0 - 4 ≤ j ∧ j < dstN regs0)
        ∨ (k ≤ j ∧ j < k + 12) ∨ (k + n4 - 12 ≤ j ∧ j < k + n4) → Q j) →
      evt segs (Post segs regs0 m0) (mkst regs (wa 0x1ac94) m1 (seg_rom segs)))
    (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop)
    (hfr : ∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r)
    (hfl : Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q)
    (h11 : getr regs 11 = wa (dstA regs0 + k))
    (h12 : getr regs 12 = wa (splatZ 4 (fillCz regs0)))
    (h13 : getr regs 13 = wa (dstA regs0 + k + n4))
    (h14 : getr regs 14 = wa n4)
    (_h15 : getr regs 15 = wa 9)
    (hk0 : 0 ≤ k) (hk3 : k ≤ 3)
    (hq4 : ∃ q : Int, n4 = 4 * q) (hn49 : 9 ≤ n4)
    (hkn : k + n4 ≤ dstN regs0) (hn4lo : dstN regs0 - k - 3 ≤ n4)
    (hcov : ∀ j : Int, (0 ≤ j ∧ j < 4) ∨ (dstN regs0 - 4 ≤ j ∧ j < dstN regs0)
      ∨ (k ≤ j ∧ j < k + 4) ∨ (k + n4 - 4 ≤ j ∧ j < k + n4) → Q j) :
    evt segs (Post segs regs0 m0) (mkst regs (wa 0x1ac7c) m1 (seg_rom segs)) := by
  obtain ⟨q, hq⟩ := hq4
  have hnr := dstN_range regs0
  have hAr := dstA_range regs0
  have hz : getr regs 0 = wa 0 := getr_zero regs
  have hn12 : 12 ≤ n4 := by omega
  -- 0x1ac7c  sw a2, 4(a1)
  obtain ⟨hs1, hfl1⟩ := sw_step segs regs0 regs 0x1ac7c 0x00c5a223 11 0x4
    (dstA regs0 + k) (k + 4) m0 m1 Q hc.f_1ac7c (by decide) hc.d_1ac7c h11
    (by rw [show bv_signed (0x4 : BitVec 12) = 4 from by decide]; omega) h12 hfl
    (by omega) (by omega)
  refine evt_step hs1 ?_
  rw [show (0x1ac7c : Int) + 4 = 0x1ac80 from by omega]
  -- 0x1ac80  sw a2, 8(a1)
  obtain ⟨hs2, hfl2⟩ := sw_step segs regs0 regs 0x1ac80 0x00c5a423 11 0x8
    (dstA regs0 + k) (k + 8) m0 _ _ hc.f_1ac80 (by decide) hc.d_1ac80 h11
    (by rw [show bv_signed (0x8 : BitVec 12) = 8 from by decide]; omega) h12 hfl1
    (by omega) (by omega)
  refine evt_step hs2 ?_
  rw [show (0x1ac80 : Int) + 4 = 0x1ac84 from by omega]
  -- 0x1ac84  addi a5, x0, 25
  refine evt_step (mstep_mkst (step_addi_at segs regs (wa 0x1ac84) _ (seg_rom segs)
    0x01900793 15 0 0x19 (wa 25) hc.f_1ac84 (by decide) hc.d_1ac84 (by decide)
    (by rw [hz, v_addi_wa,
      show bv_signed (0x19 : BitVec 12) = 25 from by decide,
      show (0 : Int) + 25 = 25 from by omega]))) ?_
  rw [v_addi_wa, show (0x1ac84 : Int) + 4 = 0x1ac88 from by omega]
  have g11 : getr (regupd regs 15 (wa 25)) 11 = wa (dstA regs0 + k) := by
    rw [getr_other regs 15 _ 11 (by decide)]; exact h11
  have g12 : getr (regupd regs 15 (wa 25)) 12 = wa (splatZ 4 (fillCz regs0)) := by
    rw [getr_other regs 15 _ 12 (by decide)]; exact h12
  have g13 : getr (regupd regs 15 (wa 25)) 13 = wa (dstA regs0 + k + n4) := by
    rw [getr_other regs 15 _ 13 (by decide)]; exact h13
  have g14 : getr (regupd regs 15 (wa 25)) 14 = wa n4 := by
    rw [getr_other regs 15 _ 14 (by decide)]; exact h14
  have g15 : getr (regupd regs 15 (wa 25)) 15 = wa 25 :=
    getr_same regs 15 _ (by decide)
  -- 0x1ac88  sw a2, -12(a3)
  obtain ⟨hs3, hfl3⟩ := sw_step segs regs0 _ 0x1ac88 0xfec6aa23 13 0xff4
    (dstA regs0 + k + n4) (k + n4 - 12) m0 _ _ hc.f_1ac88 (by decide) hc.d_1ac88 g13
    (by rw [show bv_signed (0xff4 : BitVec 12) = -12 from by decide]; omega) g12 hfl2
    (by omega) (by omega)
  refine evt_step hs3 ?_
  rw [show (0x1ac88 : Int) + 4 = 0x1ac8c from by omega]
  -- 0x1ac8c  sw a2, -8(a3)
  obtain ⟨hs4, hfl4⟩ := sw_step segs regs0 _ 0x1ac8c 0xfec6ac23 13 0xff8
    (dstA regs0 + k + n4) (k + n4 - 8) m0 _ _ hc.f_1ac8c (by decide) hc.d_1ac8c g13
    (by rw [show bv_signed (0xff8 : BitVec 12) = -8 from by decide]; omega) g12 hfl3
    (by omega) (by omega)
  refine evt_step hs4 ?_
  rw [show (0x1ac8c : Int) + 4 = 0x1ac90 from by omega]
  -- 0x1ac90  bltu a4, a5, +0x68
  have hbr : branch_taken branch_cond.BC_LTU
      (getr (regupd regs 15 (wa 25)) 14) (getr (regupd regs 15 (wa 25)) 15)
      = decide (n4 < 25) := by
    rw [g14, g15, bltu_wa _ _ (by omega) (by omega) (by omega) (by omega)]
  have hfrA : ∀ r : reg, r ∉ memset_clobber →
      getr (regupd regs 15 (wa 25)) r = getr regs0 r :=
    fr_upd 15 _ (by decide) hfr
  cases hlt : decide (n4 < 25) with
  | true =>
    have hn25 : n4 < 25 := of_decide_eq_true hlt
    refine evt_step (mstep_mkst (step_branch_tk_gen segs _ (wa 0x1ac90) _ (seg_rom segs)
      0x06f76463 .BC_LTU 14 15 0x68 hc.f_1ac90 (by decide) hc.d_1ac90
      (by rw [hbr, hlt]))) ?_
    rw [show bv_signed (0x68 : BitVec 13) = 104 from by decide, btgt_wa,
      show (0x1ac90 : Int) + 104 = 0x1acf8 from by omega]
    refine exit_ret segs hc regs0 _ m0 _ _ hfrA hfl4 ?_
    intro j hj0 hjn
    by_cases hA : (0 ≤ j ∧ j < 4) ∨ (dstN regs0 - 4 ≤ j ∧ j < dstN regs0)
        ∨ (k ≤ j ∧ j < k + 4) ∨ (k + n4 - 4 ≤ j ∧ j < k + n4)
    · exact Or.inl (Or.inl (Or.inl (Or.inl (hcov j hA))))
    · by_cases hB : k + 4 ≤ j ∧ j < k + 8
      · exact Or.inl (Or.inl (Or.inl (Or.inr (by omega))))
      · by_cases hC : k + 8 ≤ j ∧ j < k + 12
        · exact Or.inl (Or.inl (Or.inr (by omega)))
        · by_cases hD : k + n4 - 12 ≤ j ∧ j < k + n4 - 8
          · exact Or.inl (Or.inr (by omega))
          · exact Or.inr (by omega)
  | false =>
    have hn25 : 25 ≤ n4 := by
      have := of_decide_eq_false hlt
      omega
    refine evt_step (mstep_mkst (step_branch_ft_gen segs _ (wa 0x1ac90) _ (seg_rom segs)
      0x06f76463 .BC_LTU 14 15 0x68 hc.f_1ac90 (by decide) hc.d_1ac90
      (by rw [hbr, hlt]))) ?_
    rw [v_addi_wa, show (0x1ac90 : Int) + 4 = 0x1ac94 from by omega]
    refine next _ _ _ hfrA hfl4 g11 g12 g13 g14 g15 hn25 ?_
    intro j hj
    by_cases hA : (0 ≤ j ∧ j < 4) ∨ (dstN regs0 - 4 ≤ j ∧ j < dstN regs0)
        ∨ (k ≤ j ∧ j < k + 4) ∨ (k + n4 - 4 ≤ j ∧ j < k + n4)
    · exact Or.inl (Or.inl (Or.inl (Or.inl (hcov j hA))))
    · by_cases hB : k + 4 ≤ j ∧ j < k + 8
      · exact Or.inl (Or.inl (Or.inl (Or.inr (by omega))))
      · by_cases hC : k + 8 ≤ j ∧ j < k + 12
        · exact Or.inl (Or.inl (Or.inr (by omega)))
        · by_cases hD : k + n4 - 12 ≤ j ∧ j < k + n4 - 8
          · exact Or.inl (Or.inr (by omega))
          · exact Or.inr (by omega)






/-- Eight `sw`s leave the coverage predicate left-nested; this turns the flat
disjunction `omega` produces into that shape. -/
private theorem orL8 {P A1 A2 A3 A4 A5 A6 A7 A8 : Prop}
    (h : P ∨ A1 ∨ A2 ∨ A3 ∨ A4 ∨ A5 ∨ A6 ∨ A7 ∨ A8) :
    ((((((((P ∨ A1) ∨ A2) ∨ A3) ∨ A4) ∨ A5) ∨ A6) ∨ A7) ∨ A8) := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-! ## `0x1ac94` … `0x1acc4`: the third and fourth word quads and the `n < 32` exit

The twin of `R_memset.v:279-294`. -/

private theorem blk_1ac94 (segs : List Segment) (hc : Code segs) (regs0 : bvmap 5 word)
    (m0 : word → Option byte) (k n4 : Int)
    (next : ∀ (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop)
        (k4 : Int),
      (∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r) →
      Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q →
      getr regs 11 = wa (dstA regs0 + k) →
      getr regs 12 = wa (splatZ 4 (fillCz regs0)) →
      getr regs 13 = wa (dstA regs0 + k + n4) →
      getr regs 14 = wa (n4 - k4 - 24) →
      getr regs 15 = wa (k4 + 24) →
      getr regs 16 = wa 32 →
      (k4 = 0 ∨ k4 = 4) → (dstA regs0 + k + k4 + 24) % 8 = 0 →
      32 ≤ n4 - k4 - 24 →
      (∀ j : Int, (0 ≤ j ∧ j < k + 28) ∨ (k + n4 - 28 ≤ j ∧ j < dstN regs0) → Q j) →
      evt segs (Post segs regs0 m0) (mkst regs (wa 0x1acc8) m1 (seg_rom segs)))
    (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop)
    (hfr : ∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r)
    (hfl : Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q)
    (h11 : getr regs 11 = wa (dstA regs0 + k))
    (h12 : getr regs 12 = wa (splatZ 4 (fillCz regs0)))
    (h13 : getr regs 13 = wa (dstA regs0 + k + n4))
    (h14 : getr regs 14 = wa n4)
    (_h15 : getr regs 15 = wa 25)
    (hk0 : 0 ≤ k) (hk3 : k ≤ 3) (hal : (dstA regs0 + k) % 4 = 0)
    (hq4 : ∃ q : Int, n4 = 4 * q) (hn425 : 25 ≤ n4)
    (hkn : k + n4 ≤ dstN regs0) (hn4lo : dstN regs0 - k - 3 ≤ n4)
    (hcov : ∀ j : Int, (0 ≤ j ∧ j < 4) ∨ (dstN regs0 - 4 ≤ j ∧ j < dstN regs0)
      ∨ (k ≤ j ∧ j < k + 12) ∨ (k + n4 - 12 ≤ j ∧ j < k + n4) → Q j) :
    evt segs (Post segs regs0 m0) (mkst regs (wa 0x1ac94) m1 (seg_rom segs)) := by
  have hA0 : 0 ≤ dstA regs0 := hfl.wr.1
  have hAn : dstA regs0 + dstN regs0 ≤ 2 ^ 64 := hfl.wr.2.1
  have hnr := dstN_range regs0
  obtain ⟨q, hqv⟩ := hq4
  have hn428 : 28 ≤ n4 := by omega
  have hz : getr regs 0 = wa 0 := getr_zero regs
  -- 0x1ac94  sw a2, 12(a1)
  obtain ⟨hs1, hfl1⟩ := sw_step segs regs0 regs 0x1ac94 0x00c5a623 11 0xc
    (dstA regs0 + k) (k + 12) m0 m1 Q hc.f_1ac94 (by decide) hc.d_1ac94 h11
    (by rw [show bv_signed (0xc : BitVec 12) = 12 from by decide]; omega) h12 hfl
    (by omega) (by omega)
  refine evt_step hs1 ?_
  rw [show (0x1ac94 : Int) + 4 = 0x1ac98 from by omega]
  -- 0x1ac98  sw a2, 16(a1)
  obtain ⟨hs2, hfl2⟩ := sw_step segs regs0 regs 0x1ac98 0x00c5a823 11 0x10
    (dstA regs0 + k) (k + 16) m0 _ _ hc.f_1ac98 (by decide) hc.d_1ac98 h11
    (by rw [show bv_signed (0x10 : BitVec 12) = 16 from by decide]; omega) h12 hfl1
    (by omega) (by omega)
  refine evt_step hs2 ?_
  rw [show (0x1ac98 : Int) + 4 = 0x1ac9c from by omega]
  -- 0x1ac9c  sw a2, 20(a1)
  obtain ⟨hs3, hfl3⟩ := sw_step segs regs0 regs 0x1ac9c 0x00c5aa23 11 0x14
    (dstA regs0 + k) (k + 20) m0 _ _ hc.f_1ac9c (by decide) hc.d_1ac9c h11
    (by rw [show bv_signed (0x14 : BitVec 12) = 20 from by decide]; omega) h12 hfl2
    (by omega) (by omega)
  refine evt_step hs3 ?_
  rw [show (0x1ac9c : Int) + 4 = 0x1aca0 from by omega]
  -- 0x1aca0  sw a2, 24(a1)
  obtain ⟨hs4, hfl4⟩ := sw_step segs regs0 regs 0x1aca0 0x00c5ac23 11 0x18
    (dstA regs0 + k) (k + 24) m0 _ _ hc.f_1aca0 (by decide) hc.d_1aca0 h11
    (by rw [show bv_signed (0x18 : BitVec 12) = 24 from by decide]; omega) h12 hfl3
    (by omega) (by omega)
  refine evt_step hs4 ?_
  rw [show (0x1aca0 : Int) + 4 = 0x1aca4 from by omega]
  -- 0x1aca4  andi a5, a1, 4 — the one step that is not bookkeeping
  obtain ⟨k4, hk4, hm8, hand⟩ := k4_val (dstA regs0 + k) (by omega) (by omega) hal
  refine evt_step (mstep_mkst (step_andi_at segs regs (wa 0x1aca4) _ (seg_rom segs)
    0x0045f793 15 11 0x4 (wa k4) hc.f_1aca4 (by decide) hc.d_1aca4 (by decide)
    (by rw [h11, show bv_signed (0x4 : BitVec 12) = 4 from by decide]; exact hand))) ?_
  rw [v_addi_wa, show (0x1aca4 : Int) + 4 = 0x1aca8 from by omega]
  -- 0x1aca8  addi a6, x0, 32
  refine evt_step (mstep_mkst (step_addi_at segs _ (wa 0x1aca8) _ (seg_rom segs)
    0x02000813 16 0 0x20 (wa 32) hc.f_1aca8 (by decide) hc.d_1aca8 (by decide)
    (by rw [getr_other regs 15 _ 0 (by decide), hz, v_addi_wa,
      show bv_signed (0x20 : BitVec 12) = 32 from by decide,
      show (0 : Int) + 32 = 32 from by omega]))) ?_
  rw [v_addi_wa, show (0x1aca8 : Int) + 4 = 0x1acac from by omega]
  -- 0x1acac  addi a5, a5, 24
  refine evt_step (mstep_mkst (step_addi_at segs _ (wa 0x1acac) _ (seg_rom segs)
    0x01878793 15 15 0x18 (wa (k4 + 24)) hc.f_1acac (by decide) hc.d_1acac (by decide)
    (by rw [getr_other _ 16 _ 15 (by decide), getr_same regs 15 _ (by decide), v_addi_wa,
      show bv_signed (0x18 : BitVec 12) = 24 from by decide]))) ?_
  rw [v_addi_wa, show (0x1acac : Int) + 4 = 0x1acb0 from by omega]
  -- 0x1acb0  sub a4, a4, a5
  refine evt_step (mstep_mkst (step_sub_at segs _ (wa 0x1acb0) _ (seg_rom segs)
    0x40f70733 14 14 15 (wa (n4 - k4 - 24)) hc.f_1acb0 (by decide) hc.d_1acb0 (by decide)
    (by rw [getr_other _ 15 _ 14 (by decide), getr_other _ 16 _ 14 (by decide),
      getr_other regs 15 _ 14 (by decide), h14, getr_same _ 15 _ (by decide), v_sub_wa,
      show n4 - (k4 + 24) = n4 - k4 - 24 from by omega]))) ?_
  rw [v_addi_wa, show (0x1acb0 : Int) + 4 = 0x1acb4 from by omega]
  -- the register file after the four writes
  have h11' : getr (regupd (regupd (regupd (regupd regs 15 (wa k4)) 16 (wa 32)) 15
      (wa (k4 + 24))) 14 (wa (n4 - k4 - 24))) 11 = wa (dstA regs0 + k) := by
    rw [getr_other _ 14 _ 11 (by decide), getr_other _ 15 _ 11 (by decide),
      getr_other _ 16 _ 11 (by decide), getr_other regs 15 _ 11 (by decide)]
    exact h11
  have h12' : getr (regupd (regupd (regupd (regupd regs 15 (wa k4)) 16 (wa 32)) 15
      (wa (k4 + 24))) 14 (wa (n4 - k4 - 24))) 12 = wa (splatZ 4 (fillCz regs0)) := by
    rw [getr_other _ 14 _ 12 (by decide), getr_other _ 15 _ 12 (by decide),
      getr_other _ 16 _ 12 (by decide), getr_other regs 15 _ 12 (by decide)]
    exact h12
  have h13' : getr (regupd (regupd (regupd (regupd regs 15 (wa k4)) 16 (wa 32)) 15
      (wa (k4 + 24))) 14 (wa (n4 - k4 - 24))) 13 = wa (dstA regs0 + k + n4) := by
    rw [getr_other _ 14 _ 13 (by decide), getr_other _ 15 _ 13 (by decide),
      getr_other _ 16 _ 13 (by decide), getr_other regs 15 _ 13 (by decide)]
    exact h13
  have h14' : getr (regupd (regupd (regupd (regupd regs 15 (wa k4)) 16 (wa 32)) 15
      (wa (k4 + 24))) 14 (wa (n4 - k4 - 24))) 14 = wa (n4 - k4 - 24) :=
    getr_same _ 14 _ (by decide)
  have h15' : getr (regupd (regupd (regupd (regupd regs 15 (wa k4)) 16 (wa 32)) 15
      (wa (k4 + 24))) 14 (wa (n4 - k4 - 24))) 15 = wa (k4 + 24) := by
    rw [getr_other _ 14 _ 15 (by decide), getr_same _ 15 _ (by decide)]
  have h16' : getr (regupd (regupd (regupd (regupd regs 15 (wa k4)) 16 (wa 32)) 15
      (wa (k4 + 24))) 14 (wa (n4 - k4 - 24))) 16 = wa 32 := by
    rw [getr_other _ 14 _ 16 (by decide), getr_other _ 15 _ 16 (by decide),
      getr_same _ 16 _ (by decide)]
  have hfrA : ∀ r : reg, r ∉ memset_clobber →
      getr (regupd (regupd (regupd (regupd regs 15 (wa k4)) 16 (wa 32)) 15
        (wa (k4 + 24))) 14 (wa (n4 - k4 - 24))) r = getr regs0 r :=
    fr_upd 14 _ (by decide) (fr_upd 15 _ (by decide)
      (fr_upd 16 _ (by decide) (fr_upd 15 _ (by decide) hfr)))
  -- 0x1acb4  sw a2, -28(a3)
  obtain ⟨hs5, hfl5⟩ := sw_step segs regs0 _ 0x1acb4 0xfec6a223 13 0xfe4
    (dstA regs0 + k + n4) (k + n4 - 28) m0 _ _ hc.f_1acb4 (by decide) hc.d_1acb4 h13'
    (by rw [show bv_signed (0xfe4 : BitVec 12) = -28 from by decide]; omega) h12' hfl4
    (by omega) (by omega)
  refine evt_step hs5 ?_
  rw [show (0x1acb4 : Int) + 4 = 0x1acb8 from by omega]
  -- 0x1acb8  sw a2, -24(a3)
  obtain ⟨hs6, hfl6⟩ := sw_step segs regs0 _ 0x1acb8 0xfec6a423 13 0xfe8
    (dstA regs0 + k + n4) (k + n4 - 24) m0 _ _ hc.f_1acb8 (by decide) hc.d_1acb8 h13'
    (by rw [show bv_signed (0xfe8 : BitVec 12) = -24 from by decide]; omega) h12' hfl5
    (by omega) (by omega)
  refine evt_step hs6 ?_
  rw [show (0x1acb8 : Int) + 4 = 0x1acbc from by omega]
  -- 0x1acbc  sw a2, -20(a3)
  obtain ⟨hs7, hfl7⟩ := sw_step segs regs0 _ 0x1acbc 0xfec6a623 13 0xfec
    (dstA regs0 + k + n4) (k + n4 - 20) m0 _ _ hc.f_1acbc (by decide) hc.d_1acbc h13'
    (by rw [show bv_signed (0xfec : BitVec 12) = -20 from by decide]; omega) h12' hfl6
    (by omega) (by omega)
  refine evt_step hs7 ?_
  rw [show (0x1acbc : Int) + 4 = 0x1acc0 from by omega]
  -- 0x1acc0  sw a2, -16(a3)
  obtain ⟨hs8, hfl8⟩ := sw_step segs regs0 _ 0x1acc0 0xfec6a823 13 0xff0
    (dstA regs0 + k + n4) (k + n4 - 16) m0 _ _ hc.f_1acc0 (by decide) hc.d_1acc0 h13'
    (by rw [show bv_signed (0xff0 : BitVec 12) = -16 from by decide]; omega) h12' hfl7
    (by omega) (by omega)
  refine evt_step hs8 ?_
  rw [show (0x1acc0 : Int) + 4 = 0x1acc4 from by omega]
  -- 0x1acc4  bltu a4, a6, +0x34
  have hbr : branch_taken branch_cond.BC_LTU
      (getr (regupd (regupd (regupd (regupd regs 15 (wa k4)) 16 (wa 32)) 15
        (wa (k4 + 24))) 14 (wa (n4 - k4 - 24))) 14)
      (getr (regupd (regupd (regupd (regupd regs 15 (wa k4)) 16 (wa 32)) 15
        (wa (k4 + 24))) 14 (wa (n4 - k4 - 24))) 16)
      = decide (n4 - k4 - 24 < 32) := by
    rw [h14', h16', bltu_wa _ _ (by omega) (by omega) (by omega) (by omega)]
  cases hlt : decide (n4 - k4 - 24 < 32) with
  | true =>
    have hsmall : n4 - k4 - 24 < 32 := of_decide_eq_true hlt
    refine evt_step (mstep_mkst (step_branch_tk_gen segs _ (wa 0x1acc4) _ (seg_rom segs)
      0x03076a63 .BC_LTU 14 16 0x34 hc.f_1acc4 (by decide) hc.d_1acc4
      (by rw [hbr, hlt]))) ?_
    rw [show bv_signed (0x34 : BitVec 13) = 52 from by decide, btgt_wa,
      show (0x1acc4 : Int) + 52 = 0x1acf8 from by omega]
    refine exit_ret segs hc regs0 _ m0 _ _ hfrA hfl8 ?_
    intro j h1 h2
    refine orL8 ?_
    by_cases hb : (0 ≤ j ∧ j < 4) ∨ (dstN regs0 - 4 ≤ j ∧ j < dstN regs0)
        ∨ (k ≤ j ∧ j < k + 12) ∨ (k + n4 - 12 ≤ j ∧ j < k + n4)
    · exact Or.inl (hcov j hb)
    · exact Or.inr (by omega)
  | false =>
    have hbig : 32 ≤ n4 - k4 - 24 := by
      have := of_decide_eq_false hlt
      omega
    refine evt_step (mstep_mkst (step_branch_ft_gen segs _ (wa 0x1acc4) _ (seg_rom segs)
      0x03076a63 .BC_LTU 14 16 0x34 hc.f_1acc4 (by decide) hc.d_1acc4
      (by rw [hbr, hlt]))) ?_
    rw [v_addi_wa, show (0x1acc4 : Int) + 4 = 0x1acc8 from by omega]
    refine next _ _ _ k4 hfrA hfl8 h11' h12' h13' h14' h15' h16' hk4 hm8 hbig ?_
    intro j hj
    refine orL8 ?_
    by_cases hb : (0 ≤ j ∧ j < 4) ∨ (dstN regs0 - 4 ≤ j ∧ j < dstN regs0)
        ∨ (k ≤ j ∧ j < k + 12) ∨ (k + n4 - 12 ≤ j ∧ j < k + n4)
    · exact Or.inl (hcov j hb)
    · exact Or.inr (by omega)




/-! `0x1acc8` … `0x1acd8` of musl `memset`: the splat from four bytes to eight
and the entry into the 32-byte loop. The twin of `R_memset.v:295-300`. -/



/-- `or` with the writeback value named. -/
private theorem step_or_at (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg) (v : word)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op .ALU_OR rd rs1 rs2, 4))
    (hrd : bv_eqb rd 0 = false)
    (hv : v_or (getr regs rs1) (getr regs rs2) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_or segs regs pc mem rom w rd rs1 rs2 hf he hd, hrd, hv]
  rfl

private theorem blk_1acc8 (segs : List Segment) (hc : Code segs) (regs0 : bvmap 5 word)
    (m0 : word → Option byte) (k n4 k4 : Int)
    (loop : ∀ (K : Nat) (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop)
        (p r e : Int),
      r.toNat = K →
      (∀ rr : reg, rr ∉ memset_clobber → getr regs rr = getr regs0 rr) →
      Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q →
      getr regs 11 = wa (dstA regs0 + p) →
      getr regs 12 = wa (splatZ 8 (fillCz regs0)) →
      getr regs 13 = wa 31 →
      getr regs 14 = wa r →
      0 ≤ p → 32 ≤ r → (∃ q : Int, r = 4 * q) → p + r ≤ dstN regs0 →
      e + 28 ≤ p + r →
      (∀ j : Int, (0 ≤ j ∧ j < p) ∨ (e ≤ j ∧ j < dstN regs0) → Q j) →
      evt segs (Post segs regs0 m0) (mkst regs (wa 0x1acdc) m1 (seg_rom segs)))
    (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop)
    (hfr : ∀ r : reg, r ∉ memset_clobber → getr regs r = getr regs0 r)
    (hfl : Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q)
    (h11 : getr regs 11 = wa (dstA regs0 + k))
    (h12 : getr regs 12 = wa (splatZ 4 (fillCz regs0)))
    (h14 : getr regs 14 = wa (n4 - k4 - 24))
    (h15 : getr regs 15 = wa (k4 + 24))
    (hk4 : k4 = 0 ∨ k4 = 4)
    (hr32 : 32 ≤ n4 - k4 - 24)
    (hk0 : 0 ≤ k) (hk3 : k ≤ 3) (hq4 : ∃ q : Int, n4 = 4 * q)
    (hkn : k + n4 ≤ dstN regs0) (hn4lo : dstN regs0 - k - 3 ≤ n4)
    (hcov : ∀ j : Int, (0 ≤ j ∧ j < k + 28) ∨ (k + n4 - 28 ≤ j ∧ j < dstN regs0) → Q j) :
    evt segs (Post segs regs0 m0) (mkst regs (wa 0x1acc8) m1 (seg_rom segs)) := by
  have hcr := fillCz_range regs0
  have hs4 : 0 ≤ splatZ 4 (fillCz regs0) ∧ splatZ 4 (fillCz regs0) < 2 ^ 64 := by
    have h1 : 0 ≤ splatZ 4 (fillCz regs0) := splatZ_nonneg 4 _ hcr.1
    have h2 : splatZ 4 (fillCz regs0) = fillCz regs0 * 0x01010101 := splat4 _
    omega
  obtain ⟨q, hq⟩ := hq4
  have g14 : reg_get regs 14 = wa (n4 - k4 - 24) := h14
  -- 0x1acc8  slli a2, a2, 32
  refine evt_step (mstep_mkst (step_slli_at segs regs (wa 0x1acc8) m1 (seg_rom segs)
    0x02061613 12 12 32 (v_slli (wa (splatZ 4 (fillCz regs0))) 32) hc.f_1acc8 (by decide)
    hc.d_1acc8 (by decide)
    (by rw [show bv_unsigned (32 : BitVec 6) = (32 : Int) from by decide, h12]))) ?_
  rw [v_addi_wa, show (0x1acc8 : Int) + 4 = 0x1accc from by omega]
  -- 0x1accc  add a1, a1, a5
  refine evt_step (mstep_mkst (step_add_at segs _ (wa 0x1accc) m1 (seg_rom segs)
    0x00f585b3 11 11 15 (wa (dstA regs0 + (k + k4 + 24))) hc.f_1accc (by decide)
    hc.d_1accc (by decide)
    (by getr_resolve
        rw [show reg_get regs 11 = wa (dstA regs0 + k) from h11,
          show reg_get regs 15 = wa (k4 + 24) from h15, v_add_wa,
          show dstA regs0 + k + (k4 + 24) = dstA regs0 + (k + k4 + 24) from by omega]))) ?_
  rw [v_addi_wa, show (0x1accc : Int) + 4 = 0x1acd0 from by omega]
  -- 0x1acd0  srli a3, a2, 32
  refine evt_step (mstep_mkst (step_srli_at segs _ (wa 0x1acd0) m1 (seg_rom segs)
    0x02065693 13 12 32 (v_srli (v_slli (wa (splatZ 4 (fillCz regs0))) 32) 32)
    hc.f_1acd0 (by decide) hc.d_1acd0 (by decide)
    (by rw [show bv_unsigned (32 : BitVec 6) = (32 : Int) from by decide]
        getr_resolve
        try rfl))) ?_
  rw [v_addi_wa, show (0x1acd0 : Int) + 4 = 0x1acd4 from by omega]
  -- 0x1acd4  or a2, a2, a3
  refine evt_step (mstep_mkst (step_or_at segs _ (wa 0x1acd4) m1 (seg_rom segs)
    0x00d66633 12 12 13 (wa (splatZ 8 (fillCz regs0))) hc.f_1acd4 (by decide)
    hc.d_1acd4 (by decide)
    (by getr_resolve; exact splat8_or (fillCz regs0) hcr.1 hcr.2))) ?_
  rw [v_addi_wa, show (0x1acd4 : Int) + 4 = 0x1acd8 from by omega]
  -- 0x1acd8  addi a3, x0, 31
  refine evt_step (mstep_mkst (step_addi_at segs _ (wa 0x1acd8) m1 (seg_rom segs)
    0x01f00693 13 0 0x1f (wa 31) hc.f_1acd8 (by decide) hc.d_1acd8 (by decide)
    (by rw [show bv_signed (0x1f : BitVec 12) = (31 : Int) from by decide]
        getr_resolve
        show v_addi (wa 0) 31 = wa 31
        rw [v_addi_wa, show (0 : Int) + 31 = 31 from by omega]))) ?_
  rw [v_addi_wa, show (0x1acd8 : Int) + 4 = 0x1acdc from by omega]
  refine loop (n4 - k4 - 24).toNat _ _ _ (k + k4 + 24) (n4 - k4 - 24) (k + n4 - 28) rfl
    (fr_upd 13 _ (by decide) (fr_upd 12 _ (by decide) (fr_upd 13 _ (by decide)
      (fr_upd 11 _ (by decide) (fr_upd 12 _ (by decide) hfr)))))
    hfl (by getr_resolve; try rfl) (by getr_resolve; try rfl)
    (by getr_resolve; try rfl) (by getr_resolve; exact g14)
    (by omega) (by omega) ⟨q - k4 / 4 - 6, by rcases hk4 with h | h <;> omega⟩
    (by omega) (by omega) ?_
  intro j hj
  exact hcov j (by rcases hj with h | h <;> rcases hk4 with h4 | h4 <;> omega)






/-! ## `0x1acdc` … `0x1acf4`: the 32-byte `sd` loop

The twin of `R_memset.v:190-220` (`memset_loop`). The Rocq proof is
`induction K as [K IH] using lt_wf_ind` on the measure `Z.to_nat r`; here the
same recursion is an ordinary `Nat` induction on a bound `r.toNat ≤ K`, which
needs nothing outside core Lean. -/

private theorem loop_aux (segs : List Segment) (hc : Code segs) (regs0 : bvmap 5 word)
    (m0 : word → Option byte) (K : Nat) :
    ∀ (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop) (p r e : Int),
      r.toNat ≤ K →
      (∀ rr : reg, rr ∉ memset_clobber → getr regs rr = getr regs0 rr) →
      Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q →
      getr regs 11 = wa (dstA regs0 + p) →
      getr regs 12 = wa (splatZ 8 (fillCz regs0)) →
      getr regs 13 = wa 31 →
      getr regs 14 = wa r →
      0 ≤ p → 32 ≤ r → (∃ q : Int, r = 4 * q) → p + r ≤ dstN regs0 →
      e + 28 ≤ p + r →
      (∀ j : Int, (0 ≤ j ∧ j < p) ∨ (e ≤ j ∧ j < dstN regs0) → Q j) →
      evt segs (Post segs regs0 m0) (mkst regs (wa 0x1acdc) m1 (seg_rom segs)) := by
  induction K with
  | zero =>
    intro regs m1 Q p r e hK _ _ _ _ _ _ _ hr _ _ _ _
    exact absurd hK (by omega)
  | succ K IH =>
    intro regs m1 Q p r e hK hfr hfl h11 h12 h13 h14 hp hr hq4 hpr he hQ
    obtain ⟨hn0, hn1⟩ := dstN_range regs0
    obtain ⟨hA0, hA1⟩ := dstA_range regs0
    -- 0x1acdc  sd a2, 0(a1)
    obtain ⟨hs1, hfl1⟩ := sd_step segs regs0 regs 0x1acdc 0x00c5b023 11 0x0
      (dstA regs0 + p) p m0 m1 Q hc.f_1acdc (by decide) hc.d_1acdc h11
      (by rw [show bv_signed (0x0 : BitVec 12) = 0 from by decide]; omega) h12 hfl
      hp (by omega)
    refine evt_step hs1 ?_
    rw [show (0x1acdc : Int) + 4 = 0x1ace0 from by omega]
    -- 0x1ace0  sd a2, 8(a1)
    obtain ⟨hs2, hfl2⟩ := sd_step segs regs0 regs 0x1ace0 0x00c5b423 11 0x8
      (dstA regs0 + p) (p + 8) m0 _ _ hc.f_1ace0 (by decide) hc.d_1ace0 h11
      (by rw [show bv_signed (0x8 : BitVec 12) = 8 from by decide]; omega) h12 hfl1
      (by omega) (by omega)
    refine evt_step hs2 ?_
    rw [show (0x1ace0 : Int) + 4 = 0x1ace4 from by omega]
    -- 0x1ace4  sd a2, 16(a1)
    obtain ⟨hs3, hfl3⟩ := sd_step segs regs0 regs 0x1ace4 0x00c5b823 11 0x10
      (dstA regs0 + p) (p + 16) m0 _ _ hc.f_1ace4 (by decide) hc.d_1ace4 h11
      (by rw [show bv_signed (0x10 : BitVec 12) = 16 from by decide]; omega) h12 hfl2
      (by omega) (by omega)
    refine evt_step hs3 ?_
    rw [show (0x1ace4 : Int) + 4 = 0x1ace8 from by omega]
    -- 0x1ace8  sd a2, 24(a1)
    obtain ⟨hs4, hfl4⟩ := sd_step segs regs0 regs 0x1ace8 0x00c5bc23 11 0x18
      (dstA regs0 + p) (p + 24) m0 _ _ hc.f_1ace8 (by decide) hc.d_1ace8 h11
      (by rw [show bv_signed (0x18 : BitVec 12) = 24 from by decide]; omega) h12 hfl3
      (by omega) (by omega)
    refine evt_step hs4 ?_
    rw [show (0x1ace8 : Int) + 4 = 0x1acec from by omega]
    -- 0x1acec  addi a4, a4, -32
    refine evt_step (mstep_mkst (step_addi_at segs regs (wa 0x1acec) _ (seg_rom segs)
      0xfe070713 14 14 0xfe0 (wa (r - 32)) hc.f_1acec (by decide) hc.d_1acec (by decide)
      (by rw [h14, v_addi_wa, show bv_signed (0xfe0 : BitVec 12) = -32 from by decide,
        show r + -32 = r - 32 from by omega]))) ?_
    rw [v_addi_wa, show (0x1acec : Int) + 4 = 0x1acf0 from by omega]
    -- 0x1acf0  addi a1, a1, 32
    have h11' : getr (regupd regs 14 (wa (r - 32))) 11 = wa (dstA regs0 + p) := by
      rw [getr_other regs 14 _ 11 (by decide)]; exact h11
    refine evt_step (mstep_mkst (step_addi_at segs _ (wa 0x1acf0) _ (seg_rom segs)
      0x02058593 11 11 0x20 (wa (dstA regs0 + (p + 32))) hc.f_1acf0 (by decide)
      hc.d_1acf0 (by decide)
      (by rw [h11', v_addi_wa, show bv_signed (0x20 : BitVec 12) = 32 from by decide,
        show dstA regs0 + p + 32 = dstA regs0 + (p + 32) from by omega]))) ?_
    rw [v_addi_wa, show (0x1acf0 : Int) + 4 = 0x1acf4 from by omega]
    -- the register file after the two `addi`s
    have g11 : getr (regupd (regupd regs 14 (wa (r - 32))) 11
        (wa (dstA regs0 + (p + 32)))) 11 = wa (dstA regs0 + (p + 32)) :=
      getr_same _ 11 _ (by decide)
    have g12 : getr (regupd (regupd regs 14 (wa (r - 32))) 11
        (wa (dstA regs0 + (p + 32)))) 12 = wa (splatZ 8 (fillCz regs0)) := by
      rw [getr_other _ 11 _ 12 (by decide), getr_other regs 14 _ 12 (by decide)]
      exact h12
    have g13 : getr (regupd (regupd regs 14 (wa (r - 32))) 11
        (wa (dstA regs0 + (p + 32)))) 13 = wa 31 := by
      rw [getr_other _ 11 _ 13 (by decide), getr_other regs 14 _ 13 (by decide)]
      exact h13
    have g14 : getr (regupd (regupd regs 14 (wa (r - 32))) 11
        (wa (dstA regs0 + (p + 32)))) 14 = wa (r - 32) := by
      rw [getr_other _ 11 _ 14 (by decide)]
      exact getr_same regs 14 _ (by decide)
    have hfrA : ∀ rr : reg, rr ∉ memset_clobber →
        getr (regupd (regupd regs 14 (wa (r - 32))) 11
          (wa (dstA regs0 + (p + 32)))) rr = getr regs0 rr :=
      fr_upd 11 _ (by decide) (fr_upd 14 _ (by decide) hfr)
    -- 0x1acf4  bltu a3, a4, -0x18
    have hbr : branch_taken branch_cond.BC_LTU
        (getr (regupd (regupd regs 14 (wa (r - 32))) 11
          (wa (dstA regs0 + (p + 32)))) 13)
        (getr (regupd (regupd regs 14 (wa (r - 32))) 11
          (wa (dstA regs0 + (p + 32)))) 14)
        = decide (31 < r - 32) := by
      rw [g13, g14, bltu_wa _ _ (by omega) (by omega) (by omega) (by omega)]
    obtain ⟨q, hq⟩ := hq4
    cases hlt : decide (31 < r - 32) with
    | true =>
      have hge : 64 ≤ r := by
        have := of_decide_eq_true hlt
        omega
      refine evt_step (mstep_mkst (step_branch_tk_gen segs _ (wa 0x1acf4) _ (seg_rom segs)
        0xfee6e4e3 .BC_LTU 13 14 0x1fe8 hc.f_1acf4 (by decide) hc.d_1acf4
        (by rw [hbr, hlt]))) ?_
      rw [show bv_signed (0x1fe8 : BitVec 13) = -24 from by decide, btgt_wa,
        show (0x1acf4 : Int) + -24 = 0x1acdc from by omega]
      refine IH _ _ _ (p + 32) (r - 32) e (by omega) hfrA hfl4 g11 g12 g13 g14
        (by omega) (by omega) ⟨q - 8, by omega⟩ (by omega) (by omega) ?_
      intro j hj
      rcases hj with ⟨hj0, hj1⟩ | ⟨hj0, hj1⟩
      · by_cases c1 : j < p
        · exact Or.inl (Or.inl (Or.inl (Or.inl (hQ j (Or.inl ⟨hj0, c1⟩)))))
        · by_cases c2 : j < p + 8
          · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩)))
          · by_cases c3 : j < p + 16
            · exact Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))
            · by_cases c4 : j < p + 24
              · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
              · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inl (hQ j (Or.inr ⟨hj0, hj1⟩)))))
    | false =>
      have hle : r - 32 ≤ 31 := by
        have := of_decide_eq_false hlt
        omega
      have hep : e ≤ p + 32 := by omega
      refine evt_step (mstep_mkst (step_branch_ft_gen segs _ (wa 0x1acf4) _ (seg_rom segs)
        0xfee6e4e3 .BC_LTU 13 14 0x1fe8 hc.f_1acf4 (by decide) hc.d_1acf4
        (by rw [hbr, hlt]))) ?_
      rw [v_addi_wa, show (0x1acf4 : Int) + 4 = 0x1acf8 from by omega]
      refine exit_ret segs hc regs0 _ m0 _ _ hfrA hfl4 ?_
      intro j hj0 hj1
      by_cases c1 : j < p
      · exact Or.inl (Or.inl (Or.inl (Or.inl (hQ j (Or.inl ⟨hj0, c1⟩)))))
      · by_cases c2 : j < p + 8
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩)))
        · by_cases c3 : j < p + 16
          · exact Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))
          · by_cases c4 : j < p + 24
            · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
            · by_cases c5 : j < p + 32
              · exact Or.inr ⟨by omega, by omega⟩
              · exact Or.inl (Or.inl (Or.inl (Or.inl
                  (hQ j (Or.inr ⟨by omega, hj1⟩)))))

private theorem loop_body (segs : List Segment) (hc : Code segs) (regs0 : bvmap 5 word)
    (m0 : word → Option byte) (K : Nat) :
    ∀ (regs : bvmap 5 word) (m1 : word → Option byte) (Q : Int → Prop) (p r e : Int),
      r.toNat = K →
      (∀ rr : reg, rr ∉ memset_clobber → getr regs rr = getr regs0 rr) →
      Fill segs (dstA regs0) (dstN regs0) (fillC regs0) m0 m1 Q →
      getr regs 11 = wa (dstA regs0 + p) →
      getr regs 12 = wa (splatZ 8 (fillCz regs0)) →
      getr regs 13 = wa 31 →
      getr regs 14 = wa r →
      0 ≤ p → 32 ≤ r → (∃ q : Int, r = 4 * q) → p + r ≤ dstN regs0 →
      e + 28 ≤ p + r →
      (∀ j : Int, (0 ≤ j ∧ j < p) ∨ (e ≤ j ∧ j < dstN regs0) → Q j) →
      evt segs (Post segs regs0 m0) (mkst regs (wa 0x1acdc) m1 (seg_rom segs)) := by
  intro regs m1 Q p r e hK hfr hfl h11 h12 h13 h14 hp hr hq hpr he hQ
  exact loop_aux segs hc regs0 m0 K regs m1 Q p r e (by omega) hfr hfl h11 h12 h13 h14
    hp hr hq hpr he hQ



/-! ## The image

The one place the real bytes of `fuzz_knock.plain` are read: every field is a
generated certificate of
`OssFuzzTheorems.libreac.fuzz_knock.Image.PlainCode`, which closes it by
`decide +kernel` against the image's own bytes and Lean's own decoder. -/

private theorem codeOk : Code Img0.rsegs where
  f_1ac04 := by rw [show wa 0x1ac04 = (0x1ac04 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac04
  d_1ac04 := Image.PlainCode.D_1ac04
  f_1ac08 := by rw [show wa 0x1ac08 = (0x1ac08 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac08
  d_1ac08 := Image.PlainCode.D_1ac08
  f_1ac0c := by rw [show wa 0x1ac0c = (0x1ac0c : word) from by decide +kernel]; exact Image.PlainCode.F_1ac0c
  d_1ac0c := Image.PlainCode.D_1ac0c
  f_1ac10 := by rw [show wa 0x1ac10 = (0x1ac10 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac10
  d_1ac10 := Image.PlainCode.D_1ac10
  f_1ac14 := by rw [show wa 0x1ac14 = (0x1ac14 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac14
  d_1ac14 := Image.PlainCode.D_1ac14
  f_1ac18 := by rw [show wa 0x1ac18 = (0x1ac18 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac18
  d_1ac18 := Image.PlainCode.D_1ac18
  f_1ac1c := by rw [show wa 0x1ac1c = (0x1ac1c : word) from by decide +kernel]; exact Image.PlainCode.F_1ac1c
  d_1ac1c := Image.PlainCode.D_1ac1c
  f_1ac20 := by rw [show wa 0x1ac20 = (0x1ac20 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac20
  d_1ac20 := Image.PlainCode.D_1ac20
  f_1ac24 := by rw [show wa 0x1ac24 = (0x1ac24 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac24
  d_1ac24 := Image.PlainCode.D_1ac24
  f_1ac28 := by rw [show wa 0x1ac28 = (0x1ac28 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac28
  d_1ac28 := Image.PlainCode.D_1ac28
  f_1ac2c := by rw [show wa 0x1ac2c = (0x1ac2c : word) from by decide +kernel]; exact Image.PlainCode.F_1ac2c
  d_1ac2c := Image.PlainCode.D_1ac2c
  f_1ac30 := by rw [show wa 0x1ac30 = (0x1ac30 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac30
  d_1ac30 := Image.PlainCode.D_1ac30
  f_1ac34 := by rw [show wa 0x1ac34 = (0x1ac34 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac34
  d_1ac34 := Image.PlainCode.D_1ac34
  f_1ac38 := by rw [show wa 0x1ac38 = (0x1ac38 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac38
  d_1ac38 := Image.PlainCode.D_1ac38
  f_1ac3c := by rw [show wa 0x1ac3c = (0x1ac3c : word) from by decide +kernel]; exact Image.PlainCode.F_1ac3c
  d_1ac3c := Image.PlainCode.D_1ac3c
  f_1ac40 := by rw [show wa 0x1ac40 = (0x1ac40 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac40
  d_1ac40 := Image.PlainCode.D_1ac40
  f_1ac44 := by rw [show wa 0x1ac44 = (0x1ac44 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac44
  d_1ac44 := Image.PlainCode.D_1ac44
  f_1ac48 := by rw [show wa 0x1ac48 = (0x1ac48 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac48
  d_1ac48 := Image.PlainCode.D_1ac48
  f_1ac4c := by rw [show wa 0x1ac4c = (0x1ac4c : word) from by decide +kernel]; exact Image.PlainCode.F_1ac4c
  d_1ac4c := Image.PlainCode.D_1ac4c
  f_1ac50 := by rw [show wa 0x1ac50 = (0x1ac50 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac50
  d_1ac50 := Image.PlainCode.D_1ac50
  f_1ac54 := by rw [show wa 0x1ac54 = (0x1ac54 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac54
  d_1ac54 := Image.PlainCode.D_1ac54
  f_1ac58 := by rw [show wa 0x1ac58 = (0x1ac58 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac58
  d_1ac58 := Image.PlainCode.D_1ac58
  f_1ac5c := by rw [show wa 0x1ac5c = (0x1ac5c : word) from by decide +kernel]; exact Image.PlainCode.F_1ac5c
  d_1ac5c := Image.PlainCode.D_1ac5c
  f_1ac60 := by rw [show wa 0x1ac60 = (0x1ac60 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac60
  d_1ac60 := Image.PlainCode.D_1ac60
  f_1ac64 := by rw [show wa 0x1ac64 = (0x1ac64 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac64
  d_1ac64 := Image.PlainCode.D_1ac64
  f_1ac68 := by rw [show wa 0x1ac68 = (0x1ac68 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac68
  d_1ac68 := Image.PlainCode.D_1ac68
  f_1ac6c := by rw [show wa 0x1ac6c = (0x1ac6c : word) from by decide +kernel]; exact Image.PlainCode.F_1ac6c
  d_1ac6c := Image.PlainCode.D_1ac6c
  f_1ac70 := by rw [show wa 0x1ac70 = (0x1ac70 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac70
  d_1ac70 := Image.PlainCode.D_1ac70
  f_1ac74 := by rw [show wa 0x1ac74 = (0x1ac74 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac74
  d_1ac74 := Image.PlainCode.D_1ac74
  f_1ac78 := by rw [show wa 0x1ac78 = (0x1ac78 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac78
  d_1ac78 := Image.PlainCode.D_1ac78
  f_1ac7c := by rw [show wa 0x1ac7c = (0x1ac7c : word) from by decide +kernel]; exact Image.PlainCode.F_1ac7c
  d_1ac7c := Image.PlainCode.D_1ac7c
  f_1ac80 := by rw [show wa 0x1ac80 = (0x1ac80 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac80
  d_1ac80 := Image.PlainCode.D_1ac80
  f_1ac84 := by rw [show wa 0x1ac84 = (0x1ac84 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac84
  d_1ac84 := Image.PlainCode.D_1ac84
  f_1ac88 := by rw [show wa 0x1ac88 = (0x1ac88 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac88
  d_1ac88 := Image.PlainCode.D_1ac88
  f_1ac8c := by rw [show wa 0x1ac8c = (0x1ac8c : word) from by decide +kernel]; exact Image.PlainCode.F_1ac8c
  d_1ac8c := Image.PlainCode.D_1ac8c
  f_1ac90 := by rw [show wa 0x1ac90 = (0x1ac90 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac90
  d_1ac90 := Image.PlainCode.D_1ac90
  f_1ac94 := by rw [show wa 0x1ac94 = (0x1ac94 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac94
  d_1ac94 := Image.PlainCode.D_1ac94
  f_1ac98 := by rw [show wa 0x1ac98 = (0x1ac98 : word) from by decide +kernel]; exact Image.PlainCode.F_1ac98
  d_1ac98 := Image.PlainCode.D_1ac98
  f_1ac9c := by rw [show wa 0x1ac9c = (0x1ac9c : word) from by decide +kernel]; exact Image.PlainCode.F_1ac9c
  d_1ac9c := Image.PlainCode.D_1ac9c
  f_1aca0 := by rw [show wa 0x1aca0 = (0x1aca0 : word) from by decide +kernel]; exact Image.PlainCode.F_1aca0
  d_1aca0 := Image.PlainCode.D_1aca0
  f_1aca4 := by rw [show wa 0x1aca4 = (0x1aca4 : word) from by decide +kernel]; exact Image.PlainCode.F_1aca4
  d_1aca4 := Image.PlainCode.D_1aca4
  f_1aca8 := by rw [show wa 0x1aca8 = (0x1aca8 : word) from by decide +kernel]; exact Image.PlainCode.F_1aca8
  d_1aca8 := Image.PlainCode.D_1aca8
  f_1acac := by rw [show wa 0x1acac = (0x1acac : word) from by decide +kernel]; exact Image.PlainCode.F_1acac
  d_1acac := Image.PlainCode.D_1acac
  f_1acb0 := by rw [show wa 0x1acb0 = (0x1acb0 : word) from by decide +kernel]; exact Image.PlainCode.F_1acb0
  d_1acb0 := Image.PlainCode.D_1acb0
  f_1acb4 := by rw [show wa 0x1acb4 = (0x1acb4 : word) from by decide +kernel]; exact Image.PlainCode.F_1acb4
  d_1acb4 := Image.PlainCode.D_1acb4
  f_1acb8 := by rw [show wa 0x1acb8 = (0x1acb8 : word) from by decide +kernel]; exact Image.PlainCode.F_1acb8
  d_1acb8 := Image.PlainCode.D_1acb8
  f_1acbc := by rw [show wa 0x1acbc = (0x1acbc : word) from by decide +kernel]; exact Image.PlainCode.F_1acbc
  d_1acbc := Image.PlainCode.D_1acbc
  f_1acc0 := by rw [show wa 0x1acc0 = (0x1acc0 : word) from by decide +kernel]; exact Image.PlainCode.F_1acc0
  d_1acc0 := Image.PlainCode.D_1acc0
  f_1acc4 := by rw [show wa 0x1acc4 = (0x1acc4 : word) from by decide +kernel]; exact Image.PlainCode.F_1acc4
  d_1acc4 := Image.PlainCode.D_1acc4
  f_1acc8 := by rw [show wa 0x1acc8 = (0x1acc8 : word) from by decide +kernel]; exact Image.PlainCode.F_1acc8
  d_1acc8 := Image.PlainCode.D_1acc8
  f_1accc := by rw [show wa 0x1accc = (0x1accc : word) from by decide +kernel]; exact Image.PlainCode.F_1accc
  d_1accc := Image.PlainCode.D_1accc
  f_1acd0 := by rw [show wa 0x1acd0 = (0x1acd0 : word) from by decide +kernel]; exact Image.PlainCode.F_1acd0
  d_1acd0 := Image.PlainCode.D_1acd0
  f_1acd4 := by rw [show wa 0x1acd4 = (0x1acd4 : word) from by decide +kernel]; exact Image.PlainCode.F_1acd4
  d_1acd4 := Image.PlainCode.D_1acd4
  f_1acd8 := by rw [show wa 0x1acd8 = (0x1acd8 : word) from by decide +kernel]; exact Image.PlainCode.F_1acd8
  d_1acd8 := Image.PlainCode.D_1acd8
  f_1acdc := by rw [show wa 0x1acdc = (0x1acdc : word) from by decide +kernel]; exact Image.PlainCode.F_1acdc
  d_1acdc := Image.PlainCode.D_1acdc
  f_1ace0 := by rw [show wa 0x1ace0 = (0x1ace0 : word) from by decide +kernel]; exact Image.PlainCode.F_1ace0
  d_1ace0 := Image.PlainCode.D_1ace0
  f_1ace4 := by rw [show wa 0x1ace4 = (0x1ace4 : word) from by decide +kernel]; exact Image.PlainCode.F_1ace4
  d_1ace4 := Image.PlainCode.D_1ace4
  f_1ace8 := by rw [show wa 0x1ace8 = (0x1ace8 : word) from by decide +kernel]; exact Image.PlainCode.F_1ace8
  d_1ace8 := Image.PlainCode.D_1ace8
  f_1acec := by rw [show wa 0x1acec = (0x1acec : word) from by decide +kernel]; exact Image.PlainCode.F_1acec
  d_1acec := Image.PlainCode.D_1acec
  f_1acf0 := by rw [show wa 0x1acf0 = (0x1acf0 : word) from by decide +kernel]; exact Image.PlainCode.F_1acf0
  d_1acf0 := Image.PlainCode.D_1acf0
  f_1acf4 := by rw [show wa 0x1acf4 = (0x1acf4 : word) from by decide +kernel]; exact Image.PlainCode.F_1acf4
  d_1acf4 := Image.PlainCode.D_1acf4
  f_1acf8 := by rw [show wa 0x1acf8 = (0x1acf8 : word) from by decide +kernel]; exact Image.PlainCode.F_1acf8
  d_1acf8 := Image.PlainCode.D_1acf8

/-! ## The walk, and the contract it closes -/

/-- The twin of `R_memset.v:222-301` (`memset_body`): the whole walk, from the
entry to the return, over the invariant of `Fill`. -/
private theorem memset_walk (segs : List Segment) (hc : Code segs)
    (regs0 : bvmap 5 word) (m0 : word → Option byte)
    (hwr : wr_at segs m0 (dstA regs0) (dstN regs0)) (hmi : mem_inv segs m0) :
    evt segs (Post segs regs0 m0) (mkst regs0 (wa 0x1ac04) m0 (seg_rom segs)) :=
  blk_1ac04 segs hc regs0 m0 hwr hmi
    (fun regs m1 Q hfr hfl h11 h12 h13 hn hcov =>
      blk_1ac1c segs hc regs0 m0
        (fun regs m1 Q hfr hfl h11 h12 h13 hn hcov =>
          blk_1ac34 segs hc regs0 m0
            (fun regs m1 Q hfr hfl h11 h12 h15 hn hcov =>
              blk_1ac44 segs hc regs0 m0
                (fun regs m1 Q k n4 hfr hfl h11 h12 h14 h15 hk0 hk3 hal hq4 hn44 hkn
                    hn4lo hcov =>
                  blk_1ac6c segs hc regs0 m0 k n4
                    (fun regs m1 Q hfr hfl h11 h12 h13 h14 h15 hn49 hcov =>
                      blk_1ac7c segs hc regs0 m0 k n4
                        (fun regs m1 Q hfr hfl h11 h12 h13 h14 h15 hn425 hcov =>
                          blk_1ac94 segs hc regs0 m0 k n4
                            (fun regs m1 Q k4 hfr hfl h11 h12 _h13 h14 h15 _h16 hk4 _hal8
                                hr32 hcov =>
                              blk_1acc8 segs hc regs0 m0 k n4 k4
                                (loop_body segs hc regs0 m0)
                                regs m1 Q hfr hfl h11 h12 h14 h15 hk4 hr32 hk0 hk3 hq4
                                hkn hn4lo hcov)
                            regs m1 Q hfr hfl h11 h12 h13 h14 h15 hk0 hk3 hal hq4 hn425
                            hkn hn4lo hcov)
                        regs m1 Q hfr hfl h11 h12 h13 h14 h15 hk0 hk3 hq4 hn49 hkn hn4lo
                        hcov)
                    regs m1 Q hfr hfl h11 h12 h14 h15 hk0 hk3 hal hq4 hn44 hkn hn4lo hcov)
                regs m1 Q hfr hfl h11 h12 h15 hn hcov)
            regs m1 Q hfr hfl h11 h12 h13 hn hcov)
        regs m1 Q hfr hfl h11 h12 h13 hn hcov)

/-- `lib/Prog/memset.v:4-5`, which is `R_memset.v:304-316` (`memset_spec`):
the destination's `rw_cells` gives the writable window the walk needs, and the
walk gives the contract. -/
theorem memset_holds : memset_contract := by
  intro regs m junk hrw hmi
  have hn : (0 : Int) ≤ dstN regs := (u64_range _).1
  have hwr : wr_at Img0.rsegs m (dstA regs) (dstN regs) := by
    have hr := u64_range (getr regs 12)
    have h := hrw.2
    simp only [cells_size, csize] at h
    have he : (((bv_unsigned (getr regs 12)).toNat + 0 : Nat) : Int)
        = bv_unsigned (getr regs 12) := by omega
    rw [he] at h
    exact h
  exact memset_walk Img0.rsegs codeOk regs m hwr hmi

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.memset
