-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Prog/memset.v
-- and its proof, oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/R_memset.v
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.memset_c
import OssFuzzTheorems.libreac.fuzz_knock.Image.PlainCode
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.MmapSim
import LinuxProcessSemantics.Common.StoreOk

/-! `lib/Prog/memset.v` (5 lines) and the proof it applies, `lib/R_memset.v`
(316 lines): musl's `memset` at `0x1ac04` of `fuzz_knock.plain`.

Paths without a repository are in theorem-labs/oss-verify-proofs-internal
`ossv/recipes` `9b0ac6f0e6`, under `projects/libreac/fuzz_knock/proofs/`.
`linux-process-semantics@ff0313ba4f:…` names the Lean model.

## What the Rocq proof carries that this one does not

`R_memset.v` states its loop invariant over `lib/Lib/Arr.v`'s `u8arr`, a
`list byte` the destination holds, together with `Spec/StrFun.v`'s `filled`,
which records the indices of that list already holding the byte. Neither file
has a Lean twin. Here the same invariant is `Fill` below: a destination of `n`
writable bytes, a set `Q` of offsets known to hold `c`, and the three frame
facts the contract's post-state needs. No byte list appears, because nothing in
the contract reads one: the post-state's `rw_cells` is recovered from `Q`
covering `[0, n)` (`Fill.finish`), which is what `filled_all` does in Rocq.

The walk itself follows `R_memset.v` instruction for instruction, and its loop
lemma `loop_body` keeps the invariant of `R_memset.v:190-220`. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.memset

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Sem
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
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.memset_c

/-- The image this walk runs in: `lib/Img0.v:3`, the four loaded segments of
`fuzz_knock.plain`. -/
private abbrev segs : List Segment := Img0.rsegs

/-! ## Addresses

`wa` (`lib/Lib/Mem.v:20`) is `Z_to_bv 64`, so it already reduces modulo `2^64`
and these three need no range side condition. -/

private theorem wa_wrap (x d : Int) : Z_to_bv 64 (bv_wrap 64 x + d) = wa (x + d) := by
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned]
  unfold bv_wrap
  rw [Int.add_emod, Int.emod_emod_of_dvd _ dvd_rfl, ← Int.add_emod]

private theorem wa_unsigned (x : Int) (h0 : 0 ≤ x) (h1 : x < 2 ^ 64) :
    bv_unsigned (wa x) = x := bv_unsigned_Z_to_bv_small x h0 h1

private theorem v_addi_wa (x d : Int) : v_addi (wa x) d = wa (x + d) := by
  unfold v_addi wa
  rw [Z_to_bv_unsigned]
  exact wa_wrap x d

private theorem v_add_wa (x y : Int) : v_add (wa x) (wa y) = wa (x + y) := by
  unfold v_add wa
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned]
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned]
  unfold bv_wrap
  rw [Int.add_emod, Int.emod_emod_of_dvd _ dvd_rfl, Int.emod_emod_of_dvd _ dvd_rfl,
    ← Int.add_emod]

private theorem wa_succ (x : Int) : wa x + 1 = wa (x + 1) := by
  apply bv_eq_of_unsigned
  rw [bv_unsigned_add, Z_to_bv_unsigned, Z_to_bv_unsigned]
  have h1 : bv_unsigned (1 : word) = 1 := by decide +kernel
  rw [h1]
  unfold bv_wrap
  rw [Int.add_emod, Int.emod_emod_of_dvd _ dvd_rfl, ← Int.add_emod]

/-! ## The bytes a store leaves behind

`wbytes` (`linux-process-semantics@ff0313ba4f:lean/LinuxProcessSemantics/Common/CatExec.lean:64`)
is the model's store. `CatExec.wbytes_above` and `wbytes_below` say it leaves
everything outside the written run alone; these two read a byte inside the run
and state the outside fact in the `wa` form the walk uses. -/

private theorem le_bytes_length (n : Nat) (z : Int) : (Z_to_le_bytes n z).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [Z_to_le_bytes, List.length_cons, ih]

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
    · exact wbytes_below (b :: rest) m (wa base) x (by rw [hbase]; omega) (by rw [hbase]; omega)
    · exact wbytes_above (b :: rest) m (wa base) x (by rw [hbase]; omega)

private theorem wbytes_get (bs : List byte) (m : word → Option byte) (base : Int) (j : Nat)
    (hb : 0 ≤ base) (hnw : base + (bs.length : Int) ≤ 2 ^ 64) (hj : j < bs.length) :
    wbytes m (wa base) bs (wa (base + (j : Int))) = bs[j]? := by
  induction bs generalizing m base j with
  | nil => simp only [List.length_nil] at hj; omega
  | cons b rest ih =>
    have hlen : ((b :: rest).length : Int) = (rest.length : Int) + 1 := by
      simp only [List.length_cons]; push_cast; ring
    match j with
    | 0 =>
      have h0 : base + ((0 : Nat) : Int) = base := by push_cast; ring
      rw [h0]
      show wbytes (fun a => if bv_eqb a (wa base) then some b else m a) (wa base + 1) rest
          (wa base) = _
      rw [wa_succ]
      rw [wbytes_out rest _ (base + 1) (wa base) (by omega) (by rw [hlen] at hnw; omega)
        (by rw [wa_unsigned base hb (by rw [hlen] at hnw; omega)]; left; omega)]
      simp only [bv_eqb, decide_eq_true_eq, ite_true, List.getElem?_cons_zero]
    | j' + 1 =>
      have hj' : j' < rest.length := by simp only [List.length_cons] at hj; omega
      have hstep : base + ((j' + 1 : Nat) : Int) = (base + 1) + (j' : Int) := by
        push_cast; ring
      show wbytes (fun a => if bv_eqb a (wa base) then some b else m a) (wa base + 1) rest
          (wa (base + ((j' + 1 : Nat) : Int))) = _
      rw [wa_succ, hstep,
        ih (fun a => if bv_eqb a (wa base) then some b else m a) (base + 1) j'
          (by omega) (by rw [hlen] at hnw; omega) hj']
      simp only [List.getElem?_cons_succ]

/-! ## `store_ok`, `mem_inv` and the writable view -/

private theorem store_ok_of_wview (m : word → Option byte) (base : Int) (k : Nat)
    (h : ∀ i : Int, 0 ≤ i → i < (k : Int) → wview segs m (wa (base + i)) ≠ none) :
    store_ok segs m (wa base) k = true := by
  induction k generalizing base with
  | zero => rfl
  | succ k ih =>
    have h0 : wview segs m (wa base) ≠ none := by
      have := h 0 (le_refl 0) (by push_cast; omega)
      rwa [Int.add_zero] at this
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
      have := h (1 + i) (by omega) (by push_cast at hik ⊢; omega)
      rwa [show base + (1 + i) = base + 1 + i by ring] at this

private theorem ro_false_of_wview (m : word → Option byte) (x : word)
    (hmi : mem_inv segs m) (h : wview segs m x ≠ none) : ro_addr segs x = false := by
  unfold wview at h
  cases hm : m x with
  | some b => exact hmi x b hm
  | none =>
    rw [hm] at h
    unfold ro_addr
    cases hf : find_segment segs (bv_unsigned x) 1 with
    | none => rfl
    | some seg =>
      rw [hf] at h
      cases hw : seg_writable seg with
      | true => simp only [hw, Bool.not_true]
      | false => rw [hw] at h; simp only [ite_false] at h; exact absurd rfl h

private theorem mem_inv_wbytes (m : word → Option byte) (a : word) (bs : List byte)
    (hmi : mem_inv segs m) (hok : store_ok segs m a bs.length = true) :
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
        ro_false_of_wview m a hmi (by rw [hv]; exact Option.noConfusion)
      have hmi' : mem_inv segs (fun y => if bv_eqb y a then some b else m y) := by
        intro y bz hy
        by_cases hya : bv_eqb y a = true
        · have : y = a := by
            simpa only [bv_eqb, decide_eq_true_eq] using hya
          rw [this]; exact hro
        · simp only [hya, Bool.false_eq_true, ite_false] at hy
          exact hmi y bz hy
      have hgrow : mem_grows m (fun y => if bv_eqb y a then some b else m y) := by
        intro y hy
        by_cases hya : bv_eqb y a = true
        · simp only [hya, ite_true]; exact Option.noConfusion
        · simpa only [hya, Bool.false_eq_true, ite_false] using hy
      exact ih (fun y => if bv_eqb y a then some b else m y) (a + 1) hmi'
        (store_ok_mono segs rest.length m _ (a + 1) hgrow hok')

private theorem wview_wbytes_grows (m : word → Option byte) (a : word) (bs : List byte)
    (x : word) (h : wview segs m x ≠ none) : wview segs (wbytes m a bs) x ≠ none :=
  wview_grows segs m (wbytes m a bs) x (wbytes_grows bs m a) h

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.memset
