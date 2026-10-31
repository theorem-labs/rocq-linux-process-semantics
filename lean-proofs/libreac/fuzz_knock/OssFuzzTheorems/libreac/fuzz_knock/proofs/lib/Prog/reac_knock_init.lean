-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_init.v

import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_init_c
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.memset_c
import OssFuzzTheorems.libreac.fuzz_knock.Image.PlainCode
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.StoreOk

/-! `lib/Prog/reac_knock_init.v`: the walk of `reac_knock_init`.

The Rocq script is eleven tactic lines (`lib/Prog/reac_knock_init.v:30-50`):
`carve_frame`, nine `zstep`s, `call MEMS`, nine more `zstep`s,
`release_frame`, one `zstep`, `finish`, and a `rw_cells_rebytes` that reads
the written bytes back as `knock_cells`. Each of those tactics is a driver
over a project-local Rocq library (`lib/Lib/Tac.v`, 401 lines, over
`lib/Lib/Mem.v` 594, `lib/Lib/Step.v` 824, `lib/Lib/Frame.v` 245 and
`lib/Lib/Cells.v` 227). The Lean twin of that library carries the
DEFINITIONS only, so this file carries, in its first half, the frame and
cell lemmas the walk consumes, and in its second half the walk itself: an
explicit `evt_step` per instruction with the library's step lemma for it,
and `evt_done` with the post-state built by hand, as OSSV-265 slice T did
for `reac_knock_heard`.

Paths in a docstring are in theorem-labs/oss-verify-proofs-internal
`ossv/recipes` `9b0ac6f0e6` under `projects/libreac/fuzz_knock/proofs/`,
unless they name their own repository.

Gaps, all recorded for the OSSV-265 ledger:

* K1-1 `lib/Lib/Exec.v:98-99,119-124` — `msteps_trans` and `evt_cut`, which
  the Rocq `call` tactic (`lib/Lib/Tac.v:250-253`) applies, were not in the
  Lean `Lib/Exec.lean` when this file was started; KnockK1 added them on
  request, so this file uses the project's.
* K1-2 `lib/Prog/memset_c.v:8-25` — `memset_c.lean` is another prover's file
  and had not landed when this walk was written; it did, and this file now
  imports it. The walk stood on a `private` copy of `MEMSET`, `memset_post`
  and `memset_contract` until then.
* K1-3 `lib/Lib/Frame.v`, `lib/Lib/Mem.v`, `lib/Lib/Step.v`,
  `lib/Lib/Cells.v` — the transport lemmas (`munch_write`, `munch_trans`,
  `wmono_write`, `wmono_trans`, `stk_write`, `stk_transport_disjoint`,
  `mem_inv_store_cbytes`, `rw_cells_write`, `rw_cells_frame`,
  `rw_cells_transport`, `bytes_at_write_other`, `wr_at_write`) have no Lean
  twin. The `private` section below proves the instances this walk needs,
  from the Lean library's own `wbytes`/`wview`/`mem_grows` facts. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_init

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.Common
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.StoreOk
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Img0
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Cells
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Step
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_struct
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_init_c
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.memset_c

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! ## 1. The frame and cell lemmas (gaps row K1-3) -/

/-- `Common/StepTac.u_Z2bv` under its Rocq name; `Common/StepTac` is not
imported here, and `BvBase` states the same fact. -/
private theorem u_Z2bv (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    bv_unsigned (Z_to_bv 64 z) = z := bv_unsigned_Z_to_bv_small z h0 h1

/-- A byte inside a `wbytes` write reads back from the written list.
The Lean library has `wbytes_above` and `wbytes_below` for the two outside
cases but no inside case. -/
private theorem wb_get (ws : List byte) (m : word → Option byte) (a x : word)
    (hnw : bv_unsigned a + (ws.length : Int) ≤ 2 ^ 64)
    (hlo : bv_unsigned a ≤ bv_unsigned x)
    (hhi : bv_unsigned x < bv_unsigned a + (ws.length : Int)) :
    wbytes m a ws x = ws[(bv_unsigned x - bv_unsigned a).toNat]? := by
  induction ws generalizing m a with
  | nil => simp only [List.length_nil] at hhi; omega
  | cons b rest ih =>
    have ha := u64_range a
    have hx := u64_range x
    have hlen : ((b :: rest).length : Int) = (rest.length : Int) + 1 := by
      simp only [List.length_cons]; omega
    rw [hlen] at hnw hhi
    have hwb : wbytes m a (b :: rest)
        = wbytes (fun y => if bv_eqb y a then some b else m y) (a + 1) rest := rfl
    rw [hwb]
    by_cases he : bv_unsigned x = bv_unsigned a
    · have hxa : x = a := bv_eq_of_unsigned x a he
      subst hxa
      have hz : (bv_unsigned x - bv_unsigned x).toNat = 0 := by omega
      rw [hz, List.getElem?_cons_zero]
      have hm' : (fun y : word => if bv_eqb y x then some b else m y) x = some b := by
        simp only [PropExec.bv_eqb_refl, ↓reduceIte]
      rcases rest with _ | ⟨c, r⟩
      · simpa only [wbytes] using hm'
      · have hrl : (((c :: r).length : Int)) = (r.length : Int) + 1 := by
          simp only [List.length_cons]; omega
        have hu1 : bv_unsigned (x + 1) = bv_unsigned x + 1 := u_add1 x (by omega)
        rw [wbytes_below (c :: r) _ (x + 1) x (by rw [hu1]; omega) (by rw [hu1]; omega)]
        exact hm'
    · have hgt : bv_unsigned a < bv_unsigned x := by omega
      have hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 a (by omega)
      rw [ih (fun y => if bv_eqb y a then some b else m y) (a + 1) (by rw [hu1]; omega)
        (by rw [hu1]; omega) (by rw [hu1]; omega)]
      have hidx : (bv_unsigned x - bv_unsigned a).toNat
          = (bv_unsigned x - bv_unsigned (a + 1)).toNat + 1 := by rw [hu1]; omega
      rw [hidx, List.getElem?_cons_succ]

/-- `mrd` through a write that misses the address. -/
private theorem mrd_wb_out (segs : List Segment) (ws : List byte)
    (m : word → Option byte) (a x : word)
    (hnw : bv_unsigned a + (ws.length : Int) ≤ 2 ^ 64)
    (hout : bv_unsigned x < bv_unsigned a ∨ bv_unsigned a + (ws.length : Int) ≤ bv_unsigned x) :
    mrd segs (wbytes m a ws) x = mrd segs m x := by
  have h : wbytes m a ws x = m x := by
    rcases hout with h | h
    · exact wbytes_below ws m a x hnw h
    · exact wbytes_above ws m a x h
  unfold mrd
  rw [h]

/-- `mrd` through a write that hits the address. -/
private theorem mrd_wb_hit (segs : List Segment) (ws : List byte)
    (m : word → Option byte) (a x : word)
    (hnw : bv_unsigned a + (ws.length : Int) ≤ 2 ^ 64)
    (hlo : bv_unsigned a ≤ bv_unsigned x)
    (hhi : bv_unsigned x < bv_unsigned a + (ws.length : Int)) :
    mrd segs (wbytes m a ws) x = ws[(bv_unsigned x - bv_unsigned a).toNat]? := by
  have hj : (bv_unsigned x - bv_unsigned a).toNat < ws.length := by omega
  have hb := List.getElem?_eq_getElem hj
  unfold mrd
  rw [wb_get ws m a x hnw hlo hhi, hb]

/-- A memory that only grows keeps every byte it could read. -/
private theorem mrd_grows (segs : List Segment) (m m' : word → Option byte)
    (hg : mem_grows m m') (x : word) (h : mrd segs m x ≠ none) : mrd segs m' x ≠ none := by
  unfold mrd at h ⊢
  cases hm' : m' x with
  | some b => exact Option.some_ne_none b
  | none =>
    cases hm : m x with
    | some b => exact absurd hm' (hg x (by rw [hm]; exact Option.some_ne_none b))
    | none => rw [hm] at h; exact h

/-- `lib/Lib/Frame.v`'s `wmono_trans`. -/
private theorem wmono_trans (segs : List Segment) (m1 m2 m3 : word → Option byte)
    (h12 : wmono segs m1 m2) (h23 : wmono segs m2 m3) : wmono segs m1 m3 :=
  fun x hx => h23 x (h12 x hx)

/-- A write only grows the overlay, so it is a `wmono`. -/
private theorem wmono_wb (segs : List Segment) (m : word → Option byte) (a : word)
    (ws : List byte) : wmono segs m (wbytes m a ws) :=
  fun x hx => wview_grows segs m (wbytes m a ws) x (wbytes_grows ws m a) hx

/-- `lib/Lib/Frame.v`'s `munch_trans`, with the callee's footprint allowed to
be a sublist of the caller's (`munch_weaken` in the same file). -/
private theorem munch_trans_sub (W V : List ivl) (m1 m2 m3 : word → Option byte)
    (h12 : munch W m1 m2) (h23 : munch V m2 m3)
    (hsub : ∀ x : Int, outside W x → outside V x) : munch W m1 m3 :=
  fun x hx => (h23 x (hsub _ hx)).trans (h12 x hx)

/-- `lib/Lib/Frame.v`'s `munch_write`: a store inside the declared footprint
keeps the footprint. -/
private theorem munch_wb (W : List ivl) (m0 m : word → Option byte) (a : word)
    (ws : List byte) (hmu : munch W m0 m)
    (hnw : bv_unsigned a + (ws.length : Int) ≤ 2 ^ 64)
    (hin : ∀ x : Int, bv_unsigned a ≤ x → x < bv_unsigned a + (ws.length : Int) →
      ¬ outside W x) :
    munch W m0 (wbytes m a ws) := by
  intro x hx
  have hout : bv_unsigned x < bv_unsigned a
      ∨ bv_unsigned a + (ws.length : Int) ≤ bv_unsigned x := by
    rcases (by omega : bv_unsigned x < bv_unsigned a
        ∨ bv_unsigned a + (ws.length : Int) ≤ bv_unsigned x
        ∨ (bv_unsigned a ≤ bv_unsigned x
            ∧ bv_unsigned x < bv_unsigned a + (ws.length : Int))) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd hx (hin _ h.1 h.2)
  rcases hout with h | h
  · rw [wbytes_below ws m a x hnw h]; exact hmu x hx
  · rw [wbytes_above ws m a x h]; exact hmu x hx

/-- `lib/Lib/Frame.v`'s `stk_write`: the window only needs its bytes to stay
defined, and a write only adds. -/
private theorem stk_wb (segs : List Segment) (m : word → Option byte) (lo hi : Int)
    (a : word) (ws : List byte) (h : stk segs m lo hi) :
    stk segs (wbytes m a ws) lo hi := by
  obtain ⟨h0, h1, hall⟩ := h
  refine ⟨h0, h1, fun z hz1 hz2 => ?_⟩
  obtain ⟨hw, b, hb⟩ := hall z hz1 hz2
  refine ⟨wview_grows segs m _ _ (wbytes_grows ws m a) hw, ?_⟩
  have := mrd_grows segs m (wbytes m a ws) (wbytes_grows ws m a) (wa z)
    (by rw [hb]; exact Option.some_ne_none b)
  cases hr : mrd segs (wbytes m a ws) (wa z) with
  | some b' => exact ⟨b', rfl⟩
  | none => exact absurd hr this

/-- `lib/Lib/Frame.v`'s `stk_transport_disjoint`, in the only form this walk
needs: the callee's footprint misses the window, so the window is untouched. -/
private theorem stk_munch_out (segs : List Segment) (V : List ivl)
    (m m' : word → Option byte) (lo hi : Int) (h : stk segs m lo hi)
    (hmu : munch V m m') (hdis : ∀ z : Int, lo ≤ z → z < hi → outside V z) :
    stk segs m' lo hi := by
  obtain ⟨h0, h1, hall⟩ := h
  refine ⟨h0, h1, fun z hz1 hz2 => ?_⟩
  obtain ⟨hw, b, hb⟩ := hall z hz1 hz2
  have heq : m' (wa z) = m (wa z) := by
    refine hmu (wa z) ?_
    have hu : bv_unsigned (wa z) = z := by
      unfold wa; exact u_Z2bv z (by omega) (by omega)
    rw [hu]; exact hdis z hz1 hz2
  refine ⟨?_, b, ?_⟩
  · unfold wview at hw ⊢; rw [heq]; exact hw
  · unfold mrd at hb ⊢; rw [heq]; exact hb

/-- `lib/Lib/Mem.v`'s `mem_inv_store_cbytes`: a store into writable bytes
keeps the invariant. -/
private theorem mem_inv_wb (segs : List Segment) (m : word → Option byte) (a : word)
    (ws : List byte) (hmi : mem_inv segs m)
    (hnw : bv_unsigned a + (ws.length : Int) ≤ 2 ^ 64)
    (hok : store_ok segs m a ws.length = true) :
    mem_inv segs (wbytes m a ws) := by
  intro x b hx
  rcases (by omega : bv_unsigned x < bv_unsigned a
      ∨ bv_unsigned a + (ws.length : Int) ≤ bv_unsigned x
      ∨ (bv_unsigned a ≤ bv_unsigned x
          ∧ bv_unsigned x < bv_unsigned a + (ws.length : Int))) with h | h | h
  · exact hmi x b (by rw [← wbytes_below ws m a x hnw h]; exact hx)
  · exact hmi x b (by rw [← wbytes_above ws m a x h]; exact hx)
  · -- inside the store: `store_ok` says the byte is writable
    have hv : wview segs m x ≠ none := store_ok_all segs m ws.length a hnw hok x h
    cases hmx : m x with
    | some b' => exact hmi x b' hmx
    | none =>
      unfold ro_addr
      cases hf : find_segment segs (bv_unsigned x) 1 with
      | none => rfl
      | some seg =>
        show (!seg_writable seg) = false
        cases hw : seg_writable seg with
        | true => rfl
        | false =>
          exfalso
          simp only [wview, hmx, hf, hw, Bool.false_eq_true, ↓reduceIte, ne_eq,
            not_true_eq_false] at hv

/-- `lib/Lib/Mem.v`'s `wr_at_write` / `wr_at_transport`: a writable range
stays writable however the overlay grows. -/
private theorem wr_at_grows (segs : List Segment) (m m' : word → Option byte)
    (A n : Int) (hg : mem_grows m m') (h : wr_at segs m A n) : wr_at segs m' A n := by
  obtain ⟨h0, h1, hall⟩ := h
  exact ⟨h0, h1, fun i hi1 hi2 => wview_grows segs m m' _ hg (hall i hi1 hi2)⟩

private theorem wr_at_wmono (segs : List Segment) (m m' : word → Option byte)
    (A n : Int) (hg : wmono segs m m') (h : wr_at segs m A n) : wr_at segs m' A n := by
  obtain ⟨h0, h1, hall⟩ := h
  exact ⟨h0, h1, fun i hi1 hi2 => hg _ (hall i hi1 hi2)⟩

/-- `lib/Lib/Mem.v`'s `bytes_at_write_other`: a disjoint store leaves a byte
block alone. -/
private theorem bytes_at_wb_out (segs : List Segment) (m : word → Option byte)
    (A : Int) (bs : List byte) (a : word) (ws : List byte)
    (hba : bytes_at segs m A bs)
    (hnw : bv_unsigned a + (ws.length : Int) ≤ 2 ^ 64)
    (hdis : bv_unsigned a + (ws.length : Int) ≤ A ∨ A + (bs.length : Int) ≤ bv_unsigned a) :
    bytes_at segs (wbytes m a ws) A bs := by
  obtain ⟨h0, h1, hall⟩ := hba
  refine ⟨h0, h1, fun i hi => ?_⟩
  have hu : bv_unsigned (wa (A + (i : Int))) = A + (i : Int) := by
    unfold wa; exact u_Z2bv _ (by omega) (by omega)
  rw [mrd_wb_out segs ws m a _ hnw (by rw [hu]; omega)]
  exact hall i hi

/-- `lib/Lib/Step.v`'s `rw_cells_write` at the byte level: a store inside a
byte block replaces exactly its slice. -/
private theorem bytes_at_wb_in (segs : List Segment) (m : word → Option byte)
    (A : Int) (bs : List byte) (k : Nat) (koff : Int) (ws : List byte)
    (hba : bytes_at segs m A bs) (hko : (k : Int) = koff)
    (hk : k < bs.length) (hkw : k + ws.length ≤ bs.length) :
    bytes_at segs (wbytes m (wa (A + koff)) ws) A
      (bs.take k ++ ws ++ bs.drop (k + ws.length)) := by
  subst hko
  obtain ⟨h0, h1, hall⟩ := hba
  have htk : (bs.take k).length = k := by
    rw [List.length_take]; omega
  have hdr : (bs.drop (k + ws.length)).length = bs.length - (k + ws.length) := by
    rw [List.length_drop]
  have hlen : (bs.take k ++ ws ++ bs.drop (k + ws.length)).length = bs.length := by
    rw [List.length_append, List.length_append, htk, hdr]; omega
  have hua : bv_unsigned (wa (A + (k : Int))) = A + (k : Int) := by
    unfold wa; exact u_Z2bv _ (by omega) (by omega)
  refine ⟨h0, by rw [hlen]; exact h1, fun i hi => ?_⟩
  rw [hlen] at hi
  have hui : bv_unsigned (wa (A + (i : Int))) = A + (i : Int) := by
    unfold wa; exact u_Z2bv _ (by omega) (by omega)
  rcases (by omega : i < k ∨ (k ≤ i ∧ i < k + ws.length) ∨ k + ws.length ≤ i)
    with h | h | h
  · rw [mrd_wb_out segs ws m _ _ (by rw [hua]; omega) (by rw [hua, hui]; omega), hall i hi]
    rw [List.getElem?_append_left (by rw [List.length_append, htk]; omega),
      List.getElem?_append_left (by rw [htk]; omega), List.getElem?_take_of_lt h]
  · rw [mrd_wb_hit segs ws m _ _ (by rw [hua]; omega) (by rw [hua, hui]; omega)
      (by rw [hua, hui]; omega)]
    rw [List.getElem?_append_left (by rw [List.length_append, htk]; omega),
      List.getElem?_append_right (by rw [htk]; omega), htk, hua, hui,
      show (A + (i : Int) - (A + (k : Int))).toNat = i - k from by omega]
  · rw [mrd_wb_out segs ws m _ _ (by rw [hua]; omega) (by rw [hua, hui]; omega), hall i hi]
    rw [List.getElem?_append_right (by rw [List.length_append, htk]; omega),
      List.length_append, htk, List.getElem?_drop,
      show k + ws.length + (i - (k + ws.length)) = i from by omega]

/-! ## 2. The image's words, at this file's spelling of the segment list -/

private theorem f50 : fetch_word rsegs (0x12d50 : word) = some 0xfe010113 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d50
private theorem f54 : fetch_word rsegs (0x12d54 : word) = some 0x00113c23 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d54
private theorem f58 : fetch_word rsegs (0x12d58 : word) = some 0x00813823 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d58
private theorem f5c : fetch_word rsegs (0x12d5c : word) = some 0x00913423 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d5c
private theorem f60 : fetch_word rsegs (0x12d60 : word) = some 0x00058413 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d60
private theorem f64 : fetch_word rsegs (0x12d64 : word) = some 0x00050493 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d64
private theorem f68 : fetch_word rsegs (0x12d68 : word) = some 0x02800613 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d68
private theorem f6c : fetch_word rsegs (0x12d6c : word) = some 0x00000593 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d6c
private theorem f70 : fetch_word rsegs (0x12d70 : word) = some 0x695070ef := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d70
private theorem f74 : fetch_word rsegs (0x12d74 : word) = some 0x1dcd6537 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d74
private theorem f78 : fetch_word rsegs (0x12d78 : word) = some 0x5005051b := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d78
private theorem f7c : fetch_word rsegs (0x12d7c : word) = some 0x00a40533 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d7c
private theorem f80 : fetch_word rsegs (0x12d80 : word) = some 0x0084b423 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d80
private theorem f84 : fetch_word rsegs (0x12d84 : word) = some 0x00a4b823 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d84
private theorem f88 : fetch_word rsegs (0x12d88 : word) = some 0x01813083 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d88
private theorem f8c : fetch_word rsegs (0x12d8c : word) = some 0x01013403 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d8c
private theorem f90 : fetch_word rsegs (0x12d90 : word) = some 0x00813483 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d90
private theorem f94 : fetch_word rsegs (0x12d94 : word) = some 0x02010113 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d94
private theorem f98 : fetch_word rsegs (0x12d98 : word) = some 0x00008067 := by
  rw [rsegs_eq]; exact Image.PlainCode.F_12d98

/-! ## 3. Closed value facts -/

private theorem pc_start : Z_to_bv 64 REAC_KNOCK_INIT = (0x12d50 : word) := by
  unfold REAC_KNOCK_INIT; decide +kernel
private theorem p54 : v_addi (0x12d50 : word) 4 = (0x12d54 : word) := by decide +kernel
private theorem p58 : v_addi (0x12d54 : word) 4 = (0x12d58 : word) := by decide +kernel
private theorem p5c : v_addi (0x12d58 : word) 4 = (0x12d5c : word) := by decide +kernel
private theorem p60 : v_addi (0x12d5c : word) 4 = (0x12d60 : word) := by decide +kernel
private theorem p64 : v_addi (0x12d60 : word) 4 = (0x12d64 : word) := by decide +kernel
private theorem p68 : v_addi (0x12d64 : word) 4 = (0x12d68 : word) := by decide +kernel
private theorem p6c : v_addi (0x12d68 : word) 4 = (0x12d6c : word) := by decide +kernel
private theorem p70 : v_addi (0x12d6c : word) 4 = (0x12d70 : word) := by decide +kernel
private theorem p74 : v_addi (0x12d70 : word) 4 = (0x12d74 : word) := by decide +kernel
private theorem p78 : v_addi (0x12d74 : word) 4 = (0x12d78 : word) := by decide +kernel
private theorem p7c : v_addi (0x12d78 : word) 4 = (0x12d7c : word) := by decide +kernel
private theorem p80 : v_addi (0x12d7c : word) 4 = (0x12d80 : word) := by decide +kernel
private theorem p84 : v_addi (0x12d80 : word) 4 = (0x12d84 : word) := by decide +kernel
private theorem p88 : v_addi (0x12d84 : word) 4 = (0x12d88 : word) := by decide +kernel
private theorem p8c : v_addi (0x12d88 : word) 4 = (0x12d8c : word) := by decide +kernel
private theorem p90 : v_addi (0x12d8c : word) 4 = (0x12d90 : word) := by decide +kernel
private theorem p94 : v_addi (0x12d90 : word) 4 = (0x12d94 : word) := by decide +kernel
private theorem p98 : v_addi (0x12d94 : word) 4 = (0x12d98 : word) := by decide +kernel

/-- The `jal` at `0x12d70` targets `memset` at `0x1ac04`. -/
private theorem pcall : btgt (0x12d70 : word) (bv_signed (0x7e94 : BitVec 21))
    = Z_to_bv 64 MEMSET := by
  unfold MEMSET; decide +kernel

/-- `memset` returns to the word after the `jal`; the link value is even. -/
private theorem pret : ret_pc (v_addi (0x12d70 : word) 4) = (0x12d74 : word) := by
  decide +kernel

/-- `lib/Lib/MState.v:140` against the Lean library's `v_jalr`
(the OSSV-265 gaps row T-9 bridge, at `imm = 0`). -/
private theorem jalr_ret (x : word) : v_jalr x (bv_signed (0x0 : BitVec 12)) = ret_pc x := by
  have h := PropExec.b_jalr x 0
  have hz : x + sext 64 (0 : BitVec 12) = x := by
    rw [show sext 64 (0 : BitVec 12) = (0 : word) from by decide]
    exact BitVec.add_zero x
  rw [hz] at h
  exact h.symm

private theorem v_addi_zero (x : word) : v_addi x 0 = x := by
  unfold v_addi
  rw [Int.add_zero]
  exact PropExec.Z_to_bv_bv_unsigned64 x

/-- A register the contract lists as clobbered is not one it keeps. -/
private theorem clob_ne (r c : reg) (hc : init_clobbers c = true)
    (hr : init_clobbers r = false) : r ≠ c := by
  intro h
  rw [h, hc] at hr
  exact Bool.noConfusion hr

/-- `memset`'s clobber set is inside `reac_knock_init`'s: the thirty-two
five-bit registers, decided one by one. -/
private theorem memset_sub_init (r : reg) (h : init_clobbers r = false) :
    r ∉ memset_clobber := by
  have h32 : ∀ i : Fin (2 ^ 5), init_clobbers (BitVec.ofFin i) = false
      → (BitVec.ofFin i) ∉ memset_clobber := by decide
  exact h32 r.toFin h

/-! ## 4. The walk

`lib/Prog/reac_knock_init.v:28-51`. -/

/-- The twin of `reac_knock_init_holds` (`lib/Prog/reac_knock_init.v:28`). -/
theorem reac_knock_init_holds (hmemset : memset_contract) : reac_knock_init_contract := by
  intro regs m lo junk hrw hmi hstk hlo hSA
  -- names for the three addresses the contract is stated over
  obtain ⟨⟨hba0, hwf0⟩, hwr0⟩ := hrw
  have hjl : junk.length = 40 := by
    have : cell_wf (cell.CB 40 junk) := hwf0.1
    exact this
  have hbs0 : cells_bytes [cell.CB 40 junk] = junk := by
    simp only [cells_bytes, cbytes, List.append_nil]
  rw [hbs0] at hba0
  have hcs0 : ((cells_size [cell.CB 40 junk] : Nat) : Int) = 40 := by rfl
  rw [hcs0] at hwr0
  obtain ⟨hA0, hA40, hwrall⟩ := hwr0
  obtain ⟨hlo0, hS64, hstkall⟩ := hstk
  have hSr := u64_range (getr regs 2)
  have hAr := u64_range (getr regs 10)
  unfold REAC_KNOCK_INIT_FRAME at hlo ⊢
  -- the stack frame
  have hspu : bv_unsigned (v_addi (getr regs 2) (bv_signed (0xfe0 : BitVec 12)))
      = bv_unsigned (getr regs 2) - 32 := by
    rw [show bv_signed (0xfe0 : BitVec 12) = (-32 : Int) from by decide]
    unfold v_addi
    exact u_Z2bv _ (by omega) (by omega)
  have hspw : v_addi (getr regs 2) (bv_signed (0xfe0 : BitVec 12))
      = wa (bv_unsigned (getr regs 2) - 32) := by
    rw [show bv_signed (0xfe0 : BitVec 12) = (-32 : Int) from by decide]
    rfl
  -- every byte of the frame is writable
  have hframe_ok : ∀ off : Int, 0 ≤ off → off + 8 ≤ 32 →
      ∀ m' : word → Option byte, mem_grows m m' →
      store_ok rsegs m' (wa (bv_unsigned (getr regs 2) - 32 + off)) 8 = true := by
    intro off ho1 ho2 m' hg
    refine store_ok_mono rsegs 8 m m' _ hg ?_
    refine store_ok_of_all rsegs 8 m _ ?_ ?_
    · rw [show bv_unsigned (wa (bv_unsigned (getr regs 2) - 32 + off))
        = bv_unsigned (getr regs 2) - 32 + off from
        u_Z2bv _ (by omega) (by omega)]
      omega
    · intro x hx
      rw [show bv_unsigned (wa (bv_unsigned (getr regs 2) - 32 + off))
        = bv_unsigned (getr regs 2) - 32 + off from
        u_Z2bv _ (by omega) (by omega)] at hx
      have hxw : wa (bv_unsigned x) = x := PropExec.Z_to_bv_bv_unsigned64 x
      have := (hstkall (bv_unsigned x) (by omega) (by omega)).1
      rw [hxw] at this
      exact this
  have hle8 : ∀ v : word, (word_to_le_bytes 8 v).length = 8 := fun _ => rfl
  have hua : ∀ off : Int, 0 ≤ off → off ≤ 32 →
      bv_unsigned (wa (bv_unsigned (getr regs 2) - 32 + off))
        = bv_unsigned (getr regs 2) - 32 + off :=
    fun off h1 h2 => u_Z2bv _ (by omega) (by omega)
  have huo : ∀ off : Int, 0 ≤ off → off < 40 →
      bv_unsigned (wa (bv_unsigned (getr regs 10) + off))
        = bv_unsigned (getr regs 10) + off :=
    fun off h1 h2 => u_Z2bv _ (by omega) (by omega)
  have hfa : ∀ off : Int, 0 ≤ off → off ≤ 40 →
      v_addi (wa (bv_unsigned (getr regs 2) - 32)) off
        = wa (bv_unsigned (getr regs 2) - 32 + off) := by
    intro off h1 h2
    unfold v_addi wa
    rw [u_Z2bv (bv_unsigned (getr regs 2) - 32) (by omega) (by omega)]
  have hoa : ∀ off : Int,
      v_addi (getr regs 10) off = wa (bv_unsigned (getr regs 10) + off) :=
    fun _ => rfl
  -- the three frame slots, named
  obtain ⟨m1, hm1⟩ : ∃ x, wbytes m (wa (bv_unsigned (getr regs 2) - 32 + 24))
      (word_to_le_bytes 8 (getr regs 1)) = x := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ x, wbytes m1 (wa (bv_unsigned (getr regs 2) - 32 + 16))
      (word_to_le_bytes 8 (getr regs 8)) = x := ⟨_, rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ x, wbytes m2 (wa (bv_unsigned (getr regs 2) - 32 + 8))
      (word_to_le_bytes 8 (getr regs 9)) = x := ⟨_, rfl⟩
  have hg1 : mem_grows m m1 := hm1 ▸ wbytes_grows _ m _
  have hg2 : mem_grows m1 m2 := hm2 ▸ wbytes_grows _ m1 _
  have hg3 : mem_grows m2 m3 := hm3 ▸ wbytes_grows _ m2 _
  have hg13 : mem_grows m m3 :=
    mem_grows_trans _ _ _ hg1 (mem_grows_trans _ _ _ hg2 hg3)
  -- the object block survives the frame stores
  have hba3 : bytes_at rsegs m3 (bv_unsigned (getr regs 10)) junk := by
    rw [← hm3, ← hm2, ← hm1]
    refine bytes_at_wb_out rsegs _ _ _ _ _ (bytes_at_wb_out rsegs _ _ _ _ _
      (bytes_at_wb_out rsegs _ _ _ _ _ hba0 ?_ ?_) ?_ ?_) ?_ ?_
    · rw [hle8, hua 24 (by omega) (by omega)]; omega
    · rw [hle8, hua 24 (by omega) (by omega), hjl]; exact Or.inl (by omega)
    · rw [hle8, hua 16 (by omega) (by omega)]; omega
    · rw [hle8, hua 16 (by omega) (by omega), hjl]; exact Or.inl (by omega)
    · rw [hle8, hua 8 (by omega) (by omega)]; omega
    · rw [hle8, hua 8 (by omega) (by omega), hjl]; exact Or.inl (by omega)
  have hmi3 : mem_inv rsegs m3 := by
    rw [← hm3, ← hm2, ← hm1]
    refine mem_inv_wb rsegs _ _ _ (mem_inv_wb rsegs _ _ _
      (mem_inv_wb rsegs _ _ _ hmi ?_ ?_) ?_ ?_) ?_ ?_
    · rw [hle8, hua 24 (by omega) (by omega)]; omega
    · rw [hle8]; exact hframe_ok 24 (by omega) (by omega) m (mem_grows_refl m)
    · rw [hle8, hua 16 (by omega) (by omega)]; omega
    · rw [hle8, hm1]; exact hframe_ok 16 (by omega) (by omega) m1 hg1
    · rw [hle8, hua 8 (by omega) (by omega)]; omega
    · rw [hle8, hm1, hm2]
      exact hframe_ok 8 (by omega) (by omega) m2 (mem_grows_trans _ _ _ hg1 hg2)
  have hstk3 : stk rsegs m3 lo (bv_unsigned (getr regs 2)) := by
    rw [← hm3, ← hm2, ← hm1]
    exact stk_wb rsegs _ _ _ _ _ (stk_wb rsegs _ _ _ _ _
      (stk_wb rsegs m lo _ _ _ ⟨hlo0, hS64, hstkall⟩))
  have hmu3 : munch
      [(bv_unsigned (getr regs 2) - 32, bv_unsigned (getr regs 2)),
       (bv_unsigned (getr regs 10), bv_unsigned (getr regs 10) + 40)] m m3 := by
    rw [← hm3, ← hm2, ← hm1]
    refine munch_wb _ m _ _ _ (munch_wb _ m _ _ _ (munch_wb _ m m _ _
      (munch_refl _ m) ?_ ?_) ?_ ?_) ?_ ?_
    · rw [hle8, hua 24 (by omega) (by omega)]; omega
    · intro x hx1 hx2 hout
      rw [hua 24 (by omega) (by omega)] at hx1
      rw [hle8, hua 24 (by omega) (by omega)] at hx2
      simp only [outside] at hout
      omega
    · rw [hle8, hua 16 (by omega) (by omega)]; omega
    · intro x hx1 hx2 hout
      rw [hua 16 (by omega) (by omega)] at hx1
      rw [hle8, hua 16 (by omega) (by omega)] at hx2
      simp only [outside] at hout
      omega
    · rw [hle8, hua 8 (by omega) (by omega)]; omega
    · intro x hx1 hx2 hout
      rw [hua 8 (by omega) (by omega)] at hx1
      rw [hle8, hua 8 (by omega) (by omega)] at hx2
      simp only [outside] at hout
      omega
  -- the three saved registers read back out of the frame
  have hr24 : rdn rsegs m3 (wa (bv_unsigned (getr regs 2) - 32 + 24)) 8
      = some (word_to_le_bytes 8 (getr regs 1)) := by
    rw [← hm3, rdn_wbytes_out rsegs _ m2 _ _ 8
        (Or.inr (by rw [hle8, hua 8 (by omega) (by omega), hua 24 (by omega) (by omega)]; omega))
        (by rw [hua 24 (by omega) (by omega)]; omega)
        (by rw [hle8, hua 8 (by omega) (by omega)]; omega),
      ← hm2, rdn_wbytes_out rsegs _ m1 _ _ 8
        (Or.inr (by rw [hle8, hua 16 (by omega) (by omega), hua 24 (by omega) (by omega)]; omega))
        (by rw [hua 24 (by omega) (by omega)]; omega)
        (by rw [hle8, hua 16 (by omega) (by omega)]; omega),
      ← hm1]
    exact rdn_wbytes_hit8 rsegs m _ _ (by rw [hua 24 (by omega) (by omega)]; omega)
  have hr16 : rdn rsegs m3 (wa (bv_unsigned (getr regs 2) - 32 + 16)) 8
      = some (word_to_le_bytes 8 (getr regs 8)) := by
    rw [← hm3, rdn_wbytes_out rsegs _ m2 _ _ 8
        (Or.inr (by rw [hle8, hua 8 (by omega) (by omega), hua 16 (by omega) (by omega)]; omega))
        (by rw [hua 16 (by omega) (by omega)]; omega)
        (by rw [hle8, hua 8 (by omega) (by omega)]; omega),
      ← hm2]
    exact rdn_wbytes_hit8 rsegs m1 _ _ (by rw [hua 16 (by omega) (by omega)]; omega)
  have hr8 : rdn rsegs m3 (wa (bv_unsigned (getr regs 2) - 32 + 8)) 8
      = some (word_to_le_bytes 8 (getr regs 9)) := by
    rw [← hm3]
    exact rdn_wbytes_hit8 rsegs m2 _ _ (by rw [hua 8 (by omega) (by omega)]; omega)
  -- ==================== the walk ====================
  rw [pc_start]
  -- 0x12d50  addi sp, sp, -32
  refine evt_step (mstep_mkst (step_addi_at rsegs _ _ _ _ _ 2 2 0xfe0
    (wa (bv_unsigned (getr regs 2) - 32)) f50 (by decide) Image.PlainCode.D_12d50
    (by decide) hspw)) ?_
  rw [p54]
  -- 0x12d54  sd ra, 24(sp)
  refine evt_step (mstep_mkst (step_sd_at rsegs _ _ _ _ _ 2 1 0x18
    (wa (bv_unsigned (getr regs 2) - 32 + 24)) (getr regs 1) f54 (by decide)
    Image.PlainCode.D_12d54 ?_ ?_ ?_)) ?_
  · rw [getr_same _ 2 _ (by decide),
      show bv_signed (0x18 : BitVec 12) = (24 : Int) from by decide]
    exact hfa 24 (by omega) (by omega)
  · exact getr_other _ 2 _ 1 (by decide)
  · exact hframe_ok 24 (by omega) (by omega) m (mem_grows_refl m)
  rw [p58, hm1]
  -- 0x12d58  sd s0, 16(sp)
  refine evt_step (mstep_mkst (step_sd_at rsegs _ _ _ _ _ 2 8 0x10
    (wa (bv_unsigned (getr regs 2) - 32 + 16)) (getr regs 8) f58 (by decide)
    Image.PlainCode.D_12d58 ?_ ?_ ?_)) ?_
  · rw [getr_same _ 2 _ (by decide),
      show bv_signed (0x10 : BitVec 12) = (16 : Int) from by decide]
    exact hfa 16 (by omega) (by omega)
  · exact getr_other _ 2 _ 8 (by decide)
  · exact hframe_ok 16 (by omega) (by omega) m1 hg1
  rw [p5c, hm2]
  -- 0x12d5c  sd s1, 8(sp)
  refine evt_step (mstep_mkst (step_sd_at rsegs _ _ _ _ _ 2 9 0x8
    (wa (bv_unsigned (getr regs 2) - 32 + 8)) (getr regs 9) f5c (by decide)
    Image.PlainCode.D_12d5c ?_ ?_ ?_)) ?_
  · rw [getr_same _ 2 _ (by decide),
      show bv_signed (0x8 : BitVec 12) = (8 : Int) from by decide]
    exact hfa 8 (by omega) (by omega)
  · exact getr_other _ 2 _ 9 (by decide)
  · exact hframe_ok 8 (by omega) (by omega) m2 (mem_grows_trans _ _ _ hg1 hg2)
  rw [p60, hm3]
  -- 0x12d60  addi s0, a1, 0
  refine evt_step (mstep_mkst (step_addi_at rsegs _ _ _ _ _ 8 11 0x0
    (getr regs 11) f60 (by decide) Image.PlainCode.D_12d60 (by decide) ?_)) ?_
  · rw [getr_other _ 2 _ 11 (by decide),
      show bv_signed (0x0 : BitVec 12) = (0 : Int) from by decide]
    exact v_addi_zero _
  rw [p64]
  -- 0x12d64  addi s1, a0, 0
  refine evt_step (mstep_mkst (step_addi_at rsegs _ _ _ _ _ 9 10 0x0
    (getr regs 10) f64 (by decide) Image.PlainCode.D_12d64 (by decide) ?_)) ?_
  · rw [getr_other _ 8 _ 10 (by decide), getr_other _ 2 _ 10 (by decide),
      show bv_signed (0x0 : BitVec 12) = (0 : Int) from by decide]
    exact v_addi_zero _
  rw [p68]
  -- 0x12d68  addi a2, x0, 40
  refine evt_step (mstep_mkst (step_addi_at rsegs _ _ _ _ _ 12 0 0x28
    (Z_to_bv 64 40) f68 (by decide) Image.PlainCode.D_12d68 (by decide) ?_)) ?_
  · rw [getr_zero]; decide +kernel
  rw [p6c]
  -- 0x12d6c  addi a1, x0, 0
  refine evt_step (mstep_mkst (step_addi_at rsegs _ _ _ _ _ 11 0 0x0
    (Z_to_bv 64 0) f6c (by decide) Image.PlainCode.D_12d6c (by decide) ?_)) ?_
  · rw [getr_zero]; decide +kernel
  rw [p70]
  -- 0x12d70  jal ra, memset
  refine evt_step (mstep_mkst (step_jal_link rsegs _ _ _ _ _ 1 0x7e94
    f70 (by decide) Image.PlainCode.D_12d70)) ?_
  rw [show bv_eqb (1 : reg) 0 = false from by decide]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [pcall]
  -- memset(s, 0, 40)
  unfold memset_contract at hmemset
  refine evt_cut (hmemset _ _ junk ?_ ?_) ?_
  · rw [getr_other _ 1 _ 10 (by decide), getr_other _ 11 _ 10 (by decide),
      getr_other _ 12 _ 10 (by decide), getr_other _ 9 _ 10 (by decide),
      getr_other _ 8 _ 10 (by decide), getr_other _ 2 _ 10 (by decide),
      getr_other _ 1 _ 12 (by decide), getr_other _ 11 _ 12 (by decide),
      getr_same _ 12 _ (by decide),
      show (bv_unsigned (Z_to_bv 64 40)).toNat = 40 from by decide +kernel]
    refine ⟨⟨?_, ⟨?_, trivial⟩⟩, ?_⟩
    · rw [hbs0]; exact hba3
    · exact hjl
    · exact wr_at_grows rsegs m m3 _ _ hg13 ⟨hA0, hA40, hwrall⟩
  · exact hmi3
  · intro ms' hpost
    simp only [memset_post] at hpost
    obtain ⟨regs4, m4, rfl, hpres, hmu34, hwm34, hmi4, hrw4⟩ := hpost
    -- the registers `memset` gives back
    have hp2 : getr regs4 2 = wa (bv_unsigned (getr regs 2) - 32) := by
      rw [hpres 2 (by decide), getr_other _ 1 _ 2 (by decide),
        getr_other _ 11 _ 2 (by decide), getr_other _ 12 _ 2 (by decide),
        getr_other _ 9 _ 2 (by decide), getr_other _ 8 _ 2 (by decide),
        getr_same _ 2 _ (by decide)]
    have hp8 : getr regs4 8 = getr regs 11 := by
      rw [hpres 8 (by decide), getr_other _ 1 _ 8 (by decide),
        getr_other _ 11 _ 8 (by decide), getr_other _ 12 _ 8 (by decide),
        getr_other _ 9 _ 8 (by decide), getr_same _ 8 _ (by decide)]
    have hp9 : getr regs4 9 = getr regs 10 := by
      rw [hpres 9 (by decide), getr_other _ 1 _ 9 (by decide),
        getr_other _ 11 _ 9 (by decide), getr_other _ 12 _ 9 (by decide),
        getr_same _ 9 _ (by decide)]
    have hp1 : getr regs4 1 = v_addi (0x12d70 : word) 4 := by
      rw [hpres 1 (by decide), getr_same _ 1 _ (by decide)]
    -- the callee's footprint, in the caller's words
    rw [getr_other _ 1 _ 10 (by decide), getr_other _ 11 _ 10 (by decide),
      getr_other _ 12 _ 10 (by decide), getr_other _ 9 _ 10 (by decide),
      getr_other _ 8 _ 10 (by decide), getr_other _ 2 _ 10 (by decide),
      getr_other _ 1 _ 12 (by decide), getr_other _ 11 _ 12 (by decide),
      getr_same _ 12 _ (by decide),
      show bv_unsigned (Z_to_bv 64 40) = (40 : Int) from by decide +kernel] at hmu34
    rw [getr_other _ 1 _ 10 (by decide), getr_other _ 11 _ 10 (by decide),
      getr_other _ 12 _ 10 (by decide), getr_other _ 9 _ 10 (by decide),
      getr_other _ 8 _ 10 (by decide), getr_other _ 2 _ 10 (by decide),
      getr_other _ 1 _ 12 (by decide), getr_other _ 11 _ 12 (by decide),
      getr_same _ 12 _ (by decide),
      getr_other _ 1 _ 11 (by decide), getr_same _ 11 _ (by decide),
      show (bv_unsigned (Z_to_bv 64 40)).toNat = 40 from by decide +kernel,
      show Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) % 256) = (Z_to_bv 8 0 : byte) from
        by decide +kernel] at hrw4
    obtain ⟨⟨hba4, _⟩, hwr4⟩ := hrw4
    simp only [cells_bytes, cbytes, List.append_nil] at hba4
    have hwr4' : wr_at rsegs m4 (bv_unsigned (getr regs 10)) 40 := hwr4
    -- the caller's facts, transported across the call
    have hstk4 : stk rsegs m4 lo (bv_unsigned (getr regs 2)) := by
      refine stk_munch_out rsegs _ m3 m4 lo _ hstk3 hmu34 ?_
      intro z hz1 hz2
      simp only [outside]
      exact ⟨Or.inl (by omega), trivial⟩
    have hmu4 : munch
        [(bv_unsigned (getr regs 2) - 32, bv_unsigned (getr regs 2)),
         (bv_unsigned (getr regs 10), bv_unsigned (getr regs 10) + 40)] m m4 := by
      refine munch_trans_sub _ _ m m3 m4 hmu3 hmu34 ?_
      intro x hx
      simp only [outside] at hx ⊢
      exact ⟨hx.2.1, trivial⟩
    have hwm3 : wmono rsegs m m3 := fun x hx => wview_grows rsegs m m3 x hg13 hx
    have hwm4 : wmono rsegs m m4 := wmono_trans rsegs m m3 m4 hwm3 hwm34
    have hr24_4 : rdn rsegs m4 (wa (bv_unsigned (getr regs 2) - 32 + 24)) 8
        = some (word_to_le_bytes 8 (getr regs 1)) := by
      rw [rdn_ext rsegs 8 m4 m3 _ (by rw [hua 24 (by omega) (by omega)]; omega)
        (fun x hxr => hmu34 x (by
          rw [hua 24 (by omega) (by omega)] at hxr
          simp only [outside]
          exact ⟨Or.inl (by omega), trivial⟩))]
      exact hr24
    have hr16_4 : rdn rsegs m4 (wa (bv_unsigned (getr regs 2) - 32 + 16)) 8
        = some (word_to_le_bytes 8 (getr regs 8)) := by
      rw [rdn_ext rsegs 8 m4 m3 _ (by rw [hua 16 (by omega) (by omega)]; omega)
        (fun x hxr => hmu34 x (by
          rw [hua 16 (by omega) (by omega)] at hxr
          simp only [outside]
          exact ⟨Or.inl (by omega), trivial⟩))]
      exact hr16
    have hr8_4 : rdn rsegs m4 (wa (bv_unsigned (getr regs 2) - 32 + 8)) 8
        = some (word_to_le_bytes 8 (getr regs 9)) := by
      rw [rdn_ext rsegs 8 m4 m3 _ (by rw [hua 8 (by omega) (by omega)]; omega)
        (fun x hxr => hmu34 x (by
          rw [hua 8 (by omega) (by omega)] at hxr
          simp only [outside]
          exact ⟨Or.inl (by omega), trivial⟩))]
      exact hr8
    -- the two field stores, named
    obtain ⟨m5, hm5⟩ : ∃ x, wbytes m4 (wa (bv_unsigned (getr regs 10) + 8))
        (word_to_le_bytes 8 (getr regs 11)) = x := ⟨_, rfl⟩
    obtain ⟨m6, hm6⟩ : ∃ x, wbytes m5 (wa (bv_unsigned (getr regs 10) + 16))
        (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (getr regs 11) + L_NS))) = x :=
      ⟨_, rfl⟩
    have hg5 : mem_grows m4 m5 := hm5 ▸ wbytes_grows _ m4 _
    have hg6 : mem_grows m5 m6 := hm6 ▸ wbytes_grows _ m5 _
    have hobj_ok : ∀ off : Int, 0 ≤ off → off + 8 ≤ 40 →
        ∀ m' : word → Option byte, mem_grows m4 m' →
        store_ok rsegs m' (wa (bv_unsigned (getr regs 10) + off)) 8 = true := by
      intro off ho1 ho2 m' hg
      obtain ⟨hw0, hw1, hwall⟩ := hwr4'
      refine store_ok_mono rsegs 8 m4 m' _ hg ?_
      refine store_ok_of_all rsegs 8 m4 _ ?_ ?_
      · rw [huo off (by omega) (by omega)]; omega
      · intro x hx
        rw [huo off (by omega) (by omega)] at hx
        have h := hwall (bv_unsigned x - bv_unsigned (getr regs 10)) (by omega) (by omega)
        rw [show wa (bv_unsigned (getr regs 10)
              + (bv_unsigned x - bv_unsigned (getr regs 10))) = x from by
            unfold wa
            rw [show bv_unsigned (getr regs 10)
              + (bv_unsigned x - bv_unsigned (getr regs 10)) = bv_unsigned x from by omega]
            exact PropExec.Z_to_bv_bv_unsigned64 x] at h
        exact h
    have hpeel : ∀ (a : word) (n : Nat),
        bv_unsigned a + (n : Int) ≤ bv_unsigned (getr regs 10) →
        bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
        rdn rsegs m6 a n = rdn rsegs m4 a n := by
      intro a n h1 h2
      rw [← hm6, rdn_wbytes_out rsegs _ m5 _ _ n
          (Or.inl (by rw [huo 16 (by omega) (by omega)]; omega)) h2
          (by rw [hle8, huo 16 (by omega) (by omega)]; omega),
        ← hm5, rdn_wbytes_out rsegs _ m4 _ _ n
          (Or.inl (by rw [huo 8 (by omega) (by omega)]; omega)) h2
          (by rw [hle8, huo 8 (by omega) (by omega)]; omega)]
    have hrd24 : rdn rsegs m6 (wa (bv_unsigned (getr regs 2) - 32 + 24)) 8
        = some (word_to_le_bytes 8 (getr regs 1)) := by
      rw [hpeel _ 8 (by rw [hua 24 (by omega) (by omega)]; omega)
        (by rw [hua 24 (by omega) (by omega)]; omega)]
      exact hr24_4
    have hrd16 : rdn rsegs m6 (wa (bv_unsigned (getr regs 2) - 32 + 16)) 8
        = some (word_to_le_bytes 8 (getr regs 8)) := by
      rw [hpeel _ 8 (by rw [hua 16 (by omega) (by omega)]; omega)
        (by rw [hua 16 (by omega) (by omega)]; omega)]
      exact hr16_4
    have hrd8 : rdn rsegs m6 (wa (bv_unsigned (getr regs 2) - 32 + 8)) 8
        = some (word_to_le_bytes 8 (getr regs 9)) := by
      rw [hpeel _ 8 (by rw [hua 8 (by omega) (by omega)]; omega)
        (by rw [hua 8 (by omega) (by omega)]; omega)]
      exact hr8_4
    rw [getr_same _ 1 _ (by decide), pret]
    -- 0x12d74  lui a0, 0x1dcd6
    refine evt_step (mstep_mkst (step_lui_at rsegs _ _ _ _ _ 10 0x1dcd6
      (Z_to_bv 64 499998720) f74 (by decide) Image.PlainCode.D_12d74 (by decide)
      (by decide +kernel))) ?_
    rw [p78]
    -- 0x12d78  addiw a0, a0, 0x500
    refine evt_step (mstep_mkst (step_addiw_at rsegs _ _ _ _ _ 10 10 0x500
      (Z_to_bv 64 500000000) f78 (by decide) Image.PlainCode.D_12d78 (by decide) ?_)) ?_
    · rw [getr_same _ 10 _ (by decide)] <;> decide +kernel
    rw [p7c]
    -- 0x12d7c  add a0, s0, a0
    refine evt_step (mstep_mkst (step_add_at rsegs _ _ _ _ _ 10 8 10
      (Z_to_bv 64 (bv_unsigned (getr regs 11) + L_NS)) f7c (by decide)
      Image.PlainCode.D_12d7c (by decide) ?_)) ?_
    · rw [getr_other _ 10 _ 8 (by decide), getr_other _ 10 _ 8 (by decide), hp8,
        getr_same _ 10 _ (by decide)]
      unfold v_add L_NS
      congr 1
    rw [p80]
    -- 0x12d80  sd s0, 8(s1)
    refine evt_step (mstep_mkst (step_sd_at rsegs _ _ _ _ _ 9 8 0x8
      (wa (bv_unsigned (getr regs 10) + 8)) (getr regs 11) f80 (by decide)
      Image.PlainCode.D_12d80 ?_ ?_ ?_)) ?_
    · rw [getr_other _ 10 _ 9 (by decide), getr_other _ 10 _ 9 (by decide),
        getr_other _ 10 _ 9 (by decide), hp9,
        show bv_signed (0x8 : BitVec 12) = (8 : Int) from by decide]
      exact hoa 8
    · rw [getr_other _ 10 _ 8 (by decide), getr_other _ 10 _ 8 (by decide),
        getr_other _ 10 _ 8 (by decide)]
      exact hp8
    · exact hobj_ok 8 (by omega) (by omega) m4 (mem_grows_refl m4)
    rw [p84, hm5]
    -- 0x12d84  sd a0, 16(s1)
    refine evt_step (mstep_mkst (step_sd_at rsegs _ _ _ _ _ 9 10 0x10
      (wa (bv_unsigned (getr regs 10) + 16))
      (Z_to_bv 64 (bv_unsigned (getr regs 11) + L_NS)) f84 (by decide)
      Image.PlainCode.D_12d84 ?_ ?_ ?_)) ?_
    · rw [getr_other _ 10 _ 9 (by decide), getr_other _ 10 _ 9 (by decide),
        getr_other _ 10 _ 9 (by decide), hp9,
        show bv_signed (0x10 : BitVec 12) = (16 : Int) from by decide]
      exact hoa 16
    · exact getr_same _ 10 _ (by decide)
    · exact hobj_ok 16 (by omega) (by omega) m5 hg5
    rw [p88, hm6]
    -- 0x12d88  ld ra, 24(sp)
    refine evt_step (mstep_mkst (step_ld rsegs _ _ _ _ _ 1 2 0x18
      (word_to_le_bytes 8 (getr regs 1)) (getr regs 1) f88 (by decide)
      Image.PlainCode.D_12d88 ?_ (bytes_le_to_Z_8 _))) ?_
    · rw [getr_other _ 10 _ 2 (by decide), getr_other _ 10 _ 2 (by decide),
        getr_other _ 10 _ 2 (by decide), hp2,
        show bv_signed (0x18 : BitVec 12) = (24 : Int) from by decide,
        hfa 24 (by omega) (by omega)]
      exact hrd24
    rw [show bv_eqb (1 : reg) 0 = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [p8c]
    -- 0x12d8c  ld s0, 16(sp)
    refine evt_step (mstep_mkst (step_ld rsegs _ _ _ _ _ 8 2 0x10
      (word_to_le_bytes 8 (getr regs 8)) (getr regs 8) f8c (by decide)
      Image.PlainCode.D_12d8c ?_ (bytes_le_to_Z_8 _))) ?_
    · rw [getr_other _ 1 _ 2 (by decide), getr_other _ 10 _ 2 (by decide),
        getr_other _ 10 _ 2 (by decide), getr_other _ 10 _ 2 (by decide), hp2,
        show bv_signed (0x10 : BitVec 12) = (16 : Int) from by decide,
        hfa 16 (by omega) (by omega)]
      exact hrd16
    rw [show bv_eqb (8 : reg) 0 = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [p90]
    -- 0x12d90  ld s1, 8(sp)
    refine evt_step (mstep_mkst (step_ld rsegs _ _ _ _ _ 9 2 0x8
      (word_to_le_bytes 8 (getr regs 9)) (getr regs 9) f90 (by decide)
      Image.PlainCode.D_12d90 ?_ (bytes_le_to_Z_8 _))) ?_
    · rw [getr_other _ 8 _ 2 (by decide), getr_other _ 1 _ 2 (by decide),
        getr_other _ 10 _ 2 (by decide), getr_other _ 10 _ 2 (by decide),
        getr_other _ 10 _ 2 (by decide), hp2,
        show bv_signed (0x8 : BitVec 12) = (8 : Int) from by decide,
        hfa 8 (by omega) (by omega)]
      exact hrd8
    rw [show bv_eqb (9 : reg) 0 = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [p94]
    -- 0x12d94  addi sp, sp, 32
    refine evt_step (mstep_mkst (step_addi_at rsegs _ _ _ _ _ 2 2 0x20
      (getr regs 2) f94 (by decide) Image.PlainCode.D_12d94 (by decide) ?_)) ?_
    · rw [getr_other _ 9 _ 2 (by decide), getr_other _ 8 _ 2 (by decide),
        getr_other _ 1 _ 2 (by decide), getr_other _ 10 _ 2 (by decide),
        getr_other _ 10 _ 2 (by decide), getr_other _ 10 _ 2 (by decide), hp2,
        show bv_signed (0x20 : BitVec 12) = (32 : Int) from by decide,
        hfa 32 (by omega) (by omega),
        show bv_unsigned (getr regs 2) - 32 + 32 = bv_unsigned (getr regs 2) from by omega]
      exact PropExec.Z_to_bv_bv_unsigned64 _
    rw [p98]
    -- 0x12d98  jalr x0, 0(ra)
    refine evt_step (mstep_mkst (step_jalr_x0 rsegs _ _ _ _ _ 1 0x0 (getr regs 1)
      f98 (by decide) Image.PlainCode.D_12d98 ?_)) ?_
    · rw [getr_other _ 2 _ 1 (by decide), getr_other _ 9 _ 1 (by decide),
        getr_other _ 8 _ 1 (by decide), getr_same _ 1 _ (by decide)]
    rw [jalr_ret]
    -- the post-state
    refine evt_done ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- the registers the contract keeps
      intro r hr
      have hr10 : r ≠ 10 := clob_ne r 10 (by decide) hr
      have hr11 : r ≠ 11 := clob_ne r 11 (by decide) hr
      have hr12 : r ≠ 12 := clob_ne r 12 (by decide) hr
      by_cases h2 : r = 2
      · subst h2; exact getr_same _ 2 _ (by decide)
      · rw [getr_other _ 2 _ r h2]
        by_cases h9 : r = 9
        · subst h9; exact getr_same _ 9 _ (by decide)
        · rw [getr_other _ 9 _ r h9]
          by_cases h8 : r = 8
          · subst h8; exact getr_same _ 8 _ (by decide)
          · rw [getr_other _ 8 _ r h8]
            by_cases h1 : r = 1
            · subst h1; exact getr_same _ 1 _ (by decide)
            · rw [getr_other _ 1 _ r h1, getr_other _ 10 _ r hr10,
                getr_other _ 10 _ r hr10, getr_other _ 10 _ r hr10,
                hpres r (memset_sub_init r hr), getr_other _ 1 _ r h1,
                getr_other _ 11 _ r hr11, getr_other _ 12 _ r hr12,
                getr_other _ 9 _ r h9, getr_other _ 8 _ r h8,
                getr_other _ 2 _ r h2]
    · -- the footprint
      rw [← hm6, ← hm5]
      refine munch_wb _ m _ _ _ (munch_wb _ m m4 _ _ hmu4 ?_ ?_) ?_ ?_
      · rw [hle8, huo 8 (by omega) (by omega)]; omega
      · intro x hx1 hx2 hout
        rw [huo 8 (by omega) (by omega)] at hx1
        rw [hle8, huo 8 (by omega) (by omega)] at hx2
        simp only [outside] at hout
        omega
      · rw [hle8, huo 16 (by omega) (by omega)]; omega
      · intro x hx1 hx2 hout
        rw [huo 16 (by omega) (by omega)] at hx1
        rw [hle8, huo 16 (by omega) (by omega)] at hx2
        simp only [outside] at hout
        omega
    · -- a writable byte stays writable
      refine wmono_trans rsegs m m4 _ hwm4 ?_
      rw [← hm6, ← hm5]
      exact wmono_trans rsegs m4 _ _ (wmono_wb rsegs m4 _ _) (wmono_wb rsegs _ _ _)
    · -- the memory invariant
      rw [← hm6, ← hm5]
      refine mem_inv_wb rsegs _ _ _ (mem_inv_wb rsegs m4 _ _ hmi4 ?_ ?_) ?_ ?_
      · rw [hle8, huo 8 (by omega) (by omega)]; omega
      · rw [hle8]; exact hobj_ok 8 (by omega) (by omega) m4 (mem_grows_refl m4)
      · rw [hle8, huo 16 (by omega) (by omega)]; omega
      · rw [hle8, hm5]; exact hobj_ok 16 (by omega) (by omega) m5 hg5
    · -- the stack window
      rw [← hm6, ← hm5]
      exact stk_wb rsegs _ _ _ _ _ (stk_wb rsegs m4 _ _ _ _ hstk4)
    · -- the structure the call leaves behind
      refine ⟨⟨?_, by simp [knock_cells, cells_wf, cell_wf]⟩, ?_⟩
      · have h1 := bytes_at_wb_in rsegs m4 (bv_unsigned (getr regs 10))
          (List.replicate 40 (Z_to_bv 8 0 : byte)) 8 8
          (word_to_le_bytes 8 (getr regs 11)) hba4 rfl
          (by rw [List.length_replicate]; omega)
          (by rw [hle8, List.length_replicate]; omega)
        rw [hm5] at h1
        have h2 := bytes_at_wb_in rsegs m5 (bv_unsigned (getr regs 10)) _ 16 16
          (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (getr regs 11) + L_NS))) h1 rfl
          (by rw [List.length_append, List.length_append, hle8, List.length_take,
                List.length_drop, List.length_replicate]; omega)
          (by rw [hle8, List.length_append, List.length_append, hle8, List.length_take,
                List.length_drop, List.length_replicate]; omega)
        rw [hm6] at h2
        simp only [hle8] at h2
        have hlist : ((List.replicate 40 (Z_to_bv 8 0 : byte)).take 8
              ++ word_to_le_bytes 8 (getr regs 11)
              ++ (List.replicate 40 (Z_to_bv 8 0 : byte)).drop 16).take 16
            ++ word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (getr regs 11) + L_NS))
            ++ ((List.replicate 40 (Z_to_bv 8 0 : byte)).take 8
              ++ word_to_le_bytes 8 (getr regs 11)
              ++ (List.replicate 40 (Z_to_bv 8 0 : byte)).drop 16).drop 24
            = cells_bytes (knock_cells 0 (Z_to_bv 64 0) (getr regs 11)
                (Z_to_bv 64 (bv_unsigned (getr regs 11) + L_NS))
                (Z_to_bv 64 0) 0 (Z_to_bv 64 0)) := by rfl
        rw [hlist] at h2
        exact h2
      · exact wr_at_grows rsegs m4 _ _ _ (mem_grows_trans _ _ _ hg5 hg6) hwr4'
