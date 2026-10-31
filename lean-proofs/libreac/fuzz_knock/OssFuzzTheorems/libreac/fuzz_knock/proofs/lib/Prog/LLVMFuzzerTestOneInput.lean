-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput.v
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.LLVMFuzzerTestOneInput_c
import OssFuzzTheorems.libreac.fuzz_knock.Image.PlainCode
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.StoreOk

/-! `lib/Prog/LLVMFuzzerTestOneInput.v`: the walk of the fuzz harness entry.

Every path in this docstring is in theorem-labs/oss-verify-proofs-internal
`ossv/recipes` `9b0ac6f0e6`, under `projects/libreac/fuzz_knock/proofs/`,
unless it names its own repository.

WHAT IS PROVED HERE. `knock_big_holds` reaches `Qk`, the whole post-state of
`knock_main_contract` (`lib/Prog/LLVMFuzzerTestOneInput_c.v:11-33`), on the
inputs the harness rejects at once: those whose length `a1` has a set bit at
26 or above. That is the path `knock_entry`'s `if_cases EBIG` takes
(`lib/Prog/LLVMFuzzerTestOneInput.v:424-425`): the 16 instructions of the
prologue `0x12adc`-`0x12b18`, and then, through the taken `bne`, the 16
instructions of `knock_exit`'s epilogue `0x12d0c`-`0x12d48` (`:44-75`). Those
32 of the 157 instructions of `LLVMFuzzerTestOneInput` are stepped through the
Lean model's own `RiscvSemantics.step`, over the real bytes of
`fuzz_knock.plain`, with the fetch and decode facts the image module generates
(`Image/PlainCode.lean`'s `F_<pc>` and `D_<pc>`).

WHAT IS NOT PROVED HERE. The other 125 instructions: `knock_entry`'s header
parse and `knock_parsed`, `knock_loop`, `knock_tail`, `knock_mid` and
`knock_checks` (`lib/Prog/LLVMFuzzerTestOneInput.v:77-463`). They call
`reac_knock_init`, `reac_knock_heard`, `reac_knock_step` and `memset`, and
their Rocq proof rests on a reading, writing and framing theory of `rw_cells`,
`cells_at` and `stk` (`lib/Lib/Step.v`, 824 lines; `lib/Lib/Cells.v`, 227;
`lib/Lib/Frame.v`, 245; `lib/Lib/StepFast.v`, 2863) that the Lean twin of
`lib/Lib/` does not carry. OSSV-265 gaps rows K1H-4 and K1H-5.

The path below needs none of that theory: it writes 13 words below `sp` and
reads the same 13 words back, so `frame` and its lemmas stand in for
`rw_cells` (gaps row K1H-4). -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.LLVMFuzzerTestOneInput

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.StoreOk
open OssFuzzTheorems.libreac.fuzz_knock.Image.PlainCode
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Img0 (rsegs)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem (wa mrd mem_inv ro_addr)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame (munch outside wmono stk)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec (evt evt_done evt_step mstep_mkst)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState (ret_pc)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.LLVMFuzzerTestOneInput_c

set_option maxHeartbeats 4000000

/-! ## Literal arithmetic -/

/-- The twin of `lib/Lib/Mem.v:106` (`unsigned_lit`): a literal in range
reads back. -/
private theorem bvu_lit (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    bv_unsigned (Z_to_bv 64 z) = z := by
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  exact Int.emod_eq_of_lt h0 h1

/-- What Rocq's `addr_eq_tac` closes
(`lib/Prog/LLVMFuzzerTestOneInput.v:11-12`): an `sp + k` address in literal
form. -/
private theorem vaddi_at (x : word) (S : Int) (imm : BitVec 12) (t : Int)
    (hx : x = Z_to_bv 64 S) (h0 : 0 ≤ S) (h1 : S < 2 ^ 64)
    (ht : S + bv_signed imm = t) :
    v_addi x (bv_signed imm) = Z_to_bv 64 t := by
  subst hx
  unfold v_addi
  rw [bvu_lit S h0 h1, ht]

/-- `lib/Lib/MState.v:140`'s `ret_pc` IS the model's `jalr` target at offset
zero (OSSV-265 gaps row T-9: the Lean library spells it `SeqExec.v_jalr`). -/
private theorem ret_pc_jalr (a : word) : v_jalr a (bv_signed (0 : BitVec 12)) = ret_pc a := by
  have h := b_jalr a 0
  rw [show sext 64 (0 : BitVec 12) = (0 : word) from by decide] at h
  rw [show a + (0 : word) = a from by simp] at h
  exact h.symm

/-! ## The written frame

`frame base m ps` is `m` after the 13 stores of the prologue: 8 bytes at
`base - k` for each `(k, v)` of `ps`. It stands in for the Rocq proof's
`rw_cells rsegs m (sp - 144) (cs40 ++ saved)`
(`lib/Prog/LLVMFuzzerTestOneInput.v:48`), whose `cells` reading and writing
theory has no Lean twin (OSSV-265 gaps row K1H-4). -/

/-- The 13 words the prologue saves below `sp`, as `(offset below sp, value)`
pairs in the order `lib/Prog/LLVMFuzzerTestOneInput.v` writes them. The Rocq
proof calls the same bytes `saved` (`:31-32`). -/
private def savedList (regs : bvmap 5 word) : List (Int × word) :=
  [(8, getr regs 1), (16, getr regs 8), (24, getr regs 9), (32, getr regs 18), (40, getr regs 19), (48, getr regs 20), (56, getr regs 21), (64, getr regs 22), (72, getr regs 23), (80, getr regs 24), (88, getr regs 25), (96, getr regs 26), (104, getr regs 27)]

private def frame (base : Int) (m : word → Option byte) :
    List (Int × word) → (word → Option byte)
  | [] => m
  | (k, v) :: rest =>
    frame base (wbytes m (Z_to_bv 64 (base - k)) (word_to_le_bytes 8 v)) rest

private theorem frame_cons (base : Int) (m : word → Option byte) (k : Int) (v : word)
    (rest : List (Int × word)) :
    frame base m ((k, v) :: rest)
      = frame base (wbytes m (Z_to_bv 64 (base - k)) (word_to_le_bytes 8 v)) rest := rfl

private theorem frame_app (base : Int) (ps qs : List (Int × word)) :
    ∀ m : word → Option byte,
      frame base m (ps ++ qs) = frame base (frame base m ps) qs := by
  have e1 : ∀ (p : Int × word) (mm : word → Option byte) (l : List (Int × word)),
      frame base mm (p :: l)
        = frame base (wbytes mm (Z_to_bv 64 (base - p.1)) (word_to_le_bytes 8 p.2)) l := by
    intro p mm l; cases p; rfl
  induction ps with
  | nil => intro m; rfl
  | cons p rest ih =>
    intro m
    rw [List.cons_append, e1 p m (rest ++ qs), ih, e1 p m rest]

/-- `List.all` decides the offset side conditions of the `frame` lemmas on a
literal list, without looking at the saved values. -/
private theorem offs_ok (k : Int) (ps : List (Int × word))
    (h : ps.all (fun p => decide (k + 8 ≤ p.1) && decide (p.1 ≤ 104)) = true) :
    ∀ p ∈ ps, k + 8 ≤ p.1 ∧ p.1 ≤ 104 := by
  intro p hp
  have hb := (List.all_eq_true.mp h) p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  exact hb

private theorem offs_ok8 (ps : List (Int × word))
    (h : ps.all (fun p => decide (8 ≤ p.1) && decide (p.1 ≤ 104)) = true) :
    ∀ p ∈ ps, 8 ≤ p.1 ∧ p.1 ≤ 104 := by
  intro p hp
  have hb := (List.all_eq_true.mp h) p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  exact hb

private theorem frame_grows (base : Int) (ps : List (Int × word)) :
    ∀ m : word → Option byte, mem_grows m (frame base m ps) := by
  induction ps with
  | nil => intro m; exact mem_grows_refl m
  | cons p rest ih =>
    intro m
    have e1 : frame base m (p :: rest)
        = frame base (wbytes m (Z_to_bv 64 (base - p.1)) (word_to_le_bytes 8 p.2)) rest := by
      cases p; rfl
    rw [e1]
    exact mem_grows_trans _ _ _ (wbytes_grows _ m _) (ih _)

/-- One write, read away from it. -/
private theorem wbytes_out (bs : List byte) (m : word → Option byte) (addr x : word)
    (hnw : bv_unsigned addr + (bs.length : Int) ≤ 2 ^ 64)
    (h : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + (bs.length : Int) ≤ bv_unsigned x) :
    wbytes m addr bs x = m x := by
  rcases h with h | h
  · exact wbytes_below bs m addr x hnw h
  · exact wbytes_above bs m addr x h

/-- Every byte outside `[base - 104, base)` is the byte it was: the `munch`
of `lib/Lib/Frame.v:71-72` for this frame. -/
private theorem frame_away (base : Int) (ps : List (Int × word)) (x : word)
    (hb : 104 ≤ base) (hb' : base < 2 ^ 64)
    (hx : bv_unsigned x < base - 104 ∨ base ≤ bv_unsigned x) :
    ∀ m : word → Option byte, (∀ p ∈ ps, 8 ≤ p.1 ∧ p.1 ≤ 104) →
      frame base m ps x = m x := by
  induction ps with
  | nil => intro m _; rfl
  | cons p rest ih =>
    intro m hps
    have hp := hps p (by simp)
    have hrest : ∀ q ∈ rest, 8 ≤ q.1 ∧ q.1 ≤ 104 :=
      fun q hq => hps q (List.mem_cons_of_mem p hq)
    have hlen : (word_to_le_bytes 8 p.2).length = 8 := length_N_to_le_bytes 8 p.2
    have hu : bv_unsigned (Z_to_bv 64 (base - p.1)) = base - p.1 :=
      bvu_lit _ (by omega) (by omega)
    have e1 : frame base m (p :: rest)
        = frame base (wbytes m (Z_to_bv 64 (base - p.1)) (word_to_le_bytes 8 p.2)) rest := by
      cases p; rfl
    rw [e1, ih _ hrest, wbytes_out _ m _ x (by rw [hu, hlen]; omega)
      (by rw [hu, hlen]; omega)]

/-- A read at `base - k` is above every write of `ps` and sees through
them. -/
private theorem frame_rd_hi (segs : List Segment) (base : Int)
    (ps : List (Int × word)) (k : Int)
    (hb : 104 ≤ base) (hb' : base < 2 ^ 64) (hk : 8 ≤ k) (hk' : k ≤ 104) :
    ∀ m : word → Option byte, (∀ p ∈ ps, k + 8 ≤ p.1 ∧ p.1 ≤ 104) →
      rdn segs (frame base m ps) (Z_to_bv 64 (base - k)) 8
        = rdn segs m (Z_to_bv 64 (base - k)) 8 := by
  have hu2 : bv_unsigned (Z_to_bv 64 (base - k)) = base - k :=
    bvu_lit _ (by omega) (by omega)
  induction ps with
  | nil => intro m _; rfl
  | cons p rest ih =>
    intro m hps
    have hp := hps p (by simp)
    have hrest : ∀ q ∈ rest, k + 8 ≤ q.1 ∧ q.1 ≤ 104 :=
      fun q hq => hps q (List.mem_cons_of_mem p hq)
    have hlen : (word_to_le_bytes 8 p.2).length = 8 := length_N_to_le_bytes 8 p.2
    have hu : bv_unsigned (Z_to_bv 64 (base - p.1)) = base - p.1 :=
      bvu_lit _ (by omega) (by omega)
    have e1 : frame base m (p :: rest)
        = frame base (wbytes m (Z_to_bv 64 (base - p.1)) (word_to_le_bytes 8 p.2)) rest := by
      cases p; rfl
    rw [e1, ih _ hrest,
      rdn_wbytes_out segs _ m _ _ 8 (by rw [hu, hu2, hlen]; omega)
        (by rw [hu2]; omega) (by rw [hu, hlen]; omega)]

/-- The slot a write just filled reads back. -/
private theorem rd_hit8 (segs : List Segment) (m : word → Option byte) (base k : Int)
    (v : word) (h0 : 0 ≤ base - k) (h1 : base - k + 8 ≤ 2 ^ 64) :
    rdn segs (wbytes m (Z_to_bv 64 (base - k)) (word_to_le_bytes 8 v))
        (Z_to_bv 64 (base - k)) 8 = some (word_to_le_bytes 8 v) :=
  rdn_wbytes_hit8 segs m _ v (by rw [bvu_lit _ h0 (by omega)]; omega)

/-! ## `stk` and `mem_inv` under the frame -/

/-- A byte the kernel may write is not a read-only byte: `wview`'s fallback
and `ro_addr` (`lib/Lib/Mem.v:74-78`) read the SAME `find_segment`. The Rocq
proof gets this from `mem_inv_from_entry` (`lib/Lib/Mem.v`). -/
private theorem ro_false_of_wview (segs : List Segment) (m : word → Option byte)
    (hmi : mem_inv segs m) (x : word) (h : wview segs m x ≠ none) :
    ro_addr segs x = false := by
  cases hm : m x with
  | some b => exact hmi x b hm
  | none =>
    unfold ro_addr
    unfold wview at h
    rw [hm] at h
    cases hf : find_segment segs (bv_unsigned x) 1 with
    | none => simp only [hf] at h; exact absurd rfl h
    | some seg =>
      simp only [hf] at h ⊢
      cases hw : seg_writable seg with
      | false => simp only [hw, Bool.false_eq_true, ↓reduceIte] at h; exact absurd rfl h
      | true => simp only [Bool.not_true]

/-- A store inside the caller's stack window is allowed. -/
private theorem store_ok_stk (segs : List Segment) (m m' : word → Option byte)
    (lo hi a : Int) (n : Nat)
    (hstk : stk segs m lo hi) (hg : mem_grows m m')
    (h0 : 0 ≤ a) (ha : a < 2 ^ 64) (h1 : lo ≤ a) (h2 : a + (n : Int) ≤ hi)
    (h3 : a + (n : Int) ≤ 2 ^ 64) :
    store_ok segs m' (Z_to_bv 64 a) n = true := by
  refine store_ok_of_all segs n m' (Z_to_bv 64 a) (by rw [bvu_lit a h0 ha]; exact h3) ?_
  intro x hx
  rw [bvu_lit a h0 ha] at hx
  have hw := (hstk.2.2 (bv_unsigned x) (by omega) (by omega)).1
  rw [show wa (bv_unsigned x) = x from Z_to_bv_bv_unsigned64 x] at hw
  exact wview_grows segs m m' x hg hw

private theorem mrd_grows (segs : List Segment) (m m' : word → Option byte)
    (hg : mem_grows m m') (x : word) (h : ∃ b, mrd segs m x = some b) :
    ∃ b, mrd segs m' x = some b := by
  obtain ⟨b, hb⟩ := h
  unfold mrd at hb ⊢
  cases hm' : m' x with
  | some c => exact ⟨c, rfl⟩
  | none =>
    have hm : m x = none := by
      cases hmm : m x with
      | none => rfl
      | some d => exact absurd hm' (hg x (by rw [hmm]; exact Option.some_ne_none d))
    rw [hm] at hb
    exact ⟨b, hb⟩

private theorem frame_mem_inv (segs : List Segment) (base : Int)
    (ps : List (Int × word))
    (hb : 104 ≤ base) (hb' : base < 2 ^ 64)
    (hro : ∀ x : word, base - 104 ≤ bv_unsigned x → bv_unsigned x < base →
      ro_addr segs x = false) :
    ∀ m : word → Option byte, (∀ p ∈ ps, 8 ≤ p.1 ∧ p.1 ≤ 104) →
      mem_inv segs m → mem_inv segs (frame base m ps) := by
  induction ps with
  | nil => intro m _ hmi; exact hmi
  | cons p rest ih =>
    intro m hps hmi
    have hp := hps p (by simp)
    have hrest : ∀ q ∈ rest, 8 ≤ q.1 ∧ q.1 ≤ 104 :=
      fun q hq => hps q (List.mem_cons_of_mem p hq)
    have hlen : (word_to_le_bytes 8 p.2).length = 8 := length_N_to_le_bytes 8 p.2
    have hu : bv_unsigned (Z_to_bv 64 (base - p.1)) = base - p.1 :=
      bvu_lit _ (by omega) (by omega)
    have e1 : frame base m (p :: rest)
        = frame base (wbytes m (Z_to_bv 64 (base - p.1)) (word_to_le_bytes 8 p.2)) rest := by
      cases p; rfl
    rw [e1]
    refine ih _ hrest ?_
    intro x b hx
    by_cases hin : base - p.1 ≤ bv_unsigned x ∧ bv_unsigned x < base - p.1 + 8
    · exact hro x (by omega) (by omega)
    · rw [wbytes_out _ m _ x (by rw [hu, hlen]; omega) (by rw [hu, hlen]; omega)] at hx
      exact hmi x b hx

/-! ## The walk

`SP regs` is the caller's stack pointer, the Rocq section variable `sp`
(`lib/Prog/LLVMFuzzerTestOneInput.v:24`), as an `Int`. -/

private abbrev SP (regs : bvmap 5 word) : Int := bv_unsigned (getr regs 2)

private abbrev AD (regs : bvmap 5 word) (k : Int) : word := Z_to_bv 64 (SP regs - k)

/-- `knock_exit` (`lib/Prog/LLVMFuzzerTestOneInput.v:44-75`): from `0x12d0c`,
with the 13 callee-saved words still in the frame, the function restores them,
pops 144 bytes and returns `0`.

As in Rocq, the register file at entry is arbitrary; `hsp`, `hgp` and `htp` are
the three registers the Rocq statement names (`sp`, and `gp`/`tp`, which the
Rocq `mkR` carries unchanged from the section variables). -/
private theorem knock_exit_big (regs regsE : bvmap 5 word) (m : word → Option byte)
    (lo : Int)
    (hmi : mem_inv rsegs m)
    (hstk : stk rsegs m lo (SP regs))
    (hstack : lo + 176 ≤ SP regs)
    (hsp : getr regsE 2 = Z_to_bv 64 (SP regs - 144))
    (hgp : getr regsE 3 = getr regs 3)
    (htp : getr regsE 4 = getr regs 4) :
    evt rsegs (Qk regs m lo)
      (mkst regsE (0x12d0c : word) (frame (SP regs) m (savedList regs))
        (seg_rom rsegs)) := by
  have hsr := u64_range (getr regs 2)
  have hlo0 : (0 : Int) ≤ lo := hstk.1
  have hS0 : (176 : Int) ≤ SP regs := by omega
  have hS1 : SP regs < 2 ^ 64 := hsr.2
  have hsp0 : getr regs 2 = Z_to_bv 64 (SP regs) := (Z_to_bv_bv_unsigned64 _).symm
  have hro : ∀ x : word, SP regs - 104 ≤ bv_unsigned x → bv_unsigned x < SP regs →
      ro_addr rsegs x = false := by
    intro x h1 h2
    refine ro_false_of_wview rsegs m hmi x ?_
    have hw := (hstk.2.2 (bv_unsigned x) (by omega) (by omega)).1
    rwa [show wa (bv_unsigned x) = x from Z_to_bv_bv_unsigned64 x] at hw
  have hpsAll : ∀ p ∈ savedList regs, 8 ≤ p.1 ∧ p.1 ≤ 104 :=
    offs_ok8 _ (by simp only [savedList]; rfl)
  have hrd8 : rdn rsegs (frame (SP regs) m (savedList regs)) (AD regs 8) 8
      = some (word_to_le_bytes 8 (getr regs 1)) := by
    rw [show savedList regs = (savedList regs).take 0
          ++ ((8 : Int), getr regs 1) :: (savedList regs).drop 1
        from by simp only [savedList]; rfl, frame_app, frame_cons]
    exact (frame_rd_hi rsegs (SP regs) ((savedList regs).drop 1) 8
        (by omega) (by omega) (by omega) (by omega) _
        (offs_ok 8 _ (by simp only [savedList]; rfl))).trans
      (rd_hit8 rsegs _ (SP regs) 8 (getr regs 1) (by omega) (by omega))
  have hrd16 : rdn rsegs (frame (SP regs) m (savedList regs)) (AD regs 16) 8
      = some (word_to_le_bytes 8 (getr regs 8)) := by
    rw [show savedList regs = (savedList regs).take 1
          ++ ((16 : Int), getr regs 8) :: (savedList regs).drop 2
        from by simp only [savedList]; rfl, frame_app, frame_cons]
    exact (frame_rd_hi rsegs (SP regs) ((savedList regs).drop 2) 16
        (by omega) (by omega) (by omega) (by omega) _
        (offs_ok 16 _ (by simp only [savedList]; rfl))).trans
      (rd_hit8 rsegs _ (SP regs) 16 (getr regs 8) (by omega) (by omega))
  have hrd24 : rdn rsegs (frame (SP regs) m (savedList regs)) (AD regs 24) 8
      = some (word_to_le_bytes 8 (getr regs 9)) := by
    rw [show savedList regs = (savedList regs).take 2
          ++ ((24 : Int), getr regs 9) :: (savedList regs).drop 3
        from by simp only [savedList]; rfl, frame_app, frame_cons]
    exact (frame_rd_hi rsegs (SP regs) ((savedList regs).drop 3) 24
        (by omega) (by omega) (by omega) (by omega) _
        (offs_ok 24 _ (by simp only [savedList]; rfl))).trans
      (rd_hit8 rsegs _ (SP regs) 24 (getr regs 9) (by omega) (by omega))
  have hrd32 : rdn rsegs (frame (SP regs) m (savedList regs)) (AD regs 32) 8
      = some (word_to_le_bytes 8 (getr regs 18)) := by
    rw [show savedList regs = (savedList regs).take 3
          ++ ((32 : Int), getr regs 18) :: (savedList regs).drop 4
        from by simp only [savedList]; rfl, frame_app, frame_cons]
    exact (frame_rd_hi rsegs (SP regs) ((savedList regs).drop 4) 32
        (by omega) (by omega) (by omega) (by omega) _
        (offs_ok 32 _ (by simp only [savedList]; rfl))).trans
      (rd_hit8 rsegs _ (SP regs) 32 (getr regs 18) (by omega) (by omega))
  have hrd40 : rdn rsegs (frame (SP regs) m (savedList regs)) (AD regs 40) 8
      = some (word_to_le_bytes 8 (getr regs 19)) := by
    rw [show savedList regs = (savedList regs).take 4
          ++ ((40 : Int), getr regs 19) :: (savedList regs).drop 5
        from by simp only [savedList]; rfl, frame_app, frame_cons]
    exact (frame_rd_hi rsegs (SP regs) ((savedList regs).drop 5) 40
        (by omega) (by omega) (by omega) (by omega) _
        (offs_ok 40 _ (by simp only [savedList]; rfl))).trans
      (rd_hit8 rsegs _ (SP regs) 40 (getr regs 19) (by omega) (by omega))
  have hrd48 : rdn rsegs (frame (SP regs) m (savedList regs)) (AD regs 48) 8
      = some (word_to_le_bytes 8 (getr regs 20)) := by
    rw [show savedList regs = (savedList regs).take 5
          ++ ((48 : Int), getr regs 20) :: (savedList regs).drop 6
        from by simp only [savedList]; rfl, frame_app, frame_cons]
    exact (frame_rd_hi rsegs (SP regs) ((savedList regs).drop 6) 48
        (by omega) (by omega) (by omega) (by omega) _
        (offs_ok 48 _ (by simp only [savedList]; rfl))).trans
      (rd_hit8 rsegs _ (SP regs) 48 (getr regs 20) (by omega) (by omega))
  have hrd56 : rdn rsegs (frame (SP regs) m (savedList regs)) (AD regs 56) 8
      = some (word_to_le_bytes 8 (getr regs 21)) := by
    rw [show savedList regs = (savedList regs).take 6
          ++ ((56 : Int), getr regs 21) :: (savedList regs).drop 7
        from by simp only [savedList]; rfl, frame_app, frame_cons]
    exact (frame_rd_hi rsegs (SP regs) ((savedList regs).drop 7) 56
        (by omega) (by omega) (by omega) (by omega) _
        (offs_ok 56 _ (by simp only [savedList]; rfl))).trans
      (rd_hit8 rsegs _ (SP regs) 56 (getr regs 21) (by omega) (by omega))
  have hrd64 : rdn rsegs (frame (SP regs) m (savedList regs)) (AD regs 64) 8
      = some (word_to_le_bytes 8 (getr regs 22)) := by
    rw [show savedList regs = (savedList regs).take 7
          ++ ((64 : Int), getr regs 22) :: (savedList regs).drop 8
        from by simp only [savedList]; rfl, frame_app, frame_cons]
    exact (frame_rd_hi rsegs (SP regs) ((savedList regs).drop 8) 64
        (by omega) (by omega) (by omega) (by omega) _
        (offs_ok 64 _ (by simp only [savedList]; rfl))).trans
      (rd_hit8 rsegs _ (SP regs) 64 (getr regs 22) (by omega) (by omega))
  have hrd72 : rdn rsegs (frame (SP regs) m (savedList regs)) (AD regs 72) 8
      = some (word_to_le_bytes 8 (getr regs 23)) := by
    rw [show savedList regs = (savedList regs).take 8
          ++ ((72 : Int), getr regs 23) :: (savedList regs).drop 9
        from by simp only [savedList]; rfl, frame_app, frame_cons]
    exact (frame_rd_hi rsegs (SP regs) ((savedList regs).drop 9) 72
        (by omega) (by omega) (by omega) (by omega) _
        (offs_ok 72 _ (by simp only [savedList]; rfl))).trans
      (rd_hit8 rsegs _ (SP regs) 72 (getr regs 23) (by omega) (by omega))
  have hrd80 : rdn rsegs (frame (SP regs) m (savedList regs)) (AD regs 80) 8
      = some (word_to_le_bytes 8 (getr regs 24)) := by
    rw [show savedList regs = (savedList regs).take 9
          ++ ((80 : Int), getr regs 24) :: (savedList regs).drop 10
        from by simp only [savedList]; rfl, frame_app, frame_cons]
    exact (frame_rd_hi rsegs (SP regs) ((savedList regs).drop 10) 80
        (by omega) (by omega) (by omega) (by omega) _
        (offs_ok 80 _ (by simp only [savedList]; rfl))).trans
      (rd_hit8 rsegs _ (SP regs) 80 (getr regs 24) (by omega) (by omega))
  have hrd88 : rdn rsegs (frame (SP regs) m (savedList regs)) (AD regs 88) 8
      = some (word_to_le_bytes 8 (getr regs 25)) := by
    rw [show savedList regs = (savedList regs).take 10
          ++ ((88 : Int), getr regs 25) :: (savedList regs).drop 11
        from by simp only [savedList]; rfl, frame_app, frame_cons]
    exact (frame_rd_hi rsegs (SP regs) ((savedList regs).drop 11) 88
        (by omega) (by omega) (by omega) (by omega) _
        (offs_ok 88 _ (by simp only [savedList]; rfl))).trans
      (rd_hit8 rsegs _ (SP regs) 88 (getr regs 25) (by omega) (by omega))
  have hrd96 : rdn rsegs (frame (SP regs) m (savedList regs)) (AD regs 96) 8
      = some (word_to_le_bytes 8 (getr regs 26)) := by
    rw [show savedList regs = (savedList regs).take 11
          ++ ((96 : Int), getr regs 26) :: (savedList regs).drop 12
        from by simp only [savedList]; rfl, frame_app, frame_cons]
    exact (frame_rd_hi rsegs (SP regs) ((savedList regs).drop 12) 96
        (by omega) (by omega) (by omega) (by omega) _
        (offs_ok 96 _ (by simp only [savedList]; rfl))).trans
      (rd_hit8 rsegs _ (SP regs) 96 (getr regs 26) (by omega) (by omega))
  have hrd104 : rdn rsegs (frame (SP regs) m (savedList regs)) (AD regs 104) 8
      = some (word_to_le_bytes 8 (getr regs 27)) := by
    rw [show savedList regs = (savedList regs).take 12
          ++ ((104 : Int), getr regs 27) :: (savedList regs).drop 13
        from by simp only [savedList]; rfl, frame_app, frame_cons]
    exact (frame_rd_hi rsegs (SP regs) ((savedList regs).drop 13) 104
        (by omega) (by omega) (by omega) (by omega) _
        (offs_ok 104 _ (by simp only [savedList]; rfl))).trans
      (rd_hit8 rsegs _ (SP regs) 104 (getr regs 27) (by omega) (by omega))
  -- 0x12d0c  addi a0, x0, 0
  refine evt_step (mstep_mkst (step_addi_at rsegs _ (0x12d0c : word) _ _ _ 10 0 0
      (Z_to_bv 64 0) F_12d0c (by decide) D_12d0c (by decide)
      (by rw [getr_zero]; decide +kernel))) ?_
  rw [show v_addi (0x12d0c : word) 4 = (0x12d10 : word) from by decide +kernel]
  have hspL0 := (getr_other regsE 10 (Z_to_bv 64 0) 2 (by decide)).trans hsp
  -- 0x12d10  ld ra, 136(sp)
  refine evt_step (mstep_mkst (step_ld rsegs _ (0x12d10 : word) _ _ _ 1 2 0x88
      (word_to_le_bytes 8 (getr regs 1)) (getr regs 1)
      F_12d10 (by decide) D_12d10
      (by rw [vaddi_at _ (SP regs - 144) 0x88 (SP regs - 8) hspL0 (by omega) (by omega)
             (by rw [show bv_signed (0x88 : BitVec 12) = (136 : Int) from by decide]; omega)]
          exact hrd8)
      (bytes_le_to_Z_8 _))) ?_
  simp only [show bv_eqb (1 : reg) 0 = false from by decide, Bool.false_eq_true,
    ↓reduceIte]
  rw [show v_addi (0x12d10 : word) 4 = (0x12d14 : word) from by decide +kernel]
  have hspL1 :=
    (getr_other _ 1 (getr regs 1) 2 (by decide)).trans hspL0
  -- 0x12d14  ld s0, 128(sp)
  refine evt_step (mstep_mkst (step_ld rsegs _ (0x12d14 : word) _ _ _ 8 2 0x80
      (word_to_le_bytes 8 (getr regs 8)) (getr regs 8)
      F_12d14 (by decide) D_12d14
      (by rw [vaddi_at _ (SP regs - 144) 0x80 (SP regs - 16) hspL1 (by omega) (by omega)
             (by rw [show bv_signed (0x80 : BitVec 12) = (128 : Int) from by decide]; omega)]
          exact hrd16)
      (bytes_le_to_Z_8 _))) ?_
  simp only [show bv_eqb (8 : reg) 0 = false from by decide, Bool.false_eq_true,
    ↓reduceIte]
  rw [show v_addi (0x12d14 : word) 4 = (0x12d18 : word) from by decide +kernel]
  have hspL2 :=
    (getr_other _ 8 (getr regs 8) 2 (by decide)).trans hspL1
  -- 0x12d18  ld s1, 120(sp)
  refine evt_step (mstep_mkst (step_ld rsegs _ (0x12d18 : word) _ _ _ 9 2 0x78
      (word_to_le_bytes 8 (getr regs 9)) (getr regs 9)
      F_12d18 (by decide) D_12d18
      (by rw [vaddi_at _ (SP regs - 144) 0x78 (SP regs - 24) hspL2 (by omega) (by omega)
             (by rw [show bv_signed (0x78 : BitVec 12) = (120 : Int) from by decide]; omega)]
          exact hrd24)
      (bytes_le_to_Z_8 _))) ?_
  simp only [show bv_eqb (9 : reg) 0 = false from by decide, Bool.false_eq_true,
    ↓reduceIte]
  rw [show v_addi (0x12d18 : word) 4 = (0x12d1c : word) from by decide +kernel]
  have hspL3 :=
    (getr_other _ 9 (getr regs 9) 2 (by decide)).trans hspL2
  -- 0x12d1c  ld s2, 112(sp)
  refine evt_step (mstep_mkst (step_ld rsegs _ (0x12d1c : word) _ _ _ 18 2 0x70
      (word_to_le_bytes 8 (getr regs 18)) (getr regs 18)
      F_12d1c (by decide) D_12d1c
      (by rw [vaddi_at _ (SP regs - 144) 0x70 (SP regs - 32) hspL3 (by omega) (by omega)
             (by rw [show bv_signed (0x70 : BitVec 12) = (112 : Int) from by decide]; omega)]
          exact hrd32)
      (bytes_le_to_Z_8 _))) ?_
  simp only [show bv_eqb (18 : reg) 0 = false from by decide, Bool.false_eq_true,
    ↓reduceIte]
  rw [show v_addi (0x12d1c : word) 4 = (0x12d20 : word) from by decide +kernel]
  have hspL4 :=
    (getr_other _ 18 (getr regs 18) 2 (by decide)).trans hspL3
  -- 0x12d20  ld s3, 104(sp)
  refine evt_step (mstep_mkst (step_ld rsegs _ (0x12d20 : word) _ _ _ 19 2 0x68
      (word_to_le_bytes 8 (getr regs 19)) (getr regs 19)
      F_12d20 (by decide) D_12d20
      (by rw [vaddi_at _ (SP regs - 144) 0x68 (SP regs - 40) hspL4 (by omega) (by omega)
             (by rw [show bv_signed (0x68 : BitVec 12) = (104 : Int) from by decide]; omega)]
          exact hrd40)
      (bytes_le_to_Z_8 _))) ?_
  simp only [show bv_eqb (19 : reg) 0 = false from by decide, Bool.false_eq_true,
    ↓reduceIte]
  rw [show v_addi (0x12d20 : word) 4 = (0x12d24 : word) from by decide +kernel]
  have hspL5 :=
    (getr_other _ 19 (getr regs 19) 2 (by decide)).trans hspL4
  -- 0x12d24  ld s4, 96(sp)
  refine evt_step (mstep_mkst (step_ld rsegs _ (0x12d24 : word) _ _ _ 20 2 0x60
      (word_to_le_bytes 8 (getr regs 20)) (getr regs 20)
      F_12d24 (by decide) D_12d24
      (by rw [vaddi_at _ (SP regs - 144) 0x60 (SP regs - 48) hspL5 (by omega) (by omega)
             (by rw [show bv_signed (0x60 : BitVec 12) = (96 : Int) from by decide]; omega)]
          exact hrd48)
      (bytes_le_to_Z_8 _))) ?_
  simp only [show bv_eqb (20 : reg) 0 = false from by decide, Bool.false_eq_true,
    ↓reduceIte]
  rw [show v_addi (0x12d24 : word) 4 = (0x12d28 : word) from by decide +kernel]
  have hspL6 :=
    (getr_other _ 20 (getr regs 20) 2 (by decide)).trans hspL5
  -- 0x12d28  ld s5, 88(sp)
  refine evt_step (mstep_mkst (step_ld rsegs _ (0x12d28 : word) _ _ _ 21 2 0x58
      (word_to_le_bytes 8 (getr regs 21)) (getr regs 21)
      F_12d28 (by decide) D_12d28
      (by rw [vaddi_at _ (SP regs - 144) 0x58 (SP regs - 56) hspL6 (by omega) (by omega)
             (by rw [show bv_signed (0x58 : BitVec 12) = (88 : Int) from by decide]; omega)]
          exact hrd56)
      (bytes_le_to_Z_8 _))) ?_
  simp only [show bv_eqb (21 : reg) 0 = false from by decide, Bool.false_eq_true,
    ↓reduceIte]
  rw [show v_addi (0x12d28 : word) 4 = (0x12d2c : word) from by decide +kernel]
  have hspL7 :=
    (getr_other _ 21 (getr regs 21) 2 (by decide)).trans hspL6
  -- 0x12d2c  ld s6, 80(sp)
  refine evt_step (mstep_mkst (step_ld rsegs _ (0x12d2c : word) _ _ _ 22 2 0x50
      (word_to_le_bytes 8 (getr regs 22)) (getr regs 22)
      F_12d2c (by decide) D_12d2c
      (by rw [vaddi_at _ (SP regs - 144) 0x50 (SP regs - 64) hspL7 (by omega) (by omega)
             (by rw [show bv_signed (0x50 : BitVec 12) = (80 : Int) from by decide]; omega)]
          exact hrd64)
      (bytes_le_to_Z_8 _))) ?_
  simp only [show bv_eqb (22 : reg) 0 = false from by decide, Bool.false_eq_true,
    ↓reduceIte]
  rw [show v_addi (0x12d2c : word) 4 = (0x12d30 : word) from by decide +kernel]
  have hspL8 :=
    (getr_other _ 22 (getr regs 22) 2 (by decide)).trans hspL7
  -- 0x12d30  ld s7, 72(sp)
  refine evt_step (mstep_mkst (step_ld rsegs _ (0x12d30 : word) _ _ _ 23 2 0x48
      (word_to_le_bytes 8 (getr regs 23)) (getr regs 23)
      F_12d30 (by decide) D_12d30
      (by rw [vaddi_at _ (SP regs - 144) 0x48 (SP regs - 72) hspL8 (by omega) (by omega)
             (by rw [show bv_signed (0x48 : BitVec 12) = (72 : Int) from by decide]; omega)]
          exact hrd72)
      (bytes_le_to_Z_8 _))) ?_
  simp only [show bv_eqb (23 : reg) 0 = false from by decide, Bool.false_eq_true,
    ↓reduceIte]
  rw [show v_addi (0x12d30 : word) 4 = (0x12d34 : word) from by decide +kernel]
  have hspL9 :=
    (getr_other _ 23 (getr regs 23) 2 (by decide)).trans hspL8
  -- 0x12d34  ld s8, 64(sp)
  refine evt_step (mstep_mkst (step_ld rsegs _ (0x12d34 : word) _ _ _ 24 2 0x40
      (word_to_le_bytes 8 (getr regs 24)) (getr regs 24)
      F_12d34 (by decide) D_12d34
      (by rw [vaddi_at _ (SP regs - 144) 0x40 (SP regs - 80) hspL9 (by omega) (by omega)
             (by rw [show bv_signed (0x40 : BitVec 12) = (64 : Int) from by decide]; omega)]
          exact hrd80)
      (bytes_le_to_Z_8 _))) ?_
  simp only [show bv_eqb (24 : reg) 0 = false from by decide, Bool.false_eq_true,
    ↓reduceIte]
  rw [show v_addi (0x12d34 : word) 4 = (0x12d38 : word) from by decide +kernel]
  have hspL10 :=
    (getr_other _ 24 (getr regs 24) 2 (by decide)).trans hspL9
  -- 0x12d38  ld s9, 56(sp)
  refine evt_step (mstep_mkst (step_ld rsegs _ (0x12d38 : word) _ _ _ 25 2 0x38
      (word_to_le_bytes 8 (getr regs 25)) (getr regs 25)
      F_12d38 (by decide) D_12d38
      (by rw [vaddi_at _ (SP regs - 144) 0x38 (SP regs - 88) hspL10 (by omega) (by omega)
             (by rw [show bv_signed (0x38 : BitVec 12) = (56 : Int) from by decide]; omega)]
          exact hrd88)
      (bytes_le_to_Z_8 _))) ?_
  simp only [show bv_eqb (25 : reg) 0 = false from by decide, Bool.false_eq_true,
    ↓reduceIte]
  rw [show v_addi (0x12d38 : word) 4 = (0x12d3c : word) from by decide +kernel]
  have hspL11 :=
    (getr_other _ 25 (getr regs 25) 2 (by decide)).trans hspL10
  -- 0x12d3c  ld s10, 48(sp)
  refine evt_step (mstep_mkst (step_ld rsegs _ (0x12d3c : word) _ _ _ 26 2 0x30
      (word_to_le_bytes 8 (getr regs 26)) (getr regs 26)
      F_12d3c (by decide) D_12d3c
      (by rw [vaddi_at _ (SP regs - 144) 0x30 (SP regs - 96) hspL11 (by omega) (by omega)
             (by rw [show bv_signed (0x30 : BitVec 12) = (48 : Int) from by decide]; omega)]
          exact hrd96)
      (bytes_le_to_Z_8 _))) ?_
  simp only [show bv_eqb (26 : reg) 0 = false from by decide, Bool.false_eq_true,
    ↓reduceIte]
  rw [show v_addi (0x12d3c : word) 4 = (0x12d40 : word) from by decide +kernel]
  have hspL12 :=
    (getr_other _ 26 (getr regs 26) 2 (by decide)).trans hspL11
  -- 0x12d40  ld s11, 40(sp)
  refine evt_step (mstep_mkst (step_ld rsegs _ (0x12d40 : word) _ _ _ 27 2 0x28
      (word_to_le_bytes 8 (getr regs 27)) (getr regs 27)
      F_12d40 (by decide) D_12d40
      (by rw [vaddi_at _ (SP regs - 144) 0x28 (SP regs - 104) hspL12 (by omega) (by omega)
             (by rw [show bv_signed (0x28 : BitVec 12) = (40 : Int) from by decide]; omega)]
          exact hrd104)
      (bytes_le_to_Z_8 _))) ?_
  simp only [show bv_eqb (27 : reg) 0 = false from by decide, Bool.false_eq_true,
    ↓reduceIte]
  rw [show v_addi (0x12d40 : word) 4 = (0x12d44 : word) from by decide +kernel]
  have hspL13 :=
    (getr_other _ 27 (getr regs 27) 2 (by decide)).trans hspL12
  -- 0x12d44  addi sp, sp, 144
  refine evt_step (mstep_mkst (step_addi_at rsegs _ (0x12d44 : word) _ _ _ 2 2 0x90
      (getr regs 2) F_12d44 (by decide) D_12d44 (by decide)
      (by rw [vaddi_at _ (SP regs - 144) 0x90 (SP regs) hspL13 (by omega) (by omega)
             (by rw [show bv_signed (0x90 : BitVec 12) = (144 : Int) from by decide]; omega)]
          exact hsp0.symm))) ?_
  rw [show v_addi (0x12d44 : word) 4 = (0x12d48 : word) from by decide +kernel]
  -- 0x12d48  jalr x0, 0(ra)
  refine evt_step (mstep_mkst (step_jalr_x0 rsegs _ (0x12d48 : word) _ _ _ 1 0
      (getr regs 1) F_12d48 (by decide) D_12d48
      (by simp +decide only [getr_same, getr_other]))) ?_
  -- the post-state `Qk` (`lib/Prog/LLVMFuzzerTestOneInput.v:34-42`)
  rw [ret_pc_jalr]
  refine evt_done ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide only [getr_same, getr_other]
  · simp +decide only [getr_same, getr_other]
  · simp +decide only [getr_same]
  · simpa +decide only [getr_other] using hgp
  · simpa +decide only [getr_other] using htp
  · simp +decide only [getr_same, getr_other]
  · simp +decide only [getr_same, getr_other]
  · simp +decide only [getr_same, getr_other]
  · simp +decide only [getr_same, getr_other]
  · simp +decide only [getr_same, getr_other]
  · simp +decide only [getr_same, getr_other]
  · simp +decide only [getr_same, getr_other]
  · simp +decide only [getr_same, getr_other]
  · simp +decide only [getr_same, getr_other]
  · simp +decide only [getr_same, getr_other]
  · simp +decide only [getr_same, getr_other]
  · simp +decide only [getr_same, getr_other]
  · -- munch (`lib/Lib/Frame.v:71-72`)
    intro x hx
    have hx1 : bv_unsigned x < SP regs - 176 ∨ SP regs ≤ bv_unsigned x := by
      have h := hx.1
      simp only [LLVM_KNOCK_STACK] at h
      exact h
    exact frame_away (SP regs) (savedList regs) x (by omega) (by omega)
      (hx1.imp (fun h => by omega) id) m hpsAll
  · -- wmono (`lib/Lib/Frame.v:73-74`)
    intro x hx
    exact wview_grows rsegs m _ x (frame_grows (SP regs) (savedList regs) m) hx
  · -- mem_inv (`lib/Lib/Mem.v:82-83`)
    exact frame_mem_inv rsegs (SP regs) (savedList regs) (by omega) (by omega) hro m hpsAll hmi
  · -- stk (`lib/Lib/Frame.v:81-83`)
    refine ⟨hstk.1, hstk.2.1, ?_⟩
    intro a h1 h2
    exact ⟨wview_grows rsegs m _ _ (frame_grows (SP regs) (savedList regs) m)
        (hstk.2.2 a h1 h2).1,
      mrd_grows rsegs m _ (frame_grows (SP regs) (savedList regs) m) _ (hstk.2.2 a h1 h2).2⟩

/-- `knock_main_contract` (`lib/Prog/LLVMFuzzerTestOneInput_c.v:11-33`) on the
inputs the harness rejects at once: those whose length has a set bit at 26 or
above, so the `bne` at `0x12b18` is taken and `LLVMFuzzerTestOneInput` returns
`0` without parsing the header. This is the `EBIG` branch of `knock_entry`
(`lib/Prog/LLVMFuzzerTestOneInput.v:424-425`) followed by `knock_exit`
(`:44-75`).

`hbig` is the model's own `bne` condition at `0x12b18` on the value the `srl`
at `0x12b14` leaves in `a2`; Rocq states the same through `if_cases EBIG`.

Of the contract's eight hypotheses this needs three: `mem_inv` (`:16`), `stk`
(`:17`) and the frame bound (`:18`). The buffer hypotheses (`:14`, `:15`,
`:20`, `:21`) and the alignment (`:19`) are not used on this path, because the
path reads no input byte. -/
theorem knock_big_holds (regs : bvmap 5 word) (m : word → Option byte) (lo : Int)
    (hmi : mem_inv rsegs m)
    (hstk : stk rsegs m lo (SP regs))
    (hlo : lo + LLVM_KNOCK_STACK ≤ SP regs)
    (hbig : c_eq (v_srli (getr regs 11) 26) (Z_to_bv 64 0) = false) :
    evt rsegs (Qk regs m lo) (mkst regs (Z_to_bv 64 LLVM_KNOCK) m (seg_rom rsegs)) := by
  have hsr := u64_range (getr regs 2)
  have hlo0 : (0 : Int) ≤ lo := hstk.1
  have hstack : lo + 176 ≤ SP regs := by
    simpa only [LLVM_KNOCK_STACK] using hlo
  have hS0 : (176 : Int) ≤ SP regs := by omega
  have hS1 : SP regs < 2 ^ 64 := hsr.2
  have hsp0 : getr regs 2 = Z_to_bv 64 (SP regs) := (Z_to_bv_bv_unsigned64 _).symm
  rw [show Z_to_bv 64 LLVM_KNOCK = (0x12adc : word) from by decide +kernel]
  -- 0x12adc  addi sp, sp, -144
  refine evt_step (mstep_mkst (step_addi_at rsegs regs (0x12adc : word) m (seg_rom rsegs)
      0xf7010113 2 2 0xf70 (AD regs 144) F_12adc (by decide) D_12adc (by decide)
      (vaddi_at (getr regs 2) (SP regs) 0xf70 (SP regs - 144) hsp0 (by omega) hS1
        (by rw [show bv_signed (0xf70 : BitVec 12) = (-144 : Int) from by decide]; omega)))) ?_
  rw [show v_addi (0x12adc : word) 4 = (0x12ae0 : word) from by decide +kernel]
  have hsp2 : getr (regupd regs 2 (AD regs 144)) 2 = Z_to_bv 64 (SP regs - 144) :=
    getr_same regs 2 _ (by decide)
  have hg0 : mem_grows m m := mem_grows_refl m
  -- 0x12ae0  sd ra, 136(sp)   -> sp - 8
  refine evt_step (mstep_mkst (step_sd_at rsegs _ (0x12ae0 : word) _ _ _ 2 1 0x88
      (AD regs 8) (getr regs 1) F_12ae0 (by decide) D_12ae0
      (vaddi_at _ (SP regs - 144) 0x88 (SP regs - 8) hsp2 (by omega) (by omega)
        (by rw [show bv_signed (0x88 : BitVec 12) = (136 : Int) from by decide]; omega))
      (getr_other regs 2 _ 1 (by decide))
      (store_ok_stk rsegs m _ lo (SP regs) (SP regs - 8) 8 hstk hg0
        (by omega) (by omega) (by omega) (by omega) (by omega)))) ?_
  rw [show v_addi (0x12ae0 : word) 4 = (0x12ae4 : word) from by decide +kernel]
  have hg1 := mem_grows_trans _ _ _ hg0
    (wbytes_grows (word_to_le_bytes 8 (getr regs 1)) _ (AD regs 8))
  -- 0x12ae4  sd s0, 128(sp)   -> sp - 16
  refine evt_step (mstep_mkst (step_sd_at rsegs _ (0x12ae4 : word) _ _ _ 2 8 0x80
      (AD regs 16) (getr regs 8) F_12ae4 (by decide) D_12ae4
      (vaddi_at _ (SP regs - 144) 0x80 (SP regs - 16) hsp2 (by omega) (by omega)
        (by rw [show bv_signed (0x80 : BitVec 12) = (128 : Int) from by decide]; omega))
      (getr_other regs 2 _ 8 (by decide))
      (store_ok_stk rsegs m _ lo (SP regs) (SP regs - 16) 8 hstk hg1
        (by omega) (by omega) (by omega) (by omega) (by omega)))) ?_
  rw [show v_addi (0x12ae4 : word) 4 = (0x12ae8 : word) from by decide +kernel]
  have hg2 := mem_grows_trans _ _ _ hg1
    (wbytes_grows (word_to_le_bytes 8 (getr regs 8)) _ (AD regs 16))
  -- 0x12ae8  sd s1, 120(sp)   -> sp - 24
  refine evt_step (mstep_mkst (step_sd_at rsegs _ (0x12ae8 : word) _ _ _ 2 9 0x78
      (AD regs 24) (getr regs 9) F_12ae8 (by decide) D_12ae8
      (vaddi_at _ (SP regs - 144) 0x78 (SP regs - 24) hsp2 (by omega) (by omega)
        (by rw [show bv_signed (0x78 : BitVec 12) = (120 : Int) from by decide]; omega))
      (getr_other regs 2 _ 9 (by decide))
      (store_ok_stk rsegs m _ lo (SP regs) (SP regs - 24) 8 hstk hg2
        (by omega) (by omega) (by omega) (by omega) (by omega)))) ?_
  rw [show v_addi (0x12ae8 : word) 4 = (0x12aec : word) from by decide +kernel]
  have hg3 := mem_grows_trans _ _ _ hg2
    (wbytes_grows (word_to_le_bytes 8 (getr regs 9)) _ (AD regs 24))
  -- 0x12aec  sd s2, 112(sp)   -> sp - 32
  refine evt_step (mstep_mkst (step_sd_at rsegs _ (0x12aec : word) _ _ _ 2 18 0x70
      (AD regs 32) (getr regs 18) F_12aec (by decide) D_12aec
      (vaddi_at _ (SP regs - 144) 0x70 (SP regs - 32) hsp2 (by omega) (by omega)
        (by rw [show bv_signed (0x70 : BitVec 12) = (112 : Int) from by decide]; omega))
      (getr_other regs 2 _ 18 (by decide))
      (store_ok_stk rsegs m _ lo (SP regs) (SP regs - 32) 8 hstk hg3
        (by omega) (by omega) (by omega) (by omega) (by omega)))) ?_
  rw [show v_addi (0x12aec : word) 4 = (0x12af0 : word) from by decide +kernel]
  have hg4 := mem_grows_trans _ _ _ hg3
    (wbytes_grows (word_to_le_bytes 8 (getr regs 18)) _ (AD regs 32))
  -- 0x12af0  sd s3, 104(sp)   -> sp - 40
  refine evt_step (mstep_mkst (step_sd_at rsegs _ (0x12af0 : word) _ _ _ 2 19 0x68
      (AD regs 40) (getr regs 19) F_12af0 (by decide) D_12af0
      (vaddi_at _ (SP regs - 144) 0x68 (SP regs - 40) hsp2 (by omega) (by omega)
        (by rw [show bv_signed (0x68 : BitVec 12) = (104 : Int) from by decide]; omega))
      (getr_other regs 2 _ 19 (by decide))
      (store_ok_stk rsegs m _ lo (SP regs) (SP regs - 40) 8 hstk hg4
        (by omega) (by omega) (by omega) (by omega) (by omega)))) ?_
  rw [show v_addi (0x12af0 : word) 4 = (0x12af4 : word) from by decide +kernel]
  have hg5 := mem_grows_trans _ _ _ hg4
    (wbytes_grows (word_to_le_bytes 8 (getr regs 19)) _ (AD regs 40))
  -- 0x12af4  sd s4, 96(sp)   -> sp - 48
  refine evt_step (mstep_mkst (step_sd_at rsegs _ (0x12af4 : word) _ _ _ 2 20 0x60
      (AD regs 48) (getr regs 20) F_12af4 (by decide) D_12af4
      (vaddi_at _ (SP regs - 144) 0x60 (SP regs - 48) hsp2 (by omega) (by omega)
        (by rw [show bv_signed (0x60 : BitVec 12) = (96 : Int) from by decide]; omega))
      (getr_other regs 2 _ 20 (by decide))
      (store_ok_stk rsegs m _ lo (SP regs) (SP regs - 48) 8 hstk hg5
        (by omega) (by omega) (by omega) (by omega) (by omega)))) ?_
  rw [show v_addi (0x12af4 : word) 4 = (0x12af8 : word) from by decide +kernel]
  have hg6 := mem_grows_trans _ _ _ hg5
    (wbytes_grows (word_to_le_bytes 8 (getr regs 20)) _ (AD regs 48))
  -- 0x12af8  sd s5, 88(sp)   -> sp - 56
  refine evt_step (mstep_mkst (step_sd_at rsegs _ (0x12af8 : word) _ _ _ 2 21 0x58
      (AD regs 56) (getr regs 21) F_12af8 (by decide) D_12af8
      (vaddi_at _ (SP regs - 144) 0x58 (SP regs - 56) hsp2 (by omega) (by omega)
        (by rw [show bv_signed (0x58 : BitVec 12) = (88 : Int) from by decide]; omega))
      (getr_other regs 2 _ 21 (by decide))
      (store_ok_stk rsegs m _ lo (SP regs) (SP regs - 56) 8 hstk hg6
        (by omega) (by omega) (by omega) (by omega) (by omega)))) ?_
  rw [show v_addi (0x12af8 : word) 4 = (0x12afc : word) from by decide +kernel]
  have hg7 := mem_grows_trans _ _ _ hg6
    (wbytes_grows (word_to_le_bytes 8 (getr regs 21)) _ (AD regs 56))
  -- 0x12afc  sd s6, 80(sp)   -> sp - 64
  refine evt_step (mstep_mkst (step_sd_at rsegs _ (0x12afc : word) _ _ _ 2 22 0x50
      (AD regs 64) (getr regs 22) F_12afc (by decide) D_12afc
      (vaddi_at _ (SP regs - 144) 0x50 (SP regs - 64) hsp2 (by omega) (by omega)
        (by rw [show bv_signed (0x50 : BitVec 12) = (80 : Int) from by decide]; omega))
      (getr_other regs 2 _ 22 (by decide))
      (store_ok_stk rsegs m _ lo (SP regs) (SP regs - 64) 8 hstk hg7
        (by omega) (by omega) (by omega) (by omega) (by omega)))) ?_
  rw [show v_addi (0x12afc : word) 4 = (0x12b00 : word) from by decide +kernel]
  have hg8 := mem_grows_trans _ _ _ hg7
    (wbytes_grows (word_to_le_bytes 8 (getr regs 22)) _ (AD regs 64))
  -- 0x12b00  sd s7, 72(sp)   -> sp - 72
  refine evt_step (mstep_mkst (step_sd_at rsegs _ (0x12b00 : word) _ _ _ 2 23 0x48
      (AD regs 72) (getr regs 23) F_12b00 (by decide) D_12b00
      (vaddi_at _ (SP regs - 144) 0x48 (SP regs - 72) hsp2 (by omega) (by omega)
        (by rw [show bv_signed (0x48 : BitVec 12) = (72 : Int) from by decide]; omega))
      (getr_other regs 2 _ 23 (by decide))
      (store_ok_stk rsegs m _ lo (SP regs) (SP regs - 72) 8 hstk hg8
        (by omega) (by omega) (by omega) (by omega) (by omega)))) ?_
  rw [show v_addi (0x12b00 : word) 4 = (0x12b04 : word) from by decide +kernel]
  have hg9 := mem_grows_trans _ _ _ hg8
    (wbytes_grows (word_to_le_bytes 8 (getr regs 23)) _ (AD regs 72))
  -- 0x12b04  sd s8, 64(sp)   -> sp - 80
  refine evt_step (mstep_mkst (step_sd_at rsegs _ (0x12b04 : word) _ _ _ 2 24 0x40
      (AD regs 80) (getr regs 24) F_12b04 (by decide) D_12b04
      (vaddi_at _ (SP regs - 144) 0x40 (SP regs - 80) hsp2 (by omega) (by omega)
        (by rw [show bv_signed (0x40 : BitVec 12) = (64 : Int) from by decide]; omega))
      (getr_other regs 2 _ 24 (by decide))
      (store_ok_stk rsegs m _ lo (SP regs) (SP regs - 80) 8 hstk hg9
        (by omega) (by omega) (by omega) (by omega) (by omega)))) ?_
  rw [show v_addi (0x12b04 : word) 4 = (0x12b08 : word) from by decide +kernel]
  have hg10 := mem_grows_trans _ _ _ hg9
    (wbytes_grows (word_to_le_bytes 8 (getr regs 24)) _ (AD regs 80))
  -- 0x12b08  sd s9, 56(sp)   -> sp - 88
  refine evt_step (mstep_mkst (step_sd_at rsegs _ (0x12b08 : word) _ _ _ 2 25 0x38
      (AD regs 88) (getr regs 25) F_12b08 (by decide) D_12b08
      (vaddi_at _ (SP regs - 144) 0x38 (SP regs - 88) hsp2 (by omega) (by omega)
        (by rw [show bv_signed (0x38 : BitVec 12) = (56 : Int) from by decide]; omega))
      (getr_other regs 2 _ 25 (by decide))
      (store_ok_stk rsegs m _ lo (SP regs) (SP regs - 88) 8 hstk hg10
        (by omega) (by omega) (by omega) (by omega) (by omega)))) ?_
  rw [show v_addi (0x12b08 : word) 4 = (0x12b0c : word) from by decide +kernel]
  have hg11 := mem_grows_trans _ _ _ hg10
    (wbytes_grows (word_to_le_bytes 8 (getr regs 25)) _ (AD regs 88))
  -- 0x12b0c  sd s10, 48(sp)   -> sp - 96
  refine evt_step (mstep_mkst (step_sd_at rsegs _ (0x12b0c : word) _ _ _ 2 26 0x30
      (AD regs 96) (getr regs 26) F_12b0c (by decide) D_12b0c
      (vaddi_at _ (SP regs - 144) 0x30 (SP regs - 96) hsp2 (by omega) (by omega)
        (by rw [show bv_signed (0x30 : BitVec 12) = (48 : Int) from by decide]; omega))
      (getr_other regs 2 _ 26 (by decide))
      (store_ok_stk rsegs m _ lo (SP regs) (SP regs - 96) 8 hstk hg11
        (by omega) (by omega) (by omega) (by omega) (by omega)))) ?_
  rw [show v_addi (0x12b0c : word) 4 = (0x12b10 : word) from by decide +kernel]
  have hg12 := mem_grows_trans _ _ _ hg11
    (wbytes_grows (word_to_le_bytes 8 (getr regs 26)) _ (AD regs 96))
  -- 0x12b10  sd s11, 40(sp)   -> sp - 104
  refine evt_step (mstep_mkst (step_sd_at rsegs _ (0x12b10 : word) _ _ _ 2 27 0x28
      (AD regs 104) (getr regs 27) F_12b10 (by decide) D_12b10
      (vaddi_at _ (SP regs - 144) 0x28 (SP regs - 104) hsp2 (by omega) (by omega)
        (by rw [show bv_signed (0x28 : BitVec 12) = (40 : Int) from by decide]; omega))
      (getr_other regs 2 _ 27 (by decide))
      (store_ok_stk rsegs m _ lo (SP regs) (SP regs - 104) 8 hstk hg12
        (by omega) (by omega) (by omega) (by omega) (by omega)))) ?_
  rw [show v_addi (0x12b10 : word) 4 = (0x12b14 : word) from by decide +kernel]
  have hg13 := mem_grows_trans _ _ _ hg12
    (wbytes_grows (word_to_le_bytes 8 (getr regs 27)) _ (AD regs 104))
  -- 0x12b14  srl a2, a1, 26
  refine evt_step (mstep_mkst (step_srli_at rsegs _ (0x12b14 : word) _ _ _ 12 11 26
      (v_srli (getr regs 11) 26) F_12b14 (by decide) D_12b14 (by decide)
      (by rw [getr_other regs 2 _ 11 (by decide),
           show bv_unsigned (26 : BitVec 6) = (26 : Int) from by decide]))) ?_
  rw [show v_addi (0x12b14 : word) 4 = (0x12b18 : word) from by decide +kernel]
  -- 0x12b18  bne a2, x0, +500   -> 0x12d0c, the function's exit
  refine evt_step (mstep_mkst (step_bne_tk rsegs _ (0x12b18 : word) _ _ _ 12 0 0x1f4
      F_12b18 (by decide) D_12b18
      (by rw [getr_same _ 12 _ (by decide), getr_zero]; exact hbig))) ?_
  rw [show btgt (0x12b18 : word) (bv_signed (0x1f4 : BitVec 13)) = (0x12d0c : word)
        from by decide +kernel]
  exact knock_exit_big regs _ m lo hmi hstk hstack
    ((getr_other _ 12 (v_srli (getr regs 11) 26) 2 (by decide)).trans hsp2)
    (by simp +decide only [getr_other])
    (by simp +decide only [getr_other])

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.LLVMFuzzerTestOneInput
