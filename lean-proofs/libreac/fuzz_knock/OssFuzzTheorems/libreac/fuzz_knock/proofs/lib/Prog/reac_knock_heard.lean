-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard.v
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_heard_c
import OssFuzzTheorems.libreac.fuzz_knock.Image.PlainCode
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Riscv.DecodeC
import LinuxProcessSemantics.Common.SymBranch

/-! `lib/Prog/reac_knock_heard.v`: the walk of `reac_knock_heard`.

The Rocq proof is fifteen lines (`lib/Prog/reac_knock_heard.v:14-28`), each of
which drives the library tactics `step` (`lib/Lib/Step.v:722-726`), `if_cases`
(`lib/Lib/Step.v:773-777`) and `finish` (`lib/Lib/Tac.v:336-346`). The Lean
model carries no twin of those tactics, so the walk
below names the step lemma of each instruction.

Every instruction fetch and decode is a GENERATED theorem of
`OssFuzzTheorems.libreac.fuzz_knock.Image.PlainCode`, over the whole
four-segment image: `decide +kernel` on a fetch through that image does not
finish (OSSV-265 gaps row T-13). The executable segment of this image is
read-only, so the generated facts are over `fetch_word`, not `fetch_word_wx`.

What this file adds beyond the Rocq proof, and why, is in the docstring of
`reac_knock_heard_contract` (`lib/Prog/reac_knock_heard_c.lean`). -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_heard

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.SymBranch
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem (wa wr_at sx32)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Cells (cells_size)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec (evt evt_done evt_step mstep_mkst)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState (ret_pc)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame (munch wmono)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_heard_c

/-! ## The image's own words

`Image.PlainCode` states its facts over `Image.Plain.loaded_segments`;
`Img0.rsegs` is that list (`Img0.rsegs_eq`). -/

private theorem F0 : fetch_word Img0.rsegs (0x12d9c : word) = some 0x00052603#32 := by
  rw [Img0.rsegs_eq]; exact Image.PlainCode.F_12d9c

private theorem F1 : fetch_word Img0.rsegs (0x12da0 : word) = some 0x00b53c23#32 := by
  rw [Img0.rsegs_eq]; exact Image.PlainCode.F_12da0

private theorem F2 : fetch_word Img0.rsegs (0x12da4 : word) = some 0x00060463#32 := by
  rw [Img0.rsegs_eq]; exact Image.PlainCode.F_12da4

private theorem F3 : fetch_word Img0.rsegs (0x12da8 : word) = some 0x00008067#32 := by
  rw [Img0.rsegs_eq]; exact Image.PlainCode.F_12da8

private theorem F4 : fetch_word Img0.rsegs (0x12dac : word) = some 0x00200593#32 := by
  rw [Img0.rsegs_eq]; exact Image.PlainCode.F_12dac

private theorem F5 : fetch_word Img0.rsegs (0x12db0 : word) = some 0x00b52023#32 := by
  rw [Img0.rsegs_eq]; exact Image.PlainCode.F_12db0

private theorem F6 : fetch_word Img0.rsegs (0x12db4 : word) = some 0x00008067#32 := by
  rw [Img0.rsegs_eq]; exact Image.PlainCode.F_12db4

private theorem E0 : is_ecall 0x00052603#32 = false := by decide
private theorem E1 : is_ecall 0x00b53c23#32 = false := by decide
private theorem E2 : is_ecall 0x00060463#32 = false := by decide
private theorem E3 : is_ecall 0x00008067#32 = false := by decide
private theorem E4 : is_ecall 0x00200593#32 = false := by decide
private theorem E5 : is_ecall 0x00b52023#32 = false := by decide

/-! ## A branch step

The Lean proof library has no `Branch` step lemma: `SymExec.sym_step` has no
`Branch` arm (`linux-process-semantics@ff0313ba4f:lean/LinuxProcessSemantics/Common/SymExec.lean:42-45`),
and a branch is only reachable through `sym_exec`'s direction script. These
three are the twin of what the Rocq library's `if_cases` tactic drives
(`lib/Lib/Tac.v`); they were written for OSSV-265 slice T (gaps row T-7). -/

private theorem step_branch (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (c : branch_cond) (rs1 rs2 : reg)
    (imm : BitVec 13)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (instr.Branch c rs1 rs2 imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs
        (if branch_taken c (getr regs rs1) (getr regs rs2)
         then v_addi pc (bv_signed imm) else v_addi pc 4) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (with_pc (if branch_taken c (rget (core.Core regs bvmap_empty pc 0 none) rs1)
      (rget (core.Core regs bvmap_empty pc 0 none) rs2)
      then pc + sext 64 imm else pc + 4) (core.Core regs bvmap_empty pc 0 none), mem) = _
  rw [rget_mk, rget_mk, b_addsext, npc4]
  cases branch_taken c (getr regs rs1) (getr regs rs2) <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> rfl

private theorem step_branch_taken (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (c : branch_cond) (rs1 rs2 : reg)
    (imm : BitVec 13)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (instr.Branch c rs1 rs2 imm, 4))
    (hbt : branch_taken c (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc (bv_signed imm)) mem rom) := by
  rw [step_branch segs regs pc mem rom w c rs1 rs2 imm hf he hd, hbt]
  rfl

private theorem step_branch_not (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (c : branch_cond) (rs1 rs2 : reg)
    (imm : BitVec 13)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (instr.Branch c rs1 rs2 imm, 4))
    (hbt : branch_taken c (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  rw [step_branch segs regs pc mem rom w c rs1 rs2 imm hf he hd, hbt]
  simp only [Bool.false_eq_true, ↓reduceIte]

/-! ## From `wr_at` to the model's store bound

`lib/Lib/Step.v:70-76` does this with `rw_cells_store_ok`; here it is
`StoreOk.store_ok_of_all`. -/

private theorem store_ok_of_wr_at (segs : List Segment) (m : word → Option byte)
    (A N : Int) (hwr : wr_at segs m A N) (off : Int) (n : Nat)
    (hn : 0 < n) (h1 : 0 ≤ off) (h2 : off + (n : Int) ≤ N) :
    store_ok segs m (wa (A + off)) n = true := by
  obtain ⟨hA0, hAN, hall⟩ := hwr
  have hu : bv_unsigned (wa (A + off)) = A + off := by
    unfold wa
    rw [Z_to_bv_unsigned]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  apply store_ok_of_all segs n m _ (by rw [hu]; omega)
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [hu] at hx1 hx2
  have hx' := hall (bv_unsigned x - A) (by omega) (by omega)
  unfold wa at hx'
  rw [show A + (bv_unsigned x - A) = bv_unsigned x by omega, Z_to_bv_bv_unsigned64] at hx'
  exact hx'

/-! ## The frame -/

/-- One written range leaves every byte outside `[A, A+40)` as it was
(`lib/Lib/Frame.v:71-72`). -/
private theorem munch_one (A off : Int) (n : Nat) (m : word → Option byte) (bs : List byte)
    (hbs : bs.length = n) (hn : 0 < n) (h0 : 0 ≤ A) (hoff : 0 ≤ off)
    (hle : off + (n : Int) ≤ 40) (h64 : A + 40 ≤ 2 ^ 64)
    (x : word) (hx : bv_unsigned x < A ∨ A + 40 ≤ bv_unsigned x) :
    wbytes m (wa (A + off)) bs x = m x := by
  have hu : bv_unsigned (wa (A + off)) = A + off := by
    unfold wa
    rw [Z_to_bv_unsigned]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rcases hx with h | h
  · exact wbytes_below bs m _ x (by rw [hu, hbs]; omega) (by rw [hu]; omega)
  · exact wbytes_above bs m _ x (by rw [hu, hbs]; omega)

/-- `lib/Lib/MState.v:140` against the model's own `jalr` target: the two
spellings of a return address agree (OSSV-265 gaps row T-9). -/
private theorem v_jalr_ret_pc (a : word) : v_jalr a (bv_signed (0 : BitVec 12)) = ret_pc a := by
  have hs : sext 64 (0 : BitVec 12) = 0#64 := by decide
  have h := b_jalr a 0
  rw [hs, BitVec.add_zero] at h
  exact h.symm

/-! ## The sign-extended load against the stored integer

`knock_sx32_unsigned` (`lib/Prog/reac_knock_struct.v:12-28`) and
`knock_sx32_eqb` (`lib/Prog/reac_knock_struct.v:30-36`) rest on stdpp's
`bv_swrap` lemma set, which the
Lean port does not carry (OSSV-265 gaps row T-12); they follow from Lean's
own `Int` arithmetic. They are `private` here, as they are in the sibling
`reac_knock_step.lean:63` and `:77`, because
`…Prog.reac_knock_struct`, where their Rocq twins live, is another agent's
file. -/

private theorem knock_sx32_unsigned (s : Int) (h0 : 0 ≤ s) (h1 : s < 2 ^ 32) :
    bv_unsigned (sx32 (Z_to_bv 64 s)) =
      if s < 2 ^ 31 then s else s + (2 ^ 64 - 2 ^ 32) := by
  have p31 : (2 : Int) ^ 31 = 2147483648 := by decide
  have p32 : (2 : Int) ^ 32 = 4294967296 := by decide
  have p64 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  unfold sx32
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap64_mod, bv_wrap64_mod]
  unfold bv_swrap bv_wrap bv_half_modulus bv_modulus
  rw [p31, p32, p64] at *
  split <;> omega

private theorem sx32_v_lw (v : word) : sx32 v = v_lw v := rfl

private theorem knock_sx32_eqb (s c : Int) (h0 : 0 ≤ s) (h1 : s < 2 ^ 32)
    (hc0 : 0 ≤ c) (hc1 : c < 2 ^ 31) :
    bv_eqb (sx32 (Z_to_bv 64 s)) (Z_to_bv 64 c) = decide (s = c) := by
  have hu := knock_sx32_unsigned s h0 h1
  have p31 : (2 : Int) ^ 31 = 2147483648 := by decide
  have p32 : (2 : Int) ^ 32 = 4294967296 := by decide
  have p64 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  rw [bv_eqb_Z, hu, Z_to_bv_unsigned, bv_wrap64_mod]
  rw [p31, p32, p64] at *
  rw [Int.emod_eq_of_lt hc0 (by omega)]
  split <;> exact decide_eq_decide.2 (by omega)

/-- The `beq a2, x0` of `0x12da4` against Rocq's `Z.eqb st 0`
(`lib/Prog/reac_knock_heard_c.v:25`). -/
private theorem branch_eq_decide (s : Int) (h0 : 0 ≤ s) (h1 : s < 2 ^ 32) :
    branch_taken .BC_EQ (v_lw (Z_to_bv 64 s)) (Z_to_bv 64 0) = decide (s = 0) := by
  show bv_eqb (v_lw (Z_to_bv 64 s)) (Z_to_bv 64 0) = _
  rw [← sx32_v_lw]
  exact knock_sx32_eqb s 0 h0 h1 (by decide) (by decide)

/-! ## The walk -/

private theorem heard_mem_true (regs : bvmap 5 word) (mem : word → Option byte) (st : Int)
    (h : st = 0) :
    heard_mem regs mem st =
      wbytes (wbytes mem (v_addi (getr regs 10) 24) (word_to_le_bytes 8 (getr regs 11)))
        (v_addi (getr regs 10) 0) (word_to_le_bytes 4 (Z_to_bv 64 2)) := by
  simp only [heard_mem, h, ↓reduceIte]

private theorem heard_mem_false (regs : bvmap 5 word) (mem : word → Option byte) (st : Int)
    (h : ¬ st = 0) :
    heard_mem regs mem st =
      wbytes mem (v_addi (getr regs 10) 24) (word_to_le_bytes 8 (getr regs 11)) := by
  simp only [heard_mem, h, ↓reduceIte]

/-- `lib/Prog/reac_knock_heard.v:12-29`. -/
theorem reac_knock_heard_holds : reac_knock_heard_contract := by
  intro regs mem st p1 opened due heard g p2 bs hst0 hst1 _hg _hg' hrw hread hbsst
  -- the loaded word: the stored integer, sign-extended by the `lw`
  obtain ⟨v, hvdef⟩ : ∃ v : word, v = Z_to_bv 64 st := ⟨_, rfl⟩
  have hvu : bv_unsigned v = st := by
    rw [hvdef, Z_to_bv_unsigned]
    exact Int.emod_eq_of_lt hst0 (by omega)
  have hbs : bytes_le_to_Z bs = bv_unsigned v := by rw [hvu]; exact hbsst
  have hbe : branch_taken branch_cond.BC_EQ (v_lw v) (Z_to_bv 64 0) = decide (st = 0) := by
    rw [hvdef]; exact branch_eq_decide st hst0 hst1
  obtain ⟨-, hwr⟩ := hrw
  have hsz : cells_size (reac_knock_struct.knock_cells st p1 opened due heard g p2) = 40 := rfl
  rw [hsz] at hwr
  obtain ⟨hA0, hA40, -⟩ := id hwr
  have hz12 : bv_signed (0 : BitVec 12) = 0 := by decide
  have h24 : bv_signed (0x18 : BitVec 12) = 24 := by decide
  -- the store bounds the Rocq proof reads off `rw_cells`
  have hok24 : store_ok Img0.rsegs mem (v_addi (getr regs 10) 24) 8 = true :=
    store_ok_of_wr_at Img0.rsegs mem _ 40 hwr 24 8 (by omega) (by omega) (by omega)
  have hok0m : store_ok Img0.rsegs mem (v_addi (getr regs 10) 0) 4 = true :=
    store_ok_of_wr_at Img0.rsegs mem _ 40 hwr 0 4 (by omega) (by omega) (by omega)
  have hok0 : store_ok Img0.rsegs
      (wbytes mem (v_addi (getr regs 10) 24) (word_to_le_bytes 8 (getr regs 11)))
      (v_addi (getr regs 10) 0) 4 = true :=
    store_ok_mono Img0.rsegs 4 mem _ _ (wbytes_grows _ mem _) hok0m
  -- the frame, for both exits
  have hmu1 : ∀ x : word, bv_unsigned x < bv_unsigned (getr regs 10) ∨
      bv_unsigned (getr regs 10) + 40 ≤ bv_unsigned x →
      wbytes mem (v_addi (getr regs 10) 24) (word_to_le_bytes 8 (getr regs 11)) x = mem x := by
    intro x hx
    exact munch_one (bv_unsigned (getr regs 10)) 24 8 mem _
      (length_N_to_le_bytes 8 _) (by omega) hA0 (by omega) (by omega) (by omega) x hx
  have hmu0 : ∀ (m : word → Option byte) (x : word),
      bv_unsigned x < bv_unsigned (getr regs 10) ∨
      bv_unsigned (getr regs 10) + 40 ≤ bv_unsigned x →
      wbytes m (v_addi (getr regs 10) 0) (word_to_le_bytes 4 (Z_to_bv 64 2)) x = m x := by
    intro m x hx
    exact munch_one (bv_unsigned (getr regs 10)) 0 4 m _
      (length_N_to_le_bytes 4 _) (by omega) hA0 (by omega) (by omega) (by omega) x hx
  -- 0x12d9c  lw a2, 0(a0)
  have hpc : Z_to_bv 64 REAC_KNOCK_HEARD = (0x12d9c : word) := by decide +kernel
  rw [hpc]
  refine evt_step (mstep_mkst (LinuxProcessSemantics.Common.SymExec.step_lw Img0.rsegs regs
      (0x12d9c : word) mem (seg_rom Img0.rsegs) 0x00052603#32 12 10 0 bs v F0 E0
      Image.PlainCode.D_12d9c (by rw [hz12]; exact hread) hbs)) ?_
  have hrd12 : bv_eqb (12 : reg) 0 = false := by decide
  have hpc0 : v_addi (0x12d9c : word) 4 = (0x12da0 : word) := by decide +kernel
  rw [hrd12, hpc0]
  have g10 : getr (regupd regs 12 (v_lw v)) 10 = getr regs 10 :=
    getr_other regs 12 _ 10 (by decide)
  have g11 : getr (regupd regs 12 (v_lw v)) 11 = getr regs 11 :=
    getr_other regs 12 _ 11 (by decide)
  have g12 : getr (regupd regs 12 (v_lw v)) 12 = v_lw v :=
    getr_same regs 12 _ (by decide)
  have g1 : getr (regupd regs 12 (v_lw v)) 1 = getr regs 1 :=
    getr_other regs 12 _ 1 (by decide)
  -- 0x12da0  sd a1, 24(a0)
  refine evt_step (mstep_mkst (step_sd_at Img0.rsegs (regupd regs 12 (v_lw v))
      (0x12da0 : word) mem (seg_rom Img0.rsegs) 0x00b53c23#32 10 11 0x18
      (v_addi (getr regs 10) 24) (getr regs 11) F1 E1 Image.PlainCode.D_12da0
      (by rw [g10, h24]) g11 hok24)) ?_
  have hpc1 : v_addi (0x12da0 : word) 4 = (0x12da4 : word) := by decide +kernel
  rw [hpc1]
  cases hbt : branch_taken branch_cond.BC_EQ (v_lw v) (Z_to_bv 64 0) with
  | true =>
    -- taken: the stored state is zero, Rocq's `Z.eqb st 0`; 0x12dac
    have hz : st = 0 := of_decide_eq_true (by rw [← hbe]; exact hbt)
    have hbt' : branch_taken branch_cond.BC_EQ
        (getr (regupd regs 12 (v_lw v)) 12) (getr (regupd regs 12 (v_lw v)) 0) = true := by
      rw [g12, getr_zero]; exact hbt
    refine evt_step (mstep_mkst (step_branch_taken Img0.rsegs (regupd regs 12 (v_lw v))
        (0x12da4 : word)
        (wbytes mem (v_addi (getr regs 10) 24) (word_to_le_bytes 8 (getr regs 11)))
        (seg_rom Img0.rsegs) 0x00060463#32 .BC_EQ 12 0 0x8 F2 E2
        Image.PlainCode.D_12da4 hbt')) ?_
    have hpc2 : v_addi (0x12da4 : word) (bv_signed (0x8 : BitVec 13)) = (0x12dac : word) := by
      decide +kernel
    rw [hpc2]
    -- 0x12dac  addi a1, x0, 2
    refine evt_step (mstep_mkst (step_addi_at Img0.rsegs (regupd regs 12 (v_lw v))
        (0x12dac : word)
        (wbytes mem (v_addi (getr regs 10) 24) (word_to_le_bytes 8 (getr regs 11)))
        (seg_rom Img0.rsegs) 0x00200593#32 11 0 0x2 (Z_to_bv 64 2) F4 E4
        Image.PlainCode.D_12dac (by decide) (by rw [getr_zero]; decide +kernel))) ?_
    have hpc3 : v_addi (0x12dac : word) 4 = (0x12db0 : word) := by decide +kernel
    rw [hpc3]
    have h10 : getr (regupd (regupd regs 12 (v_lw v)) 11 (Z_to_bv 64 2)) 10
        = getr regs 10 := by
      rw [getr_other (regupd regs 12 (v_lw v)) 11 _ 10 (by decide), g10]
    have h11 : getr (regupd (regupd regs 12 (v_lw v)) 11 (Z_to_bv 64 2)) 11
        = Z_to_bv 64 2 := getr_same (regupd regs 12 (v_lw v)) 11 _ (by decide)
    have h1 : getr (regupd (regupd regs 12 (v_lw v)) 11 (Z_to_bv 64 2)) 1
        = getr regs 1 := by
      rw [getr_other (regupd regs 12 (v_lw v)) 11 _ 1 (by decide), g1]
    -- 0x12db0  sw a1, 0(a0)
    refine evt_step (mstep_mkst (LinuxProcessSemantics.Common.SymExec.step_sw_val Img0.rsegs
        (regupd (regupd regs 12 (v_lw v)) 11 (Z_to_bv 64 2)) (0x12db0 : word)
        (wbytes mem (v_addi (getr regs 10) 24) (word_to_le_bytes 8 (getr regs 11)))
        (seg_rom Img0.rsegs) 0x00b52023#32 10 11 0 F5 E5 Image.PlainCode.D_12db0
        (by rw [hz12, h10]; exact hok0))) ?_
    have hpc4 : v_addi (0x12db0 : word) 4 = (0x12db4 : word) := by decide +kernel
    rw [hpc4, hz12, h10, h11]
    -- 0x12db4  jalr x0, 0(ra)
    refine evt_step (mstep_mkst (step_jalr_x0 Img0.rsegs
        (regupd (regupd regs 12 (v_lw v)) 11 (Z_to_bv 64 2)) (0x12db4 : word)
        (wbytes (wbytes mem (v_addi (getr regs 10) 24) (word_to_le_bytes 8 (getr regs 11)))
          (v_addi (getr regs 10) 0) (word_to_le_bytes 4 (Z_to_bv 64 2)))
        (seg_rom Img0.rsegs) 0x00008067#32 1 0 (getr regs 1) F6 E3
        Image.PlainCode.D_12db4 h1)) ?_
    refine evt_done ⟨regupd (regupd regs 12 (v_lw v)) 11 (Z_to_bv 64 2),
      wbytes (wbytes mem (v_addi (getr regs 10) 24) (word_to_le_bytes 8 (getr regs 11)))
        (v_addi (getr regs 10) 0) (word_to_le_bytes 4 (Z_to_bv 64 2)), ?_, ?_, ?_, ?_, ?_⟩
    · rw [v_jalr_ret_pc]
    · intro r hr11 hr12
      rw [getr_other (regupd regs 12 (v_lw v)) 11 _ r hr11,
        getr_other regs 12 _ r hr12]
    · intro x hx
      obtain ⟨hout, -⟩ := hx
      rw [hmu0 _ x hout, hmu1 x hout]
    · exact fun x hx => wview_grows Img0.rsegs mem _ x
        (mem_grows_trans mem _ _ (wbytes_grows _ mem _) (wbytes_grows _ _ _)) hx
    · exact (heard_mem_true regs mem st hz).symm
  | false =>
    -- not taken: the stored state is not zero; 0x12da8, return
    have hz : ¬ st = 0 := of_decide_eq_false (by rw [← hbe]; exact hbt)
    have hbt' : branch_taken branch_cond.BC_EQ
        (getr (regupd regs 12 (v_lw v)) 12) (getr (regupd regs 12 (v_lw v)) 0) = false := by
      rw [g12, getr_zero]; exact hbt
    refine evt_step (mstep_mkst (step_branch_not Img0.rsegs (regupd regs 12 (v_lw v))
        (0x12da4 : word)
        (wbytes mem (v_addi (getr regs 10) 24) (word_to_le_bytes 8 (getr regs 11)))
        (seg_rom Img0.rsegs) 0x00060463#32 .BC_EQ 12 0 0x8 F2 E2
        Image.PlainCode.D_12da4 hbt')) ?_
    have hpc2 : v_addi (0x12da4 : word) 4 = (0x12da8 : word) := by decide +kernel
    rw [hpc2]
    refine evt_step (mstep_mkst (step_jalr_x0 Img0.rsegs (regupd regs 12 (v_lw v))
        (0x12da8 : word)
        (wbytes mem (v_addi (getr regs 10) 24) (word_to_le_bytes 8 (getr regs 11)))
        (seg_rom Img0.rsegs) 0x00008067#32 1 0 (getr regs 1) F3 E3
        Image.PlainCode.D_12da8 g1)) ?_
    refine evt_done ⟨regupd regs 12 (v_lw v),
      wbytes mem (v_addi (getr regs 10) 24) (word_to_le_bytes 8 (getr regs 11)),
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [v_jalr_ret_pc]
    · intro r _ hr12
      exact getr_other regs 12 _ r hr12
    · intro x hx
      obtain ⟨hout, -⟩ := hx
      exact hmu1 x hout
    · exact fun x hx => wview_grows Img0.rsegs mem _ x (wbytes_grows _ mem _) hx
    · exact (heard_mem_false regs mem st hz).symm

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_heard
