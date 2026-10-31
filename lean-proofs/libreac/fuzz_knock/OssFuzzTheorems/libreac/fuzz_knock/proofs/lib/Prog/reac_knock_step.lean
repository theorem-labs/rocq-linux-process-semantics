-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_step.v
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_step_c
import OssFuzzTheorems.libreac.fuzz_knock.Image.PlainCode
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.SymExec
import LinuxProcessSemantics.Common.SymBranch
import LinuxProcessSemantics.Common.StoreOk

/-! `lib/Prog/reac_knock_step.v`: the walk of `reac_knock_step`.

The Rocq proof is 70 lines of `step`/`if_cases`/`finish` over the Rocq
library's symbolic executor. The Lean port takes each step by the model's own
per-instruction lemma, as OSSV-265 slice T's probe did; the fetch and decode
facts are the generated `Image.PlainCode.F_*` and `D_*`, over the whole image.

What the Rocq script's tactics become here:

* `step` — `refine evt_step (mstep_mkst (step_<instr> …)) ?_` and a rewrite of
  the next pc;
* `if_cases H` — `by_cases` on the branch's arithmetic condition, then
  `step_branch_taken`/`step_branch_not`, which the Lean library does not carry
  (`SymExec.sym_step` has no `Branch` arm);
* `zify_cond` and `lia` — `SymBranch.bv_ltu_Z` and `omega`;
* `finish; close_step` — `evt_done` and the `ite_eq_left`/`ite_eq_right`
  reductions of `knock_step_f` and `knock_step_mem`. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_step

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Common.SymBranch
open LinuxProcessSemantics.Common.StoreOk
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem (le4 le8 sx32)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame
  (munch wmono outside munch_refl wmono_refl)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState (ret_pc)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec
  (evt evt_done evt_step mstep_mkst)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem (wa wr_at)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Cells (cells_size)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_struct
  (L_NS knock_cells)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_step_c

set_option maxHeartbeats 1000000

/-! ## The two lemmas of `lib/Prog/reac_knock_struct.v`

`knock_sx32_unsigned` (`lib/Prog/reac_knock_struct.v:12-28`) and
`knock_sx32_eqb` (`:30-36`) rest on stdpp's `bv_swrap` lemma set, which the
Lean port does not carry (OSSV-265 gaps row T-12); they are proved here from
Lean's own `Int` arithmetic. They are `private` only because
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

/-! ## A branch step

The Lean proof library has no `Branch` step lemma: `SymExec.sym_step` has no
`Branch` arm, and a branch is only reachable through `sym_exec`'s direction
script. These three are the twin of the Rocq library's `if_cases`, and are
copied from OSSV-265 slice T's probe (`probe/ossv265-t/Probe/Heard.lean` of
theorem-labs/oss-verify-proofs-internal, branch `mcsl/lean-convert-probe`
`4054974252`), which first wrote them. -/

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

/-! ## Small value and memory facts -/

private theorem not_decide_lt (a b : Int) : (!decide (a < b)) = decide (b ≤ a) := by
  by_cases h : a < b
  · rw [decide_eq_true h, decide_eq_false (by omega : ¬ b ≤ a)]
    rfl
  · rw [decide_eq_false h, decide_eq_true (by omega : b ≤ a)]
    rfl

private theorem v_addi_0 (x : word) : v_addi x 0 = x := by
  apply bv_eq_of_unsigned
  rw [v_addi, Z_to_bv_unsigned, bv_wrap64_mod, Int.add_zero]
  exact Int.emod_eq_of_lt (u64_range x).1 (u64_range x).2

/-- `lib/Lib/MState.v:140` meets `SeqExec.v_jalr` (OSSV-265 gaps row T-9). -/
private theorem ret_pc_jalr (ra : word) : ret_pc ra = v_jalr ra 0 := by
  have hs : sext 64 (0 : BitVec 12) = (0 : word) := by decide
  have hz : bv_signed (0 : BitVec 12) = 0 := by decide
  have ha : ra + (0 : word) = ra := BitVec.add_zero ra
  have hb := b_jalr ra 0
  rw [hs, ha, hz] at hb
  exact hb

private theorem le4_eq (v : word) : word_to_le_bytes 4 v = le4 v := rfl
private theorem le8_eq (v : word) : word_to_le_bytes 8 v = le8 v := rfl
private theorem len_le4 (v : word) : (le4 v).length = 4 := rfl
private theorem len_le8 (v : word) : (le8 v).length = 8 := rfl

private theorem u_addi (a : word) (k : Int) (h0 : 0 ≤ k)
    (h1 : bv_unsigned a + k < 2 ^ 64) :
    bv_unsigned (v_addi a k) = bv_unsigned a + k := by
  rw [v_addi, Z_to_bv_unsigned, bv_wrap64_mod]
  exact Int.emod_eq_of_lt (by have := (u64_range a).1; omega) h1

/-- From the `wr_at` half of Rocq's `rw_cells` to the model's store bound:
what `lib/Lib/Step.v:70-76` gives the Rocq proof for free. Over
`StoreOk.store_ok_of_all`; the same text as `reac_knock_heard.lean`'s, which
wrote it first in this slice. -/
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

/-- One of the function's stores leaves every byte outside the structure
alone: the per-store half of Rocq's `munch` conjunct
(`lib/Prog/reac_knock_step_c.v:31`). -/
private theorem munch_store (a0 : word) (k : Int) (n : Nat) (bs : List byte)
    (hbs : bs.length = n) (m : word → Option byte) (hk : 0 ≤ k) (hn : 0 < n)
    (hkn : k + n ≤ 40)
    (hnw : bv_unsigned a0 + 40 ≤ 2 ^ 64) (x : word)
    (hx : outside [(bv_unsigned a0, bv_unsigned a0 + 40)] (bv_unsigned x)) :
    wbytes m (v_addi a0 k) bs x = m x := by
  have hlen : (bs.length : Int) = (n : Int) := by rw [hbs]
  have hn' : (1 : Int) ≤ (n : Int) := by exact_mod_cast hn
  have hk64 : bv_unsigned a0 + k < 2 ^ 64 := by
    have := (u64_range a0).1
    omega
  have ha : bv_unsigned (v_addi a0 k) = bv_unsigned a0 + k := u_addi a0 k hk hk64
  cases hx.1 with
  | inl hlo => exact wbytes_below bs m _ x (by rw [ha, hlen]; omega) (by rw [ha]; omega)
  | inr hhi => exact wbytes_above bs m _ x (by rw [ha, hlen]; omega)

private theorem grows2 (m : word → Option byte) (a1 : word) (bs1 : List byte)
    (a2 : word) (bs2 : List byte) :
    mem_grows m (wbytes (wbytes m a1 bs1) a2 bs2) :=
  mem_grows_trans _ _ _ (wbytes_grows bs1 m a1) (wbytes_grows bs2 _ a2)

/-! ## The instruction words of `reac_knock_step`, through the whole image

Every one is the generated `Image.PlainCode.F_*`, restated at the `Z_to_bv 64`
spelling of the pc that the step lemmas produce. -/

private theorem f_12db8 : fetch_word Img0.rsegs (Z_to_bv 64 0x12db8) = some 0x00052603 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12db8 : Int) = (0x12db8 : word) from by decide +kernel]
  exact Image.PlainCode.F_12db8

private theorem f_12dbc : fetch_word Img0.rsegs (Z_to_bv 64 0x12dbc) = some 0x00200693 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12dbc : Int) = (0x12dbc : word) from by decide +kernel]
  exact Image.PlainCode.F_12dbc

private theorem f_12dc0 : fetch_word Img0.rsegs (Z_to_bv 64 0x12dc0) = some 0x00d60c63 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12dc0 : Int) = (0x12dc0 : word) from by decide +kernel]
  exact Image.PlainCode.F_12dc0

private theorem f_12dc4 : fetch_word Img0.rsegs (Z_to_bv 64 0x12dc4) = some 0x00061663 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12dc4 : Int) = (0x12dc4 : word) from by decide +kernel]
  exact Image.PlainCode.F_12dc4

private theorem f_12dc8 : fetch_word Img0.rsegs (Z_to_bv 64 0x12dc8) = some 0x01053683 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12dc8 : Int) = (0x12dc8 : word) from by decide +kernel]
  exact Image.PlainCode.F_12dc8

private theorem f_12dcc : fetch_word Img0.rsegs (Z_to_bv 64 0x12dcc) = some 0x02d5fc63 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12dcc : Int) = (0x12dcc : word) from by decide +kernel]
  exact Image.PlainCode.F_12dcc

private theorem f_12dd0 : fetch_word Img0.rsegs (Z_to_bv 64 0x12dd0) = some 0x00000613 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12dd0 : Int) = (0x12dd0 : word) from by decide +kernel]
  exact Image.PlainCode.F_12dd0

private theorem f_12dd4 : fetch_word Img0.rsegs (Z_to_bv 64 0x12dd4) = some 0x03c0006f := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12dd4 : Int) = (0x12dd4 : word) from by decide +kernel]
  exact Image.PlainCode.F_12dd4

private theorem f_12dd8 : fetch_word Img0.rsegs (Z_to_bv 64 0x12dd8) = some 0x01853683 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12dd8 : Int) = (0x12dd8 : word) from by decide +kernel]
  exact Image.PlainCode.F_12dd8

private theorem f_12ddc : fetch_word Img0.rsegs (Z_to_bv 64 0x12ddc) = some 0x00000613 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12ddc : Int) = (0x12ddc : word) from by decide +kernel]
  exact Image.PlainCode.F_12ddc

private theorem f_12de0 : fetch_word Img0.rsegs (Z_to_bv 64 0x12de0) = some 0x02b6f863 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12de0 : Int) = (0x12de0 : word) from by decide +kernel]
  exact Image.PlainCode.F_12de0

private theorem f_12de4 : fetch_word Img0.rsegs (Z_to_bv 64 0x12de4) = some 0x40d587b3 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12de4 : Int) = (0x12de4 : word) from by decide +kernel]
  exact Image.PlainCode.F_12de4

private theorem f_12de8 : fetch_word Img0.rsegs (Z_to_bv 64 0x12de8) = some 0x1dcd6737 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12de8 : Int) = (0x12de8 : word) from by decide +kernel]
  exact Image.PlainCode.F_12de8

private theorem f_12dec : fetch_word Img0.rsegs (Z_to_bv 64 0x12dec) = some 0x5007071b := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12dec : Int) = (0x12dec : word) from by decide +kernel]
  exact Image.PlainCode.F_12dec

private theorem f_12df0 : fetch_word Img0.rsegs (Z_to_bv 64 0x12df0) = some 0x02e7e063 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12df0 : Int) = (0x12df0 : word) from by decide +kernel]
  exact Image.PlainCode.F_12df0

private theorem f_12df4 : fetch_word Img0.rsegs (Z_to_bv 64 0x12df4) = some 0x00e686b3 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12df4 : Int) = (0x12df4 : word) from by decide +kernel]
  exact Image.PlainCode.F_12df4

private theorem f_12df8 : fetch_word Img0.rsegs (Z_to_bv 64 0x12df8) = some 0x00052023 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12df8 : Int) = (0x12df8 : word) from by decide +kernel]
  exact Image.PlainCode.F_12df8

private theorem f_12dfc : fetch_word Img0.rsegs (Z_to_bv 64 0x12dfc) = some 0x00d53823 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12dfc : Int) = (0x12dfc : word) from by decide +kernel]
  exact Image.PlainCode.F_12dfc

private theorem f_12e00 : fetch_word Img0.rsegs (Z_to_bv 64 0x12e00) = some 0xfcd5e8e3 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12e00 : Int) = (0x12e00 : word) from by decide +kernel]
  exact Image.PlainCode.F_12e00

private theorem f_12e04 : fetch_word Img0.rsegs (Z_to_bv 64 0x12e04) = some 0x00100613 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12e04 : Int) = (0x12e04 : word) from by decide +kernel]
  exact Image.PlainCode.F_12e04

private theorem f_12e08 : fetch_word Img0.rsegs (Z_to_bv 64 0x12e08) = some 0x00c52023 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12e08 : Int) = (0x12e08 : word) from by decide +kernel]
  exact Image.PlainCode.F_12e08

private theorem f_12e0c : fetch_word Img0.rsegs (Z_to_bv 64 0x12e0c) = some 0x02c52023 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12e0c : Int) = (0x12e0c : word) from by decide +kernel]
  exact Image.PlainCode.F_12e0c

private theorem f_12e10 : fetch_word Img0.rsegs (Z_to_bv 64 0x12e10) = some 0x00060513 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12e10 : Int) = (0x12e10 : word) from by decide +kernel]
  exact Image.PlainCode.F_12e10

private theorem f_12e14 : fetch_word Img0.rsegs (Z_to_bv 64 0x12e14) = some 0x00008067 := by
  rw [Img0.rsegs_eq, show Z_to_bv 64 (0x12e14 : Int) = (0x12e14 : word) from by decide +kernel]
  exact Image.PlainCode.F_12e14

/-! ## The next pc, at each instruction and each branch target -/

private theorem pc4_12db8 : v_addi (Z_to_bv 64 0x12db8) 4 = Z_to_bv 64 0x12dbc := by
  decide +kernel
private theorem pc4_12dbc : v_addi (Z_to_bv 64 0x12dbc) 4 = Z_to_bv 64 0x12dc0 := by
  decide +kernel
private theorem pc4_12dc0 : v_addi (Z_to_bv 64 0x12dc0) 4 = Z_to_bv 64 0x12dc4 := by
  decide +kernel
private theorem pc4_12dc4 : v_addi (Z_to_bv 64 0x12dc4) 4 = Z_to_bv 64 0x12dc8 := by
  decide +kernel
private theorem pc4_12dc8 : v_addi (Z_to_bv 64 0x12dc8) 4 = Z_to_bv 64 0x12dcc := by
  decide +kernel
private theorem pc4_12dcc : v_addi (Z_to_bv 64 0x12dcc) 4 = Z_to_bv 64 0x12dd0 := by
  decide +kernel
private theorem pc4_12dd0 : v_addi (Z_to_bv 64 0x12dd0) 4 = Z_to_bv 64 0x12dd4 := by
  decide +kernel
private theorem pc4_12dd8 : v_addi (Z_to_bv 64 0x12dd8) 4 = Z_to_bv 64 0x12ddc := by
  decide +kernel
private theorem pc4_12ddc : v_addi (Z_to_bv 64 0x12ddc) 4 = Z_to_bv 64 0x12de0 := by
  decide +kernel
private theorem pc4_12de0 : v_addi (Z_to_bv 64 0x12de0) 4 = Z_to_bv 64 0x12de4 := by
  decide +kernel
private theorem pc4_12de4 : v_addi (Z_to_bv 64 0x12de4) 4 = Z_to_bv 64 0x12de8 := by
  decide +kernel
private theorem pc4_12de8 : v_addi (Z_to_bv 64 0x12de8) 4 = Z_to_bv 64 0x12dec := by
  decide +kernel
private theorem pc4_12dec : v_addi (Z_to_bv 64 0x12dec) 4 = Z_to_bv 64 0x12df0 := by
  decide +kernel
private theorem pc4_12df0 : v_addi (Z_to_bv 64 0x12df0) 4 = Z_to_bv 64 0x12df4 := by
  decide +kernel
private theorem pc4_12df4 : v_addi (Z_to_bv 64 0x12df4) 4 = Z_to_bv 64 0x12df8 := by
  decide +kernel
private theorem pc4_12df8 : v_addi (Z_to_bv 64 0x12df8) 4 = Z_to_bv 64 0x12dfc := by
  decide +kernel
private theorem pc4_12dfc : v_addi (Z_to_bv 64 0x12dfc) 4 = Z_to_bv 64 0x12e00 := by
  decide +kernel
private theorem pc4_12e00 : v_addi (Z_to_bv 64 0x12e00) 4 = Z_to_bv 64 0x12e04 := by
  decide +kernel
private theorem pc4_12e04 : v_addi (Z_to_bv 64 0x12e04) 4 = Z_to_bv 64 0x12e08 := by
  decide +kernel
private theorem pc4_12e08 : v_addi (Z_to_bv 64 0x12e08) 4 = Z_to_bv 64 0x12e0c := by
  decide +kernel
private theorem pc4_12e0c : v_addi (Z_to_bv 64 0x12e0c) 4 = Z_to_bv 64 0x12e10 := by
  decide +kernel
private theorem pc4_12e10 : v_addi (Z_to_bv 64 0x12e10) 4 = Z_to_bv 64 0x12e14 := by
  decide +kernel

private theorem pct_12dc0 :
    v_addi (Z_to_bv 64 0x12dc0) (bv_signed (0x18 : BitVec 13)) = Z_to_bv 64 0x12dd8 := by
  decide +kernel
private theorem pct_12dc4 :
    v_addi (Z_to_bv 64 0x12dc4) (bv_signed (0xc : BitVec 13)) = Z_to_bv 64 0x12dd0 := by
  decide +kernel
private theorem pct_12dcc :
    v_addi (Z_to_bv 64 0x12dcc) (bv_signed (0x38 : BitVec 13)) = Z_to_bv 64 0x12e04 := by
  decide +kernel
private theorem pct_12dd4 :
    btgt (Z_to_bv 64 0x12dd4) (bv_signed (0x3c : BitVec 21)) = Z_to_bv 64 0x12e10 := by
  decide +kernel
private theorem pct_12de0 :
    v_addi (Z_to_bv 64 0x12de0) (bv_signed (0x30 : BitVec 13)) = Z_to_bv 64 0x12e10 := by
  decide +kernel
private theorem pct_12df0 :
    v_addi (Z_to_bv 64 0x12df0) (bv_signed (0x20 : BitVec 13)) = Z_to_bv 64 0x12e10 := by
  decide +kernel

private theorem imm0 : bv_signed (0x0 : BitVec 12) = 0 := by decide
private theorem imm16 : bv_signed (0x10 : BitVec 12) = 16 := by decide
private theorem imm24 : bv_signed (0x18 : BitVec 12) = 24 := by decide
private theorem imm32 : bv_signed (0x20 : BitVec 12) = 32 := by decide

/-! ## The three shared tails

`0x12e10` is where every path returns from, `0x12dd0` the "return 0" tail and
`0x12e04` the "fire" tail. The Rocq script walks each of them once per path;
here each is one lemma, used from every path that reaches it. -/

private theorem tail_e10 (regs : bvmap 5 word) (mem : word → Option byte)
    (Q : machine_state → Prop)
    (hq : Q (mkst (regupd regs 10 (getr regs 12)) (ret_pc (getr regs 1)) mem
      (seg_rom Img0.rsegs))) :
    evt Img0.rsegs Q (mkst regs (Z_to_bv 64 0x12e10) mem (seg_rom Img0.rsegs)) := by
  refine evt_step (mstep_mkst (step_addi_at Img0.rsegs regs _ mem _ _ 10 12 0x0
    (getr regs 12) f_12e10 (by decide) Image.PlainCode.D_12e10 (by decide)
    (by rw [imm0]; exact v_addi_0 _))) ?_
  rw [pc4_12e10]
  refine evt_step (mstep_mkst (step_jalr_x0 Img0.rsegs _ _ mem _ _ 1 0x0 (getr regs 1)
    f_12e14 (by decide) Image.PlainCode.D_12e14
    (getr_other regs 10 _ 1 (by decide)))) ?_
  rw [imm0, ← ret_pc_jalr]
  exact evt_done hq

private theorem tail_dd0 (regs : bvmap 5 word) (mem : word → Option byte)
    (Q : machine_state → Prop)
    (hq : Q (mkst (regupd (regupd regs 12 (Z_to_bv 64 0)) 10 (Z_to_bv 64 0))
      (ret_pc (getr regs 1)) mem (seg_rom Img0.rsegs))) :
    evt Img0.rsegs Q (mkst regs (Z_to_bv 64 0x12dd0) mem (seg_rom Img0.rsegs)) := by
  refine evt_step (mstep_mkst (step_addi_at Img0.rsegs regs _ mem _ _ 12 0 0x0
    (Z_to_bv 64 0) f_12dd0 (by decide) Image.PlainCode.D_12dd0 (by decide)
    (by rw [getr_zero]; decide +kernel))) ?_
  rw [pc4_12dd0]
  refine evt_step (mstep_mkst (step_jal_x0 Img0.rsegs _ _ mem _ _ 0x3c
    f_12dd4 (by decide) Image.PlainCode.D_12dd4)) ?_
  rw [pct_12dd4]
  refine tail_e10 _ mem Q ?_
  rw [getr_same regs 12 _ (by decide), getr_other regs 12 _ 1 (by decide)]
  exact hq

private theorem tail_e04 (regs : bvmap 5 word) (mem : word → Option byte)
    (Q : machine_state → Prop)
    (hok0 : store_ok Img0.rsegs mem (v_addi (getr regs 10) 0) 4 = true)
    (hok32 : store_ok Img0.rsegs mem (v_addi (getr regs 10) 32) 4 = true)
    (hq : Q (mkst (regupd (regupd regs 12 (Z_to_bv 64 1)) 10 (Z_to_bv 64 1))
      (ret_pc (getr regs 1))
      (wbytes (wbytes mem (v_addi (getr regs 10) 0) (le4 (Z_to_bv 64 1)))
        (v_addi (getr regs 10) 32) (le4 (Z_to_bv 64 1)))
      (seg_rom Img0.rsegs))) :
    evt Img0.rsegs Q (mkst regs (Z_to_bv 64 0x12e04) mem (seg_rom Img0.rsegs)) := by
  -- 0x12e04  addi a2, x0, 1
  refine evt_step (mstep_mkst (step_addi_at Img0.rsegs regs _ mem _ _ 12 0 0x1
    (Z_to_bv 64 1) f_12e04 (by decide) Image.PlainCode.D_12e04 (by decide)
    (by rw [getr_zero]; decide +kernel))) ?_
  rw [pc4_12e04]
  have h10 : getr (regupd regs 12 (Z_to_bv 64 1)) 10 = getr regs 10 :=
    getr_other regs 12 _ 10 (by decide)
  have h12 : getr (regupd regs 12 (Z_to_bv 64 1)) 12 = Z_to_bv 64 1 :=
    getr_same regs 12 _ (by decide)
  have h1 : getr (regupd regs 12 (Z_to_bv 64 1)) 1 = getr regs 1 :=
    getr_other regs 12 _ 1 (by decide)
  -- 0x12e08  sw a2, 0(a0)
  refine evt_step (mstep_mkst (LinuxProcessSemantics.Common.SymExec.step_sw_val
    Img0.rsegs _ _ mem _ _ 10 12 0x0
    f_12e08 (by decide) Image.PlainCode.D_12e08
    (by rw [imm0, h10]; exact hok0))) ?_
  rw [pc4_12e08, imm0, h10, h12, le4_eq]
  -- 0x12e0c  sw a2, 32(a0)
  refine evt_step (mstep_mkst (LinuxProcessSemantics.Common.SymExec.step_sw_val
    Img0.rsegs _ _ _ _ _ 10 12 0x20
    f_12e0c (by decide) Image.PlainCode.D_12e0c
    (by rw [imm32, h10]
        exact store_ok_mono Img0.rsegs 4 mem _ _ (wbytes_grows _ mem _) hok32))) ?_
  rw [pc4_12e0c, imm32, h10, h12, le4_eq]
  refine tail_e10 _ _ Q ?_
  rw [h12, h1]
  exact hq

/-! ## The contract -/

/-- `lib/Prog/reac_knock_step.v:25-70`. -/
theorem reac_knock_step_holds : reac_knock_step_contract := by
  intro regs mem st g p1 opened due heard p2 bs0 bsd bsh hst0 hst1 hrw
    hrd0 hv0 hrd16 hv16 hrd24 hv24
  -- the three store bounds and the no-wrap bound, off the `wr_at` half of
  -- Rocq's `rw_cells` (`lib/Prog/reac_knock_step_c.v:25`), the way the Rocq
  -- proof reads them off `H`
  obtain ⟨-, hwr⟩ := hrw
  have hsz : cells_size (knock_cells st p1 opened due heard g p2) = 40 := rfl
  rw [hsz] at hwr
  obtain ⟨-, hA40, -⟩ := id hwr
  have hnw : bv_unsigned (getr regs 10) + 40 ≤ 2 ^ 64 := by omega
  have hok0 : store_ok Img0.rsegs mem (v_addi (getr regs 10) 0) 4 = true :=
    store_ok_of_wr_at Img0.rsegs mem _ 40 hwr 0 4 (by omega) (by omega) (by omega)
  have hok16 : store_ok Img0.rsegs mem (v_addi (getr regs 10) 16) 8 = true :=
    store_ok_of_wr_at Img0.rsegs mem _ 40 hwr 16 8 (by omega) (by omega) (by omega)
  have hok32 : store_ok Img0.rsegs mem (v_addi (getr regs 10) 32) 4 = true :=
    store_ok_of_wr_at Img0.rsegs mem _ 40 hwr 32 4 (by omega) (by omega) (by omega)
  have p31 : (2 : Int) ^ 31 = 2147483648 := by decide
  have p32 : (2 : Int) ^ 32 = 4294967296 := by decide
  have p64 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  have BT := u64_range (getr regs 11)
  have BH := u64_range heard
  have BD := u64_range due
  unfold REAC_KNOCK_STEP
  -- 0x12db8  lw a2, 0(a0)
  refine evt_step (mstep_mkst (step_lw Img0.rsegs regs _ mem _ _ 12 10 0x0 bs0
    (Z_to_bv 64 st) f_12db8 (by decide) Image.PlainCode.D_12db8
    (by rw [imm0]; exact hrd0)
    (by rw [hv0, Z_to_bv_unsigned, bv_wrap64_mod]
        exact (Int.emod_eq_of_lt hst0 (by omega)).symm))) ?_
  rw [show bv_eqb (12 : reg) 0 = false from by decide]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [pc4_12db8]
  -- 0x12dbc  addi a3, x0, 2
  refine evt_step (mstep_mkst (step_addi_at Img0.rsegs _ _ mem _ _ 13 0 0x2
    (Z_to_bv 64 2) f_12dbc (by decide) Image.PlainCode.D_12dbc (by decide)
    (by rw [getr_zero]; decide +kernel))) ?_
  rw [pc4_12dbc]
  -- the register file after the two instructions
  have g12 : getr (regupd (regupd regs 12 (v_lw (Z_to_bv 64 st))) 13 (Z_to_bv 64 2)) 12
      = v_lw (Z_to_bv 64 st) := by
    rw [getr_other _ 13 _ 12 (by decide), getr_same regs 12 _ (by decide)]
  have g13 : getr (regupd (regupd regs 12 (v_lw (Z_to_bv 64 st))) 13 (Z_to_bv 64 2)) 13
      = Z_to_bv 64 2 := getr_same _ 13 _ (by decide)
  have g10 : getr (regupd (regupd regs 12 (v_lw (Z_to_bv 64 st))) 13 (Z_to_bv 64 2)) 10
      = getr regs 10 := by
    rw [getr_other _ 13 _ 10 (by decide), getr_other regs 12 _ 10 (by decide)]
  have g11 : getr (regupd (regupd regs 12 (v_lw (Z_to_bv 64 st))) 13 (Z_to_bv 64 2)) 11
      = getr regs 11 := by
    rw [getr_other _ 13 _ 11 (by decide), getr_other regs 12 _ 11 (by decide)]
  have g1 : getr (regupd (regupd regs 12 (v_lw (Z_to_bv 64 st))) 13 (Z_to_bv 64 2)) 1
      = getr regs 1 := by
    rw [getr_other _ 13 _ 1 (by decide), getr_other regs 12 _ 1 (by decide)]
  -- 0x12dc0  beq a2, a3  --  the `Z.eqb st 2` of the contract
  have hbr2 : branch_taken branch_cond.BC_EQ
      (getr (regupd (regupd regs 12 (v_lw (Z_to_bv 64 st))) 13 (Z_to_bv 64 2)) 12)
      (getr (regupd (regupd regs 12 (v_lw (Z_to_bv 64 st))) 13 (Z_to_bv 64 2)) 13)
      = decide (st = 2) := by
    rw [g12, g13]
    show bv_eqb (v_lw (Z_to_bv 64 st)) (Z_to_bv 64 2) = _
    rw [← sx32_v_lw]
    exact knock_sx32_eqb st 2 hst0 hst1 (by omega) (by omega)
  by_cases h2 : st = 2
  · -- the state is 2: the listen window
    subst h2
    refine evt_step (mstep_mkst (step_branch_taken Img0.rsegs _ _ mem _ _ .BC_EQ 12 13 0x18
      f_12dc0 (by decide) Image.PlainCode.D_12dc0
      (hbr2.trans (decide_eq_true (rfl : (2 : Int) = 2))))) ?_
    rw [pct_12dc0]
    -- 0x12dd8  ld a3, 24(a0)
    refine evt_step (mstep_mkst (step_ld Img0.rsegs _ _ mem _ _ 13 10 0x18 bsh heard
      f_12dd8 (by decide) Image.PlainCode.D_12dd8
      (by rw [imm24, g10]; exact hrd24) hv24)) ?_
    rw [show bv_eqb (13 : reg) 0 = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [pc4_12dd8]
    -- 0x12ddc  addi a2, x0, 0
    refine evt_step (mstep_mkst (step_addi_at Img0.rsegs _ _ mem _ _ 12 0 0x0
      (Z_to_bv 64 0) f_12ddc (by decide) Image.PlainCode.D_12ddc (by decide)
      (by rw [getr_zero]; decide +kernel))) ?_
    rw [pc4_12ddc]
    -- the register file at 0x12de0
    have r4_13 : getr (regupd (regupd (regupd (regupd regs 12 (v_lw (Z_to_bv 64 2)))
        13 (Z_to_bv 64 2)) 13 heard) 12 (Z_to_bv 64 0)) 13 = heard := by
      rw [getr_other _ 12 _ 13 (by decide), getr_same _ 13 _ (by decide)]
    have r4_11 : getr (regupd (regupd (regupd (regupd regs 12 (v_lw (Z_to_bv 64 2)))
        13 (Z_to_bv 64 2)) 13 heard) 12 (Z_to_bv 64 0)) 11 = getr regs 11 := by
      rw [getr_other _ 12 _ 11 (by decide), getr_other _ 13 _ 11 (by decide), g11]
    have r4_12 : getr (regupd (regupd (regupd (regupd regs 12 (v_lw (Z_to_bv 64 2)))
        13 (Z_to_bv 64 2)) 13 heard) 12 (Z_to_bv 64 0)) 12 = Z_to_bv 64 0 :=
      getr_same _ 12 _ (by decide)
    have r4_1 : getr (regupd (regupd (regupd (regupd regs 12 (v_lw (Z_to_bv 64 2)))
        13 (Z_to_bv 64 2)) 13 heard) 12 (Z_to_bv 64 0)) 1 = getr regs 1 := by
      rw [getr_other _ 12 _ 1 (by decide), getr_other _ 13 _ 1 (by decide), g1]
    -- 0x12de0  bgeu a3, a1  --  the `t <=? heard` of the contract
    have hbr3 : branch_taken branch_cond.BC_GEU
        (getr (regupd (regupd (regupd (regupd regs 12 (v_lw (Z_to_bv 64 2)))
          13 (Z_to_bv 64 2)) 13 heard) 12 (Z_to_bv 64 0)) 13)
        (getr (regupd (regupd (regupd (regupd regs 12 (v_lw (Z_to_bv 64 2)))
          13 (Z_to_bv 64 2)) 13 heard) 12 (Z_to_bv 64 0)) 11)
        = decide (bv_unsigned (getr regs 11) ≤ bv_unsigned heard) := by
      rw [r4_13, r4_11]
      show (!bv_ltu heard (getr regs 11)) = _
      rw [bv_ltu_Z, not_decide_lt]
    by_cases hle : bv_unsigned (getr regs 11) ≤ bv_unsigned heard
    · -- t <= heard: nothing happens
      refine evt_step (mstep_mkst (step_branch_taken Img0.rsegs _ _ mem _ _ .BC_GEU 13 11 0x30
        f_12de0 (by decide) Image.PlainCode.D_12de0 (hbr3.trans (decide_eq_true hle)))) ?_
      rw [pct_12de0]
      refine tail_e10 _ mem _ ?_
      rw [r4_12, r4_1]
      refine ⟨_, mem, rfl, munch_refl _ mem, wmono_refl _ mem, ?_, ?_, ?_⟩
      · rw [knock_step_mem, ite_eq_left rfl, ite_eq_left (Or.inl hle)]
      · rw [getr_same _ 10 _ (by decide), knock_step_f, ite_eq_left rfl,
          ite_eq_left (Or.inl hle)]
      · intro r h10' h12' h13' _ _
        rw [getr_other _ 10 _ r h10', getr_other _ 12 _ r h12',
          getr_other _ 13 _ r h13', getr_other _ 13 _ r h13',
          getr_other _ 12 _ r h12']
    · -- heard < t
      have hlt : bv_unsigned heard < bv_unsigned (getr regs 11) := by omega
      refine evt_step (mstep_mkst (step_branch_not Img0.rsegs _ _ mem _ _ .BC_GEU 13 11 0x30
        f_12de0 (by decide) Image.PlainCode.D_12de0
        (hbr3.trans (decide_eq_false hle)))) ?_
      rw [pc4_12de0]
      -- 0x12de4  sub a5, a1, a3
      refine evt_step (mstep_mkst (step_sub_at Img0.rsegs _ _ mem _ _ 15 11 13
        (v_sub (getr regs 11) heard) f_12de4 (by decide) Image.PlainCode.D_12de4
        (by decide) (by rw [r4_11, r4_13]))) ?_
      rw [pc4_12de4]
      -- 0x12de8  lui a4, 0x1dcd6
      refine evt_step (mstep_mkst (step_lui_at Img0.rsegs _ _ mem _ _ 14 0x1dcd6
        (Z_to_bv 64 0x1dcd6000) f_12de8 (by decide) Image.PlainCode.D_12de8
        (by decide) (by decide +kernel))) ?_
      rw [pc4_12de8]
      -- 0x12dec  addiw a4, a4, 0x500
      refine evt_step (mstep_mkst (step_addiw_at Img0.rsegs _ _ mem _ _ 14 14 0x500
        (Z_to_bv 64 500000000) f_12dec (by decide) Image.PlainCode.D_12dec
        (by decide)
        (by rw [getr_same _ 14 _ (by decide)]; decide +kernel))) ?_
      rw [pc4_12dec]
      -- the register file at 0x12df0
      have q15 : getr (regupd (regupd (regupd (regupd (regupd (regupd
          (regupd regs 12 (v_lw (Z_to_bv 64 2))) 13 (Z_to_bv 64 2)) 13 heard)
          12 (Z_to_bv 64 0)) 15 (v_sub (getr regs 11) heard)) 14 (Z_to_bv 64 0x1dcd6000))
          14 (Z_to_bv 64 500000000)) 15 = v_sub (getr regs 11) heard := by
        rw [getr_other _ 14 _ 15 (by decide), getr_other _ 14 _ 15 (by decide),
          getr_same _ 15 _ (by decide)]
      have q14 : getr (regupd (regupd (regupd (regupd (regupd (regupd
          (regupd regs 12 (v_lw (Z_to_bv 64 2))) 13 (Z_to_bv 64 2)) 13 heard)
          12 (Z_to_bv 64 0)) 15 (v_sub (getr regs 11) heard)) 14 (Z_to_bv 64 0x1dcd6000))
          14 (Z_to_bv 64 500000000)) 14 = Z_to_bv 64 500000000 :=
        getr_same _ 14 _ (by decide)
      have q12 : getr (regupd (regupd (regupd (regupd (regupd (regupd
          (regupd regs 12 (v_lw (Z_to_bv 64 2))) 13 (Z_to_bv 64 2)) 13 heard)
          12 (Z_to_bv 64 0)) 15 (v_sub (getr regs 11) heard)) 14 (Z_to_bv 64 0x1dcd6000))
          14 (Z_to_bv 64 500000000)) 12 = Z_to_bv 64 0 := by
        rw [getr_other _ 14 _ 12 (by decide), getr_other _ 14 _ 12 (by decide),
          getr_other _ 15 _ 12 (by decide), getr_same _ 12 _ (by decide)]
      have q1 : getr (regupd (regupd (regupd (regupd (regupd (regupd
          (regupd regs 12 (v_lw (Z_to_bv 64 2))) 13 (Z_to_bv 64 2)) 13 heard)
          12 (Z_to_bv 64 0)) 15 (v_sub (getr regs 11) heard)) 14 (Z_to_bv 64 0x1dcd6000))
          14 (Z_to_bv 64 500000000)) 1 = getr regs 1 := by
        rw [getr_other _ 14 _ 1 (by decide), getr_other _ 14 _ 1 (by decide),
          getr_other _ 15 _ 1 (by decide), getr_other _ 12 _ 1 (by decide),
          getr_other _ 13 _ 1 (by decide), g1]
      have hsub : bv_unsigned (v_sub (getr regs 11) heard)
          = bv_unsigned (getr regs 11) - bv_unsigned heard :=
        v_sub_small _ _ (by omega)
      -- 0x12df0  bltu a5, a4  --  the `t - heard <? L_NS` of the contract
      have hbr4 : branch_taken branch_cond.BC_LTU
          (getr (regupd (regupd (regupd (regupd (regupd (regupd
            (regupd regs 12 (v_lw (Z_to_bv 64 2))) 13 (Z_to_bv 64 2)) 13 heard)
            12 (Z_to_bv 64 0)) 15 (v_sub (getr regs 11) heard)) 14 (Z_to_bv 64 0x1dcd6000))
            14 (Z_to_bv 64 500000000)) 15)
          (getr (regupd (regupd (regupd (regupd (regupd (regupd
            (regupd regs 12 (v_lw (Z_to_bv 64 2))) 13 (Z_to_bv 64 2)) 13 heard)
            12 (Z_to_bv 64 0)) 15 (v_sub (getr regs 11) heard)) 14 (Z_to_bv 64 0x1dcd6000))
            14 (Z_to_bv 64 500000000)) 14)
          = decide (bv_unsigned (getr regs 11) - bv_unsigned heard < L_NS) := by
        rw [q15, q14]
        show bv_ltu (v_sub (getr regs 11) heard) (Z_to_bv 64 500000000) = _
        rw [bv_ltu_Z, hsub, Z_to_bv_unsigned, bv_wrap64_mod, L_NS]
        exact decide_eq_decide.2 (by omega)
      by_cases hns : bv_unsigned (getr regs 11) - bv_unsigned heard < L_NS
      · -- still inside the listen window: nothing happens
        refine evt_step (mstep_mkst (step_branch_taken Img0.rsegs _ _ mem _ _ .BC_LTU 15 14 0x20
          f_12df0 (by decide) Image.PlainCode.D_12df0 (hbr4.trans (decide_eq_true hns)))) ?_
        rw [pct_12df0]
        refine tail_e10 _ mem _ ?_
        rw [q12, q1]
        refine ⟨_, mem, rfl, munch_refl _ mem, wmono_refl _ mem, ?_, ?_, ?_⟩
        · rw [knock_step_mem, ite_eq_left rfl, ite_eq_left (Or.inr hns)]
        · rw [getr_same _ 10 _ (by decide), knock_step_f, ite_eq_left rfl,
            ite_eq_left (Or.inr hns)]
        · intro r h10' h12' h13' h14' h15'
          rw [getr_other _ 10 _ r h10', getr_other _ 14 _ r h14',
            getr_other _ 14 _ r h14', getr_other _ 15 _ r h15',
            getr_other _ 12 _ r h12', getr_other _ 13 _ r h13',
            getr_other _ 13 _ r h13', getr_other _ 12 _ r h12']
      · -- the window has run out: a new due time, and the knock fires
        have hge : (500000000 : Int) ≤ bv_unsigned (getr regs 11) - bv_unsigned heard := by
          have h := hns
          rw [L_NS] at h
          omega
        have hnotcond : ¬(bv_unsigned (getr regs 11) ≤ bv_unsigned heard ∨
            bv_unsigned (getr regs 11) - bv_unsigned heard < L_NS) := by
          intro hcon
          cases hcon with
          | inl h => omega
          | inr h => rw [L_NS] at h; omega
        refine evt_step (mstep_mkst (step_branch_not Img0.rsegs _ _ mem _ _ .BC_LTU 15 14 0x20
          f_12df0 (by decide) Image.PlainCode.D_12df0
          (hbr4.trans (decide_eq_false hns)))) ?_
        rw [pc4_12df0]
        have q13 : getr (regupd (regupd (regupd (regupd (regupd (regupd
            (regupd regs 12 (v_lw (Z_to_bv 64 2))) 13 (Z_to_bv 64 2)) 13 heard)
            12 (Z_to_bv 64 0)) 15 (v_sub (getr regs 11) heard)) 14 (Z_to_bv 64 0x1dcd6000))
            14 (Z_to_bv 64 500000000)) 13 = heard := by
          rw [getr_other _ 14 _ 13 (by decide), getr_other _ 14 _ 13 (by decide),
            getr_other _ 15 _ 13 (by decide), getr_other _ 12 _ 13 (by decide),
            getr_same _ 13 _ (by decide)]
        -- 0x12df4  add a3, a3, a4
        refine evt_step (mstep_mkst (step_add_at Img0.rsegs _ _ mem _ _ 13 13 14
          (Z_to_bv 64 (bv_unsigned heard + L_NS)) f_12df4 (by decide)
          Image.PlainCode.D_12df4 (by decide)
          (by rw [q13, q14, v_add_lit, L_NS]))) ?_
        rw [pc4_12df4]
        -- the register file at 0x12df8
        have s10 : getr (regupd (regupd (regupd (regupd (regupd (regupd
            (regupd (regupd regs 12 (v_lw (Z_to_bv 64 2))) 13 (Z_to_bv 64 2)) 13 heard)
            12 (Z_to_bv 64 0)) 15 (v_sub (getr regs 11) heard)) 14 (Z_to_bv 64 0x1dcd6000))
            14 (Z_to_bv 64 500000000)) 13 (Z_to_bv 64 (bv_unsigned heard + L_NS))) 10
            = getr regs 10 := by
          rw [getr_other _ 13 _ 10 (by decide), getr_other _ 14 _ 10 (by decide),
            getr_other _ 14 _ 10 (by decide), getr_other _ 15 _ 10 (by decide),
            getr_other _ 12 _ 10 (by decide), getr_other _ 13 _ 10 (by decide), g10]
        have s13 : getr (regupd (regupd (regupd (regupd (regupd (regupd
            (regupd (regupd regs 12 (v_lw (Z_to_bv 64 2))) 13 (Z_to_bv 64 2)) 13 heard)
            12 (Z_to_bv 64 0)) 15 (v_sub (getr regs 11) heard)) 14 (Z_to_bv 64 0x1dcd6000))
            14 (Z_to_bv 64 500000000)) 13 (Z_to_bv 64 (bv_unsigned heard + L_NS))) 13
            = Z_to_bv 64 (bv_unsigned heard + L_NS) := getr_same _ 13 _ (by decide)
        have s11 : getr (regupd (regupd (regupd (regupd (regupd (regupd
            (regupd (regupd regs 12 (v_lw (Z_to_bv 64 2))) 13 (Z_to_bv 64 2)) 13 heard)
            12 (Z_to_bv 64 0)) 15 (v_sub (getr regs 11) heard)) 14 (Z_to_bv 64 0x1dcd6000))
            14 (Z_to_bv 64 500000000)) 13 (Z_to_bv 64 (bv_unsigned heard + L_NS))) 11
            = getr regs 11 := by
          rw [getr_other _ 13 _ 11 (by decide), getr_other _ 14 _ 11 (by decide),
            getr_other _ 14 _ 11 (by decide), getr_other _ 15 _ 11 (by decide),
            getr_other _ 12 _ 11 (by decide), getr_other _ 13 _ 11 (by decide), g11]
        have s1 : getr (regupd (regupd (regupd (regupd (regupd (regupd
            (regupd (regupd regs 12 (v_lw (Z_to_bv 64 2))) 13 (Z_to_bv 64 2)) 13 heard)
            12 (Z_to_bv 64 0)) 15 (v_sub (getr regs 11) heard)) 14 (Z_to_bv 64 0x1dcd6000))
            14 (Z_to_bv 64 500000000)) 13 (Z_to_bv 64 (bv_unsigned heard + L_NS))) 1
            = getr regs 1 := by
          rw [getr_other _ 13 _ 1 (by decide), getr_other _ 14 _ 1 (by decide),
            getr_other _ 14 _ 1 (by decide), getr_other _ 15 _ 1 (by decide),
            getr_other _ 12 _ 1 (by decide), getr_other _ 13 _ 1 (by decide), g1]
        -- 0x12df8  sw x0, 0(a0)
        refine evt_step (mstep_mkst (LinuxProcessSemantics.Common.SymExec.step_sw_val
          Img0.rsegs _ _ mem _ _ 10 0 0x0
          f_12df8 (by decide) Image.PlainCode.D_12df8
          (by rw [imm0, s10]; exact hok0))) ?_
        rw [pc4_12df8, imm0, s10, getr_zero, le4_eq]
        -- 0x12dfc  sd a3, 16(a0)
        refine evt_step (mstep_mkst (step_sd_at Img0.rsegs _ _ _ _ _ 10 13 0x10
          (v_addi (getr regs 10) 16) (Z_to_bv 64 (bv_unsigned heard + L_NS))
          f_12dfc (by decide) Image.PlainCode.D_12dfc
          (by rw [imm16, s10]) s13
          (store_ok_mono Img0.rsegs 8 mem _ _ (wbytes_grows _ mem _) hok16))) ?_
        rw [pc4_12dfc, le8_eq]
        -- 0x12e00  bltu a1, a3: the new due time is never above t
        have hdue' : bv_unsigned (Z_to_bv 64 (bv_unsigned heard + L_NS))
            = bv_unsigned heard + L_NS := by
          rw [Z_to_bv_unsigned, bv_wrap64_mod, L_NS]
          exact Int.emod_eq_of_lt (by omega) (by omega)
        have hbr5 : branch_taken branch_cond.BC_LTU
            (getr (regupd (regupd (regupd (regupd (regupd (regupd
              (regupd (regupd regs 12 (v_lw (Z_to_bv 64 2))) 13 (Z_to_bv 64 2)) 13 heard)
              12 (Z_to_bv 64 0)) 15 (v_sub (getr regs 11) heard)) 14 (Z_to_bv 64 0x1dcd6000))
              14 (Z_to_bv 64 500000000)) 13 (Z_to_bv 64 (bv_unsigned heard + L_NS))) 11)
            (getr (regupd (regupd (regupd (regupd (regupd (regupd
              (regupd (regupd regs 12 (v_lw (Z_to_bv 64 2))) 13 (Z_to_bv 64 2)) 13 heard)
              12 (Z_to_bv 64 0)) 15 (v_sub (getr regs 11) heard)) 14 (Z_to_bv 64 0x1dcd6000))
              14 (Z_to_bv 64 500000000)) 13 (Z_to_bv 64 (bv_unsigned heard + L_NS))) 13)
            = false := by
          rw [s11, s13]
          show bv_ltu (getr regs 11) (Z_to_bv 64 (bv_unsigned heard + L_NS)) = _
          rw [bv_ltu_Z, hdue']
          refine decide_eq_false ?_
          have h := hge
          rw [L_NS]
          omega
        refine evt_step (mstep_mkst (step_branch_not Img0.rsegs _ _ _ _ _ .BC_LTU 11 13 0x1fd0
          f_12e00 (by decide) Image.PlainCode.D_12e00 hbr5)) ?_
        rw [pc4_12e00]
        -- 0x12e04  the fire tail
        refine tail_e04 _ _ _ ?_ ?_ ?_
        · rw [s10]
          exact store_ok_mono Img0.rsegs 4 mem _ _ (grows2 mem _ _ _ _) hok0
        · rw [s10]
          exact store_ok_mono Img0.rsegs 4 mem _ _ (grows2 mem _ _ _ _) hok32
        · rw [s10, s1]
          refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_⟩
          · intro x hx
            rw [munch_store (getr regs 10) 32 4 _ (len_le4 _) _ (by omega) (by omega)
                (by omega) hnw x hx,
              munch_store (getr regs 10) 0 4 _ (len_le4 _) _ (by omega) (by omega)
                (by omega) hnw x hx,
              munch_store (getr regs 10) 16 8 _ (len_le8 _) _ (by omega) (by omega)
                (by omega) hnw x hx,
              munch_store (getr regs 10) 0 4 _ (len_le4 _) _ (by omega) (by omega)
                (by omega) hnw x hx]
          · intro x hx
            exact wview_grows Img0.rsegs mem _ x
              (mem_grows_trans _ _ _ (grows2 mem _ _ _ _) (grows2 _ _ _ _ _)) hx
          · rw [knock_step_mem, ite_eq_left rfl, ite_eq_right hnotcond]
          · rw [getr_same _ 10 _ (by decide), knock_step_f, ite_eq_left rfl,
              ite_eq_right hnotcond]
          · intro r h10' h12' h13' h14' h15'
            rw [getr_other _ 10 _ r h10', getr_other _ 12 _ r h12',
              getr_other _ 13 _ r h13', getr_other _ 14 _ r h14',
              getr_other _ 14 _ r h14', getr_other _ 15 _ r h15',
              getr_other _ 12 _ r h12', getr_other _ 13 _ r h13',
              getr_other _ 13 _ r h13', getr_other _ 12 _ r h12']
  · -- the state is not 2
    refine evt_step (mstep_mkst (step_branch_not Img0.rsegs _ _ mem _ _ .BC_EQ 12 13 0x18
      f_12dc0 (by decide) Image.PlainCode.D_12dc0 (hbr2.trans (decide_eq_false h2)))) ?_
    rw [pc4_12dc0]
    -- 0x12dc4  bne a2, x0  --  the `Z.eqb st 0` of the contract
    have hbr0 : branch_taken branch_cond.BC_NE
        (getr (regupd (regupd regs 12 (v_lw (Z_to_bv 64 st))) 13 (Z_to_bv 64 2)) 12)
        (getr (regupd (regupd regs 12 (v_lw (Z_to_bv 64 st))) 13 (Z_to_bv 64 2)) 0)
        = !decide (st = 0) := by
      rw [g12, getr_zero]
      show (!bv_eqb (v_lw (Z_to_bv 64 st)) (Z_to_bv 64 0)) = _
      rw [← sx32_v_lw, knock_sx32_eqb st 0 hst0 hst1 (by omega) (by omega)]
    by_cases h0 : st = 0
    · -- the state is 0: the armed state
      subst h0
      refine evt_step (mstep_mkst (step_branch_not Img0.rsegs _ _ mem _ _ .BC_NE 12 0 0xc
        f_12dc4 (by decide) Image.PlainCode.D_12dc4
        (by rw [hbr0] <;> decide))) ?_
      rw [pc4_12dc4]
      -- 0x12dc8  ld a3, 16(a0)
      refine evt_step (mstep_mkst (step_ld Img0.rsegs _ _ mem _ _ 13 10 0x10 bsd due
        f_12dc8 (by decide) Image.PlainCode.D_12dc8
        (by rw [imm16, g10]; exact hrd16) hv16)) ?_
      rw [show bv_eqb (13 : reg) 0 = false from by decide]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [pc4_12dc8]
      have t13 : getr (regupd (regupd (regupd regs 12 (v_lw (Z_to_bv 64 0)))
          13 (Z_to_bv 64 2)) 13 due) 13 = due := getr_same _ 13 _ (by decide)
      have t11 : getr (regupd (regupd (regupd regs 12 (v_lw (Z_to_bv 64 0)))
          13 (Z_to_bv 64 2)) 13 due) 11 = getr regs 11 := by
        rw [getr_other _ 13 _ 11 (by decide), g11]
      have t10 : getr (regupd (regupd (regupd regs 12 (v_lw (Z_to_bv 64 0)))
          13 (Z_to_bv 64 2)) 13 due) 10 = getr regs 10 := by
        rw [getr_other _ 13 _ 10 (by decide), g10]
      have t1 : getr (regupd (regupd (regupd regs 12 (v_lw (Z_to_bv 64 0)))
          13 (Z_to_bv 64 2)) 13 due) 1 = getr regs 1 := by
        rw [getr_other _ 13 _ 1 (by decide), g1]
      -- 0x12dcc  bgeu a1, a3  --  the `t <? due` of the contract
      have hbr6 : branch_taken branch_cond.BC_GEU
          (getr (regupd (regupd (regupd regs 12 (v_lw (Z_to_bv 64 0)))
            13 (Z_to_bv 64 2)) 13 due) 11)
          (getr (regupd (regupd (regupd regs 12 (v_lw (Z_to_bv 64 0)))
            13 (Z_to_bv 64 2)) 13 due) 13)
          = decide (bv_unsigned due ≤ bv_unsigned (getr regs 11)) := by
        rw [t11, t13]
        show (!bv_ltu (getr regs 11) due) = _
        rw [bv_ltu_Z, not_decide_lt]
      by_cases hdue : bv_unsigned (getr regs 11) < bv_unsigned due
      · -- the due time has not come
        refine evt_step (mstep_mkst (step_branch_not Img0.rsegs _ _ mem _ _ .BC_GEU 11 13 0x38
          f_12dcc (by decide) Image.PlainCode.D_12dcc
          (hbr6.trans (decide_eq_false (by omega))))) ?_
        rw [pc4_12dcc]
        refine tail_dd0 _ mem _ ?_
        rw [t1]
        refine ⟨_, mem, rfl, munch_refl _ mem, wmono_refl _ mem, ?_, ?_, ?_⟩
        · rw [knock_step_mem, ite_eq_right (by decide : ¬((0 : Int) = 2)),
            ite_eq_left rfl, ite_eq_left hdue]
        · rw [getr_same _ 10 _ (by decide), knock_step_f,
            ite_eq_right (by decide : ¬((0 : Int) = 2)), ite_eq_left rfl,
            ite_eq_left hdue]
        · intro r h10' h12' h13' _ _
          rw [getr_other _ 10 _ r h10', getr_other _ 12 _ r h12',
            getr_other _ 13 _ r h13', getr_other _ 13 _ r h13',
            getr_other _ 12 _ r h12']
      · -- the due time has come: the knock fires
        have hge : bv_unsigned due ≤ bv_unsigned (getr regs 11) := by omega
        refine evt_step (mstep_mkst (step_branch_taken Img0.rsegs _ _ mem _ _ .BC_GEU 11 13 0x38
          f_12dcc (by decide) Image.PlainCode.D_12dcc
          (hbr6.trans (decide_eq_true hge)))) ?_
        rw [pct_12dcc]
        refine tail_e04 _ mem _ (by rw [t10]; exact hok0) (by rw [t10]; exact hok32) ?_
        rw [t10, t1]
        refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · intro x hx
          rw [munch_store (getr regs 10) 32 4 _ (len_le4 _) _ (by omega) (by omega)
              (by omega) hnw x hx,
            munch_store (getr regs 10) 0 4 _ (len_le4 _) _ (by omega) (by omega)
              (by omega) hnw x hx]
        · intro x hx
          exact wview_grows Img0.rsegs mem _ x (grows2 mem _ _ _ _) hx
        · rw [knock_step_mem, ite_eq_right (by decide : ¬((0 : Int) = 2)),
            ite_eq_left rfl, ite_eq_right hdue]
        · rw [getr_same _ 10 _ (by decide), knock_step_f,
            ite_eq_right (by decide : ¬((0 : Int) = 2)), ite_eq_left rfl,
            ite_eq_right hdue]
        · intro r h10' h12' h13' _ _
          rw [getr_other _ 10 _ r h10', getr_other _ 12 _ r h12',
            getr_other _ 13 _ r h13', getr_other _ 13 _ r h13',
            getr_other _ 12 _ r h12']
    · -- the state is neither 0 nor 2: nothing happens
      refine evt_step (mstep_mkst (step_branch_taken Img0.rsegs _ _ mem _ _ .BC_NE 12 0 0xc
        f_12dc4 (by decide) Image.PlainCode.D_12dc4
        (by rw [hbr0, decide_eq_false h0] <;> rfl))) ?_
      rw [pct_12dc4]
      refine tail_dd0 _ mem _ ?_
      rw [g1]
      refine ⟨_, mem, rfl, munch_refl _ mem, wmono_refl _ mem, ?_, ?_, ?_⟩
      · rw [knock_step_mem, ite_eq_right h2, ite_eq_right h0]
      · rw [getr_same _ 10 _ (by decide), knock_step_f, ite_eq_right h2,
          ite_eq_right h0]
      · intro r h10' h12' h13' _ _
        rw [getr_other _ 10 _ r h10', getr_other _ 12 _ r h12',
          getr_other _ 13 _ r h13', getr_other _ 12 _ r h12']

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_step
