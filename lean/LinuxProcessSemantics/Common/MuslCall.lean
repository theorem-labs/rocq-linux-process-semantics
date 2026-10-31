import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.Hoare
import LinuxProcessSemantics.Common.WallSim

/-! rocq-baseline: 2cde689f94c086b868999970834b76a25616b94a -/

/-! # Common.MuslCall — address-parametric summaries of musl's `write` wrapper

Ported from `theories/Common/MuslCall.v` at the baseline above, with the
Rocq names and statements: the blob's instruction words and their
decodings (`W*`, `D_*`, `E_ecall`), the clobber and write sets
`musl_clob` and `musl_wset`, the two summaries `musl_write_enter` (entry
to the `ecall`) and `musl_write_leave` (the post-syscall path through
`__syscall_ret`'s not-taken errno branch) with `errno_lo` and
`not_errno`, the whole-call hand-offs `musl_write_wexit` (to a
`to_wexit` continuation) and `musl_write_wall` (to a put loop's
`to_wall_tail`), and the frame lemma `musl_write_frame`.  The blob's
layout, why it is position-independent, and why the summaries split at
the `ecall` are the Rocq file's header, not repeated here.

Spellings that differ:
- Rocq Section `MuslWrite`'s variables `segs` and `B` and its fetch
  hypotheses `F00` … `F90` become explicit leading arguments of each
  lemma that uses them, in declaration order, which is how Rocq closes
  the section; `musl_clob`, `musl_wset`, `errno_lo` and `not_errno` use
  none of them and take none, and `musl_write_frame` takes `segs` only.
- `firstn n out` and `skipn n out` are `out.take n` and `out.drop n`;
  `(0 <= i < Z.of_nat n)%Z` is `0 ≤ i ∧ i < (n : Int)`.
- The decode facts are closed by `decide +kernel` where Rocq runs
  `vm_refl_bv`.

Rocq's chain tactics `at_fold`, `gres`, `apc`, `hstepv` and `in_clob` are
Ltac (proof automation, not constants) and have no Lean twin.  Each step
of a chain is one `refine` through Lean-only helpers instead, each
named for what a Rocq tactic did inline:
- `mst_next` is `hstepv`'s `eapply mst_step`, with the landing register
  file and pc restated so that each step names its result;
- `at_step` is `apc`'s `rewrite at_addi` and `at_fold`, the literal
  offset sum closed by `decide`;
- `if_link` is `apc`'s `reduce_bv_eqb_ifs` on the `if` that a linking
  `jal` or the `ld ra` leaves in the register file.
Register reads are peeled by `simp only` over `getr_same`, `getr_other`
and `getr_zero`, with `decide` discharging the register disequalities that
Rocq's `gres` closes by `reg_neq_tac`; `in_clob` is
`unfold musl_clob; decide`. -/

namespace LinuxProcessSemantics.Common.MuslCall

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.Hoare
open LinuxProcessSemantics.Common.WallSim

/-! ## Instruction words and their decodings

A decode fact is a statement about a 32-bit word, not about an image, so it
is proved here rather than assumed per binary. -/

def Wsp16m : BitVec 32 := 4278255891
def Wmv_a3a2 : BitVec 32 := 394899
def Wli_a6_0 : BitVec 32 := 2067
def Wmv_a2a1 : BitVec 32 := 362003
def Wli_a5_0 : BitVec 32 := 1939
def Wmv_a1a0 : BitVec 32 := 329107
def Wli_a4_0 : BitVec 32 := 1811
def Wli_a0_64 : BitVec 32 := 67110163
def Wsd_ra8 : BitVec 32 := 1127459
def Wjal_cp : BitVec 32 := 113246447
def Wld_ra8 : BitVec 32 := 8466563
def Wsp16p : BitVec 32 := 16843027
def Wj4 : BitVec 32 := 4194415
def Wlui_a5 : BitVec 32 := 4294965175
def Wbltu : BitVec 32 := 11002979
def Wret : BitVec 32 := 32871
def Wmv_a7a0 : BitVec 32 := 329875
def Wmv_a0a1 : BitVec 32 := 361747
def Wmv_a1a2 : BitVec 32 := 394643
def Wmv_a2a3 : BitVec 32 := 427539
def Wmv_a3a4 : BitVec 32 := 460435
def Wmv_a4a5 : BitVec 32 := 493331
def Wmv_a5a6 : BitVec 32 := 526227
def Wecall : BitVec 32 := 115
def Wj_cpc : BitVec 32 := 4259311727

theorem D_sp16m : decode_any Wsp16m = some (.OpImm .ALU_ADD 2 2 4080, 4) := by decide +kernel
theorem D_mv_a3a2 : decode_any Wmv_a3a2 = some (.OpImm .ALU_ADD 13 12 0, 4) := by decide +kernel
theorem D_li_a6_0 : decode_any Wli_a6_0 = some (.OpImm .ALU_ADD 16 0 0, 4) := by decide +kernel
theorem D_mv_a2a1 : decode_any Wmv_a2a1 = some (.OpImm .ALU_ADD 12 11 0, 4) := by decide +kernel
theorem D_li_a5_0 : decode_any Wli_a5_0 = some (.OpImm .ALU_ADD 15 0 0, 4) := by decide +kernel
theorem D_mv_a1a0 : decode_any Wmv_a1a0 = some (.OpImm .ALU_ADD 11 10 0, 4) := by decide +kernel
theorem D_li_a4_0 : decode_any Wli_a4_0 = some (.OpImm .ALU_ADD 14 0 0, 4) := by decide +kernel
theorem D_li_a0_64 : decode_any Wli_a0_64 = some (.OpImm .ALU_ADD 10 0 64, 4) := by
  decide +kernel
theorem D_sd_ra8 : decode_any Wsd_ra8 = some (.Store .SZ8 2 1 8, 4) := by decide +kernel
theorem D_jal_cp : decode_any Wjal_cp = some (.Jal 1 108, 4) := by decide +kernel
theorem D_ld_ra8 : decode_any Wld_ra8 = some (.Load .SZ8 true 1 2 8, 4) := by decide +kernel
theorem D_sp16p : decode_any Wsp16p = some (.OpImm .ALU_ADD 2 2 16, 4) := by decide +kernel
theorem D_j4 : decode_any Wj4 = some (.Jal 0 4, 4) := by decide +kernel
theorem D_lui_a5 : decode_any Wlui_a5 = some (.Lui 15 1048575, 4) := by decide +kernel
theorem D_bltu : decode_any Wbltu = some (.Branch .BC_LTU 15 10 8, 4) := by decide +kernel
theorem D_ret : decode_any Wret = some (.Jalr 0 1 0, 4) := by decide +kernel
theorem D_mv_a7a0 : decode_any Wmv_a7a0 = some (.OpImm .ALU_ADD 17 10 0, 4) := by decide +kernel
theorem D_mv_a0a1 : decode_any Wmv_a0a1 = some (.OpImm .ALU_ADD 10 11 0, 4) := by decide +kernel
theorem D_mv_a1a2 : decode_any Wmv_a1a2 = some (.OpImm .ALU_ADD 11 12 0, 4) := by decide +kernel
theorem D_mv_a2a3 : decode_any Wmv_a2a3 = some (.OpImm .ALU_ADD 12 13 0, 4) := by decide +kernel
theorem D_mv_a3a4 : decode_any Wmv_a3a4 = some (.OpImm .ALU_ADD 13 14 0, 4) := by decide +kernel
theorem D_mv_a4a5 : decode_any Wmv_a4a5 = some (.OpImm .ALU_ADD 14 15 0, 4) := by decide +kernel
theorem D_mv_a5a6 : decode_any Wmv_a5a6 = some (.OpImm .ALU_ADD 15 16 0, 4) := by decide +kernel
theorem D_j_cpc : decode_any Wj_cpc = some (.Jal 0 2097116, 4) := by decide +kernel

theorem E_ecall : is_ecall Wecall = true := by decide

/-! ## Lean-only chain helpers -/

/-- Lean-only helper: one `mst_step` out of an `mkst` state, whose
`ms_svc_pending` is `none` by construction, with the landing register file
and pc restated before the run continues. -/
theorem mst_next (segs : List Segment) (regs regs' regs'' : bvmap 5 word)
    (pc pc' pc'' : word) (mem mem' rom : word → Option byte) (ms : machine_state)
    (hs : RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs' pc' mem' rom))
    (hr : regs' = regs'') (hpc : pc' = pc'')
    (h : msteps segs (mkst regs'' pc'' mem' rom) ms) :
    msteps segs (mkst regs pc mem rom) ms := by
  subst hr hpc
  exact msteps.mst_step _ _ _ rfl hs h

/-- Lean-only helper: a displacement from an `at_` address, the offset sum
folded (Rocq's `at_addi` rewrite and `at_fold`). -/
theorem at_step (B : word) (d e d' : Int) (h : d + e = d') : v_addi (at_ B d) e = at_ B d' := by
  rw [at_addi, h]

/-- Lean-only helper: the `if` a linking step leaves on a nonzero link
register collapses to the update. -/
theorem if_link (regs : bvmap 5 word) (r : reg) (v : word) (h : bv_eqb r 0 = false) :
    (if bv_eqb r 0 then regs else regupd regs r v) = regupd regs r v := by
  rw [h]
  rfl

/-! ## Rocq's Section `MuslWrite`: any image, any load address

The fetch facts `F00` … `F90` are the whole per-binary interface: a binary
that loads the blob at `B` supplies them for its own image, and nothing
else. -/

/-- The blob's clobber set: `ra`, `sp` and the argument registers.  Every
callee-saved register is outside it, so a caller keeps its `s*` registers
and its frame pointer across the call (`Hoare.triple_frame`,
`Hoare.frameable_reg`). -/
def musl_clob : regset :=
  fun r => r = 1 ∨ r = 2 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13
           ∨ r = 14 ∨ r = 15 ∨ r = 16 ∨ r = 17

/-- Its write set: the one stack slot the wrapper spills `ra` into. -/
def musl_wset (sp0 : word) : memset :=
  fun x => ∃ i : Int, (0 ≤ i ∧ i < 8) ∧ x = at_ sp0 (-8 + i)

/-- Summary 1: entry to the `ecall`, the pc at which a caller hands the
syscall to `SeqExec.tw_write_ret` or `WallSim.twl_write_rec`.  A triple
cannot cross the `ecall`: the syscall is not an `msteps` step. -/
theorem musl_write_enter (segs : List Segment) (B : word)
    (F00 : fetch_word segs (at_ B 0x00) = some Wsp16m)
    (F04 : fetch_word segs (at_ B 0x04) = some Wmv_a3a2)
    (F08 : fetch_word segs (at_ B 0x08) = some Wli_a6_0)
    (F0c : fetch_word segs (at_ B 0x0c) = some Wmv_a2a1)
    (F10 : fetch_word segs (at_ B 0x10) = some Wli_a5_0)
    (F14 : fetch_word segs (at_ B 0x14) = some Wmv_a1a0)
    (F18 : fetch_word segs (at_ B 0x18) = some Wli_a4_0)
    (F1c : fetch_word segs (at_ B 0x1c) = some Wli_a0_64)
    (F20 : fetch_word segs (at_ B 0x20) = some Wsd_ra8)
    (F24 : fetch_word segs (at_ B 0x24) = some Wjal_cp)
    (F6c : fetch_word segs (at_ B 0x6c) = some Wmv_a7a0)
    (F70 : fetch_word segs (at_ B 0x70) = some Wmv_a0a1)
    (F74 : fetch_word segs (at_ B 0x74) = some Wmv_a1a2)
    (F78 : fetch_word segs (at_ B 0x78) = some Wmv_a2a3)
    (F7c : fetch_word segs (at_ B 0x7c) = some Wmv_a3a4)
    (F80 : fetch_word segs (at_ B 0x80) = some Wmv_a4a5)
    (F84 : fetch_word segs (at_ B 0x84) = some Wmv_a5a6)
    (F90 : fetch_word segs (at_ B 0x90) = some Wj_cpc)
    (k sp0 fd buf len : word) (mem0 : word → Option byte) :
    triple segs musl_clob (musl_wset sp0)
      (fun regs mem _ =>
         mem = mem0
         ∧ getr regs 1 = k ∧ getr regs 2 = sp0
         ∧ getr regs 10 = fd ∧ getr regs 11 = buf ∧ getr regs 12 = len
         ∧ RiscvSemantics.store_ok segs mem0 (at_ sp0 (-8)) 8 = true)
      (at_ B 0x00) (at_ B 0x88)
      (fun regs mem _ =>
         mem = wbytes mem0 (at_ sp0 (-8)) (word_to_le_bytes 8 k)
         ∧ getr regs 1 = at_ B 0x28 ∧ getr regs 2 = at_ sp0 (-16)
         ∧ getr regs 10 = fd ∧ getr regs 11 = buf ∧ getr regs 12 = len
         ∧ getr regs 17 = Z_to_bv 64 64) := by
  apply triple_intro
  rintro regs mem rom ⟨Hmem, Hra, Hsp, H10, H11, H12, Hok⟩
  subst Hmem
  refine ⟨?regs', ?mem', ?chain, ?post, ?ragree, ?magree⟩
  case chain =>
    -- +0x00 addi sp,sp,-16
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 2 2 4080 (at_ sp0 (-16)) F00 (by decide) D_sp16m (by decide)
        (by rw [Hsp]; rfl))
      rfl (at_step B 0x00 4 0x04 (by decide)) ?_
    -- +0x04 mv a3,a2
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 13 12 0 len F04 (by decide) D_mv_a3a2 (by decide)
        (by simp (disch := decide) only [getr_other]; rw [H12]; exact v_addi_0 len))
      rfl (at_step B 0x04 4 0x08 (by decide)) ?_
    -- +0x08 li a6,0
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 16 0 0 (Z_to_bv 64 0) F08 (by decide) D_li_a6_0 (by decide)
        (by simp only [getr_zero]; exact v_addi_0 _))
      rfl (at_step B 0x08 4 0x0c (by decide)) ?_
    -- +0x0c mv a2,a1
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 12 11 0 buf F0c (by decide) D_mv_a2a1 (by decide)
        (by simp (disch := decide) only [getr_other]; rw [H11]; exact v_addi_0 buf))
      rfl (at_step B 0x0c 4 0x10 (by decide)) ?_
    -- +0x10 li a5,0
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 15 0 0 (Z_to_bv 64 0) F10 (by decide) D_li_a5_0 (by decide)
        (by simp only [getr_zero]; exact v_addi_0 _))
      rfl (at_step B 0x10 4 0x14 (by decide)) ?_
    -- +0x14 mv a1,a0
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 11 10 0 fd F14 (by decide) D_mv_a1a0 (by decide)
        (by simp (disch := decide) only [getr_other]; rw [H10]; exact v_addi_0 fd))
      rfl (at_step B 0x14 4 0x18 (by decide)) ?_
    -- +0x18 li a4,0
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 14 0 0 (Z_to_bv 64 0) F18 (by decide) D_li_a4_0 (by decide)
        (by simp only [getr_zero]; exact v_addi_0 _))
      rfl (at_step B 0x18 4 0x1c (by decide)) ?_
    -- +0x1c li a0,64
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 10 0 64 (Z_to_bv 64 64) F1c (by decide) D_li_a0_64 (by decide)
        (by simp only [getr_zero]; exact v_addi_0_64))
      rfl (at_step B 0x1c 4 0x20 (by decide)) ?_
    -- +0x20 sd ra,8(sp)
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_sd_at segs _ _ _ _ _ 2 1 8 (at_ sp0 (-8)) k F20 (by decide) D_sd_ra8
        (by simp (disch := decide) only [getr_same, getr_other]
            exact at_step sp0 (-16) 8 (-8) (by decide))
        (by simp (disch := decide) only [getr_other]; exact Hra)
        Hok)
      rfl (at_step B 0x20 4 0x24 (by decide)) ?_
    -- +0x24 jal ra,__syscall_cp
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_jal_link segs _ _ _ _ _ 1 108 F24 (by decide) D_jal_cp)
      (by rw [if_link _ 1 _ (by decide), at_step B 0x24 4 0x28 (by decide)])
      (at_step B 0x24 (bv_signed (108 : BitVec 21)) 0x90 (by decide)) ?_
    -- +0x90 j __syscall_cp_c
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_jal_x0 segs _ _ _ _ _ 2097116 F90 (by decide) D_j_cpc)
      rfl (at_step B 0x90 (bv_signed (2097116 : BitVec 21)) 0x6c (by decide)) ?_
    -- +0x6c..+0x84: the raw-syscall register shuffle
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 17 10 0 (Z_to_bv 64 64) F6c (by decide) D_mv_a7a0 (by decide)
        (by simp (disch := decide) only [getr_same, getr_other]; exact v_addi_0 _))
      rfl (at_step B 0x6c 4 0x70 (by decide)) ?_
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 10 11 0 fd F70 (by decide) D_mv_a0a1 (by decide)
        (by simp (disch := decide) only [getr_same, getr_other]; exact v_addi_0 _))
      rfl (at_step B 0x70 4 0x74 (by decide)) ?_
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 11 12 0 buf F74 (by decide) D_mv_a1a2 (by decide)
        (by simp (disch := decide) only [getr_same, getr_other]; exact v_addi_0 _))
      rfl (at_step B 0x74 4 0x78 (by decide)) ?_
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 12 13 0 len F78 (by decide) D_mv_a2a3 (by decide)
        (by simp (disch := decide) only [getr_same, getr_other]; exact v_addi_0 _))
      rfl (at_step B 0x78 4 0x7c (by decide)) ?_
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 13 14 0 (Z_to_bv 64 0) F7c (by decide) D_mv_a3a4 (by decide)
        (by simp (disch := decide) only [getr_same, getr_other]; exact v_addi_0 _))
      rfl (at_step B 0x7c 4 0x80 (by decide)) ?_
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 14 15 0 (Z_to_bv 64 0) F80 (by decide) D_mv_a4a5 (by decide)
        (by simp (disch := decide) only [getr_same, getr_other]; exact v_addi_0 _))
      rfl (at_step B 0x80 4 0x84 (by decide)) ?_
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 15 16 0 (Z_to_bv 64 0) F84 (by decide) D_mv_a5a6 (by decide)
        (by simp (disch := decide) only [getr_same, getr_other]; exact v_addi_0 _))
      rfl (at_step B 0x84 4 0x88 (by decide)) ?_
    exact msteps.mst_refl _
  case post =>
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp (disch := decide) only [getr_same, getr_other]
  case ragree =>
    repeat (refine regs_agree_upd _ _ _ _ _ (by unfold musl_clob; decide) ?_)
    exact regs_agree_refl _ _
  case magree =>
    refine mem_agree_wbytes _ _ _ _ _ ?_ (mem_agree_refl _ _)
    intro i hi
    rw [length_N_to_le_bytes] at hi
    obtain ⟨hi0, hi8⟩ := hi
    unfold musl_wset
    exact ⟨i, ⟨hi0, by omega⟩, at_at sp0 (-8) i⟩

def errno_lo : word := Z_to_bv 64 18446744073709547520

theorem not_errno (rv : word) (H : bv_unsigned rv ≤ 18446744073709547520) :
    c_ltu errno_lo rv = false := by
  have he : bv_unsigned errno_lo = 18446744073709547520 := by decide
  rw [c_ltu_ltb, he]
  exact decide_eq_false (by omega)

/-- Summary 2: the post-syscall return path, from the `ret` after the
`ecall` through `__syscall_ret`'s not-taken errno branch to the caller's
return address `k`. -/
theorem musl_write_leave (segs : List Segment) (B : word)
    (F28 : fetch_word segs (at_ B 0x28) = some Wld_ra8)
    (F2c : fetch_word segs (at_ B 0x2c) = some Wsp16p)
    (F30 : fetch_word segs (at_ B 0x30) = some Wj4)
    (F34 : fetch_word segs (at_ B 0x34) = some Wlui_a5)
    (F38 : fetch_word segs (at_ B 0x38) = some Wbltu)
    (F3c : fetch_word segs (at_ B 0x3c) = some Wret)
    (F8c : fetch_word segs (at_ B 0x8c) = some Wret)
    (k sp0 rv : word) (mem1 : word → Option byte)
    (Hk : ret_ok k) (Hr28 : ret_ok (at_ B 0x28)) :
    triple segs musl_clob (musl_wset sp0)
      (fun regs mem _ =>
         mem = mem1
         ∧ getr regs 1 = at_ B 0x28 ∧ getr regs 2 = at_ sp0 (-16)
         ∧ getr regs 10 = rv
         ∧ rdn segs mem1 (at_ sp0 (-8)) 8 = some (word_to_le_bytes 8 k)
         ∧ c_ltu errno_lo rv = false)
      (at_ B 0x8c) k
      (fun regs mem _ =>
         mem = mem1 ∧ getr regs 1 = k ∧ getr regs 2 = sp0 ∧ getr regs 10 = rv) := by
  apply triple_intro
  rintro regs mem rom ⟨Hmem, H1, H2, H10, Hrd, Hlt⟩
  subst Hmem
  refine ⟨?regs', ?mem', ?chain, ?post, ?ragree, ?magree⟩
  case chain =>
    -- +0x8c ret -> +0x28
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_jalr_x0 segs _ _ _ _ _ 1 0 (at_ B 0x28) F8c (by decide) D_ret H1)
      rfl Hr28 ?_
    -- +0x28 ld ra,8(sp)
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_ld segs _ _ _ _ _ 1 2 8 (word_to_le_bytes 8 k) k F28 (by decide) D_ld_ra8
        (by rw [H2, at_step sp0 (-16) (bv_signed (8 : BitVec 12)) (-8) (by decide)]; exact Hrd)
        (bytes_le_to_Z_8 k))
      (if_link _ 1 _ (by decide)) (at_step B 0x28 4 0x2c (by decide)) ?_
    -- +0x2c addi sp,sp,16
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_addi_at segs _ _ _ _ _ 2 2 16 sp0 F2c (by decide) D_sp16p (by decide)
        (by simp (disch := decide) only [getr_other]
            rw [H2, at_step sp0 (-16) (bv_signed (16 : BitVec 12)) 0 (by decide)]
            exact at_0 sp0))
      rfl (at_step B 0x2c 4 0x30 (by decide)) ?_
    -- +0x30 j __syscall_ret
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_jal_x0 segs _ _ _ _ _ 4 F30 (by decide) D_j4)
      rfl (at_step B 0x30 (bv_signed (4 : BitVec 21)) 0x34 (by decide)) ?_
    -- +0x34 lui a5,0xfffff
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_lui_at segs _ _ _ _ _ 15 1048575 errno_lo F34 (by decide) D_lui_a5 (by decide)
        (by decide))
      rfl (at_step B 0x34 4 0x38 (by decide)) ?_
    -- +0x38 bltu a5,a0 NOT taken
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_bltu_ft segs _ _ _ _ _ 15 10 8 F38 (by decide) D_bltu
        (by simp (disch := decide) only [getr_same, getr_other]; rw [H10]; exact Hlt))
      rfl (at_step B 0x38 4 0x3c (by decide)) ?_
    -- +0x3c ret -> the caller
    refine mst_next segs _ _ _ _ _ _ _ _ _ _
      (step_jalr_x0 segs _ _ _ _ _ 1 0 k F3c (by decide) D_ret
        (by simp (disch := decide) only [getr_same, getr_other]))
      rfl Hk ?_
    exact msteps.mst_refl _
  case post =>
    refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp (disch := decide) only [getr_same, getr_other, H10]
  case ragree =>
    repeat (refine regs_agree_upd _ _ _ _ _ (by unfold musl_clob; decide) ?_)
    exact regs_agree_refl _ _
  case magree =>
    exact mem_agree_refl _ _

/-- `write(1, buf, len)` from entry to return, the `ecall` handed to
`SeqExec.tw_write_ret` and the return to the caller's continuation.  The
environment may deliver any nonempty prefix of the buffer, so the
continuation is the delivered-length family: `a0` holds
`len_word (out.take n)` for the chosen `n`, which is never in the errno
window, so `__syscall_ret`'s branch is not taken for any delivery. -/
theorem musl_write_wexit (segs : List Segment) (B : word)
    (F00 : fetch_word segs (at_ B 0x00) = some Wsp16m)
    (F04 : fetch_word segs (at_ B 0x04) = some Wmv_a3a2)
    (F08 : fetch_word segs (at_ B 0x08) = some Wli_a6_0)
    (F0c : fetch_word segs (at_ B 0x0c) = some Wmv_a2a1)
    (F10 : fetch_word segs (at_ B 0x10) = some Wli_a5_0)
    (F14 : fetch_word segs (at_ B 0x14) = some Wmv_a1a0)
    (F18 : fetch_word segs (at_ B 0x18) = some Wli_a4_0)
    (F1c : fetch_word segs (at_ B 0x1c) = some Wli_a0_64)
    (F20 : fetch_word segs (at_ B 0x20) = some Wsd_ra8)
    (F24 : fetch_word segs (at_ B 0x24) = some Wjal_cp)
    (F28 : fetch_word segs (at_ B 0x28) = some Wld_ra8)
    (F2c : fetch_word segs (at_ B 0x2c) = some Wsp16p)
    (F30 : fetch_word segs (at_ B 0x30) = some Wj4)
    (F34 : fetch_word segs (at_ B 0x34) = some Wlui_a5)
    (F38 : fetch_word segs (at_ B 0x38) = some Wbltu)
    (F3c : fetch_word segs (at_ B 0x3c) = some Wret)
    (F6c : fetch_word segs (at_ B 0x6c) = some Wmv_a7a0)
    (F70 : fetch_word segs (at_ B 0x70) = some Wmv_a0a1)
    (F74 : fetch_word segs (at_ B 0x74) = some Wmv_a1a2)
    (F78 : fetch_word segs (at_ B 0x78) = some Wmv_a2a3)
    (F7c : fetch_word segs (at_ B 0x7c) = some Wmv_a3a4)
    (F80 : fetch_word segs (at_ B 0x80) = some Wmv_a4a5)
    (F84 : fetch_word segs (at_ B 0x84) = some Wmv_a5a6)
    (F88 : fetch_word segs (at_ B 0x88) = some Wecall)
    (F8c : fetch_word segs (at_ B 0x8c) = some Wret)
    (F90 : fetch_word segs (at_ B 0x90) = some Wj_cpc)
    (regs : bvmap 5 word) (mem rom : word → Option byte)
    (k sp0 buf len : word) (out : List byte)
    (bufs : List (List byte)) (code : word)
    (Hrom : rom = seg_rom segs)
    (Hk : ret_ok k) (Hr28 : ret_ok (at_ B 0x28))
    (H1 : getr regs 1 = k) (H2 : getr regs 2 = sp0)
    (H10 : getr regs 10 = Z_to_bv 64 1) (H11 : getr regs 11 = buf) (H12 : getr regs 12 = len)
    (Hok : RiscvSemantics.store_ok segs mem (at_ sp0 (-8)) 8 = true)
    (Hnw : bv_unsigned (at_ sp0 (-8)) + 8 ≤ 2 ^ 64)
    (Hlen : bv_unsigned len ≤ 18446744073709547520)
    (Hread : rdn segs (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k))
      buf (word_to_nat len) = some out)
    (Hnb : 1 ≤ out.length)
    (Hcont : ∀ (regs' : bvmap 5 word) (n : Nat), 1 ≤ n → n ≤ out.length →
      getr regs' 1 = k → getr regs' 2 = sp0 →
      getr regs' 10 = len_word (out.take n) →
      to_wexit segs
        (mkst regs' k (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k)) rom)
        bufs code) :
    to_wexit segs (mkst regs (at_ B 0x00) mem rom) (out :: bufs) code := by
  have Hlout := rdn_length segs _ _ _ _ Hread
  have Hlr := u64_range len
  have HoutZ : (out.length : Int) = bv_unsigned len := by
    rw [Hlout]
    rfl
  -- entry -> the ecall
  refine triple_wexit segs musl_clob (musl_wset sp0) _ _ _ _ (out :: bufs) code regs mem rom
    (musl_write_enter segs B F00 F04 F08 F0c F10 F14 F18 F1c F20 F24 F6c F70 F74 F78 F7c F80
      F84 F90 k sp0 (Z_to_bv 64 1) buf len mem)
    ⟨rfl, H1, H2, H10, H11, H12, Hok⟩ ?_
  rintro regs1 mem1' ⟨Hm1, Q1, Q2, Q10, Q11, Q12, Q17⟩
  subst Hm1
  -- the ecall itself
  refine to_wexit.tw_step _ _ _ _ rfl
    (step_ecall segs regs1 (at_ B 0x88) _ rom Wecall F88 E_ecall) ?_
  refine tw_write_ret segs regs1 (at_ B 0x88) _ rom out bufs code ?_ ?_ ?_ Hnb ?_
  · rw [Q17]
    decide
  · rw [← getr_nz regs1 10 (by decide)]
    exact Q10
  · rw [ms_read_bytes_rdn segs]
    · rw [← getr_nz regs1 11 (by decide), ← getr_nz regs1 12 (by decide), Q11, Q12]
      exact Hread
    · exact Hrom
  · -- back from the kernel: __syscall_ret, then the caller
    intro n Hn1 Hn2
    have Hru : bv_unsigned (len_word (out.take n)) = (n : Int) :=
      u_len_word_firstn n out Hn2 (by omega)
    rw [at_step B 0x88 4 0x8c (by decide)]
    refine triple_wexit segs musl_clob (musl_wset sp0) _ _ _ _ bufs code _ _ rom
      (musl_write_leave segs B F28 F2c F30 F34 F38 F3c F8c k sp0 (len_word (out.take n))
        (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k)) Hk Hr28)
      ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ ?_
    · rw [getr_other _ _ _ _ (by decide)]
      exact Q1
    · rw [getr_other _ _ _ _ (by decide)]
      exact Q2
    · rw [getr_same _ _ _ (by decide)]
    · exact rdn_wbytes_hit8 segs mem _ k Hnw
    · exact not_errno _ (by rw [Hru]; omega)
    · rintro regs2 mem2 ⟨Hm2, R1, R2, R10⟩
      subst Hm2
      exact Hcont regs2 n Hn1 Hn2 R1 R2 R10

/-- `write(1, buf, len)` for a caller that wraps the call in a put-style
retry loop: the `ecall` handed to `WallSim`'s write node and, per delivered
length `n`, the return path to the caller's `to_wall_tail` of the remainder
`out.drop n` down to an arbitrary continuation predicate `k`.  Why neither
this lemma nor `musl_write_wexit` is an instance of the other is argued on
the Rocq lemma. -/
theorem musl_write_wall (segs : List Segment) (B : word)
    (F00 : fetch_word segs (at_ B 0x00) = some Wsp16m)
    (F04 : fetch_word segs (at_ B 0x04) = some Wmv_a3a2)
    (F08 : fetch_word segs (at_ B 0x08) = some Wli_a6_0)
    (F0c : fetch_word segs (at_ B 0x0c) = some Wmv_a2a1)
    (F10 : fetch_word segs (at_ B 0x10) = some Wli_a5_0)
    (F14 : fetch_word segs (at_ B 0x14) = some Wmv_a1a0)
    (F18 : fetch_word segs (at_ B 0x18) = some Wli_a4_0)
    (F1c : fetch_word segs (at_ B 0x1c) = some Wli_a0_64)
    (F20 : fetch_word segs (at_ B 0x20) = some Wsd_ra8)
    (F24 : fetch_word segs (at_ B 0x24) = some Wjal_cp)
    (F28 : fetch_word segs (at_ B 0x28) = some Wld_ra8)
    (F2c : fetch_word segs (at_ B 0x2c) = some Wsp16p)
    (F30 : fetch_word segs (at_ B 0x30) = some Wj4)
    (F34 : fetch_word segs (at_ B 0x34) = some Wlui_a5)
    (F38 : fetch_word segs (at_ B 0x38) = some Wbltu)
    (F3c : fetch_word segs (at_ B 0x3c) = some Wret)
    (F6c : fetch_word segs (at_ B 0x6c) = some Wmv_a7a0)
    (F70 : fetch_word segs (at_ B 0x70) = some Wmv_a0a1)
    (F74 : fetch_word segs (at_ B 0x74) = some Wmv_a1a2)
    (F78 : fetch_word segs (at_ B 0x78) = some Wmv_a2a3)
    (F7c : fetch_word segs (at_ B 0x7c) = some Wmv_a3a4)
    (F80 : fetch_word segs (at_ B 0x80) = some Wmv_a4a5)
    (F84 : fetch_word segs (at_ B 0x84) = some Wmv_a5a6)
    (F88 : fetch_word segs (at_ B 0x88) = some Wecall)
    (F8c : fetch_word segs (at_ B 0x8c) = some Wret)
    (F90 : fetch_word segs (at_ B 0x90) = some Wj_cpc)
    (k : machine_state → Prop)
    (regs : bvmap 5 word) (mem rom : word → Option byte)
    (kra sp0 buf len : word) (out : List byte)
    (Hrom : rom = seg_rom segs)
    (Hk : ret_ok kra) (Hr28 : ret_ok (at_ B 0x28))
    (H1 : getr regs 1 = kra) (H2 : getr regs 2 = sp0)
    (H10 : getr regs 10 = Z_to_bv 64 1) (H11 : getr regs 11 = buf) (H12 : getr regs 12 = len)
    (Hok : RiscvSemantics.store_ok segs mem (at_ sp0 (-8)) 8 = true)
    (Hnw : bv_unsigned (at_ sp0 (-8)) + 8 ≤ 2 ^ 64)
    (Hlen : bv_unsigned len ≤ 18446744073709547520)
    (Hread : rdn segs (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra))
      buf (word_to_nat len) = some out)
    (Hnb : 1 ≤ out.length)
    (Hcont : ∀ (regs' : bvmap 5 word) (n : Nat), 1 ≤ n → n ≤ out.length →
      regs_agree musl_clob regs regs' →
      getr regs' 1 = kra → getr regs' 2 = sp0 →
      getr regs' 10 = len_word (out.take n) →
      to_wall_tail segs (Z_to_bv 64 1)
        (mkst regs' kra (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra)) rom)
        (out.drop n) k) :
    to_wall_tail segs (Z_to_bv 64 1) (mkst regs (at_ B 0x00) mem rom) out k := by
  have Hlout := rdn_length segs _ _ _ _ Hread
  have Hlr := u64_range len
  have HoutZ : (out.length : Int) = bv_unsigned len := by
    rw [Hlout]
    rfl
  -- entry -> the ecall
  obtain ⟨regs1, mem1', Hst1, ⟨Hm1, Q1, Q2, Q10, Q11, Q12, Q17⟩, Hag1, -⟩ :=
    musl_write_enter segs B F00 F04 F08 F0c F10 F14 F18 F1c F20 F24 F6c F70 F74 F78 F7c F80
      F84 F90 kra sp0 (Z_to_bv 64 1) buf len mem regs mem rom
      ⟨rfl, H1, H2, H10, H11, H12, Hok⟩
  subst Hm1
  refine msteps_to_wall_tail segs _ _ _ _ _ Hst1 ?_
  -- the ecall itself
  refine to_wall_tail.twt_step _ _ _ _ rfl
    (step_ecall segs regs1 (at_ B 0x88) _ rom Wecall F88 E_ecall) ?_
  refine to_wall_tail.twt_more _ _ _ Hnb ?_
  refine twl_write_rec segs (Z_to_bv 64 1) k out regs1 (at_ B 0x88) _ rom ?_ ?_ ?_ Hnb ?_
  · rw [Q17]
    decide
  · rw [← getr_nz regs1 10 (by decide)]
    exact Q10
  · rw [ms_read_bytes_rdn segs]
    · rw [← getr_nz regs1 11 (by decide), ← getr_nz regs1 12 (by decide), Q11, Q12]
      exact Hread
    · exact Hrom
  · -- back from the kernel: __syscall_ret, then the caller's put loop
    intro n Hn1 Hn2
    have Hru : bv_unsigned (len_word (out.take n)) = (n : Int) :=
      u_len_word_firstn n out Hn2 (by omega)
    rw [at_step B 0x88 4 0x8c (by decide)]
    obtain ⟨regs2, mem2, Hst2, ⟨Hm2, R1, R2, R10⟩, Hag2, -⟩ :=
      musl_write_leave segs B F28 F2c F30 F34 F38 F3c F8c kra sp0 (len_word (out.take n))
        (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra)) Hk Hr28
        (regupd regs1 10 (len_word (out.take n)))
        (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra)) rom
        ⟨rfl,
         by rw [getr_other _ _ _ _ (by decide)]; exact Q1,
         by rw [getr_other _ _ _ _ (by decide)]; exact Q2,
         by rw [getr_same _ _ _ (by decide)],
         rdn_wbytes_hit8 segs mem _ kra Hnw,
         not_errno _ (by rw [Hru]; omega)⟩
    subst Hm2
    refine msteps_to_wall_tail segs _ _ _ _ _ Hst2 ?_
    refine Hcont regs2 n Hn1 Hn2 ?_ R1 R2 R10
    refine regs_agree_trans _ _ _ _ Hag1 (regs_agree_trans _ _ _ _ ?_ Hag2)
    exact regs_agree_upd _ _ _ _ _ (by unfold musl_clob; decide) (regs_agree_refl _ _)

/-- The frame rule at this summary's footprints: a register outside
`musl_clob` and a buffer disjoint from the spilled stack slot survive the
whole call, the syscall included, without the summaries' postconditions
naming them. -/
theorem musl_write_frame (segs : List Segment) (sp0 : word) (r : reg) (v a : word) (n : Nat)
    (bs : List byte) (Hr : ¬ musl_clob r)
    (Ha : ∀ i : Int, 0 ≤ i ∧ i < (n : Int) →
      ¬ musl_wset sp0 (Z_to_bv 64 (bv_unsigned a + i))) :
    frameable musl_clob (musl_wset sp0)
      (fun regs mem _ => getr regs r = v ∧ rdn segs mem a n = some bs) :=
  frameable_and _ _ _ _ (frameable_reg _ _ r v Hr) (frameable_rdn segs _ _ a n bs Ha)

end LinuxProcessSemantics.Common.MuslCall
