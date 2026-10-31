import LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_defs
import LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_hoare

/-! rocq-baseline: 8bef2933e7063c3b77d628343969f2352008c3ca -/

/-! Mirrors `theories/Examples/cat1024_ns/cat1024_ns_target.v` at the
baseline above; see that Rocq file for the argument. Rocq section parameters
are explicit, `Z` becomes `Int`, `nat` becomes `Nat`, and `firstn`/`skipn`
become `List.take`/`List.drop`. The Rocq Ltac `step_intro`, `stepi`, `stepiv`,
`stepj`, `stepjr`, `step_simpl`, and `norm_pc` are replaced by `cat_step`
and explicit instruction lemmas with conversion. `getr_resolve`,
`regupd_resolve`, and `reg_neq_tac` are replaced by `cat_regs` and `decide`.
`bveq`, `sp_norm`, `imm_norm`, `u_norm`, and `solve_store_ok` are replaced
by explicit value and writable-stack lemmas below.
-/

namespace LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_target

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_code
open LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_defs

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

local macro "cat_regs" : tactic =>
  `(tactic| simp (disch := decide) only [getr_nz, getr_zero, regupd_same, regupd_other])

local macro "cat_step " h:term : tactic =>
  `(tactic| first
    | refine to_rd.trd_step _ _ rfl $h ?_
    | refine to_wr.twr_step _ _ rfl $h ?_
    | refine to_wall_tail.twt_step _ _ _ _ rfl $h ?_
    | refine to_exit.te_step _ _ rfl $h ?_
    | refine LinuxProcessSemantics.Common.CatSim.msteps.mst_step _ _ _ rfl $h ?_)

def tgt_buf : word := 0x1002208

theorem u_tgt_buf : bv_unsigned tgt_buf = 0x1002208 := rfl

def tgt_LH (ms : machine_state) : Prop :=
  ∃ regs mem, ms = mkst regs 0x10011b0 mem (seg_rom target_segs) ∧
    reg_get regs 1 = (0x10011a0 : word) ∧ reg_get regs 13 = tgt_buf

theorem tgt_put_wall (fuel : Nat) (rest : List byte) (p : word) (n : Nat)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (hfuel : rest.length ≤ fuel) (hn1 : 1 ≤ n) (hn2 : n ≤ rest.length)
    (hlen : (rest.length : Int) ≤ 1024)
    (hplo : 0x1002208 ≤ bv_unsigned p)
    (hphi : bv_unsigned p + (rest.length : Int) ≤ 0x1002608)
    (h10 : reg_get regs 10 = len_word (rest.take n))
    (h11 : reg_get regs 11 = p) (h12 : reg_get regs 12 = len_word rest)
    (h1 : reg_get regs 1 = (0x10011a0 : word)) (h13 : reg_get regs 13 = tgt_buf)
    (hread : rdn target_segs mem p rest.length = some rest) :
    to_wall_tail target_segs (Z_to_bv 64 1)
      (mkst regs 0x10011e4 mem (seg_rom target_segs))
      (rest.drop n) (lh_next target_segs tgt_LH) := by
  induction fuel generalizing rest p n regs with
  | zero => omega
  | succ fuel ih =>
    have hu := u_len_word_firstn n rest hn2 (by omega)
    have hdlen : ((rest.drop n).length : Int) < 2 ^ 64 := by
      rw [List.length_drop]; omega
    have hdu := u_len_word (rest.drop n) hdlen
    cat_step (step_bge_ft target_segs _ _ _ _ _ _ _ _ TF_10011e4 (by decide) TD_10011e4
      (by cat_regs; rw [h10]; exact c_lts_0_pos _ (by omega) (by omega)))
    cat_step (step_add_at target_segs _ _ _ _ _ _ _ _
      (Z_to_bv 64 (bv_unsigned p + (n : Int))) TF_10011e8 (by decide) TD_10011e8
      (by decide) (by cat_regs; rw [h11, h10]; exact v_add_len_firstn_Z p n rest hn2 (by omega)))
    cat_step (step_sub_at target_segs _ _ _ _ _ _ _ _ (len_word (rest.drop n))
      TF_10011ec (by decide) TD_10011ec (by decide)
      (by cat_regs; rw [h12, h10]; exact v_sub_len_firstn n rest hn2 (by omega)))
    by_cases heq : n = rest.length
    · have hempty : rest.drop n = [] := by rw [heq, List.drop_length]
      rw [hempty]
      apply to_wall_tail.twt_done
      refine ⟨mkst (regupd (regupd regs 11 (Z_to_bv 64 (bv_unsigned p + (n : Int))))
        12 (len_word ([] : List byte))) 0x10011b0 mem (seg_rom target_segs), ?_, ?_⟩
      · refine LinuxProcessSemantics.Common.CatSim.msteps.mst_step _ _ _ rfl
          (step_beq_tk target_segs _ _ _ _ _ _ _ _ TF_10011f0 (by decide) TD_10011f0
            (by cat_regs; exact c_eq_0_true)) ?_
        exact LinuxProcessSemantics.Common.CatSim.msteps.mst_refl _
      · refine ⟨_, _, rfl, ?_, ?_⟩
        · cat_regs; exact h1
        · cat_regs; exact h13
    · have hnonempty : 1 ≤ (rest.drop n).length := by rw [List.length_drop]; omega
      have hsk := rdn_skipn target_segs mem rest.length p rest n hread hn2
      rw [word_add_nat_Z p n (by omega), ← List.length_drop] at hsk
      cat_step (step_beq_ft target_segs _ _ _ _ _ _ _ _ TF_10011f0 (by decide) TD_10011f0
        (by cat_regs; exact c_eq_0_false _ (by rw [hdu]; omega)))
      cat_step (step_jal_x0 target_segs _ _ _ _ _ _ TF_10011f4 (by decide) TD_10011f4)
      cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 64)
        TF_10011d8 (by decide) TD_10011d8 (by decide) (by cat_regs; rfl))
      cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
        TF_10011dc (by decide) TD_10011dc (by decide) (by cat_regs; rfl))
      cat_step (step_ecall target_segs _ _ _ _ _ TF_10011e0 (by decide))
      apply to_wall_tail.twt_more _ _ _ hnonempty
      apply twl_write_rec
      · cat_regs; rfl
      · cat_regs
      · cat_regs
        rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
        change rdn target_segs mem (Z_to_bv 64 (bv_unsigned p + (n : Int)))
          (word_to_nat (len_word (rest.drop n))) = _
        have hw : word_to_nat (len_word (rest.drop n)) = (rest.drop n).length := by
          change (word_to_nat (len_word (rest.drop n)) : Int) =
            ((rest.drop n).length : Int) at hdu
          omega
        rw [hw]; exact hsk
      · exact hnonempty
      · intro m hm1 hm2
        apply ih (rest.drop n) (Z_to_bv 64 (bv_unsigned p + (n : Int))) m
        · rw [List.length_drop]; omega
        · exact hm1
        · exact hm2
        · rw [List.length_drop]; omega
        · rw [u_Z2bv _ (by omega) (by omega)]; omega
        · rw [u_Z2bv _ (by omega) (by omega), List.length_drop]; omega
        · cat_regs
        · cat_regs
        · cat_regs
        · cat_regs; exact h1
        · cat_regs; exact h13
        · exact hsk

theorem tgt_LH_to_rd (ms : machine_state) (hlh : tgt_LH ms) :
    to_rd target_segs tgt_LH (Z_to_bv 64 1024) ms := by
  obtain ⟨regs, mem, rfl, h1, h13⟩ := hlh
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 63)
    TF_10011b0 (by decide) TD_10011b0 (by decide) (by cat_regs; rfl))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1024)
    TF_10011b4 (by decide) TD_10011b4 (by decide) (by cat_regs; rfl))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0)
    TF_10011b8 (by decide) TD_10011b8 (by decide) (by cat_regs; rfl))
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ tgt_buf
    TF_10011bc (by decide) TD_10011bc (by decide)
    (by cat_regs; rw [h13]; exact v_addi_0 _))
  cat_step (step_ecall target_segs _ _ _ _ _ TF_10011c0 (by decide))
  apply trd_here_rec (buf := tgt_buf)
  · cat_regs; rfl
  · cat_regs
  · cat_regs
  · cat_regs
  · exact target_buf_wseg
  · decide
  · cat_step (step_beq_tk target_segs _ _ _ _ _ _ _ _ TF_10011c4 (by decide) TD_10011c4
      (by cat_regs; exact c_eq_0_true))
    cat_step (step_jalr_x0 target_segs _ _ _ _ _ _ _ (0x10011a0 : word)
      TF_10011fc (by decide) TD_10011fc (by cat_regs; exact h1))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 93)
      TF_10011a0 (by decide) TD_10011a0 (by decide) (by cat_regs; rfl))
    cat_step (step_ecall target_segs _ _ _ _ _ TF_10011a4 (by decide))
    apply te_here_rec0
    · cat_regs; rfl
    · cat_regs
  · intro bs hlo hhi
    have hu := u_len_word bs (by omega)
    have hread := rdn_write_to_mem target_segs bs mem tgt_buf (by rw [u_tgt_buf]; omega)
    cat_step (step_beq_ft target_segs _ _ _ _ _ _ _ _ TF_10011c4 (by decide) TD_10011c4
      (by cat_regs; exact c_eq_0_false _ (by rw [hu]; omega)))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (len_word bs)
      TF_10011c8 (by decide) TD_10011c8 (by decide) (by cat_regs; exact v_addi_0 _))
    cat_step (step_blt_ft target_segs _ _ _ _ _ _ _ _ TF_10011cc (by decide) TD_10011cc
      (by cat_regs; exact c_lts_pos_0 _ (by rw [hu]; omega)))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ tgt_buf
      TF_10011d0 (by decide) TD_10011d0 (by decide) (by cat_regs; rw [h13]; exact v_addi_0 _))
    cat_step (step_beq_ft target_segs _ _ _ _ _ _ _ _ TF_10011d4 (by decide) TD_10011d4
      (by cat_regs; exact c_eq_0_false _ (by rw [hu]; omega)))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 64)
      TF_10011d8 (by decide) TD_10011d8 (by decide) (by cat_regs; rfl))
    cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1)
      TF_10011dc (by decide) TD_10011dc (by decide) (by cat_regs; rfl))
    cat_step (step_ecall target_segs _ _ _ _ _ TF_10011e0 (by decide))
    apply twr_here_rec
    · cat_regs; rfl
    · cat_regs
    · cat_regs
      rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
      have hw : word_to_nat (len_word bs) = bs.length := by
        change (word_to_nat (len_word bs) : Int) = (bs.length : Int) at hu
        omega
      change rdn target_segs (write_to_mem mem tgt_buf bs) tgt_buf
        (word_to_nat (len_word bs)) = _
      rw [hw]; exact hread
    · omega
    · intro n hn1 hn2
      apply tgt_put_wall bs.length bs tgt_buf n
      · exact Nat.le_refl _
      · exact hn1
      · exact hn2
      · exact hhi
      · rw [u_tgt_buf]; omega
      · rw [u_tgt_buf]; omega
      · cat_regs
      · cat_regs
      · cat_regs
      · cat_regs; exact h1
      · cat_regs; exact h13
      · exact hread

theorem asp_lo_num (asp : word) (hsp_lo : sp_window_lo ≤ bv_unsigned asp) :
    0x7fff80000000 ≤ bv_unsigned asp := hsp_lo

theorem asp_hi_num (asp : word) (hsp_hi : bv_unsigned asp ≤ sp_window_hi) :
    bv_unsigned asp ≤ 0x800000000000 := hsp_hi

theorem tgt_init_to_rd (av ev : List (List byte)) (asp : word) (arnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned asp)
    (hsp_hi : bv_unsigned asp ≤ sp_window_hi) (uid hw : word) :
    to_rd target_segs tgt_LH (Z_to_bv 64 1024)
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd av ev uid hw) := by
  have hlo := asp_lo_num asp hsp_lo
  have hhi := asp_hi_num asp hsp_hi
  have hu16 : bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 16)) = bv_unsigned asp - 16 :=
    u_Z2bv _ (by omega) (by omega)
  have hu8 : bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 8)) = bv_unsigned asp - 8 :=
    u_Z2bv _ (by omega) (by omega)
  rw [init_mkst]
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned asp - 16))
    TF_1001190 (by decide) TD_1001190 (by decide)
    (by cat_regs; exact v_addi_m16 asp (by omega)))
  cat_step (step_sd_at target_segs _ _ _ _ _ _ _ _
    (Z_to_bv 64 (bv_unsigned asp - 8)) (Z_to_bv 64 0)
    TF_1001194 (by decide) TD_1001194
    (by cat_regs
        change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 16)) + 8) = _
        rw [hu16]
        congr 1 <;> omega)
    (by cat_regs; rfl)
    (by apply store_ok_wrap_window
        · rw [hu8]; unfold stack_max_size; omega
        · rw [hu8]; omega))
  cat_step (step_auipc target_segs _ _ _ _ _ _ _ TF_1001198 (by decide) TD_1001198)
  simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_jalr_link target_segs _ _ _ _ _ _ _ _ (0x1001198 : word)
    TF_100119c (by decide) TD_100119c (by decide) (by cat_regs; rfl))
  cat_step (step_lui target_segs _ _ _ _ _ _ _ TF_10011a8 (by decide) TD_10011a8)
  simp only [show bv_eqb (13 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  cat_step (step_addi_at target_segs _ _ _ _ _ _ _ _ tgt_buf
    TF_10011ac (by decide) TD_10011ac (by decide) (by cat_regs; rfl))
  apply tgt_LH_to_rd
  refine ⟨_, _, rfl, ?_, ?_⟩
  · cat_regs; rfl
  · cat_regs

end LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_target
