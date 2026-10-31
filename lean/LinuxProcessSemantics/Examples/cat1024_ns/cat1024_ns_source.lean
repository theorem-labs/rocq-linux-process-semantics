import LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_defs
import LinuxProcessSemantics.Common.SymTac

/-! rocq-baseline: 8bef2933e7063c3b77d628343969f2352008c3ca -/

/-! Mirrors `theories/Examples/cat1024_ns/cat1024_ns_source.v` at the
baseline above; see that Rocq file for the argument. Rocq section parameters
become explicit arguments, `Z` becomes `Int`, and `nat` becomes `Nat`.
`firstn` and `skipn` become `List.take` and `List.drop`.
The Rocq Ltac `sret`, `addr_tac`, `ssd`, `sld`, `bltu_ret_ft`, `step_intro`,
`stepi`, `stepiv`, `stepj`, `stepjr`, `step_simpl`, `norm_pc`, `getr_resolve`,
`regupd_resolve`, `reg_neq_tac`, `bveq`, `sp_norm`, `imm_norm`, `u_norm`,
`solve_store_ok`, `solve_store_ok_inv`, `solve_mem_grows`, `sym_block`,
`sym_addr_norm`, `sym_regs`, and `sym_close` are replaced by local tactics
and explicit applications of the existing instruction and memory lemmas.
-/

namespace LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_source

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
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_code
open LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_defs

set_option maxRecDepth 65536
set_option maxHeartbeats 100000

local macro "cat_regs" : tactic =>
  `(tactic| simp (disch := decide) only [getr_nz, getr_zero, regupd_same, regupd_other])

local macro "cat_grows" : tactic =>
  `(tactic| (repeat first
    | assumption
    | exact mem_grows_refl _
    | refine mem_grows_trans _ _ _ ?_ (wbytes_grows _ _ _)))

local macro "cat_u" : tactic =>
  `(tactic| simp (disch := omega) only [length_N_to_le_bytes, List.length_drop, u_Z2bv])

def src_buf : word := 0x13008

theorem u_src_buf : bv_unsigned src_buf = 0x13008 := rfl

theorem rsp_lo_num (rsp : word) (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) :
    0x7fff80000000 ≤ bv_unsigned rsp := hsp_lo

theorem rsp_hi_num (rsp : word) (hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    bv_unsigned rsp ≤ 0x800000000000 := hsp_hi

def argcN (av : List (List byte)) : word := len_word av

def wmem (av ev : List (List byte)) (rsp : word) (rrnd : EntryDraw) (uid hw : word) :
    word → Option byte := wrap_mem source_phdrs rsp av ev uid hw rrnd

def rrom : word → Option byte := seg_rom source_segs

theorem u_argcN (av : List (List byte)) (hva : valid_argv av) :
    bv_unsigned (argcN av) = (av.length : Int) := by
  have h := valid_argv_len av hva
  exact u_len_word av (by omega)

theorem source_bsb_nw (av ev : List (List byte)) (hva : valid_argv av)
    (hve : valid_envp ev) (rsp : word) (rrnd : EntryDraw)
    (hsp_hi : bv_unsigned rsp ≤ sp_window_hi) (uid hw : word) :
    bv_unsigned rsp + ((build_stack_bytes source_phdrs rsp av ev uid hw rrnd).length : Int)
      < 2 ^ 64 := by
  have hb := bsb_bound source_phdrs rsp av ev uid hw rrnd hva hve
  have hh := rsp_hi_num rsp hsp_hi
  omega

def envp_ptr (av : List (List byte)) (rsp : word) : word :=
  Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * (av.length : Int) + 8)

theorem envp_ptr_eq (av : List (List byte)) (hva : valid_argv av) (rsp : word)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp)
    (hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    v_addi (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN av) 3)) 8 =
      envp_ptr av rsp := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hl := valid_argv_len av hva
  have hu := u_argcN av hva
  have hs := v_slli_3 (argcN av) (by omega)
  have hp := u_Z2bv (bv_unsigned rsp + 8) (by omega) (by omega)
  have ha := v_add_small (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN av) 3)
    (by rw [hp, hs, hu]; omega)
  unfold v_addi envp_ptr
  rw [ha, hp, hs, hu]

def fmem (av ev : List (List byte)) (rsp : word) (rrnd : EntryDraw) (uid hw : word) :
    word → Option byte :=
  wbytes (wbytes (wbytes (wmem av ev rsp rrnd uid hw)
    0x13000 (word_to_le_bytes 8 (envp_ptr av rsp)))
    (Z_to_bv 64 (bv_unsigned rsp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 8)) (word_to_le_bytes 8 (0x110a4 : word))

def mem_agree (av ev : List (List byte)) (rsp : word) (rrnd : EntryDraw) (uid hw : word)
    (mem : word → Option byte) : Prop :=
  ∀ (a : word) (n : Nat), bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
    (bv_unsigned rsp - 16 ≤ bv_unsigned a ∨
      (bv_unsigned a + (n : Int) ≤ bv_unsigned rsp - 40 ∧
        (0x13408 ≤ bv_unsigned a ∨ bv_unsigned a + (n : Int) ≤ 0x13008))) →
    rdn source_segs mem a n = rdn source_segs (fmem av ev rsp rrnd uid hw) a n

def mem_ok (av ev : List (List byte)) (rsp : word) (rrnd : EntryDraw) (uid hw : word)
    (mem : word → Option byte) : Prop :=
  mem_grows (wmem av ev rsp rrnd uid hw) mem ∧ mem_agree av ev rsp rrnd uid hw mem

theorem mem_ok_grows (av ev : List (List byte)) (rsp : word) (rrnd : EntryDraw)
    (uid hw : word) (mem : word → Option byte) (hm : mem_ok av ev rsp rrnd uid hw mem) :
    mem_grows (wmem av ev rsp rrnd uid hw) mem := hm.1

theorem fmem_ok (av ev : List (List byte)) (rsp : word) (rrnd : EntryDraw) (uid hw : word) :
    mem_ok av ev rsp rrnd uid hw (fmem av ev rsp rrnd uid hw) := by
  constructor
  · unfold fmem; cat_grows
  · intro a n _ _; rfl

theorem mem_ok_scratch8 (av ev : List (List byte)) (rsp : word) (rrnd : EntryDraw)
    (hsp_hi : bv_unsigned rsp ≤ sp_window_hi) (uid hw : word)
    (mem : word → Option byte) (a v : word)
    (hm : mem_ok av ev rsp rrnd uid hw mem)
    (hlo : bv_unsigned rsp - 40 ≤ bv_unsigned a)
    (hhi : bv_unsigned a + 8 ≤ bv_unsigned rsp - 16) :
    mem_ok av ev rsp rrnd uid hw (wbytes mem a (word_to_le_bytes 8 v)) := by
  obtain ⟨hg, hm⟩ := hm
  have hh := rsp_hi_num rsp hsp_hi
  constructor
  · cat_grows
  · intro a' n hnw hd
    rcases hd with hd | ⟨hd1, hd2⟩
    · rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by cat_u; omega) hnw]
      exact hm a' n hnw (Or.inl hd)
    · rw [rdn_wbytes_below _ _ _ _ _ _ (by omega) (by cat_u; omega)]
      exact hm a' n hnw (Or.inr ⟨hd1, hd2⟩)

theorem mem_ok_buf (av ev : List (List byte)) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (uid hw : word)
    (mem : word → Option byte) (bs : List byte)
    (hm : mem_ok av ev rsp rrnd uid hw mem) (hlen : (bs.length : Int) ≤ 1024) :
    mem_ok av ev rsp rrnd uid hw (write_to_mem mem src_buf bs) := by
  obtain ⟨hg, hm⟩ := hm
  have hl := rsp_lo_num rsp hsp_lo
  constructor
  · rw [write_to_mem_wbytes]; cat_grows
  · intro a n hnw hd
    rw [rdn_wtm_out _ _ _ _ _ _ hnw (by rw [u_src_buf]; omega) (by
      rw [u_src_buf]
      rcases hd with hd | ⟨_, hd | hd⟩
      · left; omega
      · left; omega
      · right; exact hd)]
    exact hm a n hnw hd

theorem read_ra_slot_m (av ev : List (List byte)) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp)
    (hsp_hi : bv_unsigned rsp ≤ sp_window_hi) (uid hw : word)
    (mem : word → Option byte) (hm : mem_ok av ev rsp rrnd uid hw mem) :
    rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x110a4 : word)) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  rw [hm.2 _ _ (by cat_u; omega) (Or.inl (by cat_u; omega))]
  unfold fmem
  exact rdn_wbytes_hit8 _ _ _ _ (by cat_u; omega)

theorem read_s0_slot_m (av ev : List (List byte)) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp)
    (hsp_hi : bv_unsigned rsp ≤ sp_window_hi) (uid hw : word)
    (mem : word → Option byte) (hm : mem_ok av ev rsp rrnd uid hw mem) :
    rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 16)) 8 =
      some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  rw [hm.2 _ _ (by cat_u; omega) (Or.inl (by cat_u; omega))]
  unfold fmem
  rw [rdn_wbytes_below _ _ _ _ _ _ (by cat_u; omega) (by cat_u; omega)]
  exact rdn_wbytes_hit8 _ _ _ _ (by cat_u; omega)

def src_LH (av ev : List (List byte)) (rsp : word) (rrnd : EntryDraw) (uid hw : word)
    (ms : machine_state) : Prop :=
  ∃ regs mem, ms = mkst regs 0x11010 mem rrom ∧
    reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 32) ∧
    reg_get regs 3 = (0x13800 : word) ∧ reg_get regs 8 = src_buf ∧
    mem_ok av ev rsp rrnd uid hw mem

def src_pins : List (reg × expr) :=
  [(2, EVar 32), (3, ELit 0x13800), (8, ELit 0x13008)]

private theorem source_stack_store (av ev : List (List byte)) (rsp : word)
    (rrnd : EntryDraw) (uid hw : word) (mem : word → Option byte) (a : word)
    (hg : mem_grows (wmem av ev rsp rrnd uid hw) mem)
    (hlo : bv_unsigned rsp - stack_max_size ≤ bv_unsigned a)
    (hhi : bv_unsigned a + 8 ≤ bv_unsigned rsp) :
    store_ok source_segs mem a 8 = true :=
  store_ok_mono source_segs 8 _ mem a hg
    (store_ok_wrap_window source_segs source_phdrs rsp av ev a 8 uid hw rrnd hlo hhi)

theorem src_put_wall (av ev : List (List byte)) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp)
    (hsp_hi : bv_unsigned rsp ≤ sp_window_hi) (uid hw : word)
    (fuel : Nat) (bs : List byte) (p : word) (n : Nat)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (hfuel : bs.length ≤ fuel) (hn1 : 1 ≤ n) (hn2 : n ≤ bs.length)
    (hlen : (bs.length : Int) ≤ 1024)
    (hplo : 0x13008 ≤ bv_unsigned p)
    (hphi : bv_unsigned p + (bs.length : Int) ≤ 0x13408)
    (h10 : reg_get regs 10 = len_word (bs.take n))
    (h1 : reg_get regs 1 = (0x1112c : word))
    (h2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    (h3 : reg_get regs 3 = (0x13800 : word)) (h8 : reg_get regs 8 = src_buf)
    (hm : mem_ok av ev rsp rrnd uid hw mem)
    (hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 40)) 8 =
      some (word_to_le_bytes 8 (0x11040 : word)))
    (hptr : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 32)) 8 =
      some (word_to_le_bytes 8 p))
    (hcnt : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 24)) 8 =
      some (word_to_le_bytes 8 (len_word bs)))
    (hread : rdn source_segs mem p bs.length = some bs) :
    to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs 0x11190 mem rrom)
      (bs.drop n) (lh_next source_segs (src_LH av ev rsp rrnd uid hw)) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  induction fuel generalizing bs p n regs mem with
  | zero => omega
  | succ fuel ih =>
    have hu := u_len_word_firstn n bs hn2 (by omega)
    have hdu := u_len_word (bs.drop n) (by rw [List.length_drop]; omega)
    refine to_wall_tail.twt_step _ _ _ _ rfl (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x1112c : word) SF_11190 (by decide) SD_11190 (by cat_regs; exact h1)) ?_
    refine to_wall_tail.twt_step _ _ _ _ rfl (step_ld source_segs _ _ _ _ _ _ _ _ (word_to_le_bytes 8 ((0x11040 : word))) ((0x11040 : word)) SF_1112c (by decide) SD_1112c (by
      cat_regs
      change rdn source_segs mem (v_addi (reg_get regs 2) 8) 8 = _
      rw [h2, v_addi_lit]
      have ha : bv_unsigned rsp - 48 + 8 = bv_unsigned rsp - 40 := by omega
      rw [ha]; exact hra) (bytes_le_to_Z_8 _)) ?_
    simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 32)) SF_11130 (by decide) SD_11130 (by decide) (by cat_regs; rw [h2]; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 48)) 16 = _; rw [v_addi_lit]; congr 1 <;> omega)) ?_
    refine to_wall_tail.twt_step _ _ _ _ rfl (step_jal_x0 source_segs _ _ _ _ _ _  SF_11134 (by decide) SD_11134) ?_
    refine to_wall_tail.twt_step _ _ _ _ rfl (step_lui_at source_segs _ _ _ _ _ _ _ (Z_to_bv 64 (-4096)) SF_11138 (by decide) SD_11138 (by decide) (by rfl)) ?_
    refine to_wall_tail.twt_step _ _ _ _ rfl (step_bltu_ft source_segs _ _ _ _ _ _ _ _  SF_1113c (by decide) SD_1113c (by cat_regs; rw [h10, c_ltu_ltb, hu]; change decide (18446744073709547520 < (n : Int)) = false; exact decide_eq_false (by omega))) ?_
    refine to_wall_tail.twt_step _ _ _ _ rfl (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x11040 : word) SF_11140 (by decide) SD_11140 (by cat_regs <;> rfl)) ?_
    refine to_wall_tail.twt_step _ _ _ _ rfl (step_bge_ft source_segs _ _ _ _ _ _ _ _  SF_11040 (by decide) SD_11040 (by cat_regs; rw [h10]; exact c_lts_0_pos _ (by omega) (by omega))) ?_
    refine to_wall_tail.twt_step _ _ _ _ rfl (step_ld source_segs _ _ _ _ _ _ _ _ (word_to_le_bytes 8 (len_word bs)) (len_word bs) SF_11044 (by decide) SD_11044 (by
      cat_regs
      change rdn source_segs mem (v_addi (Z_to_bv 64 (bv_unsigned rsp - 32)) 8) 8 = _
      rw [v_addi_lit]
      have ha : bv_unsigned rsp - 32 + 8 = bv_unsigned rsp - 24 := by omega
      rw [ha]; exact hcnt) (bytes_le_to_Z_8 _)) ?_
    simp only [show bv_eqb (12 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine to_wall_tail.twt_step _ _ _ _ rfl (step_ld source_segs _ _ _ _ _ _ _ _ (word_to_le_bytes 8 (p)) (p) SF_11048 (by decide) SD_11048 (by cat_regs; change rdn source_segs mem (v_addi (Z_to_bv 64 (bv_unsigned rsp - 32)) 0) 8 = _; rw [v_addi_0]; exact hptr) (bytes_le_to_Z_8 _)) ?_
    simp only [show bv_eqb (11 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine to_wall_tail.twt_step _ _ _ _ rfl (step_sub_at source_segs _ _ _ _ _ _ _ _ (len_word (bs.drop n)) SF_1104c (by decide) SD_1104c (by decide) (by cat_regs; rw [h10]; exact v_sub_len_firstn n bs hn2 (by omega))) ?_
    refine to_wall_tail.twt_step _ _ _ _ rfl (step_add_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned p + (n : Int))) SF_11050 (by decide) SD_11050 (by decide) (by cat_regs; rw [h10]; exact v_add_len_firstn_Z p n bs hn2 (by omega))) ?_
    by_cases heq : n = bs.length
    · have hempty : bs.drop n = [] := by rw [heq, List.drop_length]
      rw [hempty]
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_bne_ft source_segs _ _ _ _ _ _ _ _  SF_11054 (by decide) SD_11054 (by cat_regs; exact c_eq_0_true)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_jal_x0 source_segs _ _ _ _ _ _  SF_11058 (by decide) SD_11058) ?_
      apply to_wall_tail.twt_done
      refine ⟨_, msteps.mst_refl _, ?_⟩
      refine ⟨_, _, rfl, ?_, ?_, ?_, hm⟩
      · cat_regs
      · cat_regs; exact h3
      · cat_regs; exact h8
    · have hnonempty : 1 ≤ (bs.drop n).length := by rw [List.length_drop]; omega
      have hsk := rdn_skipn source_segs mem bs.length p bs n hread hn2
      rw [word_add_nat_Z p n (by omega), ← List.length_drop] at hsk
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_bne_tk source_segs _ _ _ _ _ _ _ _  SF_11054 (by decide) SD_11054 (by cat_regs; exact c_eq_0_false _ (by rw [hdu]; omega))) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1) SF_11030 (by decide) SD_11030 (by decide) (by cat_regs <;> rfl)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 24)) (len_word (bs.drop n)) SF_11034 (by decide) SD_11034 (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 32)) 8 = _; rw [v_addi_lit]; congr 1 <;> omega) (by cat_regs <;> rfl)
        (by apply source_stack_store av ev rsp rrnd uid hw
            · have hg := hm.1; cat_grows
            · cat_u; unfold stack_max_size; omega
            · cat_u; omega)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 32)) (Z_to_bv 64 (bv_unsigned p + (n : Int))) SF_11038 (by decide) SD_11038 (by cat_regs; exact v_addi_0 _) (by cat_regs <;> rfl)
        (by apply source_stack_store av ev rsp rrnd uid hw
            · have hg := hm.1; cat_grows
            · cat_u; unfold stack_max_size; omega
            · cat_u; omega)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_jal_link source_segs _ _ _ _ _ _ _  SF_1103c (by decide) SD_1103c) ?_
      simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 48)) SF_11104 (by decide) SD_11104 (by decide) (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 32)) (-16) = _; rw [v_addi_lit]; congr 1 <;> omega)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (len_word (bs.drop n)) SF_11108 (by decide) SD_11108 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_1110c (by decide) SD_1110c (by decide) (by cat_regs <;> rfl)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned p + (n : Int))) SF_11110 (by decide) SD_11110 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_11114 (by decide) SD_11114 (by decide) (by cat_regs <;> rfl)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1) SF_11118 (by decide) SD_11118 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_1111c (by decide) SD_1111c (by decide) (by cat_regs <;> rfl)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 64) SF_11120 (by decide) SD_11120 (by decide) (by cat_regs <;> rfl)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 40)) ((0x11040 : word)) SF_11124 (by decide) SD_11124 (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 48)) 8 = _; rw [v_addi_lit]; congr 1 <;> omega) (by cat_regs <;> rfl)
        (by apply source_stack_store av ev rsp rrnd uid hw
            · have hg := hm.1; cat_grows
            · cat_u; unfold stack_max_size; omega
            · cat_u; omega)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_jal_link source_segs _ _ _ _ _ _ _  SF_11128 (by decide) SD_11128) ?_
      simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_jal_x0 source_segs _ _ _ _ _ _  SF_11194 (by decide) SD_11194) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 64) SF_11170 (by decide) SD_11170 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1) SF_11174 (by decide) SD_11174 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned p + (n : Int))) SF_11178 (by decide) SD_11178 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (len_word (bs.drop n)) SF_1117c (by decide) SD_1117c (by decide) (by cat_regs; exact v_addi_0 _)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_11180 (by decide) SD_11180 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_11184 (by decide) SD_11184 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_11188 (by decide) SD_11188 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
      refine to_wall_tail.twt_step _ _ _ _ rfl (step_ecall source_segs _ _ _ _ _ SF_1118c (by decide)) ?_
      apply to_wall_tail.twt_more _ _ _ hnonempty
      apply twl_write_rec
      · cat_regs <;> rfl
      · cat_regs
      · cat_regs
        rw [ms_read_bytes_rdn source_segs _ _ _ rfl]
        have hwlen : word_to_nat (len_word (bs.drop n)) = (bs.drop n).length := by
          change (word_to_nat (len_word (bs.drop n)) : Int) = ((bs.drop n).length : Int) at hdu
          omega
        change rdn source_segs _ _ (word_to_nat (len_word (bs.drop n))) = _
        rw [hwlen]
        repeat rw [rdn_wbytes_below _ _ _ _ _ _ (by cat_u; omega) (by cat_u; omega)]
        exact hsk
      · exact hnonempty
      · intro m hm1 hm2
        apply ih (bs.drop n) (Z_to_bv 64 (bv_unsigned p + (n : Int))) m
        · rw [List.length_drop]; omega
        · exact hm1
        · exact hm2
        · rw [List.length_drop]; omega
        · cat_u; omega
        · cat_u; omega
        · cat_regs
        · cat_regs <;> rfl
        · cat_regs
        · cat_regs; exact h3
        · cat_regs; exact h8
        · repeat first
            | exact hm
            | refine mem_ok_scratch8 av ev rsp rrnd hsp_hi uid hw _ _ _ ?_
                (by cat_u; omega) (by cat_u; omega)
        · exact rdn_wbytes_hit8 _ _ _ _ (by cat_u; omega)
        · rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by cat_u; omega) (by cat_u; omega)]
          exact rdn_wbytes_hit8 _ _ _ _ (by cat_u; omega)
        · repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by cat_u; omega) (by cat_u; omega)]
          exact rdn_wbytes_hit8 _ _ _ _ (by cat_u; omega)
        · repeat rw [rdn_wbytes_below _ _ _ _ _ _ (by cat_u; omega) (by cat_u; omega)]
          exact hsk

theorem src_LH_to_rd (av ev : List (List byte)) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp)
    (hsp_hi : bv_unsigned rsp ≤ sp_window_hi) (uid hw : word)
    (ms : machine_state) (hlh : src_LH av ev rsp rrnd uid hw ms) :
    to_rd source_segs (src_LH av ev rsp rrnd uid hw) (Z_to_bv 64 1024) ms := by
  obtain ⟨regs, mem, rfl, h2, h3, h8, hm⟩ := hlh
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1024) SF_11010 (by decide) SD_11010 (by decide) (by cat_regs <;> rfl)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (src_buf) SF_11014 (by decide) SD_11014 (by decide) (by cat_regs; rw [h8]; exact v_addi_0 _)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_11018 (by decide) SD_11018 (by decide) (by cat_regs <;> rfl)) ?_
  refine to_rd.trd_step _ _ rfl (step_jal_link source_segs _ _ _ _ _ _ _  SF_1101c (by decide) SD_1101c) ?_
  simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 48)) SF_110d0 (by decide) SD_110d0 (by decide) (by cat_regs; rw [h2]; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 32)) (-16) = _; rw [v_addi_lit]; congr 1 <;> omega)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1024) SF_110d4 (by decide) SD_110d4 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_110d8 (by decide) SD_110d8 (by decide) (by cat_regs <;> rfl)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (src_buf) SF_110dc (by decide) SD_110dc (by decide) (by cat_regs; exact v_addi_0 _)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_110e0 (by decide) SD_110e0 (by decide) (by cat_regs <;> rfl)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_110e4 (by decide) SD_110e4 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_110e8 (by decide) SD_110e8 (by decide) (by cat_regs <;> rfl)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 63) SF_110ec (by decide) SD_110ec (by decide) (by cat_regs <;> rfl)) ?_
  refine to_rd.trd_step _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 40)) ((0x11020 : word)) SF_110f0 (by decide) SD_110f0 (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 48)) 8 = _; rw [v_addi_lit]; congr 1 <;> omega) (by cat_regs <;> rfl)
    (by apply source_stack_store av ev rsp rrnd uid hw
        · have hg := hm.1; cat_grows
        · cat_u; unfold stack_max_size; omega
        · cat_u; omega)) ?_
  refine to_rd.trd_step _ _ rfl (step_jal_link source_segs _ _ _ _ _ _ _  SF_110f4 (by decide) SD_110f4) ?_
  simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine to_rd.trd_step _ _ rfl (step_jal_x0 source_segs _ _ _ _ _ _  SF_11194 (by decide) SD_11194) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 63) SF_11170 (by decide) SD_11170 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_11174 (by decide) SD_11174 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (src_buf) SF_11178 (by decide) SD_11178 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1024) SF_1117c (by decide) SD_1117c (by decide) (by cat_regs; exact v_addi_0 _)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_11180 (by decide) SD_11180 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_11184 (by decide) SD_11184 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_11188 (by decide) SD_11188 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
  refine to_rd.trd_step _ _ rfl (step_ecall source_segs _ _ _ _ _ SF_1118c (by decide)) ?_
  apply trd_here_rec (buf := src_buf)
  · cat_regs <;> rfl
  · cat_regs
  · cat_regs
  · cat_regs
  · exact source_buf_wseg
  · decide
  · refine to_exit.te_step _ _ rfl (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x110f8 : word) SF_11190 (by decide) SD_11190 (by cat_regs <;> rfl)) ?_
    refine to_exit.te_step _ _ rfl (step_ld source_segs _ _ _ _ _ _ _ _ (word_to_le_bytes 8 ((0x11020 : word))) ((0x11020 : word)) SF_110f8 (by decide) SD_110f8 (by cat_regs; change rdn source_segs _ (v_addi (Z_to_bv 64 (bv_unsigned rsp - 48)) 8) 8 = _; rw [v_addi_lit]; have ha : bv_unsigned rsp - 48 + 8 = bv_unsigned rsp - 40 := (by omega); rw [ha]; exact rdn_wbytes_hit8 _ _ _ _ (by cat_u; omega)) (bytes_le_to_Z_8 _)) ?_
    simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine to_exit.te_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 32)) SF_110fc (by decide) SD_110fc (by decide) (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 48)) 16 = _; rw [v_addi_lit]; congr 1 <;> omega)) ?_
    refine to_exit.te_step _ _ rfl (step_jal_x0 source_segs _ _ _ _ _ _  SF_11100 (by decide) SD_11100) ?_
    refine to_exit.te_step _ _ rfl (step_lui_at source_segs _ _ _ _ _ _ _ (Z_to_bv 64 (-4096)) SF_11138 (by decide) SD_11138 (by decide) (by rfl)) ?_
    refine to_exit.te_step _ _ rfl (step_bltu_ft source_segs _ _ _ _ _ _ _ _  SF_1113c (by decide) SD_1113c (by cat_regs; exact c_ltu_x0 _)) ?_
    refine to_exit.te_step _ _ rfl (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x11020 : word) SF_11140 (by decide) SD_11140 (by cat_regs <;> rfl)) ?_
    refine to_exit.te_step _ _ rfl (step_beq_tk source_segs _ _ _ _ _ _ _ _  SF_11020 (by decide) SD_11020 (by cat_regs; exact c_eq_0_true)) ?_
    refine to_exit.te_step _ _ rfl (step_ld source_segs _ _ _ _ _ _ _ _ (word_to_le_bytes 8 ((0x110a4 : word))) ((0x110a4 : word)) SF_11060 (by decide) SD_11060 (by cat_regs; change rdn source_segs _ (v_addi (Z_to_bv 64 (bv_unsigned rsp - 32)) 24) 8 = _; rw [v_addi_lit]; have ha : bv_unsigned rsp - 32 + 24 = bv_unsigned rsp - 8 := (by omega); rw [ha]; rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by cat_u; omega) (by cat_u; omega)]; exact read_ra_slot_m av ev rsp rrnd hsp_lo hsp_hi uid hw mem hm) (bytes_le_to_Z_8 _)) ?_
    simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine to_exit.te_step _ _ rfl (step_ld source_segs _ _ _ _ _ _ _ _ (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) SF_11064 (by decide) SD_11064 (by cat_regs; change rdn source_segs _ (v_addi (Z_to_bv 64 (bv_unsigned rsp - 32)) 16) 8 = _; rw [v_addi_lit]; have ha : bv_unsigned rsp - 32 + 16 = bv_unsigned rsp - 16 := (by omega); rw [ha]; rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by cat_u; omega) (by cat_u; omega)]; exact read_s0_slot_m av ev rsp rrnd hsp_lo hsp_hi uid hw mem hm) (bytes_le_to_Z_8 _)) ?_
    simp only [show bv_eqb (8 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine to_exit.te_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (rsp) SF_11068 (by decide) SD_11068 (by decide) (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 32)) 32 = _; rw [v_addi_lit]; apply bv_eq_of_unsigned; rw [u_Z2bv _ (by omega) (by omega)]; omega)) ?_
    refine to_exit.te_step _ _ rfl (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x110a4 : word) SF_1106c (by decide) SD_1106c (by cat_regs <;> rfl)) ?_
    refine to_exit.te_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 93) SF_110a4 (by decide) SD_110a4 (by decide) (by cat_regs <;> rfl)) ?_
    refine to_exit.te_step _ _ rfl (step_ecall source_segs _ _ _ _ _ SF_110a8 (by decide)) ?_
    apply te_here_rec0
    · cat_regs <;> rfl
    · cat_regs
  · intro bs hblo hbhi
    have hu := u_len_word bs (by omega)
    have hmread := mem_ok_buf av ev rsp rrnd hsp_lo uid hw _ bs
      (mem_ok_scratch8 av ev rsp rrnd hsp_hi uid hw mem
        (Z_to_bv 64 (bv_unsigned rsp - 40)) (0x11020 : word) hm
        (by cat_u; omega) (by cat_u; omega)) hbhi
    refine to_wr.twr_step _ _ rfl (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x110f8 : word) SF_11190 (by decide) SD_11190 (by cat_regs <;> rfl)) ?_
    refine to_wr.twr_step _ _ rfl (step_ld source_segs _ _ _ _ _ _ _ _ (word_to_le_bytes 8 ((0x11020 : word))) ((0x11020 : word)) SF_110f8 (by decide) SD_110f8 (by cat_regs; change rdn source_segs _ (v_addi (Z_to_bv 64 (bv_unsigned rsp - 48)) 8) 8 = _; rw [v_addi_lit]; have ha : bv_unsigned rsp - 48 + 8 = bv_unsigned rsp - 40 := (by omega); rw [ha]; rw [rdn_wtm_out _ _ _ _ _ _ (by cat_u; omega) (by rw [u_src_buf]; omega) (Or.inl (by rw [u_src_buf]; cat_u; omega))]; exact rdn_wbytes_hit8 _ _ _ _ (by cat_u; omega)) (bytes_le_to_Z_8 _)) ?_
    simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 32)) SF_110fc (by decide) SD_110fc (by decide) (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 48)) 16 = _; rw [v_addi_lit]; congr 1 <;> omega)) ?_
    refine to_wr.twr_step _ _ rfl (step_jal_x0 source_segs _ _ _ _ _ _  SF_11100 (by decide) SD_11100) ?_
    refine to_wr.twr_step _ _ rfl (step_lui_at source_segs _ _ _ _ _ _ _ (Z_to_bv 64 (-4096)) SF_11138 (by decide) SD_11138 (by decide) (by rfl)) ?_
    refine to_wr.twr_step _ _ rfl (step_bltu_ft source_segs _ _ _ _ _ _ _ _  SF_1113c (by decide) SD_1113c (by cat_regs; rw [c_ltu_ltb, hu]; change decide (18446744073709547520 < (bs.length : Int)) = false; exact decide_eq_false (by omega))) ?_
    refine to_wr.twr_step _ _ rfl (step_jalr_x0 source_segs _ _ _ _ _ _ _ (0x11020 : word) SF_11140 (by decide) SD_11140 (by cat_regs <;> rfl)) ?_
    refine to_wr.twr_step _ _ rfl (step_beq_ft source_segs _ _ _ _ _ _ _ _  SF_11020 (by decide) SD_11020 (by cat_regs; exact c_eq_0_false _ (by rw [hu]; omega))) ?_
    refine to_wr.twr_step _ _ rfl (step_blt_ft source_segs _ _ _ _ _ _ _ _  SF_11024 (by decide) SD_11024 (by cat_regs; exact c_lts_pos_0 _ (by rw [hu]; omega))) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (len_word bs) SF_11028 (by decide) SD_11028 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (src_buf) SF_1102c (by decide) SD_1102c (by decide) (by cat_regs; rw [h8]; exact v_addi_0 _)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1) SF_11030 (by decide) SD_11030 (by decide) (by cat_regs <;> rfl)) ?_
    refine to_wr.twr_step _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 24)) (len_word bs) SF_11034 (by decide) SD_11034 (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 32)) 8 = _; rw [v_addi_lit]; congr 1 <;> omega) (by cat_regs <;> rfl)
      (by apply source_stack_store av ev rsp rrnd uid hw
          · have hg := hmread.1; cat_grows
          · cat_u; unfold stack_max_size; omega
          · cat_u; omega)) ?_
    refine to_wr.twr_step _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 32)) (src_buf) SF_11038 (by decide) SD_11038 (by cat_regs; exact v_addi_0 _) (by cat_regs <;> rfl)
      (by apply source_stack_store av ev rsp rrnd uid hw
          · have hg := hmread.1; cat_grows
          · cat_u; unfold stack_max_size; omega
          · cat_u; omega)) ?_
    refine to_wr.twr_step _ _ rfl (step_jal_link source_segs _ _ _ _ _ _ _  SF_1103c (by decide) SD_1103c) ?_
    simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 48)) SF_11104 (by decide) SD_11104 (by decide) (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 32)) (-16) = _; rw [v_addi_lit]; congr 1 <;> omega)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (len_word bs) SF_11108 (by decide) SD_11108 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_1110c (by decide) SD_1110c (by decide) (by cat_regs <;> rfl)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (src_buf) SF_11110 (by decide) SD_11110 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_11114 (by decide) SD_11114 (by decide) (by cat_regs <;> rfl)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1) SF_11118 (by decide) SD_11118 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_1111c (by decide) SD_1111c (by decide) (by cat_regs <;> rfl)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 64) SF_11120 (by decide) SD_11120 (by decide) (by cat_regs <;> rfl)) ?_
    refine to_wr.twr_step _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 40)) ((0x11040 : word)) SF_11124 (by decide) SD_11124 (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 48)) 8 = _; rw [v_addi_lit]; congr 1 <;> omega) (by cat_regs <;> rfl)
      (by apply source_stack_store av ev rsp rrnd uid hw
          · have hg := hmread.1; cat_grows
          · cat_u; unfold stack_max_size; omega
          · cat_u; omega)) ?_
    refine to_wr.twr_step _ _ rfl (step_jal_link source_segs _ _ _ _ _ _ _  SF_11128 (by decide) SD_11128) ?_
    simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine to_wr.twr_step _ _ rfl (step_jal_x0 source_segs _ _ _ _ _ _  SF_11194 (by decide) SD_11194) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 64) SF_11170 (by decide) SD_11170 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 1) SF_11174 (by decide) SD_11174 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (src_buf) SF_11178 (by decide) SD_11178 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (len_word bs) SF_1117c (by decide) SD_1117c (by decide) (by cat_regs; exact v_addi_0 _)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_11180 (by decide) SD_11180 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_11184 (by decide) SD_11184 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
    refine to_wr.twr_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 0) SF_11188 (by decide) SD_11188 (by decide) (by cat_regs; exact v_addi_0 _)) ?_
    refine to_wr.twr_step _ _ rfl (step_ecall source_segs _ _ _ _ _ SF_1118c (by decide)) ?_
    apply twr_here_rec
    · cat_regs <;> rfl
    · cat_regs
    · cat_regs
      rw [ms_read_bytes_rdn source_segs _ _ _ rfl]
      have hwlen : word_to_nat (len_word bs) = bs.length := by
        change (word_to_nat (len_word bs) : Int) = (bs.length : Int) at hu
        omega
      change rdn source_segs _ src_buf (word_to_nat (len_word bs)) = _
      rw [hwlen]
      repeat rw [rdn_wbytes_below _ _ _ _ _ _ (by rw [u_src_buf]; cat_u; omega) (by cat_u; omega)]
      exact rdn_write_to_mem _ _ _ _ (by rw [u_src_buf]; omega)
    · omega
    · intro n hn1 hn2
      apply src_put_wall av ev rsp rrnd hsp_lo hsp_hi uid hw bs.length bs src_buf n
      · exact Nat.le_refl _
      · exact hn1
      · exact hn2
      · exact hbhi
      · rw [u_src_buf]; omega
      · rw [u_src_buf]; omega
      · cat_regs
      · cat_regs <;> rfl
      · cat_regs
      · cat_regs; exact h3
      · cat_regs; exact h8
      · repeat first
          | exact hmread
          | refine mem_ok_scratch8 av ev rsp rrnd hsp_hi uid hw _ _ _ ?_
              (by cat_u; omega) (by cat_u; omega)
      · exact rdn_wbytes_hit8 _ _ _ _ (by cat_u; omega)
      · rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by cat_u; omega) (by cat_u; omega)]
        exact rdn_wbytes_hit8 _ _ _ _ (by cat_u; omega)
      · repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _ (by cat_u; omega) (by cat_u; omega)]
        exact rdn_wbytes_hit8 _ _ _ _ (by cat_u; omega)
      · repeat rw [rdn_wbytes_below _ _ _ _ _ _ (by rw [u_src_buf]; cat_u; omega) (by cat_u; omega)]
        exact rdn_write_to_mem _ _ _ _ (by rw [u_src_buf]; omega)

theorem src_init_to_rd (av ev : List (List byte)) (hva : valid_argv av)
    (hve : valid_envp ev) (rsp : word) (rrnd : EntryDraw)
    (hsp_lo : sp_window_lo ≤ bv_unsigned rsp)
    (hsp_hi : bv_unsigned rsp ≤ sp_window_hi) (uid hw : word) :
    to_rd source_segs (src_LH av ev rsp rrnd uid hw) (Z_to_bv 64 1024)
      (init_machine_state source_segs 0x11078 source_phdrs rsp rrnd av ev uid hw) := by
  have hlo := rsp_lo_num rsp hsp_lo
  have hhi := rsp_hi_num rsp hsp_hi
  have hargc : rdn source_segs (wmem av ev rsp rrnd uid hw) rsp 8 =
      some (word_le8 (argcN av)) := by
    unfold wmem
    rw [rdn_wrap_stack_above _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
    exact read_argc _ _ _ _ _ _ _ _ (source_bsb_nw av ev hva hve rsp rrnd hsp_hi uid hw)
  rw [init_mkst]
  refine to_rd.trd_step _ _ rfl (step_auipc source_segs _ _ _ _ _ _ _  SF_11078 (by decide) SD_11078) ?_
  simp only [show bv_eqb (3 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ ((0x13800 : word)) SF_1107c (by decide) SD_1107c (by decide) (by cat_regs <;> rfl)) ?_
  refine to_rd.trd_step _ _ rfl (step_ld source_segs _ _ _ _ _ _ _ _ (word_le8 (argcN av)) (argcN av) SF_11080 (by decide) SD_11080 (by cat_regs; change rdn source_segs _ (v_addi rsp 0) 8 = _; rw [v_addi_0]; exact hargc) (bytes_le_n_to_le_8 _)) ?_
  simp only [show bv_eqb (10 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp + 8)) SF_11084 (by decide) SD_11084 (by decide) (by cat_regs <;> rfl)) ?_
  refine to_rd.trd_step _ _ rfl (step_slli source_segs _ _ _ _ _ _ _ _  SF_11088 (by decide) SD_11088) ?_
  simp only [show bv_eqb (5 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine to_rd.trd_step _ _ rfl (step_add_at source_segs _ _ _ _ _ _ _ _ (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN av) 3)) SF_1108c (by decide) SD_1108c (by decide) (by cat_regs <;> rfl)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (envp_ptr av rsp) SF_11090 (by decide) SD_11090 (by decide) (by cat_regs; exact envp_ptr_eq av hva rsp hsp_lo hsp_hi)) ?_
  refine to_rd.trd_step _ _ rfl (step_auipc source_segs _ _ _ _ _ _ _  SF_11094 (by decide) SD_11094) ?_
  simp only [show bv_eqb (6 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ ((0x13000 : word)) SF_11098 (by decide) SD_11098 (by decide) (by cat_regs <;> rfl)) ?_
  refine to_rd.trd_step _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _ (0x13000 : word) (envp_ptr av rsp) SF_1109c (by decide) SD_1109c (by cat_regs <;> rfl) (by cat_regs) (by apply source_store_ok <;> decide)) ?_
  refine to_rd.trd_step _ _ rfl (step_jal_link source_segs _ _ _ _ _ _ _  SF_110a0 (by decide) SD_110a0) ?_
  simp only [show bv_eqb (1 : reg) 0 = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 32)) SF_11000 (by decide) SD_11000 (by decide) (by cat_regs; exact v_addi_m32 rsp (by omega))) ?_
  refine to_rd.trd_step _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 16)) (Z_to_bv 64 0) SF_11004 (by decide) SD_11004 (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 32)) 16 = _; rw [v_addi_lit]; congr 1 <;> omega) (by cat_regs <;> rfl)
    (by apply source_stack_store av ev rsp rrnd uid hw
        · cat_grows
        · cat_u; unfold stack_max_size; omega
        · cat_u; omega)) ?_
  refine to_rd.trd_step _ _ rfl (step_sd_at source_segs _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned rsp - 8)) ((0x110a4 : word)) SF_11008 (by decide) SD_11008 (by cat_regs; change v_addi (Z_to_bv 64 (bv_unsigned rsp - 32)) 24 = _; rw [v_addi_lit]; congr 1 <;> omega) (by cat_regs <;> rfl)
    (by apply source_stack_store av ev rsp rrnd uid hw
        · cat_grows
        · cat_u; unfold stack_max_size; omega
        · cat_u; omega)) ?_
  refine to_rd.trd_step _ _ rfl (step_addi_at source_segs _ _ _ _ _ _ _ _ (src_buf) SF_1100c (by decide) SD_1100c (by decide) (by cat_regs <;> rfl)) ?_
  apply src_LH_to_rd av ev rsp rrnd hsp_lo hsp_hi uid hw
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_⟩
  · cat_regs
  · cat_regs <;> rfl
  · cat_regs
  · exact fmem_ok av ev rsp rrnd uid hw

end LinuxProcessSemantics.Examples.cat1024_ns.cat1024_ns_source
