import LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_defs
import LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_hoare
import LinuxProcessSemantics.Common.ArgvEnv
import LinuxProcessSemantics.Common.SymTac
import LinuxProcessSemantics.Common.SymBranch
import LinuxProcessSemantics.Common.SymSide
import LinuxProcessSemantics.Common.Footprint
import LinuxProcessSemantics.Common.ErrEscape

/-! rocq-baseline: 36031418350290d5d51fae6e71cbf0b73d7cc91e -/

/-! conditional-bug-ns source binary: per-input execution derivations.
Proof-side symbolic dispatch, write-all retry loop, and explicit exit behavior.
The source additionally supplies the universal source-error escape witness. -/

namespace LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_source

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Examples.conditional_bug_ns.SourceMemImage
open LinuxProcessSemantics.Examples.conditional_bug_ns.TargetMemImage
open LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_code

open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Common.SymTac
open LinuxProcessSemantics.Common.SymBranch
open LinuxProcessSemantics.Common.Footprint
open LinuxProcessSemantics.Common.ArgvEnv
open LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_defs
open LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_hoare
open LinuxProcessSemantics.Common.Hoare
open LinuxProcessSemantics.Common.MuslCall

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

variable (av ev : List (List byte)) (uid hw : word)
variable (Hva : valid_argv av) (Hve : valid_envp ev)
variable (rsp : word) (rrnd : EntryDraw)
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp)
variable (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi)

include Hsp_lo in
theorem rsp_lo_num : 0x7fff80000000 ≤ bv_unsigned rsp := Hsp_lo

include Hsp_hi in
theorem rsp_hi_num : bv_unsigned rsp ≤ 0x800000000000 := Hsp_hi

include Hva Hve Hsp_hi in
theorem source_bsb_nw :
    bv_unsigned rsp + ((build_stack_bytes source_phdrs rsp av ev uid hw rrnd).length : Int) < 2^64 :=
  bsb_nw source_phdrs rsp av ev uid hw rrnd Hva Hve Hsp_hi

def ptr1 : word := cat_argv_ptr rsp av ev 1

include Hva Hve Hsp_hi in
theorem ptr1_bounds (Hge2 : 2 ≤ av.length) :
    bv_unsigned rsp ≤ bv_unsigned (ptr1 av ev rsp) ∧
    bv_unsigned (ptr1 av ev rsp) + ((av.getD 1 []).length : Int) + 1 < 2^64 :=
  argv_ptr_bounds_at rsp av ev Hva Hve Hsp_hi 1 (by omega)

include Hva Hve Hsp_hi in
theorem read_ptr1 (Hge2 : 2 ≤ av.length) :
    rdn source_segs (stack_to_mem rsp (entry_stack_image source_phdrs rsp av ev uid hw rrnd))
      (rsp + nat_to_word (8 + 8 * 1)) 8 = some (word_le8 (ptr1 av ev rsp)) :=
  read_argv_ptr_k source_phdrs source_segs rsp av ev 1 uid hw rrnd (by omega)
    (source_bsb_nw av ev uid hw Hva Hve rsp rrnd Hsp_hi)

include Hva Hve Hsp_hi in
theorem read_b (Hge2 : 2 ≤ av.length) :
    rdn source_segs (stack_to_mem rsp (entry_stack_image source_phdrs rsp av ev uid hw rrnd))
      (ptr1 av ev rsp) 1 = some [byte_at (av.getD 1 []) 0] := by
  have h := read_argv_byte_k source_phdrs source_segs rsp av ev 1 0 uid hw rrnd
    (by omega) (by omega) (source_bsb_nw av ev uid hw Hva Hve rsp rrnd Hsp_hi)
  rw [word_add_0] at h
  exact h

def bval : word := Z_to_bv 64 (bv_unsigned (byte_at (av.getD 1 []) 0))

theorem u_bval : bv_unsigned (bval av) = bv_unsigned (byte_at (av.getD 1 []) 0) :=
  u_zext8 _

set_option hygiene false in
local macro "cbn_read_argc" : tactic => `(tactic| (
  rw [show Z_to_bv 64 (bv_unsigned rsp + 0) = rsp by
    apply bv_eq_of_unsigned; u_norm; omega]
  refine ⟨word_le8 (argcN av), ?_, bytes_le_n_to_le_8 _⟩
  rw [rdn_wrap_stack_above source_segs _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
  exact read_argc source_phdrs source_segs rsp av ev uid hw rrnd
    (source_bsb_nw av ev uid hw Hva Hve rsp rrnd Hsp_hi)))

set_option hygiene false in
local macro "cbn_read_ptr1" : tactic => `(tactic| (
  rw [show Z_to_bv 64 (bv_unsigned rsp + 16) = rsp + nat_to_word (8 + 8 * 1) by
    rw [word_add_nat]; congr 1 <;> omega]
  refine ⟨word_le8 (ptr1 av ev rsp), ?_, bytes_le_n_to_le_8 _⟩
  rw [rdn_wrap_stack_above source_segs _ _ _ _ _ _ _ _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  exact read_ptr1 av ev uid hw Hva Hve rsp rrnd Hsp_hi Hge2))

set_option hygiene false in
local macro "cbn_read_byte" : tactic => `(tactic| (
  rw [show Z_to_bv 64 (bv_unsigned (ptr1 av ev rsp) + 0) = ptr1 av ev rsp by
    apply bv_eq_of_unsigned; u_norm; omega]
  refine ⟨[byte_at (av.getD 1 []) 0], ?_, ?_⟩
  · rw [rdn_wrap_stack_above source_segs _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
    exact read_b av ev uid hw Hva Hve rsp rrnd Hsp_hi Hge2
  · rw [bytes_le_single]
    change bv_unsigned (byte_at (av.getD 1 []) 0) = bv_unsigned (bval av)
    exact (u_bval av).symm))

set_option hygiene false in
local macro "cbn_argc_br" : tactic => `(tactic| (
  try rw [Bool.not_eq_true']
  try rw [Bool.not_eq_false']
  rw [bv_lts_small _ _ (by u_norm; omega) (by rw [u_argcN av Hva]; omega)]
  first | rw [decide_eq_true_eq] | rw [decide_eq_false_iff_not]
  u_norm
  rw [u_argcN av Hva]
  omega))

set_option hygiene false in
local macro "cbn_sc" : tactic => `(tactic| (
  repeat' first
  | apply And.intro
  | omega
  | cbn_argc_br
  | cbn_read_byte
  | cbn_read_ptr1
  | cbn_read_argc
  | (apply source_store_ok <;> (u_norm; omega))
  | solve_store_ok
  | (unfold bval; rw [Hb]; decide +kernel)
  | ((first | rw [Bool.not_eq_true'] | rw [Bool.not_eq_false'] | skip)
     unfold bval
     first
     | exact c_eq_zext_lit_false _ 110 (by omega) Hn110
     | exact c_eq_zext_lit_false _ 104 (by omega) Hn104
     | exact c_eq_zext_lit_false _ 111 (by omega) Hn111)))

include Hva Hve Hsp_lo Hsp_hi in
theorem source_wexit_lt2 (Hlt2 : av.length < 2) :
    to_wexit source_segs
      (init_machine_state source_segs 0x110a4 source_phdrs rsp rrnd av ev uid hw)
      [] (Z_to_bv 64 2) := by
  have Hargc := valid_argv_len av Hva
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  rw [init_mkst]
  norm_pc
  sym_block source_segs 20 [true] ([] : List expr)
    [((2 : reg), EVar 32)] [rsp] [argcN av] RA HRA
  · cbn_sc
  · getr_resolve; rfl
  apply to_wexit.tw_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_110d4 rfl)
  apply tw_exit_coden
  · sym_regs HRA; sym_close
  · sym_regs HRA; sym_close
  · u_norm; omega

include Hva Hve Hsp_lo Hsp_hi in
theorem source_wexit_n (Hge2 : 2 ≤ av.length)
    (Hb : byte_at (av.getD 1 []) 0 = Z_to_bv 8 110) :
    to_wexit source_segs
      (init_machine_state source_segs 0x110a4 source_phdrs rsp rrnd av ev uid hw)
      [] (Z_to_bv 64 0) := by
  have Hargc := valid_argv_len av Hva
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  obtain ⟨Hp1, Hp2⟩ := ptr1_bounds av ev Hva Hve rsp Hsp_hi Hge2
  rw [init_mkst]
  norm_pc
  sym_block source_segs 25 [false, true] ([] : List expr)
    [((2 : reg), EVar 32)] [rsp] [argcN av, ptr1 av ev rsp, bval av] RA HRA
  · cbn_sc
  · getr_resolve; rfl
  apply to_wexit.tw_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_110d4 rfl)
  apply tw_exit_coden
  · sym_regs HRA; sym_close
  · sym_regs HRA; sym_close
  · u_norm; omega

include Hva Hve Hsp_lo Hsp_hi in
theorem source_wexit_other (Hge2 : 2 ≤ av.length)
    (Hn110 : byte_at (av.getD 1 []) 0 ≠ Z_to_bv 8 110)
    (Hn104 : byte_at (av.getD 1 []) 0 ≠ Z_to_bv 8 104)
    (Hn111 : byte_at (av.getD 1 []) 0 ≠ Z_to_bv 8 111) :
    to_wexit source_segs
      (init_machine_state source_segs 0x110a4 source_phdrs rsp rrnd av ev uid hw)
      [] (Z_to_bv 64 3) := by
  have Hargc := valid_argv_len av Hva
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  obtain ⟨Hp1, Hp2⟩ := ptr1_bounds av ev Hva Hve rsp Hsp_hi Hge2
  rw [init_mkst]
  norm_pc
  sym_block source_segs 30 [false, false, true, true] ([] : List expr)
    [((2 : reg), EVar 32)] [rsp] [argcN av, ptr1 av ev rsp, bval av] RA HRA
  · cbn_sc
  · getr_resolve; rfl
  apply to_wexit.tw_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_110d4 rfl)
  apply tw_exit_coden
  · sym_regs HRA; sym_close
  · sym_regs HRA; sym_close
  · u_norm; omega

def cbwmem : word → Option byte := wrap_mem source_phdrs rsp av ev uid hw rrnd

include Hsp_lo Hsp_hi in
theorem cb_sok8 (mem : word → Option byte) (a : word)
    (Hg : mem_grows (cbwmem av ev uid hw rsp rrnd) mem)
    (Hlo : bv_unsigned rsp - 48 ≤ bv_unsigned a)
    (Hhi : bv_unsigned a + 8 ≤ bv_unsigned rsp) :
    store_ok source_segs mem a 8 = true := by
  have Hlo' := rsp_lo_num rsp Hsp_lo
  have Hhi' := rsp_hi_num rsp Hsp_hi
  apply store_ok_mono _ _ _ _ _ Hg
  apply store_ok_wrap_window <;> (first | (unfold stack_max_size; omega) | omega)

local macro "cbn_grows" : tactic => `(tactic| (unfold cbwmem; solve_mem_grows))

set_option hygiene false in
local macro "cbn_sok" : tactic => `(tactic| (
  apply cb_sok8 av ev uid hw rsp rrnd Hsp_lo Hsp_hi
  · cbn_grows
  · u_norm; omega
  · u_norm; omega))

include Hsp_lo Hsp_hi in
/-- The spilled pointer/count and return address survive every wrapper call. -/
theorem src_put_wall (fuel : Nat) (bs : List byte) (p : word) (n : Nat)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (Hfuel : bs.length ≤ fuel) (Hn1 : 1 ≤ n) (Hn2 : n ≤ bs.length)
    (Hlen : (bs.length : Int) ≤ 6)
    (Hplo : 0x12000 ≤ bv_unsigned p)
    (Hphi : bv_unsigned p + (bs.length : Int) ≤ 0x12006)
    (H10 : reg_get regs 10 = len_word (bs.take n))
    (H2 : reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 32))
    (Hgrow : mem_grows (cbwmem av ev uid hw rsp rrnd) mem)
    (Hptr : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 32)) 8 =
      some (word_to_le_bytes 8 p))
    (Hcnt : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 24)) 8 =
      some (word_to_le_bytes 8 (len_word bs)))
    (Hra : rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8 =
      some (word_to_le_bytes 8 (0x110d0 : word)))
    (Hread : rdn source_segs mem p bs.length = some bs) :
    to_wall_tail source_segs (Z_to_bv 64 1)
      (mkst regs 0x11048 mem (seg_rom source_segs)) (bs.drop n)
      (to_wallexit source_segs (Z_to_bv 64 1) [] (Z_to_bv 64 0)) := by
  induction fuel generalizing bs p n regs mem with
  | zero => omega
  | succ fuel IH =>
    have Hlo := rsp_lo_num rsp Hsp_lo
    have Hhi := rsp_hi_num rsp Hsp_hi
    step_intro
    · rfl
    · apply step_bge_ft (hf := SF_11048) (he := rfl) (hd := SD_11048)
      getr_resolve
      rw [H10]
      apply c_lts_0_pos <;>
        (rw [u_len_word_firstn n bs Hn2 (by omega)]; omega)
    norm_pc
    stepld SF_1104c SD_1104c (Z_to_bv 64 (bv_unsigned rsp - 24)) (len_word bs)
      (exact Hcnt)
    stepld SF_11050 SD_11050 (Z_to_bv 64 (bv_unsigned rsp - 32)) p (exact Hptr)
    stepiv SF_11054 SD_11054 (len_word (bs.drop n))
      (getr_resolve; rw [H10]; apply v_sub_len_firstn <;> omega)
    stepiv SF_11058 SD_11058 (Z_to_bv 64 (bv_unsigned p + (n : Int)))
      (getr_resolve; rw [H10]; apply v_add_len_firstn_Z <;> omega)
    by_cases Hne : n = bs.length
    · subst n
      rw [List.drop_length]
      step_intro
      · rfl
      · apply step_bne_ft (hf := SF_1105c) (he := rfl) (hd := SD_1105c)
        getr_resolve
        rfl
      norm_pc
      stepiv SF_11060 SD_11060 (Z_to_bv 64 0) (getr_resolve; bveq)
      stepld SF_11064 SD_11064 (Z_to_bv 64 (bv_unsigned rsp - 8))
        (0x110d0 : word) (exact Hra)
      stepi SF_11068 SD_11068
      stepi SF_1106c SD_1106c
      stepi SF_11070 SD_11070
      stepjr SF_11074 SD_11074 (0x110d0 : word) (getr_resolve; rfl)
      stepiv SF_110d0 SD_110d0 (Z_to_bv 64 93) (getr_resolve; bveq)
      apply to_wall_tail.twt_done
      change to_wexit source_segs _ [] (Z_to_bv 64 0)
      apply to_wexit.tw_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ SF_110d4 rfl)
      apply tw_exit_coden
      · getr_resolve; rfl
      · regupd_resolve; getr_resolve; bveq
      · decide +kernel
    · have Hdrop : ((bs.drop n).length : Int) < 2^64 := by
        rw [List.length_drop]; omega
      have Hsk := rdn_skipn source_segs mem bs.length p bs n Hread Hn2
      rw [word_add_nat_Z p n (by omega)] at Hsk
      have Hsk' : rdn source_segs mem (Z_to_bv 64 (bv_unsigned p + (n : Int)))
          (bs.drop n).length = some (bs.drop n) := by
        rw [List.length_drop]; exact Hsk
      step_intro
      · rfl
      · apply step_bne_tk (hf := SF_1105c) (he := rfl) (hd := SD_1105c)
        getr_resolve
        apply c_eq_0_false
        rw [u_len_word _ Hdrop, List.length_drop]
        omega
      norm_pc
      stepiv SF_11038 SD_11038 (Z_to_bv 64 1) (getr_resolve; bveq)
      stepsd SF_1103c SD_1103c (Z_to_bv 64 (bv_unsigned rsp - 24))
        (len_word (bs.drop n)) (getr_resolve; rfl) (cbn_sok)
      stepsd SF_11040 SD_11040 (Z_to_bv 64 (bv_unsigned rsp - 32))
        (Z_to_bv 64 (bv_unsigned p + (n : Int))) (getr_resolve; rfl) (cbn_sok)
      stepj SF_11044 SD_11044
      have Hs40 : at_ (Z_to_bv 64 (bv_unsigned rsp - 32)) (-8) =
          Z_to_bv 64 (bv_unsigned rsp - 40) := by
        unfold at_; u_norm; congr 1; omega
      apply cb_write_call _ _ _ (0x11048 : word)
        (Z_to_bv 64 (bv_unsigned rsp - 32))
        (Z_to_bv 64 (bv_unsigned p + (n : Int))) (len_word (bs.drop n))
      all_goals try rw [Hs40]
      · decide +kernel
      · getr_resolve; bveq
      · getr_resolve; exact H2
      · getr_resolve; rfl
      · getr_resolve; rfl
      · getr_resolve; rfl
      · cbn_sok
      · u_norm; omega
      · rw [u_len_word _ Hdrop, List.length_drop]; omega
      · have Hwn : word_to_nat (len_word (bs.drop n)) = (bs.drop n).length := by
          exact Int.ofNat_inj.mp (u_len_word _ Hdrop)
        rw [Hwn]
        repeat rw [rdn_wbytes_below _ _ _ _ _ _
          (by u_norm; rw [List.length_drop]; omega)
          (by rw [length_N_to_le_bytes]; u_norm; omega)]
        exact Hsk'
      · rw [List.length_drop]; omega
      · intro regs'' m Hm1 Hm2 _ R2 R10
        apply IH (bs.drop n) (Z_to_bv 64 (bv_unsigned p + (n : Int))) m
        · rw [List.length_drop]; omega
        · exact Hm1
        · exact Hm2
        · rw [List.length_drop]; omega
        · u_norm; omega
        · u_norm; rw [List.length_drop]; omega
        · exact R10
        · exact R2
        · cbn_grows
        · rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
          apply rdn_wbytes_hit8; u_norm; omega
        · repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
          apply rdn_wbytes_hit8; u_norm; omega
        · repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
            (by rw [length_N_to_le_bytes]; u_norm; omega) (by u_norm; omega)]
          exact Hra
        · repeat rw [rdn_wbytes_below _ _ _ _ _ _
            (by u_norm; rw [List.length_drop]; omega)
            (by rw [length_N_to_le_bytes]; u_norm; omega)]
          exact Hsk'

include Hva Hve Hsp_lo Hsp_hi in
theorem source_wexit_h (Hge2 : 2 ≤ av.length)
    (Hb : byte_at (av.getD 1 []) 0 = Z_to_bv 8 104) :
    to_wallexit source_segs (Z_to_bv 64 1) [hello] (Z_to_bv 64 0)
      (init_machine_state source_segs 0x110a4 source_phdrs rsp rrnd av ev uid hw) := by
  have Hargc := valid_argv_len av Hva
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  obtain ⟨Hp1, Hp2⟩ := ptr1_bounds av ev Hva Hve rsp Hsp_hi Hge2
  refine ⟨by decide +kernel, ?_⟩
  rw [init_mkst]
  norm_pc
  sym_block source_segs 29 [false, false, false] ([] : List expr)
    [((2 : reg), EVar 32)] [rsp] [argcN av, ptr1 av ev rsp, bval av] RA HRA
  · cbn_sc
  · getr_resolve; rfl
  have Hs40 : at_ (Z_to_bv 64 (bv_unsigned rsp - 32)) (-8) =
      Z_to_bv 64 (bv_unsigned rsp - 40) := by
    unfold at_; u_norm; congr 1; omega
  apply cb_write_call _ _ _ (0x11048 : word)
    (Z_to_bv 64 (bv_unsigned rsp - 32)) (0x12000 : word) (Z_to_bv 64 6)
  all_goals try rw [Hs40]
  · decide +kernel
  · sym_regs HRA; sym_close
  · sym_regs HRA; sym_close
  · sym_regs HRA; sym_close
  · sym_regs HRA; sym_close
  · sym_regs HRA; sym_close
  · solve_store_ok
  · u_norm; omega
  · decide +kernel
  · change rdn source_segs _ (0x12000 : word) 6 = _
    repeat rw [rdn_wbytes_below _ _ _ _ _ _
      (by imm_norm; u_norm; omega)
      (by rw [length_N_to_le_bytes]; imm_norm; u_norm; omega)]
    rw [rdn_ext source_segs 6 _ (fun _ => none) _ (by decide +kernel)
      (by intro x Hx; apply wrap_mem_below; rw [stack_max_size_val]; revert Hx; imm_norm; u_norm; intro Hx; omega)]
    exact srom_hello
  · decide +kernel
  · intro regs' n Hn1 Hn2 _ R2 R10
    apply src_put_wall av ev uid hw rsp rrnd Hsp_lo Hsp_hi hello.length hello (0x12000 : word) n
    · omega
    · exact Hn1
    · exact Hn2
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact R10
    · exact R2
    · cbn_grows
    · rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [length_N_to_le_bytes]; imm_norm; u_norm; omega) (by u_norm; omega)]
      rewrite [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
      first | rfl | (congr 2; bveq)
    · repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [length_N_to_le_bytes]; imm_norm; u_norm; omega) (by u_norm; omega)]
      rewrite [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
      first | rfl | (congr 2; bveq)
    · repeat rw [rdn_wbytes_disjoint _ _ _ _ _ _
        (by rw [length_N_to_le_bytes]; imm_norm; u_norm; omega) (by u_norm; omega)]
      rewrite [rdn_wbytes_hit8 _ _ _ _ (by u_norm; omega)]
      first | rfl | (congr 2; bveq)
    · change rdn source_segs _ (0x12000 : word) 6 = _
      repeat rw [rdn_wbytes_below _ _ _ _ _ _
        (by imm_norm; u_norm; omega)
        (by rw [length_N_to_le_bytes]; imm_norm; u_norm; omega)]
      rw [rdn_ext source_segs 6 _ (fun _ => none) _ (by decide +kernel)
        (by intro x Hx; apply wrap_mem_below; rw [stack_max_size_val]; revert Hx; imm_norm; u_norm; intro Hx; omega)]
      exact srom_hello

include Hva Hve Hsp_lo Hsp_hi in
theorem source_err_o (Hge2 : 2 ≤ av.length)
    (Hb : byte_at (av.getD 1 []) 0 = Z_to_bv 8 111) :
    ∃ ms', msteps source_segs
      (init_machine_state source_segs 0x110a4 source_phdrs rsp rrnd av ev uid hw) ms' ∧
      ms'.ms_svc_pending = none ∧ step source_segs ms' = MachineFault := by
  have Hargc := valid_argv_len av Hva
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  obtain ⟨Hp1, Hp2⟩ := ptr1_bounds av ev Hva Hve rsp Hsp_hi Hge2
  sym_block_ex source_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
      (Z_to_bv 64 0x110a4) (wrap_mem source_phdrs rsp av ev uid hw rrnd)
      (seg_rom source_segs))
    23 [false, false, true, false] ([] : List expr)
    [((2 : reg), EVar 32)] [rsp] [argcN av, ptr1 av ev rsp, bval av] RA HRA Hms
  · cbn_sc
  · getr_resolve; rfl
  rw [init_mkst]
  refine ⟨_, Hms, rfl, ?_⟩
  apply LinuxProcessSemantics.Common.ErrEscape.step_lbu_fault
    (hfetch := SF_1108c) (hecall := rfl) (hdecode := SD_1108c)
  sym_regs HRA
  change rdn source_segs _ (Z_to_bv 64 64) 1 = none
  rw [rdn_wbytes_below _ _ _ _ _ _
    (by imm_norm; u_norm; omega)
    (by rw [length_N_to_le_bytes]; imm_norm; u_norm; omega)]
  rw [rdn_ext source_segs 1 _ (fun _ => none) _ (by decide +kernel)
    (by intro x Hx; apply wrap_mem_below; rw [stack_max_size_val]; revert Hx; imm_norm; u_norm; intro Hx; omega)]
  exact srom_64_none

end LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_source
