import LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_defs
import LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_hoare
import LinuxProcessSemantics.Common.ArgvEnv
import LinuxProcessSemantics.Common.SymTac
import LinuxProcessSemantics.Common.SymBranch
import LinuxProcessSemantics.Common.SymSide
import LinuxProcessSemantics.Common.Footprint
import LinuxProcessSemantics.Common.ErrEscape

/-! rocq-baseline: 36031418350290d5d51fae6e71cbf0b73d7cc91e -/

/-! conditional-bug-ns target binary: per-input execution derivations.
Proof-side symbolic dispatch, write-all retry loop, and explicit exit behavior.
The source additionally supplies the universal source-error escape witness. -/

namespace LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_target

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
variable (asp : word) (arnd : EntryDraw)
variable (Hsp_lo : sp_window_lo ≤ bv_unsigned asp)
variable (Hsp_hi : bv_unsigned asp ≤ sp_window_hi)

include Hsp_lo in
theorem asp_lo_num : 0x7fff80000000 ≤ bv_unsigned asp := Hsp_lo

include Hsp_hi in
theorem asp_hi_num : bv_unsigned asp ≤ 0x800000000000 := Hsp_hi

include Hva Hve Hsp_hi in
theorem target_bsb_nw :
    bv_unsigned asp + ((build_stack_bytes target_phdrs asp av ev uid hw arnd).length : Int) < 2^64 :=
  bsb_nw target_phdrs asp av ev uid hw arnd Hva Hve Hsp_hi

def aptr1 : word := cat_argv_ptr asp av ev 1

include Hva Hve Hsp_hi in
theorem aptr1_bounds (Hge2 : 2 ≤ av.length) :
    bv_unsigned asp ≤ bv_unsigned (aptr1 av ev asp) ∧
    bv_unsigned (aptr1 av ev asp) + ((av.getD 1 []).length : Int) + 1 < 2^64 :=
  argv_ptr_bounds_at asp av ev Hva Hve Hsp_hi 1 (by omega)

include Hva Hve Hsp_hi in
theorem aread_ptr1 (Hge2 : 2 ≤ av.length) :
    rdn target_segs (stack_to_mem asp (entry_stack_image target_phdrs asp av ev uid hw arnd))
      (asp + nat_to_word (8 + 8 * 1)) 8 = some (word_le8 (aptr1 av ev asp)) :=
  read_argv_ptr_k target_phdrs target_segs asp av ev 1 uid hw arnd (by omega)
    (target_bsb_nw av ev uid hw Hva Hve asp arnd Hsp_hi)

include Hva Hve Hsp_hi in
theorem aread_b (Hge2 : 2 ≤ av.length) :
    rdn target_segs (stack_to_mem asp (entry_stack_image target_phdrs asp av ev uid hw arnd))
      (aptr1 av ev asp) 1 = some [byte_at (av.getD 1 []) 0] := by
  have h := read_argv_byte_k target_phdrs target_segs asp av ev 1 0 uid hw arnd
    (by omega) (by omega) (target_bsb_nw av ev uid hw Hva Hve asp arnd Hsp_hi)
  rw [word_add_0] at h
  exact h

def abval : word := Z_to_bv 64 (bv_unsigned (byte_at (av.getD 1 []) 0))

theorem u_abval : bv_unsigned (abval av) = bv_unsigned (byte_at (av.getD 1 []) 0) :=
  u_zext8 _

def aargcN (av : List (List byte)) : word := len_word av

theorem u_aargcN (av : List (List byte)) (Hva : valid_argv av) :
    bv_unsigned (aargcN av) = (av.length : Int) := u_argcN av Hva

set_option hygiene false in
local macro "cbn_read_argc" : tactic => `(tactic| (
  rw [show Z_to_bv 64 (bv_unsigned asp + 0) = asp by
    apply bv_eq_of_unsigned; u_norm; omega]
  refine ⟨word_le8 (aargcN av), ?_, bytes_le_n_to_le_8 _⟩
  rw [rdn_wrap_stack_above target_segs _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
  exact read_argc target_phdrs target_segs asp av ev uid hw arnd
    (target_bsb_nw av ev uid hw Hva Hve asp arnd Hsp_hi)))

set_option hygiene false in
local macro "cbn_read_ptr1" : tactic => `(tactic| (
  rw [show Z_to_bv 64 (bv_unsigned asp + 16) = asp + nat_to_word (8 + 8 * 1) by
    rw [word_add_nat]; congr 1 <;> omega]
  refine ⟨word_le8 (aptr1 av ev asp), ?_, bytes_le_n_to_le_8 _⟩
  rw [rdn_wrap_stack_above target_segs _ _ _ _ _ _ _ _ _
    (by rw [word_add_nat]; u_norm; omega) (by rw [word_add_nat]; u_norm; omega)]
  exact aread_ptr1 av ev uid hw Hva Hve asp arnd Hsp_hi Hge2))

set_option hygiene false in
local macro "cbn_read_byte" : tactic => `(tactic| (
  rw [show Z_to_bv 64 (bv_unsigned (aptr1 av ev asp) + 0) = aptr1 av ev asp by
    apply bv_eq_of_unsigned; u_norm; omega]
  refine ⟨[byte_at (av.getD 1 []) 0], ?_, ?_⟩
  · rw [rdn_wrap_stack_above target_segs _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
    exact aread_b av ev uid hw Hva Hve asp arnd Hsp_hi Hge2
  · rw [bytes_le_single]
    change bv_unsigned (byte_at (av.getD 1 []) 0) = bv_unsigned (abval av)
    exact (u_abval av).symm))

set_option hygiene false in
local macro "cbn_argc_br" : tactic => `(tactic| (
  try rw [Bool.not_eq_true']
  try rw [Bool.not_eq_false']
  rw [bv_ltu_Z]
  first | rw [decide_eq_true_eq] | rw [decide_eq_false_iff_not]
  u_norm
  rw [u_aargcN av Hva]
  omega))

set_option hygiene false in
local macro "cbn_sc" : tactic => `(tactic| (
  repeat' first
  | apply And.intro
  | decide +kernel
  | omega
  | cbn_argc_br
  | cbn_read_byte
  | cbn_read_ptr1
  | cbn_read_argc
  | solve_store_ok
  | (unfold abval; rw [Hb]; decide +kernel)
  | ((first | rw [Bool.not_eq_true'] | rw [Bool.not_eq_false'] | skip)
     unfold abval
     first
     | exact c_eq_zext_lit_false _ 110 (by omega) Hn110
     | exact c_eq_zext_lit_false _ 104 (by omega) Hn104
     | exact c_eq_zext_lit_false _ 111 (by omega) Hn111)))

include Hva Hve Hsp_lo Hsp_hi in
theorem target_wexit_lt2 (Hlt2 : av.length < 2) :
    to_wexit target_segs
      (init_machine_state target_segs 0x1001160 target_phdrs asp arnd av ev uid hw)
      [] (Z_to_bv 64 2) := by
  have Hargc := valid_argv_len av Hva
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  rw [init_mkst]
  norm_pc
  sym_block target_segs 20 [false] ([] : List expr)
    [((2 : reg), EVar 32)] [asp] [aargcN av] RA HRA
  · cbn_sc
  · getr_resolve; rfl
  apply to_wexit.tw_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_1001184 rfl)
  apply tw_exit_coden
  · sym_regs HRA; sym_close
  · sym_regs HRA; sym_close
  · u_norm; omega

include Hva Hve Hsp_lo Hsp_hi in
theorem target_wexit_n (Hge2 : 2 ≤ av.length)
    (Hb : byte_at (av.getD 1 []) 0 = Z_to_bv 8 110) :
    to_wexit target_segs
      (init_machine_state target_segs 0x1001160 target_phdrs asp arnd av ev uid hw)
      [] (Z_to_bv 64 0) := by
  have Hargc := valid_argv_len av Hva
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  obtain ⟨Hp1, Hp2⟩ := aptr1_bounds av ev Hva Hve asp Hsp_hi Hge2
  rw [init_mkst]
  norm_pc
  sym_block target_segs 25 [true, false, true] ([] : List expr)
    [((2 : reg), EVar 32)] [asp] [aargcN av, aptr1 av ev asp, abval av] RA HRA
  · cbn_sc
  · getr_resolve; rfl
  apply to_wexit.tw_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_1001184 rfl)
  apply tw_exit_coden
  · sym_regs HRA; sym_close
  · sym_regs HRA; sym_close
  · u_norm; omega

include Hva Hve Hsp_lo Hsp_hi in
theorem target_wexit_other (Hge2 : 2 ≤ av.length)
    (Hn110 : byte_at (av.getD 1 []) 0 ≠ Z_to_bv 8 110)
    (Hn104 : byte_at (av.getD 1 []) 0 ≠ Z_to_bv 8 104)
    (Hn111 : byte_at (av.getD 1 []) 0 ≠ Z_to_bv 8 111) :
    to_wexit target_segs
      (init_machine_state target_segs 0x1001160 target_phdrs asp arnd av ev uid hw)
      [] (Z_to_bv 64 3) := by
  have Hargc := valid_argv_len av Hva
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  obtain ⟨Hp1, Hp2⟩ := aptr1_bounds av ev Hva Hve asp Hsp_hi Hge2
  rw [init_mkst]
  norm_pc
  sym_block target_segs 25 [true, false, false, true] ([] : List expr)
    [((2 : reg), EVar 32)] [asp] [aargcN av, aptr1 av ev asp, abval av] RA HRA
  · cbn_sc
  · getr_resolve; rfl
  apply to_wexit.tw_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_1001184 rfl)
  apply tw_exit_coden
  · sym_regs HRA; sym_close
  · sym_regs HRA; sym_close
  · u_norm; omega

/-- After each nonempty delivery, the remainder strictly shrinks. -/
theorem tgt_put_wall (fuel : Nat) (rest : List byte) (p : word) (n : Nat)
    (regs : bvmap 5 word) (mem : word → Option byte)
    (Hfuel : rest.length ≤ fuel) (Hn1 : 1 ≤ n) (Hn2 : n ≤ rest.length)
    (Hlen : (rest.length : Int) ≤ 6)
    (Hplo : 0x1000158 ≤ bv_unsigned p)
    (Hphi : bv_unsigned p + (rest.length : Int) ≤ 0x100015e)
    (H10 : reg_get regs 10 = len_word (rest.take n))
    (H11 : reg_get regs 11 = p) (H12 : reg_get regs 12 = len_word rest)
    (H1 : reg_get regs 1 = (0x1001180 : word))
    (H17 : bv_unsigned (reg_get regs 17) = 64)
    (Hread : rdn target_segs mem p rest.length = some rest) :
    to_wall_tail target_segs (Z_to_bv 64 1)
      (mkst regs 0x10011d4 mem (seg_rom target_segs)) (rest.drop n)
      (to_wallexit target_segs (Z_to_bv 64 1) [] (Z_to_bv 64 0)) := by
  induction fuel generalizing rest p n regs mem with
  | zero => omega
  | succ fuel IH =>
    step_intro
    · rfl
    · apply step_bge_ft (hf := TF_10011d4) (he := rfl) (hd := TD_10011d4)
      getr_resolve
      rw [H10]
      apply c_lts_0_pos <;>
        (rw [u_len_word_firstn n rest Hn2 (by omega)]; omega)
    norm_pc
    stepiv TF_10011d8 TD_10011d8 (Z_to_bv 64 (bv_unsigned p + (n : Int)))
      (getr_resolve; rw [H11, H10]; apply v_add_len_firstn_Z <;> omega)
    stepiv TF_10011dc TD_10011dc (len_word (rest.drop n))
      (getr_resolve; rw [H12, H10]; apply v_sub_len_firstn <;> omega)
    by_cases Hne : n = rest.length
    · subst n
      rw [List.drop_length]
      apply to_wall_tail.twt_done
      change to_wexit target_segs _ [] (Z_to_bv 64 0)
      step_intro
      · rfl
      · apply step_beq_tk (hf := TF_10011e0) (he := rfl) (hd := TD_10011e0)
        getr_resolve
        rfl
      norm_pc
      stepiv TF_10011ec TD_10011ec (Z_to_bv 64 0) (getr_resolve; bveq)
      stepjr TF_10011f0 TD_10011f0 (0x1001180 : word) (getr_resolve; exact H1)
      stepiv TF_1001180 TD_1001180 (Z_to_bv 64 93) (getr_resolve; bveq)
      apply to_wexit.tw_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_1001184 rfl)
      apply tw_exit_coden
      · getr_resolve; rfl
      · regupd_resolve; rfl
      · decide +kernel
    · have Hdrop : ((rest.drop n).length : Int) < 2^64 := by
        rw [List.length_drop]; omega
      have Hsk := rdn_skipn target_segs mem rest.length p rest n Hread Hn2
      rw [word_add_nat_Z p n (by omega)] at Hsk
      have Hsk' : rdn target_segs mem (Z_to_bv 64 (bv_unsigned p + (n : Int)))
          (rest.drop n).length = some (rest.drop n) := by
        rw [List.length_drop]; exact Hsk
      step_intro
      · rfl
      · apply step_beq_ft (hf := TF_10011e0) (he := rfl) (hd := TD_10011e0)
        getr_resolve
        apply c_eq_0_false
        rw [u_len_word _ Hdrop, List.length_drop]
        omega
      norm_pc
      stepj TF_10011e4 TD_10011e4
      stepiv TF_10011cc TD_10011cc (Z_to_bv 64 1) (getr_resolve; bveq)
      apply to_wall_tail.twt_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d0 rfl)
      apply to_wall_tail.twt_more
      · rw [List.length_drop]; omega
      apply twl_write_rec target_segs (Z_to_bv 64 1)
      · getr_resolve; exact H17
      · regupd_resolve; rfl
      · rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
        dsimp only [machine_state.ms_mem]
        regupd_resolve
        have Hwn : word_to_nat (len_word (rest.drop n)) = (rest.drop n).length := by
          exact Int.ofNat_inj.mp (u_len_word _ Hdrop)
        rw [Hwn]
        exact Hsk'
      · rw [List.length_drop]; omega
      · intro m Hm1 Hm2
        norm_pc
        apply IH (rest.drop n) (Z_to_bv 64 (bv_unsigned p + (n : Int))) m
        · rw [List.length_drop]; omega
        · exact Hm1
        · exact Hm2
        · rw [List.length_drop]; omega
        · u_norm; omega
        · u_norm; rw [List.length_drop]; omega
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; rfl
        · regupd_resolve; exact H1
        · regupd_resolve; exact H17
        · exact Hsk'

include Hva Hve Hsp_lo Hsp_hi in
theorem target_wexit_h (Hge2 : 2 ≤ av.length)
    (Hb : byte_at (av.getD 1 []) 0 = Z_to_bv 8 104) :
    to_wallexit target_segs (Z_to_bv 64 1) [hello] (Z_to_bv 64 0)
      (init_machine_state target_segs 0x1001160 target_phdrs asp arnd av ev uid hw) := by
  have Hargc := valid_argv_len av Hva
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  obtain ⟨Hp1, Hp2⟩ := aptr1_bounds av ev Hva Hve asp Hsp_hi Hge2
  refine ⟨by decide +kernel, ?_⟩
  rw [init_mkst]
  norm_pc
  sym_block target_segs 30 [true, false, false, false, false] ([] : List expr)
    [((2 : reg), EVar 32)] [asp] [aargcN av, aptr1 av ev asp, abval av] RA HRA
  · cbn_sc
  · getr_resolve; rfl
  have Ha0 : getr RA 10 = Z_to_bv 64 1 := by sym_regs HRA; sym_close
  have Ha1 : getr RA 11 = (0x1000158 : word) := by sym_regs HRA; sym_close
  have Ha2 : getr RA 12 = Z_to_bv 64 6 := by sym_regs HRA; sym_close
  have Ha7 : getr RA 17 = Z_to_bv 64 64 := by sym_regs HRA; sym_close
  have Hra : getr RA 1 = (0x1001180 : word) := by sym_regs HRA; sym_close
  apply to_wall_tail.twt_step _ _ _ _ rfl (step_ecall _ _ _ _ _ _ TF_10011d0 rfl)
  apply to_wall_tail.twt_more
  · decide +kernel
  apply twl_write_rec target_segs (Z_to_bv 64 1)
  · rw [Ha7]; rfl
  · exact Ha0
  · rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
    change rdn target_segs _ (getr RA 11) (word_to_nat (getr RA 12)) = _
    rw [Ha1, Ha2]
    change rdn target_segs _ (0x1000158 : word) 6 = _
    repeat rw [rdn_wbytes_below _ _ _ _ _ _
      (by imm_norm; u_norm; omega)
      (by rw [length_N_to_le_bytes]; imm_norm; u_norm; omega)]
    rw [rdn_ext target_segs 6 _ (fun _ => none) _ (by decide +kernel)
      (by intro x Hx; apply wrap_mem_below; rw [stack_max_size_val]; revert Hx; imm_norm; u_norm; intro Hx; omega)]
    exact arom_hello
  · decide +kernel
  · intro n Hn1 Hn2
    norm_pc
    apply tgt_put_wall hello.length hello (0x1000158 : word) n
    · omega
    · exact Hn1
    · exact Hn2
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · regupd_resolve; rfl
    · regupd_resolve; exact Ha1
    · regupd_resolve; exact Ha2
    · regupd_resolve; exact Hra
    · regupd_resolve
      change bv_unsigned (getr RA 17) = 64
      rw [Ha7]; rfl
    · change rdn target_segs _ (0x1000158 : word) 6 = _
      repeat rw [rdn_wbytes_below _ _ _ _ _ _
        (by imm_norm; u_norm; omega)
        (by rw [length_N_to_le_bytes]; imm_norm; u_norm; omega)]
      rw [rdn_ext target_segs 6 _ (fun _ => none) _ (by decide +kernel)
        (by intro x Hx; apply wrap_mem_below; rw [stack_max_size_val]; revert Hx; imm_norm; u_norm; intro Hx; omega)]
      exact arom_hello

end LinuxProcessSemantics.Examples.conditional_bug_ns.conditional_bug_ns_target
