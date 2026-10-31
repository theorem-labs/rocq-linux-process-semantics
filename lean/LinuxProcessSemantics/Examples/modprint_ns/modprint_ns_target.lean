import LinuxProcessSemantics.Common.ArgvEnv
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_defs

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # modprint-ns: the target binary's single derivation

PROOF-SIDE, not trusted spec. Twins `theories/Examples/modprint_ns/modprint_ns_target.v`
at the baseline above. Rocq's section `TargetProof` variables and hypotheses
become explicit leading arguments, in the section's declaration order, of each
declaration that uses them.
-/

namespace LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_target

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_code
open LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_defs

theorem asp_lo_num (asp : word) (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) :
    0x7fff80000000 ≤ bv_unsigned asp :=
  Common.ArgvEnv.sp_lo_num asp Hsp_lo

theorem asp_hi_num (asp : word) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi) :
    bv_unsigned asp ≤ 0x800000000000 :=
  Common.ArgvEnv.sp_hi_num asp Hsp_hi

def argcA (av : List (List byte)) : word := Common.ArgvEnv.argcN av

theorem target_bsb_nw (av ev : List (List byte)) (uid hw : word) (Hva : valid_argv av)
    (Hve : valid_envp ev) (asp : word) (arnd : EntryDraw)
    (Hsp_hi : bv_unsigned asp ≤ sp_window_hi) :
    bv_unsigned asp + ((build_stack_bytes target_phdrs asp av ev uid hw arnd).length : Int)
      < 2 ^ 64 :=
  Common.ArgvEnv.bsb_nw target_phdrs asp av ev uid hw arnd Hva Hve Hsp_hi

open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.StepTac

/-- The single behavior: write the digit and a newline, then exit 0. -/
theorem target_wexit (av ev : List (List byte)) (uid hw : word) (Hva : valid_argv av)
    (Hve : valid_envp ev) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned asp) (Hsp_hi : bv_unsigned asp ≤ sp_window_hi) :
    to_wexit target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd av ev uid hw)
      (mod_bufs (av.length : Int)) (Z_to_bv 64 0) := by
  have Hargc := valid_argv_len av Hva
  have Hlo := asp_lo_num asp Hsp_lo
  have Hhi := asp_hi_num asp Hsp_hi
  have Hrem := mod_rem_range (av.length : Int) (by omega)
  unfold mod_bufs
  rw [mod_buf_bytes _ (by omega), init_mkst]
  norm_pc
  -- _start: allocate the frame and save ra and s0.
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 (bv_unsigned asp - 16))
      (hf := TF_1001190) (he := rfl) (hd := TD_1001190) (hrd := rfl)
    getr_resolve
    sp_norm
    rfl
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_sd_at (a := Z_to_bv 64 (bv_unsigned asp - 8)) (v := Z_to_bv 64 0)
      (hf := TF_1001194) (he := rfl) (hd := TD_1001194)
    · getr_resolve; regupd_resolve; sp_norm; congr 1 <;> omega
    · getr_resolve; regupd_resolve; rfl
    · apply store_ok_wrap_window
      · rw [stack_max_size_val]; u_norm; omega
      · u_norm; omega
  step_simpl
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_sd_at (a := Z_to_bv 64 (bv_unsigned asp - 16)) (v := Z_to_bv 64 0)
      (hf := TF_1001198) (he := rfl) (hd := TD_1001198)
    · getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0]
    · getr_resolve; regupd_resolve; rfl
    · apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
      apply store_ok_wrap_window
      · rw [stack_max_size_val]; u_norm; omega
      · u_norm; omega
  step_simpl
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := asp)
      (hf := TF_100119c) (he := rfl) (hd := TD_100119c) (hrd := rfl)
    getr_resolve; regupd_resolve; sp_norm
    apply bv_eq_of_unsigned
    u_norm; omega
  norm_pc
  -- The saved words lie below argc, so neither store changes its load.
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_ld (bs := word_le8 (argcA av)) (v := argcA av)
      (hfetch := TF_10011a0) (hecall := rfl) (hdecode := TD_10011a0)
    · getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0]
      rw [rdn_wbytes_disjoint, rdn_wbytes_disjoint, rdn_wrap_stack_above]
      · apply read_argc
        exact target_bsb_nw av ev uid hw Hva Hve asp arnd Hsp_hi
      all_goals first | (rw [length_N_to_le_bytes]; u_norm; omega) | omega
    · exact bytes_le_n_to_le_8 _
  step_simpl
  apply to_wexit.tw_step _ _ _ _ rfl
  · exact step_auipc _ _ _ _ _ _ _ _ TF_10011a4 rfl TD_10011a4
  step_simpl
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_jalr_link (tgt := 0x10011a4)
      (hf := TF_10011a8) (he := rfl) (hd := TD_10011a8) (hrd := rfl)
    getr_resolve; regupd_resolve; bveq
  norm_pc
  -- run: load the zero-initialized modulus base, then add seven.
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_lui_at (v := 0x1002000)
      (hf := TF_10011b8) (he := rfl) (hd := TD_10011b8) (hrd := rfl)
    bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_lw_zero (hf := TF_10011bc) (he := rfl) (hd := TD_10011bc) (hrd := rfl)
    getr_resolve; regupd_resolve
    change rdn _ _ (0x10021f0 : word) 4 = _
    rw [rdn_wbytes_below, rdn_wbytes_below]
    · rw [rdn_ext _ _ _ (fun _ => none)]
      · exact arom_zero4
      · decide +kernel
      · intro x Hx
        apply wrap_mem_below
        rw [stack_max_size_val]
        change 0x10021f0 ≤ bv_unsigned x ∧ bv_unsigned x < 0x10021f0 + 4 at Hx
        omega
    all_goals first | (rw [length_N_to_le_bytes]; u_norm; omega) | (imm_norm; u_norm; omega)
  step_simpl
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addiw_at (v := Z_to_bv 64 7)
      (hf := TF_10011c0) (he := rfl) (hd := TD_10011c0) (hrd := rfl)
    getr_resolve; regupd_resolve; imm_norm
    exact v_addiw_zero_7
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_remu (hf := TF_10011c4) (he := rfl) (hd := TD_10011c4)
    getr_resolve; regupd_resolve
    decide +kernel
  step_simpl
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_lui_at (v := 0x1002000)
      (hf := TF_10011c8) (he := rfl) (hd := TD_10011c8) (hrd := rfl)
    bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 64)
      (hf := TF_10011cc) (he := rfl) (hd := TD_10011cc) (hrd := rfl)
    getr_resolve; exact v_addi_0_64
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 1)
      (hf := TF_10011d0) (he := rfl) (hd := TD_10011d0) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 (48 + (av.length : Int) % 7))
      (hf := TF_10011d4) (he := rfl) (hd := TD_10011d4) (hrd := rfl)
    getr_resolve; regupd_resolve; imm_norm
    unfold argcA Common.ArgvEnv.argcN len_word
    rw [v_remu_7 _ (by omega) (by omega)]
    exact v_addi_digit _ Hrem
  norm_pc
  -- Patch the first byte of the output buffer with the ASCII digit.
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_sb (hfetch := TF_10011d8) (hecall := rfl) (hdecode := TD_10011d8)
    getr_resolve; regupd_resolve
    apply target_store_ok <;> decide +kernel
  step_simpl
  getr_resolve; regupd_resolve
  change to_wexit _ (mkst _ _ (wbytes _ (0x10021ec : word)
    [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (48 + (av.length : Int) % 7)))]) _) _ _
  rw [stored_digit _ Hrem]
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := 0x10021ec)
      (hf := TF_10011dc) (he := rfl) (hd := TD_10011dc) (hrd := rfl)
    getr_resolve; regupd_resolve; bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 2)
      (hf := TF_10011e0) (he := rfl) (hd := TD_10011e0) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · exact step_ecall _ _ _ _ _ _ TF_10011e4 rfl
  apply tw_write_ret
  · getr_resolve; decide +kernel
  · regupd_resolve; rfl
  · rw [ms_read_bytes_rdn target_segs _ _ _ rfl]
    dsimp only
    regupd_resolve
    change rdn _ _ _ 2 = _
    apply rdn_app _ _ 1 1 _ [Z_to_bv 8 (48 + (av.length : Int) % 7)] [nl]
    · apply rdn_wbytes_hit
      change (0x10021ec : Int) + 1 ≤ 2 ^ 64
      decide +kernel
    · change rdn _ _ (0x10021ed : word) 1 = _
      rw [rdn_wbytes_disjoint, rdn_wbytes_below, rdn_wbytes_below]
      · rw [rdn_ext _ _ _ (fun _ => none)]
        · exact arom_nl
        · decide +kernel
        · intro x Hx
          apply wrap_mem_below
          rw [stack_max_size_val]
          change 0x10021ed ≤ bv_unsigned x ∧ bv_unsigned x < 0x10021ed + 1 at Hx
          omega
      all_goals
        try rw [length_N_to_le_bytes]
        try simp only [List.length_cons, List.length_nil]
        imm_norm
        u_norm
        omega
  · exact Nat.le_succ _
  · intro n Hn1 Hn2
    norm_pc
    apply to_wexit.tw_step _ _ _ _ rfl
    · apply step_jalr_x0 (tgt := 0x10011ac)
        (hf := TF_10011e8) (he := rfl) (hd := TD_10011e8)
      getr_resolve; regupd_resolve; bveq
    norm_pc
    apply to_wexit.tw_step _ _ _ _ rfl
    · apply step_addi_at (v := Z_to_bv 64 93)
        (hf := TF_10011ac) (he := rfl) (hd := TD_10011ac) (hrd := rfl)
      getr_resolve; bveq
    norm_pc
    apply to_wexit.tw_step _ _ _ _ rfl
    · apply step_addi_at (v := Z_to_bv 64 0)
        (hf := TF_10011b0) (he := rfl) (hd := TD_10011b0) (hrd := rfl)
      getr_resolve; imm_norm; rw [v_addi_0]
    norm_pc
    apply to_wexit.tw_step _ _ _ _ rfl
    · exact step_ecall _ _ _ _ _ _ TF_10011b4 rfl
    apply tw_exit_coden
    · getr_resolve; decide +kernel
    · regupd_resolve; rfl
    · decide +kernel

end LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_target
