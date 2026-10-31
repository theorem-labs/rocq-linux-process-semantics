import LinuxProcessSemantics.Common.ArgvEnv
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Common.SymExec
import LinuxProcessSemantics.Common.SymTac
import LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_defs
import LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_hoare

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # modprint-ns: the source binary's single derivation

PROOF-SIDE, not trusted spec. Twins `theories/Examples/modprint_ns/modprint_ns_source.v`
at the baseline above. Rocq's section `SourceProof` variables and hypotheses
become explicit leading arguments, in the section's declaration order, of each
declaration that uses them. Rocq's section instances `argcN`, `u_argcN`,
`envp_ptr` and `envp_ptr_eq` are not redeclared: the proofs name
`Common/ArgvEnv.lean`'s, passing `rsp` and `av` explicitly.
-/

namespace LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_source

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.Common.ArgvEnv (argcN u_argcN envp_ptr envp_ptr_eq)
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.SymExec
open LinuxProcessSemantics.Common.SymTac
open LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_code
open LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_defs
open LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_hoare

/-- main's epilogue and the crt exit tail, standalone over an abstract entry
register file, memory and frame base: the two registers the `exit` ecall
reads, and the steps to it. -/
theorem source_main_epilogue (regs : bvmap 5 word) (mem rom : word → Option byte)
    (sp0 : word) (Hsp : getr regs 2 = sp0) (_Hnw : bv_unsigned sp0 + 16 ≤ 2 ^ 64)
    (Hrd : ∃ bs, rdn source_segs mem (Z_to_bv 64 (bv_unsigned sp0 + 8)) 8 = some bs ∧
      bytes_le_to_Z bs = 0x1106c) :
    ∃ R, getr R 10 = Z_to_bv 64 0 ∧ getr R 17 = Z_to_bv 64 93 ∧
      msteps source_segs
        (mkst regs (Z_to_bv 64 0x11034) mem rom)
        (mkst R (Z_to_bv 64 0x11070) mem rom) := by
  obtain ⟨bs, Hr, Hv⟩ := Hrd
  let R := regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x1106c))
    10 (Z_to_bv 64 0)) 2 (v_addi sp0 16)) 17 (Z_to_bv 64 93)
  refine ⟨R, ?_, ?_, ?_⟩
  · dsimp only [R]; getr_resolve; regupd_resolve; rfl
  · dsimp only [R]; getr_resolve; regupd_resolve; rfl
  apply msteps.mst_step _ _ _ rfl
  · apply step_ld (bs := bs) (v := Z_to_bv 64 0x1106c)
      (hfetch := SF_11034) (hecall := rfl) (hdecode := SD_11034)
    · rw [Hsp]; exact Hr
    · exact Hv
  step_simpl
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 0)
      (hf := SF_11038) (he := rfl) (hd := SD_11038) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := v_addi sp0 16)
      (hf := SF_1103c) (he := rfl) (hd := SD_1103c) (hrd := rfl)
    getr_resolve; regupd_resolve
    change v_addi (getr regs 2) 16 = v_addi sp0 16
    rw [Hsp]
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_jalr_x0 (tgt := Z_to_bv 64 0x1106c)
      (hf := SF_11040) (he := rfl) (hd := SD_11040)
    getr_resolve; regupd_resolve; rfl
  norm_pc
  apply msteps.mst_step _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 93)
      (hf := SF_1106c) (he := rfl) (hd := SD_1106c) (hrd := rfl)
    getr_resolve; bveq
  exact msteps.mst_refl _

theorem rsp_lo_num (rsp : word) (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) :
    0x7fff80000000 ≤ bv_unsigned rsp :=
  Common.ArgvEnv.sp_lo_num rsp Hsp_lo

theorem rsp_hi_num (rsp : word) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    bv_unsigned rsp ≤ 0x800000000000 :=
  Common.ArgvEnv.sp_hi_num rsp Hsp_hi

theorem source_bsb_nw (av ev : List (List byte)) (uid hw : word) (Hva : valid_argv av)
    (Hve : valid_envp ev) (rsp : word) (rrnd : EntryDraw)
    (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    bv_unsigned rsp + ((build_stack_bytes source_phdrs rsp av ev uid hw rrnd).length : Int)
      < 2 ^ 64 :=
  Common.ArgvEnv.bsb_nw source_phdrs rsp av ev uid hw rrnd Hva Hve Hsp_hi

/-- The value main's `sb a0,0(a1)` at 0x11024 stores into `out[0]`, in the spec's spelling. -/
theorem stored_digit_val (av : List (List byte)) (Hva : valid_argv av)
    (Hn : 0 ≤ (av.length : Int) ∧ (av.length : Int) < 2 ^ 64) :
    v_addiw (mul_div .M_REMU (argcN av) (v_addiw (v_lw (Z_to_bv 64 0)) 7)) 48
      = Z_to_bv 64 (48 + (av.length : Int) % 7) := by
  have Hrem := mod_rem_range (av.length : Int) Hn.1
  have H7 : v_addiw (v_lw (Z_to_bv 64 0)) 7 = Z_to_bv 64 7 := by decide +kernel
  rw [H7, m_remu _ _ (by decide +kernel)]
  have Ha : argcN av = Z_to_bv 64 (av.length : Int) := by
    apply bv_eq_of_unsigned
    rw [u_argcN av Hva, Common.StepTac.u_Z2bv _ Hn.1 Hn.2]
  rw [Ha, v_remu_7 _ Hn.1 Hn.2]
  exact v_addiw_digit _ Hrem

/-- The single behavior: write the digit and a newline, then exit 0. -/
theorem source_wexit (av ev : List (List byte)) (uid hw : word) (Hva : valid_argv av)
    (Hve : valid_envp ev) (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : sp_window_lo ≤ bv_unsigned rsp) (Hsp_hi : bv_unsigned rsp ≤ sp_window_hi) :
    to_wexit source_segs
      (init_machine_state source_segs 0x11044 source_phdrs rsp rrnd av ev uid hw)
      (mod_bufs (av.length : Int)) (Z_to_bv 64 0) := by
  have Hargc := valid_argv_len av Hva
  have Hlo := rsp_lo_num rsp Hsp_lo
  have Hhi := rsp_hi_num rsp Hsp_hi
  have Hrem := mod_rem_range (av.length : Int) (by omega)
  unfold mod_bufs
  rw [mod_buf_bytes _ (by omega), init_mkst]
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_auipc_at (v := 0x13044)
      (hf := SF_11044) (he := rfl) (hd := SD_11044) (hrd := rfl)
    bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := 0x13800)
      (hf := SF_11048) (he := rfl) (hd := SD_11048) (hrd := rfl)
    getr_resolve; regupd_resolve; bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_ld (bs := word_le8 (argcN av)) (v := argcN av)
      (hfetch := SF_1104c) (hecall := rfl) (hdecode := SD_1104c)
    · getr_resolve; regupd_resolve; imm_norm; rw [v_addi_0]
      rw [rdn_wrap_stack_above]
      · apply read_argc
        exact source_bsb_nw av ev uid hw Hva Hve rsp rrnd Hsp_hi
      all_goals omega
    · exact bytes_le_n_to_le_8 _
  step_simpl
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 (bv_unsigned rsp + 8))
      (hf := SF_11050) (he := rfl) (hd := SD_11050) (hrd := rfl)
    getr_resolve; regupd_resolve; sp_norm; rfl
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_slli_at (v := v_slli (argcN av) 3)
      (hf := SF_11054) (he := rfl) (hd := SD_11054) (hrd := rfl)
    getr_resolve; regupd_resolve; rfl
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_add_at (v := v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli (argcN av) 3))
      (hf := SF_11058) (he := rfl) (hd := SD_11058) (hrd := rfl)
    getr_resolve; regupd_resolve; rfl
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := envp_ptr rsp av)
      (hf := SF_1105c) (he := rfl) (hd := SD_1105c) (hrd := rfl)
    getr_resolve; regupd_resolve
    exact envp_ptr_eq rsp av Hva Hsp_lo Hsp_hi
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := 0x13010)
      (hf := SF_11060) (he := rfl) (hd := SD_11060) (hrd := rfl)
    getr_resolve; regupd_resolve; bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_sd_at (a := 0x13010) (v := envp_ptr rsp av)
      (hf := SF_11064) (he := rfl) (hd := SD_11064)
    · getr_resolve; regupd_resolve; bveq
    · getr_resolve; regupd_resolve; rfl
    · apply source_store_ok <;> decide +kernel
  step_simpl
  apply to_wexit.tw_step _ _ _ _ rfl
  · exact step_jal_link _ _ _ _ _ _ _ _ SF_11068 rfl SD_11068
  step_simpl
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_lui_at (v := 0x13000)
      (hf := SF_11000) (he := rfl) (hd := SD_11000) (hrd := rfl)
    bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_lw_zero (hf := SF_11004) (he := rfl) (hd := SD_11004) (hrd := rfl)
    getr_resolve; regupd_resolve
    change rdn _ _ (0x13008 : word) 4 = _
    rw [rdn_wbytes_below]
    · rw [rdn_ext _ _ _ (fun _ => none)]
      · exact srom_zero4
      · decide +kernel
      · intro x Hx
        apply wrap_mem_below
        rw [stack_max_size_val]
        change 0x13008 ≤ bv_unsigned x ∧ bv_unsigned x < 0x13008 + 4 at Hx
        omega
    all_goals try rw [length_N_to_le_bytes]
    all_goals decide +kernel
  step_simpl
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_lui_at (v := 0x13000)
      (hf := SF_11008) (he := rfl) (hd := SD_11008) (hrd := rfl)
    bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 (bv_unsigned rsp - 16))
      (hf := SF_1100c) (he := rfl) (hd := SD_1100c) (hrd := rfl)
    getr_resolve; regupd_resolve; sp_norm; rfl
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addiw_at (v := Z_to_bv 64 7)
      (hf := SF_11010) (he := rfl) (hd := SD_11010) (hrd := rfl)
    getr_resolve; regupd_resolve; bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_remu (hf := SF_11014) (he := rfl) (hd := SD_11014)
    getr_resolve; regupd_resolve; decide +kernel
  step_simpl
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 2)
      (hf := SF_11018) (he := rfl) (hd := SD_11018) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_sd_at (a := Z_to_bv 64 (bv_unsigned rsp - 8)) (v := 0x1106c)
      (hf := SF_1101c) (he := rfl) (hd := SD_1101c)
    · getr_resolve; regupd_resolve; sp_norm; congr 1 <;> omega
    · getr_resolve; regupd_resolve; bveq
    · apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
      apply store_ok_wrap_window
      · rw [stack_max_size_val]; u_norm; omega
      · u_norm; omega
  step_simpl
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addiw_at (v := Z_to_bv 64 (48 + (av.length : Int) % 7))
      (hf := SF_11020) (he := rfl) (hd := SD_11020) (hrd := rfl)
    getr_resolve; regupd_resolve; imm_norm
    unfold argcN len_word
    rw [v_remu_7 _ (by omega) (by omega)]
    exact v_addiw_digit _ Hrem
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_sb (hfetch := SF_11024) (hecall := rfl) (hdecode := SD_11024)
    getr_resolve; regupd_resolve
    apply source_store_ok <;> decide +kernel
  step_simpl
  getr_resolve; regupd_resolve
  change to_wexit _ (mkst _ _ (wbytes _ (0x13000 : word)
    [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (48 + (av.length : Int) % 7)))]) _) _ _
  rw [stored_digit _ Hrem]
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := 0x13000)
      (hf := SF_11028) (he := rfl) (hd := SD_11028) (hrd := rfl)
    getr_resolve; regupd_resolve; bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · apply step_addi_at (v := Z_to_bv 64 1)
      (hf := SF_1102c) (he := rfl) (hd := SD_1102c) (hrd := rfl)
    getr_resolve; bveq
  norm_pc
  apply to_wexit.tw_step _ _ _ _ rfl
  · exact step_jal_link _ _ _ _ _ _ _ _ SF_11030 rfl SD_11030
  step_simpl
  have Hs24 : Common.Hoare.at_ (Z_to_bv 64 (bv_unsigned rsp - 16)) (-8) =
      Z_to_bv 64 (bv_unsigned rsp - 24) := by
    unfold Common.Hoare.at_
    u_norm
    congr 1 <;> omega
  apply modprint_write_call _ _ (Z_to_bv 64 (bv_unsigned rsp - 16)) (0x13000 : word)
  · getr_resolve; regupd_resolve; rfl
  · getr_resolve; regupd_resolve; rfl
  · getr_resolve; regupd_resolve; rfl
  · getr_resolve; regupd_resolve; rfl
  · getr_resolve; regupd_resolve; rfl
  · rw [Hs24]
    apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
    apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
    apply store_ok_mono _ _ _ _ _ (wbytes_grows _ _ _)
    apply store_ok_wrap_window
    · rw [stack_max_size_val]; u_norm; omega
    · u_norm; omega
  · rw [Hs24]; u_norm; omega
  · rw [Hs24]
    apply rdn_app _ _ 1 1 _ [Z_to_bv 8 (48 + (av.length : Int) % 7)] [nl]
    · rw [rdn_wbytes_below]
      · apply rdn_wbytes_hit
        change (0x13000 : Int) + 1 ≤ 2 ^ 64
        decide +kernel
      all_goals try rw [length_N_to_le_bytes]
      all_goals imm_norm; u_norm; omega
    · change rdn _ _ (0x13001 : word) 1 = _
      rw [rdn_wbytes_below, rdn_wbytes_disjoint, rdn_wbytes_below, rdn_wbytes_below]
      · rw [rdn_ext _ _ _ (fun _ => none)]
        · exact srom_nl
        · decide +kernel
        · intro x Hx
          apply wrap_mem_below
          rw [stack_max_size_val]
          change 0x13001 ≤ bv_unsigned x ∧ bv_unsigned x < 0x13001 + 1 at Hx
          omega
      all_goals
        try rw [length_N_to_le_bytes]
        try simp only [List.length_cons, List.length_nil]
        imm_norm
        u_norm
        omega
  · rw [Hs24]
    intro regs' n Hn1 Hn2 R1 R2 R10
    generalize hm : wbytes _ _ _ = mem
    have Hrd : ∃ bs, rdn source_segs mem
        (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 16)) + 8)) 8 = some bs ∧
        bytes_le_to_Z bs = 0x1106c := by
      rw [← hm]
      u_norm
      have Ha : bv_unsigned rsp - 16 + 8 = bv_unsigned rsp - 8 := by omega
      rw [Ha]
      refine ⟨word_to_le_bytes 8 (0x1106c : word), ?_, ?_⟩
      · rw [rdn_wbytes_disjoint, rdn_wbytes_disjoint, rdn_wbytes_hit8]
        all_goals
          try rw [length_N_to_le_bytes]
          try simp only [List.length_cons, List.length_nil]
          imm_norm
          u_norm
          omega
      · rw [bytes_le_to_Z_8]
        decide +kernel
    obtain ⟨RB, HB10, HB17, Hms⟩ := source_main_epilogue regs' _ _
      (Z_to_bv 64 (bv_unsigned rsp - 16)) R2 (by u_norm; omega) Hrd
    sym_chain Hms
    apply to_wexit.tw_step _ _ _ _ rfl
    · exact step_ecall _ _ _ _ _ _ SF_11070 rfl
    apply tw_exit_coden
    · rw [HB17]; decide +kernel
    · rw [← getr_nz _ _ (by reg_neq_tac)]
      exact HB10
    · decide +kernel

end LinuxProcessSemantics.Examples.modprint_ns.modprint_ns_source
