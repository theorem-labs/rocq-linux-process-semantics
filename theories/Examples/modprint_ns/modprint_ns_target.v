(** * modprint-ns TARGET binary (zig -OReleaseSmall).

    PROOF-SIDE FILE (not part of the trusted specification).

    Delivers the single [to_wexit] derivation of the target binary:

      - [target_wexit] : for every input, write(1, mod_buf argc, 2)
                         then exit 0.

    The target has no libc: [_start] reads argc off the stack, calls
    [run] (which does the .bss load, the [remu], the [sb] and the write
    [ecall] inline) and exits.  Twenty instructions, no branches — the
    same observable behavior as the source's forty-odd, which is the
    point of the example.

    The run reads [Run.run_segments] (the image's segments, then the vDSO
    pair): the derivation steps over [target_segs ++ vt] with the pair an
    abstract tail [vt], each fetch carried there by
    [RunSegmentsLift.fetch_word_app]; the stack bounds come from the
    entry predicate's launch conjunct [Run.entry_launch_ok_va] and
    [Run.valid_launch], and the write's range passes [access_okb]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec MmapSim NumPrint StepTac StreamSim StoreOk RunSegmentsLift.
(** Not [Import]ed — see the note in [modprint_ns_source.v]. *)
From LinuxProcessSemantics.Common Require ArgvEnv.
From LinuxProcessSemantics.Examples.modprint_ns Require Import modprint_ns_code modprint_ns_defs.
From LinuxProcessSemantics.Examples.modprint_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.modprint_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivation runs from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them. *)
#[local] Instance modprint_ns_target_fx : FPState := fx0.

Section TargetProof.

Variable inp : ProcInput.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hvl : valid_launch inp.

(** The initial stack pointer, the program break and the mmap base are
    QUANTIFIED (ASLR), independently of the source's. *)
Variable asp abrk amb : word.

(** The target run's own draw, independent of the source's (the
    [ed_random] and [ed_top] halves of [Run.ExecEntry]'s [en_draw]; see
    the source file). *)
Variable arnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned asp)%Z.
Hypothesis Hsp_hi : (bv_unsigned asp <= sp_window_hi)%Z.

(** The launch conjunct of [Run.valid_entry_va]; see the source file. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry asp abrk amb arnd) inp.

(** As in [modprint_ns_source.v]: the startup scaffolding comes from
    [Common/ArgvEnv.v], instantiated here at the target's [asp]. *)

Lemma asp_lo_num : (0x7fff80000000 <= bv_unsigned asp)%Z.
Proof. apply (ArgvEnv.sp_lo_num asp); assumption. Qed.
Lemma asp_hi_num : (bv_unsigned asp <= 0x800000000000)%Z.
Proof. apply (ArgvEnv.sp_hi_num asp); assumption. Qed.

Definition argcA : word := ArgvEnv.argcN inp.

Lemma target_bsb_nw : forall entry : word,
  (bv_unsigned asp
   + Z.of_nat (length (entry_stack_image inp amb target_phdrs entry asp arnd)) < 2^64)%Z.
Proof.
  intros entry.
  apply (ArgvEnv.bsb_nw Sv48 inp amb target_phdrs entry asp abrk arnd); assumption.
Qed.

(* ================================================================= *)
(* The single behavior: write the digit and a newline, then exit 0.   *)
(* ================================================================= *)

Lemma target_wexit :
  to_wexit (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) 0x1001190 target_phdrs
       asp amb arnd inp)
    (mod_bufs (Z.of_nat (length (in_argv inp)))) (Z_to_bv 64 0).
Proof.
  (* the run's list is the image's followed by the vDSO pair; nothing
     below reads the pair, so it stays an abstract tail [vt] *)
  unfold run_segments.
  generalize (vdso_segments (in_kernel inp) asp amb) as vt. intros vt.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargc.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  pose proof (mod_rem_range (Z.of_nat (length (in_argv inp))) ltac:(lia)) as Hrem.
  unfold mod_bufs. rewrite mod_buf_bytes by lia.
  rewrite init_mkst. norm_pc.
  (* ---------------- _start prologue ---------------- *)
  (* 0x1001190: addi sp,sp,-16 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 (bv_unsigned asp - 16));
      [ exact (fetch_word_app _ _ _ _ TF_1001190) | reflexivity | exact TD_1001190 | reflexivity
      | getr_resolve; cbv beta; reduce_bv_eqb_ifs; sp_norm; f_equal; lia ]
    | norm_pc ].
  (* 0x1001194: sd ra,8(sp) -- ra is still its initial 0 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned asp - 8))
                             (v := Z_to_bv 64 0);
      [ exact (fetch_word_app _ _ _ _ TF_1001194) | reflexivity | exact TD_1001194
      | getr_resolve; regupd_resolve; sp_norm; f_equal; lia
      | getr_resolve; regupd_resolve; reflexivity
      | solve_store_ok ]
    | step_simpl ].
  (* 0x1001198: sd s0,0(sp) -- s0 is still its initial 0 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned asp - 16))
                             (v := Z_to_bv 64 0);
      [ exact (fetch_word_app _ _ _ _ TF_1001198) | reflexivity | exact TD_1001198
      | getr_resolve; regupd_resolve; rewrite v_addi_0; sp_norm; f_equal; lia
      | getr_resolve; regupd_resolve; reflexivity
      | solve_store_ok ]
    | step_simpl ].
  (* 0x100119c: addi s0,sp,16 -> the frame pointer is the entry sp *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := asp);
      [ exact (fetch_word_app _ _ _ _ TF_100119c) | reflexivity | exact TD_100119c | reflexivity
      | getr_resolve; regupd_resolve; sp_norm; apply bv_eq;
        rewrite u_Z2bv by lia; lia ]
    | norm_pc ].
  (* 0x10011a0: ld a0,0(s0) -- argc *)
  eapply tw_step;
    [ reflexivity
    | eapply step_ld with (bs := word_le8 argcA) (v := argcA);
      [ exact (fetch_word_app _ _ _ _ TF_10011a0) | reflexivity | exact TD_10011a0
      | match goal with |- rdn _ _ ?a _ = _ =>
          replace a with asp
            by (getr_resolve; regupd_resolve; rewrite v_addi_0; reflexivity) end;
        rewrite !rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia);
        rewrite rdn_wrap_stack_above by lia;
        apply read_argc; apply target_bsb_nw
      | exact (bytes_le_n_to_le_8 _) ]
    | step_simpl ].
  (* 0x10011a4: auipc ra,0x0 ; 0x10011a8: jalr 20(ra) -> run (0x10011b8) *)
  stepi (fetch_word_app _ vt _ _ TF_10011a4) TD_10011a4.
  stepjr (fetch_word_app _ vt _ _ TF_10011a8) TD_10011a8 (0x10011a4 : word)
    ltac:(getr_resolve; regupd_resolve; bveq).
  (* ---------------- run ---------------- *)
  (* 0x10011b8: lui a1,0x1002 -> 0x1002000 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_lui_at with (v := (0x1002000 : word));
      [ exact (fetch_word_app _ _ _ _ TF_10011b8) | reflexivity | exact TD_10011b8 | reflexivity
      | bveq ]
    | norm_pc ].
  (* 0x10011bc: lw a1,496(a1) -> a1 = modulus_base = 0.  THE step_lw_zero. *)
  eapply tw_step;
    [ reflexivity
    | eapply step_lw_zero;
      [ exact (fetch_word_app _ _ _ _ TF_10011bc) | reflexivity | exact TD_10011bc | reflexivity
      | match goal with |- rdn _ _ ?a _ = _ =>
          replace a with (0x10021f0 : word)
            by (getr_resolve; regupd_resolve; bveq) end;
        rewrite !rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia);
        erewrite rdn_ext;
          [ apply arom_zero4
          | imm_norm; lia
          | intros x Hx; revert Hx; imm_norm; intros Hx;
            eapply wrap_mem_below; [exact Hlau | rewrite stack_max_size_val; lia] ] ]
    | step_simpl ].
  (* 0x10011c0: addiw a1,a1,7 -> the divisor 7 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addiw_at with (v := Z_to_bv 64 7);
      [ exact (fetch_word_app _ _ _ _ TF_10011c0) | reflexivity | exact TD_10011c0 | reflexivity
      | getr_resolve; regupd_resolve; imm_norm; exact v_addiw_zero_7 ]
    | norm_pc ].
  (* 0x10011c4: remu a1,a0,a1 -> argc mod 7.  THE v_remu_small. *)
  eapply tw_step;
    [ reflexivity
    | eapply step_remu;
      [ exact (fetch_word_app _ _ _ _ TF_10011c4) | reflexivity | exact TD_10011c4
      | getr_resolve; regupd_resolve; rewrite u_Z2bv by lia; lia ]
    | step_simpl ].
  (* 0x10011c8: lui a2,0x1002 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_lui_at with (v := (0x1002000 : word));
      [ exact (fetch_word_app _ _ _ _ TF_10011c8) | reflexivity | exact TD_10011c8 | reflexivity
      | bveq ]
    | norm_pc ].
  (* 0x10011cc: li a7,64 ; 0x10011d0: li a0,1 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 64);
      [ exact (fetch_word_app _ _ _ _ TF_10011cc) | reflexivity | exact TD_10011cc | reflexivity
      | getr_resolve; exact v_addi_0_64 ]
    | norm_pc ].
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 1);
      [ exact (fetch_word_app _ _ _ _ TF_10011d0) | reflexivity | exact TD_10011d0 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* 0x10011d4: addi a1,a1,48 -> the ASCII digit (a 64-bit add here, not
     the source's addiw) *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 (48 + Z.of_nat (length (in_argv inp)) mod 7));
      [ exact (fetch_word_app _ _ _ _ TF_10011d4) | reflexivity | exact TD_10011d4 | reflexivity
      | getr_resolve; regupd_resolve; imm_norm;
        unfold argcA, ArgvEnv.argcN, len_word;
        rewrite (v_remu_7 (Z.of_nat (length (in_argv inp)))) by lia;
        apply v_addi_digit; lia ]
    | norm_pc ].
  (* 0x10011d8: sb a1,492(a2) -> patch out[0] at 0x10021ec *)
  eapply tw_step;
    [ reflexivity
    | eapply step_sb_at with (a := (0x10021ec : word))
                             (v := Z_to_bv 64 (48 + Z.of_nat (length (in_argv inp)) mod 7))
                             (b := Z_to_bv 8 (48 + Z.of_nat (length (in_argv inp)) mod 7));
      [ exact (fetch_word_app _ _ _ _ TF_10011d8) | reflexivity | exact TD_10011d8
      | getr_resolve; regupd_resolve; bveq
      | getr_resolve; regupd_resolve; reflexivity
      | apply stored_digit; lia
      | apply target_store_ok; imm_norm; lia ]
    | step_simpl ].
  (* 0x10011dc: addi a1,a2,492 -> 0x10021ec ; 0x10011e0: li a2,2 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := (0x10021ec : word));
      [ exact (fetch_word_app _ _ _ _ TF_10011dc) | reflexivity | exact TD_10011dc | reflexivity
      | getr_resolve; regupd_resolve; bveq ]
    | norm_pc ].
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 2);
      [ exact (fetch_word_app _ _ _ _ TF_10011e0) | reflexivity | exact TD_10011e0 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* 0x10011e4: ecall -- write(1, out, 2) *)
  eapply tw_step;
    [ reflexivity
    | apply (step_ecall _ _ _ _ _ _ (fetch_word_app _ _ _ _ TF_10011e4) eq_refl) | ].
  apply tw_write_ret.
  - getr_resolve. vm_compute. reflexivity.
  - regupd_resolve. reflexivity.
  - rewrite (ms_read_bytes_rdn (target_segs ++ vt)) by reflexivity.
    cbn [ms_mem ms_regs]. regupd_resolve.
    replace (word_to_nat (Z_to_bv 64 2)) with 2%nat by (vm_compute; reflexivity).
    apply (rdn_app (target_segs ++ vt) _ 1%nat 1%nat _
             [Z_to_bv 8 (48 + Z.of_nat (length (in_argv inp)) mod 7)] [nl]).
    + (* out[0]: the stored digit — the outermost store *)
      apply (rdn_wbytes_hit (target_segs ++ vt)
               [Z_to_bv 8 (48 + Z.of_nat (length (in_argv inp)) mod 7)]).
      cbn [length];
        match goal with |- (bv_unsigned ?a + _ <= _)%Z =>
          pose proof (u64_range a) end; lia.
    + (* out[1]: the newline, straight from the image *)
      match goal with |- rdn _ _ ?a _ = _ =>
        replace a with (0x10021ed : word) by bveq end.
      rewrite rdn_wbytes_disjoint by (cbn [length]; imm_norm; u_norm; lia).
      rewrite !rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
      erewrite rdn_ext;
        [ apply arom_nl
        | imm_norm; lia
        | intros x Hx; revert Hx; imm_norm; intros Hx;
          eapply wrap_mem_below; [exact Hlau | rewrite stack_max_size_val; lia] ].
  - (* the buffer range passes [access_ok]: a link-time address *)
    regupd_resolve. reflexivity.
  - cbn [length]; lia.
  - intros n Hn1 Hn2. norm_pc.
    (* 0x10011e8: ret -> 0x10011ac *)
    stepjr (fetch_word_app _ vt _ _ TF_10011e8) TD_10011e8 (0x10011ac : word)
      ltac:(getr_resolve; regupd_resolve; bveq).
    (* 0x10011ac: li a7,93 ; 0x10011b0: li a0,0 ; 0x10011b4: ecall *)
    stepi (fetch_word_app _ vt _ _ TF_10011ac) TD_10011ac.
    eapply tw_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 0);
        [ exact (fetch_word_app _ _ _ _ TF_10011b0) | reflexivity | exact TD_10011b0 | reflexivity
        | getr_resolve; rewrite v_addi_0; reflexivity ]
      | norm_pc ].
    eapply tw_step;
      [ reflexivity
      | apply (step_ecall _ _ _ _ _ _ (fetch_word_app _ _ _ _ TF_10011b4) eq_refl) | ].
    apply tw_exit_coden.
    + getr_resolve. vm_compute. reflexivity.
    + regupd_resolve. reflexivity.
    + u_norm; lia.
Qed.

End TargetProof.
