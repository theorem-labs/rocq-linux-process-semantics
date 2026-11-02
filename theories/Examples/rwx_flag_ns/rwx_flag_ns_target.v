(** * rwx-flag-ns TARGET binary (zig/lld, ordinary r-x code).

    PROOF-SIDE FILE (not part of the trusted specification).

    Delivers the one [to_wexit] derivation of the target binary: no
    output, exit 5, on every input.  The target's code is an ordinary
    immutable r-x segment, so this side is the standard static-fetch
    machinery — six instructions: form the data address, store 5 into
    the writable global, load it back, exit with it. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import rwx_flag_ns_code rwx_flag_ns_defs.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

Section TargetProof.

(** The launch, in the shape [Run.init_machine_state] now takes: the
    whole [State.ProcInput] record, the entry's mmap base, its stack
    pointer and its draw.  The argv and envp lists are fields of [inp]
    rather than separate arguments — Linux builds the entry block from
    the input itself ([create_elf_tables], fs/binfmt_elf.c, Linux
    v6.18.46, commit 1f99e9ab748f).  This side reads nothing off the
    initial stack, so it needs no launch conjunct and no argv or envp
    validity: it only has to name the state its six instructions run
    from. *)
Variable inp : ProcInput.

(** The initial stack pointer and the mmap base are QUANTIFIED (ASLR). *)
Variable asp amb : word.

(** The target run's own draw, independent of the source's
    (the [ed_random] and [ed_top] halves of [Run.ExecEntry]'s
    [en_draw]; see the source file). *)
Variable arnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned asp)%Z.
Hypothesis Hsp_hi : (bv_unsigned asp <= sp_window_hi)%Z.

Lemma asp_lo_num : (0x7fff80000000 <= bv_unsigned asp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma asp_hi_num : (bv_unsigned asp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

(** The vDSO pair the run appends after the image's own segments
    ([Run.run_segments]); the derivation never reaches it. *)
Local Abbreviation vt := (vdso_segments (in_kernel inp) asp amb).

Lemma target_wexit :
  to_wexit (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) 0x1001190 target_phdrs
       asp amb arnd inp)
    [] (Z_to_bv 64 5).
Proof.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  rewrite init_mkst. norm_pc.
  (* 0x1001190 lui a0, 0x1002 *)
  eapply tw_step;
    [ reflexivity
    | exact (step_lui _ _ _ _ _ _ _ _ (fetch_word_app target_segs vt _ _ TF_1001190)
               eq_refl TD_1001190)
    | step_simpl ].
  (* 0x1001194 li a1, 5 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 5);
      [ exact (fetch_word_app target_segs vt _ _ TF_1001194) | reflexivity
      | exact TD_1001194 | reflexivity
      | getr_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x1001198 sb a1, 424(a0) — the writable global := 5 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_sb_at with (a := Z_to_bv 64 0x10021a8)
        (v := Z_to_bv 64 5) (b := Z_to_bv 8 5);
      [ exact (fetch_word_app target_segs vt _ _ TF_1001198) | reflexivity
      | exact TD_1001198
      | getr_resolve; regupd_resolve; imm_norm; bveq
      | getr_resolve; regupd_resolve; reflexivity
      | bveq
      | apply (store_ok_app target_segs vt), target_store_ok; u_norm; cbn [Z.of_nat]; lia ]
    | step_simpl ].
  (* 0x100119c lbu a0, 424(a0) — read it back *)
  eapply tw_step;
    [ reflexivity
    | eapply step_lbu with (b := Z_to_bv 8 5);
      [ exact (fetch_word_app target_segs vt _ _ TF_100119c) | reflexivity
      | exact TD_100119c
      | getr_resolve; regupd_resolve; imm_norm; wlits_closed;
        change 1%nat with (length [Z_to_bv 8 5]);
        apply rdn_wbytes_hit; u_norm; cbn [length]; lia ]
    | step_simpl ].
  (* 0x10011a0 li a7, 93 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 93);
      [ exact (fetch_word_app target_segs vt _ _ TF_10011a0) | reflexivity
      | exact TD_10011a0 | reflexivity
      | getr_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x10011a4 ecall — exit(5) *)
  eapply tw_step;
    [ reflexivity
    | apply (step_ecall _ _ _ _ _ _ (fetch_word_app target_segs vt _ _ TF_10011a4) eq_refl)
    | ].
  apply tw_exit_coden.
  - getr_resolve; regupd_resolve; u_norm; lia.
  - regupd_resolve; bveq.
  - u_norm; lia.
Qed.

End TargetProof.
