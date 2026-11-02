(** * rwx-flag-ns SOURCE binary (musl-gcc -Os, single RWX LOAD segment).

    PROOF-SIDE FILE (not part of the trusted specification).

    Delivers the one [to_wexit] derivation of the source binary: no
    output, exit 5, on every valid input.

    Every fetch of this binary goes through the overlay-aware w+x path
    ([RiscvSemantics.fetch_word_ov]): the image is a single RWX LOAD
    segment, so the static [fetch_word] declines everywhere
    ([source_no_ro_exec]).  Each step closes its fetch from the
    generated static [fetch_word_wx] fact via [WxExec.wx_fetch_intro],
    whose overlay side condition is the FRAME INVARIANT "the overlay
    misses .text = [0x10078, 0x100e4)" — established on the initial
    state ([mem_clear_wrap]: the initial overlay is the stack image,
    far above the loaded segment) and re-established across each store
    by [mem_clear_wbytes] (both stores land at/above 0x100e4, i.e.
    outside the code: this is precisely the no-self-modifying-code
    condition).  The [lbu] then reads the byte the [sb] just wrote out
    of the overlay ([rdn_wbytes_hit]) — through the very same memory
    view fetch uses. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import rwx_flag_ns_code rwx_flag_ns_defs.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

Section SourceProof.

(** The launch, as [Run.init_machine_state] now takes it: the whole
    [State.ProcInput] record, the entry's mmap base, its stack pointer,
    its program break and its draw.  The argv and envp lists, the
    credentials, AT_HWCAP and the exec file name are FIELDS of [inp]
    rather than separate arguments, because Linux builds the entry
    block from exactly those ([create_elf_tables], fs/binfmt_elf.c,
    Linux v6.18.46, commit 1f99e9ab748f), and the stack VMA's end is
    [StackLayout.ed_top] of the draw.  So one [State.ProcInput] and one
    [StackLayout.EntryDraw] fix the whole initial stack image.  The
    shared form of this scaffolding is [Common.ArgvEnv]; it is written
    out here because this file predates that module. *)
Variable inp : ProcInput.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hvl : valid_launch inp.

(** The initial stack pointer is QUANTIFIED (ASLR): the whole section is
    generic over any [rsp] in the valid window.  So are the program
    break and the mmap base, for the same reason. *)
Variable rsp rbrk rmb : word.

(** The entry stack draw this run was started with
    ([Run.ExecEntry]'s [en_draw]): the 16 AT_RANDOM bytes the kernel
    picks afresh at every [execve], and the stack VMA's end
    [StackLayout.ed_top] that [setup_arg_pages] (fs/exec.c, Linux
    v6.18.46, commit 1f99e9ab748f) page-aligns.  This proof may assume
    NOTHING about either beyond the launch conjunct below, exactly as
    it may assume nothing about where the stack landed.  Quantified per
    binary, so the target's draw below is a different variable. *)
Variable rrnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned rsp)%Z.
Hypothesis Hsp_hi : (bv_unsigned rsp <= sp_window_hi)%Z.

(** The fifth conjunct of [Run.valid_entry_va]: this placement is one a
    Linux launch can give.  It is what bounds the entry block (through
    [StepTac.bsb_bound]) and what puts [rsp] at or below
    [StackLayout.ed_top], hence the zero-filled stack window at or
    above [rsp - 8 MiB] that the frame invariant needs
    ([WxExec.mem_clear_wrap]).  [Run.valid_argv] and [Run.valid_envp]
    no longer bound the block: the strings sit at the TOP of it now, and
    the exec file name and [arch_align_stack]'s pad are in it too, so
    the E2BIG cap of [Run.valid_launch] is the real bound. *)
Hypothesis Hlaunch : entry_launch_ok_va Sv48 (mkEntry rsp rbrk rmb rrnd) inp.

Lemma rsp_lo_num : (0x7fff80000000 <= bv_unsigned rsp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma rsp_hi_num : (bv_unsigned rsp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Definition argcN : word := len_word (in_argv inp).

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length (in_argv inp)).
Proof.
  pose proof (valid_argv_len (in_argv inp) Hva).
  unfold argcN, len_word. apply u_Z2bv; lia.
Qed.

(** No-overflow bound for the initial stack image (feeds the stack-read
    lemmas' side conditions).  Quantified over the entry word because
    the auxv's AT_ENTRY carries it and the block therefore mentions it,
    while nothing here cares which value it is. *)
Lemma source_bsb_nw : forall entry : word,
  (bv_unsigned rsp
   + Z.of_nat (length (entry_stack_image inp rmb source_phdrs entry rsp rrnd))
     < 2^64)%Z.
Proof.
  intros entry.
  pose proof (bsb_bound Sv48 inp rmb source_phdrs entry rsp rbrk rrnd
                Hvl Hlaunch).
  pose proof rsp_hi_num. lia.
Qed.

(** The pointer _start stores into musl's [__environ] slot at 0x100e8. *)
Definition envp_ptr : word :=
  Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat (length (in_argv inp)) + 8).

(** The value _start computes in a2 equals [envp_ptr]. *)
Lemma envp_ptr_eq :
  v_addi (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli argcN 3)) 8 = envp_ptr.
Proof.
  pose proof rsp_hi_num. pose proof rsp_lo_num.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hlen.
  apply bv_eq. unfold envp_ptr, v_addi.
  rewrite !Z_to_bv_unsigned.
  rewrite v_add_small
    by (rewrite u_Z2bv by lia; rewrite v_slli_3 by (rewrite u_argcN; lia);
        rewrite u_argcN; lia).
  rewrite u_Z2bv by lia.
  rewrite v_slli_3 by (rewrite u_argcN; lia).
  rewrite u_argcN.
  f_equal; lia.
Qed.

(* ================================================================= *)
(* Per-step side-condition tactics                                    *)
(* ================================================================= *)

(** Re-establish the frame invariant on the CURRENT overlay: peel the
    [wbytes] of the stores made so far (each lands at/above [stext_hi],
    so the [left] disjunct closes) down to the initial [wrap_mem],
    which misses everything below the stack window.

    The base arm is an [eapply] because [WxExec.mem_clear_wrap] now
    takes the launch conjunct, whose address-space size and program
    break the conclusion does not mention; [Hlaunch] fixes both.  Its
    arithmetic arm is what says the zero-filled window stops at or
    above [rsp - 8 MiB]: RLIMIT_STACK is counted from the stack VMA's
    end rather than from [rsp] ([expand_downwards], mm/vma.c, Linux
    v6.18.46, commit 1f99e9ab748f), and the launch conjunct is what
    puts [rsp] at or below that end. *)
Ltac src_clear :=
  first
    [ eapply mem_clear_wrap;
        [ exact Hlaunch | unfold stack_max_size; lia ]
    | apply mem_clear_wbytes;
        [ src_clear
        | rewrite ?length_word_to_le_bytes; cbn [length];
          imm_norm; u_norm; left; lia
        | rewrite ?length_word_to_le_bytes; cbn [length];
          imm_norm; u_norm; lia ] ].

(** The vDSO pair the run appends after the image's own segment
    ([Run.run_segments]); the derivation never reaches it. *)
Local Abbreviation vt := (vdso_segments (in_kernel inp) rsp rmb).

(** The packed w+x fetch premise for one step, from the generated
    static fetch fact [SF], carried to the run's segment list. *)
Ltac wxf SF :=
  eapply wx_fetch_intro with (lo := 0x10078%Z) (hi := 0x100e4%Z);
    [ apply source_run_no_ro_exec
    | src_clear
    | imm_norm; lia
    | imm_norm; lia
    | lia
    | exact (fetch_word_wx_app source_segs vt _ _ SF) ].

(* ================================================================= *)
(* The derivation: 18 instructions, no output, exit 5.                *)
(* ================================================================= *)

Lemma source_wexit :
  to_wexit (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) 0x10078 source_phdrs
       rsp rmb rrnd inp)
    [] (Z_to_bv 64 5).
Proof.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargc.
  rewrite init_mkst. norm_pc.
  (* 0x10078 auipc gp, 0x1 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_auipc_wx; [wxf SF_10078 | reflexivity | exact SD_10078]
    | step_simpl ].
  (* 0x1007c addi gp, gp, -1939 (gp is dead: never read below) *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_wx; [wxf SF_1007c | reflexivity | exact SD_1007c]
    | step_simpl ].
  (* 0x10080 ld a0, 0(sp) — argc out of the initial stack image *)
  eapply tw_step;
    [ reflexivity
    | eapply step_ld_wx with (bs := word_le8 argcN) (v := argcN);
      [ wxf SF_10080 | reflexivity | exact SD_10080
      | getr_resolve; imm_norm; rewrite v_addi_0;
        rewrite rdn_wrap_stack_above by (u_norm; lia);
        apply read_argc; apply source_bsb_nw
      | apply bytes_le_n_to_le_8 ]
    | step_simpl ].
  (* 0x10084 addi a1, sp, 8 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at_wx with (v := Z_to_bv 64 (bv_unsigned rsp + 8));
      [ wxf SF_10084 | reflexivity | exact SD_10084 | reflexivity
      | getr_resolve; imm_norm; reflexivity ]
    | step_simpl ].
  (* 0x10088 slli t0, a0, 3 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_slli_wx; [wxf SF_10088 | reflexivity | exact SD_10088]
    | step_simpl ].
  (* 0x1008c add a2, a1, t0 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_add_wx; [wxf SF_1008c | reflexivity | exact SD_1008c]
    | step_simpl ].
  (* 0x10090 addi a2, a2, 8 — a2 is now the envp pointer *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at_wx with (v := envp_ptr);
      [ wxf SF_10090 | reflexivity | exact SD_10090 | reflexivity
      | getr_resolve; regupd_resolve; imm_norm; exact envp_ptr_eq ]
    | step_simpl ].
  (* 0x10094 auipc t1, 0x0 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_auipc_wx; [wxf SF_10094 | reflexivity | exact SD_10094]
    | step_simpl ].
  (* 0x10098 addi t1, t1, 84 — t1 = &__environ = 0x100e8 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at_wx with (v := Z_to_bv 64 0x100e8);
      [ wxf SF_10098 | reflexivity | exact SD_10098 | reflexivity
      | getr_resolve; regupd_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x1009c sd a2, 0(t1) — the envp pointer into __environ (w+x .bss) *)
  eapply tw_step;
    [ reflexivity
    | eapply step_sd_at_wx with (a := Z_to_bv 64 0x100e8) (v := envp_ptr);
      [ wxf SF_1009c | reflexivity | exact SD_1009c
      | getr_resolve; regupd_resolve; imm_norm; rewrite v_addi_0; reflexivity
      | getr_resolve; regupd_resolve; reflexivity
      | apply (store_ok_app source_segs vt), source_store_ok; u_norm; cbn [Z.of_nat]; lia ]
    | step_simpl ].
  (* 0x100a0 jal ra, main (0x100d0) *)
  eapply tw_step;
    [ reflexivity
    | eapply step_jal_link_wx; [wxf SF_100a0 | reflexivity | exact SD_100a0]
    | step_simpl ].
  (* 0x100d0 lui a5, 0x10 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_lui_wx; [wxf SF_100d0 | reflexivity | exact SD_100d0]
    | step_simpl ].
  (* 0x100d4 li a4, 5 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at_wx with (v := Z_to_bv 64 5);
      [ wxf SF_100d4 | reflexivity | exact SD_100d4 | reflexivity
      | getr_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x100d8 sb a4, 228(a5) — flag := 5, in the SAME RWX segment *)
  eapply tw_step;
    [ reflexivity
    | eapply step_sb_at_wx with (a := Z_to_bv 64 0x100e4)
        (v := Z_to_bv 64 5) (b := Z_to_bv 8 5);
      [ wxf SF_100d8 | reflexivity | exact SD_100d8
      | getr_resolve; regupd_resolve; imm_norm; bveq
      | getr_resolve; regupd_resolve; reflexivity
      | bveq
      | apply (store_ok_app source_segs vt), source_store_ok; u_norm; cbn [Z.of_nat]; lia ]
    | step_simpl ].
  (* 0x100dc lbu a0, 228(a5) — read flag back OUT OF THE OVERLAY *)
  eapply tw_step;
    [ reflexivity
    | eapply step_lbu_wx with (b := Z_to_bv 8 5);
      [ wxf SF_100dc | reflexivity | exact SD_100dc
      | getr_resolve; regupd_resolve; imm_norm; wlits_closed;
        change 1%nat with (length [Z_to_bv 8 5]);
        apply rdn_wbytes_hit; u_norm; cbn [length]; lia ]
    | step_simpl ].
  (* 0x100e0 ret *)
  eapply tw_step;
    [ reflexivity
    | eapply step_jalr_x0_wx with (tgt := Z_to_bv 64 0x100a4);
      [ wxf SF_100e0 | reflexivity | exact SD_100e0
      | getr_resolve; regupd_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x100a4 li a7, 93 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at_wx with (v := Z_to_bv 64 93);
      [ wxf SF_100a4 | reflexivity | exact SD_100a4 | reflexivity
      | getr_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x100a8 ecall — exit(5) *)
  eapply tw_step;
    [ reflexivity
    | eapply step_ecall_wx; [wxf SF_100a8 | reflexivity]
    | ].
  apply tw_exit_coden.
  - getr_resolve; regupd_resolve; u_norm; lia.
  - regupd_resolve; bveq.
  - u_norm; lia.
Qed.

End SourceProof.
