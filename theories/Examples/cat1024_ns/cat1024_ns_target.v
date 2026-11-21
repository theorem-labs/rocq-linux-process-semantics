(** * cat1024-ns, target binary (Zig ReleaseSmall, raw syscalls).

    PROOF-SIDE FILE (not part of the trusted specification).

    The target loop is register-only: _start saves ra once, calls run(),
    and run() loops { ecall read(0, buf, 1024); 0 -> ret 0; ecall
    write(1, buf, r) (full in one call in the model) }.  The loop head is
    0x10011b0; the loop-head invariant only pins ra (the return into
    _start's exit sequence) and a3 (the buffer address).

    Conventions: pc/rodata constants in numeral-literal form,
    sp-relative addresses in the canonical [Z_to_bv 64 (...)] form,
    block lengths as [len_word bs].

    The run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  The section takes the pair as a variable [vt] and every
    derivation steps over [target_segs ++ vt]; [Proof.v] instantiates it.
    The one stack store needs the entry predicate's launch conjunct
    [Run.entry_launch_ok_va] and [Run.valid_launch]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamExec WallSim StreamSim StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Examples.cat1024_ns Require Import cat1024_ns_code cat1024_ns_defs.
From LinuxProcessSemantics.Examples.cat1024_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.cat1024_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them. *)
#[local] Instance cat1024_ns_target_fx : FPState := fx0.

(** The target buffer (bss). *)
Definition tgt_buf : word := 0x1002208.

Lemma u_tgt_buf : bv_unsigned tgt_buf = 0x1002208%Z.
Proof. reflexivity. Qed.

Section TargetRun.

(** The segments the run appends after the image's own: the vDSO pair
    ([Run.run_segments]).  Nothing below reads them. *)
Variable vt : list Segment.

(** The run's segment list, and a fetch fact of the image carried to it. *)
Local Abbreviation rsegs := (target_segs ++ vt).
Local Abbreviation TFv F := (fetch_word_app _ vt _ _ F).

(** Loop-head invariant: at 0x10011b0 with ra = _start's exit tail and
    a3 = the buffer.  Memory is unconstrained (the loop never loads). *)
Definition tgt_LH (ms : machine_state) : Prop :=
  exists regs mem,
    ms = mkst regs 0x10011b0 mem (seg_rom rsegs) /\
    reg_get regs 1 = (0x10011a0 : word) /\
    reg_get regs 13 = tgt_buf.

(** The put-style retry loop after a (possibly short) write delivery:
    from the post-write state at 0x10011e4 — a0 = the delivered length
    [len_word (firstn n rest)], a1 = the offered pointer [p], a2 = the
    offered count — the loop runs [blez a0] (fall-through), bumps the
    pointer, decrements the count, and either returns to the loop head
    ([beqz a2] taken, full delivery) or reissues the write on the
    remainder: a [WallSim.to_wall_tail] of [skipn n rest] down to
    [lh_next].  Induction on [fuel >= length rest]; the remainder
    strictly shrinks because every delivery is nonempty. *)
Lemma tgt_put_wall : forall fuel (rest : list byte) (p : word) n regs mem,
  (length rest <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length rest)%nat ->
  (Z.of_nat (length rest) <= 1024)%Z ->
  (0x1002208 <= bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) <= 0x1002608)%Z ->
  reg_get regs 10 = len_word (firstn n rest) ->
  reg_get regs 11 = p ->
  reg_get regs 12 = len_word rest ->
  reg_get regs 1 = (0x10011a0 : word) ->
  reg_get regs 13 = tgt_buf ->
  rdn rsegs mem p (length rest) = Some rest ->
  to_wall_tail rsegs (Z_to_bv 64 1)
    (mkst regs (0x10011e4 : word) mem (seg_rom rsegs))
    (skipn n rest) (lh_next rsegs tgt_LH).
Proof.
  induction fuel as [|fuel IH];
    intros rest p n regs mem Hfuel Hn1 Hn2 Hlen Hplo Hphi
           H10 H11 H12 H1 H13 Hread.
  { lia. }
  destruct (Nat.eq_dec n (length rest)) as [-> | Hne].
  - (* full delivery: blez ft; add; sub; beqz TAKEN -> loop head *)
    rewrite skipn_all.
    apply twt_done.
    unfold lh_next. eexists. split.
    + (* blez a0 falls through *)
      step_intro;
        [ reflexivity
        | eapply step_bge_ft;
          [ exact (TFv TF_10011e4) | reflexivity | exact TD_10011e4
          | getr_resolve; rewrite H10; apply c_lts_0_pos;
            rewrite u_len_word_firstn by lia; lia ]
        | norm_pc ].
      (* add a1,a1,a0 ; sub a2,a2,a0 *)
      stepi (TFv TF_10011e8) TD_10011e8.
      stepi (TFv TF_10011ec) TD_10011ec.
      (* beqz a2 taken: back to 0x10011b0 *)
      step_intro;
        [ reflexivity
        | eapply step_beq_tk;
          [ exact (TFv TF_10011f0) | reflexivity | exact TD_10011f0
          | getr_resolve; rewrite H12, H10; apply c_eq_0_of_u;
            rewrite v_sub_len_firstn by lia;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite length_skipn; lia ]
        | norm_pc ].
      apply mst_refl.
    + (* the loop-head invariant *)
      unfold tgt_LH. do 2 eexists. split; [reflexivity|]. split.
      * regupd_resolve. exact H1.
      * regupd_resolve. exact H13.
  - (* short delivery: blez ft; add; sub; beqz ft; j; reissue *)
    step_intro;
      [ reflexivity
      | eapply step_bge_ft;
        [ exact (TFv TF_10011e4) | reflexivity | exact TD_10011e4
        | getr_resolve; rewrite H10; apply c_lts_0_pos;
          rewrite u_len_word_firstn by lia; lia ]
      | norm_pc ].
    (* add a1,a1,a0: the pointer bump *)
    stepiv (TFv TF_10011e8) TD_10011e8 (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
      ltac:(getr_resolve; rewrite H11, H10; apply v_add_len_firstn_Z; lia).
    (* sub a2,a2,a0: the count decrement *)
    stepiv (TFv TF_10011ec) TD_10011ec (len_word (skipn n rest))
      ltac:(getr_resolve; rewrite H12, H10; apply v_sub_len_firstn; lia).
    (* beqz a2 falls through (remainder nonempty) *)
    step_intro;
      [ reflexivity
      | eapply step_beq_ft;
        [ exact (TFv TF_10011f0) | reflexivity | exact TD_10011f0
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* j 0x10011d8 *)
    stepj (TFv TF_10011f4) TD_10011f4.
    (* li a7,64 ; li a0,1 *)
    stepiv (TFv TF_10011d8) TD_10011d8 (Z_to_bv 64 64) ltac:(getr_resolve; bveq).
    stepiv (TFv TF_10011dc) TD_10011dc (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* ecall: the reissued write *)
    eapply twt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10011e0) eq_refl) |].
    apply twt_more; [rewrite length_skipn; lia|].
    apply (twl_write_rec rsegs (Z_to_bv 64 1)).
    + getr_resolve; reflexivity.
    + regupd_resolve; reflexivity.
    + (* the remainder read back at the bumped pointer *)
      match goal with
      | |- ms_read_bytes _ (reg_get ?R 11) (reg_get ?R 12) = Some _ =>
          replace (reg_get R 11)
            with (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
            by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word (skipn n rest))
            by (regupd_resolve; reflexivity)
      end.
      rewrite (ms_read_bytes_rdn rsegs) by reflexivity.
      cbn [ms_mem].
      replace (word_to_nat (len_word (skipn n rest)))
        with (length (skipn n rest))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      pose proof (rdn_skipn rsegs mem (length rest) p rest n Hread Hn2)
        as Hsk.
      rewrite word_add_nat_Z in Hsk by lia.
      rewrite length_skipn. exact Hsk.
    + (* the remainder's range passes [access_ok]: inside the buffer *)
      match goal with
      | |- access_okb (reg_get ?R 11) (bv_unsigned (reg_get ?R 12)) = true =>
          replace (reg_get R 11)
            with (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
            by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word (skipn n rest))
            by (regupd_resolve; reflexivity)
      end.
      apply access_okb_intro.
      rewrite u_len_word by (rewrite length_skipn; lia).
      rewrite length_skipn. u_norm. unfold TASK_SIZE. lia.
    + rewrite length_skipn; lia.
    + (* the (shorter) remainder, by induction *)
      intros m Hm1 Hm2.
      norm_pc.
      apply (IH (skipn n rest) (Z_to_bv 64 (bv_unsigned p + Z.of_nat n)) m).
      * rewrite length_skipn; lia.
      * exact Hm1.
      * exact Hm2.
      * rewrite length_skipn; lia.
      * rewrite u_Z2bv by lia; lia.
      * rewrite u_Z2bv by lia; rewrite length_skipn; lia.
      * regupd_resolve; reflexivity.
      * regupd_resolve; reflexivity.
      * regupd_resolve; reflexivity.
      * regupd_resolve; exact H1.
      * regupd_resolve; exact H13.
      * pose proof (rdn_skipn rsegs mem (length rest) p rest n Hread Hn2)
          as Hsk.
        rewrite word_add_nat_Z in Hsk by lia.
        rewrite length_skipn. exact Hsk.
Qed.

Lemma tgt_LH_to_rd : forall ms,
  tgt_LH ms -> to_rd rsegs tgt_LH (Z_to_bv 64 1024) ms.
Proof.
  intros ms (regs & mem & -> & H1 & H13).
  (* li a7,63; li a2,1024; li a0,0; mv a1,a3 *)
  stepiv (TFv TF_10011b0) TD_10011b0 (Z_to_bv 64 63) ltac:(getr_resolve; bveq).
  stepiv (TFv TF_10011b4) TD_10011b4 (Z_to_bv 64 1024) ltac:(getr_resolve; bveq).
  stepiv (TFv TF_10011b8) TD_10011b8 (Z_to_bv 64 0) ltac:(getr_resolve; apply v_addi_0).
  stepiv (TFv TF_10011bc) TD_10011bc tgt_buf
    ltac:(getr_resolve; rewrite H13; apply v_addi_0).
  (* ecall: the pending read *)
  eapply trd_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10011c0) eq_refl) |].
  apply trd_here_rec with (buf := tgt_buf).
  - getr_resolve; reflexivity.
  - regupd_resolve; reflexivity.
  - regupd_resolve; reflexivity.
  - regupd_resolve; reflexivity.
  - apply target_buf_wseg.
  - (* the buffer is a link-time constant far under [State.TASK_SIZE], so the range passes [access_ok] *)
    apply access_okb_intro. rewrite u_tgt_buf.
    change (bv_unsigned (Z_to_bv 64 1024)) with 1024%Z.
    unfold TASK_SIZE. lia.
  - (* EOF continuation: beqz a0 taken; ret; li a7,93; ecall -> exit 0 *)
    norm_pc.
    step_intro;
      [ reflexivity
      | eapply step_beq_tk;
        [ exact (TFv TF_10011c4) | reflexivity | exact TD_10011c4
        | getr_resolve; exact c_eq_0_true ]
      | norm_pc ].
    stepjr (TFv TF_10011fc) TD_10011fc (0x10011a0 : word) ltac:(getr_resolve; exact H1).
    stepiv (TFv TF_10011a0) TD_10011a0 (Z_to_bv 64 93) ltac:(getr_resolve; bveq).
    eapply te_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10011a4) eq_refl) |].
    apply te_here_rec0.
    + getr_resolve; reflexivity.
    + regupd_resolve; reflexivity.
  - (* bytes continuation *)
    intros bs Hblo Hbhi.
    norm_pc.
    (* beqz a0 falls through *)
    step_intro;
      [ reflexivity
      | eapply step_beq_ft;
        [ exact (TFv TF_10011c4) | reflexivity | exact TD_10011c4
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by lia; lia ]
      | norm_pc ].
    (* mv a2,a0 *)
    stepiv (TFv TF_10011c8) TD_10011c8 (len_word bs) ltac:(getr_resolve; apply v_addi_0).
    (* bltz a0 falls through *)
    step_intro;
      [ reflexivity
      | eapply step_blt_ft;
        [ exact (TFv TF_10011cc) | reflexivity | exact TD_10011cc
        | getr_resolve; apply c_lts_pos_0;
          rewrite u_len_word by lia; lia ]
      | norm_pc ].
    (* mv a1,a3 *)
    stepiv (TFv TF_10011d0) TD_10011d0 tgt_buf
      ltac:(getr_resolve; rewrite H13; apply v_addi_0).
    (* beqz a2 falls through (a2 = len <> 0) *)
    step_intro;
      [ reflexivity
      | eapply step_beq_ft;
        [ exact (TFv TF_10011d4) | reflexivity | exact TD_10011d4
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by lia; lia ]
      | norm_pc ].
    (* li a7,64; li a0,1 *)
    stepiv (TFv TF_10011d8) TD_10011d8 (Z_to_bv 64 64) ltac:(getr_resolve; bveq).
    stepiv (TFv TF_10011dc) TD_10011dc (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* ecall: the pending write *)
    eapply twr_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10011e0) eq_refl) |].
    apply twr_here_rec.
    + getr_resolve; reflexivity.
    + regupd_resolve; reflexivity.
    + (* the buffer bytes read back *)
      match goal with
      | |- ms_read_bytes _ (reg_get ?R 11) (reg_get ?R 12) = Some bs =>
          replace (reg_get R 11) with tgt_buf by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word bs) by (regupd_resolve; reflexivity)
      end.
      rewrite (ms_read_bytes_rdn rsegs) by reflexivity.
      cbn [ms_mem].
      replace (word_to_nat (len_word bs)) with (length bs)
        by (unfold word_to_nat; rewrite u_len_word by lia;
            rewrite Nat2Z.id; reflexivity).
      apply rdn_write_to_mem. rewrite u_tgt_buf. lia.
    + (* the buffer range passes [access_ok]: a link-time address *)
      match goal with
      | |- access_okb (reg_get ?R 11) (bv_unsigned (reg_get ?R 12)) = true =>
          replace (reg_get R 11) with tgt_buf by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word bs) by (regupd_resolve; reflexivity)
      end.
      apply access_okb_intro. rewrite u_tgt_buf.
      rewrite u_len_word by lia. unfold TASK_SIZE. lia.
    + (* the block is nonempty *)
      lia.
    + (* the write-all retry loop, per delivered length *)
      intros n Hn1 Hn2.
      norm_pc.
      apply (tgt_put_wall (length bs) bs tgt_buf n).
      * lia.
      * exact Hn1.
      * exact Hn2.
      * lia.
      * rewrite u_tgt_buf; lia.
      * rewrite u_tgt_buf; lia.
      * regupd_resolve; reflexivity.
      * regupd_resolve; reflexivity.
      * regupd_resolve; reflexivity.
      * regupd_resolve; exact H1.
      * regupd_resolve; exact H13.
      * apply rdn_write_to_mem. rewrite u_tgt_buf. lia.
Qed.

Section TargetInit.

Variable inp : ProcInput.
Variable Hvl : valid_launch inp.
Variable asp abrk amb : word.

(** The target run's own draw, independent of the source's (the
    [ed_random] and [ed_top] halves of [Run.ExecEntry]'s [en_draw]; see
    the source file). *)
Variable arnd : EntryDraw.
Variable Hsp_lo : (sp_window_lo <= bv_unsigned asp)%Z.
Variable Hsp_hi : (bv_unsigned asp <= sp_window_hi)%Z.

(** The launch conjunct of [Run.valid_entry_va]: with [Hvl] it places
    the stack-store window the [sd ra,8(sp)] below lands in. *)
Variable Hlau : entry_launch_ok_va Sv48 (mkEntry asp abrk amb arnd) inp.

Lemma asp_lo_num : (0x7fff80000000 <= bv_unsigned asp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma asp_hi_num : (bv_unsigned asp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

(** From the initial state, _start and run()'s prologue reach the loop
    head, whence [to_rd]. *)
Lemma tgt_init_to_rd :
  to_rd rsegs tgt_LH (Z_to_bv 64 1024)
    (init_machine_state rsegs 0x1001190 target_phdrs asp amb arnd inp).
Proof.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  rewrite init_mkst. norm_pc.
  (* addi sp,sp,-16 *)
  stepiv (TFv TF_1001190) TD_1001190 (Z_to_bv 64 (bv_unsigned asp - 16))
    ltac:(getr_resolve; sp_norm; f_equal; lia).
  (* sd ra,8(sp) *)
  eapply trd_step;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned asp - 8))
                             (v := Z_to_bv 64 0);
      [ exact (TFv TF_1001194) | reflexivity | exact TD_1001194
      | getr_resolve; sp_norm; f_equal; lia
      | getr_resolve; reflexivity
      | solve_store_ok ]
    | step_simpl ].
  (* auipc ra,0 *)
  stepi (TFv TF_1001198) TD_1001198.
  (* jalr 16(ra): call run, ra := 0x10011a0 *)
  stepjr (TFv TF_100119c) TD_100119c (0x1001198 : word) ltac:(getr_resolve; bveq).
  (* lui a3,0x1002; addi a3,a3,520: a3 := buf *)
  stepi (TFv TF_10011a8) TD_10011a8.
  stepiv (TFv TF_10011ac) TD_10011ac tgt_buf ltac:(getr_resolve; bveq).
  (* loop head *)
  apply tgt_LH_to_rd.
  unfold tgt_LH. do 2 eexists. split; [reflexivity|]. split.
  - regupd_resolve. bveq.
  - regupd_resolve. reflexivity.
Qed.

End TargetInit.

End TargetRun.
