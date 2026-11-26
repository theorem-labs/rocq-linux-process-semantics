(** * oob-read-bug-ns target binary: brk outcome set (companion file).

    PROOF-SIDE FILE (not part of the trusted specification).

    Builds on the compiled [oob_read_bug_ns_target] (entry/strlen/copy/
    put/sum lemmas) and derives the brk-syscall spine and the outcome
    set [target_outcomes], mirroring [oob_read_bug_ns_source].

    Conventions: bytes are [byte = bv 8], machine values
    [word = bv 64]; unbounded bookkeeping in [Z] over
    [bv_unsigned]; computed stack addresses in the canonical
    [Z_to_bv 64 (...)] form; the brk x8 is quantified via
    [ms_svc_pending ms = Some x8] with [bv_unsigned x8 = 214%Z];
    outcomes are [(list (list byte) * word)] with exit codes
    [Z_to_bv 64 4] / [Z_to_bv 64 0]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec AllocSim WallSim NumPrint StepTac StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Examples.oob_read_bug_ns Require Import oob_read_bug_ns_code oob_read_bug_ns_defs.
From LinuxProcessSemantics.Examples.oob_read_bug_ns Require Import oob_read_bug_ns_target.
From LinuxProcessSemantics.Examples.oob_read_bug_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.oob_read_bug_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them.  [fx0] itself is
    the instance, so every state here is [init_mkst]'s [@mkst fx0]. *)
#[local] Existing Instance fx0.

(* ================================================================= *)
(* Reading the '\n' constant from rodata (0x1000158)                  *)
(* ================================================================= *)

Lemma read_newline_t : forall (mem : word -> option byte),
  mem (0x1000158 : word) = None ->
  rdn target_segs mem (0x1000158 : word) 1%nat = Some [Z_to_bv 8 10].
Proof.
  intros mem Hn. cbn [rdn]. rewrite Hn.
  replace (seg_rom target_segs (0x1000158 : word)) with (Some (Z_to_bv 8 10)).
  - wlits. reflexivity.
  - symmetry.
    apply (@bool_decide_eq_true_1
             (seg_rom target_segs (0x1000158 : word) = Some (Z_to_bv 8 10)) _).
    vm_cast_no_check (@eq_refl bool true).
Qed.

(* ================================================================= *)
(* A region free against the reservations is entirely below or        *)
(* entirely above the loaded pages                                    *)
(* ================================================================= *)

Lemma target_free_cases : forall (b l : word),
  region_free (segments_reserved target_segs) b l = true ->
  (0 < bv_unsigned l)%Z ->
  (bv_unsigned b + bv_unsigned l <= 0x1000000 \/ 0x1002000 <= bv_unsigned b)%Z.
Proof.
  intros b l Hfree Hl.
  rewrite target_reserved_val in Hfree.
  cbn [region_free] in Hfree.
  apply andb_true_iff in Hfree as [H0 Hfree].
  apply andb_true_iff in Hfree as [H1 _].
  apply negb_true_iff in H0. apply negb_true_iff in H1.
  unfold iv_overlap in H0, H1.
  apply andb_false_iff in H0. apply andb_false_iff in H1.
  change (bv_unsigned (0x1000000 : word)) with 0x1000000%Z in H0.
  change (bv_unsigned (0x1001000 : word)) with 0x1001000%Z in H1.
  change (bv_unsigned (0x1000 : word)) with 0x1000%Z in H0, H1.
  destruct H0 as [H0|H0]; destruct H1 as [H1|H1];
    apply Z.ltb_ge in H0; apply Z.ltb_ge in H1; lia.
Qed.

(* ================================================================= *)
(* The proof, generic over argv/envp and the stack pointer             *)
(* ================================================================= *)

Section TargetProof.

Variable inp : ProcInput.
Local Abbreviation av := (in_argv inp).
Local Abbreviation ev := (in_envp inp).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.

Variable asp : word.

(** The target run's own AT_RANDOM draw, independent of the source's
    (the [ed_random] half of [Run.ExecEntry]'s [en_draw]; see the source file). *)
Variable arnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned asp)%Z.
Hypothesis Hsp_hi : (bv_unsigned asp <= sp_window_hi)%Z.

(** The quantified initial program break ([Run.valid_brk] window, like the
    SP above; alignment is not needed by this proof). *)
Variable abrk : word.
Variable amb : word.
Hypothesis Hbrk_lo :
  (reserved_top (segments_reserved target_segs) <= bv_unsigned abrk)%Z.
Hypothesis Hbrk_hi :
  (bv_unsigned abrk
   <= reserved_top (segments_reserved target_segs) + brk_aslr_max)%Z.
Hypothesis Hvl : valid_launch inp.

(** The fifth conjunct of [Run.valid_entry_va] for the target's run
    ([create_elf_tables] and [setup_arg_pages], fs/binfmt_elf.c and
    fs/exec.c, Linux v6.18.46). *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry asp abrk amb arnd) inp.

Lemma rtop_tgt_val : reserved_top (segments_reserved target_segs) = 0x1002000%Z.
Proof. rewrite target_reserved_val. reflexivity. Qed.
Lemma abrk_lo_num : (0x1002000 <= bv_unsigned abrk)%Z.
Proof. rewrite <- rtop_tgt_val. exact Hbrk_lo. Qed.
Lemma abrk_hi_num : (bv_unsigned abrk <= 0x1002000 + 1073741824)%Z.
Proof. rewrite <- rtop_tgt_val, <- brk_aslr_max_val. exact Hbrk_hi. Qed.
Lemma abrk_lt64 : (bv_unsigned abrk < 2^64)%Z.
Proof. pose proof (u64_range abrk). lia. Qed.

Local Abbreviation targ1 := (oob_read_bug_ns_target.targ1 inp).
Local Abbreviation tnn := (oob_read_bug_ns_target.tnn inp).
Local Abbreviation tnN := (oob_read_bug_ns_target.tnN inp).
Local Abbreviation ptrA := (oob_read_bug_ns_target.ptrA inp arnd).
Local Abbreviation awmem := (oob_read_bug_ns_target.awmem inp asp arnd amb).
Local Abbreviation amem1 := (oob_read_bug_ns_target.amem1 inp asp arnd amb).
Local Abbreviation tfmem := (oob_read_bug_ns_target.tfmem inp asp arnd amb).
(** The run's rom: the image's segments, then the vDSO pair. *)
Local Abbreviation trom := (oob_read_bug_ns_target.trom inp asp amb).

Local Abbreviation asp_lo_num := (oob_read_bug_ns_target.asp_lo_num asp Hsp_lo).
Local Abbreviation asp_hi_num := (oob_read_bug_ns_target.asp_hi_num asp Hsp_hi).
Local Abbreviation target_exit :=
  (oob_read_bug_ns_target.target_exit inp asp Hsp_lo Hsp_hi amb).
Local Abbreviation read_slot_ra_t :=
  (oob_read_bug_ns_target.read_slot_ra_t inp asp arnd Hsp_lo Hsp_hi amb).
Local Abbreviation read_slot_s0_t :=
  (oob_read_bug_ns_target.read_slot_s0_t inp asp arnd Hsp_lo Hsp_hi amb).

(** tfmem misses below the stack window (rodata / brk arena reads fall
    through to the image / zero-fill). *)
Lemma tfmem_low_none : forall a : word,
  (bv_unsigned a < bv_unsigned asp - stack_max_size)%Z -> tfmem a = None.
Proof.
  intros a Ha. pose proof stack_max_size_val as Hsms.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof (u64_range asp).
  unfold oob_read_bug_ns_target.tfmem, oob_read_bug_ns_target.amem1.
  rewrite !(wbytes_below (word_to_le_bytes 8 _))
    by (rewrite ?length_N_to_le_bytes; u_norm; lia).
  unfold oob_read_bug_ns_target.awmem.
  apply (wrap_mem_below Sv48 inp amb target_phdrs _ asp abrk arnd _ Hlau).
  exact Ha.
Qed.

(* ================================================================= *)
(* argc >= 2                                                          *)
(* ================================================================= *)

Section Ge2MainT.

Hypothesis Hge2 : (2 <= length av)%nat.

Local Abbreviation tnN_le := (oob_read_bug_ns_target.tnN_le inp Hva Hge2).
Local Abbreviation u_tnN := (oob_read_bug_ns_target.u_tnN inp Hva Hge2).
Local Abbreviation targ1_nz := (oob_read_bug_ns_target.targ1_nz inp Hva Hge2).
Local Abbreviation targ1_bytes := (oob_read_bug_ns_target.targ1_bytes inp Hva Hge2).
Local Abbreviation ptrA_lo :=
  (oob_read_bug_ns_target.ptrA_lo inp asp arnd abrk amb Hlau Hge2).
Local Abbreviation ptrA_hi :=
  (oob_read_bug_ns_target.ptrA_hi inp asp arnd abrk amb Hlau Hge2).
Local Abbreviation read_str_t :=
  (oob_read_bug_ns_target.read_str_t inp asp arnd Hsp_lo Hsp_hi abrk amb Hlau Hge2).
Local Abbreviation target_to_captest :=
  (oob_read_bug_ns_target.target_to_captest inp Hva asp arnd Hsp_lo Hsp_hi abrk amb
     Hvl Hlau Hge2).
Local Abbreviation target_copy :=
  (oob_read_bug_ns_target.target_copy inp Hva asp arnd Hsp_lo Hsp_hi abrk amb Hlau Hge2).
Local Abbreviation target_put := (oob_read_bug_ns_target.target_put inp asp amb Hge2).
Local Abbreviation target_sum := (oob_read_bug_ns_target.target_sum inp Hva asp amb Hge2).

(* ================================================================= *)
(* Entry to the first brk ecall (0x10011cc)                           *)
(* ================================================================= *)

Lemma target_to_brk1 : (Z.of_nat tnn <= 65536)%Z ->
  exists regsB,
    reg_get regsB 2 = Z_to_bv 64 (bv_unsigned asp - 64) /\
    reg_get regsB 8 = ptrA /\
    reg_get regsB 10 = Z_to_bv 64 0 /\
    reg_get regsB 11 = tnN /\
    reg_get regsB 13 = Z_to_bv 64 4 /\
    msteps target_segs
      (init_machine_state (run_segments target_segs inp asp amb) 0x100115c target_phdrs asp amb arnd inp)
      {| ms_regs := regsB; ms_fregs := fp_regs; ms_pc_val := (0x10011e8 : word);
         ms_svc_pending := Some (Z_to_bv 64 214); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := tfmem; ms_rom := trom |}.
Proof.
  intros Hncap.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tnN_le as HnnLe.
  destruct target_to_captest as (regs2 & H1 & H2 & H8 & H10 & Hms).
  eexists. repeat split.
  6: {
  eapply msteps_trans; [exact Hms|].
  (* lui a2, 0x10 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_lui_at with (v := Z_to_bv 64 65536);
      [ exact TF_10011b0 | reflexivity | exact TD_10011b0 | reflexivity | bveq ]
    | step_simpl ].
  (* bgeu a2, a0 taken (n <= 65536) -> 0x10011c0 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_bgeu_tk;
      [ exact TF_10011b4 | reflexivity | exact TD_10011b4
      | getr_resolve; regupd_resolve; rewrite H10;
        rewrite c_ltu_ltb; apply Z.ltb_ge; u_norm; rewrite u_tnN; lia ]
    | norm_pc ].
  (* mv a1, a0 : a1 = n *)
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := tnN);
      [ exact TF_10011c0 | reflexivity | exact TD_10011c0 | reflexivity
      | getr_resolve; regupd_resolve; rewrite H10; apply v_addi_0 ]
    | step_simpl ].
  (* opaque continuation marker: a0 = 0 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact TF_10011c4 | reflexivity | exact TD_10011c4 | reflexivity
      | getr_resolve; bveq ]
    | step_simpl ].
  (* li a3, 4 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 4);
      [ exact TF_10011c8 | reflexivity | exact TD_10011c8 | reflexivity
      | getr_resolve; bveq ]
    | step_simpl ].
  (* beqz a0 taken (the opaque marker is zero) -> 0x10011e4 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_beq_tk;
      [ exact TF_10011cc | reflexivity | exact TD_10011cc
      | getr_resolve; regupd_resolve; exact c_eq_0_true ]
    | norm_pc ].
  (* li a7, 214 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 214);
      [ exact TF_10011e4 | reflexivity | exact TD_10011e4 | reflexivity
      | getr_resolve; bveq ]
    | step_simpl ].
  (* ecall *)
  eapply mst_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ TF_10011e8 eq_refl) | ].
  match goal with
  | |- msteps _ {| ms_regs := ?R; ms_fregs := _; ms_pc_val := _; ms_svc_pending := _;
                   ms_resv := _; ms_fcsr := _; ms_mem := _; ms_rom := _ |} _ =>
      replace (getr R 17) with (Z_to_bv 64 214)
        by (getr_resolve; regupd_resolve; reflexivity)
  end.
  apply mst_refl. }
  - regupd_resolve. exact H2.
  - regupd_resolve. exact H8.
  - regupd_resolve. reflexivity.
  - regupd_resolve. reflexivity.
  - regupd_resolve. reflexivity.
Qed.

(* ================================================================= *)
(* From the return of the first brk (a0 = r <> 0, no wrap) to the      *)
(* second brk ecall (0x10011ec)                                        *)
(* ================================================================= *)

Lemma target_to_brk2 : forall regsB (r : word),
  reg_get regsB 2 = Z_to_bv 64 (bv_unsigned asp - 64) ->
  reg_get regsB 8 = ptrA ->
  reg_get regsB 11 = tnN ->
  reg_get regsB 13 = Z_to_bv 64 4 ->
  r <> Z_to_bv 64 0 ->
  (bv_unsigned r + Z.of_nat tnn < 2^64)%Z ->
  exists regs5,
    reg_get regs5 2 = Z_to_bv 64 (bv_unsigned asp - 64) /\
    reg_get regs5 8 = ptrA /\
    reg_get regs5 10 = r + tnN /\
    reg_get regs5 11 = tnN /\
    reg_get regs5 12 = r /\
    reg_get regs5 13 = Z_to_bv 64 4 /\
    reg_get regs5 14 = r + tnN /\
    msteps target_segs (mkst (regupd regsB 10 r) 0x10011ec tfmem trom)
      {| ms_regs := regs5; ms_fregs := fp_regs; ms_pc_val := (0x1001204 : word);
         ms_svc_pending := Some (Z_to_bv 64 214); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := tfmem; ms_rom := trom |}.
Proof.
  intros regsB r B2 B8 B11 B13 Hrnz Hw.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tnN_le as HnnLe.
  pose proof (u64_range r) as Hur.
  pose proof (word_neq0_unsigned r Hrnz) as Hur0.
  assert (Hurn : bv_unsigned (r + tnN) = (bv_unsigned r + Z.of_nat tnn)%Z).
  { rewrite u_add_small; rewrite u_tnN; lia. }
  eexists. repeat split.
  8: {
  (* beq a0, x0 fall-through (r <> 0) *)
  eapply mst_step;
    [ reflexivity
    | eapply step_beq_ft;
      [ exact TF_10011ec | reflexivity | exact TD_10011ec
      | getr_resolve; regupd_resolve; apply c_eq_0_false; exact Hur0 ]
    | step_simpl ].
  (* mv a2, a0 : a2 = r *)
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := r);
      [ exact TF_10011f0 | reflexivity | exact TD_10011f0 | reflexivity
      | getr_resolve; regupd_resolve; apply v_addi_0 ]
    | step_simpl ].
  (* add a4, a0, a1 : a4 = r + n *)
  eapply mst_step;
    [ reflexivity
    | eapply step_add_at with (v := r + tnN);
      [ exact TF_10011f4 | reflexivity | exact TD_10011f4 | reflexivity
      | getr_resolve; regupd_resolve; rewrite B11; reflexivity ]
    | step_simpl ].
  (* bltu a4, a0 fall-through (r <= r + n) *)
  eapply mst_step;
    [ reflexivity
    | eapply step_bltu_ft;
      [ exact TF_10011f8 | reflexivity | exact TD_10011f8
      | getr_resolve; regupd_resolve;
        rewrite c_ltu_ltb, Hurn; apply Z.ltb_ge; lia ]
    | step_simpl ].
  (* li a7, 214 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 214);
      [ exact TF_10011fc | reflexivity | exact TD_10011fc | reflexivity
      | getr_resolve; bveq ]
    | step_simpl ].
  (* mv a0, a4 : a0 = r + n *)
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := r + tnN);
      [ exact TF_1001200 | reflexivity | exact TD_1001200 | reflexivity
      | getr_resolve; regupd_resolve; apply v_addi_0 ]
    | step_simpl ].
  (* ecall *)
  eapply mst_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ TF_1001204 eq_refl) | ].
  match goal with
  | |- msteps _ {| ms_regs := ?R; ms_fregs := _; ms_pc_val := _; ms_svc_pending := _;
                   ms_resv := _; ms_fcsr := _; ms_mem := _; ms_rom := _ |} _ =>
      replace (getr R 17) with (Z_to_bv 64 214)
        by (getr_resolve; regupd_resolve; reflexivity)
  end.
  apply mst_refl. }
  - regupd_resolve. exact B2.
  - regupd_resolve. exact B8.
  - regupd_resolve. reflexivity.
  - regupd_resolve. exact B11.
  - regupd_resolve. reflexivity.
  - regupd_resolve. exact B13.
  - regupd_resolve. reflexivity.
Qed.

(* ================================================================= *)
(* The decimal print loop: body head 0x1001260, writes udec(v) into    *)
(* the stack scratch buffer at [asp-56 .. asp-33].                     *)
(* ================================================================= *)

Lemma target_udec_loop : forall f m (v k : Z) regs,
  (1 <= v)%Z -> (v < 2 ^ 64)%Z -> (v < 10 ^ Z.of_nat f)%Z ->
  (Z.of_nat (length (udec v)) <= k)%Z ->
  (k <= 23)%Z ->
  reg_get regs 10 = Z_to_bv 64 v ->
  reg_get regs 11 = Z_to_bv 64 k ->
  reg_get regs 12 = Z_to_bv 64 (bv_unsigned asp - 56) ->
  reg_get regs 13 = Z_to_bv 64 10 ->
  (* the digit buffer is a stack slot: the [sb] below is a machine store *)
  mem_grows awmem m ->
  exists regs',
    (forall x : reg, x <> 10 -> x <> 11 -> x <> 14 -> x <> 15 -> x <> 16 ->
       reg_get regs' x = reg_get regs x) /\
    reg_get regs' 11 = Z_to_bv 64 (k - Z.of_nat (length (udec v))) /\
    msteps target_segs (mkst regs 0x1001278 m trom)
      (mkst regs' 0x100129c
        (wbytes m
           (Z_to_bv 64 (bv_unsigned asp - 56 + (k + 1 - Z.of_nat (length (udec v)))))
           (udec v)) trom).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof (u64_range asp).
  induction f as [|f IH];
    intros m v k regs Hv1 Hv64 Hvf HLk Hk H10 H11 H12 H13 Hgrow.
  { assert (E0 : (10 ^ Z.of_nat 0 = 1)%Z) by reflexivity.
    rewrite E0 in Hvf. lia. }
  set (dg := (v mod 10)%Z).
  assert (Hdg : (0 <= dg < 10)%Z) by (unfold dg; apply Z.mod_pos_bound; lia).
  assert (Hdm : v = (10 * (v / 10) + dg)%Z)
    by (unfold dg; apply Z.div_mod; lia).
  assert (HL1 : (1 <= Z.of_nat (length (udec v)))%Z)
    by (pose proof (udec_len_pos v); lia).
  (* 0x1001278 divu a4, a0, a3 : a4 = v / 10 *)
  set (regs1 := regupd regs 14 (Z_to_bv 64 (v / 10))).
  assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001278 m trom)
               = MachineOk (mkst regs1 0x100127c m trom)).
  { rewrite (step_divu target_segs regs 0x1001278 m trom _ 14 10 13
               TF_1001278 eq_refl TD_1001278).
    - reduce_bv_eqb_ifs. wlits. unfold regs1. getr_resolve. rewrite H10, H13.
      replace (v_divu (Z_to_bv 64 v) (Z_to_bv 64 10))
        with (Z_to_bv 64 (v / 10)); [reflexivity|].
      apply bv_eq. rewrite v_divu_small by (u_norm; lia). u_norm; lia.
    - getr_resolve. rewrite H13. u_norm; lia. }
  (* 0x100127c add a5, a2, a1 : a5 = asp - 56 + k *)
  set (regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned asp - 56 + k))).
  assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x100127c m trom)
               = MachineOk (mkst regs2 0x1001280 m trom)).
  { rewrite (step_add_at target_segs regs1 0x100127c m trom _ 15 12 11
               (Z_to_bv 64 (bv_unsigned asp - 56 + k))
               TF_100127c eq_refl TD_100127c eq_refl).
    - wlits. reflexivity.
    - unfold regs1. getr_resolve. rewrite H12, H11.
      apply bv_eq. rewrite v_add_small by (u_norm; lia). u_norm; lia. }
  (* 0x1001280 mul a6, a4, a3 : a6 = (v / 10) * 10 *)
  set (regs3 := regupd regs2 16 (Z_to_bv 64 (v / 10 * 10))).
  assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x1001280 m trom)
               = MachineOk (mkst regs3 0x1001284 m trom)).
  { rewrite (step_mul_at target_segs regs2 0x1001280 m trom _ 16 14 13
               (Z_to_bv 64 (v / 10 * 10)) TF_1001280 eq_refl TD_1001280 eq_refl).
    - wlits. reflexivity.
    - unfold regs2, regs1. getr_resolve. rewrite H13.
      apply bv_eq. rewrite v_mul_small by (u_norm; lia). u_norm; lia. }
  (* 0x1001284 subw a0, a0, a6 : a0 = v mod 10 *)
  set (regs4 := regupd regs3 10 (Z_to_bv 64 dg)).
  assert (E4 : RiscvSemantics.step target_segs (mkst regs3 0x1001284 m trom)
               = MachineOk (mkst regs4 0x1001288 m trom)).
  { rewrite (step_subw target_segs regs3 0x1001284 m trom _ 10 10 16
               TF_1001284 eq_refl TD_1001284).
    reduce_bv_eqb_ifs. wlits. unfold regs4, regs3, regs2, regs1.
    getr_resolve. rewrite H10.
    replace (v_subw (Z_to_bv 64 v) (Z_to_bv 64 (v / 10 * 10)))
      with (Z_to_bv 64 dg); [reflexivity|].
    apply bv_eq. rewrite v_subw_small by (u_norm; lia). u_norm; lia. }
  (* 0x1001288 ori a0, a0, 48 : a0 = 48 + dg *)
  set (regs5 := regupd regs4 10 (Z_to_bv 64 (48 + dg))).
  assert (E5 : RiscvSemantics.step target_segs (mkst regs4 0x1001288 m trom)
               = MachineOk (mkst regs5 0x100128c m trom)).
  { rewrite (step_ori target_segs regs4 0x1001288 m trom _ 10 10 _
               TF_1001288 eq_refl TD_1001288).
    reduce_bv_eqb_ifs. wlits. unfold regs5, regs4.
    rewrite getr_same by reg_neq_tac.
    imm_norm. rewrite v_ori_lor by (u_norm; lia).
    replace (bv_unsigned (Z_to_bv 64 dg) + 48)%Z with (48 + dg)%Z
      by (u_norm; lia).
    reflexivity. }
  (* 0x100128c sb a0, 0(a5) : store the digit char at asp - 56 + k *)
  set (m1 := wbytes m (Z_to_bv 64 (bv_unsigned asp - 56 + k)) [Z_to_bv 8 (48 + dg)]).
  assert (E6 : RiscvSemantics.step target_segs (mkst regs5 0x100128c m trom)
               = MachineOk (mkst regs5 0x1001290 m1 trom)).
  { rewrite (step_sb_at target_segs regs5 0x100128c m trom _ 15 10 _
               (Z_to_bv 64 (bv_unsigned asp - 56 + k)) (Z_to_bv 8 (48 + dg))
               TF_100128c eq_refl TD_100128c).
    - wlits. reflexivity.
    - unfold regs5, regs4, regs3, regs2. getr_resolve. apply v_addi_0.
    - unfold regs5. rewrite getr_same by reg_neq_tac.
      rewrite u_Z2bv by lia. reflexivity.
    - eapply store_ok_mono; [exact Hgrow|].
      apply (store_ok_wrap_window_valid target_segs inp amb target_phdrs _ asp abrk _ 1 arnd
               Hvl Hlau);
        unfold stack_window_reach, stack_max_size; u_norm; lia. }
  (* 0x1001290 addi a1, a1, -1 : a1 = k - 1 *)
  set (regs7 := regupd regs5 11 (Z_to_bv 64 (k - 1))).
  assert (E7 : RiscvSemantics.step target_segs (mkst regs5 0x1001290 m1 trom)
               = MachineOk (mkst regs7 0x1001294 m1 trom)).
  { rewrite (step_addi_at target_segs regs5 0x1001290 m1 trom _ 11 11 _
               (Z_to_bv 64 (k - 1)) TF_1001290 eq_refl TD_1001290 eq_refl).
    - wlits. reflexivity.
    - unfold regs5, regs4, regs3, regs2, regs1. getr_resolve. rewrite H11.
      sp_norm. reflexivity. }
  (* 0x1001294 mv a0, a4 : a0 = v / 10 *)
  set (regs8 := regupd regs7 10 (Z_to_bv 64 (v / 10))).
  assert (E8 : RiscvSemantics.step target_segs (mkst regs7 0x1001294 m1 trom)
               = MachineOk (mkst regs8 0x1001298 m1 trom)).
  { rewrite (step_addi_at target_segs regs7 0x1001294 m1 trom _ 10 14 _
               (Z_to_bv 64 (v / 10)) TF_1001294 eq_refl TD_1001294 eq_refl).
    - wlits. reflexivity.
    - unfold regs7, regs5, regs4, regs3, regs2, regs1. getr_resolve.
      apply v_addi_0. }
  destruct (Z.le_gt_cases v 9) as [Hle9 | Hgt9].
  - (* single digit: bne falls through to 0x100129c *)
    assert (Hq0 : (v / 10 = 0)%Z) by (apply Z.div_small; lia).
    assert (Hudec : udec v = [Z_to_bv 8 (48 + dg)]).
    { unfold dg. rewrite Z.mod_small by lia. apply udec_single. lia. }
    assert (E9 : RiscvSemantics.step target_segs (mkst regs8 0x1001298 m1 trom)
                 = MachineOk (mkst regs8 0x100129c m1 trom)).
    { rewrite (step_bne_ft target_segs regs8 0x1001298 m1 trom _ 14 0 _
                 TF_1001298 eq_refl TD_1001298).
      - wlits. reflexivity.
      - unfold regs8, regs7, regs5, regs4, regs3, regs2, regs1.
        getr_resolve. rewrite Hq0. exact c_eq_0_true. }
    exists regs8. split; [|split].
    + intros x Hx10 Hx11 Hx14 Hx15 Hx16.
      unfold regs8, regs7, regs5, regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs8. rewrite regupd_other by reg_neq_tac.
      unfold regs7. rewrite regupd_same.
      rewrite Hudec. cbn [length]. f_equal.
    + rewrite Hudec.
      replace (wbytes m
                 (Z_to_bv 64 (bv_unsigned asp - 56
                              + (k + 1 - Z.of_nat (length [Z_to_bv 8 (48 + dg)]))))
                 [Z_to_bv 8 (48 + dg)])
        with m1.
      2:{ unfold m1. cbn [length]. f_equal. f_equal. lia. }
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      eapply mst_step; [reflexivity | exact E7 |].
      eapply mst_step; [reflexivity | exact E8 |].
      eapply mst_step; [reflexivity | exact E9 |].
      apply mst_refl.
  - (* multi-digit: bne taken back to 0x1001278 with v/10, k-1 *)
    assert (Hudec : udec v = udec (v / 10) ++ [Z_to_bv 8 (48 + dg)]).
    { unfold dg. apply udec_step; lia. }
    assert (HLv : Z.of_nat (length (udec v))
                  = (Z.of_nat (length (udec (v / 10))) + 1)%Z).
    { rewrite Hudec. rewrite length_app. cbn [length]. lia. }
    assert (Hv10_1 : (1 <= v / 10)%Z)
      by (apply Z.div_le_lower_bound; lia).
    assert (Hv10_64 : (v / 10 < 2 ^ 64)%Z)
      by (pose proof (Z.div_le_upper_bound v 10 v ltac:(lia) ltac:(lia)); lia).
    assert (Hv10_f : (v / 10 < 10 ^ Z.of_nat f)%Z).
    { apply Z.div_lt_upper_bound; [lia|].
      replace (10 * 10 ^ Z.of_nat f)%Z with (10 ^ Z.of_nat (S f))%Z
        by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity).
      exact Hvf. }
    assert (Hr8_10 : reg_get regs8 10 = Z_to_bv 64 (v / 10)).
    { unfold regs8. apply regupd_same. }
    assert (Hr8_11 : reg_get regs8 11 = Z_to_bv 64 (k - 1)).
    { unfold regs8. rewrite regupd_other by reg_neq_tac.
      unfold regs7. apply regupd_same. }
    assert (Hr8_12 : reg_get regs8 12 = Z_to_bv 64 (bv_unsigned asp - 56)).
    { unfold regs8, regs7, regs5, regs4, regs3, regs2, regs1.
      rewrite !regupd_other by reg_neq_tac. exact H12. }
    assert (Hr8_13 : reg_get regs8 13 = Z_to_bv 64 10).
    { unfold regs8, regs7, regs5, regs4, regs3, regs2, regs1.
      rewrite !regupd_other by reg_neq_tac. exact H13. }
    assert (E9 : RiscvSemantics.step target_segs (mkst regs8 0x1001298 m1 trom)
                 = MachineOk (mkst regs8 0x1001278 m1 trom)).
    { rewrite (step_bne_tk target_segs regs8 0x1001298 m1 trom _ 14 0 _
                 TF_1001298 eq_refl TD_1001298).
      - wlits. reflexivity.
      - unfold regs8, regs7, regs5, regs4, regs3, regs2, regs1.
        getr_resolve. apply c_eq_0_false. u_norm; lia. }
    destruct (IH m1 ((v / 10)%Z) ((k - 1)%Z) regs8 Hv10_1 Hv10_64 Hv10_f
                ltac:(lia) ltac:(lia) Hr8_10 Hr8_11 Hr8_12 Hr8_13
                ltac:(unfold m1; solve_mem_grows))
      as (regs' & Hag' & H11' & Hms').
    exists regs'. split; [|split].
    + intros x Hx10 Hx11 Hx14 Hx15 Hx16.
      rewrite (Hag' x Hx10 Hx11 Hx14 Hx15 Hx16).
      unfold regs8, regs7, regs5, regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + rewrite H11'. f_equal. rewrite HLv. lia.
    + (* memory reconciliation *)
      assert (HL'k : (Z.of_nat (length (udec (v / 10))) <= k)%Z)
        by (rewrite HLv in HLk; lia).
      replace (wbytes m
                 (Z_to_bv 64 (bv_unsigned asp - 56
                              + (k + 1 - Z.of_nat (length (udec v)))))
                 (udec v))
        with (wbytes m1
                (Z_to_bv 64 (bv_unsigned asp - 56
                             + (k - 1 + 1 - Z.of_nat (length (udec (v / 10))))))
                (udec (v / 10))).
      2:{ unfold m1.
          replace (k - 1 + 1 - Z.of_nat (length (udec (v / 10))))%Z
            with (k - Z.of_nat (length (udec (v / 10))))%Z by lia.
          replace (k + 1 - Z.of_nat (length (udec v)))%Z
            with (k - Z.of_nat (length (udec (v / 10))))%Z
            by (rewrite HLv; lia).
          rewrite Hudec. rewrite wbytes_app.
          replace (Z_to_bv 64 (bv_unsigned asp - 56
                               + (k - Z.of_nat (length (udec (v / 10)))))
                   + nat_to_word (length (udec (v / 10))))
            with (Z_to_bv 64 (bv_unsigned asp - 56 + k))
            by (rewrite word_add_nat; f_equal; u_norm; lia).
          symmetry. apply wbytes_disjoint_comm; cbn [length]; u_norm; lia. }
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      eapply mst_step; [reflexivity | exact E7 |].
      eapply mst_step; [reflexivity | exact E8 |].
      eapply mst_step; [reflexivity | exact E9 |].
      exact Hms'.
Qed.

(* ================================================================= *)
(* The print tail: 0x1001298, writes the decimal string then newline,  *)
(* then exits 0.  Entered from both the sum=0 and sum>0 paths with     *)
(* a1 = 24 - |udec sum| and the digits already in the scratch buffer.  *)
(* ================================================================= *)

Lemma target_print_tail : forall regs (M : word -> option byte) (sum : Z),
  (0 <= sum)%Z -> (sum < 2 ^ 64)%Z ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64) ->
  reg_get regs 11 = Z_to_bv 64 (24 - Z.of_nat (length (udec sum))) ->
  M (0x1000158 : word) = None ->
  rdn target_segs M (Z_to_bv 64 (bv_unsigned asp - 24)) 8%nat
    = Some (word_to_le_bytes 8 (0x100117c : word)) ->
  rdn target_segs M (Z_to_bv 64 (bv_unsigned asp - 32)) 8%nat
    = Some (word_to_le_bytes 8 asp) ->
  (* the scratch stores below are machine stores into the stack frame *)
  mem_grows awmem M ->
  to_wallexit target_segs (Z_to_bv 64 1)
    [udec sum; [Z_to_bv 8 10]] (Z_to_bv 64 0)
    (mkst regs 0x10012b0
      (wbytes M
         (Z_to_bv 64 (bv_unsigned asp - 56 + (24 - Z.of_nat (length (udec sum)))))
         (udec sum)) trom).
Proof.
  intros regs M sum Hsum0 Hsum H2 H11 Hnl Hra Hs0 Hgrow.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof (u64_range asp).
  assert (HLv1 : (1 <= Z.of_nat (length (udec sum)))%Z)
    by (pose proof (udec_len_pos sum); lia).
  assert (HLv20 : (Z.of_nat (length (udec sum)) <= 20)%Z)
    by (pose proof (udec_len_le sum Hsum0 Hsum); lia).
  set (Lv := Z.of_nat (length (udec sum))) in *.
  set (base := Z_to_bv 64 (bv_unsigned asp - 56 + (24 - Lv))) in *.
  set (Md := wbytes M base (udec sum)) in *.
  (* 0x10012b0 addi a0, sp, 8 : a0 = asp - 56 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 (bv_unsigned asp - 56));
      [ exact TF_10012b0 | reflexivity | exact TD_10012b0 | reflexivity
      | getr_resolve; rewrite H2; sp_norm; f_equal; lia ]
    | step_simpl ].
  (* 0x10012b4 li a2, 24 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 24);
      [ exact TF_10012b4 | reflexivity | exact TD_10012b4 | reflexivity
      | getr_resolve; bveq ]
    | step_simpl ].
  (* 0x10012b8 add a0, a0, a1 : a0 = base *)
  chain_step;
    [ reflexivity
    | eapply step_add_at with (v := base);
      [ exact TF_10012b8 | reflexivity | exact TD_10012b8 | reflexivity
      | getr_resolve; regupd_resolve; rewrite H11;
        unfold base; apply bv_eq;
        rewrite v_add_small by (u_norm; lia); u_norm; lia ]
    | step_simpl ].
  (* 0x10012bc sub a1, a2, a1 : a1 = Lv *)
  chain_step;
    [ reflexivity
    | eapply step_sub_at with (v := Z_to_bv 64 Lv);
      [ exact TF_10012bc | reflexivity | exact TD_10012bc | reflexivity
      | getr_resolve; regupd_resolve; rewrite H11;
        apply bv_eq; rewrite v_sub_small by (u_norm; lia); u_norm; lia ]
    | step_simpl ].
  (* 0x10012c0 auipc ra, 0 ; jalr ra, 72(ra) -> put 0x1001308 *)
  chain_step;
    [ reflexivity
    | eapply step_auipc_at with (v := (0x10012c0 : word));
      [ exact TF_10012c0 | reflexivity | exact TD_10012c0 | reflexivity
      | bveq ]
    | step_simpl ].
  stepjr TF_10012c4 TD_10012c4 (0x10012c0 : word) ltac:(getr_resolve; regupd_resolve; reflexivity).
  (* put(base, Lv) : writes udec sum *)
  eapply (target_put _ Md (udec sum) base (Z_to_bv 64 Lv) (0x10012c8 : word)
            [[Z_to_bv 8 10]] (Z_to_bv 64 0)).
  - regupd_resolve. bveq.
  - regupd_resolve. reflexivity.
  - regupd_resolve. reflexivity.
  - u_norm; lia.
  - u_norm; lia.
  - (* [vfs_write]'s [access_ok] on the digit string *)
    rewrite u_Z2bv by lia. unfold base, TASK_SIZE. u_norm; fold Lv; lia.
  - bveq.
  - (* read the digit string back *)
    replace (word_to_nat (Z_to_bv 64 Lv)) with (length (udec sum)).
    2:{ unfold word_to_nat. rewrite u_Z2bv by lia. unfold Lv. lia. }
    unfold Md. apply rdn_wbytes_hit. unfold base. u_norm; fold Lv; lia.
  - (* continuation after the first write *)
    intros regs1 Hag1 H1_10.
    (* 0x10012c8 beq a0, x0 taken -> 0x10012d4 *)
    chain_step;
      [ reflexivity
      | eapply step_beq_tk;
        [ exact TF_10012c8 | reflexivity | exact TD_10012c8
        | getr_resolve; rewrite H1_10; exact c_eq_0_true ]
      | norm_pc ].
    (* 0x10012d4 lui a0, 0x1000000 *)
    chain_step;
      [ reflexivity
      | eapply step_lui_at with (v := (0x1000000 : word));
        [ exact TF_10012d4 | reflexivity | exact TD_10012d4 | reflexivity
        | bveq ]
      | step_simpl ].
    (* 0x10012d8 addi a0, a0, 344 : a0 = 0x1000158 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := (0x1000158 : word));
        [ exact TF_10012d8 | reflexivity | exact TD_10012d8 | reflexivity
        | getr_resolve; regupd_resolve; bveq ]
      | step_simpl ].
    (* 0x10012dc li a1, 1 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 1);
        [ exact TF_10012dc | reflexivity | exact TD_10012dc | reflexivity
        | getr_resolve; bveq ]
      | step_simpl ].
    (* 0x10012e0 auipc ra, 0 ; jalr ra, 40(ra) -> put 0x1001308 *)
    chain_step;
      [ reflexivity
      | eapply step_auipc_at with (v := (0x10012e0 : word));
        [ exact TF_10012e0 | reflexivity | exact TD_10012e0 | reflexivity
        | bveq ]
      | step_simpl ].
    stepjr TF_10012e4 TD_10012e4 (0x10012e0 : word) ltac:(getr_resolve; regupd_resolve; reflexivity).
    (* put(0x1000158, 1) : writes the newline *)
    eapply (target_put _ Md [Z_to_bv 8 10] (0x1000158 : word) (Z_to_bv 64 1)
              (0x10012e8 : word) [] (Z_to_bv 64 0)).
    + regupd_resolve. bveq.
    + regupd_resolve. reflexivity.
    + regupd_resolve. reflexivity.
    + u_norm; lia.
    + u_norm; lia.
    + (* [vfs_write]'s [access_ok] on the newline byte *)
      change (bv_unsigned (0x1000158 : word)) with 0x1000158%Z.
      rewrite u_Z2bv by lia. unfold TASK_SIZE. lia.
    + bveq.
    + (* read the newline byte *)
      replace (word_to_nat (Z_to_bv 64 1)) with 1%nat by reflexivity.
      unfold Md.
      rewrite rdn_wbytes_below
        by (unfold base;
            change (bv_unsigned (0x1000158 : word)) with 0x1000158%Z;
            u_norm; fold Lv; lia).
      apply read_newline_t. exact Hnl.
    + (* continuation after the second write : exit 0 *)
      intros regs2 Hag2 H2_10.
      (* sltiu a0, a0, 1 ; addi a0, a0, -1 ; andi a3, a0, 5 *)
      stepi TF_10012e8 TD_10012e8.
      stepi TF_10012ec TD_10012ec.
      stepi TF_10012f0 TD_10012f0.
      stepj TF_10012f4 TD_10012f4.
      apply target_exit.
      * regupd_resolve.
        rewrite (Hag2 2) by reg_neq_tac.
        regupd_resolve.
        rewrite (Hag1 2) by reg_neq_tac.
        regupd_resolve. exact H2.
      * regupd_resolve. getr_resolve. regupd_resolve.
        rewrite H2_10. bveq.
      * vm_compute. reflexivity.
      * unfold Md.
        rewrite rdn_wbytes_disjoint
          by (unfold base; u_norm; fold Lv; lia).
        exact Hra.
      * unfold Md.
        rewrite rdn_wbytes_disjoint
          by (unfold base; u_norm; fold Lv; lia).
        exact Hs0.
Qed.

(* ================================================================= *)
(* target_success: from the sum-loop exit (0x100124c) to exit 0,       *)
(* writing [udec (sumb targ1); "\n"].                                  *)
(* ================================================================= *)

Lemma target_success : forall regs (M : word -> option byte),
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64) ->
  reg_get regs 10 = Z_to_bv 64 (sumb targ1) ->
  M (0x1000158 : word) = None ->
  rdn target_segs M (Z_to_bv 64 (bv_unsigned asp - 24)) 8%nat
    = Some (word_to_le_bytes 8 (0x100117c : word)) ->
  rdn target_segs M (Z_to_bv 64 (bv_unsigned asp - 32)) 8%nat
    = Some (word_to_le_bytes 8 asp) ->
  (* the scratch stores below are machine stores into the stack frame *)
  mem_grows awmem M ->
  to_wallexit target_segs (Z_to_bv 64 1) (outbufs targ1) (Z_to_bv 64 0)
    (mkst regs 0x1001264 M trom).
Proof.
  intros regs M H2 H10 Hnl Hra Hs0 Hgrow.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tnN_le as HnnLe.
  pose proof targ1_bytes as Hbytes.
  pose proof (sumb_nonneg targ1) as Hsum0.
  assert (Hnn : tnn = length targ1) by reflexivity.
  assert (Hsum64 : (sumb targ1 < 2 ^ 64)%Z).
  { pose proof (sumb_le targ1 Hbytes) as Hle. lia. }
  assert (HLv20 : (Z.of_nat (length (udec (sumb targ1))) <= 20)%Z)
    by (pose proof (udec_len_le (sumb targ1) Hsum0 Hsum64); lia).
  assert (HLv1 : (1 <= Z.of_nat (length (udec (sumb targ1))))%Z)
    by (pose proof (udec_len_pos (sumb targ1)); lia).
  unfold outbufs.
  destruct (Z.eq_dec (sumb targ1) 0%Z) as [Hsz | Hnz].
  - (* sum = 0 : the '0' path *)
    (* 0x1001264 beq a0, x0 taken -> 0x10012a4 *)
    chain_step;
      [ reflexivity
      | eapply step_beq_tk;
        [ exact TF_1001264 | reflexivity | exact TD_1001264
        | getr_resolve; rewrite H10, Hsz; exact c_eq_0_true ]
      | norm_pc ].
    (* 0x10012a4 li a0, 48 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 48);
        [ exact TF_10012a4 | reflexivity | exact TD_10012a4 | reflexivity
        | getr_resolve; bveq ]
      | step_simpl ].
    (* 0x10012a8 sb a0, 31(sp) : store '0' at asp - 33 *)
    chain_step;
      [ reflexivity
      | eapply step_sb_at with (a := Z_to_bv 64 (bv_unsigned asp - 33))
                               (b := Z_to_bv 8 48);
        [ exact TF_10012a8 | reflexivity | exact TD_10012a8
        | getr_resolve; regupd_resolve; rewrite H2; sp_norm; f_equal; lia
        | getr_resolve; regupd_resolve; bveq
        | solve_store_ok_inv ]
      | step_simpl ].
    (* 0x10012ac li a1, 23 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 23);
        [ exact TF_10012ac | reflexivity | exact TD_10012ac | reflexivity
        | getr_resolve; bveq ]
      | step_simpl ].
    (* now at 0x10012b0 with a1 = 23 = 24 - |udec 0| *)
    assert (Hudec0 : udec (sumb targ1) = [Z_to_bv 8 48])
      by (rewrite Hsz; reflexivity).
    match goal with
    |- to_wallexit _ _ _ _ (mkst ?R _ ?Mem _) =>
        replace Mem with
          (wbytes M
             (Z_to_bv 64 (bv_unsigned asp - 56
                          + (24 - Z.of_nat (length (udec (sumb targ1))))))
             (udec (sumb targ1)))
    end.
    2:{ rewrite Hudec0. cbn [length]. f_equal. f_equal. lia. }
    apply target_print_tail.
    + exact Hsum0.
    + exact Hsum64.
    + regupd_resolve. exact H2.
    + regupd_resolve. rewrite Hsz. reflexivity.
    + exact Hnl.
    + exact Hra.
    + exact Hs0.
    + solve_mem_grows.
  - (* sum > 0 : the udec loop path *)
    assert (Hsum1 : (1 <= sumb targ1)%Z) by lia.
    (* 0x1001264 beq a0, x0 fall-through *)
    chain_step;
      [ reflexivity
      | eapply step_beq_ft;
        [ exact TF_1001264 | reflexivity | exact TD_1001264
        | getr_resolve; rewrite H10; apply c_eq_0_false; u_norm; lia ]
      | step_simpl ].
    (* 0x1001268 li a1, 23 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 23);
        [ exact TF_1001268 | reflexivity | exact TD_1001268 | reflexivity
        | getr_resolve; bveq ]
      | step_simpl ].
    (* 0x100126c addi a2, sp, 8 : a2 = asp - 56 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 (bv_unsigned asp - 56));
        [ exact TF_100126c | reflexivity | exact TD_100126c | reflexivity
        | getr_resolve; regupd_resolve; rewrite H2; sp_norm; f_equal; lia ]
      | step_simpl ].
    (* 0x1001270 li a3, 10 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 10);
        [ exact TF_1001270 | reflexivity | exact TD_1001270 | reflexivity
        | getr_resolve; bveq ]
      | step_simpl ].
    (* 0x1001274 beq a0, x0 fall-through (sum <> 0) *)
    chain_step;
      [ reflexivity
      | eapply step_beq_ft;
        [ exact TF_1001274 | reflexivity | exact TD_1001274
        | getr_resolve; regupd_resolve; rewrite H10;
          apply c_eq_0_false; u_norm; lia ]
      | step_simpl ].
    (* the decimal loop *)
    assert (Hf : (sumb targ1 < 10 ^ Z.of_nat 25)%Z).
    { eapply Z.lt_le_trans; [exact Hsum64 | vm_compute; discriminate]. }
    match goal with
    |- to_wallexit _ _ _ _ (mkst ?R _ _ _) =>
        destruct (target_udec_loop 25 M (sumb targ1) 23%Z R
                    Hsum1 Hsum64 Hf
                    ltac:(lia) ltac:(lia)
                    ltac:(regupd_resolve; exact H10)
                    ltac:(regupd_resolve; reflexivity)
                    ltac:(regupd_resolve; reflexivity)
                    ltac:(regupd_resolve; reflexivity)
                    ltac:(solve_mem_grows))
          as (regsU & HagU & H11U & HmsU)
    end.
    eapply msteps_to_wallexit; [exact HmsU|].
    (* 0x100129c addi a1, a1, 1 : a1 = 24 - Lv *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at
          with (v := Z_to_bv 64 (24 - Z.of_nat (length (udec (sumb targ1)))));
        [ exact TF_100129c | reflexivity | exact TD_100129c | reflexivity
        | getr_resolve; rewrite H11U; sp_norm; f_equal; lia ]
      | step_simpl ].
    (* 0x10012a0 j +16 -> 0x10012b0 *)
    chain_step;
      [ reflexivity
      | exact (step_jal_x0 _ _ _ _ _ _ _ TF_10012a0 eq_refl TD_10012a0)
      | norm_pc ].
    match goal with
    |- to_wallexit _ _ _ _ (mkst ?R _ ?Mem _) =>
        replace Mem with
          (wbytes M
             (Z_to_bv 64 (bv_unsigned asp - 56
                          + (24 - Z.of_nat (length (udec (sumb targ1))))))
             (udec (sumb targ1)))
    end.
    2:{ f_equal; f_equal; lia. }
    apply target_print_tail.
    + exact Hsum0.
    + exact Hsum64.
    + regupd_resolve. rewrite (HagU 2) by reg_neq_tac.
      regupd_resolve. exact H2.
    + regupd_resolve. reflexivity.
    + exact Hnl.
    + exact Hra.
    + exact Hs0.
    + solve_mem_grows.
Qed.

(* ================================================================= *)
(* target_run_empty: the n = 0 defined run (second brk is a keep, so   *)
(* no grant; the empty string prints "0\n").                           *)
(* ================================================================= *)

Lemma target_run_empty : (tnn = 0)%nat -> forall regs5 (r : word),
  (bv_unsigned r + Z.of_nat tnn < 2 ^ 64)%Z ->
  reg_get regs5 2 = Z_to_bv 64 (bv_unsigned asp - 64) ->
  reg_get regs5 11 = tnN ->
  reg_get regs5 12 = r ->
  reg_get regs5 14 = r + tnN ->
  to_wallexit target_segs (Z_to_bv 64 1) (outbufs targ1) (Z_to_bv 64 0)
    (mkst (regupd regs5 10 (r + tnN)) 0x1001208 tfmem trom).
Proof.
  intros Hnn0 regs5 r Hrw H2 H11 H12 H14.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  assert (Harg : targ1 = []) by (apply length_zero_iff_nil; exact Hnn0).
  assert (HnN0 : tnN = Z_to_bv 64 0).
  { unfold oob_read_bug_ns_target.tnN. rewrite Hnn0. reflexivity. }
  (* 0x1001208 bne a0, a4 fall-through (r+n = r+n) *)
  chain_step;
    [ reflexivity
    | eapply step_bne_ft;
      [ exact TF_1001208 | reflexivity | exact TD_1001208
      | getr_resolve; regupd_resolve; rewrite H14; apply c_eq_refl ]
    | step_simpl ].
  (* 0x100120c mv a0, a2 : a0 = r *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := r);
      [ exact TF_100120c | reflexivity | exact TD_100120c | reflexivity
      | getr_resolve; regupd_resolve; rewrite H12; apply v_addi_0 ]
    | step_simpl ].
  (* 0x1001210 mv a3, a1 : a3 = 0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact TF_1001210 | reflexivity | exact TD_1001210 | reflexivity
      | getr_resolve; regupd_resolve; rewrite H11, HnN0; apply v_addi_0 ]
    | step_simpl ].
  (* 0x1001214 beq a1, x0 taken (n = 0) -> 0x1001230 *)
  chain_step;
    [ reflexivity
    | eapply step_beq_tk;
      [ exact TF_1001214 | reflexivity | exact TD_1001214
      | getr_resolve; regupd_resolve; rewrite H11, HnN0; exact c_eq_0_true ]
    | norm_pc ].
  (* 0x1001230 li a0, 0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact TF_1001230 | reflexivity | exact TD_1001230 | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | step_simpl ].
  (* 0x1001234 bgeu a3, a1 taken (0 >= 0) -> 0x1001264 *)
  chain_step;
    [ reflexivity
    | eapply step_bgeu_tk;
      [ exact TF_1001234 | reflexivity | exact TD_1001234
      | getr_resolve; regupd_resolve; rewrite H11, HnN0;
        vm_compute; reflexivity ]
    | norm_pc ].
  (* print (sum = 0) *)
  apply target_success.
  - regupd_resolve. exact H2.
  - regupd_resolve. rewrite Harg. reflexivity.
  - apply tfmem_low_none.
    change (bv_unsigned (0x1000158 : word)) with 0x1000158%Z. lia.
  - apply read_slot_ra_t.
  - apply read_slot_s0_t.
  - unfold tfmem. solve_mem_grows.
Qed.

(* ================================================================= *)
(* target_run_success: from the second brk's SUCCESS post-state, run   *)
(* the copy + page-padded byte-sum + print to exit 0 (n > 0).         *)
(* ================================================================= *)

Lemma target_run_success : forall regs5 (r grant : word),
  (bv_unsigned tnN <= bv_unsigned grant)%Z ->
  (Z.of_nat (8 * ((tnn + 7) / 8)) <= bv_unsigned grant)%Z ->
  (bv_unsigned r + bv_unsigned grant <= bv_unsigned asp - stack_max_size)%Z ->
  (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + Z.of_nat tnn <= bv_unsigned asp - stack_max_size)%Z ->
  region_free (segments_reserved target_segs) r tnN = true ->
  region_free (segments_reserved target_segs) r grant = true ->
  (tnn <> 0)%nat ->
  reg_get regs5 2 = Z_to_bv 64 (bv_unsigned asp - 64) ->
  reg_get regs5 8 = ptrA ->
  reg_get regs5 11 = tnN ->
  reg_get regs5 12 = r ->
  reg_get regs5 14 = r + tnN ->
  to_wallexit target_segs (Z_to_bv 64 1) (outbufs targ1) (Z_to_bv 64 0)
    (mkst (regupd regs5 10 (r + tnN)) 0x1001208 (zmem tfmem r grant) trom).
Proof.
  intros regs5 r grant Hgrant Htotalgrant Hgrantceil Hr0 Hceil Hfree Hphysfree
    Hnnz H2 H8 H11 H12 H14.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tnN_le as HnnLe.
  pose proof ptrA_lo as Hplo. pose proof ptrA_hi as Hphi.
  pose proof (u64_range r) as Hur.
  assert (Hnn : tnn = length targ1) by reflexivity.
  assert (Hbelow : (bv_unsigned r + bv_unsigned grant <= bv_unsigned asp - 8388608)%Z)
    by exact Hgrantceil.
  assert (Hurn : bv_unsigned (r + tnN) = (bv_unsigned r + Z.of_nat tnn)%Z).
  { rewrite u_add_small; rewrite u_tnN; lia. }
  assert (Hrw : (bv_unsigned r + Z.of_nat tnn < 2 ^ 64)%Z).
  { change (2 ^ 64)%Z with 18446744073709551616%Z. lia. }
  set (chunks := ((tnn + 7) / 8)%nat).
  set (total := (8 * chunks)%nat).
  pose proof (Nat.div_mod (tnn + 7) 8 ltac:(lia)) as Hdiv8.
  pose proof (Nat.mod_upper_bound (tnn + 7) 8 ltac:(lia)) as Hmod8.
  assert (Hchunks : (1 <= chunks)%nat) by (unfold chunks; lia).
  assert (Hstop : (8 * (chunks - 1) < tnn <= 8 * chunks)%nat)
    by (unfold chunks in *; lia).
  assert (Htotalgrant' : (Z.of_nat total <= bv_unsigned grant)%Z).
  { unfold total, chunks. exact Htotalgrant. }
  assert (Htotalrw : (bv_unsigned r + Z.of_nat total < 2 ^ 64)%Z).
  { change (2 ^ 64)%Z with 18446744073709551616%Z. lia. }
  set (mem0 := zmem tfmem r grant).
  set (M := wbytes mem0 r targ1).
  assert (Hstr0 : rdn target_segs mem0 ptrA (S tnn) = Some (targ1 ++ [Z_to_bv 8 0])).
  { unfold mem0. rewrite rdn_zmem_out by (rewrite ?u_tnN; lia).
    apply read_str_t. }
  (* 0x1001208 bne a0, a4 fall-through (r+n = r+n) *)
  chain_step;
    [ reflexivity
    | eapply step_bne_ft;
      [ exact TF_1001208 | reflexivity | exact TD_1001208
      | getr_resolve; regupd_resolve; rewrite H14; apply c_eq_refl ]
    | step_simpl ].
  (* 0x100120c mv a0, a2 : a0 = r *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := r);
      [ exact TF_100120c | reflexivity | exact TD_100120c | reflexivity
      | getr_resolve; regupd_resolve; rewrite H12; apply v_addi_0 ]
    | step_simpl ].
  (* 0x1001210 mv a3, a1 : a3 = n *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := tnN);
      [ exact TF_1001210 | reflexivity | exact TD_1001210 | reflexivity
      | getr_resolve; regupd_resolve; rewrite H11; apply v_addi_0 ]
    | step_simpl ].
  (* 0x1001214 beq a1, x0 fall-through (n <> 0) *)
  chain_step;
    [ reflexivity
    | eapply step_beq_ft;
      [ exact TF_1001214 | reflexivity | exact TD_1001214
      | getr_resolve; regupd_resolve; rewrite H11;
        apply c_eq_0_false; rewrite u_tnN; lia ]
    | step_simpl ].
  (* the forward copy loop, d = tnn *)
  match goal with
  |- to_wallexit _ _ _ _ (mkst ?R _ _ _) =>
      destruct (target_copy r mem0
                  ltac:(unfold mem0; apply store_grant_zmem_prefix;
                        [ exact Hgrant
                        | change (2 ^ 64)%Z with 18446744073709551616%Z; lia ])
                  Hstr0 Hfree Hr0 Hceil Hrw tnn R
                  ltac:(lia) (Nat.le_refl tnn)
                  ltac:(regupd_resolve; rewrite H8, Nat.sub_diag;
                        symmetry; apply word_add_0_r)
                  ltac:(regupd_resolve; rewrite Nat.sub_diag;
                        symmetry; apply word_add_0_r)
                  ltac:(regupd_resolve; reflexivity))
        as (regsC & HagC & H8C & H10C & H13C & HmsC)
  end.
  replace (wbytes mem0 r (firstn (tnn - tnn) targ1)) with mem0 in HmsC
    by (rewrite Nat.sub_diag; cbn [firstn wbytes]; reflexivity).
  eapply msteps_to_wallexit; [exact HmsC|].
  fold M.
  (* 0x1001230 li a0, 0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact TF_1001230 | reflexivity | exact TD_1001230 | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | step_simpl ].
  (* 0x1001234 bgeu a3, a1 fall-through (0 < n) *)
  chain_step;
    [ reflexivity
    | eapply step_bgeu_ft;
      [ exact TF_1001234 | reflexivity | exact TD_1001234
      | getr_resolve; regupd_resolve; rewrite H13C;
        rewrite (HagC 11) by reg_neq_tac; regupd_resolve; rewrite H11;
        rewrite c_ltu_ltb; apply Z.ltb_lt;
        rewrite u_tnN; u_norm; lia ]
    | step_simpl ].
  (* the byte-sum loop, m = tnn/8 chunks *)
  assert (HbufM : rdn target_segs M r tnn = Some targ1).
  { unfold M. rewrite Hnn. apply rdn_wbytes_hit. rewrite <- Hnn. lia. }
  assert (Hbyte : forall i, (i < total)%nat ->
            rdn target_segs M (r + nat_to_word i) 1%nat
            = Some [nth i targ1 (Z_to_bv 8 0)]).
  { intros i Hi. destruct (lt_dec i tnn) as [Hin|Hpad].
    - exact (rdn_nth _ _ _ _ _ i HbufM Hin).
    - unfold M. rewrite rdn_wbytes_disjoint.
      + unfold mem0. rewrite nth_overflow by (rewrite <- Hnn; lia).
        apply rdn_zmem_in1. rewrite word_add_nat, u_Z2bv by lia. lia.
      + rewrite <- Hnn, word_add_nat, u_Z2bv by lia. lia.
      + rewrite word_add_nat, u_Z2bv by lia. lia. }
  match goal with
  |- to_wallexit _ _ _ _ (mkst ?R _ _ _) =>
      destruct (target_sum M r total Hbyte Htotalrw chunks 0%nat R
                  Hchunks Hstop ltac:(reflexivity)
                  ltac:(regupd_resolve; reflexivity)
                  ltac:(regupd_resolve; rewrite (HagC 11) by reg_neq_tac;
                        regupd_resolve; exact H11)
                  ltac:(regupd_resolve; rewrite (HagC 12) by reg_neq_tac;
                        regupd_resolve; rewrite H12;
                        symmetry; apply word_add_0_r)
                  ltac:(regupd_resolve; exact H13C))
        as (regsS & HagS & H10S & HmsS)
  end.
  eapply msteps_to_wallexit; [exact HmsS|].
  (* print *)
  apply target_success.
  - rewrite (HagS 2) by reg_neq_tac.
    regupd_resolve.
    rewrite (HagC 2) by reg_neq_tac.
    regupd_resolve. exact H2.
  - exact H10S.
  - (* M 0x1000158 = None *)
    assert (Hdisj : (0x1000158 + 1 <= bv_unsigned r
                     \/ bv_unsigned r + bv_unsigned grant <= 0x1000158)%Z).
    { destruct (target_free_cases r grant Hphysfree ltac:(rewrite u_tnN in Hgrant; lia))
        as [Hc|Hc]; [right; lia | left; lia]. }
    assert (HMt : M (0x1000158 : word) = tfmem (0x1000158 : word)).
    { unfold M. destruct Hdisj as [Hd|Hd].
      - rewrite wbytes_below
          by (try change (bv_unsigned (0x1000158 : word)) with 0x1000158%Z;
              rewrite <- ?Hnn; lia).
        unfold mem0. apply zmem_out. left.
        change (bv_unsigned (0x1000158 : word)) with 0x1000158%Z. lia.
      - rewrite wbytes_above
          by (change (bv_unsigned (0x1000158 : word)) with 0x1000158%Z;
              rewrite <- Hnn; lia).
        unfold mem0. apply zmem_out. right.
        change (bv_unsigned (0x1000158 : word)) with 0x1000158%Z.
        lia. }
    rewrite HMt. apply tfmem_low_none.
    change (bv_unsigned (0x1000158 : word)) with 0x1000158%Z. lia.
  - (* frame ra slot *)
    erewrite rdn_ext; [ apply read_slot_ra_t | u_norm; lia | ].
    intros x Hx. revert Hx. u_norm. intro Hx. unfold M.
    rewrite wbytes_above by (rewrite <- Hnn; lia).
    unfold mem0. rewrite zmem_out by (right; lia). reflexivity.
  - (* frame s0 slot *)
    erewrite rdn_ext; [ apply read_slot_s0_t | u_norm; lia | ].
    intros x Hx. revert Hx. u_norm. intro Hx. unfold M.
    rewrite wbytes_above by (rewrite <- Hnn; lia).
    unfold mem0. rewrite zmem_out by (right; lia). reflexivity.
  - unfold M, mem0, tfmem. solve_mem_grows.
Qed.

(* ================================================================= *)
(* target_outcomes: the shared brk outcome set for every length        *)
(* ================================================================= *)

Hypothesis Hbrk_mod : (bv_unsigned abrk mod page_size = 0)%Z.

Local Abbreviation RT := (run_segments target_segs inp asp amb).

(** The run's outcome set, over the run's segment list and initial model
    (the vDSO counter, and the vDSO pair in the brk ledger
    [State.init_reserved]).  [Hmb] is [Run.valid_mmap_base]'s floor, which
    keeps the vDSO pair far above the heap ([run_ledger_free]); [Hrd] is
    the stdout reader [Run.valid_input] pins, which the write nodes need. *)
Lemma target_outcomes :
  (mmap_base_min <= bv_unsigned amb)%Z ->
  in_channel_reader inp = true ->
  (Z.of_nat tnn <= 65536)%Z ->
  to_outcomes RT
    (init_machine_state RT 0x100115c target_phdrs asp amb arnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
       (init_model (segments_reserved RT) abrk amb asp target_alloc_limit inp))
    (oobU tnN (outbufs targ1)).
Proof.
  intros Hmb Hrd Hncap.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tnN_le as HnnLe.
  pose proof abrk_lo_num as Hblo. pose proof abrk_hi_num as Hbhi.
  assert (E10i : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg))
    by (apply bv_eq; reflexivity).
  (* the image's list is concrete, so the run's reservations split by
     computation; the vDSO pair reserves nothing *)
  assert (HresRT : segments_reserved RT = segments_reserved target_segs).
  { replace (segments_reserved RT)
      with (segments_reserved target_segs
            ++ segments_reserved (vdso_segments (in_kernel inp) asp amb))
      by reflexivity.
    rewrite segments_reserved_vdso, app_nil_r. reflexivity. }
  rewrite HresRT.
  (* fd 1 is the stdout channel and has a reader in the run's initial
     model ([with_vdso] keeps the descriptor table and the reader flag) *)
  assert (Hfd0 : fd1chan (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
                   (init_model (segments_reserved target_segs) abrk amb asp
                      target_alloc_limit inp)))
    by exact (init_model_fd1chan (segments_reserved target_segs) abrk amb asp
                target_alloc_limit inp Hrd).
  destruct (target_to_brk1 Hncap)
    as (regsB & B2 & B8 & B10 & B11 & B13 & Hms).
  eapply tou_msteps; [exact (msteps_run target_segs inp asp amb _ _ Hms)|].
  apply (tou_brk_r RT _ _ (Z_to_bv 64 214)
           (T1 (init_reserved (segments_reserved target_segs) amb asp (in_kernel inp))
              target_alloc_limit (bv_unsigned asp - stack_max_size) tnN (outbufs targ1)));
    [reflexivity | vm_compute; reflexivity | | ].
  { (* per-resolution continuation at the first brk *)
    intros r Hok.
    unfold ms_gpr in Hok |- *; cbn [ms_regs] in Hok |- *.
    rewrite E10i, B10 in Hok |- *.
    change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved target_segs) amb asp
                                      (in_kernel inp))
                        [] [] abrk abrk target_alloc_limit amb asp)
              (Z_to_bv 64 0) r) in Hok.
    (* brk(0) is deterministic: it reports the quantified ASLR base. *)
    apply brk_r_ok_query_iff in Hok. cbn [vm_brk] in Hok.
    rewrite m_vmmaps_with_vdso, m_vmmaps_init_model. cbn [vm_brk].
    assert (Hurb : bv_unsigned r = bv_unsigned abrk)
      by (rewrite Hok; reflexivity).
    assert (Hrmod : (bv_unsigned r mod page_size = 0)%Z).
    { rewrite Hurb. exact Hbrk_mod. }
    assert (Hrnz : r <> Z_to_bv 64 0).
    { intro He. apply (f_equal bv_unsigned) in He.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in He. lia. }
    assert (Hnw : (bv_unsigned r + Z.of_nat tnn < 2^64)%Z) by lia.
    assert (Hurn : bv_unsigned (r + tnN) = (bv_unsigned r + Z.of_nat tnn)%Z)
      by (rewrite u_add_small; rewrite u_tnN; lia).
    assert (Hwant0 : r + tnN <> Z_to_bv 64 0).
    { intro He. apply (f_equal bv_unsigned) in He. rewrite Hurn in He.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in He. lia. }
    rewrite brk_zeros_query.
    rewrite (brk_unmaps_grow r abrk) by lia.
    rewrite adv_brk, apply_zeros_nil. wlits.
    rewrite brk_model_query by exact Hok.
    rewrite m_vmmaps_with_vdso, m_vmmaps_init_model.
    cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_limit vm_mmap_base vm_init_sp].
    (* base is nonzero and non-wrapping: straight to the second brk *)
    destruct (target_to_brk2 regsB r B2 B8 B11 B13 Hrnz Hnw)
      as (regs5 & F2 & F8 & F10 & F11 & F12 & F13 & F14 & Hms2).
    eapply tou_msteps; [exact (msteps_run target_segs inp asp amb _ _ Hms2)|].
    apply (tou_brk_r RT _ _ (Z_to_bv 64 214)
             (T2 (r + tnN) (outbufs targ1)));
      [reflexivity | vm_compute; reflexivity | | ].
        * (* per-resolution continuation at the second brk *)
          intros r2 Hok2.
          unfold ms_gpr in Hok2 |- *; cbn [ms_regs] in Hok2 |- *.
          rewrite E10i, F10 in Hok2 |- *.
          change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved target_segs) amb asp
                                            (in_kernel inp))
                              [] [] abrk r target_alloc_limit amb asp)
                    (r + tnN) r2) in Hok2.
          rewrite m_vmmaps_with_vmmaps. cbn [vm_brk].
          apply brk_r_ok_grow_iff in Hok2;
            [ | rewrite ?Hurn; lia | rewrite ?Hurn; lia | rewrite ?Hurn; lia ].
          destruct (decide (r2 = r + tnN)) as [-> | Hne].
          { (* success resolution *)
            destruct (Nat.eq_dec tnn 0) as [Hnn0 | Hnnpos].
            - (* n = 0: the second brk is a keep (no grant) *)
              assert (HnN0 : tnN = Z_to_bv 64 0).
              { unfold oob_read_bug_ns_target.tnN. rewrite Hnn0. reflexivity. }
              assert (Hz : brk_zeros (r + tnN) (r + tnN) r = []).
              { rewrite HnN0, word_add_0_r. apply brk_zeros_keep. }
              rewrite Hz.
              rewrite brk_unmaps_grow by lia.
              rewrite adv_brk, apply_zeros_nil. wlits.
              eapply tou_equiv;
                [ | intro o; apply (T2_succ_iff (r + tnN) (outbufs targ1)) ].
              apply tou_wexit_eq.
              + apply fd1chan_brk_model. apply fd1chan_with_vmmaps. exact Hfd0.
              + apply to_wallexit_run.
                exact (target_run_empty Hnn0 regs5 r Hnw F2 F11 F12 F14).
              + apply outbufs_modeled.
            - (* n > 0: a genuine grow *)
              destruct Hok2 as [_ Hgrow2].
              rewrite brk_grow_ok_aligned_grow in Hgrow2;
                [ cbn [vm_brk vm_reserved vm_maps] in Hgrow2;
                  rewrite app_nil_r in Hgrow2
                | exact Hwant0
                | cbn [vm_brk]; lia
                | cbn [vm_brk]; rewrite Hurn; lia
                | cbn [vm_brk]; exact Hrmod ].
              apply andb_true_iff in Hgrow2;
              destruct Hgrow2 as [Hgrow2 Hbud].
              apply andb_true_iff in Hgrow2;
              destruct Hgrow2 as [Hle Hfree].
              apply Z.leb_le in Hle.
              set (grant := Z_to_bv 64
                (page_round_up_Z (bv_unsigned (r + tnN)) - bv_unsigned r)).
              destruct (brk_aligned_grant_ok _ r tnN grant _ _
                          ltac:(rewrite u_tnN; exact Hurn) Hurn eq_refl
                          (alloc_top_page_lt _) Hle Hfree)
                as (HgrantU & Hgrant & Hphysceil & Hrawceil & Hrawfree & Hgrantfree).
              assert (Htotalgrant :
                (Z.of_nat (8 * ((tnn + 7) / 8)) <= bv_unsigned grant)%Z).
              { rewrite HgrantU, Hurn.
                rewrite Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add by lia.
                cbn [Z.of_nat].
                rewrite Z.mul_comm.
                apply round8_le_page_grant; [lia|lia|exact Hrmod]. }
              rewrite brk_zeros_aligned_grow;
                [ | exact Hwant0 | lia | rewrite Hurn; lia | exact Hrmod ].
              fold grant.
              rewrite brk_unmaps_grow by lia.
              rewrite adv_brk, apply_zeros_one. wlits.
              eapply tou_equiv;
                [ | intro o; apply (T2_succ_iff (r + tnN) (outbufs targ1)) ].
              apply tou_wexit_eq.
              + apply fd1chan_brk_model. apply fd1chan_with_vmmaps. exact Hfd0.
              + apply to_wallexit_run.
                apply (target_run_success regs5 r grant).
                * exact Hgrant.
                * exact Htotalgrant.
                * exact Hphysceil.
                * lia.
                * exact Hrawceil.
                * (* the image's part of the run's ledger *)
                  exact (region_free_init_reserved_img _ amb asp (in_kernel inp) r tnN
                           Hrawfree).
                * exact (region_free_init_reserved_img _ amb asp (in_kernel inp) r grant
                           Hgrantfree).
                * exact Hnnpos.
                * exact F2.
                * exact F8.
                * exact F11.
                * exact F12.
                * exact F14.
              + apply outbufs_modeled. }
          { (* failure resolution: r2 = r, exit 4 *)
            destruct Hok2 as [Hcase _].
            destruct Hcase as [Hc | Hc]; [exact (False_ind _ (Hne Hc)) |].
            subst r2.
            rewrite brk_zeros_keep.
            rewrite brk_unmaps_grow by lia.
            rewrite adv_brk, apply_zeros_nil. wlits.
            eapply tou_equiv;
              [ | intro o;
                  apply (T2_fail_iff (r + tnN) (outbufs targ1) r Hne) ].
            apply tou_wexit_eq.
            - apply fd1chan_brk_model. apply fd1chan_with_vmmaps. exact Hfd0.
            - (* bne a0, a4 taken -> exit 4 *)
              apply to_wallexit_run.
              chain_step;
                [ reflexivity
                | eapply step_bne_tk;
                  [ exact TF_1001208 | reflexivity | exact TD_1001208
                  | getr_resolve; regupd_resolve; rewrite F14;
                    apply c_eq_neq; intro He; apply Hne;
                    apply bv_eq; exact He ]
                | norm_pc ].
              apply target_exit.
              + regupd_resolve. exact F2.
              + regupd_resolve. exact F13.
              + u_norm; lia.
              + apply read_slot_ra_t.
              + apply read_slot_s0_t.
            - apply Forall_nil. }
        * (* set identity at the second node *)
          intro o.
          unfold ms_gpr; cbn [ms_regs].
          rewrite E10i, F10.
          change (T1 (init_reserved (segments_reserved target_segs) amb asp (in_kernel inp))
                     target_alloc_limit (bv_unsigned asp - stack_max_size) tnN
                     (outbufs targ1) r o <->
                  (exists r2,
                     brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved target_segs)
                                               amb asp (in_kernel inp))
                                 [] [] abrk r target_alloc_limit amb asp)
                       (r + tnN) r2
                     /\ T2 (r + tnN) (outbufs targ1) r2 o)).
          apply (T1_iff_T2 (init_reserved (segments_reserved target_segs) amb asp (in_kernel inp))
                   target_alloc_limit abrk amb asp tnN (outbufs targ1) r);
            [exact Hrnz | lia | rewrite u_tnN; lia]. }
  { (* set identity at the first node: the query resolves to abrk only *)
    intro o.
    unfold ms_gpr; cbn [ms_regs].
    rewrite E10i, B10.
    apply (oobU_iff_T1 (init_reserved (segments_reserved target_segs) amb asp (in_kernel inp))
             target_alloc_limit (bv_unsigned asp - stack_max_size) tnN (outbufs targ1) abrk).
    - intro r0.
      change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved target_segs) amb asp
                                        (in_kernel inp))
                          [] [] abrk abrk target_alloc_limit amb asp)
                (Z_to_bv 64 0) r0 <-> r0 = abrk).
      apply brk_r_ok_query_iff.
    - (* growable at the quantified base, over the run's ledger *)
      destruct (Nat.eq_dec tnn 0) as [Hn0|Hnpos].
      + split; [| split].
        * intro He. apply (f_equal bv_unsigned) in He.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in He. lia.
        * rewrite u_tnN. lia.
        * left. unfold oob_read_bug_ns_target.tnN. rewrite Hn0. reflexivity.
      + apply growable_ledger.
        * exact Hmb.
        * exact Hsp_lo.
        * exact Hbrk_mod.
        * lia.
        * exact Hbrk_lo.
        * rewrite u_tnN. lia.
        * rewrite u_tnN. unfold page_size. lia.
        * rewrite u_tnN. unfold page_size. change target_alloc_limit with 0x8000000000%Z. lia.
        * rewrite u_tnN. unfold page_size. lia. }
Qed.

End Ge2MainT.

End TargetProof.
