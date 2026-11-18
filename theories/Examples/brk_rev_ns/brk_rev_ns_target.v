(** * brk-rev-ns target binary: per-binary derivations.

    PROOF-SIDE FILE (not part of the trusted specification).

    Deliverables (Section [TargetProof], generic over the input and the
    ASLR placement):
    - [target_wexit_lt2]  : argc < 2             -> to_wexit [] 2
    - [target_wexit_cap]  : argc >= 2, n > 65536 -> to_wexit [] 3
    - [target_outcomes]   : argc >= 2, n <= 65536 ->
        to_outcomes (init) (init_model) (brkU (rev_buf argv[1])).

    Same conventions as brk_rev_ns_source.v, and the same treatment of
    the run: derivations over the image's own segments, carried to
    [Run.run_segments] by [RunSegmentsLift]; the launch conjunct
    [Run.entry_launch_ok_va] with [Run.valid_launch]; the run's brk ledger
    [State.init_reserved]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec WallSim AllocSim StepTac StoreOk Footprint SymExec SymTac SymBranch SymSide RunSegmentsLift.
From LinuxProcessSemantics.Examples.brk_rev_ns Require Import brk_rev_ns_code brk_rev_ns_defs.
From LinuxProcessSemantics.Examples.brk_rev_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.brk_rev_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them. *)
#[local] Instance brk_rev_ns_target_fx : FPState := fx0.

(** [sym_block]'s closers, [vm_compute]-free by construction: every goal
    below mentions the ASLR [asp] or the argv pointer, and [vm_compute]
    on an open [bv] term does not fail -- it allocates until the machine
    dies (see [StepTac.bveq]'s docstring). *)
Ltac sc0 := first [ reflexivity | (f_equal; lia) | (apply bv_eq; u_norm; lia) ].

(** The zero-extension a [lbu] leaves in a register, as a [Z] identity:
    this is what closes the [SCReadBase] obligation of every byte load. *)
Lemma zext_byte_u : forall b : byte,
  bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intro b. pose proof (u8_range b). apply u_Z2bv; lia. Qed.

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x1001158%N.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Reserved list and store legality                                   *)
(* ================================================================= *)

Lemma target_reserved_val :
  segments_reserved target_segs = [(0x1000000, 0x1000); (0x1001000, 0x1000)].
Proof.
  apply (proj1 (listNN_eqb_eq _ _)). vm_compute. reflexivity.
Qed.

(** Stores at/above the end of the second (read-only) segment are legal
    (ro segments: [0x1000000, 0x1000158) and [0x1001158, 0x1001288)). *)
Lemma target_avoids_stack : forall (a : word) (n : Z),
  (0x1002000 <= bv_unsigned a)%Z ->
  range_avoids_ro_segs target_segs (bv_unsigned a) n = true.
Proof.
  intros a n Ha.
  unfold target_segs, TargetMemImage_loaded_segments, range_avoids_ro_segs.
  cbn [forallb].
  change (Z.of_N (seg_base TargetMemImage_segment_000)
          + Z.of_N (seg_size TargetMemImage_segment_000))%Z with 0x1001000%Z.
  change (Z.of_N (seg_base TargetMemImage_segment_001)
          + Z.of_N (seg_size TargetMemImage_segment_001))%Z with 0x1002000%Z.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned a) 0x1001000)) by lia.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned a) 0x1002000)) by lia.
  rewrite !andb_false_r. reflexivity.
Qed.

(** A region free against the page-rounded reservations avoids both
    read-only segments everywhere inside it. *)
Lemma target_free_avoids : forall (b l : word),
  region_free (segments_reserved target_segs) b l = true ->
  (0 < bv_unsigned l)%Z ->
  forall (a : word) (k : Z),
  (bv_unsigned b <= bv_unsigned a)%Z ->
  (bv_unsigned a + k <= bv_unsigned b + bv_unsigned l)%Z ->
  range_avoids_ro_segs target_segs (bv_unsigned a) k = true.
Proof.
  intros b l Hfree Hl a k Hlo Hhi.
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
  assert (Hcase : (bv_unsigned b + bv_unsigned l <= 0x1000000
                   \/ 0x1002000 <= bv_unsigned b)%Z).
  { destruct H0 as [H0|H0]; destruct H1 as [H1|H1];
      apply Z.ltb_ge in H0; apply Z.ltb_ge in H1; lia. }
  unfold range_avoids_ro_segs, target_segs, TargetMemImage_loaded_segments.
  cbn [forallb].
  change (Z.of_N (seg_base TargetMemImage_segment_000)
          + Z.of_N (seg_size TargetMemImage_segment_000))%Z with 0x1001000%Z.
  change (Z.of_N (seg_base TargetMemImage_segment_001)
          + Z.of_N (seg_size TargetMemImage_segment_001))%Z with 0x1002000%Z.
  change (Z.of_N (seg_base TargetMemImage_segment_000)) with 0x1000000%Z.
  change (Z.of_N (seg_base TargetMemImage_segment_001)) with 0x1001000%Z.
  destruct Hcase as [Hc | Hc].
  - rewrite (proj2 (Z.ltb_ge 0x1000000 (bv_unsigned a + k))) by lia.
    rewrite (proj2 (Z.ltb_ge 0x1001000 (bv_unsigned a + k))) by lia.
    reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) 0x1001000)) by lia.
    rewrite (proj2 (Z.ltb_ge (bv_unsigned a) 0x1002000)) by lia.
    rewrite !andb_false_r. reflexivity.
Qed.

(* ================================================================= *)
(* The proof, generic over argv/envp and the stack pointer             *)
(* ================================================================= *)

Section TargetProof.

Variable inp : ProcInput.
Local Abbreviation av := (in_argv inp).
Local Abbreviation ev := (in_envp inp).
Hypothesis Hva : valid_argv av.
Hypothesis Hvl : valid_launch inp.

(** The initial stack pointer, the program break and the mmap base are
    QUANTIFIED (ASLR). *)
Variable asp abrk amb : word.

(** The target run's own draw, independent of the source's (the
    [ed_random] and [ed_top] halves of [Run.ExecEntry]'s [en_draw]; see
    the source file). *)
Variable arnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned asp)%Z.
Hypothesis Hsp_hi : (bv_unsigned asp <= sp_window_hi)%Z.

(** The launch conjunct of [Run.valid_entry_va]; see the source file. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry asp abrk amb arnd) inp.

(** The run's segment list, and its read-only backing as
    [PropExec.init_mkst] gives it. *)
Local Abbreviation RT := (run_segments target_segs inp asp amb).
Definition trom : word -> option byte := seg_rom (run_segments target_segs inp asp amb).

Lemma asp_lo_num : (0x7fff80000000 <= bv_unsigned asp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma asp_hi_num : (bv_unsigned asp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

(** The quantified initial program break ([Run.valid_brk] window, like the
    SP above), including the page alignment used by physical [brk] grants. *)
Hypothesis Hbrk_lo :
  (reserved_top (segments_reserved target_segs) <= bv_unsigned abrk)%Z.
Hypothesis Hbrk_hi :
  (bv_unsigned abrk
   <= reserved_top (segments_reserved target_segs) + brk_aslr_max)%Z.

Lemma rtop_tgt_val :
  reserved_top (segments_reserved target_segs) = 0x1002000%Z.
Proof. rewrite target_reserved_val. reflexivity. Qed.
Lemma abrk_lo_num : (0x1002000 <= bv_unsigned abrk)%Z.
Proof. rewrite <- rtop_tgt_val. exact Hbrk_lo. Qed.
Lemma abrk_hi_num : (bv_unsigned abrk <= 0x1002000 + 1073741824)%Z.
Proof. rewrite <- rtop_tgt_val, <- brk_aslr_max_val. exact Hbrk_hi. Qed.
Lemma abrk_lt64 : (bv_unsigned abrk < 2^64)%Z.
Proof.
  pose proof abrk_hi_num. change (2^64)%Z with 18446744073709551616%Z. lia.
Qed.

Definition targcN : word := len_word av.
Definition awmem : word -> option byte :=
  wrap_mem inp amb target_phdrs (Z_to_bv 64 (Z.of_N 0x1001158)) asp arnd.

Lemma u_targcN : bv_unsigned targcN = Z.of_nat (length av).
Proof.
  pose proof (valid_argv_len av Hva).
  unfold targcN, len_word. apply u_Z2bv; lia.
Qed.

Lemma target_bsb_nw : forall entry : word,
  (bv_unsigned asp
   + Z.of_nat (length (entry_stack_image inp amb target_phdrs entry asp arnd)) < 2^64)%Z.
Proof.
  intros entry.
  pose proof (bsb_bound Sv48 inp amb target_phdrs entry asp abrk arnd Hvl Hlau).
  pose proof asp_hi_num. lia.
Qed.

(** Memory after the entry prologue (sp = asp - 16): ra = 0, s0 = 0. *)
Definition amem1 : word -> option byte :=
  wbytes (wbytes awmem
    (Z_to_bv 64 (bv_unsigned asp - 8))  (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

(** Memory after main's prologue (sp = asp - 32):
    ra = 0x1001178 at asp-24, s0 = asp at asp-32. *)
Definition tfmem : word -> option byte :=
  wbytes (wbytes amem1
    (Z_to_bv 64 (bv_unsigned asp - 24)) (word_to_le_bytes 8 (0x1001178 : word)))
    (Z_to_bv 64 (bv_unsigned asp - 32)) (word_to_le_bytes 8 asp).

Lemma rdn_amem1_above : forall (a : word) n,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn target_segs amem1 a n = rdn target_segs awmem a n.
Proof.
  intros a n Ha Hn. pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. unfold amem1.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia)).
  reflexivity.
Qed.

Lemma rdn_tfmem_above : forall (a : word) n,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn target_segs tfmem a n = rdn target_segs awmem a n.
Proof.
  intros a n Ha Hn. pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. unfold tfmem.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia)).
  apply rdn_amem1_above; assumption.
Qed.

Lemma rdn_awmem_stack : forall (a : word) n,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn target_segs awmem a n
  = rdn target_segs (stack_to_mem asp (entry_stack_image inp amb target_phdrs
                                         (Z_to_bv 64 (Z.of_N 0x1001158)) asp arnd)) a n.
Proof. intros a n Ha Hn. apply rdn_wrap_stack_above; assumption. Qed.

Lemma read_argc_a1 :
  rdn target_segs amem1 asp 8%nat = Some (word_le8 targcN).
Proof.
  pose proof asp_hi_num.
  rewrite rdn_amem1_above by lia.
  rewrite rdn_awmem_stack by lia.
  apply read_argc. apply target_bsb_nw.
Qed.

(* ----------------------------------------------------------------- *)
(* argv[1] and its bytes                                              *)
(* ----------------------------------------------------------------- *)

Definition targ1 : list byte := nth 1 av [].
Definition tnn : nat := length targ1.
Definition tnN : word := nat_to_word tnn.
Definition ptrA : word := cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1.

(* ----------------------------------------------------------------- *)
(* Frame-slot read-back                                               *)
(* ----------------------------------------------------------------- *)

Lemma read_slot_ra_t :
  rdn target_segs tfmem (Z_to_bv 64 (bv_unsigned asp - 24)) 8%nat
  = Some (word_to_le_bytes 8 (0x1001178 : word)).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. unfold tfmem.
  rewrite rdn_wbytes_disjoint
    by (rewrite ?length_N_to_le_bytes; u_norm; lia).
  apply rdn_wbytes_hit8. u_norm; lia.
Qed.

Lemma read_slot_s0_t :
  rdn target_segs tfmem (Z_to_bv 64 (bv_unsigned asp - 32)) 8%nat
  = Some (word_to_le_bytes 8 asp).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. unfold tfmem.
  apply rdn_wbytes_hit8. u_norm; lia.
Qed.

(* ================================================================= *)
(* Epilogue-exit: 0x1001258 .. ret .. exit ecall                      *)
(* ================================================================= *)

Lemma target_exit : forall regs mem code,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 32) ->
  reg_get regs 14 = code -> (bv_unsigned code < 256)%Z ->
  rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 24)) 8%nat
    = Some (word_to_le_bytes 8 (0x1001178 : word)) ->
  rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 32)) 8%nat
    = Some (word_to_le_bytes 8 asp) ->
  to_wexit target_segs (mkst regs 0x1001258 mem trom) [] code.
Proof.
  intros regs mem code H2 H14 Hc Hra Hs0.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi. pose proof stack_max_size_val as Hsms.
  (* 0x1001258 .. 0x1001178: the two reloads, the frame pop, the [ret]
     and the exit-number [li], reflectively.  The reloaded [ra] is NAMED
     [ELit 0x1001178] in the read script, which is what lets the [ret]
     three instructions later resolve inside the same block. *)
  sym_block target_segs 8%nat (@nil bool) [ELit 0x1001178]
    [((2 : reg), EVar 32); ((14 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned asp - 32); code] [Z_to_bv 64 0; asp] R HR.
  { (* ld s0, 0(sp) *)
    exists (word_to_le_bytes 8 asp). split;
      [ replace (bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 32)) + 0)%Z
          with (bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 32)))
          by lia;
        rewrite <- (u_Z2bv (bv_unsigned asp - 32)) by lia;
        rewrite Z_to_bv_bv_unsigned; exact Hs0
      | exact (bytes_le_to_Z_8 _) ]. }
  { (* ld ra, 8(sp) *)
    exists (word_to_le_bytes 8 (0x1001178 : word)). split;
      [ replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned asp - 32)) + 8))
          with (Z_to_bv 64 (bv_unsigned asp - 24))
          by (u_norm; f_equal; lia);
        exact Hra
      | exact (bytes_le_to_Z_8 _) ]. }
  { exact H2. }
  { exact H14. }
  (* 0x100117c: ecall -- exit(code) *)
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ TF_100117c eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HR. vm_compute. reflexivity.
  - sym_regs HR. sym_close.
  - exact Hc.
Qed.

(* ================================================================= *)
(* Entry: prologue and the argc test                                  *)
(* ================================================================= *)

(** argc < 2: no output, exit 2. *)
Lemma target_wexit_lt2 : (length av < 2)%nat ->
  to_wexit RT (init_machine_state RT 0x1001158 target_phdrs asp amb arnd inp)
    [] (Z_to_bv 64 2).
Proof.
  intros Hlt2. apply to_wexit_run.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as HargcLe.
  rewrite init_mkst. norm_pc.
  match goal with
  | |- to_wexit _ (mkst ?R ?P _ _) ?B ?C =>
      change (to_wexit target_segs (mkst R P awmem trom) B C)
  end.
  (* 0x1001158 .. 0x100117c: the whole run, in ONE block.  The [auipc]
     makes the indirect call's target a literal, so the executor walks
     straight through it, through the argc test and the shared exit
     tail, and stops only at the [ecall]. *)
  sym_block target_segs 17%nat [false] (@nil expr)
    [((2 : reg), EVar 32)] [asp] [targcN] R HR.
  { (* bltu a2, a0 is NOT taken: argc <= 1 *)
    pose proof u_targcN. sym_br. }
  { (* ld a0, 0(s0) -- argc, out of the initial stack image *)
    replace (Z_to_bv 64 (bv_unsigned asp + 0)) with asp
      by (apply bv_eq; u_norm; lia).
    exists (word_le8 targcN). split;
      [ unfold awmem; rewrite rdn_wrap_stack_above by lia;
        apply read_argc; apply target_bsb_nw
      | apply bytes_le_n_to_le_8 ]. }
  { (* sd s0, 0(sp) *) unfold awmem; solve_store_ok. }
  { (* sd ra, 8(sp) *) unfold awmem; solve_store_ok. }
  (* 0x100117c: ecall -- exit(2) *)
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ TF_100117c eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HR. vm_compute. reflexivity.
  - sym_regs HR. sym_close.
  - u_norm; lia.
Qed.

(* ================================================================= *)
(* argc >= 2                                                          *)
(* ================================================================= *)

Section Ge2MainT.

Hypothesis Hge2 : (2 <= length av)%nat.

Lemma tnN_le : (Z.of_nat tnn <= 131071)%Z.
Proof.
  unfold tnn, targ1. apply valid_argv_str_len; [exact Hva | lia].
Qed.

(** The one buffer this program ever writes -- argv[1] reversed plus a
    newline -- is short enough for the model to transfer in one [write]:
    [valid_argv] caps a single argv string at 131071 bytes, and
    131071 + 1 = [rw_bytes_max]. *)
Lemma tbufs_modeled : bufs_modeled [rev_buf targ1].
Proof.
  pose proof tnN_le as Hn.
  constructor; [| constructor].
  unfold buf_modeled, rw_bytes_max. rewrite length_rev_buf.
  unfold tnn in Hn. lia.
Qed.

Lemma u_tnN : bv_unsigned tnN = Z.of_nat tnn.
Proof. pose proof tnN_le. unfold tnN. apply u_ntw. lia. Qed.

Lemma u_tnN1 : bv_unsigned (tnN + 1) = (Z.of_nat tnn + 1)%Z.
Proof.
  pose proof tnN_le.
  rewrite u_add_small; rewrite ?u_tnN;
    change (bv_unsigned (1 : word)) with 1%Z; lia.
Qed.

Lemma targ1_nz : ~ In (Z_to_bv 8 0) targ1.
Proof. unfold targ1. apply valid_argv_str_nz; [exact Hva | lia]. Qed.

Lemma ptrA_bounds :
  (bv_unsigned asp <= bv_unsigned ptrA)%Z /\
  (bv_unsigned ptrA + Z.of_nat tnn + 1 < 2^64)%Z.
Proof.
  unfold ptrA, tnn, targ1.
  exact (argv_ptr_bounds Sv48 inp amb asp abrk arnd 1 Hlau ltac:(lia)).
Qed.

Lemma ptrA_lo : (bv_unsigned asp <= bv_unsigned ptrA)%Z.
Proof. exact (proj1 ptrA_bounds). Qed.
Lemma ptrA_hi : (bv_unsigned ptrA + Z.of_nat tnn + 1 < 2^64)%Z.
Proof. exact (proj2 ptrA_bounds). Qed.

(** The whole NUL-terminated string at ptrA (through tfmem). *)
Lemma read_str_t :
  rdn target_segs tfmem ptrA (S tnn) = Some (targ1 ++ [Z_to_bv 8 0]).
Proof.
  destruct ptrA_bounds as [Hlo Hhi].
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  rewrite rdn_tfmem_above by lia.
  rewrite rdn_awmem_stack by lia.
  replace (S tnn) with (tnn + 1)%nat by lia.
  apply rdn_app.
  - unfold ptrA, targ1, tnn.
    exact (read_argv_str_k Sv48 target_segs inp amb target_phdrs _ asp abrk arnd 1
             Hlau ltac:(lia)).
  - pose proof (read_argv_byte_k Sv48 target_segs inp amb target_phdrs
                  (Z_to_bv 64 (Z.of_N 0x1001158)) asp abrk arnd 1 tnn Hlau
                  ltac:(lia) ltac:(unfold tnn, targ1; lia)) as Hbk.
    assert (Hb0 : nth tnn (nth 1 av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)
                  = Z_to_bv 8 0).
    { change (nth tnn (nth 1 av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))
        with (byte_at (nth 1 av []) tnn).
      apply byte_at_len. }
    rewrite Hb0 in Hbk. exact Hbk.
Qed.

(** From the entry point to the strlen loop head 0x1001270. *)
Lemma target_to_loop :
  exists regs1,
    reg_get regs1 1 = (0x10011ac : word) /\
    reg_get regs1 2 = Z_to_bv 64 (bv_unsigned asp - 32) /\
    reg_get regs1 8 = ptrA /\
    reg_get regs1 10 = ptrA /\
    reg_get regs1 11 = Z_to_bv 64 0 /\
    msteps target_segs
      (init_machine_state RT 0x1001158 target_phdrs asp amb arnd inp)
      (mkst regs1 0x1001270 tfmem trom).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as HargcLe.
  pose proof ptrA_lo as Hplo. pose proof ptrA_hi as Hphi.
  pose proof tnN_le as HnnLe.
  (* 0x1001158 .. 0x100126c: the crt entry, the argc test (taken), main's
     own frame, the argv[1] reload and the two indirect calls -- one
     block.  Both [jalr]s are preceded by the [auipc] that makes their
     target a literal, so nothing stops the executor before the strlen
     loop head.  [sym_block_ex] rather than [sym_block] because the
     statement's [exists regs1] has to be instantiated with the block's
     own exit register file. *)
  sym_block_ex target_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 asp)
          (Z_to_bv 64 0x1001158) awmem trom)
    18%nat [true] (@nil expr)
    [((2 : reg), EVar 32)] [asp] [targcN; ptrA] R HR Hms.
  { (* ld s0, 8(a1) -- the argv[1] pointer *)
    replace (Z_to_bv 64 (bv_unsigned asp + 16)) with (asp + nat_to_word (8 + 8 * 1))
      by (rewrite word_add_nat; f_equal; u_norm; lia).
    exists (word_le8 ptrA). split;
      [ unfold awmem; rewrite rdn_wrap_stack_above
          by (rewrite word_add_nat; u_norm; lia);
        unfold ptrA; apply read_argv_ptr_k; [lia | apply target_bsb_nw]
      | apply bytes_le_n_to_le_8 ]. }
  { (* sd s0, 0(sp) -- main's frame *) unfold awmem; solve_store_ok. }
  { (* sd ra, 8(sp) -- main's frame *) unfold awmem; solve_store_ok. }
  { (* bltu a2, a0 IS taken: argc >= 2 *) pose proof u_targcN. sym_br. }
  { (* ld a0, 0(s0) -- argc *)
    replace (Z_to_bv 64 (bv_unsigned asp + 0)) with asp
      by (apply bv_eq; u_norm; lia).
    exists (word_le8 targcN). split;
      [ unfold awmem; rewrite rdn_wrap_stack_above by lia;
        apply read_argc; apply target_bsb_nw
      | apply bytes_le_n_to_le_8 ]. }
  { (* sd s0, 0(sp) -- the crt frame *) unfold awmem; solve_store_ok. }
  { (* sd ra, 8(sp) -- the crt frame *) unfold awmem; solve_store_ok. }
  (* [sym_block_ex] leaves the exit memory as the log's raw denotation;
     put it into the [wbytes] spelling [tfmem] names.  (The chain-goal
     [sym_block] does this itself with [sym_mem_norm]; the factorable
     variant deliberately does not touch it.) *)
  match type of Hms with
  | msteps _ _ (mkst _ _ ?m _) =>
      replace m with tfmem in Hms;
        [ | unfold tfmem, amem1; sym_mem_norm;
            getr_resolve; regupd_resolve; reflexivity ]
  end.
  exists R. repeat split.
  6: { rewrite init_mkst.
       match goal with
       | |- msteps _ _ ?T =>
           change (msteps target_segs
                     (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 asp)
                           (Z_to_bv 64 0x1001158) awmem trom) T)
       end.
       sym_chain Hms. apply mst_refl. }
  all: sym_regs HR; sym_close.
Qed.

(* DELIBERATELY NOT REFLECTIVE.  The loop below is a four-instruction
   body with an existential conclusion, which is below the per-block
   break-even: converting it needs one body block plus one exit block,
   the index pinned as [ELit jz] (after [remember (Z.of_nat j)]) so that
   the opening [add a2,a0,a1] is still a base-plus-literal address, and
   a restatement of the register-agreement postcondition as per-register
   equalities -- more scaffolding than the four [stepi]s it replaces.
   The same applies to [target_copy] below and to [source_copy] and the
   musl SWAR [strlen_*] lemmas on the source side, which additionally
   step over a [wbytes _ _ (firstn i _)] store log that a block cannot
   express at all. *)
(** The strlen loop: from 0x1001270 with a1 = j, exit at 0x1001280 with
    a1 = n + 1. *)
Lemma target_strlen : forall mem,
  rdn target_segs mem ptrA (S tnn) = Some (targ1 ++ [Z_to_bv 8 0]) ->
  forall d j regs,
  (j + d = tnn)%nat ->
  reg_get regs 10 = ptrA ->
  reg_get regs 11 = nat_to_word j ->
  exists regs',
    (forall x : reg, x <> 11 -> x <> 12 -> reg_get regs' x = reg_get regs x) /\
    reg_get regs' 11 = tnN + 1 /\
    msteps target_segs (mkst regs 0x1001270 mem trom)
                       (mkst regs' 0x1001280 mem trom).
Proof.
  intros mem Hread.
  pose proof ptrA_lo as Hplo. pose proof ptrA_hi as Hphi.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tnN_le as HnnLe.
  pose proof targ1_nz as Hnz.
  induction d as [|d IH]; intros j regs Hjd Hr10 Hr11.
  - (* j = tnn: NUL sentinel *)
    assert (Hj : j = tnn) by lia.
    set (regs1 := regupd regs 12 (ptrA + nat_to_word j)).
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001270 mem trom)
                 = MachineOk (mkst regs1 0x1001274 mem trom)).
    { rewrite (step_add target_segs regs 0x1001270 mem trom _ 12 10 11
                 TF_1001270 eq_refl TD_1001270).
      reduce_bv_eqb_ifs.
      getr_resolve. rewrite Hr10, Hr11. wlits. reflexivity. }
    set (regs2 := regupd regs1 12 (Z_to_bv 64 0)).
    assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x1001274 mem trom)
                 = MachineOk (mkst regs2 0x1001278 mem trom)).
    { rewrite (step_lbu target_segs regs1 0x1001274 mem trom _ 12 12 _ (Z_to_bv 8 0)
                 TF_1001274 eq_refl TD_1001274).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite v_addi_0.
        pose proof (rdn_nth _ _ _ _ _ j Hread ltac:(lia)) as Hb.
        assert (Hb0 : nth j (targ1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = Z_to_bv 8 0).
        { change (nth j (targ1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))
            with (byte_at targ1 j).
          rewrite Hj. apply byte_at_len. }
        rewrite Hb0 in Hb. exact Hb. }
    set (regs3 := regupd regs2 11 (nat_to_word (S j))).
    assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x1001278 mem trom)
                 = MachineOk (mkst regs3 0x100127c mem trom)).
    { rewrite (step_addi target_segs regs2 0x1001278 mem trom _ 11 11 _
                 TF_1001278 eq_refl TD_1001278).
      reduce_bv_eqb_ifs.
      unfold regs3, regs2, regs1. getr_resolve. rewrite Hr11.
      rewrite v_addi_Sj by lia. wlits. reflexivity. }
    assert (E4 : RiscvSemantics.step target_segs (mkst regs3 0x100127c mem trom)
                 = MachineOk (mkst regs3 0x1001280 mem trom)).
    { rewrite (step_bne_ft target_segs regs3 0x100127c mem trom _ 12 0 _
                 TF_100127c eq_refl TD_100127c).
      - wlits. reflexivity.
      - unfold regs3, regs2. getr_resolve. exact c_eq_0_true. }
    exists regs3. split; [|split].
    + intros x H11 H12. unfold regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs3. rewrite regupd_same. rewrite Hj.
      unfold tnN. rewrite word1_nat, nat_to_word_merge.
      f_equal. lia.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      apply mst_refl.
  - (* j < tnn: nonzero byte *)
    assert (Hjlt : (j < tnn)%nat) by lia.
    set (b := byte_at targ1 j).
    assert (Hbnz : b <> Z_to_bv 8 0)
      by (apply byte_at_nz; [exact Hnz | exact Hjlt]).
    set (regs1 := regupd regs 12 (ptrA + nat_to_word j)).
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001270 mem trom)
                 = MachineOk (mkst regs1 0x1001274 mem trom)).
    { rewrite (step_add target_segs regs 0x1001270 mem trom _ 12 10 11
                 TF_1001270 eq_refl TD_1001270).
      reduce_bv_eqb_ifs.
      getr_resolve. rewrite Hr10, Hr11. wlits. reflexivity. }
    set (regs2 := regupd regs1 12 (Z_to_bv 64 (bv_unsigned b))).
    assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x1001274 mem trom)
                 = MachineOk (mkst regs2 0x1001278 mem trom)).
    { rewrite (step_lbu target_segs regs1 0x1001274 mem trom _ 12 12 _ b
                 TF_1001274 eq_refl TD_1001274).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite v_addi_0.
        pose proof (rdn_nth _ _ _ _ _ j Hread ltac:(lia)) as Hb'.
        replace (nth j (targ1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) with b in Hb'
          by reflexivity.
        exact Hb'. }
    set (regs3 := regupd regs2 11 (nat_to_word (S j))).
    assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x1001278 mem trom)
                 = MachineOk (mkst regs3 0x100127c mem trom)).
    { rewrite (step_addi target_segs regs2 0x1001278 mem trom _ 11 11 _
                 TF_1001278 eq_refl TD_1001278).
      reduce_bv_eqb_ifs.
      unfold regs3, regs2, regs1. getr_resolve. rewrite Hr11.
      rewrite v_addi_Sj by lia. wlits. reflexivity. }
    assert (E4 : RiscvSemantics.step target_segs (mkst regs3 0x100127c mem trom)
                 = MachineOk (mkst regs3 0x1001270 mem trom)).
    { rewrite (step_bne_tk target_segs regs3 0x100127c mem trom _ 12 0 _
                 TF_100127c eq_refl TD_100127c).
      - wlits. reflexivity.
      - unfold regs3, regs2. getr_resolve.
        apply c_eq_0_false. rewrite u_zext8. apply byte_nz_u. exact Hbnz. }
    assert (Hr10' : reg_get regs3 10 = ptrA).
    { unfold regs3, regs2, regs1. regupd_resolve. exact Hr10. }
    assert (Hr11' : reg_get regs3 11 = nat_to_word (S j)).
    { unfold regs3. apply regupd_same. }
    destruct (IH (S j) regs3 ltac:(lia) Hr10' Hr11') as [regs' [Hag [H11 Hms]]].
    exists regs'. split; [|split].
    + intros x H11' H12'. rewrite (Hag x H11' H12').
      unfold regs3, regs2, regs1. rewrite !regupd_other by assumption.
      reflexivity.
    + exact H11.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      exact Hms.
Qed.

(** After strlen: back in main at 0x10011ac with a0 = n. *)
Lemma target_to_captest :
  exists regs2,
    reg_get regs2 1 = (0x10011ac : word) /\
    reg_get regs2 2 = Z_to_bv 64 (bv_unsigned asp - 32) /\
    reg_get regs2 8 = ptrA /\
    reg_get regs2 10 = tnN /\
    msteps target_segs
      (init_machine_state RT 0x1001158 target_phdrs asp amb arnd inp)
      (mkst regs2 0x10011ac tfmem trom).
Proof.
  pose proof ptrA_hi as Hphi. pose proof tnN_le as HnnLe.
  destruct target_to_loop as (regs1 & H1 & H2 & H8 & H10 & H11 & Hms1).
  destruct (target_strlen tfmem read_str_t tnn O regs1
              ltac:(lia) H10 H11) as (regs2 & Hag & H11' & Hms2).
  eexists. repeat split.
  5: {
  eapply msteps_trans; [exact Hms1|].
  eapply msteps_trans; [exact Hms2|].
  (* addi a0, a1, -1 : a0 = n *)
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := tnN);
      [ exact TF_1001280 | reflexivity | exact TD_1001280 | reflexivity
      | getr_resolve; rewrite H11'; imm_norm; apply v_addi_pred ]
    | norm_pc ].
  (* ret -> 0x10011ac *)
  stepjr TF_1001284 TD_1001284 (0x10011ac : word) ltac:(getr_resolve; regupd_resolve; rewrite (Hag 1) by reg_neq_tac; exact H1).
  apply mst_refl. }
  - regupd_resolve. rewrite (Hag 1) by reg_neq_tac. exact H1.
  - regupd_resolve. rewrite (Hag 2) by reg_neq_tac. exact H2.
  - regupd_resolve. rewrite (Hag 8) by reg_neq_tac. exact H8.
  - regupd_resolve. reflexivity.
Qed.

(** n > 65536: no output, exit 3. *)
Lemma target_wexit_cap : (65536 < Z.of_nat tnn)%Z ->
  to_wexit RT (init_machine_state RT 0x1001158 target_phdrs asp amb arnd inp)
    [] (Z_to_bv 64 3).
Proof.
  intros Hcap. apply to_wexit_run.
  pose proof tnN_le as HnnLe.
  destruct target_to_captest as (regs2 & H1 & H2 & H8 & H10 & Hms).
  eapply msteps_to_wexit; [exact Hms|].
  (* 0x10011ac .. 0x10011b8: the cap test (fall-through) and the jump to
     the shared exit tail; the fuel is EXACT, one more step would walk
     into the epilogue reloads. *)
  sym_block target_segs 4%nat [false] (@nil expr)
    [((2 : reg), EVar 32); ((10 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned asp - 32); tnN] (@nil word) R HR.
  { (* 0x10011b0: bgeu a1, a0 falls through -- 65536 < n *)
    pose proof u_tnN. sym_br. }
  { exact H2. }
  { exact H10. }
  apply target_exit.
  - sym_regs HR. sym_close.
  - sym_regs HR. sym_close.
  - u_norm; lia.
  - apply read_slot_ra_t.
  - apply read_slot_s0_t.
Qed.

(* ================================================================= *)
(* The reverse-copy loop: 0x1001208 .. 0x100121c                      *)
(* ================================================================= *)

(* [store_grant_ok]: the loop's [sb]s are machine stores into the brk
   grant, and [mem0] is abstract here, so the writability of the grant
   has to come in as a hypothesis. *)
Lemma target_copy : forall (r : word) mem0,
  store_grant_ok target_segs mem0 r (tnN + 1) ->
  rdn target_segs mem0 ptrA (S tnn) = Some (targ1 ++ [Z_to_bv 8 0]) ->
  (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + Z.of_nat tnn + 1 <= bv_unsigned asp - stack_max_size)%Z ->
  forall d regs,
  (1 <= d)%nat -> (d <= tnn)%nat ->
  reg_get regs 10 = Z_to_bv 64 (- Z.of_nat d) ->
  reg_get regs 14 = Z_to_bv 64 (bv_unsigned ptrA + Z.of_nat d - 1) ->
  reg_get regs 15 = r + nat_to_word (tnn - d) ->
  exists regs',
    (forall x : reg, x <> 16 -> x <> 10 -> x <> 14 -> x <> 15 ->
       reg_get regs' x = reg_get regs x) /\
    reg_get regs' 15 = r + tnN /\
    msteps target_segs
      (mkst regs 0x1001208 (wbytes mem0 r (firstn (tnn - d) (rev targ1))) trom)
      (mkst regs' 0x1001220 (wbytes mem0 r (rev targ1)) trom).
Proof.
  intros r mem0 Hgok Hstr Hr0 Hceil.
  pose proof ptrA_lo as Hplo. pose proof ptrA_hi as Hphi.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tnN_le as HnnLe.
  pose proof (u64_range r) as Hur.
  assert (HnnA : Z.of_nat (length targ1) = Z.of_nat tnn) by reflexivity.
  induction d as [|d IH]; intros regs Hd1 Hd Hr10 Hr14 Hr15; [lia|].
  set (memI := wbytes mem0 r (firstn (tnn - S d) (rev targ1))).
  set (b := byte_at targ1 d).
  assert (HlenF : length (firstn (tnn - S d) (rev targ1)) = (tnn - S d)%nat)
    by (apply firstn_length_le; rewrite length_rev; lia).
  assert (Hud : bv_unsigned (ptrA + nat_to_word d)
                = (bv_unsigned ptrA + Z.of_nat d)%Z).
  { rewrite u_add_small; rewrite u_ntw by lia; lia. }
  assert (HuW : bv_unsigned (r + nat_to_word (tnn - S d))
                = (bv_unsigned r + Z.of_nat (tnn - S d))%Z).
  { rewrite u_add_small; rewrite u_ntw by lia; lia. }
  (* lbu a6, 0(a4) : byte targ1[d] *)
  set (regs1 := regupd regs 16 (Z_to_bv 64 (bv_unsigned b))).
  assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001208 memI trom)
               = MachineOk (mkst regs1 0x100120c memI trom)).
  { rewrite (step_lbu target_segs regs 0x1001208 memI trom _ 16 14 _ b
               TF_1001208 eq_refl TD_1001208).
    - reduce_bv_eqb_ifs. wlits. reflexivity.
    - getr_resolve. rewrite Hr14. rewrite v_addi_0.
      replace (Z_to_bv 64 (bv_unsigned ptrA + Z.of_nat (S d) - 1))
        with (ptrA + nat_to_word d)
        by (rewrite word_add_nat; f_equal; lia).
      unfold memI.
      rewrite rdn_wbytes_disjoint by (rewrite ?HlenF, ?Hud; lia).
      pose proof (rdn_nth _ _ _ _ _ d Hstr ltac:(lia)) as Hb'.
      replace (nth d (targ1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) with b in Hb'
        by reflexivity.
      exact Hb'. }
  (* addi a0, a0, 1 *)
  set (regs2 := regupd regs1 10 (Z_to_bv 64 (- Z.of_nat d))).
  assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x100120c memI trom)
               = MachineOk (mkst regs2 0x1001210 memI trom)).
  { rewrite (step_addi_at target_segs regs1 0x100120c memI trom _ 10 10 _
               (Z_to_bv 64 (- Z.of_nat d)) TF_100120c eq_refl TD_100120c eq_refl).
    - wlits. reflexivity.
    - unfold regs1. getr_resolve. rewrite Hr10.
      apply v_addi_neg_S. }
  (* addi a4, a4, -1 *)
  set (regs3 := regupd regs2 14 (Z_to_bv 64 (bv_unsigned ptrA + Z.of_nat d - 1))).
  assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x1001210 memI trom)
               = MachineOk (mkst regs3 0x1001214 memI trom)).
  { rewrite (step_addi_at target_segs regs2 0x1001210 memI trom _ 14 14 _
               (Z_to_bv 64 (bv_unsigned ptrA + Z.of_nat d - 1))
               TF_1001210 eq_refl TD_1001210 eq_refl).
    - wlits. reflexivity.
    - unfold regs2, regs1. getr_resolve. rewrite Hr14. imm_norm.
      rewrite v_addi_m1 by (u_norm; lia).
      u_norm. f_equal. lia. }
  (* sb a6, 0(a5) : write byte at r + (tnn - S d) *)
  set (memI' := wbytes mem0 r (firstn (tnn - d) (rev targ1))).
  assert (E4 : RiscvSemantics.step target_segs (mkst regs3 0x1001214 memI trom)
               = MachineOk (mkst regs3 0x1001218 memI' trom)).
  { rewrite (step_sb_at target_segs regs3 0x1001214 memI trom _ 15 16 _
               (r + nat_to_word (tnn - S d)) b TF_1001214 eq_refl TD_1001214).
    - wlits.
      replace (wbytes memI (r + nat_to_word (tnn - S d)) [b]) with memI';
        [reflexivity|].
      unfold memI', memI.
      replace (tnn - d)%nat with (S (tnn - S d)) by lia.
      rewrite (firstn_rev_snoc targ1 (tnn - S d)) by (unfold tnn in *; lia).
      rewrite wbytes_app.
      rewrite HlenF.
      replace (nth (length targ1 - S (tnn - S d)) targ1 (Z_to_bv 8 0)) with b.
      + reflexivity.
      + unfold b. replace (length targ1 - S (tnn - S d))%nat with d
          by (unfold tnn in *; lia).
        apply nth_lt_byte_at. unfold tnn in *; lia.
    - unfold regs3, regs2, regs1. getr_resolve. rewrite Hr15.
      apply v_addi_0.
    - unfold regs3, regs2, regs1. getr_resolve.
      apply zext8_byte.
    - store_ok_peel; apply Hgok;
        rewrite ?u_tnN1, ?HuW; u_norm; lia. }
  (* addi a5, a5, 1 *)
  set (regs4 := regupd regs3 15 (r + nat_to_word (tnn - d))).
  assert (E5 : RiscvSemantics.step target_segs (mkst regs3 0x1001218 memI' trom)
               = MachineOk (mkst regs4 0x100121c memI' trom)).
  { rewrite (step_addi_at target_segs regs3 0x1001218 memI' trom _ 15 15 _
               (r + nat_to_word (tnn - d)) TF_1001218 eq_refl TD_1001218 eq_refl).
    - wlits. reflexivity.
    - unfold regs3, regs2, regs1. getr_resolve. rewrite Hr15.
      rewrite word_add_nat_1.
      do 2 f_equal. lia. }
  destruct (Nat.eqb_spec d 0) as [-> | Hdnz].
  - (* last iteration: bne falls through to 0x1001220 *)
    assert (E6 : RiscvSemantics.step target_segs (mkst regs4 0x100121c memI' trom)
                 = MachineOk (mkst regs4 0x1001220 memI' trom)).
    { rewrite (step_bne_ft target_segs regs4 0x100121c memI' trom _ 10 0 _
                 TF_100121c eq_refl TD_100121c).
      - wlits. reflexivity.
      - unfold regs4, regs3, regs2. getr_resolve. exact c_eq_0_true. }
    exists regs4. split; [|split].
    + intros x H16 H10 H14 H15. unfold regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs4. rewrite regupd_same.
      rewrite Nat.sub_0_r. reflexivity.
    + replace (wbytes mem0 r (rev targ1)) with memI'.
      2:{ unfold memI'. rewrite Nat.sub_0_r.
          replace (firstn tnn (rev targ1)) with (rev targ1)
            by (symmetry; apply firstn_all_rev).
          reflexivity. }
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      apply mst_refl.
  - (* more iterations: bne taken back to 0x1001208 *)
    assert (E6 : RiscvSemantics.step target_segs (mkst regs4 0x100121c memI' trom)
                 = MachineOk (mkst regs4 0x1001208 memI' trom)).
    { rewrite (step_bne_tk target_segs regs4 0x100121c memI' trom _ 10 0 _
                 TF_100121c eq_refl TD_100121c).
      - wlits. reflexivity.
      - unfold regs4, regs3, regs2. getr_resolve.
        apply c_eq_0_false. rewrite u_neg_small by lia. lia. }
    assert (Hr10' : reg_get regs4 10 = Z_to_bv 64 (- Z.of_nat d)).
    { unfold regs4, regs3, regs2. regupd_resolve. reflexivity. }
    assert (Hr14' : reg_get regs4 14
                    = Z_to_bv 64 (bv_unsigned ptrA + Z.of_nat d - 1)).
    { unfold regs4, regs3. regupd_resolve. reflexivity. }
    assert (Hr15' : reg_get regs4 15 = r + nat_to_word (tnn - d)).
    { unfold regs4. apply regupd_same. }
    destruct (IH regs4 ltac:(lia) ltac:(lia) Hr10' Hr14' Hr15')
      as (regs' & Hag & H15 & Hms).
    exists regs'. split; [|split].
    + intros x H16 H10 H14 H15'. rewrite (Hag x H16 H10 H14 H15').
      unfold regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + exact H15.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      exact Hms.
Qed.

(* ================================================================= *)
(* Output tail: 0x1001220 (newline, write, exit 0)                    *)
(* ================================================================= *)

(** The put-style retry loop after a (possibly short) write delivery:
    from the post-write state at 0x100123c — a0 = the delivered length,
    a1 = the offered pointer, a2 = the offered count — the loop runs
    [blez a0] (fall-through, the error arm is dead), bumps the pointer,
    decrements the count, and either falls into the exit-0 tail
    ([bnez a2] not taken) or reissues the write on the remainder.  The
    loop is register-only, so the exit tail's two frame reloads see the
    unchanged memory. *)
Lemma tgt_put_wall : forall fuel (rest : list byte) (p : word) n regs mem,
  (length rest <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length rest)%nat ->
  (Z.of_nat (length rest) <= 131073)%Z ->
  (0 < bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) < 2^64)%Z ->
  reg_get regs 10 = len_word (firstn n rest) ->
  reg_get regs 11 = p ->
  reg_get regs 12 = len_word rest ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 32) ->
  bv_unsigned (reg_get regs 17) = 64%Z ->
  rdn target_segs mem p (length rest) = Some rest ->
  rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 24)) 8%nat
    = Some (word_to_le_bytes 8 (0x1001178 : word)) ->
  rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 32)) 8%nat
    = Some (word_to_le_bytes 8 asp) ->
  (* the caller's buffer passes [access_ok], so every remainder does *)
  (bv_unsigned p + Z.of_nat (length rest) <= TASK_SIZE)%Z ->
  to_wall_tail target_segs (Z_to_bv 64 1)
    (mkst regs (0x100123c : word) mem trom)
    (skipn n rest)
    (to_wallexit target_segs (Z_to_bv 64 1) [] (Z_to_bv 64 0)).
Proof.
  induction fuel as [|fuel IH];
    intros rest p n regs mem Hfuel Hn1 Hn2 Hlen Hplo Hphi
           H10 H11 H12 H2 H17 Hread Hra Hs0 Hpa.
  { lia. }
  (* blez a0 falls through (the delivery is nonempty) *)
  step_intro;
    [ reflexivity
    | eapply step_bge_ft;
      [ exact TF_100123c | reflexivity | exact TD_100123c
      | getr_resolve; rewrite H10; apply c_lts_0_pos;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* add a1,a1,a0: the pointer bump *)
  stepiv TF_1001240 TD_1001240 (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
    ltac:(getr_resolve; rewrite H11, H10; apply v_add_len_firstn_Z; lia).
  (* sub a2,a2,a0: the count decrement *)
  stepiv TF_1001244 TD_1001244 (len_word (skipn n rest))
    ltac:(getr_resolve; rewrite H12, H10; apply v_sub_len_firstn; lia).
  destruct (Nat.eq_dec n (length rest)) as [-> | Hne].
  - (* full delivery: bnez not taken, fall into the exit-0 tail *)
    rewrite skipn_all.
    step_intro;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact TF_1001248 | reflexivity | exact TD_1001248
        | getr_resolve; apply c_eq_0_of_u; reflexivity ]
      | norm_pc ].
    (* li a4,0 ; j 0x1001258 *)
    stepiv TF_100124c TD_100124c (Z_to_bv 64 0) ltac:(getr_resolve; bveq).
    stepj TF_1001250 TD_1001250.
    apply twt_done. cbn [to_wallexit].
    apply target_exit.
    + regupd_resolve; exact H2.
    + regupd_resolve; reflexivity.
    + vm_compute; reflexivity.
    + exact Hra.
    + exact Hs0.
  - (* short delivery: bnez taken, reissue on the remainder *)
    step_intro;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact TF_1001248 | reflexivity | exact TD_1001248
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* li a0,1 *)
    stepiv TF_1001234 TD_1001234 (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* ecall: the reissued write *)
    eapply twt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_1001238 eq_refl) |].
    apply twt_more; [rewrite length_skipn; lia|].
    apply (twl_write_rec target_segs (Z_to_bv 64 1)).
    + getr_resolve; exact H17.
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
      rewrite (ms_read_bytes_rdn (run_segments target_segs inp asp amb)) by reflexivity.
      unfold run_segments. apply rdn_lift.
      cbn [ms_mem].
      replace (word_to_nat (len_word (skipn n rest)))
        with (length (skipn n rest))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      pose proof (rdn_skipn target_segs mem (length rest) p rest n Hread Hn2)
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
      apply access_okb_intro. unfold TASK_SIZE in Hpa |- *.
      rewrite u_len_word by (rewrite length_skipn; lia).
      rewrite u_Z2bv by lia. rewrite length_skipn. lia.
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
      * regupd_resolve; exact H2.
      * regupd_resolve; exact H17.
      * pose proof (rdn_skipn target_segs mem (length rest) p rest n Hread Hn2)
          as Hsk.
        rewrite word_add_nat_Z in Hsk by lia.
        rewrite length_skipn. exact Hsk.
      * exact Hra.
      * exact Hs0.
      * rewrite u_Z2bv by lia. rewrite length_skipn. lia.
Qed.

Lemma target_out : forall regs (r grant : word),
  (bv_unsigned (tnN + 1) <= bv_unsigned grant)%Z ->
  (bv_unsigned r + bv_unsigned grant <= bv_unsigned asp - stack_max_size)%Z ->
  (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + Z.of_nat tnn + 1 <= bv_unsigned asp - stack_max_size)%Z ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 32) ->
  reg_get regs 11 = r ->
  reg_get regs 12 = tnN + 1 ->
  reg_get regs 13 = tnN ->
  to_wallexit target_segs (Z_to_bv 64 1) [rev_buf targ1] (Z_to_bv 64 0)
    (mkst regs 0x1001220 (wbytes (zmem tfmem r grant) r (rev targ1)) trom).
Proof.
  intros regs r grant Hgrant Hgrantceil Hr0 Hceil H2 H11 H12 H13.
  split; [rewrite length_rev_buf; lia|].
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tnN_le as HnnLe.
  pose proof (u64_range r) as Hur.
  assert (HnnA : Z.of_nat (length targ1) = Z.of_nat tnn) by reflexivity.
  assert (Hun1 : bv_unsigned (tnN + 1) = (Z.of_nat tnn + 1)%Z) by (exact u_tnN1).
  assert (Hurn : bv_unsigned (r + tnN) = (bv_unsigned r + Z.of_nat tnn)%Z).
  { rewrite u_add_small; rewrite u_tnN; lia. }
  set (mem0 := zmem tfmem r grant).
  set (memA := wbytes mem0 r (rev targ1)).
  (* 0x1001220 .. 0x1001224: the end pointer and the newline literal.
     The executor stops at the [sb]: its address [a1 + a3] is a sum of
     two symbolic registers, which [to_saddr] does not recognise. *)
  sym_block target_segs 2%nat (@nil bool) (@nil expr)
    [((11 : reg), EVar 32); ((13 : reg), EVar 33)] [r; tnN] (@nil word) R1 HR1.
  { exact H11. }
  { exact H13. }
  (* 0x1001228: sb a0, 0(a3) -- the newline at r + n *)
  set (memB := wbytes mem0 r (rev_buf targ1)).
  eapply twt_step;
    [ reflexivity
    | eapply step_sb_at with (a := r + tnN) (b := Z_to_bv 8 10);
      [ exact TF_1001228 | reflexivity | exact TD_1001228
      | sym_regs HR1; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | sym_regs HR1; sym_close
      | store_ok_peel; apply store_ok_zmem;
        rewrite ?u_tnN1, ?Hurn; u_norm; lia ]
    | step_simpl ].
  match goal with
  |- to_wall_tail _ _ (mkst ?R _ ?M _) _ _ =>
      replace M with memB
  end.
  2:{ unfold memB, memA, rev_buf.
      rewrite wbytes_app. rewrite length_rev.
      reflexivity. }
  (* 0x100122c .. 0x1001234: the write's syscall number, the empty-buffer
     test (fall-through) and the fd -- one block, stopping at the ecall. *)
  sym_block target_segs 4%nat [false] (@nil expr)
    [((2 : reg), EVar 32); ((11 : reg), EVar 33); ((12 : reg), EVar 34)]
    [Z_to_bv 64 (bv_unsigned asp - 32); r; tnN + 1] (@nil word) R2 HR2.
  { (* 0x1001230: beq a2, x0 falls through -- n + 1 <> 0 *) sym_br. }
  (* [a1] was pinned in the previous block, so [sym_pin_auto] discharges
     its obligation itself. *)
  { sym_regs HR1; exact H2. }
  { sym_regs HR1; exact H12. }
  (* 0x1001238: ecall -- write(1, r, n+1) *)
  eapply twt_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ TF_1001238 eq_refl) | ].
  apply twt_more; [rewrite length_rev_buf; lia|].
  apply (twl_write_rec target_segs (Z_to_bv 64 1)).
  - sym_regs HR2. vm_compute. reflexivity.
  - sym_regs HR2. sym_close.
  - rewrite (ms_read_bytes_rdn (run_segments target_segs inp asp amb)) by reflexivity.
    unfold run_segments. apply rdn_lift.
    cbn [ms_mem ms_regs].
    sym_regs HR2.
    replace (word_to_nat (tnN + 1)) with (S tnn)
      by (unfold word_to_nat; rewrite u_tnN1; lia).
    unfold memB.
    replace (S tnn) with (length (rev_buf targ1))
      by (rewrite length_rev_buf; reflexivity).
    apply rdn_wbytes_hit.
    rewrite length_rev_buf. lia.
  - (* the buffer's range passes [access_ok]: the brk grant, below the
       stack *)
    replace (reg_get R2 11) with r by (sym_regs HR2; sym_close).
    replace (reg_get R2 12) with (tnN + 1) by (sym_regs HR2; sym_close).
    apply access_okb_intro. rewrite u_tnN1. unfold TASK_SIZE. lia.
  - rewrite length_rev_buf; lia.
  - (* the write-all retry loop, per delivered length *)
    intros n Hn1 Hn2.
    norm_pc.
    apply (tgt_put_wall (length (rev_buf targ1)) (rev_buf targ1) r n).
    + lia.
    + exact Hn1.
    + exact Hn2.
    + rewrite length_rev_buf; lia.
    + lia.
    + rewrite length_rev_buf; lia.
    + regupd_resolve; reflexivity.
    + regupd_resolve; sym_regs HR2; sym_close.
    + regupd_resolve; sym_regs HR2.
      match goal with |- ?x = _ => transitivity (tnN + 1) end;
        [ sym_close
        | apply bv_eq; rewrite u_tnN1, u_len_word
            by (rewrite length_rev_buf; lia);
          rewrite length_rev_buf; lia ].
    + regupd_resolve; sym_regs HR2;
      first [ exact H2 | sym_close | reflexivity ].
    + regupd_resolve; sym_regs HR2. reflexivity.
    + unfold memB.
      apply rdn_wbytes_hit.
      rewrite length_rev_buf. lia.
    + unfold memB, mem0.
      rewrite rdn_wbytes_disjoint
        by (rewrite ?length_rev_buf; u_norm; lia).
      rewrite rdn_zmem_out by (rewrite ?u_tnN1; u_norm; lia).
      apply read_slot_ra_t.
    + unfold memB, mem0.
      rewrite rdn_wbytes_disjoint
        by (rewrite ?length_rev_buf; u_norm; lia).
      rewrite rdn_zmem_out by (rewrite ?u_tnN1; u_norm; lia).
      apply read_slot_s0_t.
    + rewrite length_rev_buf. unfold TASK_SIZE. lia.
Qed.

(* ================================================================= *)
(* Success tail from the return of the second brk                     *)
(* ================================================================= *)

Lemma target_success : forall regs (r grant : word),
  (bv_unsigned (tnN + 1) <= bv_unsigned grant)%Z ->
  (bv_unsigned r + bv_unsigned grant <= bv_unsigned asp - stack_max_size)%Z ->
  (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + Z.of_nat tnn + 1 <= bv_unsigned asp - stack_max_size)%Z ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 32) ->
  reg_get regs 8 = ptrA ->
  reg_get regs 10 = r + (tnN + 1) ->
  reg_get regs 11 = r ->
  reg_get regs 12 = tnN + 1 ->
  reg_get regs 13 = tnN ->
  reg_get regs 15 = r + (tnN + 1) ->
  to_wallexit target_segs (Z_to_bv 64 1) [rev_buf targ1] (Z_to_bv 64 0)
    (mkst regs 0x10011f0 (zmem tfmem r grant) trom).
Proof.
  intros regs r grant Hgrant Hgrantceil Hr0 Hceil
    H2 H8 H10 H11 H12 H13 H15.
  split; [rewrite length_rev_buf; lia|].
  pose proof ptrA_lo as Hplo. pose proof ptrA_hi as Hphi.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tnN_le as HnnLe.
  pose proof (u64_range r) as Hur.
  assert (HnnA : Z.of_nat (length targ1) = Z.of_nat tnn) by reflexivity.
  assert (Hupn : bv_unsigned (ptrA + tnN) = (bv_unsigned ptrA + Z.of_nat tnn)%Z).
  { rewrite u_add_small; rewrite u_tnN; lia. }
  set (mem0 := zmem tfmem r grant).
  assert (Hstr0 : rdn target_segs mem0 ptrA (S tnn) = Some (targ1 ++ [Z_to_bv 8 0])).
  { unfold mem0. rewrite rdn_zmem_out by (rewrite ?u_tnN1; lia).
    apply read_str_t. }
  destruct (Nat.eqb_spec tnn 0) as [Hz | Hnz].
  - (* empty string: skip the copy loop *)
    assert (Htarg : targ1 = []).
    { exact (proj1 (length_zero_iff_nil targ1) Hz). }
    assert (HtnN0 : tnN = Z_to_bv 64 0)
      by (unfold tnN; rewrite Hz; reflexivity).
    (* 0x10011f0 .. 0x1001204: the got/want test (fall-through -- a0 and
       a5 are pinned to the SAME slot, so it is a syntactic identity),
       the negated length, the source cursor, and the empty-buffer test
       (taken).  One block. *)
    sym_block target_segs 6%nat [false; true] (@nil expr)
      [((2 : reg), EVar 32); ((8 : reg), EVar 33); ((10 : reg), EVar 34);
       ((11 : reg), EVar 35); ((12 : reg), EVar 36); ((13 : reg), EVar 37);
       ((15 : reg), EVar 34)]
      [Z_to_bv 64 (bv_unsigned asp - 32); ptrA; r + (tnN + 1); r;
       tnN + 1; tnN] (@nil word) R HR.
    { (* 0x1001204: beq a0, x0 IS taken -- the string is empty *)
      rewrite HtnN0. vm_compute. reflexivity. }
    { (* 0x10011f0: bne a0, a5 falls through -- got = want *) sym_br. }
    { exact H2. }
    { exact H8. }
    { exact H10. }
    { exact H11. }
    { exact H12. }
    { exact H13. }
    { exact H15. }
    match goal with
    |- to_wall_tail _ _ (mkst ?RR _ ?M _) _ _ =>
        replace M with (wbytes mem0 r (rev targ1))
          by (rewrite Htarg; reflexivity)
    end.
    refine (proj2 (target_out _ r grant Hgrant
                     Hgrantceil
                     Hr0 Hceil
                     _ _ _ _));
      sym_regs HR; sym_close.
  - (* nonempty string: run the copy loop *)
    (* the same six instructions, with the empty-buffer test falling
       through into the copy loop instead *)
    sym_block target_segs 6%nat [false; false] (@nil expr)
      [((2 : reg), EVar 32); ((8 : reg), EVar 33); ((10 : reg), EVar 34);
       ((11 : reg), EVar 35); ((12 : reg), EVar 36); ((13 : reg), EVar 37);
       ((15 : reg), EVar 34)]
      [Z_to_bv 64 (bv_unsigned asp - 32); ptrA; r + (tnN + 1); r;
       tnN + 1; tnN] (@nil word) R HR.
    { (* 0x1001204: beq a0, x0 falls through -- a0 = -n <> 0 *)
      apply c_eq_0_false. rewrite v_sub_0_neg, u_tnN.
      rewrite u_neg_small by lia. lia. }
    { (* 0x10011f0: bne a0, a5 falls through -- got = want *) sym_br. }
    { exact H2. }
    { exact H8. }
    { exact H10. }
    { exact H11. }
    { exact H12. }
    { exact H13. }
    { exact H15. }
    destruct (target_copy r mem0
                ltac:(unfold mem0; apply store_grant_zmem_prefix;
                      [ exact Hgrant | lia ])
                Hstr0 Hr0 Hceil tnn R
                ltac:(lia) (Nat.le_refl tnn)
                ltac:(sym_regs HR; rewrite v_sub_0_neg, u_tnN; reflexivity)
                ltac:(sym_regs HR; rewrite alu_add; unfold v_add;
                      rewrite u_Z2bv by (rewrite u_tnN; lia);
                      rewrite u_tnN; f_equal; lia)
                ltac:(rewrite Nat.sub_diag, word_add_0; sym_regs HR; sym_close))
      as (regsC & HagC & H15C & HmsC).
    replace (wbytes mem0 r (firstn (tnn - tnn) (rev targ1))) with mem0 in HmsC.
    2:{ rewrite Nat.sub_diag. cbn [firstn wbytes]. reflexivity. }
    eapply msteps_to_wall_tail; [exact HmsC|].
    refine (proj2 (target_out _ r grant Hgrant
                     Hgrantceil
                     Hr0 Hceil
                     _ _ _ _)).
    + rewrite (HagC 2) by reg_neq_tac. sym_regs HR. sym_close.
    + rewrite (HagC 11) by reg_neq_tac. sym_regs HR. sym_close.
    + rewrite (HagC 12) by reg_neq_tac. sym_regs HR. sym_close.
    + rewrite (HagC 13) by reg_neq_tac. sym_regs HR. sym_close.
Qed.

(* ================================================================= *)
(* Entry to the first brk ecall                                       *)
(* ================================================================= *)

Lemma target_to_brk1 : (Z.of_nat tnn <= 65536)%Z ->
  exists regs3,
    reg_get regs3 2 = Z_to_bv 64 (bv_unsigned asp - 32) /\
    reg_get regs3 8 = ptrA /\
    reg_get regs3 10 = Z_to_bv 64 0 /\
    reg_get regs3 13 = tnN /\
    msteps target_segs
      (init_machine_state RT 0x1001158 target_phdrs asp amb arnd inp)
      {| ms_regs := regs3; ms_fregs := fp_regs; ms_pc_val := (0x10011c8 : word);
         ms_svc_pending := Some (Z_to_bv 64 214); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := tfmem; ms_rom := trom |}.
Proof.
  intros Hncap.
  pose proof tnN_le as HnnLe.
  destruct target_to_captest as (regs2 & H1 & H2 & H8 & H10 & Hms).
  (* 0x10011ac .. 0x10011c4: the cap test (taken), the brk argument
     registers -- one block, stopping at the [ecall]. *)
  sym_block_ex target_segs (mkst regs2 (Z_to_bv 64 0x10011ac) tfmem trom)
    6%nat [true] (@nil expr)
    [((2 : reg), EVar 32); ((8 : reg), EVar 33); ((10 : reg), EVar 34)]
    [Z_to_bv 64 (bv_unsigned asp - 32); ptrA; tnN] (@nil word) R HR Hms2.
  { (* 0x10011b0: bgeu a1, a0 IS taken -- n <= 65536 *)
    pose proof u_tnN. sym_br. }
  { exact H2. }
  { exact H8. }
  { exact H10. }
  exists R. repeat split.
  5: { eapply msteps_trans; [exact Hms|].
       sym_chain Hms2.
       (* 0x10011c8: ecall -- brk(0) *)
       eapply mst_step;
         [ reflexivity | apply (step_ecall _ _ _ _ _ _ TF_10011c8 eq_refl) | ].
       match goal with
       | |- msteps _ {| ms_regs := ?RR; ms_fregs := _; ms_pc_val := _;
                        ms_svc_pending := _; ms_resv := _; ms_fcsr := _;
                        ms_mem := _; ms_rom := _ |} _ =>
           replace (getr RR 17) with (Z_to_bv 64 214)
             by (sym_regs HR; sym_close)
       end.
       apply mst_refl. }
  all: sym_regs HR; sym_close.
Qed.

(* ================================================================= *)
(* From the return of the first brk (r <> 0, no wrap) to the second    *)
(* brk ecall                                                           *)
(* ================================================================= *)

Lemma target_to_brk2 : forall regs3 (r : word),
  reg_get regs3 2 = Z_to_bv 64 (bv_unsigned asp - 32) ->
  reg_get regs3 8 = ptrA ->
  reg_get regs3 13 = tnN ->
  r <> Z_to_bv 64 0 ->
  (bv_unsigned r + Z.of_nat tnn + 1 < 2^64)%Z ->
  exists regs5,
    reg_get regs5 2 = Z_to_bv 64 (bv_unsigned asp - 32) /\
    reg_get regs5 8 = ptrA /\
    reg_get regs5 10 = r + (tnN + 1) /\
    reg_get regs5 11 = r /\
    reg_get regs5 12 = tnN + 1 /\
    reg_get regs5 13 = tnN /\
    reg_get regs5 14 = Z_to_bv 64 4 /\
    reg_get regs5 15 = r + (tnN + 1) /\
    msteps target_segs (mkst (regupd regs3 10 r) 0x10011cc tfmem trom)
      {| ms_regs := regs5; ms_fregs := fp_regs; ms_pc_val := (0x10011ec : word);
         ms_svc_pending := Some (Z_to_bv 64 214); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := tfmem; ms_rom := trom |}.
Proof.
  intros regs3 r H2 H8 H13 Hrnz Hw.
  pose proof tnN_le as HnnLe.
  pose proof (u64_range r) as Hur.
  pose proof (word_neq0_unsigned r Hrnz) as Hur0.
  assert (Hun1 : bv_unsigned (tnN + 1) = (Z.of_nat tnn + 1)%Z) by (exact u_tnN1).
  assert (Hurn1 : bv_unsigned (r + (tnN + 1))
                  = (bv_unsigned r + Z.of_nat tnn + 1)%Z).
  { rewrite u_add_small; rewrite Hun1; lia. }
  (* The executor computes [a2 = a3 + 1] before [a5 = a2 + a0], so both
     the wrap test and the exit facts see the request in the opposite
     spelling from the statement's. *)
  assert (Ht1 : Z_to_bv 64 (bv_unsigned tnN + 1) = tnN + 1).
  { apply bv_eq. rewrite Hun1, u_Z2bv by (rewrite u_tnN; lia).
    rewrite u_tnN. lia. }
  (* 0x10011cc .. 0x10011e8: the null test on the returned break
     (fall-through), the request, the wrap test (fall-through) and the
     second brk's argument registers -- one block. *)
  sym_block_ex target_segs
    (mkst (regupd regs3 10 r) (Z_to_bv 64 0x10011cc) tfmem trom)
    9%nat [false; false] (@nil expr)
    [((2 : reg), EVar 32); ((8 : reg), EVar 33); ((10 : reg), EVar 34);
     ((13 : reg), EVar 35)]
    [Z_to_bv 64 (bv_unsigned asp - 32); ptrA; r; tnN] (@nil word) R HR Hms.
  { (* 0x10011e0: bgeu a0, a5 falls through -- the request does not wrap *)
    apply negb_false_iff. unfold bv_ltu. apply Z.ltb_lt.
    rewrite Ht1. unfold v_add.
    rewrite u_Z2bv by (rewrite Hun1; lia). rewrite Hun1. lia. }
  { (* 0x10011d0: beq a0, x0 falls through -- the first brk succeeded *)
    sym_br. }
  all: rewrite ?getr_nz by reg_neq_tac.
  { regupd_resolve. exact H2. }
  { regupd_resolve. exact H8. }
  { regupd_resolve. reflexivity. }
  { regupd_resolve. exact H13. }
  exists R. repeat split.
  9: { sym_chain Hms.
       (* 0x10011ec: ecall -- brk(r + n + 1) *)
       eapply mst_step;
         [ reflexivity | apply (step_ecall _ _ _ _ _ _ TF_10011ec eq_refl) | ].
       match goal with
       | |- msteps _ {| ms_regs := ?RR; ms_fregs := _; ms_pc_val := _;
                        ms_svc_pending := _; ms_resv := _; ms_fcsr := _;
                        ms_mem := _; ms_rom := _ |} _ =>
           replace (getr RR 17) with (Z_to_bv 64 214)
             by (sym_regs HR; sym_close)
       end.
       apply mst_refl. }
  (* NOT [sym_close]: its last alternative is [bveq], whose [vm_compute]
     on the OPEN [r]/[ptrA] goals below costs a minute before failing.
     [v_add_comm] goes ahead of it instead. *)
  all: sym_regs HR; rewrite ?Ht1;
       first [ reflexivity | (f_equal; lia) | (apply bv_eq; u_norm; lia)
             | apply v_add_comm | bveq ].
Qed.

(* ================================================================= *)
(* The outcome tree                                                   *)
(* ================================================================= *)

Hypothesis Hbrk_mod : (bv_unsigned abrk mod page_size = 0)%Z.

(** The run's outcome set, over the run's segment list and initial model;
    [Hmb] and [Hrd] as in [brk_rev_ns_source.source_outcomes]. *)
Lemma target_outcomes :
  (mmap_base_min <= bv_unsigned amb)%Z ->
  in_channel_reader inp = true ->
  (Z.of_nat tnn <= 65536)%Z ->
  to_outcomes RT
    (init_machine_state RT 0x1001158 target_phdrs asp amb arnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
       (init_model (segments_reserved RT) abrk amb asp target_alloc_limit inp))
    (brkU (rev_buf targ1)).
Proof.
  intros Hmb Hrd Hncap.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tnN_le as HnnLe.
  assert (Hun1 : bv_unsigned (tnN + 1) = (Z.of_nat tnn + 1)%Z) by (exact u_tnN1).
  pose proof abrk_lo_num as Hblo. pose proof abrk_hi_num as Hbhi.
  assert (Hres : (reserved_top (segments_reserved RT) <= bv_unsigned abrk)%Z).
  { (* the image's list is concrete, so the run's reservations split by
       computation; the vDSO pair reserves nothing *)
    replace (segments_reserved RT)
      with (segments_reserved target_segs
            ++ segments_reserved (vdso_segments (in_kernel inp) asp amb))
      by reflexivity.
    rewrite segments_reserved_vdso, app_nil_r. exact Hbrk_lo. }
  assert (Hfd0 : fd1chan (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
                   (init_model (segments_reserved RT) abrk amb asp target_alloc_limit inp)))
    by exact (init_model_fd1chan (segments_reserved RT) abrk amb asp
                target_alloc_limit inp Hrd).
  destruct (target_to_brk1 Hncap)
    as (regs3 & E2 & E8 & E10 & E13 & Hms).
  eapply tou_msteps; [exact (msteps_run target_segs inp asp amb _ _ Hms)|].
  apply (tou_brk_r RT _ _ (Z_to_bv 64 214)
           (T1 (init_reserved (segments_reserved RT) amb asp (in_kernel inp))
              target_alloc_limit (bv_unsigned asp - stack_max_size) (tnN + 1)
              [rev_buf targ1]));
    [reflexivity | vm_compute; reflexivity | | ].
  { (* per-resolution continuation *)
    intros r Hok.
    unfold ms_gpr in Hok |- *; cbn [ms_regs] in Hok |- *.
    rewrite arg_reg_0, E10 in Hok |- *.
    change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved RT) amb asp (in_kernel inp))
                        [] [] abrk abrk target_alloc_limit amb asp)
              (Z_to_bv 64 0) r) in Hok.
    (* brk(0) is deterministic: it reports the quantified ASLR base. *)
    apply brk_r_ok_query_iff in Hok. cbn [vm_brk] in Hok.
    rewrite m_vmmaps_with_vdso, m_vmmaps_init_model. cbn [vm_brk].
    assert (Hur : bv_unsigned r = bv_unsigned abrk)
      by (rewrite Hok; reflexivity).
    assert (Hrmod : (bv_unsigned r mod page_size = 0)%Z).
    { rewrite Hur. exact Hbrk_mod. }
    assert (Hrnz : r <> Z_to_bv 64 0).
    { intro Hc. apply (f_equal bv_unsigned) in Hc.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
    assert (Hnw : (bv_unsigned r + Z.of_nat tnn + 1 < 2^64)%Z)
      by (change (2^64)%Z with 18446744073709551616%Z; lia).
    assert (Hurn1 : bv_unsigned (r + (tnN + 1))
                    = (bv_unsigned r + Z.of_nat tnn + 1)%Z).
    { rewrite u_add_small; rewrite Hun1; lia. }
    assert (Hwant0 : r + (tnN + 1) <> Z_to_bv 64 0).
    { intro He. apply (f_equal bv_unsigned) in He.
      rewrite Hurn1 in He.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in He. lia. }
    assert (Hne2 : r <> r + (tnN + 1)).
    { intro He. apply (f_equal bv_unsigned) in He.
      rewrite Hurn1 in He. lia. }
    rewrite brk_zeros_query.
    rewrite (brk_unmaps_grow r abrk) by lia.
    rewrite adv_brk, apply_zeros_nil. wlits.
    rewrite brk_model_query by exact Hok.
    rewrite m_vmmaps_with_vdso, m_vmmaps_init_model.
    cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_limit vm_mmap_base vm_init_sp].
    (* base is nonzero and non-wrapping: straight to the second brk *)
    destruct (target_to_brk2 regs3 r E2 E8 E13 Hrnz Hnw)
          as (regs5 & F2 & F8 & F10 & F11 & F12 & F13 & F14 & F15 & Hms2).
        eapply tou_msteps; [exact (msteps_run target_segs inp asp amb _ _ Hms2)|].
        apply (tou_brk_r RT _ _ (Z_to_bv 64 214)
                 (T2 (r + (tnN + 1)) [rev_buf targ1]));
          [reflexivity | vm_compute; reflexivity | | ].
        * (* per-resolution continuation at the second brk *)
          intros r2 Hok2.
          unfold ms_gpr in Hok2 |- *; cbn [ms_regs] in Hok2 |- *.
          rewrite arg_reg_0, F10 in Hok2 |- *.
          change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved RT) amb asp
                                            (in_kernel inp))
                              [] [] abrk r target_alloc_limit amb asp)
                    (r + (tnN + 1)) r2) in Hok2.
          rewrite m_vmmaps_with_vmmaps. cbn [vm_brk].
          apply brk_r_ok_grow_iff in Hok2;
            [ | lia | lia | lia ].
          destruct (decide (r2 = r + (tnN + 1))) as [-> | Hne].
          { (* success resolution *)
            destruct Hok2 as [_ Hgrow2].
            rewrite brk_grow_ok_aligned_grow in Hgrow2;
              [ cbn [vm_brk vm_reserved vm_maps] in Hgrow2;
                rewrite app_nil_r in Hgrow2
              | exact Hwant0
              | cbn [vm_brk]; lia
              | cbn [vm_brk]; rewrite Hurn1; lia
              | cbn [vm_brk]; exact Hrmod ].
            apply andb_true_iff in Hgrow2; destruct Hgrow2 as [Hgrow2 Hbud].
            apply andb_true_iff in Hgrow2; destruct Hgrow2 as [Hle Hfree].
            apply Z.leb_le in Hle.
            set (grant := Z_to_bv 64
              (page_round_up_Z (bv_unsigned (r + (tnN + 1))) - bv_unsigned r)).
            destruct (brk_aligned_grant_ok _ r (tnN + 1) grant _ _
                        ltac:(apply u_add_small; rewrite Hun1; lia)
                        Hurn1 eq_refl (alloc_top_page_lt _) Hle Hfree)
              as (HgrantU & Hgrant & Hphysceil & Hrawceil & Hrawfree & _).
            rewrite brk_zeros_aligned_grow;
              [ | exact Hwant0 | lia | rewrite Hurn1; lia | exact Hrmod ].
            fold grant.
            rewrite brk_unmaps_grow by lia.
            rewrite adv_brk, apply_zeros_one. wlits.
            eapply tou_equiv;
              [ | intro o; apply (T2_succ_iff (r + (tnN + 1)) [rev_buf targ1]) ].
            apply tou_wexit_eq.
            - apply fd1chan_brk_model. apply fd1chan_with_vmmaps. exact Hfd0.
            - apply to_wallexit_run.
              apply (target_success (regupd regs5 10 (r + (tnN + 1))) r grant).
              + exact Hgrant.
              + exact Hphysceil.
              + lia.
              + exact Hrawceil.
              + regupd_resolve. exact F2.
              + regupd_resolve. exact F8.
              + regupd_resolve. reflexivity.
              + regupd_resolve. exact F11.
              + regupd_resolve. exact F12.
              + regupd_resolve. exact F13.
              + regupd_resolve. exact F15.
            - exact tbufs_modeled. }
          { (* failure resolution: r2 = r, exit 4 *)
            destruct Hok2 as [Hcase _].
            destruct Hcase as [Hc | Hc]; [exact (False_ind _ (Hne Hc)) |].
            subst r2.
            rewrite brk_zeros_keep.
            rewrite brk_unmaps_grow by lia.
            rewrite adv_brk, apply_zeros_nil. wlits.
            eapply tou_equiv;
              [ | intro o;
                  apply (T2_fail_iff (r + (tnN + 1)) [rev_buf targ1] r Hne2) ].
            apply tou_wexit_eq.
            - apply fd1chan_brk_model. apply fd1chan_with_vmmaps. exact Hfd0.
            - (* bne a0, a5 taken ; exit 4 *)
              apply to_wallexit_run. cbn [to_wallexit].
              eapply tw_step;
                [ reflexivity
                | eapply step_bne_tk;
                  [ exact TF_10011f0 | reflexivity | exact TD_10011f0
                  | getr_resolve; regupd_resolve; rewrite F15;
                    apply c_eq_neq; rewrite Hurn1; lia ]
                | norm_pc ].
              apply target_exit.
              + regupd_resolve. exact F2.
              + regupd_resolve. exact F14.
              + u_norm; lia.
              + apply read_slot_ra_t.
              + apply read_slot_s0_t.
            - (* no output on the failing resolution *)
              apply Forall_nil. }
        * (* set identity at the second node *)
          intro o.
          unfold ms_gpr; cbn [ms_regs].
          rewrite arg_reg_0, F10.
          change (T1 (init_reserved (segments_reserved RT) amb asp (in_kernel inp))
                     target_alloc_limit (bv_unsigned asp - stack_max_size) (tnN + 1)
                     [rev_buf targ1] r o <->
                  (exists r2,
                     brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved RT) amb asp
                                               (in_kernel inp))
                                 [] [] abrk r target_alloc_limit amb asp)
                       (r + (tnN + 1)) r2
                     /\ T2 (r + (tnN + 1)) [rev_buf targ1] r2 o)).
          apply (T1_iff_T2 (init_reserved (segments_reserved RT) amb asp (in_kernel inp))
                   target_alloc_limit abrk amb asp tnN [rev_buf targ1] r);
            [ exact Hrnz | lia
            | rewrite u_tnN; lia | rewrite u_tnN; lia ]. }
  { (* set identity at the first node: the query resolves to abrk only *)
    intro o.
    unfold ms_gpr; cbn [ms_regs].
    rewrite arg_reg_0, E10.
    apply (brkU_iff_T1 (init_reserved (segments_reserved RT) amb asp (in_kernel inp))
             target_alloc_limit (bv_unsigned asp - stack_max_size) tnN (rev_buf targ1)
             abrk).
    - intro r0.
      change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved RT) amb asp
                                        (in_kernel inp))
                          [] [] abrk abrk target_alloc_limit amb asp)
                (Z_to_bv 64 0) r0 <-> r0 = abrk).
      apply brk_r_ok_query_iff.
    - (* growable at the quantified base, over the run's ledger *)
      apply growable_ledger.
      + exact Hmb.
      + exact Hsp_lo.
      + exact Hbrk_mod.
      + lia.
      + exact Hres.
      + rewrite Hun1. lia.
      + rewrite Hun1. unfold page_size. lia.
      + rewrite Hun1. unfold page_size, target_alloc_limit. lia.
      + rewrite Hun1. unfold page_size. lia.
    - (* the grow amount cannot be the zero word *)
      intro Hc. apply (f_equal bv_unsigned) in Hc.
      rewrite Hun1 in Hc.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
Qed.

End Ge2MainT.

End TargetProof.
