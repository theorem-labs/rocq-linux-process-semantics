(** * oob-read-bug-ns target binary: per-binary derivations.

    PROOF-SIDE FILE (not part of the trusted specification).

    Bytes are [byte = bv 8], machine values [word = bv 64]; unbounded
    bookkeeping is in [Z] over [bv_unsigned]; computed stack addresses use
    the canonical [Z_to_bv 64 (...)] form, pc values numeral literals.

    Deliverables (Section [TargetProof], generic over av/ev and the
    ASLR window asp):
    - [target_wexit_lt2]  : argc < 2             -> to_wexit [] 2
    - [target_wexit_cap]  : argc >= 2, n > 65536 -> to_wexit [] 3
    - the copy/sum/put pieces consumed by target_outcomes.v. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec AllocSim WallSim StepTac StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Common Require Import Footprint SymExec SymTac SymBranch SymSide.
From LinuxProcessSemantics.Examples.oob_read_bug_ns Require Import oob_read_bug_ns_code oob_read_bug_ns_defs.
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

(** Close a CLOSED word/byte equation by unsigned comparison. *)

(* ######################################################################### *)
(* Local helpers (copied from grep_args_ns / brk_rev_ns ports)               *)
(* ######################################################################### *)


Lemma word_add_nat_1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word m) 1 = a + nat_to_word (S m).
Proof.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma word_add_nat_m1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word (S m)) (-1) = a + nat_to_word m.
Proof.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma v_addi_natS_m1 : forall k : nat, v_addi (nat_to_word (S k)) (-1) = nat_to_word k.
Proof.
  intro k. unfold nat_to_word, v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma sumb_nonneg : forall s, (0 <= sumb s)%Z.
Proof.
  induction s as [|b s IH]; [cbn; lia|].
  unfold sumb in *. cbn [fold_right]. pose proof (u8_range b). lia.
Qed.

(* ######################################################################### *)
(* Reserved list and store legality                                          *)
(* ######################################################################### *)


(** [andi] with the written value pre-normalized (the [andi] analogue of
    [SeqExec.step_addi_at]): keeps the chained machine state flat. *)
Lemma step_andi_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_AND rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_andi (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_andi segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

(** The defensive guard's [andi a0, a0, 7] is the mod-8 residue. *)
Lemma v_andi_7_mod8 : forall x : word,
  v_andi x 7 = Z_to_bv 64 (bv_unsigned x mod 8).
Proof.
  intro x. unfold v_andi. f_equal.
  replace (bv_wrap 64 7) with (Z.ones 3) by (vm_compute; reflexivity).
  rewrite Z.land_ones by lia.
  change (2 ^ 3)%Z with 8%Z. reflexivity.
Qed.

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x100115c%N.
Proof. vm_compute. reflexivity. Qed.

Lemma target_reserved_val :
  segments_reserved target_segs = [(0x1000000, 0x1000); (0x1001000, 0x1000)].
Proof.
  apply (@bool_decide_eq_true_1 (_ = _) _). vm_cast_no_check (eq_refl true).
Qed.

(** Stores at/above the end of the second (read-only) segment are legal
    (page-rounded ro segments: [0x1000000, 0x1001000) and
    [0x1001000, 0x1002000)). *)
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

(* ######################################################################### *)
(* The proof, generic over argv/envp and the stack pointer                   *)
(* ######################################################################### *)

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

(** The quantified initial program break and mmap base, read here only
    by the launch conjunct. *)
Variable abrk : word.
Variable amb : word.
Hypothesis Hvl : valid_launch inp.

(** The fifth conjunct of [Run.valid_entry_va] for the target's run
    ([create_elf_tables] and [setup_arg_pages], fs/binfmt_elf.c and
    fs/exec.c, Linux v6.18.46): it bounds the entry block, places the
    argv strings below [ed_top] and the stack-store window. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry asp abrk amb arnd) inp.

(** The run's rom: the image's segments, then the vDSO pair. *)
Definition trom : word -> option byte := seg_rom (run_segments target_segs inp asp amb).

Lemma asp_lo_num : (0x7fff80000000 <= bv_unsigned asp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma asp_hi_num : (bv_unsigned asp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Lemma asp_lt64 : (bv_unsigned asp < 2 ^ 64)%Z.
Proof. pose proof (u64_range asp). lia. Qed.

Definition targcN : word := len_word av.
(** The initial overlay, with the entry point [init_mkst] passes to it. *)
Definition awmem : word -> option byte :=
  wrap_mem inp amb target_phdrs (Z_to_bv 64 (Z.of_N 0x100115c)) asp arnd.

Lemma u_targcN : bv_unsigned targcN = Z.of_nat (length av).
Proof.
  pose proof (valid_argv_len av Hva).
  unfold targcN, len_word. apply u_Z2bv; lia.
Qed.

Lemma targcN_le : (Z.of_nat (length av) <= 1024)%Z.
Proof. apply valid_argv_len. exact Hva. Qed.

(** No-overflow bound for the initial stack image, for any entry word. *)
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
  wbytes (wbytes awmem (Z_to_bv 64 (bv_unsigned asp - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
         (Z_to_bv 64 (bv_unsigned asp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

(** Memory after main's prologue (sp = asp - 64):
    ra = 0x100117c at asp-24, s0 = asp at asp-32. *)
Definition tfmem : word -> option byte :=
  wbytes (wbytes amem1 (Z_to_bv 64 (bv_unsigned asp - 24)) (word_to_le_bytes 8 (0x100117c : word)))
         (Z_to_bv 64 (bv_unsigned asp - 32)) (word_to_le_bytes 8 asp).

Lemma rdn_amem1_above : forall (a : word) n,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn target_segs amem1 a n = rdn target_segs awmem a n.
Proof.
  intros a n Ha Hn. pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof (u64_range asp). unfold amem1.
  rewrite rdn_wbytes_disjoint by (rewrite ?length_N_to_le_bytes; u_norm; lia).
  rewrite rdn_wbytes_disjoint by (rewrite ?length_N_to_le_bytes; u_norm; lia).
  reflexivity.
Qed.

Lemma rdn_tfmem_above : forall (a : word) n,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn target_segs tfmem a n = rdn target_segs awmem a n.
Proof.
  intros a n Ha Hn. pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof (u64_range asp). unfold tfmem.
  rewrite rdn_wbytes_disjoint by (rewrite ?length_N_to_le_bytes; u_norm; lia).
  rewrite rdn_wbytes_disjoint by (rewrite ?length_N_to_le_bytes; u_norm; lia).
  apply rdn_amem1_above; [exact Ha | exact Hn].
Qed.

Lemma rdn_awmem_stack : forall (a : word) n,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn target_segs awmem a n
  = rdn target_segs
      (stack_to_mem asp (entry_stack_image inp amb target_phdrs
                           (Z_to_bv 64 (Z.of_N 0x100115c)) asp arnd)) a n.
Proof. intros a n Ha Hn. apply rdn_wrap_stack_above; [exact Ha | exact Hn]. Qed.

Lemma read_argc_a1 :
  rdn target_segs amem1 asp 8%nat = Some (word_le8 targcN).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  rewrite rdn_amem1_above by lia.
  rewrite rdn_awmem_stack by lia.
  apply read_argc. apply target_bsb_nw.
Qed.

(* ----------------------------------------------------------------- *)
(* argv[1] and its bytes                                             *)
(* ----------------------------------------------------------------- *)

Definition targ1 : list byte := nth 1 av [].
Definition tnn : nat := length targ1.
Definition tnN : word := nat_to_word tnn.
Definition ptrA : word := cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1.

(* ----------------------------------------------------------------- *)
(* Frame-slot read-back                                             *)
(* ----------------------------------------------------------------- *)

Lemma read_slot_ra_t :
  rdn target_segs tfmem (Z_to_bv 64 (bv_unsigned asp - 24)) 8%nat
  = Some (word_to_le_bytes 8 (0x100117c : word)).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof (u64_range asp). unfold tfmem.
  rewrite rdn_wbytes_disjoint by (rewrite ?length_N_to_le_bytes; u_norm; lia).
  apply rdn_wbytes_hit8. u_norm; lia.
Qed.

Lemma read_slot_s0_t :
  rdn target_segs tfmem (Z_to_bv 64 (bv_unsigned asp - 32)) 8%nat
  = Some (word_to_le_bytes 8 asp).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof (u64_range asp). unfold tfmem.
  apply rdn_wbytes_hit8. u_norm; lia.
Qed.

(** The [ld a0,0(s0)] of argc, as the executor's [SCReadBase] states it:
    against the ORIGINAL memory, so no overlay peeling is needed. *)
Ltac tb_read_argc :=
  replace (Z_to_bv 64 (bv_unsigned asp + 0)) with asp by (apply bv_eq; u_norm; lia);
  exists (word_le8 targcN); split;
    [ rewrite rdn_wrap_stack_above by lia; apply read_argc; apply target_bsb_nw
    | apply bytes_le_n_to_le_8 ].

(* ################################################################# *)
(* Epilogue-exit: 0x10012dc .. ret .. exit ecall                     *)
(* ################################################################# *)

Lemma target_exit : forall regs mem (code : word),
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64) ->
  reg_get regs 13 = code -> (bv_unsigned code < 256)%Z ->
  rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 24)) 8%nat
    = Some (word_to_le_bytes 8 (0x100117c : word)) ->
  rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 32)) 8%nat
    = Some (word_to_le_bytes 8 asp) ->
  to_wexit target_segs (mkst regs 0x10011d0 mem trom) [] code.
Proof.
  intros regs mem code H2 H13 Hc Hra Hs0.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof (u64_range asp).
  (* SIX instructions in one reflective block: the two frame reloads, the
     stack pop, the exit-code shuffle, the [ret] and crt's [li a7,93],
     stopping at the [exit] ecall.  The [ra] reload is NAMED in the read
     script, which is what lets the [ret] resolve to a literal pc. *)
  sym_block target_segs 10%nat (@nil bool) [ELit 0x100117c]
    [((2 : reg), EVar 32)] [Z_to_bv 64 (bv_unsigned asp - 64)]
    (* the read script's own [ELit] still consumes a variable slot, so the
       first [rvals] entry is a placeholder and [s0]'s value is the
       second *)
    [Z_to_bv 64 0; asp] RA HRA.
  { (* [ld s0,32(sp)] -> the caller's frame pointer *)
    exists (word_to_le_bytes 8 asp); split; [exact Hs0 | apply bytes_le_to_Z_8]. }
  { (* [ld ra,40(sp)] -> main's return address *)
    exists (word_to_le_bytes 8 (0x100117c : word)); split;
      [ exact Hra | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]. }
  { (* the [sp] pin *) exact H2. }
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ TF_1001180 eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRA; sym_close.
  - sym_regs HRA; exact H13.
  - exact Hc.
Qed.

(* ################################################################# *)
(* Entry: prologue and the argc test                                 *)
(* ################################################################# *)

(** argc < 2: no output, exit 2. *)
Lemma target_wexit_lt2 : (length av < 2)%nat ->
  to_wexit target_segs
    (init_machine_state (run_segments target_segs inp asp amb) 0x100115c target_phdrs asp amb arnd inp)
    [] (Z_to_bv 64 2).
Proof.
  intros Hlt2.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof targcN_le as HargcLe.
  rewrite init_mkst. norm_pc.
  (* FIFTEEN instructions in one block: the entry prologue, the argc
     load, the [jalr] into main, the [bltu] falling through, the exit
     code and the [j] into the epilogue's tail, stopping at the [ecall]. *)
  sym_block target_segs 20%nat [false] (@nil expr)
    [((2 : reg), EVar 32)] [asp] [targcN] RA HRA.
  { (* [bltu a2,a0] falls through: argc <= 1 *)
    rewrite bv_ltu_Z; apply Z.ltb_ge; u_norm; rewrite u_targcN; lia. }
  { (* [ld a0,0(s0)] -> argc, out of the initial stack image *)
    tb_read_argc. }
  { (* [sd s0,0(sp)] *) solve_store_ok_inv. }
  { (* [sd ra,8(sp)] *) solve_store_ok_inv. }
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ TF_1001180 eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRA; sym_close.
  - sym_regs HRA; sym_close.
  - vm_compute. reflexivity.
Qed.

(* ################################################################# *)
(* argc >= 2                                                         *)
(* ################################################################# *)

Section Ge2MainT.

Hypothesis Hge2 : (2 <= length av)%nat.

Lemma tnN_le : (Z.of_nat tnn <= 131071)%Z.
Proof.
  unfold tnn, targ1. apply valid_argv_str_len; [exact Hva | lia].
Qed.

Lemma u_tnN : bv_unsigned tnN = Z.of_nat tnn.
Proof. unfold tnN, nat_to_word. apply u_Z2bv; [lia | pose proof tnN_le; lia]. Qed.

Lemma targ1_nz : ~ In (Z_to_bv 8 0) targ1.
Proof. unfold targ1. apply valid_argv_str_nz; [exact Hva | lia]. Qed.

Lemma targ1_bytes : Forall (fun b : byte => (bv_unsigned b < 256)%Z) targ1.
Proof. unfold targ1. apply valid_argv_str_bytes; [exact Hva | lia]. Qed.

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
  rewrite rdn_tfmem_above by lia. rewrite rdn_awmem_stack by lia.
  replace (S tnn) with (tnn + 1)%nat by lia.
  apply rdn_app.
  - unfold ptrA, targ1, tnn.
    apply (read_argv_str_k Sv48 target_segs inp amb target_phdrs _ asp abrk arnd 1 Hlau).
    lia.
  - pose proof (read_argv_byte_k Sv48 target_segs inp amb target_phdrs
                  (Z_to_bv 64 (Z.of_N 0x100115c)) asp abrk arnd 1 tnn Hlau
                  ltac:(lia) ltac:(unfold tnn, targ1; lia)) as Hbk.
    replace (nth tnn (nth 1 av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) with (Z_to_bv 8 0) in Hbk.
    + exact Hbk.
    + symmetry. unfold tnn, targ1.
      change (nth (length (nth 1 av [])) (nth 1 av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))
        with (byte_at (nth 1 av []) (length (nth 1 av []))).
      apply byte_at_len.
Qed.

(** From the entry point to the strlen loop head 0x100132c. *)
Lemma target_to_loop :
  exists regs1,
    reg_get regs1 1 = (0x10011b0 : word) /\
    reg_get regs1 2 = Z_to_bv 64 (bv_unsigned asp - 64) /\
    reg_get regs1 8 = ptrA /\
    reg_get regs1 10 = ptrA /\ reg_get regs1 11 = Z_to_bv 64 0 /\
    msteps target_segs
      (init_machine_state (run_segments target_segs inp asp amb) 0x100115c target_phdrs asp amb arnd inp)
      (mkst regs1 0x1001334 tfmem trom).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof (u64_range asp).
  pose proof targcN_le as HargcLe.
  pose proof ptrA_lo as Hplo. pose proof ptrA_hi as Hphi.
  pose proof tnN_le as HnnLe.
  (* EIGHTEEN instructions in one reflective block: the entry prologue,
     main's own prologue and argv[1] load, and the [jalr] into strlen up
     to its loop head.  The exit register file is the WITNESS of this
     statement's existential, so the [destruct] has to happen before the
     [exists] -- which is what [sym_block_ex] is for. *)
  sym_block_ex target_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 asp)
          (Z_to_bv 64 (Z.of_N 0x100115c))
          (wrap_mem inp amb target_phdrs (Z_to_bv 64 (Z.of_N 0x100115c)) asp arnd)
          (seg_rom (run_segments target_segs inp asp amb)))
    18%nat [true] (@nil expr)
    [((2 : reg), EVar 32)] [asp] [targcN; ptrA] RA HRA Hms.
  { (* [ld s0,8(a1)] -> the argv[1] pointer *)
    replace (Z_to_bv 64 (bv_unsigned asp + 16)) with (asp + nat_to_word (8 + 8 * 1))
      by (rewrite word_add_nat; f_equal; cbn [Z.of_nat Nat.add Nat.mul]; lia);
    exists (word_le8 ptrA); split;
      [ rewrite rdn_wrap_stack_above by (rewrite ?word_add_nat; u_norm; lia);
        unfold ptrA; apply read_argv_ptr_k; [lia | apply target_bsb_nw]
      | apply bytes_le_n_to_le_8 ]. }
  { (* [sd s0,32(sp)] *) solve_store_ok_inv. }
  { (* [sd ra,40(sp)] *) solve_store_ok_inv. }
  { (* [bltu a2,a0] taken: argc >= 2 *)
    rewrite bv_ltu_Z; apply Z.ltb_lt; u_norm; rewrite u_targcN; lia. }
  { (* [ld a0,0(s0)] -> argc *) tb_read_argc. }
  { (* [sd s0,0(sp)] *) solve_store_ok_inv. }
  { (* [sd ra,8(sp)] *) solve_store_ok_inv. }
  (* The block's exit memory is the store log's denotation; [tfmem] is
     the same four-layer chain, written out in the file's own spelling. *)
  match type of Hms with
  | msteps _ _ (mkst _ _ ?m _) =>
      assert (Hm : m = tfmem)
        by (unfold tfmem, amem1, awmem;
            cbn [edenot adenot bdenot a_base a_off e_addr e_width e_val];
            rewrite alu64_add_0; reflexivity)
  end.
  rewrite Hm in Hms.
  exists RA. repeat split; try (sym_regs HRA; sym_close).
  rewrite init_mkst.
  replace (0x1001334 : word) with (Z_to_bv 64 0x1001334) by bveq.
  exact Hms.
Qed.

(** The strlen loop: from 0x100132c with a1 = j, exit at 0x100133c with
    a1 = n + 1. *)
Lemma target_strlen : forall mem,
  rdn target_segs mem ptrA (S tnn) = Some (targ1 ++ [Z_to_bv 8 0]) ->
  forall d j regs,
  (j + d = tnn)%nat ->
  reg_get regs 10 = ptrA ->
  reg_get regs 11 = nat_to_word j ->
  exists regs',
    (forall x : reg, x <> 11 -> x <> 12 -> reg_get regs' x = reg_get regs x) /\
    reg_get regs' 11 = nat_to_word (S tnn) /\
    msteps target_segs (mkst regs 0x1001334 mem trom)
                       (mkst regs' 0x1001344 mem trom).
Proof.
  intros mem Hread.
  pose proof ptrA_lo as Hplo. pose proof ptrA_hi as Hphi.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tnN_le as HnnLe.
  pose proof targ1_nz as Hnz.
  pose proof targ1_bytes as Hbytes.
  induction d as [|d IH]; intros j regs Hjd Hr10 Hr11.
  - (* j = tnn: NUL sentinel *)
    assert (Hj : j = tnn) by lia.
    set (regs1 := regupd regs 12 (ptrA + nat_to_word j)).
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001334 mem trom)
                 = MachineOk (mkst regs1 0x1001338 mem trom)).
    { rewrite (step_add target_segs regs 0x1001334 mem trom _ 12 10 11
                 TF_1001334 eq_refl TD_1001334).
      reduce_bv_eqb_ifs. getr_resolve. rewrite Hr10, Hr11. wlits. reflexivity. }
    set (regs2 := regupd regs1 12 (Z_to_bv 64 0)).
    assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x1001338 mem trom)
                 = MachineOk (mkst regs2 0x100133c mem trom)).
    { rewrite (step_lbu target_segs regs1 0x1001338 mem trom _ 12 12 _ (Z_to_bv 8 0)
                 TF_1001338 eq_refl TD_1001338).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite v_addi_0.
        pose proof (rdn_nth _ _ _ _ _ tnn Hread ltac:(lia)) as Hb.
        assert (Hb0 : nth tnn (targ1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = Z_to_bv 8 0).
        { change (nth tnn (targ1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))
            with (byte_at targ1 tnn).
          rewrite <- Hj at 1. rewrite Hj. apply byte_at_len. }
        rewrite Hb0 in Hb.
        rewrite Hj. exact Hb. }
    set (regs3 := regupd regs2 11 (nat_to_word (S tnn))).
    assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x100133c mem trom)
                 = MachineOk (mkst regs3 0x1001340 mem trom)).
    { rewrite (step_addi_at target_segs regs2 0x100133c mem trom _ 11 11 _
                 (nat_to_word (S tnn)) TF_100133c eq_refl TD_100133c eq_refl).
      - wlits. reflexivity.
      - unfold regs3, regs2, regs1. getr_resolve. rewrite Hr11, Hj.
        rewrite v_addi_Sj by (pose proof tnN_le; lia). reflexivity. }
    assert (E4 : RiscvSemantics.step target_segs (mkst regs3 0x1001340 mem trom)
                 = MachineOk (mkst regs3 0x1001344 mem trom)).
    { rewrite (step_bne_ft target_segs regs3 0x1001340 mem trom _ 12 0 _
                 TF_1001340 eq_refl TD_1001340).
      - wlits. reflexivity.
      - unfold regs3, regs2. getr_resolve. exact c_eq_0_true. }
    exists regs3. split; [|split].
    + intros x H11 H12. unfold regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs3. apply regupd_same.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      apply mst_refl.
  - (* j < tnn: nonzero byte *)
    assert (Hjlt : (j < tnn)%nat) by lia.
    set (b := byte_at targ1 j).
    assert (Hbnz : b <> Z_to_bv 8 0) by (apply byte_at_nz; assumption).
    set (regs1 := regupd regs 12 (ptrA + nat_to_word j)).
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001334 mem trom)
                 = MachineOk (mkst regs1 0x1001338 mem trom)).
    { rewrite (step_add target_segs regs 0x1001334 mem trom _ 12 10 11
                 TF_1001334 eq_refl TD_1001334).
      reduce_bv_eqb_ifs. getr_resolve. rewrite Hr10, Hr11. wlits. reflexivity. }
    set (regs2 := regupd regs1 12 (Z_to_bv 64 (bv_unsigned b))).
    assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x1001338 mem trom)
                 = MachineOk (mkst regs2 0x100133c mem trom)).
    { rewrite (step_lbu target_segs regs1 0x1001338 mem trom _ 12 12 _ b
                 TF_1001338 eq_refl TD_1001338).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite v_addi_0.
        pose proof (rdn_nth _ _ _ _ _ j Hread ltac:(lia)) as Hb'.
        replace (nth j (targ1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) with b in Hb'
          by (unfold b, byte_at; reflexivity).
        exact Hb'. }
    set (regs3 := regupd regs2 11 (nat_to_word (S j))).
    assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x100133c mem trom)
                 = MachineOk (mkst regs3 0x1001340 mem trom)).
    { rewrite (step_addi_at target_segs regs2 0x100133c mem trom _ 11 11 _
                 (nat_to_word (S j)) TF_100133c eq_refl TD_100133c eq_refl).
      - wlits. reflexivity.
      - unfold regs3, regs2, regs1. getr_resolve. rewrite Hr11.
        rewrite v_addi_Sj by lia. reflexivity. }
    assert (E4 : RiscvSemantics.step target_segs (mkst regs3 0x1001340 mem trom)
                 = MachineOk (mkst regs3 0x1001334 mem trom)).
    { rewrite (step_bne_tk target_segs regs3 0x1001340 mem trom _ 12 0 _
                 TF_1001340 eq_refl TD_1001340).
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

(** After strlen: back in main at 0x10011b0 with a0 = n. *)
Lemma target_to_captest :
  exists regs2,
    reg_get regs2 1 = (0x10011b0 : word) /\
    reg_get regs2 2 = Z_to_bv 64 (bv_unsigned asp - 64) /\
    reg_get regs2 8 = ptrA /\
    reg_get regs2 10 = tnN /\
    msteps target_segs
      (init_machine_state (run_segments target_segs inp asp amb) 0x100115c target_phdrs asp amb arnd inp)
      (mkst regs2 0x10011b0 tfmem trom).
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
      [ exact TF_1001344 | reflexivity | exact TD_1001344 | reflexivity
      | getr_resolve; rewrite H11'; unfold tnN; apply v_addi_natS_m1 ]
    | step_simpl ].
  (* ret -> 0x10011b0 *)
  stepjr TF_1001348 TD_1001348 (0x10011b0 : word) ltac:(getr_resolve; regupd_resolve; rewrite (Hag 1) by reg_neq_tac; exact H1).
  apply mst_refl. }
  - regupd_resolve. rewrite (Hag 1) by reg_neq_tac. exact H1.
  - regupd_resolve. rewrite (Hag 2) by reg_neq_tac. exact H2.
  - regupd_resolve. rewrite (Hag 8) by reg_neq_tac. exact H8.
  - regupd_resolve. reflexivity.
Qed.

(** n > 65536: no output, exit 3. *)
Lemma target_wexit_cap : (65536 < Z.of_nat tnn)%Z ->
  to_wexit target_segs
    (init_machine_state (run_segments target_segs inp asp amb) 0x100115c target_phdrs asp amb arnd inp)
    [] (Z_to_bv 64 3).
Proof.
  intros Hcap.
  pose proof tnN_le as HnnLe.
  destruct target_to_captest as (regs2 & H1 & H2 & H8 & H10 & Hms).
  eapply msteps_to_wexit; [exact Hms|].
  (* lui a2, 0x10 -> 65536 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_lui_at with (v := Z_to_bv 64 65536);
      [ exact TF_10011b0 | reflexivity | exact TD_10011b0 | reflexivity
      | bveq ]
    | step_simpl ].
  (* bgeu a2, a0 fall-through (65536 < n) *)
  eapply tw_step;
    [ reflexivity
    | eapply step_bgeu_ft;
      [ exact TF_10011b4 | reflexivity | exact TD_10011b4
      | getr_resolve; regupd_resolve; rewrite H10;
        rewrite c_ltu_ltb; apply Z.ltb_lt; u_norm; rewrite u_tnN; lia ]
    | step_simpl ].
  (* li a3, 3 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 3);
      [ exact TF_10011b8 | reflexivity | exact TD_10011b8 | reflexivity
      | getr_resolve; bveq ]
    | step_simpl ].
  (* j 0x10011d0 *)
  eapply tw_step;
    [ reflexivity
    | exact (step_jal_x0 _ _ _ _ _ _ _ TF_10011bc eq_refl TD_10011bc)
    | norm_pc ].
  apply target_exit.
  - regupd_resolve. exact H2.
  - regupd_resolve. reflexivity.
  - vm_compute. reflexivity.
  - apply read_slot_ra_t.
  - apply read_slot_s0_t.
Qed.

(** The old defensive modulus guard is now an opaque zero marker.  In
    particular, a non-multiple-of-eight input reaches the common brk path
    instead of returning 4.

    RETAINED BUT NO LONGER CALLED, for the same reason as
    [oob_read_bug_ns_source.v]'s [source_outcomes_mix]: page-rounded [brk]
    grants removed the [n mod 8] case split that used to consume it. *)
Lemma target_continues_mod :
  (Z.of_nat tnn <= 65536)%Z -> (tnn mod 8 <> 0)%nat ->
  exists regs3,
    msteps target_segs
      (init_machine_state (run_segments target_segs inp asp amb) 0x100115c target_phdrs asp amb arnd inp)
      (mkst regs3 0x10011c8 tfmem trom).
Proof.
  intros Hncap _.
  pose proof tnN_le as HnnLe.
  destruct target_to_captest as (regs2 & H1 & H2 & H8 & H10 & Hms).
  eapply ex_intro.
  eapply msteps_trans; [exact Hms|].
  (* lui a2, 0x10 -> 65536 *)
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
  apply mst_refl.
Qed.

(* ################################################################# *)
(* The forward-copy loop: 0x1001200 .. 0x1001214                     *)
(* ################################################################# *)

(* [store_grant_ok]: the loop's [sb]s are machine stores into the brk
   grant, and [mem0] is abstract here, so the grant's writability has to
   come in as a hypothesis. *)
Lemma target_copy : forall (r : word) mem0,
  store_grant_ok target_segs mem0 r tnN ->
  rdn target_segs mem0 ptrA (S tnn) = Some (targ1 ++ [Z_to_bv 8 0]) ->
  region_free (segments_reserved target_segs) r tnN = true ->
  (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + Z.of_nat tnn <= bv_unsigned asp - stack_max_size)%Z ->
  (bv_unsigned r + Z.of_nat tnn < 2^64)%Z ->
  forall d regs,
  (1 <= d)%nat -> (d <= tnn)%nat ->
  reg_get regs 8 = ptrA + nat_to_word (tnn - d) ->
  reg_get regs 10 = r + nat_to_word (tnn - d) ->
  reg_get regs 13 = nat_to_word d ->
  exists regs',
    (forall x : reg, x <> 8 -> x <> 10 -> x <> 13 -> x <> 14 ->
       reg_get regs' x = reg_get regs x) /\
    reg_get regs' 8 = ptrA + tnN /\ reg_get regs' 10 = r + tnN /\
    reg_get regs' 13 = Z_to_bv 64 0 /\
    msteps target_segs
      (mkst regs 0x1001218 (wbytes mem0 r (firstn (tnn - d) targ1)) trom)
      (mkst regs' 0x1001230 (wbytes mem0 r targ1) trom).
Proof.
  intros r mem0 Hgok Hstr Hfree Hr0 Hceil Hrw.
  pose proof ptrA_lo as Hplo. pose proof ptrA_hi as Hphi.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tnN_le as HnnLe.
  pose proof targ1_bytes as Hbytes.
  pose proof (u64_range r) as Hur.
  assert (Hnn : tnn = length targ1) by reflexivity.
  assert (Hrp : (bv_unsigned r + Z.of_nat tnn <= bv_unsigned ptrA)%Z) by lia.
  induction d as [|d IH]; intros regs Hd1 Hd Hr8 Hr10 Hr13; [lia|].
  remember (tnn - S d)%nat as i eqn:Hie.
  set (b := nth i targ1 (Z_to_bv 8 0)).
  assert (Hi : (i < tnn)%nat) by (rewrite Hie; lia).
  assert (HlenF : length (firstn i targ1) = i) by (apply firstn_length_le; lia).
  assert (Hui : bv_unsigned (r + nat_to_word i) = (bv_unsigned r + Z.of_nat i)%Z)
    by (rewrite u_add_small; rewrite u_ntw by lia; lia).
  assert (Hupi : bv_unsigned (ptrA + nat_to_word i) = (bv_unsigned ptrA + Z.of_nat i)%Z)
    by (rewrite u_add_small; rewrite u_ntw by lia; lia).
  set (memI := wbytes mem0 r (firstn i targ1)).
  (* lbu a4, 0(s0) : byte targ1[i] *)
  set (regs1 := regupd regs 14 (Z_to_bv 64 (bv_unsigned b))).
  assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001218 memI trom)
               = MachineOk (mkst regs1 0x100121c memI trom)).
  { rewrite (step_lbu target_segs regs 0x1001218 memI trom _ 14 8 _ b
               TF_1001218 eq_refl TD_1001218).
    - reduce_bv_eqb_ifs. wlits. reflexivity.
    - getr_resolve. rewrite Hr8. rewrite v_addi_0. unfold memI.
      rewrite rdn_wbytes_disjoint by (rewrite ?HlenF; rewrite ?Hupi; lia).
      pose proof (rdn_nth target_segs mem0 (S tnn) ptrA (targ1 ++ [Z_to_bv 8 0]) i
                    Hstr ltac:(lia)) as Hb'.
      replace (nth i (targ1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) with b in Hb'
        by (unfold b; symmetry; apply app_nth1; exact Hi).
      exact Hb'. }
  (* addi a3, a3, -1 : a3 = d *)
  set (regs2 := regupd regs1 13 (nat_to_word d)).
  assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x100121c memI trom)
               = MachineOk (mkst regs2 0x1001220 memI trom)).
  { rewrite (step_addi_at target_segs regs1 0x100121c memI trom _ 13 13 _
               (nat_to_word d) TF_100121c eq_refl TD_100121c eq_refl).
    - wlits. reflexivity.
    - unfold regs2, regs1. getr_resolve. rewrite Hr13.
      apply v_addi_natS_m1. }
  (* sb a4, 0(a0) : write b at r + i *)
  set (memI' := wbytes mem0 r (firstn (S i) targ1)).
  assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x1001220 memI trom)
               = MachineOk (mkst regs2 0x1001224 memI' trom)).
  { rewrite (step_sb_at target_segs regs2 0x1001220 memI trom _ 10 14 _
               (r + nat_to_word i) b TF_1001220 eq_refl TD_1001220).
    - wlits. replace (wbytes memI (r + nat_to_word i) [b]) with memI'; [reflexivity|].
      unfold memI', memI.
      rewrite (firstn_snoc targ1 i) by lia.
      rewrite wbytes_app. rewrite HlenF. reflexivity.
    - unfold regs2, regs1. getr_resolve. rewrite Hr10. apply v_addi_0.
    - unfold regs2, regs1. getr_resolve. apply zext8_byte.
    - store_ok_peel; apply Hgok; rewrite Hui; rewrite ?u_tnN; lia. }
  (* addi a0, a0, 1 *)
  set (regs3 := regupd regs2 10 (r + nat_to_word (S i))).
  assert (E4 : RiscvSemantics.step target_segs (mkst regs2 0x1001224 memI' trom)
               = MachineOk (mkst regs3 0x1001228 memI' trom)).
  { rewrite (step_addi_at target_segs regs2 0x1001224 memI' trom _ 10 10 _
               (r + nat_to_word (S i)) TF_1001224 eq_refl TD_1001224 eq_refl).
    - wlits. reflexivity.
    - unfold regs3, regs2, regs1. getr_resolve. rewrite Hr10.
      apply word_add_nat_1. }
  (* addi s0, s0, 1 *)
  set (regs4 := regupd regs3 8 (ptrA + nat_to_word (S i))).
  assert (E5 : RiscvSemantics.step target_segs (mkst regs3 0x1001228 memI' trom)
               = MachineOk (mkst regs4 0x100122c memI' trom)).
  { rewrite (step_addi_at target_segs regs3 0x1001228 memI' trom _ 8 8 _
               (ptrA + nat_to_word (S i)) TF_1001228 eq_refl TD_1001228 eq_refl).
    - wlits. reflexivity.
    - unfold regs4, regs3, regs2, regs1. getr_resolve. rewrite Hr8.
      apply word_add_nat_1. }
  assert (HSi : (S i = tnn - d)%nat) by (rewrite Hie; lia).
  destruct (Nat.eqb_spec d 0) as [-> | Hdnz].
  - (* last iteration: bne falls through to 0x1001230 *)
    assert (E6 : RiscvSemantics.step target_segs (mkst regs4 0x100122c memI' trom)
                 = MachineOk (mkst regs4 0x1001230 memI' trom)).
    { rewrite (step_bne_ft target_segs regs4 0x100122c memI' trom _ 13 0 _
                 TF_100122c eq_refl TD_100122c).
      - wlits. reflexivity.
      - unfold regs4, regs3, regs2. getr_resolve. regupd_resolve.
        exact c_eq_0_true. }
    exists regs4. split; [|split; [|split; [|split]]].
    + intros x H8 H10 H13 H14. unfold regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs4. rewrite regupd_same. rewrite HSi, Nat.sub_0_r.
      unfold tnN. reflexivity.
    + unfold regs4. rewrite regupd_other by reg_neq_tac.
      unfold regs3. rewrite regupd_same. rewrite HSi, Nat.sub_0_r.
      unfold tnN. reflexivity.
    + unfold regs4. rewrite regupd_other by reg_neq_tac.
      unfold regs3. rewrite regupd_other by reg_neq_tac.
      unfold regs2. rewrite regupd_same. reflexivity.
    + replace (wbytes mem0 r targ1) with memI'.
      2:{ unfold memI'. rewrite HSi, Nat.sub_0_r.
          rewrite firstn_all2 by lia. reflexivity. }
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      apply mst_refl.
  - (* more iterations: bne taken back to 0x1001218 *)
    assert (E6 : RiscvSemantics.step target_segs (mkst regs4 0x100122c memI' trom)
                 = MachineOk (mkst regs4 0x1001218 memI' trom)).
    { rewrite (step_bne_tk target_segs regs4 0x100122c memI' trom _ 13 0 _
                 TF_100122c eq_refl TD_100122c).
      - wlits. reflexivity.
      - unfold regs4, regs3, regs2. getr_resolve. regupd_resolve.
        apply c_eq_0_false. rewrite u_ntw by lia. lia. }
    assert (Hr8' : reg_get regs4 8 = ptrA + nat_to_word (tnn - d)).
    { unfold regs4. rewrite regupd_same. rewrite HSi. reflexivity. }
    assert (Hr10' : reg_get regs4 10 = r + nat_to_word (tnn - d)).
    { unfold regs4. rewrite regupd_other by reg_neq_tac.
      unfold regs3. rewrite regupd_same. rewrite HSi. reflexivity. }
    assert (Hr13' : reg_get regs4 13 = nat_to_word d).
    { unfold regs4, regs3. rewrite !regupd_other by reg_neq_tac.
      unfold regs2. apply regupd_same. }
    destruct (IH regs4 ltac:(lia) ltac:(lia) Hr8' Hr10' Hr13')
      as (regs' & Hag & H8 & H10 & H13z & Hms).
    exists regs'. split; [|split; [|split; [|split]]].
    + intros x H8' H10' H13' H14'. rewrite (Hag x H8' H10' H13' H14').
      unfold regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + exact H8.
    + exact H10.
    + exact H13z.
    + replace (wbytes mem0 r (firstn (tnn - d) targ1)) with memI' in Hms.
      2:{ unfold memI'. rewrite HSi. reflexivity. }
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      exact Hms.
Qed.

(* ################################################################# *)
(* The write wrapper (musl-style): 0x10012f0 .. write .. ret          *)
(* ################################################################# *)

(** The put-style write-all retry loop at 0x1001310: register-only, so
    the memory and every register outside a0/a1/a2 carry through
    unchanged.  [blez a0]'s error arm is dead: every delivery is
    nonempty. *)
Lemma tgt_put_wall : forall (K : machine_state -> Prop) fuel
    (rest : list byte) (p RA : word) n regs mem,
  (length rest <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length rest)%nat ->
  (Z.of_nat (length rest) < 2^31)%Z ->
  (* [vfs_write]'s [access_ok] on the remaining buffer *)
  (bv_unsigned p + Z.of_nat (length rest) <= TASK_SIZE)%Z ->
  reg_get regs 1 = RA ->
  v_jalr RA 0 = RA ->
  reg_get regs 10 = len_word (firstn n rest) ->
  reg_get regs 11 = p ->
  reg_get regs 12 = len_word rest ->
  bv_unsigned (reg_get regs 17) = 64%Z ->
  reg_get regs 17 = Z_to_bv 64 64 ->
  rdn target_segs mem p (length rest) = Some rest ->
  (forall regs',
     (forall x : reg, x <> 10 -> x <> 11 -> x <> 12 -> x <> 17 ->
        reg_get regs' x = reg_get regs x) ->
     reg_get regs' 10 = Z_to_bv 64 0 ->
     K (mkst regs' RA mem trom)) ->
  to_wall_tail target_segs (Z_to_bv 64 1)
    (mkst regs (0x1001310 : word) mem trom) (skipn n rest) K.
Proof.
  intros K fuel. induction fuel as [|fuel IH];
    intros rest p RA n regs mem Hfuel Hn1 Hn2 Hlen Hacc
           H1 HRAj H10 H11 H12 H17 H17w Hread Hcont.
  { lia. }
  (* 0x1001310: blez a0 falls through (the delivery is nonempty) *)
  step_intro;
    [ reflexivity
    | eapply step_bge_ft;
      [ exact TF_1001310 | reflexivity | exact TD_1001310
      | getr_resolve; rewrite H10; apply c_lts_0_pos;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x1001314: add a1,a1,a0 *)
  stepiv TF_1001314 TD_1001314 (p + nat_to_word n)
    ltac:(getr_resolve; rewrite H11, H10; apply v_add_len_firstn; lia).
  (* 0x1001318: sub a2,a2,a0 *)
  stepiv TF_1001318 TD_1001318 (len_word (skipn n rest))
    ltac:(getr_resolve; rewrite H12, H10; apply v_sub_len_firstn; lia).
  destruct (Nat.eq_dec n (length rest)) as [-> | Hne].
  - (* full delivery: bnez not taken, return through [ret] *)
    rewrite skipn_all.
    step_intro;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact TF_100131c | reflexivity | exact TD_100131c
        | getr_resolve; apply c_eq_0_of_u; reflexivity ]
      | norm_pc ].
    (* 0x1001320: li a0,0 *)
    stepiv TF_1001320 TD_1001320 (Z_to_bv 64 0) ltac:(getr_resolve; bveq).
    (* 0x1001324: ret -> RA *)
    step_intro;
      [ reflexivity
      | eapply step_jalr_x0 with (tgt := RA);
        [ exact TF_1001324 | reflexivity | exact TD_1001324
        | getr_resolve; regupd_resolve; exact H1 ]
      | idtac ].
    imm_norm. rewrite HRAj.
    apply twt_done. apply Hcont.
    + intros x Hx10 Hx11 Hx12 Hx17.
      rewrite !regupd_other by assumption. reflexivity.
    + regupd_resolve. reflexivity.
  - (* short delivery: bnez taken, reissue on the remainder *)
    step_intro;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact TF_100131c | reflexivity | exact TD_100131c
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* 0x1001308: li a0,1 *)
    stepiv TF_1001308 TD_1001308 (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* 0x100130c: ecall -- the reissued write *)
    eapply twt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_100130c eq_refl) |].
    apply twt_more; [rewrite length_skipn; lia|].
    apply (twl_write_rec target_segs (Z_to_bv 64 1)).
    + getr_resolve; regupd_resolve; exact H17.
    + regupd_resolve; reflexivity.
    + match goal with
      | |- ms_read_bytes _ (reg_get ?R 11) (reg_get ?R 12) = Some _ =>
          replace (reg_get R 11) with (p + nat_to_word n)
            by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word (skipn n rest))
            by (regupd_resolve; reflexivity)
      end.
      rewrite (ms_read_bytes_rdn (run_segments target_segs inp asp amb)) by reflexivity;
        unfold run_segments; apply rdn_lift.
      cbn [ms_mem].
      replace (word_to_nat (len_word (skipn n rest)))
        with (length (skipn n rest))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      pose proof (rdn_skipn target_segs mem (length rest) p rest n Hread Hn2)
        as Hsk.
      rewrite length_skipn. exact Hsk.
    + (* [vfs_write]'s [access_ok] on the remaining range *)
      match goal with
      | |- access_okb (reg_get ?R 11) (bv_unsigned (reg_get ?R 12)) = true =>
          replace (reg_get R 11) with (p + nat_to_word n)
            by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word (skipn n rest))
            by (regupd_resolve; reflexivity)
      end.
      pose proof (u64_range p).
      apply Uaccess.access_okb_intro.
      rewrite u_len_word by (rewrite length_skipn; lia).
      rewrite word_add_nat, u_Z2bv by (unfold TASK_SIZE in Hacc; lia).
      rewrite length_skipn. lia.
    + rewrite length_skipn; lia.
    + intros m Hm1 Hm2.
      norm_pc.
      eapply (IH (skipn n rest) (p + nat_to_word n) RA m).
      * rewrite length_skipn; lia.
      * exact Hm1.
      * exact Hm2.
      * rewrite length_skipn; lia.
      * pose proof (u64_range p).
        rewrite length_skipn, word_add_nat.
        rewrite u_Z2bv by (unfold TASK_SIZE in Hacc; lia).
        lia.
      * regupd_resolve; exact H1.
      * exact HRAj.
      * regupd_resolve; reflexivity.
      * regupd_resolve; reflexivity.
      * regupd_resolve; reflexivity.
      * regupd_resolve; exact H17.
      * regupd_resolve; exact H17w.
      * pose proof (rdn_skipn target_segs mem (length rest) p rest n Hread Hn2)
          as Hsk.
        rewrite length_skipn. exact Hsk.
      * intros regs'' Hag H0.
        apply Hcont; [ | exact H0 ].
        intros x Hx10 Hx11 Hx12 Hx17.
        rewrite (Hag x Hx10 Hx11 Hx12 Hx17).
        rewrite !regupd_other by assumption. reflexivity.
Qed.

Lemma target_put : forall regs mem buf (ptr len RA : word) bufs (code : word),
  reg_get regs 1 = RA ->
  reg_get regs 10 = ptr ->
  reg_get regs 11 = len ->
  (0 < bv_unsigned len)%Z -> (bv_unsigned len < 2^31)%Z ->
  (* [vfs_write]'s [access_ok] on the buffer *)
  (bv_unsigned ptr + bv_unsigned len <= TASK_SIZE)%Z ->
  v_jalr RA 0 = RA ->
  rdn target_segs mem ptr (word_to_nat len) = Some buf ->
  (forall regs',
     (forall x : reg, x <> 10 -> x <> 11 -> x <> 12 -> x <> 17 ->
        reg_get regs' x = reg_get regs x) ->
     reg_get regs' 10 = Z_to_bv 64 0 ->
     to_wallexit target_segs (Z_to_bv 64 1) bufs code (mkst regs' RA mem trom)) ->
  to_wallexit target_segs (Z_to_bv 64 1) (buf :: bufs) code
    (mkst regs 0x10012f8 mem trom).
Proof.
  intros regs mem buf ptr len RA bufs code H1 H10 H11 Hlen0 Hlen31 Hacc HRAj Hread Hcont.
  pose proof (rdn_length _ _ _ _ _ Hread) as Hbl.
  pose proof (u64_range len) as Hul.
  pose proof (u64_range ptr) as Hup.
  assert (HbufL : Z.of_nat (length buf) = bv_unsigned len)
    by (rewrite Hbl; unfold word_to_nat; rewrite Z2Nat.id by lia; reflexivity).
  assert (Hlw : len_word buf = len)
    by (unfold len_word; rewrite HbufL; apply bv_eq; rewrite u_Z2bv by lia; reflexivity).
  split; [lia|].
  (* mv a2, a1 : a2 = len *)
  eapply twt_step;
    [ reflexivity
    | eapply step_addi_at with (v := len);
      [ exact TF_10012f8 | reflexivity | exact TD_10012f8 | reflexivity
      | getr_resolve; rewrite H11; apply v_addi_0 ]
    | step_simpl ].
  (* mv a1, a0 : a1 = ptr *)
  eapply twt_step;
    [ reflexivity
    | eapply step_addi_at with (v := ptr);
      [ exact TF_10012fc | reflexivity | exact TD_10012fc | reflexivity
      | getr_resolve; regupd_resolve; rewrite H10; apply v_addi_0 ]
    | step_simpl ].
  (* li a7, 64 *)
  eapply twt_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 64);
      [ exact TF_1001300 | reflexivity | exact TD_1001300 | reflexivity
      | getr_resolve; bveq ]
    | step_simpl ].
  (* beq a2, x0 fall-through (len <> 0) *)
  eapply twt_step;
    [ reflexivity
    | eapply step_beq_ft;
      [ exact TF_1001304 | reflexivity | exact TD_1001304
      | getr_resolve; regupd_resolve; apply c_eq_0_false; lia ]
    | step_simpl ].
  (* li a0, 1 *)
  eapply twt_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 1);
      [ exact TF_1001308 | reflexivity | exact TD_1001308 | reflexivity
      | getr_resolve; bveq ]
    | step_simpl ].
  (* ecall : write(1, ptr, len) *)
  eapply twt_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ TF_100130c eq_refl) | ].
  apply twt_more; [lia|].
  apply (twl_write_rec target_segs (Z_to_bv 64 1)).
  - getr_resolve. vm_compute. reflexivity.
  - regupd_resolve. reflexivity.
  - rewrite (ms_read_bytes_rdn (run_segments target_segs inp asp amb)) by reflexivity;
      unfold run_segments; apply rdn_lift.
    cbn [ms_mem ms_regs]. regupd_resolve.
    exact Hread.
  - (* [vfs_write]'s [access_ok] on the buffer *)
    cbn [ms_regs]. regupd_resolve. rewrite ?H10, ?H11.
    apply Uaccess.access_okb_intro. exact Hacc.
  - lia.
  - (* the put-style retry loop, per delivered length *)
    intros n Hn1 Hn2.
    norm_pc.
    eapply (tgt_put_wall _ (length buf) buf ptr RA n).
    + lia.
    + exact Hn1.
    + exact Hn2.
    + lia.
    + rewrite HbufL. exact Hacc.
    + regupd_resolve; exact H1.
    + exact HRAj.
    + regupd_resolve; reflexivity.
    + regupd_resolve; reflexivity.
    + regupd_resolve; symmetry; exact Hlw.
    + regupd_resolve; vm_compute; reflexivity.
    + regupd_resolve; bveq.
    + rewrite Hbl. exact Hread.
    + intros regs' Hag H0.
      apply Hcont; [ | exact H0 ].
      intros x Hx10 Hx11 Hx12 Hx17.
      rewrite (Hag x Hx10 Hx11 Hx12 Hx17).
      rewrite !regupd_other by assumption. reflexivity.
Qed.

(* ################################################################# *)
(* The byte-sum loops: inner (0x100122c) and outer (0x1001220)        *)
(* ################################################################# *)

Lemma sumb_firstn_bound : forall k, (sumb (firstn k targ1) <= 255 * Z.of_nat tnn)%Z.
Proof.
  intro k.
  assert (Hle : (sumb (firstn k targ1) <= sumb targ1)%Z).
  { rewrite <- (firstn_skipn k targ1) at 2. rewrite sumb_app.
    pose proof (sumb_nonneg (skipn k targ1)). lia. }
  pose proof (sumb_le targ1 targ1_bytes) as Hb. unfold tnn. lia.
Qed.

Lemma target_sum_inner : forall memC (r : word) total,
  (forall i, (i < total)%nat ->
     rdn target_segs memC (r + nat_to_word i) 1 = Some [nth i targ1 (Z_to_bv 8 0)]) ->
  (bv_unsigned r + Z.of_nat total < 2^64)%Z ->
  forall c s regs,
  (1 <= c)%nat -> (s + c <= total)%nat ->
  reg_get regs 10 = Z_to_bv 64 (sumb (firstn s targ1)) ->
  reg_get regs 14 = nat_to_word c ->
  reg_get regs 15 = r + nat_to_word s ->
  exists regs',
    (forall x : reg, x <> 10 -> x <> 14 -> x <> 15 -> x <> 16 ->
       reg_get regs' x = reg_get regs x) /\
    reg_get regs' 10 = Z_to_bv 64 (sumb (firstn (s + c) targ1)) /\
    reg_get regs' 15 = r + nat_to_word (s + c) /\
    msteps target_segs (mkst regs 0x1001244 memC trom)
                       (mkst regs' 0x1001258 memC trom).
Proof.
  intros memC r total Hbyte Hrw.
  pose proof tnN_le as HnnLe. pose proof targ1_bytes as Hbytes.
  pose proof (u64_range r) as Hur.
  assert (Hnn : tnn = length targ1) by reflexivity.
  induction c as [|c IH]; intros s regs Hc1 Hsc Hacc H14 H15; [lia|].
  set (byi := nth s targ1 (Z_to_bv 8 0)).
  assert (Hs : (s < total)%nat) by lia.
  assert (Hb256 : (bv_unsigned byi < 256)%Z) by apply u8_range.
  assert (Haccbnd : (sumb (firstn s targ1) <= 255 * Z.of_nat tnn)%Z) by apply sumb_firstn_bound.
  assert (Haccnn : (0 <= sumb (firstn s targ1))%Z) by apply sumb_nonneg.
  assert (Hus : bv_unsigned (r + nat_to_word s) = (bv_unsigned r + Z.of_nat s)%Z)
    by (rewrite u_add_small; rewrite u_ntw by lia; lia).
  (* lbu a6, 0(a5) *)
  set (regs1 := regupd regs 16 (Z_to_bv 64 (bv_unsigned byi))).
  assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001244 memC trom)
               = MachineOk (mkst regs1 0x1001248 memC trom)).
  { rewrite (step_lbu target_segs regs 0x1001244 memC trom _ 16 15 _ byi
               TF_1001244 eq_refl TD_1001244).
    - reduce_bv_eqb_ifs. wlits. reflexivity.
    - getr_resolve. rewrite H15. rewrite v_addi_0.
      apply (Hbyte s Hs). }
  (* addi a4, a4, -1 : a4 = c *)
  set (regs2 := regupd regs1 14 (nat_to_word c)).
  assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x1001248 memC trom)
               = MachineOk (mkst regs2 0x100124c memC trom)).
  { rewrite (step_addi_at target_segs regs1 0x1001248 memC trom _ 14 14 _
               (nat_to_word c) TF_1001248 eq_refl TD_1001248 eq_refl).
    - wlits. reflexivity.
    - unfold regs2, regs1. getr_resolve. rewrite H14.
      apply v_addi_natS_m1. }
  (* add a0, a0, a6 : a0 = acc + byte *)
  set (regs3 := regupd regs2 10 (Z_to_bv 64 (sumb (firstn (S s) targ1)))).
  assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x100124c memC trom)
               = MachineOk (mkst regs3 0x1001250 memC trom)).
  { rewrite (step_add_at target_segs regs2 0x100124c memC trom _ 10 10 16
               (Z_to_bv 64 (sumb (firstn (S s) targ1))) TF_100124c eq_refl TD_100124c eq_refl).
    - wlits. reflexivity.
    - unfold regs3, regs2, regs1. getr_resolve. rewrite Hacc.
      pose proof (u8_range byi) as Hbr.
      apply bv_eq. rewrite v_add_small.
      + rewrite (sumb_firstn_S_default targ1 s).
        fold byi. rewrite !u_Z2bv by lia. reflexivity.
      + rewrite !u_Z2bv by lia. lia. }
  (* addi a5, a5, 1 : a5 = r + s + 1 *)
  set (regs4 := regupd regs3 15 (r + nat_to_word (S s))).
  assert (E4 : RiscvSemantics.step target_segs (mkst regs3 0x1001250 memC trom)
               = MachineOk (mkst regs4 0x1001254 memC trom)).
  { rewrite (step_addi_at target_segs regs3 0x1001250 memC trom _ 15 15 _
               (r + nat_to_word (S s)) TF_1001250 eq_refl TD_1001250 eq_refl).
    - wlits. reflexivity.
    - unfold regs4, regs3, regs2, regs1. getr_resolve. rewrite H15.
      apply word_add_nat_1. }
  destruct (Nat.eqb_spec c 0) as [-> | Hcnz].
  - (* last inner iteration: bne falls through to 0x1001258 *)
    assert (E5 : RiscvSemantics.step target_segs (mkst regs4 0x1001254 memC trom)
                 = MachineOk (mkst regs4 0x1001258 memC trom)).
    { rewrite (step_bne_ft target_segs regs4 0x1001254 memC trom _ 14 0 _
                 TF_1001254 eq_refl TD_1001254).
      - wlits. reflexivity.
      - unfold regs4, regs3, regs2. getr_resolve. regupd_resolve.
        exact c_eq_0_true. }
    exists regs4. split; [|split; [|split]].
    + intros x H10 H14' H15' H16. unfold regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs4. rewrite regupd_other by reg_neq_tac.
      unfold regs3. rewrite regupd_same.
      rewrite Nat.add_1_r. reflexivity.
    + unfold regs4. rewrite regupd_same. rewrite Nat.add_1_r. reflexivity.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      apply mst_refl.
  - (* more inner iterations: bne taken back to 0x1001244 *)
    assert (E5 : RiscvSemantics.step target_segs (mkst regs4 0x1001254 memC trom)
                 = MachineOk (mkst regs4 0x1001244 memC trom)).
    { rewrite (step_bne_tk target_segs regs4 0x1001254 memC trom _ 14 0 _
                 TF_1001254 eq_refl TD_1001254).
      - wlits. reflexivity.
      - unfold regs4, regs3, regs2. getr_resolve. regupd_resolve.
        apply c_eq_0_false. rewrite u_ntw by lia. lia. }
    assert (Hacc' : reg_get regs4 10 = Z_to_bv 64 (sumb (firstn (S s) targ1))).
    { unfold regs4. rewrite regupd_other by reg_neq_tac.
      unfold regs3. apply regupd_same. }
    assert (H14' : reg_get regs4 14 = nat_to_word c).
    { unfold regs4, regs3. rewrite !regupd_other by reg_neq_tac.
      unfold regs2. apply regupd_same. }
    assert (H15' : reg_get regs4 15 = r + nat_to_word (S s)).
    { unfold regs4. apply regupd_same. }
    destruct (IH (S s) regs4 ltac:(lia) ltac:(lia) Hacc' H14' H15')
      as (regs' & Hag & H10r & H15r & Hms).
    exists regs'. split; [|split; [|split]].
    + intros x H10 H14'' H15'' H16. rewrite (Hag x H10 H14'' H15'' H16).
      unfold regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + rewrite H10r. replace (S s + c)%nat with (s + S c)%nat by lia. reflexivity.
    + rewrite H15r. replace (S s + c)%nat with (s + S c)%nat by lia. reflexivity.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      exact Hms.
Qed.

Lemma target_sum : forall memC (r : word) total,
  (forall i, (i < total)%nat ->
     rdn target_segs memC (r + nat_to_word i) 1 = Some [nth i targ1 (Z_to_bv 8 0)]) ->
  (bv_unsigned r + Z.of_nat total < 2^64)%Z ->
  forall m s regs,
  (1 <= m)%nat ->
  (s + 8 * (m - 1) < tnn <= s + 8 * m)%nat ->
  (s + 8 * m = total)%nat ->
  reg_get regs 10 = Z_to_bv 64 (sumb (firstn s targ1)) ->
  reg_get regs 11 = tnN ->
  reg_get regs 12 = r + nat_to_word s ->
  reg_get regs 13 = nat_to_word s ->
  exists regs',
    (forall x : reg, x <> 10 -> x <> 12 -> x <> 13 -> x <> 14 -> x <> 15 -> x <> 16 ->
       reg_get regs' x = reg_get regs x) /\
    reg_get regs' 10 = Z_to_bv 64 (sumb targ1) /\
    msteps target_segs (mkst regs 0x1001238 memC trom)
                       (mkst regs' 0x1001264 memC trom).
Proof.
  intros memC r total Hbyte Hrw.
  pose proof tnN_le as HnnLe.
  pose proof (u64_range r) as Hur.
  induction m as [|m IH]; intros s regs Hm1 Hstop Htotal Hacc H11 H12 H13; [lia|].
  assert (Hs8 : (s + 8 <= total)%nat) by lia.
  assert (Hus : bv_unsigned (r + nat_to_word s) = (bv_unsigned r + Z.of_nat s)%Z)
    by (rewrite u_add_small; rewrite u_ntw by lia; lia).
  (* addi a4, 0, 8 *)
  set (regs1 := regupd regs 14 (Z_to_bv 64 8)).
  assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001238 memC trom)
               = MachineOk (mkst regs1 0x100123c memC trom)).
  { rewrite (step_addi_at target_segs regs 0x1001238 memC trom _ 14 0 _
               (Z_to_bv 64 8) TF_1001238 eq_refl TD_1001238 eq_refl).
    - wlits. reflexivity.
    - getr_resolve. bveq. }
  (* addi a5, a2, 0 : a5 = r + s *)
  set (regs2 := regupd regs1 15 (r + nat_to_word s)).
  assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x100123c memC trom)
               = MachineOk (mkst regs2 0x1001240 memC trom)).
  { rewrite (step_addi_at target_segs regs1 0x100123c memC trom _ 15 12 _
               (r + nat_to_word s) TF_100123c eq_refl TD_100123c eq_refl).
    - wlits. reflexivity.
    - unfold regs2, regs1. getr_resolve. rewrite H12. apply v_addi_0. }
  (* beq a4, x0 fall-through (a4 = 8 <> 0) *)
  assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x1001240 memC trom)
               = MachineOk (mkst regs2 0x1001244 memC trom)).
  { rewrite (step_beq_ft target_segs regs2 0x1001240 memC trom _ 14 0 _
               TF_1001240 eq_refl TD_1001240).
    - wlits. reflexivity.
    - unfold regs2, regs1. getr_resolve. regupd_resolve.
      apply c_eq_0_false. vm_compute. discriminate. }
  (* the inner loop, 8 iterations from start index s *)
  assert (Hi2_10 : reg_get regs2 10 = Z_to_bv 64 (sumb (firstn s targ1))).
  { unfold regs2, regs1. regupd_resolve. exact Hacc. }
  assert (Hi2_14 : reg_get regs2 14 = nat_to_word 8).
  { unfold regs2. rewrite regupd_other by reg_neq_tac.
    unfold regs1. rewrite regupd_same. reflexivity. }
  assert (Hi2_15 : reg_get regs2 15 = r + nat_to_word s).
  { unfold regs2. apply regupd_same. }
  destruct (target_sum_inner memC r total Hbyte Hrw 8 s regs2
              ltac:(lia) ltac:(lia) Hi2_10 Hi2_14 Hi2_15)
    as (regsI & HagI & H10I & H15I & HmsI).
  (* addi a3, a3, 8 : a3 = s + 8 *)
  set (regs4 := regupd regsI 13 (nat_to_word (s + 8))).
  assert (E4 : RiscvSemantics.step target_segs (mkst regsI 0x1001258 memC trom)
               = MachineOk (mkst regs4 0x100125c memC trom)).
  { rewrite (step_addi_at target_segs regsI 0x1001258 memC trom _ 13 13 _
               (nat_to_word (s + 8)) TF_1001258 eq_refl TD_1001258 eq_refl).
    - wlits. reflexivity.
    - getr_resolve. rewrite (HagI 13) by reg_neq_tac.
      assert (H13' : reg_get regs2 13 = nat_to_word s).
      { unfold regs2, regs1. regupd_resolve. exact H13. }
      rewrite H13'. imm_norm.
      rewrite v_addi_nneg_t by (rewrite ?u_ntw by lia; lia).
      rewrite u_ntw by lia.
      unfold nat_to_word. f_equal. lia. }
  (* addi a2, a2, 8 : a2 = r + s + 8 *)
  set (regs5 := regupd regs4 12 (r + nat_to_word (s + 8))).
  assert (E5 : RiscvSemantics.step target_segs (mkst regs4 0x100125c memC trom)
               = MachineOk (mkst regs5 0x1001260 memC trom)).
  { rewrite (step_addi_at target_segs regs4 0x100125c memC trom _ 12 12 _
               (r + nat_to_word (s + 8)) TF_100125c eq_refl TD_100125c eq_refl).
    - wlits. reflexivity.
    - unfold regs4. getr_resolve. regupd_resolve.
      rewrite (HagI 12) by reg_neq_tac.
      assert (H12' : reg_get regs2 12 = r + nat_to_word s).
      { unfold regs2, regs1. regupd_resolve. exact H12. }
      rewrite H12'. rewrite !word_add_nat. imm_norm.
      rewrite v_addi_nneg_t by (rewrite ?u_Z2bv by lia; lia).
      rewrite u_Z2bv by lia. f_equal. lia. }
  assert (Hr2_11 : reg_get regs2 11 = tnN).
  { unfold regs2, regs1. regupd_resolve. exact H11. }
  assert (Hr5_10 : reg_get regs5 10 = Z_to_bv 64 (sumb (firstn (s + 8) targ1))).
  { unfold regs5, regs4. rewrite !regupd_other by reg_neq_tac. exact H10I. }
  assert (Hr5_11 : reg_get regs5 11 = tnN).
  { unfold regs5, regs4. rewrite !regupd_other by reg_neq_tac.
    rewrite (HagI 11) by reg_neq_tac. exact Hr2_11. }
  assert (Hr5_12 : reg_get regs5 12 = r + nat_to_word (s + 8)).
  { unfold regs5. apply regupd_same. }
  assert (Hr5_13 : reg_get regs5 13 = nat_to_word (s + 8)).
  { unfold regs5. rewrite regupd_other by reg_neq_tac.
    unfold regs4. apply regupd_same. }
  destruct (Nat.eqb_spec m 0) as [-> | Hmnz].
  - (* last chunk: bltu falls through to 0x1001264 *)
    assert (E6 : RiscvSemantics.step target_segs (mkst regs5 0x1001260 memC trom)
                 = MachineOk (mkst regs5 0x1001264 memC trom)).
    { rewrite (step_bltu_ft target_segs regs5 0x1001260 memC trom _ 13 11 _
                 TF_1001260 eq_refl TD_1001260).
      - wlits. reflexivity.
      - getr_resolve. rewrite Hr5_13, Hr5_11.
        rewrite c_ltu_ltb. apply Z.ltb_ge.
        rewrite u_tnN. rewrite u_ntw by lia. lia. }
    exists regs5. split; [|split].
    + intros x H10 H12' H13' H14' H15' H16.
      unfold regs5, regs4. rewrite !regupd_other by assumption.
      rewrite (HagI x) by assumption.
      unfold regs2, regs1. rewrite !regupd_other by assumption. reflexivity.
    + rewrite Hr5_10.
      rewrite firstn_all2 by (unfold tnn in Hstop; lia). reflexivity.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply msteps_trans; [exact HmsI |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      apply mst_refl.
  - (* more chunks: bltu taken back to 0x1001238 *)
    assert (E6 : RiscvSemantics.step target_segs (mkst regs5 0x1001260 memC trom)
                 = MachineOk (mkst regs5 0x1001238 memC trom)).
    { rewrite (step_bltu_tk target_segs regs5 0x1001260 memC trom _ 13 11 _
                 TF_1001260 eq_refl TD_1001260).
      - wlits. reflexivity.
      - getr_resolve. rewrite Hr5_13, Hr5_11.
        rewrite c_ltu_ltb. apply Z.ltb_lt.
        rewrite u_tnN. rewrite u_ntw by lia. lia. }
    destruct (IH (s + 8)%nat regs5 ltac:(lia) ltac:(lia) ltac:(lia)
                Hr5_10 Hr5_11 Hr5_12 Hr5_13)
      as (regs' & Hag & H10' & Hms).
    exists regs'. split; [|split].
    + intros x H10 H12' H13' H14' H15' H16.
      rewrite (Hag x H10 H12' H13' H14' H15' H16).
      unfold regs5, regs4. rewrite !regupd_other by assumption.
      rewrite (HagI x) by assumption.
      unfold regs2, regs1. rewrite !regupd_other by assumption. reflexivity.
    + exact H10'.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply msteps_trans; [exact HmsI |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      exact Hms.
Qed.

End Ge2MainT.

End TargetProof.
