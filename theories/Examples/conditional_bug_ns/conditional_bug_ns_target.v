(** * conditional-bug-ns TARGET binary (Zig ReleaseSmall).

    PROOF-SIDE FILE (not part of the trusted specification).

    Delivers the four [to_wexit] derivations of the target binary:

      - [target_wexit_lt2]   : argc < 2            -> no output, exit 2
      - [target_wexit_n]     : argv[1][0] = 'n'    -> no output, exit 0
      - [target_wexit_h]     : argv[1][0] = 'h'    -> "hello\n", exit 0
      - [target_wexit_other] : any other first byte (not 'n'/'h'/'o')
                                                   -> no output, exit 3

    The 'o' arm is NOT analyzed: on those inputs the SOURCE follows a
    deterministic instruction path to error, so [Equivalence.equiv]'s
    all-executions-error escape frees the target.

    STEPPING.  Every instruction is executed by [Common/SymTac.v]'s
    reflective [sym_block]; the binary is freestanding (raw [ecall]
    syscall wrappers, no musl blob), so the only tactic residue is the
    two [ecall] nodes, the image reads and the store legality.

    The run reads [Run.run_segments] (the image's segments, then the vDSO
    pair): each derivation steps over [target_segs ++ vt] with the pair an
    abstract tail [vt]; the stack bounds come from the entry predicate's
    launch conjunct [Run.entry_launch_ok_va] and [Run.valid_launch]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim WallSim StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Common Require Import Footprint SymExec SymTac SymBranch SymSide.
From LinuxProcessSemantics.Examples.conditional_bug_ns Require Import conditional_bug_ns_code conditional_bug_ns_defs.
From LinuxProcessSemantics.Examples.conditional_bug_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.conditional_bug_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them. *)
#[local] Instance conditional_bug_ns_target_fx : FPState := fx0.

Section TargetProof.

Variable inp : ProcInput.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hvl : valid_launch inp.

(** The initial stack pointer, the program break and the mmap base are
    QUANTIFIED (ASLR): the whole section is generic over them. *)
Variable asp abrk amb : word.

(** The target run's own draw, independent of the source's (the
    [ed_random] and [ed_top] halves of [Run.ExecEntry]'s [en_draw]; see
    the source file). *)
Variable arnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned asp)%Z.
Hypothesis Hsp_hi : (bv_unsigned asp <= sp_window_hi)%Z.

(** The launch conjunct of [Run.valid_entry_va]; see the source file. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry asp abrk amb arnd) inp.

Lemma asp_lo_num : (0x7fff80000000 <= bv_unsigned asp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma asp_hi_num : (bv_unsigned asp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Definition aargcN : word := len_word (in_argv inp).

Lemma u_aargcN : bv_unsigned aargcN = Z.of_nat (length (in_argv inp)).
Proof.
  pose proof (valid_argv_len (in_argv inp) Hva).
  unfold aargcN, len_word. apply u_Z2bv; lia.
Qed.

(** No-overflow bound for the initial stack image (feeds the stack-read
    lemmas' side conditions), for any entry word the auxv carries. *)
Lemma target_bsb_nw : forall entry : word,
  (bv_unsigned asp
   + Z.of_nat (length (entry_stack_image inp amb target_phdrs entry asp arnd)) < 2^64)%Z.
Proof.
  intros entry.
  pose proof (bsb_bound Sv48 inp amb target_phdrs entry asp abrk arnd Hvl Hlau).
  pose proof asp_hi_num. lia.
Qed.

(** The argv[1] string pointer. *)
Definition aptr1 : word :=
  cat_argv_ptr (ed_top arnd) (in_argv inp) (in_envp inp) (in_execfn inp) 1.

Lemma aptr1_bounds : (2 <= length (in_argv inp))%nat ->
  (bv_unsigned asp <= bv_unsigned aptr1)%Z /\
  (bv_unsigned aptr1 + Z.of_nat (length (nth 1 (in_argv inp) [])) + 1 < 2^64)%Z.
Proof.
  intro H. unfold aptr1.
  exact (argv_ptr_bounds Sv48 inp amb asp abrk arnd 1 Hlau ltac:(lia)).
Qed.

(** argv pointer 1 at [asp + 16]. *)
Lemma aread_ptr1 : forall segs entry, (2 <= length (in_argv inp))%nat ->
  rdn segs (stack_to_mem asp (entry_stack_image inp amb target_phdrs entry asp arnd))
      (asp + nat_to_word (8 + 8 * 1)) 8%nat
  = Some (word_le8 aptr1).
Proof.
  intros segs entry H. unfold aptr1.
  apply read_argv_ptr_k; [lia | apply target_bsb_nw].
Qed.

(** The first byte of argv[1] (its NUL if the string is empty). *)
Lemma aread_b : forall segs entry, (2 <= length (in_argv inp))%nat ->
  rdn segs (stack_to_mem asp (entry_stack_image inp amb target_phdrs entry asp arnd)) aptr1 1%nat
  = Some [byte_at (nth 1 (in_argv inp) []) 0].
Proof.
  intros segs entry H. unfold aptr1, byte_at.
  rewrite <- (word_add_0 (cat_argv_ptr (ed_top arnd) (in_argv inp) (in_envp inp)
                            (in_execfn inp) 1)).
  apply (read_argv_byte_k Sv48 segs inp amb target_phdrs entry asp abrk arnd 1 0 Hlau);
    lia.
Qed.

(** The dispatched byte, zero-extended into a machine word: the value
    the [lbu] at 0x100119c leaves in a0, named for the executor. *)
Definition abval : word := Z_to_bv 64 (bv_unsigned (byte_at (nth 1 (in_argv inp) []) 0)).

Lemma u_abval : bv_unsigned abval = bv_unsigned (byte_at (nth 1 (in_argv inp) []) 0).
Proof.
  unfold abval. pose proof (u8_range (byte_at (nth 1 (in_argv inp) []) 0)).
  apply u_Z2bv; lia.
Qed.

(* ================================================================= *)
(* The prologue's image obligations, shared by all four paths.        *)
(* ================================================================= *)

(** Note that the executor states its [SCReadBase]/[SCStoreOk]
    obligations against the ORIGINAL memory (the store log is lifted
    monotonically), so unlike the per-instruction route these reads need
    no [rdn_wbytes_disjoint] peeling of the two frame spills. *)

Ltac tb_read_argc :=
  replace (Z_to_bv 64 (bv_unsigned asp + 0)) with asp by (apply bv_eq; u_norm; lia);
  exists (word_le8 aargcN); split;
    [ rewrite rdn_wrap_stack_above by lia; apply read_argc; apply target_bsb_nw
    | apply bytes_le_n_to_le_8 ].

Ltac tb_read_ptr1 Hge2 :=
  replace (Z_to_bv 64 (bv_unsigned asp + 16)) with (asp + nat_to_word (8 + 8 * 1))
    by (rewrite word_add_nat; f_equal; cbn [Z.of_nat Nat.add Nat.mul]; lia);
  exists (word_le8 aptr1); split;
    [ rewrite rdn_wrap_stack_above by (rewrite ?word_add_nat; u_norm; lia);
      apply aread_ptr1; exact Hge2
    | apply bytes_le_n_to_le_8 ].

Ltac tb_read_byte Hge2 :=
  replace (Z_to_bv 64 (bv_unsigned aptr1 + 0)) with aptr1 by (apply bv_eq; u_norm; lia);
  exists [byte_at (nth 1 (in_argv inp) []) 0]; split;
    [ rewrite rdn_wrap_stack_above by lia; apply aread_b; exact Hge2
    | cbn [bytes_le_to_Z]; rewrite Z.shiftl_0_l, Z.lor_0_r; symmetry; exact u_abval ].

(** The [bltu a2,a0] at 0x100118c, in both directions. *)
Ltac tb_argc_br :=
  rewrite bv_ltu_Z;
  first [ apply Z.ltb_ge | apply Z.ltb_lt ]; u_norm; rewrite u_aargcN; lia.

(* ================================================================= *)
(* argc < 2: exit 2, no output.                                       *)
(* ================================================================= *)

Lemma target_wexit_lt2 : (length (in_argv inp) < 2)%nat ->
  to_wexit (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) 0x1001160 target_phdrs
       asp amb arnd inp)
    [] (Z_to_bv 64 2).
Proof.
  intros Hlt2.
  unfold run_segments.
  generalize (vdso_segments (in_kernel inp) asp amb) as vt. intros vt.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargc.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  rewrite init_mkst. norm_pc.
  (* The frame push, the two spills, the argc load, the [jalr] into the
     dispatcher, the [bltu] falling through and the exit tail --
     THIRTEEN instructions, one block, stopping at the [ecall]. *)
  sym_block (target_segs ++ vt) 20%nat [false] (@nil expr)
    [((2 : reg), EVar 32)] [asp] [aargcN] RA HRA.
  { (* [bltu a2,a0] falls through: argc <= 1 *) tb_argc_br. }
  { (* [ld a0,0(s0)] -> argc, out of the initial stack image *) tb_read_argc. }
  { (* [sd s0,0(sp)] *) solve_store_ok. }
  { (* [sd ra,8(sp)] *) solve_store_ok. }
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ (fetch_word_app _ _ _ _ TF_1001184) eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRA; sym_close.
  - sym_regs HRA; sym_close.
  - u_norm; lia.
Qed.

Optimize Heap.

(* ================================================================= *)
(* argv[1][0] = 'n': exit 0, no output.                               *)
(* ================================================================= *)

Lemma target_wexit_n : (2 <= length (in_argv inp))%nat ->
  byte_at (nth 1 (in_argv inp) []) 0 = Z_to_bv 8 110 ->
  to_wexit (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) 0x1001160 target_phdrs
       asp amb arnd inp)
    [] (Z_to_bv 64 0).
Proof.
  intros Hge2 Hb.
  unfold run_segments.
  generalize (vdso_segments (in_kernel inp) asp amb) as vt. intros vt.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargc.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  destruct (aptr1_bounds Hge2) as [Hp1 Hp2].
  rewrite init_mkst. norm_pc.
  sym_block (target_segs ++ vt) 25%nat [true; false; true] (@nil expr)
    [((2 : reg), EVar 32)] [asp] [aargcN; aptr1; abval] RA HRA.
  { (* [beq a0,a1] taken at 0x10011ac: the byte is 'n' *)
    unfold abval; rewrite Hb; vm_compute; reflexivity. }
  { (* [beq a0,a1] falls through at 0x10011a4: 'n' is not 'o' *)
    unfold abval; rewrite Hb; vm_compute; reflexivity. }
  { (* [lbu a0,0(a0)] -> the first byte of argv[1] *) tb_read_byte Hge2. }
  { (* [ld a0,8(a1)] -> the argv[1] pointer *) tb_read_ptr1 Hge2. }
  { (* [bltu a2,a0] taken: argc >= 2 *) tb_argc_br. }
  { (* [ld a0,0(s0)] -> argc *) tb_read_argc. }
  { solve_store_ok. }
  { solve_store_ok. }
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ (fetch_word_app _ _ _ _ TF_1001184) eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRA; sym_close.
  - sym_regs HRA; sym_close.
  - u_norm; lia.
Qed.

Optimize Heap.

(* ================================================================= *)
(* Any other first byte (not 'n'/'h'/'o'): exit 3, no output.         *)
(* ================================================================= *)

Lemma target_wexit_other : (2 <= length (in_argv inp))%nat ->
  byte_at (nth 1 (in_argv inp) []) 0 <> Z_to_bv 8 110 ->
  byte_at (nth 1 (in_argv inp) []) 0 <> Z_to_bv 8 104 ->
  byte_at (nth 1 (in_argv inp) []) 0 <> Z_to_bv 8 111 ->
  to_wexit (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) 0x1001160 target_phdrs
       asp amb arnd inp)
    [] (Z_to_bv 64 3).
Proof.
  intros Hge2 Hn110 Hn104 Hn111.
  unfold run_segments.
  generalize (vdso_segments (in_kernel inp) asp amb) as vt. intros vt.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargc.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  destruct (aptr1_bounds Hge2) as [Hp1 Hp2].
  rewrite init_mkst. norm_pc.
  sym_block (target_segs ++ vt) 25%nat [true; false; false; true] (@nil expr)
    [((2 : reg), EVar 32)] [asp] [aargcN; aptr1; abval] RA HRA.
  { (* [bne a0,a1] taken at 0x10011b4: the byte is not 'h' *)
    rewrite negb_true_iff; unfold abval;
    apply c_eq_zext_lit_false; [lia | exact Hn104]. }
  { (* [beq a0,a1] falls through at 0x10011ac: not 'n' *)
    unfold abval; apply c_eq_zext_lit_false; [lia | exact Hn110]. }
  { (* [beq a0,a1] falls through at 0x10011a4: not 'o' *)
    unfold abval; apply c_eq_zext_lit_false; [lia | exact Hn111]. }
  { tb_read_byte Hge2. }
  { tb_read_ptr1 Hge2. }
  { tb_argc_br. }
  { tb_read_argc. }
  { solve_store_ok. }
  { solve_store_ok. }
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ (fetch_word_app _ _ _ _ TF_1001184) eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRA; sym_close.
  - sym_regs HRA; sym_close.
  - u_norm; lia.
Qed.

Optimize Heap.

(* ================================================================= *)
(* argv[1][0] = 'h': write "hello\n", exit 0.                          *)
(* ================================================================= *)

(** The put-style retry loop after a (possibly short) write delivery:
    from the post-write state at 0x10011d4 — a0 = the delivered length
    [len_word (firstn n rest)], a1 = the offered pointer [p], a2 = the
    offered count — the loop runs [blez a0] (fall-through, the error
    arm is dead for n >= 1), bumps the pointer, decrements the count,
    and either exits the loop ([beqz a2] taken, full delivery) into the
    exit-0 tail, or reissues the write on the remainder.  Induction on
    [fuel >= length rest]; the remainder strictly shrinks because every
    delivery is nonempty.  Over the run's list [target_segs ++ vt]. *)
Lemma tgt_put_wall : forall vt fuel (rest : list byte) (p : word) n regs mem,
  (length rest <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length rest)%nat ->
  (Z.of_nat (length rest) <= 6)%Z ->
  (0x1000158 <= bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) <= 0x100015e)%Z ->
  reg_get regs 10 = len_word (firstn n rest) ->
  reg_get regs 11 = p ->
  reg_get regs 12 = len_word rest ->
  reg_get regs 1 = (0x1001180 : word) ->
  bv_unsigned (reg_get regs 17) = 64%Z ->
  rdn (target_segs ++ vt) mem p (length rest) = Some rest ->
  to_wall_tail (target_segs ++ vt) (Z_to_bv 64 1)
    (mkst regs (0x10011d4 : word) mem (seg_rom (target_segs ++ vt)))
    (skipn n rest)
    (to_wallexit (target_segs ++ vt) (Z_to_bv 64 1) [] (Z_to_bv 64 0)).
Proof.
  intros vt fuel.
  induction fuel as [|fuel IH];
    intros rest p n regs mem Hfuel Hn1 Hn2 Hlen Hplo Hphi
           H10 H11 H12 H1 H17 Hread.
  { lia. }
  destruct (Nat.eq_dec n (length rest)) as [-> | Hne].
  - (* full delivery: blez ft; add; sub; beqz TAKEN -> the exit tail *)
    rewrite skipn_all.
    apply twt_done. cbn [to_wallexit].
    (* blez a0 falls through *)
    step_intro;
      [ reflexivity
      | eapply step_bge_ft;
        [ exact (fetch_word_app _ _ _ _ TF_10011d4) | reflexivity | exact TD_10011d4
        | getr_resolve; rewrite H10; apply c_lts_0_pos;
          rewrite u_len_word_firstn by lia; lia ]
      | norm_pc ].
    (* add a1,a1,a0 ; sub a2,a2,a0 *)
    stepi (fetch_word_app _ vt _ _ TF_10011d8) TD_10011d8.
    stepi (fetch_word_app _ vt _ _ TF_10011dc) TD_10011dc.
    (* beqz a2 taken: to the loop exit at 0x10011ec *)
    step_intro;
      [ reflexivity
      | eapply step_beq_tk;
        [ exact (fetch_word_app _ _ _ _ TF_10011e0) | reflexivity | exact TD_10011e0
        | getr_resolve; rewrite H12, H10; apply c_eq_0_of_u;
          rewrite v_sub_len_firstn by lia;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* li a0,0 *)
    stepiv (fetch_word_app _ vt _ _ TF_10011ec) TD_10011ec (Z_to_bv 64 0) ltac:(getr_resolve; bveq).
    (* ret -> 0x1001180 *)
    stepjr (fetch_word_app _ vt _ _ TF_10011f0) TD_10011f0 (0x1001180 : word)
      ltac:(getr_resolve; exact H1).
    (* li a7,93 *)
    stepiv (fetch_word_app _ vt _ _ TF_1001180) TD_1001180 (Z_to_bv 64 93) ltac:(getr_resolve; bveq).
    (* the exit ecall *)
    eapply tw_step;
      [ reflexivity | apply (step_ecall _ _ _ _ _ _ (fetch_word_app _ _ _ _ TF_1001184) eq_refl) | ].
    apply tw_exit_coden.
    + getr_resolve; reflexivity.
    + regupd_resolve; reflexivity.
    + vm_compute; reflexivity.
  - (* short delivery: blez ft; add; sub; beqz ft; j; li a0,1; reissue *)
    step_intro;
      [ reflexivity
      | eapply step_bge_ft;
        [ exact (fetch_word_app _ _ _ _ TF_10011d4) | reflexivity | exact TD_10011d4
        | getr_resolve; rewrite H10; apply c_lts_0_pos;
          rewrite u_len_word_firstn by lia; lia ]
      | norm_pc ].
    (* add a1,a1,a0: the pointer bump *)
    stepiv (fetch_word_app _ vt _ _ TF_10011d8) TD_10011d8 (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
      ltac:(getr_resolve; rewrite H11, H10; apply v_add_len_firstn_Z; lia).
    (* sub a2,a2,a0: the count decrement *)
    stepiv (fetch_word_app _ vt _ _ TF_10011dc) TD_10011dc (len_word (skipn n rest))
      ltac:(getr_resolve; rewrite H12, H10; apply v_sub_len_firstn; lia).
    (* beqz a2 falls through (remainder nonempty) *)
    step_intro;
      [ reflexivity
      | eapply step_beq_ft;
        [ exact (fetch_word_app _ _ _ _ TF_10011e0) | reflexivity | exact TD_10011e0
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* j 0x10011cc *)
    stepj (fetch_word_app _ vt _ _ TF_10011e4) TD_10011e4.
    (* li a0,1 *)
    stepiv (fetch_word_app _ vt _ _ TF_10011cc) TD_10011cc (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* ecall: the reissued write *)
    eapply twt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (fetch_word_app _ _ _ _ TF_10011d0) eq_refl) |].
    apply twt_more; [rewrite length_skipn; lia|].
    apply (twl_write_rec (target_segs ++ vt) (Z_to_bv 64 1)).
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
      rewrite (ms_read_bytes_rdn (target_segs ++ vt)) by reflexivity.
      cbn [ms_mem].
      replace (word_to_nat (len_word (skipn n rest)))
        with (length (skipn n rest))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      pose proof (rdn_skipn (target_segs ++ vt) mem (length rest) p rest n Hread Hn2)
        as Hsk.
      rewrite word_add_nat_Z in Hsk by lia.
      rewrite length_skipn. exact Hsk.
    + (* the remainder's range passes [access_ok]: inside .rodata *)
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
      * regupd_resolve; exact H17.
      * pose proof (rdn_skipn (target_segs ++ vt) mem (length rest) p rest n Hread Hn2)
          as Hsk.
        rewrite word_add_nat_Z in Hsk by lia.
        rewrite length_skipn. exact Hsk.
Qed.

Lemma target_wexit_h : (2 <= length (in_argv inp))%nat ->
  byte_at (nth 1 (in_argv inp) []) 0 = Z_to_bv 8 104 ->
  to_wallexit (run_segments target_segs inp asp amb) (Z_to_bv 64 1) [hello] (Z_to_bv 64 0)
    (init_machine_state (run_segments target_segs inp asp amb) 0x1001160 target_phdrs
       asp amb arnd inp).
Proof.
  intros Hge2 Hb.
  unfold run_segments.
  generalize (vdso_segments (in_kernel inp) asp amb) as vt. intros vt.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargc.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  destruct (aptr1_bounds Hge2) as [Hp1 Hp2].
  split; [cbn; lia|].
  rewrite init_mkst. norm_pc.
  (* TWENTY-FOUR instructions in ONE block: the frame push, the whole
     three-way dispatch falling through to the 'h' arm, the write
     argument setup and the not-taken zero-length test, stopping at the
     write [ecall] at 0x10011d0. *)
  sym_block (target_segs ++ vt) 30%nat [true; false; false; false; false] (@nil expr)
    [((2 : reg), EVar 32)] [asp] [aargcN; aptr1; abval] RA HRA.
  (* the [beqz a2] at 0x10011c8 compares two literals, so [sym_block]
     discharges its [SCBr] itself and no goal for it appears below. *)
  { (* [bne a0,a1] falls through at 0x10011b4: the byte IS 'h' *)
    rewrite negb_false_iff; unfold abval; rewrite Hb; vm_compute; reflexivity. }
  { (* [beq a0,a1] falls through at 0x10011ac: 'h' is not 'n' *)
    unfold abval; rewrite Hb; vm_compute; reflexivity. }
  { (* [beq a0,a1] falls through at 0x10011a4: 'h' is not 'o' *)
    unfold abval; rewrite Hb; vm_compute; reflexivity. }
  { tb_read_byte Hge2. }
  { tb_read_ptr1 Hge2. }
  { tb_argc_br. }
  { tb_read_argc. }
  { solve_store_ok. }
  { solve_store_ok. }
  (* ---------------- the write [ecall] at 0x10011d0 ---------------- *)
  (* The block's exit register file is the write [ecall]'s argument
     vector; read the four values it is about to be observed through
     ONCE, with [sym_regs], instead of re-resolving them per goal. *)
  assert (Ha0 : getr RA 10 = Z_to_bv 64 1) by (sym_regs HRA; sym_close).
  assert (Ha1 : getr RA 11 = (0x1000158 : word)) by (sym_regs HRA; sym_close).
  assert (Ha2 : getr RA 12 = Z_to_bv 64 6) by (sym_regs HRA; sym_close).
  assert (Ha7 : getr RA 17 = Z_to_bv 64 64) by (sym_regs HRA; sym_close).
  assert (Hra : getr RA 1 = (0x1001180 : word)) by (sym_regs HRA; sym_close).
  eapply twt_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ (fetch_word_app _ _ _ _ TF_10011d0) eq_refl) | ].
  apply twt_more; [cbn; lia|].
  apply (twl_write_rec (target_segs ++ vt) (Z_to_bv 64 1)).
  - rewrite Ha7. vm_compute. reflexivity.
  - exact Ha0.
  - rewrite (ms_read_bytes_rdn (target_segs ++ vt)) by reflexivity.
    cbn [ms_mem ms_regs].
    change (reg_get RA 11) with (getr RA 11);
    change (reg_get RA 12) with (getr RA 12); rewrite Ha1, Ha2.
    replace (word_to_nat (Z_to_bv 64 6)) with 6%nat by (vm_compute; reflexivity).
    rewrite !rdn_wbytes_below
      by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
    erewrite rdn_ext;
      [ apply arom_hello
      | imm_norm; lia
      | intros x Hx; revert Hx; imm_norm; intros Hx;
        eapply wrap_mem_below; [exact Hlau | rewrite stack_max_size_val; lia] ].
  - (* the string's range passes [access_ok]: a link-time address *)
    change (reg_get RA 11) with (getr RA 11);
    change (reg_get RA 12) with (getr RA 12); rewrite Ha1, Ha2.
    vm_compute; reflexivity.
  - cbn; lia.
  - (* the write-all retry loop, per delivered length *)
    intros n Hn1 Hn2.
    norm_pc.
    apply (tgt_put_wall vt (length hello) hello (0x1000158 : word) n).
    + lia.
    + exact Hn1.
    + exact Hn2.
    + cbn; lia.
    + assert (Hu : bv_unsigned (0x1000158 : word) = 0x1000158%Z)
        by (vm_compute; reflexivity).
      rewrite Hu; lia.
    + assert (Hu : bv_unsigned (0x1000158 : word) = 0x1000158%Z)
        by (vm_compute; reflexivity).
      rewrite Hu; cbn; lia.
    + regupd_resolve; reflexivity.
    + regupd_resolve; exact Ha1.
    + regupd_resolve; change (reg_get RA 12) with (getr RA 12);
      rewrite Ha2; bveq.
    + regupd_resolve; exact Hra.
    + regupd_resolve; change (reg_get RA 17) with (getr RA 17);
      rewrite Ha7; vm_compute; reflexivity.
    + change (length hello) with 6%nat.
      rewrite !rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
      erewrite rdn_ext;
        [ apply arom_hello
        | imm_norm; lia
        | intros x Hx; revert Hx; imm_norm; intros Hx;
          eapply wrap_mem_below; [exact Hlau | rewrite stack_max_size_val; lia] ].
Qed.

End TargetProof.
