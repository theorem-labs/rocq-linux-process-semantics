(** * brk-rev-ns source binary: per-binary derivations.

    PROOF-SIDE FILE (not part of the trusted specification).

    Deliverables (Section [SourceProof], generic over the input and the
    ASLR placement):
    - [source_wexit_lt2]  : argc < 2            -> to_wexit [] 2
    - [source_wexit_cap]  : argc >= 2, n > 65536 -> to_wexit [] 3
    - [source_outcomes]   : argc >= 2, n <= 65536 ->
        to_outcomes (init) (init_model) (brkU (rev_buf argv[1])).

    Register invariants are [reg_get regs r = v] with sp-relative values
    in the canonical [Z_to_bv 64 (bv_unsigned rsp - k)] form, loop
    indices as [nat_to_word], counters/bounds in [Z].

    NOTE (compile flags): the reference sources are built with
    [-fno-builtin], so gcc 15 no longer recognizes the program's [slen]
    as the strlen idiom -- the binary keeps the hand-written byte-scan
    loop inline in main (0x1102c..0x11034 / 0x11090..0x11094) and musl's
    word-at-a-time [strlen] is gone from the image.  The walk is a plain
    per-byte induction ([source_scan]); no read ever goes past the
    terminating NUL.

    The run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  The derivations step over the image's own segments and the
    three deliverables carry them to the run's list
    ([RunSegmentsLift.to_wexit_run], [msteps_run], [to_wallexit_run]):
    no instruction here fetches from the pair.  The machine states carry
    the run's read-only backing [seg_rom (run_segments ...)], as
    [PropExec.init_mkst] gives it.  The stack bounds come from the entry
    predicate's launch conjunct [Run.entry_launch_ok_va] and
    [Run.valid_launch]; the brk ledger is the run's
    ([State.init_reserved]: the image's reservations and the vDSO pair). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec WallSim AllocSim StepTac StreamSim StoreOk Footprint SymExec SymTac SymBranch SymSide RunSegmentsLift.
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
#[local] Instance brk_rev_ns_source_fx : FPState := fx0.

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x11134%N.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Reserved list and store legality                                   *)
(* ================================================================= *)

Lemma source_reserved_val :
  segments_reserved source_segs
  = [(0x10000, 0x1000); (0x11000, 0x1000); (0x12000, 0x1000); (0x13000, 0x1000)].
Proof.
  apply (proj1 (listNN_eqb_eq _ _)). vm_compute. reflexivity.
Qed.

(** Stores at/above the data segment's base are legal.  [-z separate-code]
    plus gcc 15's own [.eh_frame] LOAD give the image THREE read-only
    segments ([0x10000] headers/rodata, [0x11000] text, [0x12000]
    eh_frame) below the writable one at [0x13000]; the generic
    [range_avoids_ro_above] is keyed off that single bound, so the proof
    does not name the segments. *)
Lemma source_avoids_stack : forall (a : word) (n : Z),
  (0x13000 <= bv_unsigned a)%Z ->
  range_avoids_ro_segs source_segs (bv_unsigned a) n = true.
Proof.
  intros a n Ha.
  apply range_avoids_ro_above with (data_base := 0x13000%Z);
    [vm_compute; reflexivity | exact Ha].
Qed.

(** The source image's WRITABLE window: the rw- segment covers
    [0x13000, 0x14000) and the snapshot carries a byte for every
    address in it (.bss is zero-filled in the .hex), so [wview] is
    defined there whatever the overlay holds — a store into .data/.bss
    needs no prior write.  That is the [store_ok] side condition
    machine stores now carry; stack targets go through the RLIMIT_STACK
    window ([solve_store_ok]) and heap targets through the grant's
    zero-fill ([store_ok_zmem]). *)
Lemma source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma source_store_ok : forall (m : word -> option byte) (a : word) (n : nat),
  (0x13000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x14000)%Z ->
  store_ok source_segs m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply store_ok_window with (base := 0x13000%Z) (hi := 0x14000%Z);
    [ | | | exact source_data_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.

(** The mirror image of [range_avoids_ro_above]: a range that ENDS at or
    below every read-only segment's base avoids them all. *)
Lemma range_avoids_ro_below : forall (segs : list Segment) (top addr n : Z),
  forallb (fun seg => seg_writable seg
                      || Z.leb top (Z.of_N (seg_base seg))) segs = true ->
  (addr + n <= top)%Z ->
  range_avoids_ro_segs segs addr n = true.
Proof.
  intros segs top addr n Habove Hr.
  unfold range_avoids_ro_segs. rewrite forallb_forall in *.
  intros seg Hin. specialize (Habove seg Hin).
  destruct (seg_writable seg) eqn:W; cbn [orb] in *; [reflexivity|].
  apply Z.leb_le in Habove.
  apply negb_true_iff. apply andb_false_iff. left.
  apply Z.ltb_ge. lia.
Qed.

(** A region [b, b+l) free against the page-rounded reservations avoids
    the read-only segments everywhere inside it: freedom against all FOUR
    page reservations forces the region entirely below 0x10000 or at/above
    0x14000. *)
Lemma source_free_avoids : forall (b l : word),
  region_free (segments_reserved source_segs) b l = true ->
  (0 < bv_unsigned l)%Z ->
  forall (a : word) (k : Z),
  (bv_unsigned b <= bv_unsigned a)%Z ->
  (bv_unsigned a + k <= bv_unsigned b + bv_unsigned l)%Z ->
  range_avoids_ro_segs source_segs (bv_unsigned a) k = true.
Proof.
  intros b l Hfree Hl a k Hlo Hhi.
  rewrite source_reserved_val in Hfree.
  cbn [region_free] in Hfree.
  apply andb_true_iff in Hfree as [H0 Hfree].
  apply andb_true_iff in Hfree as [H1 Hfree].
  apply andb_true_iff in Hfree as [H2 Hfree].
  apply andb_true_iff in Hfree as [H3 _].
  apply negb_true_iff in H0. apply negb_true_iff in H1.
  apply negb_true_iff in H2. apply negb_true_iff in H3.
  unfold iv_overlap in H0, H1, H2, H3.
  apply andb_false_iff in H0. apply andb_false_iff in H1.
  apply andb_false_iff in H2. apply andb_false_iff in H3.
  change (bv_unsigned (0x10000 : word)) with 0x10000%Z in H0.
  change (bv_unsigned (0x11000 : word)) with 0x11000%Z in H1.
  change (bv_unsigned (0x12000 : word)) with 0x12000%Z in H2.
  change (bv_unsigned (0x13000 : word)) with 0x13000%Z in H3.
  change (bv_unsigned (0x1000 : word)) with 0x1000%Z in H0, H1, H2, H3.
  assert (Hcase : (bv_unsigned b + bv_unsigned l <= 0x10000
                   \/ 0x14000 <= bv_unsigned b)%Z).
  { destruct H0 as [H0|H0]; destruct H1 as [H1|H1];
      destruct H2 as [H2|H2]; destruct H3 as [H3|H3];
      apply Z.ltb_ge in H0; apply Z.ltb_ge in H1;
      apply Z.ltb_ge in H2; apply Z.ltb_ge in H3; lia. }
  destruct Hcase as [Hc | Hc].
  - apply (range_avoids_ro_below source_segs 0x10000%Z);
      [vm_compute; reflexivity | lia].
  - apply source_avoids_stack. lia.
Qed.

(* ================================================================= *)
(* The proof, generic over argv/envp and the stack pointer             *)
(* ================================================================= *)

Section SourceProof.

Variable inp : ProcInput.
Local Abbreviation av := (in_argv inp).
Local Abbreviation ev := (in_envp inp).
Hypothesis Hva : valid_argv av.
Hypothesis Hvl : valid_launch inp.

(** The initial stack pointer, the program break and the mmap base are
    QUANTIFIED (ASLR). *)
Variable rsp rbrk rmb : word.

(** The entry stack draw this run was started with
    ([Run.ExecEntry]'s [en_draw]): the 16 AT_RANDOM bytes the kernel
    picks afresh at every [execve], and the stack VMA's end
    [StackLayout.ed_top].  This proof may assume NOTHING about either
    beyond the launch conjunct below, exactly as it may assume nothing
    about where the stack landed.  Quantified per binary, so the target's
    draw is a different variable. *)
Variable rrnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned rsp)%Z.
Hypothesis Hsp_hi : (bv_unsigned rsp <= sp_window_hi)%Z.

(** The fifth conjunct of [Run.valid_entry_va]: this placement is one a
    Linux launch can give ([create_elf_tables] and [setup_arg_pages],
    fs/binfmt_elf.c and fs/exec.c, Linux v6.18.46, commit
    1f99e9ab748f).  With [Hvl] it bounds the entry block
    ([StepTac.bsb_bound]), places argv ([SeqExec.argv_ptr_bounds]) and
    places the stack-store window ([StoreOk.store_ok_wrap_window_valid]). *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry rsp rbrk rmb rrnd) inp.

(** The run's segment list, and its read-only backing as
    [PropExec.init_mkst] gives it. *)
Local Abbreviation RS := (run_segments source_segs inp rsp rmb).
Definition rrom : word -> option byte := seg_rom (run_segments source_segs inp rsp rmb).

Lemma rsp_lo_num : (0x7fff80000000 <= bv_unsigned rsp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma rsp_hi_num : (bv_unsigned rsp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

(** The quantified initial program break ([Run.valid_brk] window, like the
    SP above).  Its page alignment exposes the kernel's physical [brk]
    grant while the binary continues to use only its logical byte prefix. *)
Hypothesis Hbrk_lo :
  (reserved_top (segments_reserved source_segs) <= bv_unsigned rbrk)%Z.
Hypothesis Hbrk_hi :
  (bv_unsigned rbrk
   <= reserved_top (segments_reserved source_segs) + brk_aslr_max)%Z.

Lemma rtop_src_val : reserved_top (segments_reserved source_segs) = 0x14000%Z.
Proof. rewrite source_reserved_val. reflexivity. Qed.
Lemma rbrk_lo_num : (0x14000 <= bv_unsigned rbrk)%Z.
Proof. rewrite <- rtop_src_val. exact Hbrk_lo. Qed.
Lemma rbrk_hi_num : (bv_unsigned rbrk <= 0x14000 + 1073741824)%Z.
Proof. rewrite <- rtop_src_val, <- brk_aslr_max_val. exact Hbrk_hi. Qed.
Lemma rbrk_lt64 : (bv_unsigned rbrk < 2^64)%Z.
Proof.
  pose proof rbrk_hi_num. change (2^64)%Z with 18446744073709551616%Z. lia.
Qed.

Definition argcN : word := len_word av.
Definition wmem : word -> option byte :=
  wrap_mem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x11134)) rsp rrnd.

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
Proof.
  pose proof (valid_argv_len av Hva).
  unfold argcN, len_word. apply u_Z2bv; lia.
Qed.

(** No-overflow bound for the initial stack image (feeds the stack-read
    lemmas' side conditions). *)
Lemma source_bsb_nw : forall entry : word,
  (bv_unsigned rsp
   + Z.of_nat (length (entry_stack_image inp rmb source_phdrs entry rsp rrnd)) < 2^64)%Z.
Proof.
  intros entry.
  pose proof (bsb_bound Sv48 inp rmb source_phdrs entry rsp rbrk rrnd Hvl Hlau).
  pose proof rsp_hi_num. lia.
Qed.

(** environ pointer _start stores at 0x13000. *)
Definition envp_val : word :=
  Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat (length av) + 8).

Lemma envp_val_eq :
  v_addi (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli argcN 3)) 8 = envp_val.
Proof.
  pose proof rsp_hi_num. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as Hlen.
  apply bv_eq. unfold envp_val, v_addi.
  rewrite !Z_to_bv_unsigned.
  rewrite v_add_small
    by (rewrite u_Z2bv by lia; rewrite v_slli_3 by (rewrite u_argcN; lia);
        rewrite u_argcN; lia).
  rewrite u_Z2bv by lia.
  rewrite v_slli_3 by (rewrite u_argcN; lia).
  rewrite u_argcN.
  f_equal; lia.
Qed.

(** The executor's spelling of the same value: the log denotes the
    [slli]/[add]/[addi] chain with [alu64] and the REGISTER shift
    [v_sll _ (Z_to_bv 64 3)], not the [v_add]/[v_slli] of [envp_val_eq]. *)
Lemma envp_val_sym :
  Z_to_bv 64 (bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
                                         (v_sll argcN (Z_to_bv 64 3))) + 8)
  = envp_val.
Proof.
  rewrite alu_add.
  replace (v_sll argcN (Z_to_bv 64 3)) with (v_slli argcN 3) by reflexivity.
  exact envp_val_eq.
Qed.

(** Memory after _start's environ store. *)
Definition emem : word -> option byte :=
  wbytes wmem (0x13000 : word) (word_to_le_bytes 8 envp_val).

(** main()'s 64-byte frame (stores in execution order; sp = rsp - 64):
    s1@+40, ra@+56 (= 0x11160), s0@+48, s2@+32, s3@+24, s4@+16.  gcc 15
    keeps six callee-saves live across the inline scan loop, and uses +8
    (rsp-56) as a SCRATCH spill slot for the running pointer; +0 is never
    touched.  All stored callee-saves are 0 in the initial register file. *)
Definition fmem : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes emem
    (Z_to_bv 64 (bv_unsigned rsp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 8))  (word_to_le_bytes 8 (0x11160 : word)))
    (Z_to_bv 64 (bv_unsigned rsp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 48)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

Lemma grows_fmem : mem_grows wmem fmem.
Proof.
  unfold fmem, emem.
  repeat (eapply mem_grows_trans; [ | apply wbytes_grows ]).
  apply mem_grows_refl.
Qed.

Lemma rdn_emem_above : forall (a : word) n,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn source_segs emem a n = rdn source_segs wmem a n.
Proof.
  intros a n Ha Hn. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. unfold emem.
  rewrite rdn_wbytes_disjoint
    by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
  reflexivity.
Qed.

Lemma rdn_fmem_above : forall (a : word) n,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn source_segs fmem a n = rdn source_segs wmem a n.
Proof.
  intros a n Ha Hn. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. unfold fmem.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia)).
  apply rdn_emem_above; assumption.
Qed.

Lemma rdn_wmem_stack : forall (a : word) n,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn source_segs wmem a n
  = rdn source_segs (stack_to_mem rsp (entry_stack_image inp rmb source_phdrs
                                         (Z_to_bv 64 (Z.of_N 0x11134)) rsp rrnd)) a n.
Proof. intros a n Ha Hn. apply rdn_wrap_stack_above; assumption. Qed.

(** argc at rsp (read at program entry, memory = wmem). *)
Lemma read_argc_w :
  rdn source_segs wmem rsp 8%nat = Some (word_le8 argcN).
Proof.
  pose proof rsp_hi_num.
  rewrite rdn_wmem_stack by lia.
  apply read_argc. apply source_bsb_nw.
Qed.

(* ----------------------------------------------------------------- *)
(* argv[1] and its bytes                                              *)
(* ----------------------------------------------------------------- *)

Definition arg1 : list byte := nth 1 av [].
Definition nn : nat := length arg1.
Definition nN : word := nat_to_word nn.
Definition ptr : word := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1.

(* ----------------------------------------------------------------- *)
(* Frame-slot read-back                                               *)
(* ----------------------------------------------------------------- *)

Lemma read_slot_ra :
  rdn source_segs fmem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
  = Some (word_to_le_bytes 8 (0x11160 : word)).
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. unfold fmem.
  repeat first
    [ rewrite rdn_wbytes_hit8 by (u_norm; lia)
    | rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia)
    | rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia) ].
  reflexivity.
Qed.

Lemma read_slot_0 : forall a : word,
  In a [Z_to_bv 64 (bv_unsigned rsp - 16); Z_to_bv 64 (bv_unsigned rsp - 24);
        Z_to_bv 64 (bv_unsigned rsp - 32); Z_to_bv 64 (bv_unsigned rsp - 40);
        Z_to_bv 64 (bv_unsigned rsp - 48)] ->
  rdn source_segs fmem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros a Ha. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. unfold fmem.
  repeat destruct Ha as [<-|Ha];
    try (exfalso; exact Ha);
    repeat first
      [ rewrite rdn_wbytes_hit8 by (u_norm; lia)
      | rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia)
      | rewrite rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia) ];
    reflexivity.
Qed.

(* ================================================================= *)
(* Epilogue: 0x11070 .. ret .. exit ecall                             *)
(* ================================================================= *)

(** From main's epilogue with ANY memory whose frame slots read back
    the initial values: exit with code = a0, no output. *)
Lemma source_epilogue : forall regs mem code,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ->
  reg_get regs 10 = code -> (bv_unsigned code < 256)%Z ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
    = Some (word_to_le_bytes 8 (0x11160 : word)) ->
  (forall a : word,
     In a [Z_to_bv 64 (bv_unsigned rsp - 16); Z_to_bv 64 (bv_unsigned rsp - 24);
           Z_to_bv 64 (bv_unsigned rsp - 32); Z_to_bv 64 (bv_unsigned rsp - 40);
           Z_to_bv 64 (bv_unsigned rsp - 48)] ->
     rdn source_segs mem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  to_wexit source_segs (mkst regs 0x11070 mem rrom) [] code.
Proof.
  intros regs mem code H2 H10 Hc Hra Hsl.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi. pose proof stack_max_size_val as Hsms.
  (* 0x11070 .. 0x11160: the six callee-save reloads, the frame pop, the
     [ret] and the exit-number [li], reflectively.  The reloaded [ra] is
     NAMED [ELit 0x11160] in the read script, which is what lets the [ret]
     two instructions later resolve inside the same block. *)
  sym_block source_segs 12%nat (@nil bool) [ELit 0x11160]
    [((2 : reg), EVar 32); ((10 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp - 64); code]
    [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
     Z_to_bv 64 0]
    R HR.
  { (* ld s4, 16(sp) *)
    exists (word_to_le_bytes 8 (Z_to_bv 64 0)). split;
      [ replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 64)) + 16))
          with (Z_to_bv 64 (bv_unsigned rsp - 48)) by (u_norm; f_equal; lia);
        apply Hsl; right; right; right; right; left; reflexivity
      | exact (bytes_le_to_Z_8 _) ]. }
  { (* ld s3, 24(sp) *)
    exists (word_to_le_bytes 8 (Z_to_bv 64 0)). split;
      [ replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 64)) + 24))
          with (Z_to_bv 64 (bv_unsigned rsp - 40)) by (u_norm; f_equal; lia);
        apply Hsl; right; right; right; left; reflexivity
      | exact (bytes_le_to_Z_8 _) ]. }
  { (* ld s2, 32(sp) *)
    exists (word_to_le_bytes 8 (Z_to_bv 64 0)). split;
      [ replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 64)) + 32))
          with (Z_to_bv 64 (bv_unsigned rsp - 32)) by (u_norm; f_equal; lia);
        apply Hsl; right; right; left; reflexivity
      | exact (bytes_le_to_Z_8 _) ]. }
  { (* ld s1, 40(sp) *)
    exists (word_to_le_bytes 8 (Z_to_bv 64 0)). split;
      [ replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 64)) + 40))
          with (Z_to_bv 64 (bv_unsigned rsp - 24)) by (u_norm; f_equal; lia);
        apply Hsl; right; left; reflexivity
      | exact (bytes_le_to_Z_8 _) ]. }
  { (* ld s0, 48(sp) *)
    exists (word_to_le_bytes 8 (Z_to_bv 64 0)). split;
      [ replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 64)) + 48))
          with (Z_to_bv 64 (bv_unsigned rsp - 16)) by (u_norm; f_equal; lia);
        apply Hsl; left; reflexivity
      | exact (bytes_le_to_Z_8 _) ]. }
  { (* ld ra, 56(sp) *)
    exists (word_to_le_bytes 8 (0x11160 : word)). split;
      [ replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 64)) + 56))
          with (Z_to_bv 64 (bv_unsigned rsp - 8)) by (u_norm; f_equal; lia);
        exact Hra
      | exact (bytes_le_to_Z_8 _) ]. }
  { exact H2. }
  { exact H10. }
  (* 0x11164: ecall -- exit(code) *)
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_11164 eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HR. vm_compute. reflexivity.
  - sym_regs HR. sym_close.
  - exact Hc.
Qed.

(* ================================================================= *)
(* _start and main's prologue                                         *)
(* ================================================================= *)

(** argc < 2: no output, exit 2. *)
Lemma source_wexit_lt2 : (length av < 2)%nat ->
  to_wexit RS (init_machine_state RS 0x11134 source_phdrs rsp rmb rrnd inp)
    [] (Z_to_bv 64 2).
Proof.
  intros Hlt2. apply to_wexit_run.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as HargcLe.
  rewrite init_mkst. norm_pc.
  (* 0x11134 .. 0x11164: the whole run, in ONE block.  The crt prologue
     computes and stores [__environ], calls main, main's argc test is
     taken, and the [ret] out of main resolves because the [jal] linked
     [ra] inside the same block; the executor stops only at the [ecall]. *)
  match goal with
  | |- to_wexit _ (mkst ?R ?P _ _) ?B ?C =>
      change (to_wexit source_segs (mkst R P wmem rrom) B C)
  end.
  sym_block source_segs 20%nat [true] (@nil expr)
    [((2 : reg), EVar 32)] [rsp] [argcN] R HR.
  { (* 0x11004: bge a5, a0 IS taken -- 1 >= argc *)
    pose proof u_argcN. sym_br. }
  { (* 0x11158: sd a2, 0(t1) -- the [__environ] store *)
    unfold wmem; apply source_store_ok; u_norm; lia. }
  { (* 0x1113c: ld a0, 0(sp) -- argc, out of the initial stack image *)
    replace (Z_to_bv 64 (bv_unsigned rsp + 0)) with rsp
      by (apply bv_eq; u_norm; lia).
    exists (word_le8 argcN). split;
      [ apply read_argc_w | apply bytes_le_n_to_le_8 ]. }
  (* 0x11164: ecall -- exit(2) *)
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_11164 eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HR. vm_compute. reflexivity.
  - sym_regs HR. sym_close.
  - u_norm; lia.
Qed.

(* ================================================================= *)
(* argc >= 2                                                          *)
(* ================================================================= *)

Section Ge2Main.

Hypothesis Hge2 : (2 <= length av)%nat.

Lemma nN_le : (Z.of_nat nn <= 131071)%Z.
Proof.
  unfold nn, arg1. apply valid_argv_str_len; [exact Hva | lia].
Qed.

(** The one buffer this program ever writes -- argv[1] reversed plus a
    newline -- is short enough for the model to transfer in one [write]:
    [valid_argv] caps a single argv string at 131071 bytes, and
    131071 + 1 = [rw_bytes_max]. *)
Lemma bufs_modeled_out : bufs_modeled [rev_buf arg1].
Proof.
  pose proof nN_le as Hn.
  constructor; [| constructor].
  unfold buf_modeled, rw_bytes_max. rewrite length_rev_buf.
  unfold nn in Hn. lia.
Qed.

Lemma u_nN : bv_unsigned nN = Z.of_nat nn.
Proof. pose proof nN_le. unfold nN. apply u_ntw. lia. Qed.

Lemma u_nN1 : bv_unsigned (nN + 1) = (Z.of_nat nn + 1)%Z.
Proof.
  pose proof nN_le.
  rewrite u_add_small; rewrite ?u_nN;
    change (bv_unsigned (1 : word)) with 1%Z; lia.
Qed.

Lemma arg1_nz : ~ In (Z_to_bv 8 0) arg1.
Proof. unfold arg1. apply valid_argv_str_nz; [exact Hva | lia]. Qed.

Lemma ptr_bounds :
  (bv_unsigned rsp <= bv_unsigned ptr)%Z /\
  (bv_unsigned ptr + Z.of_nat nn + 1 < 2^64)%Z.
Proof.
  unfold ptr, nn, arg1.
  exact (argv_ptr_bounds Sv48 inp rmb rsp rbrk rrnd 1 Hlau ltac:(lia)).
Qed.

Lemma ptr_lo : (bv_unsigned rsp <= bv_unsigned ptr)%Z.
Proof. exact (proj1 ptr_bounds). Qed.
Lemma ptr_hi : (bv_unsigned ptr + Z.of_nat nn + 1 < 2^64)%Z.
Proof. exact (proj2 ptr_bounds). Qed.

(** argv[1] pointer slot at rsp + 16 (in the post-store memory). *)
Lemma read_ptr1_f :
  rdn source_segs fmem (rsp + nat_to_word (8 + 8 * 1)) 8%nat
  = Some (word_le8 ptr).
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva).
  rewrite rdn_fmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
  unfold ptr. apply read_argv_ptr_k; [lia | apply source_bsb_nw].
Qed.

(** The whole NUL-terminated string at ptr. *)
Lemma read_str_f :
  rdn source_segs fmem ptr (S nn) = Some (arg1 ++ [Z_to_bv 8 0]).
Proof.
  destruct ptr_bounds as [Hlo Hhi].
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  rewrite rdn_fmem_above by lia.
  rewrite rdn_wmem_stack by lia.
  replace (S nn) with (nn + 1)%nat by lia.
  apply rdn_app.
  - unfold ptr, arg1, nn.
    exact (read_argv_str_k Sv48 source_segs inp rmb source_phdrs _ rsp rbrk rrnd 1
             Hlau ltac:(lia)).
  - pose proof (read_argv_byte_k Sv48 source_segs inp rmb source_phdrs
                  (Z_to_bv 64 (Z.of_N 0x11134)) rsp rbrk rrnd 1 nn Hlau
                  ltac:(lia) ltac:(unfold nn, arg1; lia)) as Hbk.
    assert (Hb0 : nth nn (nth 1 av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)
                  = Z_to_bv 8 0).
    { change (nth nn (nth 1 av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))
        with (byte_at arg1 nn).
      unfold nn. apply byte_at_len. }
    rewrite Hb0 in Hbk. exact Hbk.
Qed.

(** Every byte of the string, including the terminating NUL. *)
Lemma read_byte_f : forall j, (j <= nn)%nat ->
  rdn source_segs fmem (ptr + nat_to_word j) 1%nat = Some [byte_at arg1 j].
Proof.
  intros j Hj. destruct ptr_bounds as [Hlo Hhi].
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le.
  rewrite rdn_fmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
  unfold ptr, byte_at, arg1.
  apply (read_argv_byte_k Sv48 source_segs inp rmb source_phdrs _ rsp rbrk rrnd 1 j Hlau);
    [lia | unfold nn, arg1 in Hj; lia].
Qed.

(* ================================================================= *)
(* The inline byte-scan loop: 0x1102c .. 0x11034 / 0x11090 .. 0x11094 *)
(* ================================================================= *)

(** The scan loop gcc 15 emits for the program's own [slen] under
    [-fno-builtin]:

      0x1102c  add  s2,s4,s1        s2 := ptr + i
      0x11030  lbu  a5,0(s2)
      0x11034  bnez a5,0x11090  ->  0x11090 addi s1,s1,1 ; 0x11094 j 0x1102c

    The index lives in s1 and the string base in s4, so falling through
    the [bnez] lands at 0x11038 with s1 = n and s2 = ptr + n. *)
Lemma source_scan : forall d i regs,
  (i + d = nn)%nat ->
  reg_get regs 9 = nat_to_word i ->
  reg_get regs 20 = ptr ->
  exists regs',
    (forall r : reg, r <> 9 -> r <> 15 -> r <> 18 ->
       reg_get regs' r = reg_get regs r) /\
    reg_get regs' 9 = nN /\
    reg_get regs' 18 = ptr + nN /\
    msteps source_segs (mkst regs 0x1102c fmem rrom) (mkst regs' 0x11038 fmem rrom).
Proof.
  pose proof arg1_nz as Hnz.
  induction d as [|d IH]; intros i regs Hid H9 H20.
  - (* the NUL: the branch falls through to 0x11038 *)
    assert (Hi : i = nn) by lia.
    set (regs1 := regupd regs 18 (ptr + nat_to_word i)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x1102c fmem rrom)
                 = MachineOk (mkst regs1 0x11030 fmem rrom)).
    { rewrite (step_add source_segs regs 0x1102c fmem rrom _ 18 20 9
                 SF_1102c eq_refl SD_1102c).
      reduce_bv_eqb_ifs.
      unfold regs1. getr_resolve. rewrite H20, H9. wlits. reflexivity. }
    set (regs2 := regupd regs1 15 (Z_to_bv 64 0)).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x11030 fmem rrom)
                 = MachineOk (mkst regs2 0x11034 fmem rrom)).
    { rewrite (step_lbu source_segs regs1 0x11030 fmem rrom _ 15 18 _ (Z_to_bv 8 0)
                 SF_11030 eq_refl SD_11030).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite v_addi_0.
        assert (Hb : byte_at arg1 i = Z_to_bv 8 0)
          by (rewrite Hi; unfold nn; apply byte_at_len).
        rewrite <- Hb. apply read_byte_f. lia. }
    assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x11034 fmem rrom)
                 = MachineOk (mkst regs2 0x11038 fmem rrom)).
    { rewrite (step_bne_ft source_segs regs2 0x11034 fmem rrom _ 15 0 _
                 SF_11034 eq_refl SD_11034).
      - wlits. reflexivity.
      - unfold regs2. getr_resolve. exact c_eq_0_true. }
    exists regs2. split; [|split; [|split]].
    + intros r Hr9 Hr15 Hr18. unfold regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs2, regs1. regupd_resolve. rewrite H9, Hi. reflexivity.
    + unfold regs2, regs1. regupd_resolve. rewrite Hi. reflexivity.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      apply mst_refl.
  - (* a nonzero byte: take the branch, bump s1, and come back *)
    assert (Hilt : (i < nn)%nat) by lia.
    set (b := byte_at arg1 i).
    assert (Hbnz : b <> Z_to_bv 8 0)
      by (apply byte_at_nz; [exact Hnz | unfold nn in Hilt; exact Hilt]).
    set (regs1 := regupd regs 18 (ptr + nat_to_word i)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x1102c fmem rrom)
                 = MachineOk (mkst regs1 0x11030 fmem rrom)).
    { rewrite (step_add source_segs regs 0x1102c fmem rrom _ 18 20 9
                 SF_1102c eq_refl SD_1102c).
      reduce_bv_eqb_ifs.
      unfold regs1. getr_resolve. rewrite H20, H9. wlits. reflexivity. }
    set (regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned b))).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x11030 fmem rrom)
                 = MachineOk (mkst regs2 0x11034 fmem rrom)).
    { rewrite (step_lbu source_segs regs1 0x11030 fmem rrom _ 15 18 _ b
                 SF_11030 eq_refl SD_11030).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite v_addi_0.
        apply read_byte_f. lia. }
    assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x11034 fmem rrom)
                 = MachineOk (mkst regs2 0x11090 fmem rrom)).
    { rewrite (step_bne_tk source_segs regs2 0x11034 fmem rrom _ 15 0 _
                 SF_11034 eq_refl SD_11034).
      - wlits. reflexivity.
      - unfold regs2. getr_resolve.
        apply c_eq_0_false. rewrite u_zext8. apply byte_nz_u. exact Hbnz. }
    set (regs3 := regupd regs2 9 (nat_to_word (S i))).
    assert (E4 : RiscvSemantics.step source_segs (mkst regs2 0x11090 fmem rrom)
                 = MachineOk (mkst regs3 0x11094 fmem rrom)).
    { rewrite (step_addi source_segs regs2 0x11090 fmem rrom _ 9 9 _
                 SF_11090 eq_refl SD_11090).
      reduce_bv_eqb_ifs.
      unfold regs3, regs2, regs1. getr_resolve. rewrite H9.
      imm_norm. rewrite nat_to_word_S. wlits. reflexivity. }
    assert (E5 : RiscvSemantics.step source_segs (mkst regs3 0x11094 fmem rrom)
                 = MachineOk (mkst regs3 0x1102c fmem rrom)).
    { rewrite (step_jal_x0 source_segs regs3 0x11094 fmem rrom _ _
                 SF_11094 eq_refl SD_11094).
      wlits. reflexivity. }
    assert (H9' : reg_get regs3 9 = nat_to_word (S i))
      by (unfold regs3; apply regupd_same).
    assert (H20' : reg_get regs3 20 = ptr).
    { unfold regs3, regs2, regs1. rewrite !regupd_other by discriminate.
      exact H20. }
    destruct (IH (S i) regs3 ltac:(lia) H9' H20')
      as (regs' & Hag & H9f & H18f & Hms).
    exists regs'. split; [|split; [|split]].
    + intros r Hr9 Hr15 Hr18. rewrite (Hag r Hr9 Hr15 Hr18).
      unfold regs3, regs2, regs1. rewrite !regupd_other by assumption.
      reflexivity.
    + exact H9f.
    + exact H18f.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      exact Hms.
Qed.

(* ================================================================= *)
(* main's prologue and the scan loop                                  *)
(* ================================================================= *)

(** From the entry point to the scan loop's head, with main's frame
    pushed, s1 = 0 and s4 = argv[1]. *)
Lemma source_to_loop :
  exists regsA,
    msteps source_segs
      (init_machine_state RS 0x11134 source_phdrs rsp rmb rrnd inp)
      (mkst regsA 0x1102c fmem rrom) /\
    reg_get regsA 2 = Z_to_bv 64 (bv_unsigned rsp - 64) /\
    reg_get regsA 9 = nat_to_word 0 /\
    reg_get regsA 20 = ptr.
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as HargcLe.
  pose proof ptr_lo as Hplo. pose proof ptr_hi as Hphi.
  pose proof nN_le as HnnLe.
  (* 0x11134 .. 0x11028: the crt prologue (including the [__environ]
     store), main's argc test (fall-through), main's whole 64-byte frame,
     the argv[1] load into s4 and the scan index's [li s1,0] -- ONE
     block.  [sym_block_ex] rather than [sym_block] because the
     statement's [exists regsA] has to be instantiated with the block's
     own exit register file.  The fuel is EXACT: one more step would
     walk into the scan loop. *)
  sym_block_ex source_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
          (Z_to_bv 64 0x11134) wmem rrom)
    22%nat [false] (@nil expr)
    [((2 : reg), EVar 32)] [rsp] [argcN; ptr] R HR Hms.
  { (* 0x11024: ld s4, 8(a1) -- the argv[1] pointer *)
    replace (Z_to_bv 64 (bv_unsigned rsp + 16)) with (rsp + nat_to_word (8 + 8 * 1))
      by (rewrite word_add_nat; f_equal; u_norm; lia).
    exists (word_le8 ptr). split;
      [ unfold wmem; rewrite rdn_wrap_stack_above
          by (rewrite word_add_nat; u_norm; lia);
        unfold ptr; apply read_argv_ptr_k; [lia | apply source_bsb_nw]
      | apply bytes_le_n_to_le_8 ]. }
  { (* 0x11020: sd s4, 16(sp) *) unfold wmem; solve_store_ok. }
  { (* 0x1101c: sd s3, 24(sp) *) unfold wmem; solve_store_ok. }
  { (* 0x11018: sd s2, 32(sp) *) unfold wmem; solve_store_ok. }
  { (* 0x11014: sd s0, 48(sp) *) unfold wmem; solve_store_ok. }
  { (* 0x11010: sd ra, 56(sp) *) unfold wmem; solve_store_ok. }
  { (* 0x1100c: sd s1, 40(sp) *) unfold wmem; solve_store_ok. }
  { (* 0x11004: bge a5, a0 falls through -- argc >= 2 *)
    pose proof u_argcN. sym_br. }
  { (* 0x11158: sd a2, 0(t1) -- the [__environ] store *)
    unfold wmem; apply source_store_ok; u_norm; lia. }
  { (* 0x1113c: ld a0, 0(sp) -- argc *)
    replace (Z_to_bv 64 (bv_unsigned rsp + 0)) with rsp
      by (apply bv_eq; u_norm; lia).
    exists (word_le8 argcN). split;
      [ apply read_argc_w | apply bytes_le_n_to_le_8 ]. }
  (* Put the block's exit memory into the [wbytes] spelling [fmem] names. *)
  match type of Hms with
  | msteps _ _ (mkst _ _ ?m _) =>
      replace m with fmem in Hms;
        [ | unfold fmem, emem; sym_mem_norm;
            getr_resolve; regupd_resolve; rewrite ?envp_val_sym; reflexivity ]
  end.
  exists R. split.
  { rewrite init_mkst.
    match goal with
    | |- msteps _ _ ?T =>
        change (msteps source_segs
                  (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
                        (Z_to_bv 64 0x11134) wmem rrom) T)
    end.
    sym_chain Hms. apply mst_refl. }
  repeat split; sym_regs HR; sym_close.
Qed.

(** From the entry point to 0x11038 with s1 = n, s2 = ptr + n and
    s4 = argv[1]. *)
Lemma source_to_len :
  exists regs1,
    msteps source_segs
      (init_machine_state RS 0x11134 source_phdrs rsp rmb rrnd inp)
      (mkst regs1 0x11038 fmem rrom) /\
    reg_get regs1 2 = Z_to_bv 64 (bv_unsigned rsp - 64) /\
    reg_get regs1 9 = nN /\
    reg_get regs1 18 = ptr + nN /\
    reg_get regs1 20 = ptr.
Proof.
  destruct source_to_loop as (regsA & HmsA & H2 & H9 & H20).
  destruct (source_scan nn 0%nat regsA ltac:(lia) H9 H20)
    as (regsB & HagB & H9B & H18B & HmsB).
  exists regsB. split; [|split; [|split; [|split]]].
  - eapply msteps_trans; [exact HmsA | exact HmsB].
  - rewrite (HagB 2) by reg_neq_tac. exact H2.
  - exact H9B.
  - exact H18B.
  - rewrite (HagB 20) by reg_neq_tac. exact H20.
Qed.

(** n > 65536: no output, exit 3. *)
Lemma source_wexit_cap : (65536 < Z.of_nat nn)%Z ->
  to_wexit RS (init_machine_state RS 0x11134 source_phdrs rsp rmb rrnd inp)
    [] (Z_to_bv 64 3).
Proof.
  intros Hcap. apply to_wexit_run.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le as HnnLe.
  destruct source_to_len as (regs1 & Hms1 & H2 & H9 & H18 & H20).
  eapply msteps_to_wexit; [exact Hms1|].
  (* 0x11038 .. 0x11040: the length cap test (taken) and the exit code;
     the fuel is EXACT, one more step would walk into the epilogue. *)
  sym_block source_segs 3%nat [true] (@nil expr)
    [((2 : reg), EVar 32); ((9 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp - 64); nN] (@nil word) R HR.
  { (* 0x11040: bltu a5, s1 IS taken -- 65536 < n *)
    pose proof u_nN. sym_br. }
  { exact H2. }
  { exact H9. }
  apply source_epilogue.
  - sym_regs HR. sym_close.
  - sym_regs HR. sym_close.
  - u_norm; lia.
  - apply read_slot_ra.
  - apply read_slot_0.
Qed.

(* ================================================================= *)
(* Exit-4 leaf: 0x1106c over any memory with an intact frame          *)
(* ================================================================= *)

Lemma source_exit4 : forall regs mem,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
    = Some (word_to_le_bytes 8 (0x11160 : word)) ->
  (forall a : word,
     In a [Z_to_bv 64 (bv_unsigned rsp - 16); Z_to_bv 64 (bv_unsigned rsp - 24);
           Z_to_bv 64 (bv_unsigned rsp - 32); Z_to_bv 64 (bv_unsigned rsp - 40);
           Z_to_bv 64 (bv_unsigned rsp - 48)] ->
     rdn source_segs mem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  to_wexit source_segs (mkst regs 0x1106c mem rrom) [] (Z_to_bv 64 4).
Proof.
  intros regs mem H2 Hra Hsl.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 4);
      [ exact SF_1106c | reflexivity | exact SD_1106c | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  apply source_epilogue.
  - regupd_resolve. exact H2.
  - regupd_resolve. reflexivity.
  - u_norm; lia.
  - exact Hra.
  - exact Hsl.
Qed.

(** The scratch spill slot at rsp-56 does not disturb the frame slots. *)
Lemma spill_ra : forall (v : word),
  rdn source_segs
    (wbytes fmem (Z_to_bv 64 (bv_unsigned rsp - 56)) (word_to_le_bytes 8 v))
    (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
  = Some (word_to_le_bytes 8 (0x11160 : word)).
Proof.
  intro v. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  rewrite rdn_wbytes_disjoint
    by (rewrite ?length_N_to_le_bytes; u_norm; lia).
  apply read_slot_ra.
Qed.

Lemma spill_0 : forall (v : word) (a : word),
  In a [Z_to_bv 64 (bv_unsigned rsp - 16); Z_to_bv 64 (bv_unsigned rsp - 24);
        Z_to_bv 64 (bv_unsigned rsp - 32); Z_to_bv 64 (bv_unsigned rsp - 40);
        Z_to_bv 64 (bv_unsigned rsp - 48)] ->
  rdn source_segs
    (wbytes fmem (Z_to_bv 64 (bv_unsigned rsp - 56)) (word_to_le_bytes 8 v))
    a 8%nat
  = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros v a Ha. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  assert (Hab : (bv_unsigned rsp - 48 <= bv_unsigned a
                 /\ bv_unsigned a + 8 <= bv_unsigned rsp - 8)%Z).
  { repeat destruct Ha as [<-|Ha]; try (exfalso; exact Ha); u_norm; lia. }
  rewrite rdn_wbytes_disjoint
    by (rewrite ?length_N_to_le_bytes; u_norm; lia).
  apply read_slot_0. exact Ha.
Qed.

(* ================================================================= *)
(* The reverse-copy loop: 0x110d4 / 0x11110 .. 0x11120               *)
(* ================================================================= *)

(* [store_grant_ok]: the loop's [sb]s are machine stores into the brk
   grant, and [mem0] is abstract here, so the writability of the grant
   has to come in as a hypothesis. *)
Lemma source_copy : forall (r : word) mem0,
  store_grant_ok source_segs mem0 r (nN + 1) ->
  rdn source_segs mem0 ptr (S nn) = Some (arg1 ++ [Z_to_bv 8 0]) ->
  (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + Z.of_nat nn + 1 <= bv_unsigned rsp - stack_max_size)%Z ->
  forall d regs,
  (d <= nn)%nat ->
  reg_get regs 20 = ptr ->
  reg_get regs 15 = ptr + nat_to_word d ->
  reg_get regs 8 = r + nat_to_word (nn - d) ->
  exists regs',
    (forall x : reg, x <> 15 -> x <> 8 -> x <> 14 ->
       reg_get regs' x = reg_get regs x) /\
    reg_get regs' 15 = ptr /\ reg_get regs' 8 = r + nN /\
    msteps source_segs
      (mkst regs 0x110d4 (wbytes mem0 r (firstn (nn - d) (rev arg1))) rrom)
      (mkst regs' 0x110d4 (wbytes mem0 r (rev arg1)) rrom).
Proof.
  intros r mem0 Hgok Hstr Hr0 Hceil.
  pose proof ptr_lo as Hplo. pose proof ptr_hi as Hphi.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le as HnnLe.
  pose proof (u64_range r) as Hur.
  assert (HnnA : Z.of_nat (length arg1) = Z.of_nat nn) by reflexivity.
  induction d as [|d IH]; intros regs Hd Hr19 Hr15 Hr8.
  - (* done *)
    exists regs. split; [|split; [|split]].
    + intros x _ _ _. reflexivity.
    + rewrite Hr15, word_add_0. reflexivity.
    + rewrite Hr8, Nat.sub_0_r. reflexivity.
    + rewrite Nat.sub_0_r.
      replace (firstn nn (rev arg1)) with (rev arg1)
        by (symmetry; apply firstn_all_rev).
      apply mst_refl.
  - (* one more byte to copy *)
    set (memI := wbytes mem0 r (firstn (nn - S d) (rev arg1))).
    set (b := byte_at arg1 d).
    assert (HlenF : length (firstn (nn - S d) (rev arg1)) = (nn - S d)%nat)
      by (apply firstn_length_le; rewrite length_rev; lia).
    assert (HuSd : bv_unsigned (ptr + nat_to_word (S d))
                   = (bv_unsigned ptr + Z.of_nat (S d))%Z).
    { rewrite u_add_small; rewrite u_ntw by lia; lia. }
    assert (Hud : bv_unsigned (ptr + nat_to_word d)
                  = (bv_unsigned ptr + Z.of_nat d)%Z).
    { rewrite u_add_small; rewrite u_ntw by lia; lia. }
    assert (HuW : bv_unsigned (r + nat_to_word (nn - S d))
                  = (bv_unsigned r + Z.of_nat (nn - S d))%Z).
    { rewrite u_add_small; rewrite u_ntw by lia; lia. }
    (* bne s4, a5 taken (ptr <> ptr + S d) *)
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x110d4 memI rrom)
                 = MachineOk (mkst regs 0x11110 memI rrom)).
    { rewrite (step_bne_tk source_segs regs 0x110d4 memI rrom _ 20 15 _
                 SF_110d4 eq_refl SD_110d4).
      - wlits. reflexivity.
      - getr_resolve. rewrite Hr19, Hr15.
        apply c_eq_neq. rewrite HuSd. lia. }
    (* lbu a4, -1(a5): byte arg1[d] *)
    set (regs1 := regupd regs 14 (Z_to_bv 64 (bv_unsigned b))).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs 0x11110 memI rrom)
                 = MachineOk (mkst regs1 0x11114 memI rrom)).
    { rewrite (step_lbu source_segs regs 0x11110 memI rrom _ 14 15 _ b
                 SF_11110 eq_refl SD_11110).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - getr_resolve. rewrite Hr15. imm_norm.
        rewrite word_add_nat_m1.
        unfold memI.
        rewrite rdn_wbytes_disjoint
          by (rewrite ?HlenF, ?Hud; lia).
        pose proof (rdn_nth _ _ _ _ _ d Hstr ltac:(lia)) as Hb'.
        replace (nth d (arg1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) with b in Hb'
          by reflexivity.
        exact Hb'. }
    (* addi s0, s0, 1 *)
    set (regs2 := regupd regs1 8 (r + nat_to_word (nn - d))).
    assert (E3 : RiscvSemantics.step source_segs (mkst regs1 0x11114 memI rrom)
                 = MachineOk (mkst regs2 0x11118 memI rrom)).
    { rewrite (step_addi_at source_segs regs1 0x11114 memI rrom _ 8 8 _
                 (r + nat_to_word (nn - d)) SF_11114 eq_refl SD_11114 eq_refl).
      - wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite Hr8.
        rewrite word_add_nat_1.
        do 2 f_equal. lia. }
    (* addi a5, a5, -1 *)
    set (regs3 := regupd regs2 15 (ptr + nat_to_word d)).
    assert (E4 : RiscvSemantics.step source_segs (mkst regs2 0x11118 memI rrom)
                 = MachineOk (mkst regs3 0x1111c memI rrom)).
    { rewrite (step_addi_at source_segs regs2 0x11118 memI rrom _ 15 15 _
                 (ptr + nat_to_word d) SF_11118 eq_refl SD_11118 eq_refl).
      - wlits. reflexivity.
      - unfold regs2, regs1. getr_resolve. rewrite Hr15. imm_norm.
        apply word_add_nat_m1. }
    (* sb a4, -1(s0) : write byte at r + (nn - S d) *)
    set (memI' := wbytes mem0 r (firstn (nn - d) (rev arg1))).
    assert (E5 : RiscvSemantics.step source_segs (mkst regs3 0x1111c memI rrom)
                 = MachineOk (mkst regs3 0x11120 memI' rrom)).
    { rewrite (step_sb_at source_segs regs3 0x1111c memI rrom _ 8 14 _
                 (r + nat_to_word (nn - S d)) b SF_1111c eq_refl SD_1111c).
      - wlits.
        replace (wbytes memI (r + nat_to_word (nn - S d)) [b]) with memI';
          [reflexivity|].
        unfold memI', memI.
        replace (nn - d)%nat with (S (nn - S d)) by lia.
        rewrite (firstn_rev_snoc arg1 (nn - S d)) by (unfold nn in *; lia).
        rewrite wbytes_app.
        rewrite HlenF.
        replace (nth (length arg1 - S (nn - S d)) arg1 (Z_to_bv 8 0)) with b.
        + reflexivity.
        + unfold b. replace (length arg1 - S (nn - S d))%nat with d
            by (unfold nn in *; lia).
          apply nth_lt_byte_at. unfold nn in *; lia.
      - unfold regs3, regs2, regs1. getr_resolve. imm_norm.
        replace (nn - d)%nat with (S (nn - S d)) by lia.
        apply word_add_nat_m1.
      - unfold regs3, regs2, regs1. getr_resolve.
        apply zext8_byte.
      - store_ok_peel; apply Hgok;
          rewrite ?u_nN1, ?HuW; u_norm; lia. }
    (* j 0x110d4 *)
    assert (E6 : RiscvSemantics.step source_segs (mkst regs3 0x11120 memI' rrom)
                 = MachineOk (mkst regs3 0x110d4 memI' rrom)).
    { rewrite (step_jal_x0 source_segs regs3 0x11120 memI' rrom _ _
                 SF_11120 eq_refl SD_11120).
      wlits. reflexivity. }
    assert (Hr19' : reg_get regs3 20 = ptr).
    { unfold regs3, regs2, regs1. regupd_resolve. exact Hr19. }
    assert (Hr15' : reg_get regs3 15 = ptr + nat_to_word d).
    { unfold regs3. apply regupd_same. }
    assert (Hr8' : reg_get regs3 8 = r + nat_to_word (nn - d)).
    { unfold regs3, regs2. regupd_resolve. reflexivity. }
    destruct (IH regs3 ltac:(lia) Hr19' Hr15' Hr8')
      as (regs' & Hag & H15 & H8 & Hms).
    exists regs'. split; [|split; [|split]].
    + intros x Hx15 Hx8 Hx14. rewrite (Hag x Hx15 Hx8 Hx14).
      unfold regs3, regs2, regs1. rewrite !regupd_other by assumption.
      reflexivity.
    + exact H15.
    + exact H8.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      exact Hms.
Qed.

(* ================================================================= *)
(* The put-style write-all retry loop                                  *)
(* ================================================================= *)

(** Every store the loop makes lands in main's frame or in musl's
    16-byte frame just below it, both inside the RLIMIT_STACK window. *)
Lemma brk_sok8 : forall (mem : word -> option byte) (a : word),
  mem_grows wmem mem ->
  (bv_unsigned rsp - 96 <= bv_unsigned a)%Z ->
  (bv_unsigned a + 8 <= bv_unsigned rsp)%Z ->
  RiscvSemantics.store_ok source_segs mem a 8%nat = true.
Proof.
  intros mem a Hg Hlo Hhi.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  eapply store_ok_mono; [exact Hg|].
  unfold wmem.
  apply (store_ok_wrap_window_valid source_segs inp rmb source_phdrs _ rsp rbrk a 8 rrnd
           Hvl Hlau);
    unfold stack_window_reach, stack_max_size; lia.
Qed.

Local Ltac bk_grows := solve_mem_grows.

Local Ltac bk_sok := apply brk_sok8; [ bk_grows | u_norm; lia | u_norm; lia ].

Local Ltac bk_ssd F D aexp vexp vtac := stepsd F D aexp vexp vtac ltac:(bk_sok).

Local Ltac bk_sld F D aexp vexp readtac := stepld F D aexp vexp readtac.

(** After a (possibly short) delivery of [n] bytes the machine sits at
    0x11218 — [__syscall_cp_c]'s post-ecall [ret] — with
    a0 = [len_word (firstn n rest)].  The run returns through musl's
    [write] wrapper and [__syscall_ret], reloads the buffer-pointer
    spill at rsp-56, decrements the running count in s3, bumps the
    pointer, and either falls into main's exit-0 tail (full delivery,
    [bnez s3] not taken) or respills and reissues the write.  Induction
    on [fuel >= length rest]; the remainder strictly shrinks because
    every delivery is nonempty. *)
Lemma src_put_wall : forall fuel (rest : list byte) (p : word) n regs mem,
  (length rest <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length rest)%nat ->
  (Z.of_nat (length rest) <= 131073)%Z ->
  (0 < bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) <= bv_unsigned rsp - 96)%Z ->
  reg_get regs 1 = (0x111b4 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
  reg_get regs 10 = len_word (firstn n rest) ->
  reg_get regs 19 = len_word rest ->
  mem_grows wmem mem ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 72)) 8%nat
    = Some (word_to_le_bytes 8 (0x110f4 : word)) ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8%nat
    = Some (word_to_le_bytes 8 p) ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
    = Some (word_to_le_bytes 8 (0x11160 : word)) ->
  (forall a : word,
     In a [Z_to_bv 64 (bv_unsigned rsp - 16); Z_to_bv 64 (bv_unsigned rsp - 24);
           Z_to_bv 64 (bv_unsigned rsp - 32); Z_to_bv 64 (bv_unsigned rsp - 40);
           Z_to_bv 64 (bv_unsigned rsp - 48)] ->
     rdn source_segs mem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  rdn source_segs mem p (length rest) = Some rest ->
  to_wall_tail source_segs (Z_to_bv 64 1)
    (mkst regs (0x11218 : word) mem rrom)
    (skipn n rest)
    (to_wallexit source_segs (Z_to_bv 64 1) [] (Z_to_bv 64 0)).
Proof.
  induction fuel as [|fuel IH];
    intros rest p n regs mem Hfuel Hn1 Hn2 Hlen Hplo Hphi
           H1 H2 H10 H19 Hgrow Hra72 Hptr Hslra Hsl Hread.
  { lia. }
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi. pose proof stack_max_size_val as Hsms.
  (* 0x11218: ret out of __syscall_cp_c, back into the write wrapper *)
  stepjr SF_11218 SD_11218 (0x111b4 : word) ltac:(getr_resolve; exact H1).
  (* 0x111b4: ld ra,8(sp) -- the wrapper's saved ra (0x110f4) *)
  bk_sld SF_111b4 SD_111b4 (Z_to_bv 64 (bv_unsigned rsp - 72))
    (0x110f4 : word) ltac:(exact Hra72).
  (* 0x111b8: addi sp,sp,16 -- pop the wrapper frame *)
  stepiv SF_111b8 SD_111b8 (Z_to_bv 64 (bv_unsigned rsp - 64))
    ltac:(getr_resolve; rewrite H2; sp_norm; f_equal; lia).
  (* 0x111bc: j __syscall_ret *)
  stepj SF_111bc SD_111bc.
  (* 0x111c0: lui a5,0xfffff *)
  stepi SF_111c0 SD_111c0.
  (* 0x111c4: bltu a5,a0 falls through (the delivery is no error) *)
  step_intro;
    [ reflexivity
    | eapply step_bltu_ft;
      [ exact SF_111c4 | reflexivity | exact SD_111c4
      | getr_resolve; rewrite H10;
        rewrite c_ltu_ltb; apply Z.ltb_ge;
        match goal with |- context [bv_unsigned (v_lui ?z)] =>
          replace (bv_unsigned (v_lui z)) with 18446744073709547520%Z
            by (vm_compute; reflexivity)
        end;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x111c8: ret -- back into main's put loop at 0x110f4 *)
  stepjr SF_111c8 SD_111c8 (0x110f4 : word) ltac:(getr_resolve; reflexivity).
  (* 0x110f4: blez a0 falls through (the delivery is nonempty) *)
  step_intro;
    [ reflexivity
    | eapply step_bge_ft;
      [ exact SF_110f4 | reflexivity | exact SD_110f4
      | getr_resolve; rewrite H10; apply c_lts_0_pos;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x110f8: ld a1,8(sp) -- the buffer-pointer spill *)
  bk_sld SF_110f8 SD_110f8 (Z_to_bv 64 (bv_unsigned rsp - 56)) p
    ltac:(exact Hptr).
  (* 0x110fc: sub s3,s3,a0 -- the count decrement *)
  stepiv SF_110fc SD_110fc (len_word (skipn n rest))
    ltac:(getr_resolve; rewrite H10, H19; apply v_sub_len_firstn; lia).
  (* 0x11100: add a1,a1,a0 -- the pointer bump *)
  stepiv SF_11100 SD_11100 (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
    ltac:(getr_resolve; rewrite H10; apply v_add_len_firstn_Z; lia).
  destruct (Nat.eq_dec n (length rest)) as [-> | Hne].
  - (* full delivery: bnez not taken, fall into main's exit-0 tail *)
    rewrite skipn_all.
    step_intro;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact SF_11104 | reflexivity | exact SD_11104
        | getr_resolve; apply c_eq_0_of_u; reflexivity ]
      | norm_pc ].
    (* 0x11108: li a0,0 *)
    stepiv SF_11108 SD_11108 (Z_to_bv 64 0) ltac:(getr_resolve; bveq).
    (* 0x1110c: j 0x11070 -- main's epilogue *)
    stepj SF_1110c SD_1110c.
    apply twt_done. cbn [to_wallexit].
    apply source_epilogue.
    + regupd_resolve; reflexivity.
    + regupd_resolve; reflexivity.
    + u_norm; lia.
    + exact Hslra.
    + exact Hsl.
  - (* short delivery: bnez taken, respill and reissue *)
    step_intro;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact SF_11104 | reflexivity | exact SD_11104
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* 0x110e4: addi a2,s3,0 -- the remaining count *)
    stepiv SF_110e4 SD_110e4 (len_word (skipn n rest))
      ltac:(getr_resolve; apply v_addi_0).
    (* 0x110e8: li a0,1 -- the fd *)
    stepiv SF_110e8 SD_110e8 (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* 0x110ec: sd a1,8(sp) -- respill the bumped pointer *)
    bk_ssd SF_110ec SD_110ec (Z_to_bv 64 (bv_unsigned rsp - 56))
      (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
      ltac:(getr_resolve; reflexivity).
    (* 0x110f0: jal write() *)
    stepj SF_110f0 SD_110f0.
    (* the wrapper: frame, arg shuffle, ra spill, __syscall_cp *)
    stepiv SF_1118c SD_1118c (Z_to_bv 64 (bv_unsigned rsp - 80))
      ltac:(getr_resolve; sp_norm; f_equal; lia).
    stepiv SF_11190 SD_11190 (len_word (skipn n rest))
      ltac:(getr_resolve; apply v_addi_0).
    stepi SF_11194 SD_11194.
    stepiv SF_11198 SD_11198 (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
      ltac:(getr_resolve; apply v_addi_0).
    stepi SF_1119c SD_1119c.
    stepiv SF_111a0 SD_111a0 (Z_to_bv 64 1)
      ltac:(getr_resolve; apply v_addi_0).
    stepi SF_111a4 SD_111a4.
    stepiv SF_111a8 SD_111a8 (Z_to_bv 64 64) ltac:(getr_resolve; bveq).
    bk_ssd SF_111ac SD_111ac (Z_to_bv 64 (bv_unsigned rsp - 72))
      (0x110f4 : word) ltac:(getr_resolve; bveq).
    stepj SF_111b0 SD_111b0.
    (* 0x1121c: __syscall_cp's trampoline into __syscall_cp_c *)
    stepj SF_1121c SD_1121c.
    (* __syscall_cp_c's seven shuffles *)
    stepiv SF_111f8 SD_111f8 (Z_to_bv 64 64) ltac:(getr_resolve; apply v_addi_0).
    stepiv SF_111fc SD_111fc (Z_to_bv 64 1) ltac:(getr_resolve; apply v_addi_0).
    stepiv SF_11200 SD_11200 (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
      ltac:(getr_resolve; apply v_addi_0).
    stepiv SF_11204 SD_11204 (len_word (skipn n rest))
      ltac:(getr_resolve; apply v_addi_0).
    stepi SF_11208 SD_11208.
    stepi SF_1120c SD_1120c.
    stepi SF_11210 SD_11210.
    (* 0x11214: ecall -- the reissued write *)
    eapply twt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ SF_11214 eq_refl) |].
    apply twt_more; [rewrite length_skipn; lia|].
    apply (twl_write_rec source_segs (Z_to_bv 64 1)).
    + getr_resolve; reflexivity.
    + regupd_resolve; reflexivity.
    + match goal with
      | |- ms_read_bytes _ (reg_get ?R 11) (reg_get ?R 12) = Some _ =>
          replace (reg_get R 11)
            with (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
            by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word (skipn n rest))
            by (regupd_resolve; reflexivity)
      end.
      rewrite (ms_read_bytes_rdn (run_segments source_segs inp rsp rmb)) by reflexivity.
      unfold run_segments. apply rdn_lift.
      cbn [ms_mem].
      replace (word_to_nat (len_word (skipn n rest)))
        with (length (skipn n rest))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      rewrite !rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes, ?length_skipn; u_norm; lia).
      pose proof (rdn_skipn source_segs mem (length rest) p rest n Hread Hn2)
        as Hsk.
      rewrite word_add_nat_Z in Hsk by lia.
      rewrite length_skipn. exact Hsk.
    + (* the remainder's range passes [access_ok]: inside the grant *)
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
      rewrite u_Z2bv by lia. rewrite length_skipn. unfold TASK_SIZE. lia.
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
      * regupd_resolve; bveq.
      * regupd_resolve; reflexivity.
      * regupd_resolve; reflexivity.
      * regupd_resolve; reflexivity.
      * bk_grows.
      * apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite !rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        exact Hslra.
      * intros a Ha.
        assert (Hab : (bv_unsigned rsp - 48 <= bv_unsigned a
                       /\ bv_unsigned a + 8 <= bv_unsigned rsp - 8)%Z).
        { repeat destruct Ha as [<-|Ha]; try (exfalso; exact Ha); u_norm; lia. }
        rewrite !rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        apply Hsl. exact Ha.
      * rewrite !rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes, ?length_skipn; u_norm; lia).
        pose proof (rdn_skipn source_segs mem (length rest) p rest n Hread Hn2)
          as Hsk.
        rewrite word_add_nat_Z in Hsk by lia.
        rewrite length_skipn. exact Hsk.
Qed.

(* ================================================================= *)
(* Success tail: from the return of the second brk (a0 = want) to      *)
(* the single write and exit 0.                                        *)
(* ================================================================= *)

Lemma source_success : forall regs (r grant : word),
  (bv_unsigned (nN + 1) <= bv_unsigned grant)%Z ->
  (bv_unsigned r + bv_unsigned grant <= bv_unsigned rsp - stack_max_size)%Z ->
  (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + Z.of_nat nn + 1 <= bv_unsigned rsp - stack_max_size)%Z ->
  reg_get regs 1 = (0x110c4 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ->
  reg_get regs 8 = r ->
  reg_get regs 9 = nN ->
  reg_get regs 10 = r + (nN + 1) ->
  reg_get regs 18 = ptr + nN ->
  reg_get regs 19 = nN + 1 ->
  reg_get regs 20 = ptr ->
  to_wallexit source_segs (Z_to_bv 64 1) [rev_buf arg1] (Z_to_bv 64 0)
    (mkst regs 0x11188
       (zmem (wbytes fmem (Z_to_bv 64 (bv_unsigned rsp - 56))
                (word_to_le_bytes 8 (r + (nN + 1)))) r grant) rrom).
Proof.
  intros regs r grant Hgrant Hgrantceil Hr0 Hceil
    H1 H2 H8 H9 H10 H18 H19 H20.
  split; [rewrite length_rev_buf; lia|].
  pose proof ptr_lo as Hplo. pose proof ptr_hi as Hphi.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le as HnnLe.
  pose proof (u64_range r) as Hur.
  assert (HnnA : Z.of_nat (length arg1) = Z.of_nat nn) by reflexivity.
  assert (Hun1 : bv_unsigned (nN + 1) = (Z.of_nat nn + 1)%Z) by (exact u_nN1).
  assert (Hurn : bv_unsigned (r + nN) = (bv_unsigned r + Z.of_nat nn)%Z).
  { rewrite u_add_small; rewrite u_nN; lia. }
  assert (Hurn1 : bv_unsigned (r + (nN + 1))
                  = (bv_unsigned r + Z.of_nat nn + 1)%Z).
  { rewrite u_add_small; rewrite Hun1; lia. }
  set (gmem := wbytes fmem (Z_to_bv 64 (bv_unsigned rsp - 56))
                 (word_to_le_bytes 8 (r + (nN + 1)))).
  set (mem0 := zmem gmem r grant).
  (* 0x11188 .. 0x110d0: the [ret] out of [raw_syscall], the reload of
     the requested break, the equality test against a0 and the two
     register moves that set up the copy loop -- one block.  The reload
     is SCRIPTED as the SAME expression a0 is pinned to, which is what
     makes the [bne] two instructions later a syntactic identity. *)
  sym_block source_segs 5%nat [false] [EVar 35]
    [((1 : reg), ELit 0x110c4); ((2 : reg), EVar 32); ((8 : reg), EVar 33);
     ((9 : reg), EVar 34); ((10 : reg), EVar 35); ((18 : reg), EVar 36);
     ((20 : reg), EVar 37)]
    [Z_to_bv 64 (bv_unsigned rsp - 64); r; nN; r + (nN + 1); ptr + nN; ptr]
    [r + (nN + 1)] R HR.
  { (* 0x110c8: bne a1, a0 falls through -- both are the reloaded break *)
    sym_br. }
  { (* 0x110c4: ld a1, 8(sp) -- the spilled break request *)
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 64)) + 8))
      with (Z_to_bv 64 (bv_unsigned rsp - 56)) by (u_norm; f_equal; lia).
    exists (word_to_le_bytes 8 (r + (nN + 1))). split;
      [ unfold mem0; rewrite rdn_zmem_out by (rewrite ?Hun1; u_norm; lia);
        unfold gmem; apply rdn_wbytes_hit8; u_norm; lia
      | exact (bytes_le_to_Z_8 _) ]. }
  { transitivity (0x110c4 : word); [ exact H1 | bveq ]. }
  { exact H2. }
  { exact H8. }
  { exact H9. }
  { exact H10. }
  { exact H18. }
  { exact H20. }
  (* the copy loop *)
  assert (Hstr0 : rdn source_segs mem0 ptr (S nn) = Some (arg1 ++ [Z_to_bv 8 0])).
  { unfold mem0. rewrite rdn_zmem_out by (rewrite ?Hun1; lia).
    unfold gmem.
    rewrite rdn_wbytes_disjoint
      by (rewrite ?length_N_to_le_bytes; u_norm; lia).
    apply read_str_f. }
  destruct (source_copy r mem0
              ltac:(unfold mem0; apply store_grant_zmem_prefix;
                    [ exact Hgrant | lia ])
              Hstr0 Hr0
              ltac:(lia)
              nn R (Nat.le_refl nn)
              ltac:(sym_regs HR; sym_close)
              ltac:(sym_regs HR; sym_close)
              ltac:(rewrite Nat.sub_diag, word_add_0; sym_regs HR; sym_close))
    as (regsC & HagC & H15C & H8C & HmsC).
  replace (wbytes mem0 r (firstn (nn - nn) (rev arg1))) with mem0 in HmsC.
  2:{ rewrite Nat.sub_diag. cbn [firstn wbytes]. reflexivity. }
  eapply msteps_to_wall_tail; [ exact HmsC | ].
  set (memA := wbytes mem0 r (rev arg1)) in *.
  (* Register facts for the post-copy file, once. *)
  assert (Hc2 : reg_get regsC 2 = Z_to_bv 64 (bv_unsigned rsp - 64))
    by (rewrite (HagC 2) by reg_neq_tac; sym_regs HR; sym_close).
  assert (Hc9 : reg_get regsC 9 = nN)
    by (rewrite (HagC 9) by reg_neq_tac; sym_regs HR; sym_close).
  assert (Hc11 : reg_get regsC 11 = r)
    by (rewrite (HagC 11) by reg_neq_tac; sym_regs HR; sym_close).
  assert (Hc19 : reg_get regsC 19 = nN + 1)
    by (rewrite (HagC 19) by reg_neq_tac; sym_regs HR; exact H19).
  assert (Hc20 : reg_get regsC 20 = ptr)
    by (rewrite (HagC 20) by reg_neq_tac; sym_regs HR; sym_close).
  (* 0x110d4 .. 0x110dc: the loop-exit test (s4 = a5 = ptr, pinned to the
     SAME symbolic slot so the [bne] is a syntactic identity), the end
     pointer and the newline literal.  The executor stops at the [sb]:
     its address [a1 + s1] is a sum of two symbolic registers, which
     [to_saddr] does not recognise. *)
  sym_block source_segs 3%nat [false] (@nil expr)
    [((9 : reg), EVar 32); ((11 : reg), EVar 33);
     ((15 : reg), EVar 34); ((20 : reg), EVar 34)]
    [nN; r; ptr] (@nil word) R1 HR1.
  { (* 0x110d4: bne s4, a5 falls through *) sym_br. }
  { exact Hc9. }
  { exact Hc11. }
  { exact H15C. }
  { exact Hc20. }
  (* 0x110e0: sb a5, 0(s1) -- the newline at r + n *)
  set (memB := wbytes mem0 r (rev_buf arg1)).
  eapply twt_step;
    [ reflexivity
    | eapply step_sb_at with (a := r + nN) (b := Z_to_bv 8 10);
      [ exact SF_110e0 | reflexivity | exact SD_110e0
      | sym_regs HR1; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | sym_regs HR1; sym_close
      | store_ok_peel; apply store_ok_zmem;
        rewrite ?u_nN1, ?Hurn; u_norm; lia ]
    | step_simpl ].
  match goal with
  |- to_wall_tail _ _ (mkst ?R _ ?M _) _ _ =>
      replace M with memB
  end.
  2:{ unfold memB, memA, rev_buf.
      rewrite wbytes_app. rewrite length_rev.
      reflexivity. }
  (* 0x110e4 .. 0x11214: the write-argument setup, the spill of the
     buffer pointer, and musl's whole [write] wrapper down to the
     syscall -- ONE block of twenty-two instructions across four
     functions ([write], [__syscall_cp], [__syscall_cp_c]), every call
     a direct [jal] whose link register the executor tracks itself. *)
  sym_block source_segs 24%nat (@nil bool) (@nil expr)
    [((2 : reg), EVar 32); ((11 : reg), EVar 33); ((19 : reg), EVar 34)]
    [Z_to_bv 64 (bv_unsigned rsp - 64); r; nN + 1] (@nil word) R2 HR2.
  { (* 0x111ac: sd ra, 8(sp) -- musl's own frame *) solve_store_ok_inv. }
  { (* 0x110ec: sd a1, 8(sp) -- spill the buffer pointer *)
    solve_store_ok_inv. }
  (* [a1] was pinned in the previous block, so [sym_pin_auto] discharges
     its obligation itself; only the two registers this block reads out
     of the pre-copy file are left. *)
  { sym_regs HR1; exact Hc2. }
  { sym_regs HR1; exact Hc19. }
  (* 0x11214: ecall -- write(1, r, n+1) *)
  eapply twt_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_11214 eq_refl) | ].
  apply twt_more; [rewrite length_rev_buf; lia|].
  apply (twl_write_rec source_segs (Z_to_bv 64 1)).
  - sym_regs HR2. vm_compute. reflexivity.
  - sym_regs HR2. sym_close.
  - rewrite (ms_read_bytes_rdn (run_segments source_segs inp rsp rmb)) by reflexivity.
    unfold run_segments. apply rdn_lift.
    cbn [ms_mem ms_regs].
    sym_regs HR2.
    replace (word_to_nat (nN + 1)) with (S nn)
      by (unfold word_to_nat; rewrite u_nN1; lia).
    repeat (rewrite rdn_wbytes_below
              by (rewrite ?length_N_to_le_bytes; u_norm; lia)).
    unfold memB.
    replace (S nn) with (length (rev_buf arg1))
      by (rewrite length_rev_buf; reflexivity).
    apply rdn_wbytes_hit.
    rewrite length_rev_buf. lia.
  - (* the buffer's range passes [access_ok]: the brk grant, below the
       stack *)
    replace (reg_get R2 11) with r by (sym_regs HR2; sym_close).
    replace (reg_get R2 12) with (nN + 1) by (sym_regs HR2; sym_close).
    apply access_okb_intro. rewrite u_nN1. unfold TASK_SIZE. lia.
  - rewrite length_rev_buf; lia.
  - (* the write-all retry loop, per delivered length *)
    intros n Hn1 Hn2.
    norm_pc.
    apply (src_put_wall (length (rev_buf arg1)) (rev_buf arg1) r n).
    + lia.
    + exact Hn1.
    + exact Hn2.
    + rewrite length_rev_buf; lia.
    + exact Hr0.
    + rewrite length_rev_buf; lia.
    + regupd_resolve; sym_regs HR2; sym_close.
    + regupd_resolve; sym_regs HR2; sym_close.
    + regupd_resolve; reflexivity.
    + regupd_resolve; sym_regs HR2.
      match goal with |- ?x = _ => transitivity (nN + 1) end;
        [ sym_close
        | apply bv_eq; rewrite u_nN1, u_len_word
            by (rewrite length_rev_buf; lia);
          rewrite length_rev_buf; unfold nn; lia ].
    + (* the loop's memory grows out of the initial stack image *)
      eapply mem_grows_trans; [ | apply wbytes_grows ].
      eapply mem_grows_trans; [ | apply wbytes_grows ].
      unfold memB, memA, mem0, gmem.
      eapply mem_grows_trans; [ | apply wbytes_grows ].
      eapply mem_grows_trans; [ | apply zmem_grows ].
      eapply mem_grows_trans; [ | apply wbytes_grows ].
      exact grows_fmem.
    + apply rdn_wbytes_hit8; u_norm; lia.
    + rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; u_norm; lia).
      apply rdn_wbytes_hit8; u_norm; lia.
    + repeat (rewrite rdn_wbytes_disjoint
                by (rewrite ?length_N_to_le_bytes; u_norm; lia)).
      unfold memB, mem0, gmem.
      repeat (rewrite rdn_wbytes_disjoint
                by (rewrite ?length_N_to_le_bytes, ?length_rev_buf;
                    u_norm; lia)).
      rewrite rdn_zmem_out by (rewrite ?u_nN1; u_norm; lia).
      rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; u_norm; lia).
      apply read_slot_ra.
    + intros a Ha.
      assert (Hab : (bv_unsigned rsp - 48 <= bv_unsigned a
                     /\ bv_unsigned a + 8 <= bv_unsigned rsp - 8)%Z).
      { repeat destruct Ha as [<-|Ha]; try (exfalso; exact Ha); u_norm; lia. }
      repeat (rewrite rdn_wbytes_disjoint
                by (rewrite ?length_N_to_le_bytes; u_norm; lia)).
      unfold memB, mem0, gmem.
      repeat (rewrite rdn_wbytes_disjoint
                by (rewrite ?length_N_to_le_bytes, ?length_rev_buf;
                    u_norm; lia)).
      rewrite rdn_zmem_out by (rewrite ?u_nN1; u_norm; lia).
      rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; u_norm; lia).
      apply read_slot_0. exact Ha.
    + repeat (rewrite rdn_wbytes_below
                by (rewrite ?length_N_to_le_bytes, ?length_rev_buf;
                    u_norm; lia)).
      unfold memB.
      apply rdn_wbytes_hit.
      rewrite length_rev_buf. lia.
Qed.

(* ================================================================= *)
(* Entry to the first brk ecall                                       *)
(* ================================================================= *)

Lemma source_to_brk1 : (Z.of_nat nn <= 65536)%Z ->
  exists regs3,
    msteps source_segs
      (init_machine_state RS 0x11134 source_phdrs rsp rmb rrnd inp)
      {| ms_regs := regs3; ms_fregs := fp_regs; ms_pc_val := (0x11184 : word);
         ms_svc_pending := Some (Z_to_bv 64 214); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := fmem; ms_rom := rrom |} /\
    reg_get regs3 1 = (0x11064 : word) /\
    reg_get regs3 2 = Z_to_bv 64 (bv_unsigned rsp - 64) /\
    reg_get regs3 9 = nN /\
    reg_get regs3 10 = Z_to_bv 64 0 /\
    reg_get regs3 18 = ptr + nN /\
    reg_get regs3 20 = ptr.
Proof.
  intros Hncap.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le as HnnLe.
  destruct source_to_len as (regs1 & Hms1 & H2 & H9 & H18 & H20).
  (* 0x11038 .. 0x11180: the length cap test (fall-through), the six
     zeroed syscall arguments, the [jal] into [raw_syscall] and its seven
     register moves -- ONE block, stopping at the [ecall]. *)
  sym_block_ex source_segs (mkst regs1 (Z_to_bv 64 0x11038) fmem rrom)
    18%nat [false] (@nil expr)
    [((2 : reg), EVar 32); ((9 : reg), EVar 33); ((18 : reg), EVar 34);
     ((20 : reg), EVar 35)]
    [Z_to_bv 64 (bv_unsigned rsp - 64); nN; ptr + nN; ptr] (@nil word) R HR Hms.
  { (* 0x11040: bltu a5, s1 falls through -- n <= 65536 *)
    pose proof u_nN. sym_br. }
  { exact H2. }
  { exact H9. }
  { exact H18. }
  { exact H20. }
  exists R. split.
  { eapply msteps_trans; [exact Hms1|].
    sym_chain Hms.
    (* 0x11184: ecall -- brk(0) *)
    eapply mst_step;
      [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_11184 eq_refl) | ].
    match goal with
    | |- msteps _ {| ms_regs := ?RR; ms_fregs := _; ms_pc_val := _;
                     ms_svc_pending := _; ms_resv := _; ms_fcsr := _;
                     ms_mem := _; ms_rom := _ |} _ =>
        replace (getr RR 17) with (Z_to_bv 64 214) by (sym_regs HR; sym_close)
    end.
    apply mst_refl. }
  repeat split; sym_regs HR; sym_close.
Qed.

(* ================================================================= *)
(* From the return of the first brk (a0 = r <> 0, no wrap) to the      *)
(* second brk ecall                                                    *)
(* ================================================================= *)

Lemma source_to_brk2 : forall regs3 (r : word),
  reg_get regs3 1 = (0x11064 : word) ->
  reg_get regs3 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ->
  reg_get regs3 9 = nN ->
  reg_get regs3 18 = ptr + nN ->
  reg_get regs3 20 = ptr ->
  r <> Z_to_bv 64 0 ->
  (bv_unsigned r + Z.of_nat nn + 1 < 2^64)%Z ->
  exists regs5,
    msteps source_segs (mkst (regupd regs3 10 r) 0x11188 fmem rrom)
      {| ms_regs := regs5; ms_fregs := fp_regs; ms_pc_val := (0x11184 : word);
         ms_svc_pending := Some (Z_to_bv 64 214); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := wbytes fmem (Z_to_bv 64 (bv_unsigned rsp - 56))
                     (word_to_le_bytes 8 (r + (nN + 1)));
         ms_rom := rrom |} /\
    reg_get regs5 1 = (0x110c4 : word) /\
    reg_get regs5 2 = Z_to_bv 64 (bv_unsigned rsp - 64) /\
    reg_get regs5 8 = r /\
    reg_get regs5 9 = nN /\
    reg_get regs5 10 = r + (nN + 1) /\
    reg_get regs5 18 = ptr + nN /\
    reg_get regs5 19 = nN + 1 /\
    reg_get regs5 20 = ptr.
Proof.
  intros regs3 r H1 H2 H9 H18 H20 Hrnz Hw.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le as HnnLe.
  pose proof (u64_range r) as Hur.
  pose proof (word_neq0_unsigned r Hrnz) as Hur0.
  assert (Hun1 : bv_unsigned (nN + 1) = (Z.of_nat nn + 1)%Z) by (exact u_nN1).
  assert (Hurn1 : bv_unsigned (r + (nN + 1))
                  = (bv_unsigned r + Z.of_nat nn + 1)%Z).
  { rewrite u_add_small; rewrite Hun1; lia. }
  (* The executor's spelling of the requested break. *)
  assert (Hrn1s : Z_to_bv 64 (bv_unsigned r + (bv_unsigned nN + 1))
                  = r + (nN + 1)).
  { apply bv_eq. rewrite Hurn1, u_Z2bv by (rewrite u_nN; lia).
    rewrite u_nN. lia. }
  (* 0x11188 .. 0x11180: the [ret] out of the first [raw_syscall], the
     null test on the returned break (taken), the wrap test on the
     request (fall-through), the six zeroed arguments, the spill of the
     request and [raw_syscall] again -- ONE block. *)
  sym_block_ex source_segs
    (mkst (regupd regs3 10 r) (Z_to_bv 64 0x11188) fmem rrom)
    21%nat [true; false] (@nil expr)
    [((1 : reg), ELit 0x11064); ((2 : reg), EVar 32); ((9 : reg), EVar 33);
     ((10 : reg), EVar 34); ((18 : reg), EVar 35); ((20 : reg), EVar 36)]
    [Z_to_bv 64 (bv_unsigned rsp - 64); nN; r; ptr + nN; ptr] (@nil word) R HR Hms.
  { (* 0x110bc: sd a1, 8(sp) -- spill the requested break *)
    solve_store_ok_inv. }
  { (* 0x110a0: bgeu a0, a1 falls through -- the request does not wrap *)
    apply negb_false_iff. unfold bv_ltu. apply Z.ltb_lt.
    rewrite u_Z2bv by (rewrite u_nN; lia). rewrite u_nN. lia. }
  { (* 0x11068: bnez a0 IS taken -- the first brk succeeded *)
    sym_br. }
  all: rewrite ?getr_nz by reg_neq_tac.
  { transitivity (0x11064 : word); [ regupd_resolve; exact H1 | bveq ]. }
  { regupd_resolve. exact H2. }
  { regupd_resolve. exact H9. }
  { regupd_resolve. reflexivity. }
  { regupd_resolve. exact H18. }
  { regupd_resolve. exact H20. }
  match type of Hms with
  | msteps _ _ (mkst _ _ ?m _) =>
      replace m with (wbytes fmem (Z_to_bv 64 (bv_unsigned rsp - 56))
                        (word_to_le_bytes 8 (r + (nN + 1)))) in Hms;
        [ | sym_mem_norm; rewrite Hrn1s; reflexivity ]
  end.
  exists R. split.
  { sym_chain Hms.
    (* 0x11184: ecall -- brk(r + n + 1) *)
    eapply mst_step;
      [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_11184 eq_refl) | ].
    match goal with
    | |- msteps _ {| ms_regs := ?RR; ms_fregs := _; ms_pc_val := _;
                     ms_svc_pending := _; ms_resv := _; ms_fcsr := _;
                     ms_mem := _; ms_rom := _ |} _ =>
        replace (getr RR 17) with (Z_to_bv 64 214) by (sym_regs HR; sym_close)
    end.
    apply mst_refl. }
  repeat split; sym_regs HR; first [ exact Hrn1s | sym_close ].
Qed.


(* ================================================================= *)
(* The outcome tree                                                   *)
(* ================================================================= *)

Hypothesis Hbrk_mod : (bv_unsigned rbrk mod page_size = 0)%Z.

(** The run's outcome set, over the run's segment list and initial model
    (the vDSO counter, and the vDSO pair in the brk ledger
    [State.init_reserved]).  [Hmb] is [Run.valid_mmap_base]'s floor, which
    keeps the vDSO pair far above the heap ([run_ledger_free]); [Hrd] is
    the stdout reader [Run.valid_input] pins, which the write node needs. *)
Lemma source_outcomes :
  (mmap_base_min <= bv_unsigned rmb)%Z ->
  in_channel_reader inp = true ->
  (Z.of_nat nn <= 65536)%Z ->
  to_outcomes RS
    (init_machine_state RS 0x11134 source_phdrs rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
       (init_model (segments_reserved RS) rbrk rmb rsp source_alloc_limit inp))
    (brkU (rev_buf arg1)).
Proof.
  intros Hmb Hrd Hncap.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le as HnnLe.
  assert (Hun1 : bv_unsigned (nN + 1) = (Z.of_nat nn + 1)%Z) by (exact u_nN1).
  pose proof rbrk_lo_num as Hblo. pose proof rbrk_hi_num as Hbhi.
  assert (Hres : (reserved_top (segments_reserved RS) <= bv_unsigned rbrk)%Z).
  { (* the image's list is concrete, so the run's reservations split by
       computation; the vDSO pair reserves nothing *)
    replace (segments_reserved RS)
      with (segments_reserved source_segs
            ++ segments_reserved (vdso_segments (in_kernel inp) rsp rmb))
      by reflexivity.
    rewrite segments_reserved_vdso, app_nil_r. exact Hbrk_lo. }
  (* fd 1 is the stdout channel and has a reader in the run's initial
     model ([with_vdso] keeps the descriptor table and the reader flag) *)
  assert (Hfd0 : fd1chan (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
                   (init_model (segments_reserved RS) rbrk rmb rsp source_alloc_limit inp)))
    by exact (init_model_fd1chan (segments_reserved RS) rbrk rmb rsp
                source_alloc_limit inp Hrd).
  destruct (source_to_brk1 Hncap)
    as (regs3 & Hms & E1 & E2 & E9 & E10 & E18 & E20).
  eapply tou_msteps; [exact (msteps_run source_segs inp rsp rmb _ _ Hms)|].
  apply (tou_brk_r RS _ _ (Z_to_bv 64 214)
           (T1 (init_reserved (segments_reserved RS) rmb rsp (in_kernel inp))
              source_alloc_limit (bv_unsigned rsp - stack_max_size) (nN + 1)
              [rev_buf arg1]));
    [reflexivity | vm_compute; reflexivity | | ].
  { (* per-resolution continuation *)
    intros r Hok.
    unfold ms_gpr in Hok |- *; cbn [ms_regs] in Hok |- *.
    rewrite arg_reg_0, E10 in Hok |- *.
    change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved RS) rmb rsp (in_kernel inp))
                        [] [] rbrk rbrk source_alloc_limit rmb rsp)
              (Z_to_bv 64 0) r) in Hok.
    (* brk(0) is deterministic: it reports the quantified ASLR base. *)
    apply brk_r_ok_query_iff in Hok. cbn [vm_brk] in Hok.
    rewrite m_vmmaps_with_vdso, m_vmmaps_init_model. cbn [vm_brk].
    assert (Hur : bv_unsigned r = bv_unsigned rbrk)
      by (rewrite Hok; reflexivity).
    assert (Hrmod : (bv_unsigned r mod page_size = 0)%Z).
    { rewrite Hur. exact Hbrk_mod. }
    assert (Hrnz : r <> Z_to_bv 64 0).
    { intro Hc. apply (f_equal bv_unsigned) in Hc.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
    assert (Hnw : (bv_unsigned r + Z.of_nat nn + 1 < 2^64)%Z)
      by (change (2^64)%Z with 18446744073709551616%Z; lia).
    assert (Hurn1 : bv_unsigned (r + (nN + 1))
                    = (bv_unsigned r + Z.of_nat nn + 1)%Z).
    { rewrite u_add_small; rewrite Hun1; lia. }
    assert (Hwant0 : r + (nN + 1) <> Z_to_bv 64 0).
    { intro He. apply (f_equal bv_unsigned) in He.
      rewrite Hurn1 in He.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in He. lia. }
    assert (Hne2 : r <> r + (nN + 1)).
    { intro He. apply (f_equal bv_unsigned) in He.
      rewrite Hurn1 in He. lia. }
    rewrite brk_zeros_query.
    rewrite (brk_unmaps_grow r rbrk) by lia.
    rewrite adv_brk, apply_zeros_nil. wlits.
    rewrite brk_model_query by exact Hok.
    rewrite m_vmmaps_with_vdso, m_vmmaps_init_model.
    cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_limit vm_mmap_base vm_init_sp].
    (* base is nonzero and non-wrapping: straight to the second brk *)
    destruct (source_to_brk2 regs3 r E1 E2 E9 E18 E20 Hrnz Hnw)
          as (regs5 & Hms2 & F1 & F2 & F8 & F9 & F10 & F18 & F19 & F20).
        eapply tou_msteps; [exact (msteps_run source_segs inp rsp rmb _ _ Hms2)|].
        apply (tou_brk_r RS _ _ (Z_to_bv 64 214) (T2 (r + (nN + 1)) [rev_buf arg1]));
          [reflexivity | vm_compute; reflexivity | | ].
        * (* per-resolution continuation at the second brk *)
          intros r2 Hok2.
          unfold ms_gpr in Hok2 |- *; cbn [ms_regs] in Hok2 |- *.
          rewrite arg_reg_0, F10 in Hok2 |- *.
          change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved RS) rmb rsp
                                            (in_kernel inp))
                              [] [] rbrk r source_alloc_limit rmb rsp)
                    (r + (nN + 1)) r2) in Hok2.
          rewrite m_vmmaps_with_vmmaps. cbn [vm_brk].
          apply brk_r_ok_grow_iff in Hok2;
            [ | lia | lia | lia ].
          destruct (decide (r2 = r + (nN + 1))) as [-> | Hne].
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
              (page_round_up_Z (bv_unsigned (r + (nN + 1))) - bv_unsigned r)).
            destruct (brk_aligned_grant_ok _ r (nN + 1) grant _ _
                        ltac:(apply u_add_small; rewrite Hun1; lia)
                        Hurn1 eq_refl (alloc_top_page_lt _) Hle Hfree)
              as (HgrantU & Hgrant & Hphysceil & Hrawceil & Hrawfree & _).
            rewrite brk_zeros_aligned_grow;
              [ | exact Hwant0 | lia | rewrite Hurn1; lia | exact Hrmod ].
            fold grant.
            rewrite brk_unmaps_grow by lia.
            rewrite adv_brk, apply_zeros_one. wlits.
            eapply tou_equiv;
              [ | intro o; apply (T2_succ_iff (r + (nN + 1)) [rev_buf arg1]) ].
            apply tou_wexit_eq.
            - apply fd1chan_brk_model. apply fd1chan_with_vmmaps. exact Hfd0.
            - apply to_wallexit_run.
              apply (source_success (regupd regs5 10 (r + (nN + 1))) r grant).
              + exact Hgrant.
              + exact Hphysceil.
              + lia.
              + exact Hrawceil.
              + regupd_resolve. exact F1.
              + regupd_resolve. exact F2.
              + regupd_resolve. exact F8.
              + regupd_resolve. exact F9.
              + regupd_resolve. reflexivity.
              + regupd_resolve. exact F18.
              + regupd_resolve. exact F19.
              + regupd_resolve. exact F20.
            - exact bufs_modeled_out. }
          { (* failure resolution: r2 = r, exit 4 *)
            destruct Hok2 as [Hcase _].
            destruct Hcase as [Hc | Hc]; [exact (False_ind _ (Hne Hc)) |].
            subst r2.
            rewrite brk_zeros_keep.
            rewrite brk_unmaps_grow by lia.
            rewrite adv_brk, apply_zeros_nil. wlits.
            eapply tou_equiv;
              [ | intro o;
                  apply (T2_fail_iff (r + (nN + 1)) [rev_buf arg1] r Hne2) ].
            apply tou_wexit_eq.
            - apply fd1chan_brk_model. apply fd1chan_with_vmmaps. exact Hfd0.
            - (* ret ; ld a1,8(sp) ; bne a1,a0 taken ; exit 4 *)
              apply to_wallexit_run. cbn [to_wallexit].
              eapply tw_step;
                [ reflexivity
                | eapply step_jalr_x0 with (tgt := (0x110c4 : word));
                  [ exact SF_11188 | reflexivity | exact SD_11188
                  | getr_resolve; exact F1 ]
                | norm_pc ].
              eapply tw_step;
                [ reflexivity
                | eapply step_ld with (bs := word_to_le_bytes 8 (r + (nN + 1)))
                                      (v := r + (nN + 1));
                  [ exact SF_110c4 | reflexivity | exact SD_110c4
                  | match goal with |- rdn _ _ ?a _ = _ =>
                      replace a with (Z_to_bv 64 (bv_unsigned rsp - 56))
                        by (getr_resolve; regupd_resolve; rewrite F2;
                            sp_norm; f_equal; lia) end;
                    apply rdn_wbytes_hit8; u_norm; lia
                  | exact (bytes_le_to_Z_8 _) ]
                | step_simpl ].
              eapply tw_step;
                [ reflexivity
                | eapply step_bne_tk;
                  [ exact SF_110c8 | reflexivity | exact SD_110c8
                  | getr_resolve; regupd_resolve;
                    apply c_eq_neq; rewrite Hurn1; lia ]
                | norm_pc ].
              apply source_exit4.
              + regupd_resolve. exact F2.
              + apply spill_ra.
              + apply spill_0.
            - (* no output on the failing resolution *)
              apply Forall_nil. }
        * (* set identity at the second node *)
          intro o.
          unfold ms_gpr; cbn [ms_regs].
          rewrite arg_reg_0, F10.
          change (T1 (init_reserved (segments_reserved RS) rmb rsp (in_kernel inp))
                     source_alloc_limit (bv_unsigned rsp - stack_max_size) (nN + 1)
                     [rev_buf arg1] r o <->
                  (exists r2,
                     brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved RS) rmb rsp
                                               (in_kernel inp))
                                 [] [] rbrk r source_alloc_limit rmb rsp)
                       (r + (nN + 1)) r2
                     /\ T2 (r + (nN + 1)) [rev_buf arg1] r2 o)).
          apply (T1_iff_T2 (init_reserved (segments_reserved RS) rmb rsp (in_kernel inp))
                   source_alloc_limit rbrk rmb rsp nN [rev_buf arg1] r);
            [ exact Hrnz | lia
            | rewrite u_nN; lia | rewrite u_nN; lia ]. }
  { (* set identity at the first node: the query resolves to rbrk only *)
    intro o.
    unfold ms_gpr; cbn [ms_regs].
    rewrite arg_reg_0, E10.
    apply (brkU_iff_T1 (init_reserved (segments_reserved RS) rmb rsp (in_kernel inp))
             source_alloc_limit (bv_unsigned rsp - stack_max_size) nN (rev_buf arg1) rbrk).
    - intro r0.
      change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved RS) rmb rsp
                                        (in_kernel inp))
                          [] [] rbrk rbrk source_alloc_limit rmb rsp)
                (Z_to_bv 64 0) r0 <-> r0 = rbrk).
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
      + rewrite Hun1. unfold page_size, source_alloc_limit. lia.
      + rewrite Hun1. unfold page_size. lia.
    - (* the grow amount cannot be the zero word *)
      intro Hc. apply (f_equal bv_unsigned) in Hc.
      rewrite Hun1 in Hc.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
Qed.

End Ge2Main.
End SourceProof.
