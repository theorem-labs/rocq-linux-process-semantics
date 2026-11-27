(** * alloc-join-ns source binary: per-binary derivations.

    PROOF-SIDE FILE (not part of the trusted specification).

    Deliverables (Section [SourceProof], generic over av/ev and the
    ASLR window sp):
    - [source_wexit_lt2]  : argc < 2                 -> to_wexit [] 2
    - [source_wexit_cap]  : argc >= 2, tot > 65536   -> to_wexit [] 3
    - [source_outcomes]   : argc >= 2, tot <= 65536  ->
        to_outcomes (the run's list) (init) (the run's initial model)
          (two_outcomes [] 4 [jout av] 0).

    gcc 15 / musl 1.2.6 binary: the argument lengths are measured by an
    out-of-line call to musl's word-at-a-time [strlen] (the gcc 9 build
    inlined the C [slen] byte loop).  The [Z]-level exactness of musl's
    has-zero test and the readability of the (NUL-straddling) word load
    live in Common/MuslStrlen.v; the per-instruction walk over the
    routine (0x111e8..0x11260) is below, pinned to this binary's
    addresses.

    Conventions: sp-relative values are in the canonical
    [Z_to_bv 64 (bv_unsigned rsp - k)] form, loop indices in
    [nat_to_word], the total byte count [tot] is the word
    [nat_to_word totn]; all range bookkeeping is [Z] over
    [bv_unsigned].

    The run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  The derivations step over the image's own [source_segs] and are
    carried to the run's list whole in [source_outcomes]
    ([RunSegmentsLift.msteps_run], [to_wallexit_run]): no instruction here
    fetches from the pair.  The states carry the run's rom.  The brk
    ledger of the run's initial model is [State.init_reserved]: the
    image's reservations, then the vDSO pair, which lies far above the
    heap ([run_ledger_free]).  The stack bounds come from the entry
    predicate's launch conjunct [Run.entry_launch_ok_va] and
    [Run.valid_launch]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec AllocSim WallSim MmapSim AllocSim2 StepTac ListFacts MuslStrlen StreamSim StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Common Require Import Footprint SymExec SymTac SymSide SymBranch.
From LinuxProcessSemantics.Examples.alloc_join_ns Require Import alloc_join_ns_code alloc_join_ns_defs.
From LinuxProcessSemantics.Examples.alloc_join_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.alloc_join_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them.  [fx0] itself is
    the instance, so every state here is [init_mkst]'s [@mkst fx0]. *)
#[local] Existing Instance fx0.

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x11190%N.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Reserved list and store legality                                   *)
(* ================================================================= *)

Lemma source_reserved_val :
  segments_reserved source_segs
  = [(0x10000, 0x1000); (0x11000, 0x1000); (0x12000, 0x1000); (0x13000, 0x1000)].
Proof. vm_refl. Qed.

(** Stores at/above the first writable address are legal.  The
    read-only part of the image spans THREE page-rounded segments --
    [0x10000, 0x11000) headers, [0x11000, 0x12000) text ([-z
    separate-code]), [0x12000, 0x13000) rodata/.eh_frame -- so a store
    is legal from 0x13000 up, where the writable data segment begins. *)
Lemma source_avoids_ro : forall (a : word) (n : Z), (0x13000 <= bv_unsigned a)%Z ->
  range_avoids_ro_segs source_segs (bv_unsigned a) n = true.
Proof.
  intros a n Ha.
  apply range_avoids_ro_above with (data_base := 0x13000%Z);
    [vm_compute; reflexivity | exact Ha].
Qed.

(** The source image's WRITABLE window: the rw- segment covers
    [0x13000, 0x14000) and the snapshot carries a byte for every address in
    it (.bss is zero-filled in the .hex), so [wview] is defined there
    whatever the overlay holds — a store into .data/.bss needs no
    prior write.  That is the [store_ok] side condition machine stores
    now carry; stack targets go through the RLIMIT_STACK window
    ([solve_store_ok]) instead. *)
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

(** A region [b, b+l) free against the page-rounded reservations avoids
    the read-only segment everywhere inside it.  Four reservations now:
    the free region lies entirely below 0x10000 or at/above 0x14000. *)
Lemma source_free_avoids : forall (b l : word),
  region_free (segments_reserved source_segs) b l = true ->
  (0 < bv_unsigned l)%Z ->
  forall (a k : Z), (bv_unsigned b <= a)%Z ->
  (a + k <= bv_unsigned b + bv_unsigned l)%Z ->
  range_avoids_ro_segs source_segs a k = true.
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
  change (bv_unsigned (0x10000 : word)) with 0x10000%Z in H0.
  change (bv_unsigned (0x1000 : word)) with 0x1000%Z in H0.
  change (bv_unsigned (0x11000 : word)) with 0x11000%Z in H1.
  change (bv_unsigned (0x1000 : word)) with 0x1000%Z in H1.
  change (bv_unsigned (0x12000 : word)) with 0x12000%Z in H2.
  change (bv_unsigned (0x1000 : word)) with 0x1000%Z in H2.
  change (bv_unsigned (0x13000 : word)) with 0x13000%Z in H3.
  change (bv_unsigned (0x1000 : word)) with 0x1000%Z in H3.
  apply andb_false_iff in H0. apply andb_false_iff in H1.
  apply andb_false_iff in H2. apply andb_false_iff in H3.
  assert (Hcase : (bv_unsigned b + bv_unsigned l <= 0x10000)%Z
                  \/ (0x14000 <= bv_unsigned b)%Z).
  { destruct H0 as [H0|H0]; destruct H1 as [H1|H1];
      destruct H2 as [H2|H2]; destruct H3 as [H3|H3];
      apply Z.ltb_ge in H0; apply Z.ltb_ge in H1;
      apply Z.ltb_ge in H2; apply Z.ltb_ge in H3; lia. }
  destruct Hcase as [Hc | Hc].
  - unfold range_avoids_ro_segs, source_segs, SourceMemImage_loaded_segments.
    cbn [forallb].
    change (seg_writable SourceMemImage_segment_000) with false.
    change (seg_writable SourceMemImage_segment_001) with false.
    change (seg_writable SourceMemImage_segment_002) with false.
    change (seg_writable SourceMemImage_segment_003) with true.
    change (Z.of_N (seg_base SourceMemImage_segment_000))%Z with 0x10000%Z.
    change (Z.of_N (seg_base SourceMemImage_segment_001))%Z with 0x11000%Z.
    change (Z.of_N (seg_base SourceMemImage_segment_002))%Z with 0x12000%Z.
    rewrite (proj2 (Z.ltb_ge 0x10000 (a + k))) by lia.
    rewrite (proj2 (Z.ltb_ge 0x11000 (a + k))) by lia.
    rewrite (proj2 (Z.ltb_ge 0x12000 (a + k))) by lia.
    cbn [negb orb andb]. reflexivity.
  - apply range_avoids_ro_above with (data_base := 0x13000%Z);
      [vm_compute; reflexivity | lia].
Qed.

(* ================================================================= *)
(* The proof, generic over argv/envp and the stack pointer             *)
(* ================================================================= *)

Section SourceProof.

Variable inp : ProcInput.
Local Abbreviation av := (in_argv inp).
Local Abbreviation ev := (in_envp inp).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.

Variable rsp : word.

(** The entry stack draw this run was started with
    ([Run.ExecEntry]'s [en_draw]): the 16 AT_RANDOM bytes the kernel
    picks afresh at every [execve], and the bytes of the entry stack's
    last page above the block.  This proof may assume NOTHING about
    either, exactly as it may assume nothing about where the stack
    landed.  Quantified per binary, so the target's draw below is a
    different variable. *)
Variable rrnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned rsp)%Z.
Hypothesis Hsp_hi : (bv_unsigned rsp <= sp_window_hi)%Z.

Lemma rsp_lo_num : (0x7fff80000000 <= bv_unsigned rsp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma rsp_hi_num : (bv_unsigned rsp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

(** The quantified initial program break ([Run.valid_brk] window, like the
    SP above).  Its page alignment exposes the kernel's physical [brk]
    grant while the binary continues to use only its logical byte prefix. *)
Variable rbrk : word.
Variable rmb : word.
Hypothesis Hvl : valid_launch inp.

(** The fifth conjunct of [Run.valid_entry_va]: this placement is one a
    Linux launch can give ([create_elf_tables] and [setup_arg_pages],
    fs/binfmt_elf.c and fs/exec.c, Linux v6.18.46).  With [Hvl] it bounds
    the entry block, places the argv strings below [ed_top] and the
    stack-store window. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry rsp rbrk rmb rrnd) inp.

(** The run's rom: the image's segments, then the vDSO pair. *)
Definition rrom : word -> option byte := seg_rom (run_segments source_segs inp rsp rmb).
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
(** The initial overlay, with the entry point [init_mkst] passes to it. *)
Definition wmem : word -> option byte :=
  wrap_mem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x11190)) rsp rrnd.

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
Proof.
  pose proof (valid_argv_len av Hva).
  unfold argcN, len_word. apply u_Z2bv; lia.
Qed.

Lemma argcN_le : (bv_unsigned argcN <= 1024)%Z.
Proof.
  rewrite u_argcN. apply valid_argv_len. exact Hva.
Qed.

(** No-overflow bound for the initial stack image, for any entry word. *)
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
  Z_to_bv 64 (bv_unsigned rsp + 16 + 8 * Z.of_nat (length av)).

(** The a2 chain _start computes ([a1 = sp+8], [t0 = argc << 3],
    [a2 = a1 + t0 + 8]) equals [envp_val]. *)
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

(** The register shift the crt's [slli t0,a0,3] compiles to, in the
    immediate-shift spelling the rest of the file uses.  The shift
    amount is a closed literal; only the shifted value is symbolic. *)
Lemma v_sll_3 : forall x : word, v_sll x (Z_to_bv 64 3) = v_slli x 3.
Proof. intro x. unfold v_sll, v_slli. f_equal. Qed.

(** [envp_val_eq] in the spelling a REFLECTIVE block leaves behind: the
    executor denotes the crt's four-instruction envp computation as an
    [alu64]/[v_sll] tree, and this is where it becomes [envp_val].
    Without it the exit memory is only CONVERTIBLE to [fmem], and making
    the unifier find that conversion costs minutes. *)
Lemma envp_val_sym :
  Z_to_bv 64 (bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
                                         (v_sll argcN (Z_to_bv 64 3))) + 8)
  = envp_val.
Proof. rewrite alu_add, v_sll_3. exact envp_val_eq. Qed.

(** Memory after _start's environ store. *)
Definition emem : word -> option byte :=
  wbytes wmem 0x13000 (word_to_le_bytes 8 envp_val).

(** main()'s 48-byte frame (stores in execution order; sp = rsp - 48):
    s1@+24 (rsp-24), ra@+40 (rsp-8, = 0x111bc), s0@+32 (rsp-16),
    s2@+16 (rsp-32), s3@+8 (rsp-40), s4@+0 (rsp-48). *)
Definition fmem : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes emem
    (Z_to_bv 64 (bv_unsigned rsp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))   (* sd s1, 24(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 8))  (word_to_le_bytes 8 (0x111bc : word))) (* sd ra, 40(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))   (* sd s0, 32(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))   (* sd s2, 16(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))   (* sd s3, 8(sp)  *)
    (Z_to_bv 64 (bv_unsigned rsp - 48)) (word_to_le_bytes 8 (Z_to_bv 64 0)).   (* sd s4, 0(sp)  *)

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
  = rdn source_segs
      (stack_to_mem rsp (entry_stack_image inp rmb source_phdrs
                           (Z_to_bv 64 (Z.of_N 0x11190)) rsp rrnd)) a n.
Proof. intros a n Ha Hn. apply rdn_wrap_stack_above; assumption. Qed.

(** argc at rsp. *)
Lemma read_argc_w :
  rdn source_segs wmem rsp 8%nat = Some (word_le8 argcN).
Proof.
  pose proof rsp_hi_num.
  rewrite rdn_wmem_stack by lia.
  apply read_argc. apply source_bsb_nw.
Qed.

(* ----------------------------------------------------------------- *)
(* Frame-slot read-back                                               *)
(* ----------------------------------------------------------------- *)

Lemma read_slot_ra :
  rdn source_segs fmem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
  = Some (word_to_le_bytes 8 (0x111bc : word)).
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. unfold fmem.
  repeat first
    [ rewrite rdn_wbytes_hit8 by (u_norm; lia)
    | rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; u_norm; lia)
    | rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; u_norm; lia) ].
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
          by (rewrite ?length_N_to_le_bytes; u_norm; lia)
      | rewrite rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes; u_norm; lia) ];
    reflexivity.
Qed.

(* ================================================================= *)
(* Epilogue: 0x11098 .. ret .. exit ecall                             *)
(* ================================================================= *)

(** From main's epilogue with ANY memory whose frame slots read back
    the initial values: exit with code = a0, no output. sp = rsp - 48. *)
Lemma source_epilogue : forall regs mem (code : word),
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 10 = code -> (bv_unsigned code < 256)%Z ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
  = Some (word_to_le_bytes 8 (0x111bc : word)) ->
  (forall a : word,
     In a [Z_to_bv 64 (bv_unsigned rsp - 16); Z_to_bv 64 (bv_unsigned rsp - 24);
           Z_to_bv 64 (bv_unsigned rsp - 32); Z_to_bv 64 (bv_unsigned rsp - 40);
           Z_to_bv 64 (bv_unsigned rsp - 48)] ->
     rdn source_segs mem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  to_wexit source_segs (mkst regs 0x11098 mem rrom) [] code.
(** NINE instructions in ONE reflective block: the six frame reloads,
    the stack pop, main's [ret] — literal because the reload of [ra] is
    NAMED in the read script — and the crt's [li a7,93] before the
    [exit] ecall.  The only pinned register is [sp]; what is left below
    is exactly the six [rdn] facts the caller supplies, in the
    executor's (reverse) order, plus the [sp] pin. *)
Proof.
  intros regs mem code H2 H10 Hc Hra Hsl.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  sym_block source_segs 9%nat (@nil bool)
    [ELit 0x111bc; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0]
    [((2 : reg), EVar 32)] [Z_to_bv 64 (bv_unsigned rsp - 48)] (@nil word) R HR.
  1: (exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hsl; right; right; right; right; left; reflexivity
      | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  1: (exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hsl; right; right; right; left; reflexivity
      | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  1: (exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hsl; right; right; left; reflexivity
      | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  1: (exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hsl; right; left; reflexivity
      | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  1: (exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hsl; left; reflexivity
      | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  1: (exists (word_to_le_bytes 8 (0x111bc : word)); split;
      [ exact Hra | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  { (* the [sp] pin *) exact H2. }
  (* 0x111c0: the exit [ecall] *)
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_111c0 eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HR. vm_compute. reflexivity.
  - sym_regs HR. first [ exact H10 | rewrite <- getr_nz by reg_neq_tac; exact H10 ].
  - exact Hc.
Qed.

(* ================================================================= *)
(* _start and main's prologue                                         *)
(* ================================================================= *)

(** argc < 2: no output, exit 2.  Unlike the gcc 9 build (bare [ret]
    with no frame), the frame is built BEFORE the argc test, so this
    path goes through the prologue and the shared epilogue. *)
Lemma source_wexit_lt2 : (length av < 2)%nat ->
  to_wexit source_segs
    (init_machine_state (run_segments source_segs inp rsp rmb) 0x11190 source_phdrs rsp rmb rrnd inp)
    [] (Z_to_bv 64 2).
(** TWENTY-TWO instructions in ONE reflective block: the whole crt
    entry sequence (gp setup, the [ld] of argc, the envp pointer
    arithmetic and its store into musl's [__environ] slot, the [jal]
    into main), main's frame push with its SIX spills, the
    [argc < 2] test and the [j] onto the shared epilogue at 0x11098.
    One branch, so one [SCBr]; one load and seven stores, so eight
    memory obligations.  The five callee-saved registers are PINNED to
    [ELit 0] so that their spilled values are literals, which is what
    makes the exit memory literally [fmem]. *)
Proof.
  intros Hlt2.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as HargcLe.
  pose proof u_argcN as Hu.
  rewrite init_mkst.
  sym_block source_segs 22%nat [true] (@nil expr)
    [((2 : reg), EVar 32); ((8 : reg), ELit 0); ((9 : reg), ELit 0);
     ((18 : reg), ELit 0); ((19 : reg), ELit 0); ((20 : reg), ELit 0)]
    [rsp] [argcN] RA HRA.
  { (* [bge s1,a0] at 0x11020 -> taken, because [argc <= 1] *) sym_br. }
  1-6: solve_store_ok.
  { (* [sd a2,0(t1)] at 0x111b4 -> musl's [__environ] slot at 0x13000 *)
    apply source_store_ok; u_norm; lia. }
  { (* [ld a0,0(sp)] at 0x11198 -> argc, out of the initial stack image *)
    replace (Z_to_bv 64 (bv_unsigned rsp + 0)) with rsp
      by (apply bv_eq; u_norm; lia);
    exists (word_le8 argcN); split;
      [ fold wmem; apply read_argc_w | apply bytes_le_n_to_le_8 ]. }
  match goal with
  | |- to_wexit _ (mkst _ _ ?M _) _ _ =>
      replace M with fmem
        by (unfold fmem, emem, wmem; rewrite envp_val_sym; reflexivity)
  end.
  apply source_epilogue.
  - sym_regs HRA. sym_close.
  - sym_regs HRA. sym_close.
  - u_norm; lia.
  - apply read_slot_ra.
  - apply read_slot_0.
Qed.

(* ================================================================= *)
(* General per-argument reads (index k)                               *)
(* ================================================================= *)

Definition sptr (k : nat) : word := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k.

Lemma sptr_bounds : forall k, (k < length av)%nat ->
  (bv_unsigned rsp <= bv_unsigned (sptr k))%Z /\
  (bv_unsigned (sptr k) + Z.of_nat (length (nth k av [])) + 1 < 2^64)%Z.
Proof.
  intros k Hk. unfold sptr.
  exact (argv_ptr_bounds Sv48 inp rmb rsp rbrk rrnd k Hlau Hk).
Qed.

(** [sptr_bounds] restated over [cat_argv_ptr] (the strlen walk below
    spells the pointer out). *)
Lemma source_ptr_bounds : forall k, (k < length av)%nat ->
  (bv_unsigned rsp <= bv_unsigned (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k))%Z /\
  (bv_unsigned (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)
     + Z.of_nat (length (nth k av [])) + 1 < 2^64)%Z.
Proof. intros k Hk. exact (sptr_bounds k Hk). Qed.

Lemma read_arg_ptr_f : forall k, (k < length av)%nat ->
  rdn source_segs fmem (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat k)) 8%nat
  = Some (word_le8 (sptr k)).
Proof.
  intros k Hk. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as Hlen.
  assert (HkZ : (Z.of_nat k <= 1024)%Z) by lia.
  replace (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat k))
    with (rsp + nat_to_word (8 + 8 * k)) by (rewrite word_add_nat; f_equal; lia).
  rewrite rdn_fmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
  unfold sptr. apply read_argv_ptr_k; [assumption | apply source_bsb_nw].
Qed.

Lemma read_arg_byte_f : forall k j, (k < length av)%nat ->
  (j <= length (nth k av []))%nat ->
  rdn source_segs fmem (sptr k + nat_to_word j) 1%nat
  = Some [byte_at (nth k av []) j].
Proof.
  intros k j Hk Hj.
  destruct (sptr_bounds k Hk) as [Hge Hup].
  pose proof (valid_argv_str_len av k Hva Hk) as Hslen.
  pose proof (u64_range rsp). pose proof (u64_range (sptr k)).
  rewrite rdn_fmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
  unfold sptr, byte_at.
  apply (read_argv_byte_k Sv48 source_segs inp rmb source_phdrs _ rsp rbrk rrnd k j Hlau);
    [exact Hk | exact Hj].
Qed.

Lemma arg_nz_k : forall k, (k < length av)%nat -> ~ In (Z_to_bv 8 0) (nth k av []).
Proof. intros k Hk. apply valid_argv_str_nz; assumption. Qed.

(** Room for a whole word past ANY offset inside argv string [k] but the
    last: the NUL, the exec name and its NUL and the 8-byte slot lie
    above it, so at least 9 bytes (Linux v6.18.46 fs/exec.c:1831-1840,
    mm/vma_exec.c:150; instance of MuslStrlen's [argv_ptr_room]). *)
Lemma source_ptr_room : forall k, (k < length av)%nat ->
  (bv_unsigned (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)
     + Z.of_nat (length (nth k av [])) + 9
   <= bv_unsigned rsp
      + Z.of_nat (length (entry_stack_image inp rmb source_phdrs
                            (Z_to_bv 64 (Z.of_N 0x11190)) rsp rrnd)))%Z.
Proof. intros k Hk. eapply argv_ptr_room; eassumption. Qed.

(* ================================================================= *)
(* The mem_ok abstraction.                                            *)
(*                                                                    *)
(* grep_args_ns threads its strlen walk through memories that agree   *)
(* with [fmem] outside a scratch window (its write wrapper stores     *)
(* between calls).  In THIS binary strlen is only ever called from    *)
(* the length loop, before any store, so the memory is always exactly *)
(* [fmem]; [mem_ok] degenerates to that, and the walk's text ports    *)
(* unchanged.                                                         *)
(* ================================================================= *)

Definition mem_ok (mem : word -> option byte) : Prop := mem = fmem.

Lemma fmem_ok : mem_ok fmem.
Proof. reflexivity. Qed.

Lemma read_str_byte_m : forall mem, mem_ok mem -> forall k j,
  (k < length av)%nat -> (j <= length (nth k av []))%nat ->
  rdn source_segs mem (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word j) 1%nat
  = Some [byte_at (nth k av []) j].
Proof.
  intros mem Hm k j Hk Hj. unfold mem_ok in Hm. subst mem.
  exact (read_arg_byte_f k j Hk Hj).
Qed.

(** An 8-byte load at offset [m] inside argv string [k] never faults:
    peel this binary's frame overlay off down to [wmem = wrap_mem ...],
    then hand off to MuslStrlen's [argv_word_readable] (which is where
    the argument about the bytes above the argv strings lives). *)
Lemma read_word_m : forall mem, mem_ok mem -> forall k m,
  (k < length av)%nat -> (m <= length (nth k av []))%nat ->
  exists bs, length bs = 8%nat /\
    rdn source_segs mem (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word m) 8%nat
    = Some bs.
Proof.
  intros mem Hmk k m Hk Hm. unfold mem_ok in Hmk. subst mem.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  destruct (source_ptr_bounds k Hk) as [Hge Hup].
  pose proof (source_ptr_room k Hk) as Hroom.
  pose proof (source_bsb_nw (Z_to_bv 64 (Z.of_N 0x11190))) as Hnw.
  pose proof (u64_range (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)).
  assert (Hu : bv_unsigned (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word m)
               = (bv_unsigned (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k) + Z.of_nat m)%Z)
    by (rewrite word_add_nat; apply u_Z2bv; lia).
  destruct (argv_word_readable source_segs Sv48 inp rmb source_phdrs
              (Z_to_bv 64 (Z.of_N 0x11190)) rsp rbrk rrnd Hvl Hlau Hsp_lo Hsp_hi k m Hk Hm)
    as [bs [Hl Hr]].
  exists bs. split; [exact Hl|].
  rewrite rdn_fmem_above by (rewrite Hu; lia).
  exact Hr.
Qed.

(** Its bytes, as far as the NUL (MuslStrlen's [word_bytes_nth] fed with
    this binary's overlay-relative byte-read lemma). *)
Lemma read_word_nth : forall mem, mem_ok mem -> forall k m bs j,
  (k < length av)%nat ->
  rdn source_segs mem (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word m) 8%nat = Some bs ->
  (j < 8)%nat -> (m + j <= length (nth k av []))%nat ->
  nth j bs (Z_to_bv 8 0) = byte_at (nth k av []) (m + j).
Proof.
  intros mem Hmk k m bs j Hk Hr Hj Hmj.
  apply (word_bytes_nth source_segs mem (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)
           (nth k av []) m bs j Hr);
    [ intros i Hi; apply read_str_byte_m; assumption
    | exact Hj | exact Hmj ].
Qed.

(** [addi rd, rs, 8] over a symbolic base. *)
Lemma v_addi_8 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word m) 8 = a + nat_to_word (m + 8).
Proof.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* ================================================================= *)
(* musl strlen (0x111e8)                                              *)
(*                                                                    *)
(* gcc 15 recognizes the source's [slen] loop and emits a call to      *)
(* musl's [strlen], which is                                          *)
(*                                                                    *)
(*   0x111f4  byte scan until the pointer is 8-aligned (or a NUL)      *)
(*   0x11234  word-at-a-time scan, stopping at the word that holds     *)
(*            a zero byte (test proved exact in module [HZ])           *)
(*   0x11254  byte scan inside that word, down to the NUL              *)
(*   0x1125c  a0 := a5 - a0                                           *)
(*                                                                    *)
(* Instruction for instruction this is grep_args_ns's routine at a     *)
(* uniform +0x50 shift.  The word load may straddle the NUL;           *)
(* [read_word_m] shows the read is always inside the initial stack     *)
(* image, and the bytes past the NUL never matter (a zero byte         *)
(* anywhere stops the loop).                                          *)
(* ================================================================= *)

(** The exit tail 0x1125c: a0 := a5 - a0 = length, then [ret]. *)
Lemma source_strlen_tail : forall k, (k < length av)%nat ->
  forall mem regs (RA : word), v_jalr RA 0 = RA ->
  reg_get regs 10 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k ->
  reg_get regs 15 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k
                    + nat_to_word (length (nth k av [])) ->
  reg_get regs 1 = RA ->
  exists regs',
    (forall r : reg, r <> 10 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 10 = nat_to_word (length (nth k av [])) /\
    msteps source_segs (mkst regs 0x1125c mem rrom) (mkst regs' RA mem rrom).
Proof.
  intros k Hk mem regs RA Hvj Hr10 Hr15 Hr1.
  destruct (source_ptr_bounds k Hk) as [Hge Hup].
  pose proof (valid_argv_str_len av k Hva Hk) as Hslen.
  set (ptr := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k) in *.
  set (regs1 := regupd regs 10 (nat_to_word (length (nth k av [])))).
  assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x1125c mem rrom)
               = MachineOk (mkst regs1 0x11260 mem rrom)).
  { rewrite (step_sub source_segs regs 0x1125c mem rrom _ 10 15 10
               SF_1125c eq_refl SD_1125c).
    reduce_bv_eqb_ifs. getr_resolve. rewrite Hr10, Hr15.
    unfold regs1.
    replace (v_sub (ptr + nat_to_word (length (nth k av []))) ptr)
      with (nat_to_word (length (nth k av []))).
    2:{ unfold v_sub. rewrite word_add_nat.
        rewrite u_Z2bv by (pose proof (u64_range ptr); lia).
        unfold nat_to_word. f_equal. lia. }
    wlits. reflexivity. }
  assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x11260 mem rrom)
               = MachineOk (mkst regs1 RA mem rrom)).
  { rewrite (step_jalr_x0 source_segs regs1 0x11260 mem rrom _ 1 _ RA
               SF_11260 eq_refl SD_11260).
    - imm_norm. rewrite Hvj. reflexivity.
    - unfold regs1. getr_resolve. exact Hr1. }
  exists regs1. split; [|split].
  - intros r Hr. unfold regs1. rewrite regupd_other by assumption. reflexivity.
  - unfold regs1. apply regupd_same.
  - eapply mst_step; [reflexivity | exact E1 |].
    eapply mst_step; [reflexivity | exact E2 |].
    apply mst_refl.
Qed.

(** The final byte scan 0x11254, from offset [j]. *)
Lemma source_strlen_scan : forall k, (k < length av)%nat ->
  forall mem, mem_ok mem ->
  forall (RA : word), v_jalr RA 0 = RA ->
  forall d j regs,
  (j + d = length (nth k av []))%nat ->
  reg_get regs 10 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k ->
  reg_get regs 15 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word j ->
  reg_get regs 1 = RA ->
  exists regs',
    (forall r : reg, r <> 10 -> r <> 14 -> r <> 15 ->
       reg_get regs' r = reg_get regs r) /\
    reg_get regs' 10 = nat_to_word (length (nth k av [])) /\
    msteps source_segs (mkst regs 0x11254 mem rrom) (mkst regs' RA mem rrom).
Proof.
  intros k Hk mem Hmem RA Hvj.
  pose proof (source_ptr_bounds k Hk) as [Hge Hup].
  pose proof (valid_argv_str_len av k Hva Hk) as Hslen.
  pose proof (valid_argv_str_nz av k Hva Hk) as Hsnz.
  set (ptr := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k) in *.
  set (s := nth k av []) in *.
  induction d as [|d IH]; intros j regs Hjd Hr10 Hr15 Hr1.
  - (* j = length s: the byte is the NUL *)
    assert (Hj : j = length s) by lia.
    set (regs1 := regupd regs 14 (Z_to_bv 64 0)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11254 mem rrom)
                 = MachineOk (mkst regs1 0x11258 mem rrom)).
    { rewrite (step_lbu source_segs regs 0x11254 mem rrom _ 14 15 _ (Z_to_bv 8 0)
                 SF_11254 eq_refl SD_11254).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - getr_resolve. rewrite Hr15, v_addi_0.
        pose proof (read_str_byte_m mem Hmem k j Hk ltac:(unfold s in Hjd; lia)) as Hrd.
        assert (Hb0 : byte_at (nth k av []) j = Z_to_bv 8 0)
          by (unfold s in Hj; rewrite Hj; apply byte_at_len).
        rewrite Hb0 in Hrd. exact Hrd. }
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x11258 mem rrom)
                 = MachineOk (mkst regs1 0x1125c mem rrom)).
    { rewrite (step_bne_ft source_segs regs1 0x11258 mem rrom _ 14 0 _
                 SF_11258 eq_refl SD_11258).
      - wlits. reflexivity.
      - unfold regs1. getr_resolve. exact c_eq_0_true. }
    assert (Hr10' : reg_get regs1 10 = ptr)
      by (unfold regs1; regupd_resolve; exact Hr10).
    assert (Hr15' : reg_get regs1 15 = ptr + nat_to_word (length (nth k av [])))
      by (unfold regs1; regupd_resolve; rewrite Hr15; unfold s in Hj; rewrite Hj;
          reflexivity).
    assert (Hr1' : reg_get regs1 1 = RA)
      by (unfold regs1; regupd_resolve; exact Hr1).
    destruct (source_strlen_tail k Hk mem regs1 RA Hvj Hr10' Hr15' Hr1')
      as [regs' [Hag [H10 Hms]]].
    exists regs'. split; [|split].
    + intros r Hx10 Hx14 Hx15. rewrite (Hag r Hx10).
      unfold regs1. rewrite regupd_other by assumption. reflexivity.
    + exact H10.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      exact Hms.
  - (* j < length s: the byte is nonzero, advance *)
    assert (Hjlt : (j < length s)%nat) by lia.
    set (b := byte_at s j).
    assert (Hbnz : b <> Z_to_bv 8 0)
      by (apply byte_at_nz; [exact Hsnz | exact Hjlt]).
    set (regs1 := regupd regs 14 (Z_to_bv 64 (bv_unsigned b))).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11254 mem rrom)
                 = MachineOk (mkst regs1 0x11258 mem rrom)).
    { rewrite (step_lbu source_segs regs 0x11254 mem rrom _ 14 15 _ b
                 SF_11254 eq_refl SD_11254).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - getr_resolve. rewrite Hr15, v_addi_0.
        unfold b, ptr, s. apply (read_str_byte_m mem Hmem);
          [exact Hk | unfold s in Hjlt; lia]. }
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x11258 mem rrom)
                 = MachineOk (mkst regs1 0x11250 mem rrom)).
    { rewrite (step_bne_tk source_segs regs1 0x11258 mem rrom _ 14 0 _
                 SF_11258 eq_refl SD_11258).
      - wlits. reflexivity.
      - unfold regs1. getr_resolve.
        apply c_eq_0_false. rewrite u_zext8. apply byte_nz_u. exact Hbnz. }
    set (regs2 := regupd regs1 15 (ptr + nat_to_word (S j))).
    assert (E3 : RiscvSemantics.step source_segs (mkst regs1 0x11250 mem rrom)
                 = MachineOk (mkst regs2 0x11254 mem rrom)).
    { rewrite (step_addi source_segs regs1 0x11250 mem rrom _ 15 15 _
                 SF_11250 eq_refl SD_11250).
      reduce_bv_eqb_ifs.
      unfold regs2, regs1. getr_resolve. rewrite Hr15.
      rewrite word_add_nat_1. wlits. reflexivity. }
    assert (Hr10' : reg_get regs2 10 = ptr)
      by (unfold regs2, regs1; regupd_resolve; exact Hr10).
    assert (Hr15' : reg_get regs2 15 = ptr + nat_to_word (S j))
      by (unfold regs2; apply regupd_same).
    assert (Hr1' : reg_get regs2 1 = RA)
      by (unfold regs2, regs1; regupd_resolve; exact Hr1).
    destruct (IH (S j) regs2 ltac:(lia) Hr10' Hr15' Hr1')
      as [regs' [Hag [H10 Hms]]].
    exists regs'. split; [|split].
    + intros r Hx10 Hx14 Hx15. rewrite (Hag r Hx10 Hx14 Hx15).
      unfold regs2, regs1. rewrite !regupd_other by assumption. reflexivity.
    + exact H10.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      exact Hms.
Qed.

(** The word-loop body 0x11234..0x11248: load the word at [ptr+m] and
    compute musl's has-zero test into a4. *)
Lemma source_strlen_word_body : forall k, (k < length av)%nat ->
  forall mem, mem_ok mem -> forall m regs,
  (m <= length (nth k av []))%nat ->
  reg_get regs 15 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word m ->
  reg_get regs 11 = Z_to_bv 64 18374403900871474943 ->
  reg_get regs 12 = Z_to_bv 64 9259542123273814144 ->
  exists regs1 bs,
    msteps source_segs (mkst regs 0x11234 mem rrom)
                       (mkst regs1 0x11248 mem rrom) /\
    length bs = 8%nat /\
    (forall j, (j < 8)%nat -> (m + j <= length (nth k av []))%nat ->
       nth j bs (Z_to_bv 8 0) = byte_at (nth k av []) (m + j)) /\
    (forall r : reg, r <> 13 -> r <> 14 -> reg_get regs1 r = reg_get regs r) /\
    bv_unsigned (reg_get regs1 14) = HZ.Tz (bytes_le_to_Z bs).
Proof.
  intros k Hk mem Hmem m regs Hm Hr15 Hr11 Hr12.
  destruct (read_word_m mem Hmem k m Hk Hm) as [bs [Hlenb Hread]].
  pose proof (bytes_le_to_Z_range bs Hlenb) as Hrange.
  eexists. exists bs. split.
  {
    eapply mst_step;
      [ reflexivity
      | eapply step_ld with (bs := bs) (v := Z_to_bv 64 (bytes_le_to_Z bs));
        [ exact SF_11234 | reflexivity | exact SD_11234
        | getr_resolve; rewrite Hr15, v_addi_0; exact Hread
        | symmetry; apply u_Z2bv; lia ]
      | step_simpl ].
    stepi SF_11238 SD_11238.
    stepi SF_1123c SD_1123c.
    stepi SF_11240 SD_11240.
    stepi SF_11244 SD_11244.
    apply mst_refl. }
  repeat split.
  - exact Hlenb.
  - intros j Hj Hmj. exact (read_word_nth mem Hmem k m bs j Hk Hread Hj Hmj).
  - intros r H13 H14. rewrite !regupd_other by assumption. reflexivity.
  - regupd_resolve. getr_resolve. rewrite Hr11, Hr12. imm_norm.
    rewrite v_haszero. f_equal. apply u_Z2bv; lia.
Qed.

(** Leaving the word loop at 0x11248 (a4 <> 0: the word holds a NUL). *)
Lemma source_strlen_word_exit : forall k, (k < length av)%nat ->
  forall mem, mem_ok mem -> forall (RA : word), v_jalr RA 0 = RA ->
  forall m regs,
  (m <= length (nth k av []))%nat ->
  bv_unsigned (reg_get regs 14) <> 0%Z ->
  reg_get regs 10 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k ->
  reg_get regs 15 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word m ->
  reg_get regs 1 = RA ->
  exists regs',
    (forall r : reg, r <> 10 -> r <> 14 -> r <> 15 ->
       reg_get regs' r = reg_get regs r) /\
    reg_get regs' 10 = nat_to_word (length (nth k av [])) /\
    msteps source_segs (mkst regs 0x11248 mem rrom) (mkst regs' RA mem rrom).
Proof.
  intros k Hk mem Hmem RA Hvj m regs Hm Ha4 Hr10 Hr15 Hr1.
  assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11248 mem rrom)
               = MachineOk (mkst regs 0x1124c mem rrom)).
  { rewrite (step_beq_ft source_segs regs 0x11248 mem rrom _ 14 0 _
               SF_11248 eq_refl SD_11248).
    - wlits. reflexivity.
    - getr_resolve. apply c_eq_0_false. exact Ha4. }
  assert (E2 : RiscvSemantics.step source_segs (mkst regs 0x1124c mem rrom)
               = MachineOk (mkst regs 0x11254 mem rrom)).
  { rewrite (step_jal_x0 source_segs regs 0x1124c mem rrom _ _
               SF_1124c eq_refl SD_1124c).
    wlits. reflexivity. }
  destruct (source_strlen_scan k Hk mem Hmem RA Hvj
              (length (nth k av []) - m)%nat m regs ltac:(lia) Hr10 Hr15 Hr1)
    as [regs' [Hag [H10 Hms]]].
  exists regs'. split; [|split].
  - exact Hag.
  - exact H10.
  - eapply mst_step; [reflexivity | exact E1 |].
    eapply mst_step; [reflexivity | exact E2 |].
    exact Hms.
Qed.

(** The word-at-a-time loop 0x11234, from offset [m]. *)
Lemma source_strlen_word : forall k, (k < length av)%nat ->
  forall mem, mem_ok mem -> forall (RA : word), v_jalr RA 0 = RA ->
  forall f m regs,
  (length (nth k av []) - m <= f)%nat ->
  (m <= length (nth k av []))%nat ->
  reg_get regs 10 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k ->
  reg_get regs 15 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word m ->
  reg_get regs 11 = Z_to_bv 64 18374403900871474943 ->
  reg_get regs 12 = Z_to_bv 64 9259542123273814144 ->
  reg_get regs 1 = RA ->
  exists regs',
    (forall r : reg, r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 ->
       r <> 15 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 10 = nat_to_word (length (nth k av [])) /\
    msteps source_segs (mkst regs 0x11234 mem rrom) (mkst regs' RA mem rrom).
Proof.
  intros k Hk mem Hmem RA Hvj.
  pose proof (valid_argv_str_nz av k Hva Hk) as Hsnz.
  induction f as [|f IH]; intros m regs Hf Hm Hr10 Hr15 Hr11 Hr12 Hr1;
    destruct (source_strlen_word_body k Hk mem Hmem m regs Hm Hr15 Hr11 Hr12)
      as [regs1 [bs [Hms1 [Hlenb [Hnthb [Hag1 Ha4]]]]]];
    pose proof (bytes_le_to_Z_range bs Hlenb) as Hrange;
    [ | destruct (le_lt_dec (m + 8) (length (nth k av []))) as [Hle | Hlt] ].
  - (* fuel exhausted: m = length s, so the word starts at the NUL *)
    assert (Hm0 : m = length (nth k av [])) by lia.
    assert (Hnz : bv_unsigned (reg_get regs1 14) <> 0%Z).
    { rewrite Ha4. apply (HZ.Tz_haszero _ (length (nth k av []) - m)%nat);
        [ exact Hrange | lia | | ].
      - rewrite zb_of_bytes by lia. rewrite Hnthb by lia.
        replace (m + (length (nth k av []) - m))%nat with (length (nth k av []))
          by lia.
        rewrite byte_at_len. exact u8_zero.
      - intros j Hj. rewrite zb_of_bytes by lia. rewrite Hnthb by lia.
        apply byte_nz_u. apply byte_at_nz; [exact Hsnz | lia]. }
    assert (Hr10' : reg_get regs1 10 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)
      by (rewrite Hag1 by reg_neq_tac; exact Hr10).
    assert (Hr15' : reg_get regs1 15 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word m)
      by (rewrite Hag1 by reg_neq_tac; exact Hr15).
    assert (Hr1' : reg_get regs1 1 = RA)
      by (rewrite Hag1 by reg_neq_tac; exact Hr1).
    destruct (source_strlen_word_exit k Hk mem Hmem RA Hvj m regs1 Hm Hnz
                Hr10' Hr15' Hr1') as [regs' [Hag [H10 Hms]]].
    exists regs'. split; [|split].
    + intros r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15.
      rewrite (Hag r Hx10 Hx14 Hx15). apply Hag1; assumption.
    + exact H10.
    + eapply msteps_trans; [exact Hms1 | exact Hms].
  - (* the whole word is inside the string: keep going *)
    assert (Hz : bv_unsigned (reg_get regs1 14) = 0%Z).
    { rewrite Ha4. apply HZ.Tz_nozero; [exact Hrange|].
      intros i Hi. rewrite zb_of_bytes by lia. rewrite Hnthb by lia.
      apply byte_nz_u. apply byte_at_nz; [exact Hsnz | lia]. }
    assert (E1 : RiscvSemantics.step source_segs (mkst regs1 0x11248 mem rrom)
                 = MachineOk (mkst regs1 0x11230 mem rrom)).
    { rewrite (step_beq_tk source_segs regs1 0x11248 mem rrom _ 14 0 _
                 SF_11248 eq_refl SD_11248).
      - wlits. reflexivity.
      - getr_resolve. apply c_eq_0_of_u. exact Hz. }
    set (regs2 := regupd regs1 15
           (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word (m + 8))).
    assert (Hr15' : reg_get regs1 15
                    = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word m)
      by (rewrite Hag1 by reg_neq_tac; exact Hr15).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x11230 mem rrom)
                 = MachineOk (mkst regs2 0x11234 mem rrom)).
    { rewrite (step_addi source_segs regs1 0x11230 mem rrom _ 15 15 _
                 SF_11230 eq_refl SD_11230).
      reduce_bv_eqb_ifs.
      unfold regs2. getr_resolve. rewrite Hr15'.
      rewrite v_addi_8. wlits. reflexivity. }
    assert (Hr10' : reg_get regs2 10 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)
      by (unfold regs2; regupd_resolve; rewrite Hag1 by reg_neq_tac; exact Hr10).
    assert (Hr15'' : reg_get regs2 15
                     = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word (m + 8))
      by (unfold regs2; apply regupd_same).
    assert (Hr11' : reg_get regs2 11 = Z_to_bv 64 18374403900871474943)
      by (unfold regs2; regupd_resolve; rewrite Hag1 by reg_neq_tac; exact Hr11).
    assert (Hr12' : reg_get regs2 12 = Z_to_bv 64 9259542123273814144)
      by (unfold regs2; regupd_resolve; rewrite Hag1 by reg_neq_tac; exact Hr12).
    assert (Hr1' : reg_get regs2 1 = RA)
      by (unfold regs2; regupd_resolve; rewrite Hag1 by reg_neq_tac; exact Hr1).
    destruct (IH (m + 8)%nat regs2 ltac:(lia) ltac:(lia) Hr10' Hr15'' Hr11' Hr12'
                Hr1') as [regs' [Hag [H10 Hms]]].
    exists regs'. split; [|split].
    + intros r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15.
      rewrite (Hag r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15).
      unfold regs2. rewrite regupd_other by assumption.
      apply Hag1; assumption.
    + exact H10.
    + eapply msteps_trans; [exact Hms1 |].
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      exact Hms.
  - (* the NUL is inside this word: leave the loop *)
    assert (Hnz : bv_unsigned (reg_get regs1 14) <> 0%Z).
    { rewrite Ha4. apply (HZ.Tz_haszero _ (length (nth k av []) - m)%nat);
        [ exact Hrange | lia | | ].
      - rewrite zb_of_bytes by lia. rewrite Hnthb by lia.
        replace (m + (length (nth k av []) - m))%nat with (length (nth k av []))
          by lia.
        rewrite byte_at_len. exact u8_zero.
      - intros j Hj. rewrite zb_of_bytes by lia. rewrite Hnthb by lia.
        apply byte_nz_u. apply byte_at_nz; [exact Hsnz | lia]. }
    assert (Hr10' : reg_get regs1 10 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)
      by (rewrite Hag1 by reg_neq_tac; exact Hr10).
    assert (Hr15' : reg_get regs1 15 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word m)
      by (rewrite Hag1 by reg_neq_tac; exact Hr15).
    assert (Hr1' : reg_get regs1 1 = RA)
      by (rewrite Hag1 by reg_neq_tac; exact Hr1).
    destruct (source_strlen_word_exit k Hk mem Hmem RA Hvj m regs1 Hm Hnz
                Hr10' Hr15' Hr1') as [regs' [Hag [H10 Hms]]].
    exists regs'. split; [|split].
    + intros r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15.
      rewrite (Hag r Hx10 Hx14 Hx15). apply Hag1; assumption.
    + exact H10.
    + eapply msteps_trans; [exact Hms1 | exact Hms].
Qed.

(** The constant setup 0x11208..0x1122c, entering the word loop. *)
Lemma source_strlen_setup : forall mem regs,
  exists regs',
    msteps source_segs (mkst regs 0x11208 mem rrom)
                       (mkst regs' 0x11234 mem rrom) /\
    (forall r : reg, r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 ->
       reg_get regs' r = reg_get regs r) /\
    reg_get regs' 11 = Z_to_bv 64 18374403900871474943 /\
    reg_get regs' 12 = Z_to_bv 64 9259542123273814144.
Proof.
  intros mem regs. eexists. split.
  {
    stepi SF_11208 SD_11208.
    stepi SF_1120c SD_1120c.
    stepi SF_11210 SD_11210.
    stepi SF_11214 SD_11214.
    stepi SF_11218 SD_11218.
    stepi SF_1121c SD_1121c.
    stepi SF_11220 SD_11220.
    stepi SF_11224 SD_11224.
    stepi SF_11228 SD_11228.
    stepj SF_1122c SD_1122c.
    apply mst_refl. }
  repeat split.
  - intros r H11 H12 H13 H14. rewrite !regupd_other by assumption. reflexivity.
  - regupd_resolve. getr_resolve. bveq.
  - regupd_resolve. getr_resolve. bveq.
Qed.

(** Setup + word loop, entered at 0x11208 with a5 = ptr + j. *)
Lemma source_strlen_from_aligned : forall k, (k < length av)%nat ->
  forall mem, mem_ok mem -> forall (RA : word), v_jalr RA 0 = RA ->
  forall j regs,
  (j <= length (nth k av []))%nat ->
  reg_get regs 10 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k ->
  reg_get regs 15 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word j ->
  reg_get regs 1 = RA ->
  exists regs',
    (forall r : reg, r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 ->
       r <> 15 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 10 = nat_to_word (length (nth k av [])) /\
    msteps source_segs (mkst regs 0x11208 mem rrom) (mkst regs' RA mem rrom).
Proof.
  intros k Hk mem Hmem RA Hvj j regs Hj Hr10 Hr15 Hr1.
  destruct (source_strlen_setup mem regs) as [regsC [HmsC [HagC [H11 H12]]]].
  assert (Hr10C : reg_get regsC 10 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)
    by (rewrite HagC by reg_neq_tac; exact Hr10).
  assert (Hr15C : reg_get regsC 15 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word j)
    by (rewrite HagC by reg_neq_tac; exact Hr15).
  assert (Hr1C : reg_get regsC 1 = RA)
    by (rewrite HagC by reg_neq_tac; exact Hr1).
  destruct (source_strlen_word k Hk mem Hmem RA Hvj
              (length (nth k av []) - j)%nat j regsC ltac:(lia) Hj
              Hr10C Hr15C H11 H12 Hr1C) as [regs' [Hag [H10 Hms]]].
  exists regs'. split; [|split].
  - intros r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15.
    rewrite (Hag r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15). apply HagC; assumption.
  - exact H10.
  - eapply msteps_trans; [exact HmsC | exact Hms].
Qed.

(** The alignment byte scan 0x111f4, from offset [j]. *)
Lemma source_strlen_align : forall k, (k < length av)%nat ->
  forall mem, mem_ok mem ->
  forall (RA : word), v_jalr RA 0 = RA ->
  forall d j regs,
  (j + d = length (nth k av []))%nat ->
  reg_get regs 10 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k ->
  reg_get regs 15 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word j ->
  reg_get regs 1 = RA ->
  exists regs',
    (forall r : reg, r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 ->
       r <> 15 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 10 = nat_to_word (length (nth k av [])) /\
    msteps source_segs (mkst regs 0x111f4 mem rrom) (mkst regs' RA mem rrom).
Proof.
  intros k Hk mem Hmem RA Hvj.
  pose proof (source_ptr_bounds k Hk) as [Hge Hup].
  pose proof (valid_argv_str_len av k Hva Hk) as Hslen.
  pose proof (valid_argv_str_nz av k Hva Hk) as Hsnz.
  set (ptr := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k) in *.
  set (s := nth k av []) in *.
  induction d as [|d IH]; intros j regs Hjd Hr10 Hr15 Hr1.
  - (* j = length s *)
    assert (Hj : j = length s) by lia.
    set (regs1 := regupd regs 14 (v_andi (ptr + nat_to_word j) 7)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x111f4 mem rrom)
                 = MachineOk (mkst regs1 0x111f8 mem rrom)).
    { rewrite (step_andi source_segs regs 0x111f4 mem rrom _ 14 15 _
                 SF_111f4 eq_refl SD_111f4).
      reduce_bv_eqb_ifs. unfold regs1. getr_resolve. rewrite Hr15.
      imm_norm. wlits. reflexivity. }
    assert (Hr10' : reg_get regs1 10 = ptr)
      by (unfold regs1; regupd_resolve; exact Hr10).
    assert (Hr15' : reg_get regs1 15 = ptr + nat_to_word j)
      by (unfold regs1; regupd_resolve; exact Hr15).
    assert (Hr1' : reg_get regs1 1 = RA)
      by (unfold regs1; regupd_resolve; exact Hr1).
    destruct (Z.eq_dec (bv_unsigned (v_andi (ptr + nat_to_word j) 7)) 0%Z)
      as [Halg | Halg].
    + (* aligned: enter the word loop *)
      assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x111f8 mem rrom)
                   = MachineOk (mkst regs1 0x11208 mem rrom)).
      { rewrite (step_beq_tk source_segs regs1 0x111f8 mem rrom _ 14 0 _
                   SF_111f8 eq_refl SD_111f8).
        - wlits. reflexivity.
        - unfold regs1. getr_resolve. apply c_eq_0_of_u. exact Halg. }
      destruct (source_strlen_from_aligned k Hk mem Hmem RA Hvj j regs1
                  ltac:(unfold s in Hj; lia) Hr10' Hr15' Hr1')
        as [regs' [Hag [H10 Hms]]].
      exists regs'. split; [|split].
      * intros r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15.
        rewrite (Hag r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15).
        unfold regs1. rewrite regupd_other by assumption. reflexivity.
      * exact H10.
      * eapply mst_step; [reflexivity | exact E1 |].
        eapply mst_step; [reflexivity | exact E2 |].
        exact Hms.
    + (* unaligned: read the byte -- it is the NUL *)
      assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x111f8 mem rrom)
                   = MachineOk (mkst regs1 0x111fc mem rrom)).
      { rewrite (step_beq_ft source_segs regs1 0x111f8 mem rrom _ 14 0 _
                   SF_111f8 eq_refl SD_111f8).
        - wlits. reflexivity.
        - unfold regs1. getr_resolve. apply c_eq_0_false. exact Halg. }
      set (regs2 := regupd regs1 14 (Z_to_bv 64 0)).
      assert (E3 : RiscvSemantics.step source_segs (mkst regs1 0x111fc mem rrom)
                   = MachineOk (mkst regs2 0x11200 mem rrom)).
      { rewrite (step_lbu source_segs regs1 0x111fc mem rrom _ 14 15 _
                   (Z_to_bv 8 0) SF_111fc eq_refl SD_111fc).
        - reduce_bv_eqb_ifs. wlits. reflexivity.
        - unfold regs1. getr_resolve. rewrite Hr15, v_addi_0.
          pose proof (read_str_byte_m mem Hmem k j Hk
                        ltac:(unfold s in Hjd; lia)) as Hrd.
          assert (Hb0 : byte_at (nth k av []) j = Z_to_bv 8 0)
            by (unfold s in Hj; rewrite Hj; apply byte_at_len).
          rewrite Hb0 in Hrd. exact Hrd. }
      assert (E4 : RiscvSemantics.step source_segs (mkst regs2 0x11200 mem rrom)
                   = MachineOk (mkst regs2 0x11204 mem rrom)).
      { rewrite (step_bne_ft source_segs regs2 0x11200 mem rrom _ 14 0 _
                   SF_11200 eq_refl SD_11200).
        - wlits. reflexivity.
        - unfold regs2. getr_resolve. exact c_eq_0_true. }
      assert (E5 : RiscvSemantics.step source_segs (mkst regs2 0x11204 mem rrom)
                   = MachineOk (mkst regs2 0x1125c mem rrom)).
      { rewrite (step_jal_x0 source_segs regs2 0x11204 mem rrom _ _
                   SF_11204 eq_refl SD_11204).
        wlits. reflexivity. }
      assert (Hr10'' : reg_get regs2 10 = ptr)
        by (unfold regs2; regupd_resolve; exact Hr10').
      assert (Hr15'' : reg_get regs2 15 = ptr + nat_to_word (length (nth k av [])))
        by (unfold regs2; regupd_resolve; rewrite Hr15'; unfold s in Hj;
            rewrite Hj; reflexivity).
      assert (Hr1'' : reg_get regs2 1 = RA)
        by (unfold regs2; regupd_resolve; exact Hr1').
      destruct (source_strlen_tail k Hk mem regs2 RA Hvj Hr10'' Hr15'' Hr1'')
        as [regs' [Hag [H10 Hms]]].
      exists regs'. split; [|split].
      * intros r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15. rewrite (Hag r Hx10).
        unfold regs2, regs1. rewrite !regupd_other by assumption. reflexivity.
      * exact H10.
      * eapply mst_step; [reflexivity | exact E1 |].
        eapply mst_step; [reflexivity | exact E2 |].
        eapply mst_step; [reflexivity | exact E3 |].
        eapply mst_step; [reflexivity | exact E4 |].
        eapply mst_step; [reflexivity | exact E5 |].
        exact Hms.
  - (* j < length s *)
    assert (Hjlt : (j < length s)%nat) by lia.
    set (regs1 := regupd regs 14 (v_andi (ptr + nat_to_word j) 7)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x111f4 mem rrom)
                 = MachineOk (mkst regs1 0x111f8 mem rrom)).
    { rewrite (step_andi source_segs regs 0x111f4 mem rrom _ 14 15 _
                 SF_111f4 eq_refl SD_111f4).
      reduce_bv_eqb_ifs. unfold regs1. getr_resolve. rewrite Hr15.
      imm_norm. wlits. reflexivity. }
    assert (Hr10' : reg_get regs1 10 = ptr)
      by (unfold regs1; regupd_resolve; exact Hr10).
    assert (Hr15' : reg_get regs1 15 = ptr + nat_to_word j)
      by (unfold regs1; regupd_resolve; exact Hr15).
    assert (Hr1' : reg_get regs1 1 = RA)
      by (unfold regs1; regupd_resolve; exact Hr1).
    destruct (Z.eq_dec (bv_unsigned (v_andi (ptr + nat_to_word j) 7)) 0%Z)
      as [Halg | Halg].
    + (* aligned: enter the word loop *)
      assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x111f8 mem rrom)
                   = MachineOk (mkst regs1 0x11208 mem rrom)).
      { rewrite (step_beq_tk source_segs regs1 0x111f8 mem rrom _ 14 0 _
                   SF_111f8 eq_refl SD_111f8).
        - wlits. reflexivity.
        - unfold regs1. getr_resolve. apply c_eq_0_of_u. exact Halg. }
      destruct (source_strlen_from_aligned k Hk mem Hmem RA Hvj j regs1
                  ltac:(unfold s in Hjlt; lia) Hr10' Hr15' Hr1')
        as [regs' [Hag [H10 Hms]]].
      exists regs'. split; [|split].
      * intros r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15.
        rewrite (Hag r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15).
        unfold regs1. rewrite regupd_other by assumption. reflexivity.
      * exact H10.
      * eapply mst_step; [reflexivity | exact E1 |].
        eapply mst_step; [reflexivity | exact E2 |].
        exact Hms.
    + (* unaligned: read the (nonzero) byte and advance *)
      set (b := byte_at s j).
      assert (Hbnz : b <> Z_to_bv 8 0)
        by (apply byte_at_nz; [exact Hsnz | exact Hjlt]).
      assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x111f8 mem rrom)
                   = MachineOk (mkst regs1 0x111fc mem rrom)).
      { rewrite (step_beq_ft source_segs regs1 0x111f8 mem rrom _ 14 0 _
                   SF_111f8 eq_refl SD_111f8).
        - wlits. reflexivity.
        - unfold regs1. getr_resolve. apply c_eq_0_false. exact Halg. }
      set (regs2 := regupd regs1 14 (Z_to_bv 64 (bv_unsigned b))).
      assert (E3 : RiscvSemantics.step source_segs (mkst regs1 0x111fc mem rrom)
                   = MachineOk (mkst regs2 0x11200 mem rrom)).
      { rewrite (step_lbu source_segs regs1 0x111fc mem rrom _ 14 15 _ b
                   SF_111fc eq_refl SD_111fc).
        - reduce_bv_eqb_ifs. wlits. reflexivity.
        - unfold regs1. getr_resolve. rewrite Hr15, v_addi_0.
          unfold b, ptr, s. apply (read_str_byte_m mem Hmem);
            [exact Hk | unfold s in Hjlt; lia]. }
      assert (E4 : RiscvSemantics.step source_segs (mkst regs2 0x11200 mem rrom)
                   = MachineOk (mkst regs2 0x111f0 mem rrom)).
      { rewrite (step_bne_tk source_segs regs2 0x11200 mem rrom _ 14 0 _
                   SF_11200 eq_refl SD_11200).
        - wlits. reflexivity.
        - unfold regs2. getr_resolve.
          apply c_eq_0_false. rewrite u_zext8. apply byte_nz_u. exact Hbnz. }
      set (regs3 := regupd regs2 15 (ptr + nat_to_word (S j))).
      assert (E5 : RiscvSemantics.step source_segs (mkst regs2 0x111f0 mem rrom)
                   = MachineOk (mkst regs3 0x111f4 mem rrom)).
      { rewrite (step_addi source_segs regs2 0x111f0 mem rrom _ 15 15 _
                   SF_111f0 eq_refl SD_111f0).
        reduce_bv_eqb_ifs.
        unfold regs3, regs2, regs1. getr_resolve. rewrite Hr15.
        rewrite word_add_nat_1. wlits. reflexivity. }
      assert (Hr10'' : reg_get regs3 10 = ptr)
        by (unfold regs3, regs2, regs1; regupd_resolve; exact Hr10).
      assert (Hr15'' : reg_get regs3 15 = ptr + nat_to_word (S j))
        by (unfold regs3; apply regupd_same).
      assert (Hr1'' : reg_get regs3 1 = RA)
        by (unfold regs3, regs2, regs1; regupd_resolve; exact Hr1).
      destruct (IH (S j) regs3 ltac:(lia) Hr10'' Hr15'' Hr1'')
        as [regs' [Hag [H10 Hms]]].
      exists regs'. split; [|split].
      * intros r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15.
        rewrite (Hag r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15).
        unfold regs3, regs2, regs1. rewrite !regupd_other by assumption.
        reflexivity.
      * exact H10.
      * eapply mst_step; [reflexivity | exact E1 |].
        eapply mst_step; [reflexivity | exact E2 |].
        eapply mst_step; [reflexivity | exact E3 |].
        eapply mst_step; [reflexivity | exact E4 |].
        eapply mst_step; [reflexivity | exact E5 |].
        exact Hms.
Qed.

(** [strlen(argv[k])]: enter at 0x111e8 with a0 = &argv[k] and ra = RA,
    return to RA with a0 = the length.  Clobbers a0..a5 only. *)
Lemma source_strlen : forall k, (k < length av)%nat ->
  forall mem, mem_ok mem ->
  forall (RA : word), v_jalr RA 0 = RA ->
  forall regs,
  reg_get regs 10 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k ->
  reg_get regs 1 = RA ->
  exists regs',
    (forall r : reg, r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 ->
       r <> 15 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 10 = nat_to_word (length (nth k av [])) /\
    msteps source_segs (mkst regs 0x111e8 mem rrom) (mkst regs' RA mem rrom).
Proof.
  intros k Hk mem Hmem RA Hvj regs Hr10 Hr1.
  set (regs1 := regupd regs 15 (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word 0)).
  assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x111e8 mem rrom)
               = MachineOk (mkst regs1 0x111ec mem rrom)).
  { rewrite (step_addi source_segs regs 0x111e8 mem rrom _ 15 10 _
               SF_111e8 eq_refl SD_111e8).
    reduce_bv_eqb_ifs. unfold regs1. getr_resolve. rewrite Hr10.
    rewrite v_addi_0, word_add_nat_0. wlits. reflexivity. }
  assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x111ec mem rrom)
               = MachineOk (mkst regs1 0x111f4 mem rrom)).
  { rewrite (step_jal_x0 source_segs regs1 0x111ec mem rrom _ _
               SF_111ec eq_refl SD_111ec).
    wlits. reflexivity. }
  assert (Hr10' : reg_get regs1 10 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)
    by (unfold regs1; regupd_resolve; exact Hr10).
  assert (Hr15' : reg_get regs1 15 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word 0)
    by (unfold regs1; apply regupd_same).
  assert (Hr1' : reg_get regs1 1 = RA)
    by (unfold regs1; regupd_resolve; exact Hr1).
  destruct (source_strlen_align k Hk mem Hmem RA Hvj
              (length (nth k av [])) 0%nat regs1 ltac:(lia) Hr10' Hr15' Hr1')
    as [regs' [Hag [H10 Hms]]].
  exists regs'. split; [|split].
  - intros r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15.
    rewrite (Hag r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15).
    unfold regs1. rewrite regupd_other by assumption. reflexivity.
  - exact H10.
  - eapply mst_step; [reflexivity | exact E1 |].
    eapply mst_step; [reflexivity | exact E2 |].
    exact Hms.
Qed.

(* ================================================================= *)
(* Join-length recurrence for the outer length loop                   *)
(* ================================================================= *)

Lemma tab_join1 : forall l,
  total_arg_bytes_nat l
  = (length (join1 l) + (if Nat.eqb (length l) 0 then 0 else 1))%nat.
Proof.
  intro l. destruct l as [|a l'].
  - reflexivity.
  - cbn [length Nat.eqb].
    rewrite <- length_wjoin. rewrite wjoin_join1 by discriminate.
    rewrite length_app. cbn [length]. lia.
Qed.

Lemma jpre_step : forall i, (1 <= i)%nat -> (i <= length (tl av))%nat ->
  length (join1 (firstn i (tl av)))
  = (length (join1 (firstn (i-1) (tl av))) + length (nth i av [])
     + (if Nat.eqb i 1 then 0 else 1))%nat.
Proof.
  intros i H1 Hi.
  replace i with (S (i - 1)) at 1 by lia.
  rewrite (firstn_S_nth _ (tl av) (i-1) []) by lia.
  rewrite join1_snoc. rewrite length_app, length_wjoin.
  rewrite nth_tl. replace (S (i-1)) with i by lia.
  rewrite (tab_join1 (firstn (i-1) (tl av))).
  rewrite firstn_length_le by lia.
  destruct i as [|i']; [lia|].
  cbn [Nat.sub]. rewrite Nat.sub_0_r.
  destruct i' as [|i'']; cbn [Nat.eqb]; lia.
Qed.

Section Ge2Main.

Hypothesis Hge2 : (2 <= length av)%nat.

Definition totn : nat := total_arg_bytes_nat (tl av).
Definition tot : word := nat_to_word totn.

Lemma tl_nonnil : tl av <> [].
Proof.
  destruct av as [|a0 [|a1 l]]; cbn in Hge2; try lia.
  cbn [tl]. congruence.
Qed.

Lemma length_tl_av : length (tl av) = (length av - 1)%nat.
Proof. apply length_tl_list. Qed.

Lemma totn_ge1 : (1 <= totn)%nat.
Proof.
  unfold totn. rewrite tab_join1.
  destruct (Nat.eqb (length (tl av)) 0) eqn:E.
  - apply Nat.eqb_eq in E. apply length_zero_iff_nil in E.
    exfalso. apply tl_nonnil. exact E.
  - lia.
Qed.

Lemma totn_bound : (Z.of_nat totn <= 2097152)%Z.
Proof.
  unfold totn.
  pose proof (valid_argv_tab av Hva) as Hb.
  apply Nat2Z.inj_le in Hb. rewrite of_nat_2097152 in Hb.
  assert (Htlskip : tl av = skipn 1 av) by (destruct av; reflexivity).
  rewrite Htlskip.
  rewrite <- (firstn_skipn 1 av) in Hb.
  rewrite tab_app in Hb. lia.
Qed.

Lemma u_tot : bv_unsigned tot = Z.of_nat totn.
Proof.
  unfold tot. apply u_ntw. pose proof totn_bound. lia.
Qed.

Lemma tot_ge1 : (1 <= bv_unsigned tot)%Z.
Proof. rewrite u_tot. pose proof totn_ge1. lia. Qed.

Lemma totN_bound : (bv_unsigned tot <= 2097152)%Z.
Proof. rewrite u_tot. exact totn_bound. Qed.

Lemma join1_tl_len_nat : length (join1 (tl av)) = (totn - 1)%nat.
Proof.
  pose proof (length_join1 (tl av) tl_nonnil) as H.
  unfold totn. lia.
Qed.

Lemma S_join1_tot : nat_to_word (S (length (join1 (tl av)))) = tot.
Proof.
  unfold tot, totn. f_equal. apply length_join1. exact tl_nonnil.
Qed.

Lemma jout_len_nat : length (jout av) = totn.
Proof.
  unfold jout. rewrite length_app. cbn [length].
  pose proof join1_tl_len_nat. pose proof totn_ge1. lia.
Qed.

Lemma jout_len_w : word_to_nat tot = length (jout av).
Proof.
  rewrite jout_len_nat. unfold tot. apply word_to_nat_ntw.
  pose proof totn_bound. lia.
Qed.

(** The single output buffer is small enough for the model to transfer
    it in one [write]: both binaries exit 3 without writing when [tot]
    exceeds 65536, so the buffer written on a successful run is at most
    65536 bytes -- well inside [Uaccess.rw_bytes_max] (131072). *)
Lemma jout_modeled : (bv_unsigned tot <= 65536)%Z -> bufs_modeled [jout av].
Proof.
  intro Hcap. apply bufs_modeled_single.
  unfold buf_modeled, rw_bytes_max.
  rewrite jout_len_nat, <- u_tot. lia.
Qed.

Lemma argc_le_nat : (length av <= 1024)%nat.
Proof. pose proof (valid_argv_len av Hva). lia. Qed.

Lemma iN_le : forall i, (i <= length av)%nat -> (Z.of_nat i <= 1024)%Z.
Proof. intros i Hi. pose proof argc_le_nat. lia. Qed.

Lemma acc_bound : forall i,
  (Z.of_nat (length (join1 (firstn i (tl av)))) <= 2097152)%Z.
Proof.
  intro i. pose proof totn_bound as Hb. unfold totn in Hb.
  assert (H1 : (length (join1 (firstn i (tl av)))
                <= total_arg_bytes_nat (firstn i (tl av)))%nat).
  { rewrite (tab_join1 (firstn i (tl av))). lia. }
  assert (H2 : (total_arg_bytes_nat (firstn i (tl av))
                <= total_arg_bytes_nat (tl av))%nat).
  { rewrite <- (firstn_skipn i (tl av)) at 2. rewrite tab_app. lia. }
  lia.
Qed.

(* ================================================================= *)
(* Prologue: entry -> outer length loop head 0x11034                  *)
(* ================================================================= *)

Lemma source_to_loop :
  exists regs1,
    reg_get regs1 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs1 18 = argcN /\
    reg_get regs1 19 = Z_to_bv 64 (bv_unsigned rsp + 8) /\
    reg_get regs1 20 = Z_to_bv 64 1 /\
    reg_get regs1 9 = Z_to_bv 64 1 /\
    reg_get regs1 8 = Z_to_bv 64 0 /\
    msteps source_segs
      (init_machine_state (run_segments source_segs inp rsp rmb) 0x11190 source_phdrs rsp rmb rrnd inp)
      (mkst regs1 0x11034 fmem rrom).
(** TWENTY-FOUR instructions in ONE reflective block: the crt entry
    sequence again, main's frame push with its six spills, the
    [argc >= 2] fall-through and the four [mv]s that set the outer
    loop's induction registers.  Same seven stores and one load as the
    [argc < 2] path, and the five callee-saved registers pinned to
    [ELit 0] so that the spilled values are literals and the exit
    memory is literally [fmem].

    [sym_block_ex] rather than [sym_block] because the conclusion is
    existential in the exit register file; the exit memory is then
    reconciled with [fmem] by REVERTING the block's [msteps] and
    running [sym_mem_norm] on it. *)
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as HargcLe.
  pose proof u_argcN as Hu.
  rewrite init_mkst.
  sym_block_ex source_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
          (Z_to_bv 64 (Z.of_N 0x11190))
          (wrap_mem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x11190)) rsp rrnd)
          (seg_rom (run_segments source_segs inp rsp rmb)))
    24%nat [false] (@nil expr)
    [((2 : reg), EVar 32); ((8 : reg), ELit 0); ((9 : reg), ELit 0);
     ((18 : reg), ELit 0); ((19 : reg), ELit 0); ((20 : reg), ELit 0)]
    [rsp] [argcN] RA HRA Hms.
  { (* [bge s1,a0] at 0x11020 -> not taken, because [argc >= 2] *) sym_br. }
  1-6: solve_store_ok.
  { (* [sd a2,0(t1)] at 0x111b4 -> musl's [__environ] slot at 0x13000 *)
    apply source_store_ok; u_norm; lia. }
  { (* [ld a0,0(sp)] at 0x11198 -> argc, out of the initial stack image *)
    replace (Z_to_bv 64 (bv_unsigned rsp + 0)) with rsp
      by (apply bv_eq; u_norm; lia);
    exists (word_le8 argcN); split;
      [ fold wmem; apply read_argc_w | apply bytes_le_n_to_le_8 ]. }
  exists RA. repeat split.
  1-6: sym_regs HRA; sym_close.
  replace (0x11034 : word) with (Z_to_bv 64 69684) by bveq.
  unfold fmem, emem, wmem, rrom.
  revert Hms. sym_mem_norm. rewrite envp_val_sym. exact (fun x => x).
Qed.

(* ================================================================= *)
(* Outer length loop: 0x11034 .. 0x1105c                              *)
(*                                                                    *)
(* s1 (x9) is the index i, s0 (x8) the accumulator, s4 (x20) the      *)
(* constant 1; each iteration calls musl strlen (ra := 0x11044).      *)
(* ================================================================= *)

Lemma source_length : forall f i regs,
  (1 <= i)%nat -> (i < length av)%nat -> (length av - i <= f)%nat ->
  reg_get regs 18 = argcN ->
  reg_get regs 19 = Z_to_bv 64 (bv_unsigned rsp + 8) ->
  reg_get regs 20 = Z_to_bv 64 1 ->
  reg_get regs 9 = nat_to_word i ->
  reg_get regs 8 = nat_to_word (length (join1 (firstn (i-1) (tl av)))) ->
  exists regs',
    (forall r : reg, r <> 1 -> r <> 8 -> r <> 9 -> r <> 10 -> r <> 11 ->
       r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 ->
       reg_get regs' r = reg_get regs r) /\
    reg_get regs' 8 = nat_to_word (length (join1 (tl av))) /\
    msteps source_segs (mkst regs 0x11034 fmem rrom)
                       (mkst regs' 0x1105c fmem rrom).
Proof.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as HargcLe.
  induction f as [|f IH]; intros i regs H1 Hi Hf H18 H19 H20 H9 H8; [lia|].
  assert (Hilt : (i < length av)%nat) by lia.
  assert (HiZ : (Z.of_nat i <= 1024)%Z) by (apply iN_le; lia).
  assert (HSiZ : (Z.of_nat (S i) <= 1024)%Z) by (apply iN_le; lia).
  assert (HniB : (Z.of_nat (length (nth i av [])) <= 131071)%Z)
    by (apply valid_argv_str_len; assumption).
  pose proof (acc_bound (i-1)) as Haccb.
  destruct (sptr_bounds i Hilt) as [Hptrlo Hptrhi].
  (* slli a5,s1,3 *)
  set (regs1 := regupd regs 15 (Z_to_bv 64 (8 * Z.of_nat i))).
  assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11034 fmem rrom)
               = MachineOk (mkst regs1 0x11038 fmem rrom)).
  { rewrite (step_slli source_segs regs 0x11034 fmem rrom _ 15 9 _
               SF_11034 eq_refl SD_11034).
    reduce_bv_eqb_ifs. getr_resolve. rewrite H9.
    imm_norm. rewrite v_slli3_nat by lia. wlits. reflexivity. }
  (* add a5,s3,a5 *)
  set (regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat i))).
  assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x11038 fmem rrom)
               = MachineOk (mkst regs2 0x1103c fmem rrom)).
  { eapply eq_trans;
    [ apply (step_add_at source_segs regs1 0x11038 fmem rrom _ 15 19 15
               (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat i))
               SF_11038 eq_refl SD_11038 eq_refl);
      unfold regs1; getr_resolve; rewrite H19;
      unfold v_add; u_norm; f_equal; lia
    | wlits; reflexivity ]. }
  (* ld a0,0(a5) : a0 = sptr i *)
  set (regs3 := regupd regs2 10 (sptr i)).
  assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x1103c fmem rrom)
               = MachineOk (mkst regs3 0x11040 fmem rrom)).
  { rewrite (step_ld source_segs regs2 0x1103c fmem rrom _ 10 15 _
               (word_le8 (sptr i)) (sptr i) SF_1103c eq_refl SD_1103c).
    - reduce_bv_eqb_ifs. wlits. reflexivity.
    - unfold regs2. getr_resolve. rewrite v_addi_0.
      apply read_arg_ptr_f. exact Hilt.
    - exact (bytes_le_n_to_le_8 _). }
  (* jal ra, strlen : ra = 0x11044 *)
  set (regs4 := regupd regs3 1 (0x11044 : word)).
  assert (E4 : RiscvSemantics.step source_segs (mkst regs3 0x11040 fmem rrom)
               = MachineOk (mkst regs4 0x111e8 fmem rrom)).
  { rewrite (step_jal_link source_segs regs3 0x11040 fmem rrom _ 1 _
               SF_11040 eq_refl SD_11040).
    reduce_bv_eqb_ifs. unfold regs4. wlits. reflexivity. }
  (* strlen(argv[i]) : a0 = length *)
  assert (Hr10_4 : reg_get regs4 10 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) i).
  { unfold regs4, regs3. regupd_resolve. reflexivity. }
  assert (Hr1_4 : reg_get regs4 1 = (0x11044 : word))
    by (unfold regs4; apply regupd_same).
  destruct (source_strlen i Hilt fmem fmem_ok (0x11044 : word) ltac:(bveq)
              regs4 Hr10_4 Hr1_4) as [regs5 [Hag5 [H10_5 Hms5]]].
  assert (Hpres5 : forall r : reg, r <> 1 -> r <> 10 -> r <> 11 -> r <> 12 ->
                   r <> 13 -> r <> 14 -> r <> 15 ->
                   reg_get regs5 r = reg_get regs r).
  { intros r Hx1 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15.
    rewrite (Hag5 r Hx10 Hx11 Hx12 Hx13 Hx14 Hx15).
    unfold regs4, regs3, regs2, regs1.
    rewrite !regupd_other by assumption. reflexivity. }
  assert (H8_5 : reg_get regs5 8
                 = nat_to_word (length (join1 (firstn (i-1) (tl av)))))
    by (rewrite Hpres5 by reg_neq_tac; exact H8).
  assert (H9_5 : reg_get regs5 9 = nat_to_word i)
    by (rewrite Hpres5 by reg_neq_tac; exact H9).
  assert (H20_5 : reg_get regs5 20 = Z_to_bv 64 1)
    by (rewrite Hpres5 by reg_neq_tac; exact H20).
  assert (H18_5 : reg_get regs5 18 = argcN)
    by (rewrite Hpres5 by reg_neq_tac; exact H18).
  assert (H19_5 : reg_get regs5 19 = Z_to_bv 64 (bv_unsigned rsp + 8))
    by (rewrite Hpres5 by reg_neq_tac; exact H19).
  (* add s0,s0,a0 : s0 += ni *)
  set (regs6 := regupd regs5 8
        (nat_to_word (length (join1 (firstn (i-1) (tl av))) + length (nth i av [])))).
  assert (E6 : RiscvSemantics.step source_segs (mkst regs5 0x11044 fmem rrom)
               = MachineOk (mkst regs6 0x11048 fmem rrom)).
  { eapply eq_trans;
    [ apply (step_add_at source_segs regs5 0x11044 fmem rrom _ 8 8 10
               (nat_to_word (length (join1 (firstn (i-1) (tl av))) + length (nth i av [])))
               SF_11044 eq_refl SD_11044 eq_refl);
      getr_resolve; rewrite H8_5, H10_5;
      rewrite v_add_word; apply nat_to_word_merge
    | wlits; reflexivity ]. }
  assert (Hpres6 : forall r : reg, r <> 8 -> r <> 1 -> r <> 10 -> r <> 11 ->
                   r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 ->
                   reg_get regs6 r = reg_get regs r).
  { intros r Ha Hb Hc Hd He Hf' Hg Hh. unfold regs6.
    rewrite regupd_other by assumption.
    apply Hpres5; assumption. }
  assert (H9_6 : reg_get regs6 9 = nat_to_word i)
    by (rewrite Hpres6 by reg_neq_tac; exact H9).
  assert (H20_6 : reg_get regs6 20 = Z_to_bv 64 1)
    by (rewrite Hpres6 by reg_neq_tac; exact H20).
  assert (H18_6 : reg_get regs6 18 = argcN)
    by (rewrite Hpres6 by reg_neq_tac; exact H18).
  assert (H19_6 : reg_get regs6 19 = Z_to_bv 64 (bv_unsigned rsp + 8))
    by (rewrite Hpres6 by reg_neq_tac; exact H19).
  (* separator branch: reach 0x11050 with s0 = newacc *)
  set (sep := if Nat.eqb i 1 then 0%nat else 1%nat).
  set (newacc := nat_to_word (length (join1 (firstn (i-1) (tl av)))
                              + length (nth i av []) + sep)).
  assert (Hnew : nat_to_word (length (join1 (firstn i (tl av)))) = newacc).
  { unfold newacc, sep.
    rewrite jpre_step by (rewrite ?length_tl_av; lia).
    destruct (Nat.eqb i 1); reflexivity. }
  assert (HB : exists regsB,
     (forall r : reg, r <> 8 -> reg_get regsB r = reg_get regs6 r) /\
     reg_get regsB 8 = newacc /\
     msteps source_segs (mkst regs6 0x11048 fmem rrom)
                        (mkst regsB 0x11050 fmem rrom)).
  { destruct (Nat.eq_dec i 1) as [Hi1 | Hine].
    - (* i = 1: beq taken, no separator *)
      exists regs6. split; [intros; reflexivity | split].
      + unfold newacc, sep.
        replace (Nat.eqb i 1) with true by (symmetry; apply Nat.eqb_eq; exact Hi1).
        unfold regs6. rewrite regupd_same. f_equal. lia.
      + eapply mst_step;
          [ reflexivity
          | eapply step_beq_tk;
            [ exact SF_11048 | reflexivity | exact SD_11048
            | getr_resolve; rewrite H9_6, H20_6, Hi1; apply c_eq_refl ]
          | ].
        norm_pc. apply mst_refl.
    - (* i >= 2: beq fall-through, add separator *)
      exists (regupd regs6 8 newacc). split; [| split].
      + intros r Hr8. rewrite regupd_other by assumption. reflexivity.
      + apply regupd_same.
      + eapply mst_step;
          [ reflexivity
          | eapply step_beq_ft;
            [ exact SF_11048 | reflexivity | exact SD_11048
            | getr_resolve; rewrite H9_6, H20_6;
              apply c_eq_neq;
              rewrite u_ntw by lia; u_norm; lia ]
          | ].
        (* addi s0,s0,1 *)
        eapply mst_step;
          [ reflexivity
          | eapply step_addi_at with (v := newacc);
            [ exact SF_1104c | reflexivity | exact SD_1104c | reflexivity
            | getr_resolve; unfold regs6; rewrite regupd_same;
              rewrite v_addi_Sj by lia;
              unfold newacc, sep;
              replace (Nat.eqb i 1) with false
                by (symmetry; apply Nat.eqb_neq; exact Hine);
              f_equal; lia ]
          | ].
        norm_pc. apply mst_refl. }
  destruct HB as [regsB [HagB [H8B HmsB]]].
  assert (H9B : reg_get regsB 9 = nat_to_word i)
    by (rewrite (HagB 9 ltac:(discriminate)); exact H9_6).
  assert (H18B : reg_get regsB 18 = argcN)
    by (rewrite (HagB 18 ltac:(discriminate)); exact H18_6).
  assert (H19B : reg_get regsB 19 = Z_to_bv 64 (bv_unsigned rsp + 8))
    by (rewrite (HagB 19 ltac:(discriminate)); exact H19_6).
  assert (H20B : reg_get regsB 20 = Z_to_bv 64 1)
    by (rewrite (HagB 20 ltac:(discriminate)); exact H20_6).
  (* addi s1,s1,1 *)
  set (regsC := regupd regsB 9 (nat_to_word (S i))).
  assert (EC : RiscvSemantics.step source_segs (mkst regsB 0x11050 fmem rrom)
               = MachineOk (mkst regsC 0x11054 fmem rrom)).
  { rewrite (step_addi source_segs regsB 0x11050 fmem rrom _ 9 9 _
               SF_11050 eq_refl SD_11050).
    reduce_bv_eqb_ifs. getr_resolve. rewrite H9B.
    rewrite v_addi_Sj by lia. wlits. reflexivity. }
  (* sext.w a5,s1 *)
  set (regsD := regupd regsC 15 (nat_to_word (S i))).
  assert (ED : RiscvSemantics.step source_segs (mkst regsC 0x11054 fmem rrom)
               = MachineOk (mkst regsD 0x11058 fmem rrom)).
  { rewrite (step_addiw source_segs regsC 0x11054 fmem rrom _ 15 9 _
               SF_11054 eq_refl SD_11054).
    reduce_bv_eqb_ifs. unfold regsC. getr_resolve.
    rewrite v_addiw_id by (rewrite u_ntw by lia; lia).
    wlits. reflexivity. }
  assert (H15D : reg_get regsD 15 = nat_to_word (S i))
    by (unfold regsD; apply regupd_same).
  assert (H18D : reg_get regsD 18 = argcN).
  { unfold regsD, regsC. regupd_resolve. exact H18B. }
  assert (H8D : reg_get regsD 8 = newacc).
  { unfold regsD, regsC. regupd_resolve. exact H8B. }
  destruct (lt_dec (S i) (length av)) as [Hlti | Hge].
  - (* blt taken: loop again *)
    assert (HmsE : RiscvSemantics.step source_segs (mkst regsD 0x11058 fmem rrom)
                   = MachineOk (mkst regsD 0x11034 fmem rrom)).
    { rewrite (step_blt_tk source_segs regsD 0x11058 fmem rrom _ 15 18 _
                 SF_11058 eq_refl SD_11058).
      - wlits. reflexivity.
      - getr_resolve. rewrite H15D, H18D.
        rewrite c_lts_small by (rewrite ?u_ntw, ?u_argcN by lia; lia).
        apply Z.ltb_lt. rewrite u_ntw by lia. rewrite u_argcN. lia. }
    assert (H9D : reg_get regsD 9 = nat_to_word (S i)).
    { unfold regsD. rewrite regupd_other by discriminate.
      unfold regsC. apply regupd_same. }
    assert (H19D : reg_get regsD 19 = Z_to_bv 64 (bv_unsigned rsp + 8)).
    { unfold regsD, regsC. regupd_resolve. exact H19B. }
    assert (H20D : reg_get regsD 20 = Z_to_bv 64 1).
    { unfold regsD, regsC. regupd_resolve. exact H20B. }
    assert (Hinv : reg_get regsD 8
                   = nat_to_word (length (join1 (firstn (S i - 1) (tl av))))).
    { rewrite H8D. rewrite <- Hnew. replace (S i - 1)%nat with i by lia. reflexivity. }
    destruct (IH (S i) regsD ltac:(lia) Hlti ltac:(lia) H18D H19D H20D H9D Hinv)
      as [regs' [Hag' [H8' Hms']]].
    exists regs'. split; [| split].
    + intros r Ha Hb Hc Hd He Hf' Hg Hh Hj'.
      rewrite (Hag' r Ha Hb Hc Hd He Hf' Hg Hh Hj').
      unfold regsD, regsC. rewrite !regupd_other by assumption.
      rewrite (HagB r Hb). apply Hpres6; assumption.
    + exact H8'.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply msteps_trans; [exact Hms5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      eapply msteps_trans; [exact HmsB |].
      eapply mst_step; [reflexivity | exact EC |].
      eapply mst_step; [reflexivity | exact ED |].
      eapply mst_step; [reflexivity | exact HmsE |].
      exact Hms'.
  - (* blt fall-through: i = argc - 1, done *)
    assert (Hieq : i = (length av - 1)%nat) by lia.
    assert (HmsF : RiscvSemantics.step source_segs (mkst regsD 0x11058 fmem rrom)
                   = MachineOk (mkst regsD 0x1105c fmem rrom)).
    { rewrite (step_blt_ft source_segs regsD 0x11058 fmem rrom _ 15 18 _
                 SF_11058 eq_refl SD_11058).
      - wlits. reflexivity.
      - getr_resolve. rewrite H15D, H18D.
        rewrite c_lts_small by (rewrite ?u_ntw, ?u_argcN by lia; lia).
        apply Z.ltb_ge. rewrite u_ntw by lia. rewrite u_argcN. lia. }
    exists regsD. split; [| split].
    + intros r Ha Hb Hc Hd He Hf' Hg Hh Hj'.
      unfold regsD, regsC. rewrite !regupd_other by assumption.
      rewrite (HagB r Hb). apply Hpres6; assumption.
    + rewrite H8D. rewrite <- Hnew.
      replace (firstn i (tl av)) with (tl av).
      2:{ rewrite Hieq. rewrite <- length_tl_av. rewrite firstn_all. reflexivity. }
      reflexivity.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply msteps_trans; [exact Hms5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      eapply msteps_trans; [exact HmsB |].
      eapply mst_step; [reflexivity | exact EC |].
      eapply mst_step; [reflexivity | exact ED |].
      eapply mst_step; [reflexivity | exact HmsF |].
      apply mst_refl.
Qed.

(* ================================================================= *)
(* From entry to 0x1105c (post length loop)                           *)
(* ================================================================= *)

Lemma source_after_length :
  exists regs2,
    reg_get regs2 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs2 18 = argcN /\
    reg_get regs2 19 = Z_to_bv 64 (bv_unsigned rsp + 8) /\
    reg_get regs2 8 = nat_to_word (length (join1 (tl av))) /\
    msteps source_segs
      (init_machine_state (run_segments source_segs inp rsp rmb) 0x11190 source_phdrs rsp rmb rrnd inp)
      (mkst regs2 0x1105c fmem rrom).
Proof.
  destruct source_to_loop as (regs1 & H2 & H18 & H19 & H20 & H9 & H8 & Hms1).
  destruct (source_length (length av) 1 regs1 ltac:(lia) ltac:(lia) ltac:(lia)
              H18 H19 H20 ltac:(rewrite H9; reflexivity)
              ltac:(rewrite H8; reflexivity))
    as (regs2 & Hag & H8' & Hms2).
  exists regs2. split; [|split; [|split; [|split]]].
  - rewrite (Hag 2) by reg_neq_tac. exact H2.
  - rewrite (Hag 18) by reg_neq_tac. exact H18.
  - rewrite (Hag 19) by reg_neq_tac. exact H19.
  - exact H8'.
  - eapply msteps_trans; [exact Hms1 | exact Hms2].
Qed.

(* ================================================================= *)
(* tot > 65536: no output, exit 3                                     *)
(* ================================================================= *)

Lemma source_wexit_cap : (65536 < bv_unsigned tot)%Z ->
  to_wexit source_segs
    (init_machine_state (run_segments source_segs inp rsp rmb) 0x11190 source_phdrs rsp rmb rrnd inp)
    [] (Z_to_bv 64 3).
Proof.
  intros Hcap.
  pose proof rsp_lo_num as Hlo. pose proof tot_ge1 as Hg1.
  pose proof totN_bound as Htb.
  destruct source_after_length as (regs2 & H2 & H18 & H19 & H8 & Hms).
  eapply msteps_to_wexit; [exact Hms|].
  (* addi s0,s0,1 : s0 = tot *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := tot);
      [ exact SF_1105c | reflexivity | exact SD_1105c | reflexivity
      | getr_resolve; rewrite H8;
        rewrite v_addi_Sj by (pose proof join1_tl_len_nat;
                              pose proof totn_bound; lia);
        exact S_join1_tot ]
    | norm_pc ].
  (* lui a5,0x10 : a5 = 65536 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_lui_at with (v := Z_to_bv 64 0x10000);
      [ exact SF_11060 | reflexivity | exact SD_11060 | reflexivity
      | bveq ]
    | norm_pc ].
  (* li a0,3 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 3);
      [ exact SF_11064 | reflexivity | exact SD_11064 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* bltu a5,s0 taken (65536 < tot) -> 0x11098 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_bltu_tk;
      [ exact SF_11068 | reflexivity | exact SD_11068
      | getr_resolve; regupd_resolve;
        rewrite c_ltu_ltb; u_norm; apply Z.ltb_lt; lia ]
    | norm_pc ].
  apply source_epilogue.
  - regupd_resolve. exact H2.
  - regupd_resolve. reflexivity.
  - u_norm; lia.
  - apply read_slot_ra.
  - apply read_slot_0.
Qed.

(* ================================================================= *)
(* Exit-4 leaf: 0x11094 li a0,4 ; epilogue                            *)
(* ================================================================= *)

Lemma source_exit4 : forall regs,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  to_wexit source_segs (mkst regs 0x11094 fmem rrom) [] (Z_to_bv 64 4).
Proof.
  intros regs H2.
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 4);
      [ exact SF_11094 | reflexivity | exact SD_11094 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  apply source_epilogue.
  - regupd_resolve. exact H2.
  - regupd_resolve. reflexivity.
  - u_norm; lia.
  - apply read_slot_ra.
  - apply read_slot_0.
Qed.

(* ================================================================= *)
(* Inner copy loop: 0x1111c .. 0x11134  (copy one arg's bytes)        *)
(*                                                                    *)
(* a5 (x15) = pos'+j, a2 (x12) = pos' (loop-invariant), t1 (x6) = the *)
(* source string pointer, s1 (x9) = buf; each iteration recomputes    *)
(* j = a5 - a2 and both addresses, stores through a3 (x13) and        *)
(* advances a5 via s0 (x8).                                           *)
(* ================================================================= *)

Lemma source_copy_inner : forall base_mem (r p : word) (s prefix : list byte),
  (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + bv_unsigned tot <= bv_unsigned rsp - stack_max_size)%Z ->
  region_free (segments_reserved source_segs) r tot = true ->
  ~ In (Z_to_bv 8 0) s ->
  (length prefix + length s + 1 <= totn)%nat ->
  (bv_unsigned rsp <= bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length s) + 1 < 2^64)%Z ->
  (forall j, (j <= length s)%nat ->
     rdn source_segs base_mem (p + nat_to_word j) 1%nat = Some [byte_at s j]) ->
  (* the whole grant is writable: the loop's [sb]s are machine stores now *)
  store_grant_ok source_segs base_mem r tot ->
  forall d j regs,
  (j + d = length s)%nat ->
  reg_get regs 6 = p ->
  reg_get regs 9 = r ->
  reg_get regs 12 = nat_to_word (length prefix) ->
  reg_get regs 15 = nat_to_word (length prefix + j) ->
  exists regs',
    (forall x : reg, x <> 8 -> x <> 10 -> x <> 13 -> x <> 15 ->
       reg_get regs' x = reg_get regs x) /\
    reg_get regs' 8 = nat_to_word (length prefix + length s + 1) /\
    reg_get regs' 13 = r + nat_to_word (length prefix + length s) /\
    reg_get regs' 15 = nat_to_word (length prefix + length s) /\
    msteps source_segs
      (mkst regs 0x1111c (wbytes base_mem r (prefix ++ firstn j s)) rrom)
      (mkst regs' 0x11134 (wbytes base_mem r (prefix ++ s)) rrom).
Proof.
  intros base_mem r p s prefix Hr0 Hceil Hfree Hnz Hpsb Hp Hpbnd Hrd Hgok.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof tot_ge1 as Htg1. pose proof totN_bound as Htb.
  pose proof totn_bound as HtbZ.
  pose proof stack_max_size_val as Hacv.
  pose proof u_tot as Hut.
  set (lp := length prefix) in *.
  set (ls := length s) in *.
  induction d as [|d IH]; intros j regs Hjd H6 H9 H12 H15.
  - (* j = length s: NUL, no store, fall through *)
    assert (Hj : j = ls) by lia.
    set (M := wbytes base_mem r (prefix ++ firstn j s)).
    assert (HlenF : (length (prefix ++ firstn j s) = lp + j)%nat)
      by (rewrite length_app, firstn_length_le by lia; reflexivity).
    set (regs1 := regupd regs 13 (nat_to_word j)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x1111c M rrom)
                 = MachineOk (mkst regs1 0x11120 M rrom)).
    { eapply eq_trans;
      [ apply (step_sub_at source_segs regs 0x1111c M rrom _ 13 15 12
                 (nat_to_word j) SF_1111c eq_refl SD_1111c eq_refl);
        getr_resolve; rewrite H15, H12;
        rewrite ntw_sub by lia; f_equal; lia
      | wlits; reflexivity ]. }
    set (regs2 := regupd regs1 13 (p + nat_to_word j)).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x11120 M rrom)
                 = MachineOk (mkst regs2 0x11124 M rrom)).
    { eapply eq_trans;
      [ apply (step_add_at source_segs regs1 0x11120 M rrom _ 13 6 13
                 (p + nat_to_word j) SF_11120 eq_refl SD_11120 eq_refl);
        unfold regs1; getr_resolve; rewrite H6;
        rewrite v_add_word; reflexivity
      | wlits; reflexivity ]. }
    set (regs3 := regupd regs2 10 (Z_to_bv 64 0)).
    assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x11124 M rrom)
                 = MachineOk (mkst regs3 0x11128 M rrom)).
    { rewrite (step_lbu source_segs regs2 0x11124 M rrom _ 10 13 _ (Z_to_bv 8 0)
                 SF_11124 eq_refl SD_11124).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs2. getr_resolve. rewrite v_addi_0.
        unfold M. rewrite rdn_wbytes_disjoint
          by (rewrite ?HlenF, ?word_add_nat; u_norm; lia).
        pose proof (Hrd j ltac:(lia)) as Hrdj.
        assert (Hb0 : byte_at s j = Z_to_bv 8 0).
        { unfold ls in Hj. rewrite Hj. apply byte_at_len. }
        rewrite Hb0 in Hrdj. exact Hrdj. }
    set (regs4 := regupd regs3 8 (nat_to_word (S (lp + j)))).
    assert (E4 : RiscvSemantics.step source_segs (mkst regs3 0x11128 M rrom)
                 = MachineOk (mkst regs4 0x1112c M rrom)).
    { eapply eq_trans;
      [ apply (step_addi_at source_segs regs3 0x11128 M rrom _ 8 15 _
                 (nat_to_word (S (lp + j))) SF_11128 eq_refl SD_11128 eq_refl);
        unfold regs3, regs2, regs1; getr_resolve; rewrite H15;
        apply v_addi_Sj; lia
      | wlits; reflexivity ]. }
    set (regs5 := regupd regs4 13 (r + nat_to_word (lp + j))).
    assert (E5 : RiscvSemantics.step source_segs (mkst regs4 0x1112c M rrom)
                 = MachineOk (mkst regs5 0x11130 M rrom)).
    { eapply eq_trans;
      [ apply (step_add_at source_segs regs4 0x1112c M rrom _ 13 15 9
                 (r + nat_to_word (lp + j)) SF_1112c eq_refl SD_1112c eq_refl);
        unfold regs4, regs3, regs2, regs1; getr_resolve; rewrite H15, H9;
        rewrite v_add_word; apply word_add_comm
      | wlits; reflexivity ]. }
    assert (E6 : RiscvSemantics.step source_segs (mkst regs5 0x11130 M rrom)
                 = MachineOk (mkst regs5 0x11134 M rrom)).
    { rewrite (step_bne_ft source_segs regs5 0x11130 M rrom _ 10 0 _
                 SF_11130 eq_refl SD_11130).
      - wlits. reflexivity.
      - unfold regs5, regs4, regs3. getr_resolve. exact c_eq_0_true. }
    exists regs5. split; [|split; [|split; [|split]]].
    + intros x Hx8 Hx10 Hx13 Hx15. unfold regs5, regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs5, regs4. regupd_resolve.
      unfold ls in Hj. rewrite Hj. f_equal. lia.
    + unfold regs5. regupd_resolve.
      unfold ls in Hj. rewrite Hj. reflexivity.
    + unfold regs5, regs4, regs3, regs2, regs1. regupd_resolve.
      rewrite H15. unfold ls in Hj. rewrite Hj. reflexivity.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      unfold M.
      replace (firstn j s) with s by (rewrite Hj; symmetry; apply firstn_all).
      apply mst_refl.
  - (* j < length s: store byte, loop *)
    assert (Hjlt : (j < ls)%nat) by lia.
    set (b := byte_at s j).
    assert (Hbnz : b <> Z_to_bv 8 0) by (apply byte_at_nz; assumption).
    set (M := wbytes base_mem r (prefix ++ firstn j s)).
    assert (HlenF : (length (prefix ++ firstn j s) = lp + j)%nat)
      by (rewrite length_app, firstn_length_le by lia; reflexivity).
    set (regs1 := regupd regs 13 (nat_to_word j)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x1111c M rrom)
                 = MachineOk (mkst regs1 0x11120 M rrom)).
    { eapply eq_trans;
      [ apply (step_sub_at source_segs regs 0x1111c M rrom _ 13 15 12
                 (nat_to_word j) SF_1111c eq_refl SD_1111c eq_refl);
        getr_resolve; rewrite H15, H12;
        rewrite ntw_sub by lia; f_equal; lia
      | wlits; reflexivity ]. }
    set (regs2 := regupd regs1 13 (p + nat_to_word j)).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x11120 M rrom)
                 = MachineOk (mkst regs2 0x11124 M rrom)).
    { eapply eq_trans;
      [ apply (step_add_at source_segs regs1 0x11120 M rrom _ 13 6 13
                 (p + nat_to_word j) SF_11120 eq_refl SD_11120 eq_refl);
        unfold regs1; getr_resolve; rewrite H6;
        rewrite v_add_word; reflexivity
      | wlits; reflexivity ]. }
    set (regs3 := regupd regs2 10 (Z_to_bv 64 (bv_unsigned b))).
    assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x11124 M rrom)
                 = MachineOk (mkst regs3 0x11128 M rrom)).
    { rewrite (step_lbu source_segs regs2 0x11124 M rrom _ 10 13 _ b
                 SF_11124 eq_refl SD_11124).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs2. getr_resolve. rewrite v_addi_0.
        unfold M. rewrite rdn_wbytes_disjoint
          by (rewrite ?HlenF, ?word_add_nat; u_norm; lia).
        unfold b. apply Hrd. lia. }
    set (regs4 := regupd regs3 8 (nat_to_word (S (lp + j)))).
    assert (E4 : RiscvSemantics.step source_segs (mkst regs3 0x11128 M rrom)
                 = MachineOk (mkst regs4 0x1112c M rrom)).
    { eapply eq_trans;
      [ apply (step_addi_at source_segs regs3 0x11128 M rrom _ 8 15 _
                 (nat_to_word (S (lp + j))) SF_11128 eq_refl SD_11128 eq_refl);
        unfold regs3, regs2, regs1; getr_resolve; rewrite H15;
        apply v_addi_Sj; lia
      | wlits; reflexivity ]. }
    set (regs5 := regupd regs4 13 (r + nat_to_word (lp + j))).
    assert (E5 : RiscvSemantics.step source_segs (mkst regs4 0x1112c M rrom)
                 = MachineOk (mkst regs5 0x11130 M rrom)).
    { eapply eq_trans;
      [ apply (step_add_at source_segs regs4 0x1112c M rrom _ 13 15 9
                 (r + nat_to_word (lp + j)) SF_1112c eq_refl SD_1112c eq_refl);
        unfold regs4, regs3, regs2, regs1; getr_resolve; rewrite H15, H9;
        rewrite v_add_word; apply word_add_comm
      | wlits; reflexivity ]. }
    assert (E6 : RiscvSemantics.step source_segs (mkst regs5 0x11130 M rrom)
                 = MachineOk (mkst regs5 0x11154 M rrom)).
    { rewrite (step_bne_tk source_segs regs5 0x11130 M rrom _ 10 0 _
                 SF_11130 eq_refl SD_11130).
      - wlits. reflexivity.
      - unfold regs5, regs4, regs3. getr_resolve.
        apply c_eq_0_false. rewrite u_zext8. apply byte_nz_u. exact Hbnz. }
    set (Mnext := wbytes base_mem r (prefix ++ firstn (S j) s)).
    assert (E7 : RiscvSemantics.step source_segs (mkst regs5 0x11154 M rrom)
                 = MachineOk (mkst regs5 0x11158 Mnext rrom)).
    { eapply eq_trans;
      [ apply (step_sb_atv source_segs regs5 0x11154 M rrom _ 13 10 _
                 (r + nat_to_word (length (prefix ++ firstn j s))) b
                 SF_11154 eq_refl SD_11154);
        [ unfold regs5; getr_resolve; rewrite v_addi_0;
          rewrite HlenF; reflexivity
        | unfold regs5, regs4, regs3; getr_resolve; reflexivity
        | store_ok_peel; apply Hgok; rewrite ?HlenF, ?word_add_nat; u_norm; lia ]
      | wlits;
        unfold Mnext, M;
        replace (prefix ++ firstn (S j) s)
          with ((prefix ++ firstn j s) ++ [b])
          by (rewrite (firstn_S_nth _ s j (Z_to_bv 8 0)) by lia;
              rewrite app_assoc; unfold b;
              rewrite (nth_lt_byte_at s j Hjlt); reflexivity);
        rewrite wbytes_snoc; reflexivity ]. }
    set (regs6 := regupd regs5 15 (nat_to_word (lp + S j))).
    assert (E8 : RiscvSemantics.step source_segs (mkst regs5 0x11158 Mnext rrom)
                 = MachineOk (mkst regs6 0x1115c Mnext rrom)).
    { eapply eq_trans;
      [ apply (step_addi_at source_segs regs5 0x11158 Mnext rrom _ 15 8 _
                 (nat_to_word (lp + S j)) SF_11158 eq_refl SD_11158 eq_refl);
        unfold regs5, regs4; getr_resolve; regupd_resolve;
        rewrite v_addi_0; f_equal; lia
      | wlits; reflexivity ]. }
    assert (E9 : RiscvSemantics.step source_segs (mkst regs6 0x1115c Mnext rrom)
                 = MachineOk (mkst regs6 0x1111c Mnext rrom)).
    { rewrite (step_jal_x0 source_segs regs6 0x1115c Mnext rrom _ _
                 SF_1115c eq_refl SD_1115c).
      wlits. reflexivity. }
    assert (H6' : reg_get regs6 6 = p).
    { unfold regs6, regs5, regs4, regs3, regs2, regs1. regupd_resolve. exact H6. }
    assert (H9' : reg_get regs6 9 = r).
    { unfold regs6, regs5, regs4, regs3, regs2, regs1. regupd_resolve. exact H9. }
    assert (H12' : reg_get regs6 12 = nat_to_word lp).
    { unfold regs6, regs5, regs4, regs3, regs2, regs1. regupd_resolve. exact H12. }
    assert (H15' : reg_get regs6 15 = nat_to_word (lp + S j))
      by (unfold regs6; apply regupd_same).
    destruct (IH (S j) regs6 ltac:(lia) H6' H9' H12' H15')
      as (regs' & Hag' & H8f & H13f & H15f & Hms').
    exists regs'. split; [|split; [|split; [|split]]].
    + intros x Hx8 Hx10 Hx13 Hx15. rewrite (Hag' x Hx8 Hx10 Hx13 Hx15).
      unfold regs6, regs5, regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + exact H8f.
    + exact H13f.
    + exact H15f.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      eapply mst_step; [reflexivity | exact E7 |].
      eapply mst_step; [reflexivity | exact E8 |].
      eapply mst_step; [reflexivity | exact E9 |].
      unfold Mnext in Hms'. exact Hms'.
Qed.

(* ================================================================= *)
(* Outer copy loop: 0x110f8 .. 0x11140                                *)
(*                                                                    *)
(* The separator is written BEFORE the argument (the gcc 9 build      *)
(* wrote it after), so the loop-head memory invariant is the          *)
(* separator-less [join1] prefix, becoming the [wjoin] prefix after   *)
(* the store at 0x11108.                                              *)
(* ================================================================= *)

(** Length of the wjoin prefix at outer index [i] (args 1..i-1 done,
    including the trailing separator), and its join1 companion
    (without it). *)
Definition pbW (i : nat) : nat := length (wjoin (firstn (i-1) (tl av))).
Definition pbJ (i : nat) : nat := length (join1 (firstn (i-1) (tl av))).

Lemma pbW_1 : pbW 1 = 0%nat.
Proof. reflexivity. Qed.

Lemma pbJ_1 : pbJ 1 = 0%nat.
Proof. reflexivity. Qed.

Lemma pbW_le : forall i, (pbW i <= totn)%nat.
Proof.
  intro i. unfold pbW, totn. rewrite length_wjoin.
  rewrite <- (firstn_skipn (i-1) (tl av)) at 2. rewrite tab_app. lia.
Qed.

Lemma pbW_pbJ : forall i, (2 <= i)%nat -> (i <= length av)%nat ->
  pbW i = S (pbJ i).
Proof.
  intros i H2 Hi. unfold pbW, pbJ.
  rewrite wjoin_join1
    by (apply firstn_nonnil; [lia | apply tl_nonnil]).
  rewrite length_app. cbn [length]. lia.
Qed.

Lemma pbJ_le : forall i, (pbJ i <= pbW i)%nat.
Proof.
  intro i. unfold pbW, pbJ.
  destruct (firstn (i-1) (tl av)) as [|x l] eqn:E.
  - cbn. lia.
  - rewrite wjoin_join1 by congruence. rewrite length_app. cbn [length]. lia.
Qed.

Lemma pbase_bound : forall i, (1 <= i)%nat -> (i < length av)%nat ->
  (pbW i + length (nth i av []) + 1 <= totn)%nat.
Proof.
  intros i H1 Hi. unfold pbW, totn.
  rewrite length_wjoin.
  assert (Hstep : (total_arg_bytes_nat (firstn (i-1) (tl av))
                    + length (nth i av []) + 1
                  = total_arg_bytes_nat (firstn i (tl av)))%nat).
  { replace i with (S (i-1)) at 3 by lia.
    rewrite (firstn_S_nth _ (tl av) (i-1) []) by (rewrite length_tl_av; lia).
    rewrite tab_app. rewrite nth_tl. replace (S (i-1)) with i by lia.
    cbn [total_arg_bytes_nat fold_right]. lia. }
  assert (Hle : (total_arg_bytes_nat (firstn i (tl av))
                 <= total_arg_bytes_nat (tl av))%nat).
  { rewrite <- (firstn_skipn i (tl av)) at 2. rewrite tab_app. lia. }
  lia.
Qed.

Lemma wjoin_firstn_step : forall i, (1 <= i)%nat -> (i < length av)%nat ->
  wjoin (firstn i (tl av))
  = wjoin (firstn (i-1) (tl av)) ++ nth i av [] ++ [Z_to_bv 8 32].
Proof.
  intros i H1 Hi.
  replace i with (S (i-1)) at 1 by lia.
  rewrite (firstn_S_nth _ (tl av) (i-1) []) by (rewrite length_tl_av; lia).
  rewrite nth_tl. replace (S (i-1)) with i by lia.
  generalize (firstn (i-1) (tl av)) as l. intro l.
  induction l as [|a l IHl]; [reflexivity|].
  cbn [wjoin app]. rewrite IHl, <- app_assoc. reflexivity.
Qed.

(** The join1 prefix after arg [i] is the wjoin prefix before it plus
    the arg itself. *)
Lemma join1_firstn_step : forall i, (1 <= i)%nat -> (i < length av)%nat ->
  join1 (firstn i (tl av)) = wjoin (firstn (i-1) (tl av)) ++ nth i av [].
Proof.
  intros i H1 Hi.
  replace i with (S (i-1)) at 1 by lia.
  rewrite (firstn_S_nth _ (tl av) (i-1) []) by (rewrite length_tl_av; lia).
  rewrite join1_snoc. rewrite nth_tl. replace (S (i-1)) with i by lia.
  reflexivity.
Qed.

Lemma join1_tl_split : forall i, (S i = length av)%nat -> (1 <= i)%nat ->
  join1 (tl av) = wjoin (firstn (i-1) (tl av)) ++ nth i av [].
Proof.
  intros i HSi H1.
  assert (Htl : (i = length (tl av))%nat) by (rewrite length_tl_av; lia).
  replace (tl av) with (firstn i (tl av)) at 1
    by (rewrite Htl; apply firstn_all).
  apply join1_firstn_step; lia.
Qed.

Lemma pbW_step : forall i, (1 <= i)%nat -> (i < length av)%nat ->
  pbW (S i) = (pbW i + length (nth i av []) + 1)%nat.
Proof.
  intros i H1 Hi. unfold pbW.
  replace (S i - 1)%nat with i by lia.
  rewrite (wjoin_firstn_step i H1 Hi).
  rewrite !length_app. cbn [length]. lia.
Qed.

Lemma pbJ_S : forall i, (1 <= i)%nat -> (i < length av)%nat ->
  pbJ (S i) = (pbW i + length (nth i av []))%nat.
Proof.
  intros i H1 Hi. unfold pbJ, pbW.
  replace (S i - 1)%nat with i by lia.
  rewrite (join1_firstn_step i H1 Hi).
  rewrite length_app. reflexivity.
Qed.

Lemma pbW_last : forall i, (S i = length av)%nat -> (1 <= i)%nat ->
  (pbW i + length (nth i av []))%nat = (totn - 1)%nat.
Proof.
  intros i HSi H1.
  pose proof join1_tl_len_nat as Hjl.
  rewrite (join1_tl_split i HSi H1) in Hjl.
  rewrite length_app in Hjl.
  unfold pbW. lia.
Qed.

(* ================================================================= *)
(* Outer copy driver: 0x110f8 .. exit at 0x11140                      *)
(* ================================================================= *)

Lemma source_copy_outer : forall r grant : word,
  (bv_unsigned tot <= bv_unsigned grant)%Z ->
  (bv_unsigned r + bv_unsigned grant <= bv_unsigned rsp - stack_max_size)%Z ->
  (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + bv_unsigned tot <= bv_unsigned rsp - stack_max_size)%Z ->
  region_free (segments_reserved source_segs) r tot = true ->
  forall f i regs,
  (1 <= i)%nat -> (i < length av)%nat -> (length av - i <= f)%nat ->
  reg_get regs 9 = r ->
  reg_get regs 16 = Z_to_bv 64 1 ->
  reg_get regs 17 = Z_to_bv 64 32 ->
  reg_get regs 14 = nat_to_word i ->
  reg_get regs 15 = nat_to_word (pbJ i) ->
  reg_get regs 18 = argcN ->
  reg_get regs 19 = Z_to_bv 64 (bv_unsigned rsp + 8) ->
  exists regs',
    (forall x : reg, x <> 6 -> x <> 8 -> x <> 10 -> x <> 12 -> x <> 13 ->
       x <> 14 -> x <> 15 -> reg_get regs' x = reg_get regs x) /\
    reg_get regs' 8 = tot /\
    reg_get regs' 13 = r + nat_to_word (totn - 1) /\
    msteps source_segs
      (mkst regs 0x110f8
        (wbytes (zmem fmem r grant) r (join1 (firstn (i-1) (tl av)))) rrom)
      (mkst regs' 0x11140
        (wbytes (zmem fmem r grant) r (join1 (tl av))) rrom).
Proof.
  intros r grant Hgrant Hgrantceil Hr0 Hceil Hfree.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi. pose proof stack_max_size_val as Hsms.
  pose proof tot_ge1 as Htg1. pose proof totN_bound as Htb.
  pose proof totn_bound as HtbZ. pose proof totn_ge1 as Htgn1.
  pose proof stack_max_size_val as Hacv. pose proof u_tot as Hut.
  pose proof (valid_argv_len av Hva) as HargcLe.
  set (base := zmem fmem r grant).
  induction f as [|f IH];
    intros i regs H1 Hi Hf H9 H16 H17 H14 H15 H18 H19; [lia|].
  assert (HiZ : (Z.of_nat i <= 1024)%Z) by (apply iN_le; lia).
  assert (HSiZ : (Z.of_nat (S i) <= 1024)%Z) by (apply iN_le; lia).
  assert (HniB : (Z.of_nat (length (nth i av [])) <= 131071)%Z)
    by (apply valid_argv_str_len; [exact Hva | lia]).
  pose proof (pbW_le i) as HpbLe. pose proof (pbW_le (S i)) as HpbLeS.
  pose proof (pbJ_le i) as HpbJle.
  pose proof (pbase_bound i H1 Hi) as Hpsb.
  destruct (sptr_bounds i ltac:(lia)) as [Hptrlo Hptrhi].
  set (M0 := wbytes base r (join1 (firstn (i-1) (tl av)))).
  set (MW := wbytes base r (wjoin (firstn (i-1) (tl av)))).
  assert (HlenW : length (wjoin (firstn (i-1) (tl av))) = pbW i) by reflexivity.
  assert (HlenJ : length (join1 (firstn (i-1) (tl av))) = pbJ i) by reflexivity.
  (* mv a2,a5 ; separator branch: reach 0x1110c with a2 = pbW i and
     memory = the wjoin prefix *)
  assert (HB : exists regsB,
     (forall x : reg, x <> 12 -> x <> 15 -> reg_get regsB x = reg_get regs x) /\
     reg_get regsB 12 = nat_to_word (pbW i) /\
     msteps source_segs (mkst regs 0x110f8 M0 rrom)
                        (mkst regsB 0x1110c MW rrom)).
  { set (regs1 := regupd regs 12 (nat_to_word (pbJ i))).
    assert (E0 : RiscvSemantics.step source_segs (mkst regs 0x110f8 M0 rrom)
                 = MachineOk (mkst regs1 0x110fc M0 rrom)).
    { eapply eq_trans;
      [ apply (step_addi_at source_segs regs 0x110f8 M0 rrom _ 12 15 _
                 (nat_to_word (pbJ i)) SF_110f8 eq_refl SD_110f8 eq_refl);
        getr_resolve; rewrite H15; apply v_addi_0
      | wlits; reflexivity ]. }
    destruct (Nat.eq_dec i 1) as [Hi1 | Hine].
    - (* i = 1: beq taken, no separator; the prefixes coincide ([]) *)
      exists regs1. split; [|split].
      + intros x Hx12 Hx15. unfold regs1.
        rewrite regupd_other by assumption. reflexivity.
      + unfold regs1. rewrite regupd_same. rewrite Hi1. reflexivity.
      + eapply mst_step; [reflexivity | exact E0 |].
        eapply mst_step;
          [ reflexivity
          | eapply step_beq_tk;
            [ exact SF_110fc | reflexivity | exact SD_110fc
            | unfold regs1; getr_resolve; regupd_resolve;
              rewrite H14, H16, Hi1; apply c_eq_refl ]
          | ].
        norm_pc.
        replace MW with M0 by (unfold MW, M0; rewrite Hi1; reflexivity).
        apply mst_refl.
    - (* i >= 2: separator before the arg *)
      assert (Hge2i : (2 <= i)%nat) by lia.
      set (regs2 := regupd regs1 12 (nat_to_word (pbW i))).
      set (regs3 := regupd regs2 15 (r + nat_to_word (pbJ i))).
      exists regs3. split; [|split].
      + intros x Hx12 Hx15. unfold regs3, regs2, regs1.
        rewrite !regupd_other by assumption. reflexivity.
      + unfold regs3, regs2. regupd_resolve. reflexivity.
      + eapply mst_step; [reflexivity | exact E0 |].
        (* beq a4,a6 fall-through *)
        eapply mst_step;
          [ reflexivity
          | eapply step_beq_ft;
            [ exact SF_110fc | reflexivity | exact SD_110fc
            | unfold regs1; getr_resolve; regupd_resolve;
              rewrite H14, H16; apply c_eq_neq;
              rewrite u_ntw by lia; u_norm; lia ]
          | norm_pc ].
        (* addi a2,a5,1 : a2 = pbJ i + 1 = pbW i *)
        eapply mst_step;
          [ reflexivity
          | eapply step_addi_at with (v := nat_to_word (pbW i));
            [ exact SF_11100 | reflexivity | exact SD_11100 | reflexivity
            | unfold regs1; getr_resolve; regupd_resolve; rewrite H15;
              rewrite v_addi_Sj by lia;
              rewrite (pbW_pbJ i Hge2i ltac:(lia)); reflexivity ]
          | norm_pc ].
        (* add a5,s1,a5 : a5 = r + pbJ i *)
        eapply mst_step;
          [ reflexivity
          | eapply step_add_at with (v := r + nat_to_word (pbJ i));
            [ exact SF_11104 | reflexivity | exact SD_11104 | reflexivity
            | unfold regs1; getr_resolve; regupd_resolve; rewrite H9, H15;
              rewrite v_add_word; reflexivity ]
          | norm_pc ].
        (* sb a7,0(a5) : separator at r + pbJ i *)
        eapply mst_step;
          [ reflexivity
          | eapply step_sb_atv with
              (a := r + nat_to_word (length (join1 (firstn (i-1) (tl av)))))
              (b := Z_to_bv 8 32);
            [ exact SF_11108 | reflexivity | exact SD_11108
            | getr_resolve; regupd_resolve; rewrite v_addi_0;
              rewrite HlenJ; reflexivity
            | unfold regs1; getr_resolve; regupd_resolve; rewrite H17; reflexivity
            | store_ok_peel; apply store_ok_zmem;
              rewrite ?HlenJ, ?word_add_nat; u_norm;
              rewrite (pbW_pbJ i Hge2i ltac:(lia)) in Hpsb; lia ]
          | step_simpl ].
        match goal with
        |- msteps _ (mkst ?R _ ?M _) _ =>
            replace M with MW
        end.
        2:{ unfold MW, M0.
            rewrite (wjoin_join1 (firstn (i-1) (tl av)))
              by (apply firstn_nonnil; [lia | apply tl_nonnil]).
            rewrite wbytes_snoc. reflexivity. }
        match goal with
        |- msteps _ (mkst ?R _ _ _) (mkst ?R' _ _ _) =>
            replace R' with R by (unfold regs3, regs2, regs1; reflexivity)
        end.
        apply mst_refl. }
  destruct HB as [regsB [HagB [H12B HmsB]]].
  assert (H9B : reg_get regsB 9 = r)
    by (rewrite (HagB 9) by reg_neq_tac; exact H9).
  assert (H14B : reg_get regsB 14 = nat_to_word i)
    by (rewrite (HagB 14) by reg_neq_tac; exact H14).
  assert (H16B : reg_get regsB 16 = Z_to_bv 64 1)
    by (rewrite (HagB 16) by reg_neq_tac; exact H16).
  assert (H17B : reg_get regsB 17 = Z_to_bv 64 32)
    by (rewrite (HagB 17) by reg_neq_tac; exact H17).
  assert (H18B : reg_get regsB 18 = argcN)
    by (rewrite (HagB 18) by reg_neq_tac; exact H18).
  assert (H19B : reg_get regsB 19 = Z_to_bv 64 (bv_unsigned rsp + 8))
    by (rewrite (HagB 19) by reg_neq_tac; exact H19).
  (* slli a5,a4,3 *)
  set (regs1 := regupd regsB 15 (Z_to_bv 64 (8 * Z.of_nat i))).
  assert (E1 : RiscvSemantics.step source_segs (mkst regsB 0x1110c MW rrom)
               = MachineOk (mkst regs1 0x11110 MW rrom)).
  { rewrite (step_slli source_segs regsB 0x1110c MW rrom _ 15 14 _
               SF_1110c eq_refl SD_1110c).
    reduce_bv_eqb_ifs. getr_resolve. rewrite H14B.
    imm_norm. rewrite v_slli3_nat by lia. wlits. reflexivity. }
  (* add a5,s3,a5 *)
  set (regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat i))).
  assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x11110 MW rrom)
               = MachineOk (mkst regs2 0x11114 MW rrom)).
  { eapply eq_trans;
    [ apply (step_add_at source_segs regs1 0x11110 MW rrom _ 15 19 15
               (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat i))
               SF_11110 eq_refl SD_11110 eq_refl);
      unfold regs1; getr_resolve; rewrite H19B;
      unfold v_add; u_norm; f_equal; lia
    | wlits; reflexivity ]. }
  (* ld t1,0(a5) : t1 = sptr i *)
  set (regs3 := regupd regs2 6 (sptr i)).
  assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x11114 MW rrom)
               = MachineOk (mkst regs3 0x11118 MW rrom)).
  { rewrite (step_ld source_segs regs2 0x11114 MW rrom _ 6 15 _
               (word_le8 (sptr i)) (sptr i) SF_11114 eq_refl SD_11114).
    - reduce_bv_eqb_ifs. wlits. reflexivity.
    - unfold regs2. getr_resolve. rewrite v_addi_0.
      unfold MW. rewrite rdn_wbytes_disjoint
        by (rewrite ?HlenW; u_norm; lia).
      unfold base. rewrite rdn_zmem_out by (u_norm; lia).
      apply read_arg_ptr_f. lia.
    - exact (bytes_le_n_to_le_8 _). }
  (* mv a5,a2 : a5 = pbW i *)
  set (regs4 := regupd regs3 15 (nat_to_word (pbW i + 0))).
  assert (E4 : RiscvSemantics.step source_segs (mkst regs3 0x11118 MW rrom)
               = MachineOk (mkst regs4 0x1111c MW rrom)).
  { eapply eq_trans;
    [ apply (step_addi_at source_segs regs3 0x11118 MW rrom _ 15 12 _
               (nat_to_word (pbW i + 0)) SF_11118 eq_refl SD_11118 eq_refl);
      unfold regs3, regs2, regs1; getr_resolve; regupd_resolve;
      rewrite H12B; rewrite v_addi_0; f_equal; lia
    | wlits; reflexivity ]. }
  (* inner byte copy of arg i at the wjoin-prefix offset *)
  assert (Hrdb : forall j, (j <= length (nth i av []))%nat ->
    rdn source_segs base (sptr i + nat_to_word j) 1%nat
    = Some [byte_at (nth i av []) j]).
  { intros j Hj. unfold base.
    rewrite rdn_zmem_out by (rewrite word_add_nat; u_norm; lia).
    apply read_arg_byte_f; lia. }
  destruct (source_copy_inner base r (sptr i) (nth i av [])
              (wjoin (firstn (i-1) (tl av))) Hr0 Hceil Hfree
              ltac:(apply arg_nz_k; lia)
              ltac:(rewrite HlenW; exact Hpsb)
              ltac:(lia) ltac:(lia)
              Hrdb
              ltac:(unfold base; apply store_grant_zmem_prefix;
                    [ exact Hgrant | lia ])
              (length (nth i av [])) O regs4
              ltac:(lia)
              ltac:(unfold regs4, regs3; regupd_resolve; reflexivity)
              ltac:(unfold regs4, regs3, regs2, regs1; regupd_resolve; exact H9B)
              ltac:(unfold regs4, regs3, regs2, regs1; regupd_resolve;
                    rewrite H12B; rewrite HlenW; reflexivity)
              ltac:(unfold regs4; rewrite regupd_same; rewrite HlenW; reflexivity))
    as (regsI & HagI & H8I & H13I & H15I & HmsI).
  assert (HmemI : wbytes base r
      (wjoin (firstn (i-1) (tl av)) ++ firstn 0 (nth i av [])) = MW).
  { unfold MW. rewrite app_nil_r. reflexivity. }
  rewrite HmemI in HmsI.
  set (M1 := wbytes base r (wjoin (firstn (i-1) (tl av)) ++ nth i av [])) in *.
  assert (HpresI : forall x : reg, x <> 6 -> x <> 8 -> x <> 10 -> x <> 12 ->
                   x <> 13 -> x <> 15 ->
                   reg_get regsI x = reg_get regsB x).
  { intros x Hx6 Hx8 Hx10 Hx13' Hx13 Hx15.
    rewrite (HagI x Hx8 Hx10 Hx13 Hx15).
    unfold regs4, regs3, regs2, regs1.
    rewrite !regupd_other by assumption. reflexivity. }
  assert (H14I : reg_get regsI 14 = nat_to_word i)
    by (rewrite HpresI by reg_neq_tac; exact H14B).
  assert (H18I : reg_get regsI 18 = argcN)
    by (rewrite HpresI by reg_neq_tac; exact H18B).
  (* addi a4,a4,1 : a4 = i+1 *)
  set (regsA := regupd regsI 14 (nat_to_word (S i))).
  assert (EA : RiscvSemantics.step source_segs (mkst regsI 0x11134 M1 rrom)
               = MachineOk (mkst regsA 0x11138 M1 rrom)).
  { rewrite (step_addi source_segs regsI 0x11134 M1 rrom _ 14 14 _
               SF_11134 eq_refl SD_11134).
    reduce_bv_eqb_ifs. getr_resolve. rewrite H14I.
    rewrite v_addi_Sj by lia. wlits. reflexivity. }
  (* sext.w a2,a4 : a2 = i+1 *)
  set (regsC := regupd regsA 12 (nat_to_word (S i))).
  assert (EB : RiscvSemantics.step source_segs (mkst regsA 0x11138 M1 rrom)
               = MachineOk (mkst regsC 0x1113c M1 rrom)).
  { rewrite (step_addiw source_segs regsA 0x11138 M1 rrom _ 12 14 _
               SF_11138 eq_refl SD_11138).
    reduce_bv_eqb_ifs. unfold regsA. getr_resolve.
    rewrite v_addiw_id by (rewrite u_ntw by lia; lia).
    wlits. reflexivity. }
  assert (H12C : reg_get regsC 12 = nat_to_word (S i))
    by (unfold regsC; apply regupd_same).
  assert (H18C : reg_get regsC 18 = argcN).
  { unfold regsC, regsA. regupd_resolve. exact H18I. }
  assert (HM1J : M1 = wbytes base r (join1 (firstn (S i - 1) (tl av)))).
  { unfold M1. replace (S i - 1)%nat with i by lia.
    rewrite (join1_firstn_step i H1 Hi). reflexivity. }
  destruct (lt_dec (S i) (length av)) as [Hlti | Hge].
  - (* blt taken: next arg *)
    assert (EC : RiscvSemantics.step source_segs (mkst regsC 0x1113c M1 rrom)
                 = MachineOk (mkst regsC 0x110f8 M1 rrom)).
    { rewrite (step_blt_tk source_segs regsC 0x1113c M1 rrom _ 12 18 _
                 SF_1113c eq_refl SD_1113c).
      - wlits. reflexivity.
      - getr_resolve. rewrite H12C, H18C.
        rewrite c_lts_small by (rewrite ?u_ntw, ?u_argcN by lia; lia).
        apply Z.ltb_lt. rewrite u_ntw by lia. rewrite u_argcN. lia. }
    assert (H9C : reg_get regsC 9 = r).
    { unfold regsC, regsA. regupd_resolve.
      rewrite HpresI by reg_neq_tac. exact H9B. }
    assert (H16C : reg_get regsC 16 = Z_to_bv 64 1).
    { unfold regsC, regsA. regupd_resolve.
      rewrite HpresI by reg_neq_tac. exact H16B. }
    assert (H17C : reg_get regsC 17 = Z_to_bv 64 32).
    { unfold regsC, regsA. regupd_resolve.
      rewrite HpresI by reg_neq_tac. exact H17B. }
    assert (H14C : reg_get regsC 14 = nat_to_word (S i)).
    { unfold regsC. rewrite regupd_other by discriminate.
      unfold regsA. apply regupd_same. }
    assert (H15C : reg_get regsC 15 = nat_to_word (pbJ (S i))).
    { unfold regsC, regsA. regupd_resolve.
      rewrite H15I. rewrite HlenW.
      rewrite (pbJ_S i H1 Hi). reflexivity. }
    assert (H19C : reg_get regsC 19 = Z_to_bv 64 (bv_unsigned rsp + 8)).
    { unfold regsC, regsA. regupd_resolve.
      rewrite HpresI by reg_neq_tac. exact H19B. }
    destruct (IH (S i) regsC ltac:(lia) Hlti ltac:(lia)
                H9C H16C H17C H14C H15C H18C H19C)
      as (regs' & Hag' & H8' & H13' & Hms').
    exists regs'. split; [| split; [| split]].
    + intros x Hx6 Hx8 Hx10 Hx12 Hx13 Hx14 Hx15.
      rewrite (Hag' x Hx6 Hx8 Hx10 Hx12 Hx13 Hx14 Hx15).
      unfold regsC, regsA. rewrite !regupd_other by assumption.
      rewrite HpresI by assumption.
      apply HagB; assumption.
    + exact H8'.
    + exact H13'.
    + eapply msteps_trans; [exact HmsB |].
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply msteps_trans; [exact HmsI |].
      eapply mst_step; [reflexivity | exact EA |].
      eapply mst_step; [reflexivity | exact EB |].
      eapply mst_step; [reflexivity | exact EC |].
      rewrite <- HM1J in Hms'. exact Hms'.
  - (* blt fall-through: last arg done *)
    assert (HSieq : (S i = length av)%nat) by lia.
    assert (EC : RiscvSemantics.step source_segs (mkst regsC 0x1113c M1 rrom)
                 = MachineOk (mkst regsC 0x11140 M1 rrom)).
    { rewrite (step_blt_ft source_segs regsC 0x1113c M1 rrom _ 12 18 _
                 SF_1113c eq_refl SD_1113c).
      - wlits. reflexivity.
      - getr_resolve. rewrite H12C, H18C.
        rewrite c_lts_small by (rewrite ?u_ntw, ?u_argcN by lia; lia).
        apply Z.ltb_ge. rewrite u_ntw by lia. rewrite u_argcN. lia. }
    assert (Hlast : (pbW i + length (nth i av []))%nat = (totn - 1)%nat)
      by (apply pbW_last; [exact HSieq | lia]).
    assert (HM1 : M1 = wbytes base r (join1 (tl av))).
    { unfold M1. rewrite (join1_tl_split i HSieq ltac:(lia)). reflexivity. }
    exists regsC. split; [| split; [| split]].
    + intros x Hx6 Hx8 Hx10 Hx12 Hx13 Hx14 Hx15.
      unfold regsC, regsA. rewrite !regupd_other by assumption.
      rewrite HpresI by assumption.
      apply HagB; assumption.
    + unfold regsC, regsA. regupd_resolve.
      rewrite H8I. rewrite HlenW. unfold tot. f_equal.
      pose proof totn_ge1. lia.
    + unfold regsC, regsA. regupd_resolve.
      rewrite H13I. rewrite HlenW. do 2 f_equal. lia.
    + rewrite <- HM1.
      eapply msteps_trans; [exact HmsB |].
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply msteps_trans; [exact HmsI |].
      eapply mst_step; [reflexivity | exact EA |].
      eapply mst_step; [reflexivity | exact EB |].
      eapply mst_step; [reflexivity | exact EC |].
      apply mst_refl.
Qed.

(* ================================================================= *)
(* Entry to the first brk ecall                                       *)
(* ================================================================= *)

Lemma source_to_brk1 : (bv_unsigned tot <= 65536)%Z ->
  exists regs3,
    reg_get regs3 1 = (0x1108c : word) /\
    reg_get regs3 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs3 8 = tot /\
    reg_get regs3 10 = Z_to_bv 64 0 /\
    reg_get regs3 18 = argcN /\
    reg_get regs3 19 = Z_to_bv 64 (bv_unsigned rsp + 8) /\
    msteps source_segs
      (init_machine_state (run_segments source_segs inp rsp rmb) 0x11190 source_phdrs rsp rmb rrnd inp)
      {| ms_regs := regs3; ms_fregs := fp_regs; ms_pc_val := (0x111e0 : word);
         ms_svc_pending := Some (Z_to_bv 64 214); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := fmem; ms_rom := rrom |}.
(** NINETEEN instructions in ONE reflective block, with no memory
    traffic at all: the [tot <= 65536] test, main's six argument [li]s
    and the [li a0,214], the [jal] into the crt's [raw_syscall] and its
    seven register moves, stopping at the [ecall] that is the allocator
    branch point.  The only pinned register is [s0], holding the
    accumulated length; the only obligation is the [bltu]. *)
Proof.
  intros Hcap.
  pose proof rsp_lo_num as Hlon. pose proof tot_ge1 as Htotg.
  pose proof totN_bound as Htotb.
  pose proof join1_tl_len_nat as Hjl. pose proof totn_bound as Htn.
  destruct source_after_length as (regs2 & H2 & H18 & H19 & H8 & Hms).
  (* the executor's spelling of [addi s0,s0,1]: [v_addi] is this term
     definitionally, but [rewrite] needs the spelling that occurs. *)
  assert (Htotv : Z_to_bv 64 (bv_unsigned (nat_to_word (length (join1 (tl av)))) + 1)
                  = tot).
  { change (Z_to_bv 64 (bv_unsigned (nat_to_word (length (join1 (tl av)))) + 1))
      with (v_addi (nat_to_word (length (join1 (tl av)))) 1).
    rewrite v_addi_Sj by lia. exact S_join1_tot. }
  replace (0x1105c : word) with (Z_to_bv 64 0x1105c) in Hms by bveq.
  sym_block_ex source_segs (mkst regs2 (Z_to_bv 64 0x1105c) fmem rrom)
    19%nat [false] (@nil expr)
    [((8 : reg), EVar 32)] [nat_to_word (length (join1 (tl av)))] (@nil word)
    RA HRA Hms2.
  { (* [bltu a5,s0] at 0x11068 -> not taken, because [tot <= 65536] *)
    rewrite Htotv; sym_br. }
  { (* the [s0] pin: the accumulated length *) exact H8. }
  exists RA.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  1-6: (sym_regs HRA;
        first [ reflexivity | assumption | exact Htotv
              | (f_equal; lia) | (apply bv_eq; u_norm; lia) | bveq ]).
  eapply msteps_trans; [ exact Hms | ].
  eapply msteps_trans; [ exact Hms2 | ]. norm_pc; sym_pc_lit.
  eapply mst_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_111e0 eq_refl) | ].
  match goal with
  | |- msteps _ {| ms_regs := ?R |} _ =>
      replace (getr R 17) with (Z_to_bv 64 214)
        by (sym_regs HRA; sym_close)
  end.
  apply mst_refl.
Qed.

(* ================================================================= *)
(* From the first brk (a0 = r <> 0, no wrap) to the second brk ecall  *)
(* ================================================================= *)

Lemma source_to_brk2 : forall regs3 (r : word),
  reg_get regs3 1 = (0x1108c : word) ->
  reg_get regs3 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs3 8 = tot ->
  reg_get regs3 18 = argcN ->
  reg_get regs3 19 = Z_to_bv 64 (bv_unsigned rsp + 8) ->
  r <> Z_to_bv 64 0 ->
  (bv_unsigned r + bv_unsigned tot < 2^64)%Z ->
  exists regs5,
    reg_get regs5 1 = (0x110e0 : word) /\
    reg_get regs5 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs5 8 = r + tot /\
    reg_get regs5 9 = r /\
    reg_get regs5 10 = r + tot /\
    reg_get regs5 18 = argcN /\
    reg_get regs5 19 = Z_to_bv 64 (bv_unsigned rsp + 8) /\
    msteps source_segs (mkst (regupd regs3 10 r) 0x111e4 fmem rrom)
      {| ms_regs := regs5; ms_fregs := fp_regs; ms_pc_val := (0x111e0 : word);
         ms_svc_pending := Some (Z_to_bv 64 214); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := fmem; ms_rom := rrom |}.
(** TWENTY instructions in ONE reflective block, with no memory
    traffic: [raw_syscall]'s [ret] (literal because [ra] is PINNED),
    main's [r <> 0] test, the [r + tot] no-wrap test, the seven
    arguments of the second [brk], the [jal] back into [raw_syscall]
    and its seven moves, stopping at the [ecall].  Two branches, so two
    [SCBr]s, and nothing else. *)
Proof.
  intros regs3 r H1 H2 H8 H18 H19 Hrnz Hw.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tot_ge1. pose proof totN_bound.
  pose proof (u64_range r) as Hur.
  pose proof (word_neq0_unsigned r Hrnz) as Hur0.
  assert (Hurt : bv_unsigned (r + tot) = (bv_unsigned r + bv_unsigned tot)%Z)
    by (apply u_add_small; exact Hw).
  sym_block_ex source_segs
    (mkst (regupd regs3 10 r) (Z_to_bv 64 0x111e4) fmem rrom)
    20%nat [true; false] (@nil expr)
    [((1 : reg), ELit 0x1108c); ((10 : reg), EVar 32); ((8 : reg), EVar 33)]
    [r; tot] (@nil word) RA HRA Hms.
  { (* [bgeu a0,s0] at 0x110bc -> not taken: [r < r + tot] *)
    apply negb_false_iff; rewrite v_add_word, (word_add_comm tot r);
    unfold bv_ltu; apply Z.ltb_lt; rewrite Hurt; lia. }
  { (* [bnez a0] at 0x11090 -> taken, because the brk returned nonzero *)
    sym_br. }
  { (* the [ra] pin *) getr_resolve; regupd_resolve; rewrite H1; bveq. }
  { (* the [a0] pin *) getr_resolve; regupd_resolve; reflexivity. }
  { (* the [s0] pin *) getr_resolve; regupd_resolve; exact H8. }
  exists RA.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  1-7: (sym_regs HRA;
        first [ reflexivity | assumption | apply word_add_comm
              | (getr_resolve; regupd_resolve; assumption)
              | (f_equal; lia) | (apply bv_eq; u_norm; lia) | bveq ]).
  replace (0x111e4 : word) with (Z_to_bv 64 0x111e4) by bveq.
  eapply msteps_trans; [ exact Hms | ]. norm_pc; sym_pc_lit.
  eapply mst_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_111e0 eq_refl) | ].
  match goal with
  | |- msteps _ {| ms_regs := ?R |} _ =>
      replace (getr R 17) with (Z_to_bv 64 214)
        by (sym_regs HRA; sym_close)
  end.
  apply mst_refl.
Qed.

(* ================================================================= *)
(* Success tail: from the second brk's grant to the write and exit 0  *)
(* ================================================================= *)

(* ================================================================= *)
(* The put-style write-all retry loop                                 *)
(* ================================================================= *)

(** The loop's only store is musl's own [ra] spill, inside the
    RLIMIT_STACK window. *)
Lemma aj_sok8 : forall (mem : word -> option byte) (a : word),
  mem_grows wmem mem ->
  (bv_unsigned rsp - 80 <= bv_unsigned a)%Z ->
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

Local Ltac aj_grows := solve_mem_grows.

Local Ltac aj_sok := apply aj_sok8; [ aj_grows | u_norm; lia | u_norm; lia ].

Local Ltac aj_ssd F D aexp vexp vtac := stepsd F D aexp vexp vtac ltac:(aj_sok).

Local Ltac aj_sld F D aexp vexp readtac := stepld F D aexp vexp readtac.

(** After a (possibly short) delivery of [k] bytes the machine sits at
    0x112f0 ([__syscall_cp_c]'s post-ecall [ret]) with
    a0 = [len_word (firstn k rest)].  It returns through musl's [write]
    wrapper and [__syscall_ret] to main's drain loop, which keeps the
    running pointer in s4 and the running count in s0 (register-only;
    the only store on the path is musl's own [ra] spill).  Induction on
    [fuel >= length rest]. *)
Lemma src_put_wall : forall fuel (rest : list byte) (p : word) k regs mem,
  (length rest <= fuel)%nat ->
  (1 <= k)%nat -> (k <= length rest)%nat ->
  (Z.of_nat (length rest) <= 2097152)%Z ->
  (0 < bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) <= bv_unsigned rsp - 80)%Z ->
  reg_get regs 1 = (0x1128c : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ->
  reg_get regs 8 = len_word rest ->
  reg_get regs 10 = len_word (firstn k rest) ->
  reg_get regs 20 = p ->
  bv_unsigned (reg_get regs 17) = 64%Z ->
  mem_grows wmem mem ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8%nat
    = Some (word_to_le_bytes 8 (0x11170 : word)) ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
    = Some (word_to_le_bytes 8 (0x111bc : word)) ->
  (forall a : word,
     In a [Z_to_bv 64 (bv_unsigned rsp - 16); Z_to_bv 64 (bv_unsigned rsp - 24);
           Z_to_bv 64 (bv_unsigned rsp - 32); Z_to_bv 64 (bv_unsigned rsp - 40);
           Z_to_bv 64 (bv_unsigned rsp - 48)] ->
     rdn source_segs mem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  rdn source_segs mem p (length rest) = Some rest ->
  to_wall_tail source_segs (Z_to_bv 64 1)
    (mkst regs (0x112f0 : word) mem rrom)
    (skipn k rest)
    (to_wallexit source_segs (Z_to_bv 64 1) [] (Z_to_bv 64 0)).
Proof.
  induction fuel as [|fuel IH];
    intros rest p k regs mem Hfuel Hk1 Hk2 Hlen Hplo Hphi
           H1 H2 H8 H10 H20 H17 Hgrow Hra56 Hslra Hsl Hread.
  { lia. }
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi. pose proof stack_max_size_val as Hsms.
  (* 0x112f0: ret out of __syscall_cp_c, back into the write wrapper *)
  stepjr SF_112f0 SD_112f0 (0x1128c : word) ltac:(getr_resolve; exact H1).
  (* 0x1128c: ld ra,8(sp) -- the wrapper's saved ra (0x11170) *)
  aj_sld SF_1128c SD_1128c (Z_to_bv 64 (bv_unsigned rsp - 56))
    (0x11170 : word) ltac:(exact Hra56).
  (* 0x11290: addi sp,sp,16 -- pop the wrapper frame *)
  stepiv SF_11290 SD_11290 (Z_to_bv 64 (bv_unsigned rsp - 48))
    ltac:(getr_resolve; rewrite H2; sp_norm; f_equal; lia).
  (* 0x11294: j __syscall_ret *)
  stepj SF_11294 SD_11294.
  (* 0x11298: lui a5,0xfffff *)
  stepi SF_11298 SD_11298.
  (* 0x1129c: bltu a5,a0 falls through (the delivery is no error) *)
  step_intro;
    [ reflexivity
    | eapply step_bltu_ft;
      [ exact SF_1129c | reflexivity | exact SD_1129c
      | getr_resolve; rewrite H10;
        rewrite c_ltu_ltb; apply Z.ltb_ge;
        match goal with |- context [bv_unsigned (v_lui ?z)] =>
          replace (bv_unsigned (v_lui z)) with 18446744073709547520%Z
            by (vm_compute; reflexivity)
        end;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x112a0: ret -- back into main's drain loop at 0x11170 *)
  stepjr SF_112a0 SD_112a0 (0x11170 : word) ltac:(getr_resolve; reflexivity).
  (* 0x11170: blez a0 falls through (the delivery is nonempty) *)
  step_intro;
    [ reflexivity
    | eapply step_bge_ft;
      [ exact SF_11170 | reflexivity | exact SD_11170
      | getr_resolve; rewrite H10; apply c_lts_0_pos;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x11174: add s4,s4,a0 -- the pointer bump *)
  stepiv SF_11174 SD_11174 (Z_to_bv 64 (bv_unsigned p + Z.of_nat k))
    ltac:(getr_resolve; rewrite H20, H10; apply v_add_len_firstn_Z; lia).
  (* 0x11178: sub s0,s0,a0 -- the count decrement *)
  stepiv SF_11178 SD_11178 (len_word (skipn k rest))
    ltac:(getr_resolve; rewrite H8, H10; apply v_sub_len_firstn; lia).
  (* 0x1117c: j 0x11148 -- the loop test *)
  stepj SF_1117c SD_1117c.
  destruct (Nat.eq_dec k (length rest)) as [-> | Hne].
  - (* full delivery: bnez s0 not taken, fall into the exit-0 tail *)
    rewrite skipn_all.
    step_intro;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact SF_11148 | reflexivity | exact SD_11148
        | getr_resolve; apply c_eq_0_of_u; reflexivity ]
      | norm_pc ].
    (* 0x1114c: li a0,0 *)
    stepiv SF_1114c SD_1114c (Z_to_bv 64 0) ltac:(getr_resolve; bveq).
    (* 0x11150: j 0x11098 -- main's epilogue *)
    stepj SF_11150 SD_11150.
    apply twt_done. cbn [to_wallexit].
    apply source_epilogue.
    + regupd_resolve; reflexivity.
    + regupd_resolve; reflexivity.
    + u_norm; lia.
    + exact Hslra.
    + exact Hsl.
  - (* short delivery: bnez s0 taken, reissue on the remainder *)
    step_intro;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact SF_11148 | reflexivity | exact SD_11148
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* 0x11160: mv a2,s0 -- the remaining count *)
    stepiv SF_11160 SD_11160 (len_word (skipn k rest))
      ltac:(getr_resolve; apply v_addi_0).
    (* 0x11164: mv a1,s4 -- the bumped pointer *)
    stepiv SF_11164 SD_11164 (Z_to_bv 64 (bv_unsigned p + Z.of_nat k))
      ltac:(getr_resolve; apply v_addi_0).
    (* 0x11168: li a0,1 -- the fd *)
    stepiv SF_11168 SD_11168 (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* 0x1116c: jal write() *)
    stepj SF_1116c SD_1116c.
    (* the wrapper: frame, arg shuffle, ra spill, __syscall_cp *)
    stepiv SF_11264 SD_11264 (Z_to_bv 64 (bv_unsigned rsp - 64))
      ltac:(getr_resolve; sp_norm; f_equal; lia).
    stepiv SF_11268 SD_11268 (len_word (skipn k rest))
      ltac:(getr_resolve; apply v_addi_0).
    stepi SF_1126c SD_1126c.
    stepiv SF_11270 SD_11270 (Z_to_bv 64 (bv_unsigned p + Z.of_nat k))
      ltac:(getr_resolve; apply v_addi_0).
    stepi SF_11274 SD_11274.
    stepiv SF_11278 SD_11278 (Z_to_bv 64 1)
      ltac:(getr_resolve; apply v_addi_0).
    stepi SF_1127c SD_1127c.
    stepiv SF_11280 SD_11280 (Z_to_bv 64 64) ltac:(getr_resolve; bveq).
    aj_ssd SF_11284 SD_11284 (Z_to_bv 64 (bv_unsigned rsp - 56))
      (0x11170 : word) ltac:(getr_resolve; bveq).
    stepj SF_11288 SD_11288.
    (* 0x112f4: __syscall_cp's trampoline into __syscall_cp_c *)
    stepj SF_112f4 SD_112f4.
    (* __syscall_cp_c's seven shuffles *)
    stepiv SF_112d0 SD_112d0 (Z_to_bv 64 64) ltac:(getr_resolve; apply v_addi_0).
    stepiv SF_112d4 SD_112d4 (Z_to_bv 64 1) ltac:(getr_resolve; apply v_addi_0).
    stepiv SF_112d8 SD_112d8 (Z_to_bv 64 (bv_unsigned p + Z.of_nat k))
      ltac:(getr_resolve; apply v_addi_0).
    stepiv SF_112dc SD_112dc (len_word (skipn k rest))
      ltac:(getr_resolve; apply v_addi_0).
    stepi SF_112e0 SD_112e0.
    stepi SF_112e4 SD_112e4.
    stepi SF_112e8 SD_112e8.
    (* 0x112ec: ecall -- the reissued write *)
    eapply twt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ SF_112ec eq_refl) |].
    apply twt_more; [rewrite length_skipn; lia|].
    apply (twl_write_rec source_segs (Z_to_bv 64 1)).
    + getr_resolve; first [ exact H17 | vm_compute; reflexivity ].
    + regupd_resolve; reflexivity.
    + match goal with
      | |- ms_read_bytes _ (reg_get ?R 11) (reg_get ?R 12) = Some _ =>
          replace (reg_get R 11)
            with (Z_to_bv 64 (bv_unsigned p + Z.of_nat k))
            by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word (skipn k rest))
            by (regupd_resolve; reflexivity)
      end.
      rewrite (ms_read_bytes_rdn (run_segments source_segs inp rsp rmb)) by reflexivity;
        unfold run_segments; apply rdn_lift.
      cbn [ms_mem].
      replace (word_to_nat (len_word (skipn k rest)))
        with (length (skipn k rest))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      rewrite !rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes, ?length_skipn; u_norm; lia).
      pose proof (rdn_skipn source_segs mem (length rest) p rest k Hread Hk2)
        as Hsk.
      rewrite word_add_nat_Z in Hsk by lia.
      rewrite length_skipn. exact Hsk.
    + (* [vfs_write]'s [access_ok] on the remaining range *)
      match goal with
      | |- access_okb (reg_get ?R 11) (bv_unsigned (reg_get ?R 12)) = true =>
          replace (reg_get R 11)
            with (Z_to_bv 64 (bv_unsigned p + Z.of_nat k))
            by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word (skipn k rest))
            by (regupd_resolve; reflexivity)
      end.
      pose proof rsp_hi_num.
      apply Uaccess.access_okb_intro.
      rewrite u_len_word by (rewrite length_skipn; lia).
      rewrite u_Z2bv by lia. rewrite length_skipn. unfold TASK_SIZE. lia.
    + rewrite length_skipn; lia.
    + intros m Hm1 Hm2.
      norm_pc.
      apply (IH (skipn k rest) (Z_to_bv 64 (bv_unsigned p + Z.of_nat k)) m).
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
      * regupd_resolve; reflexivity.
      * regupd_resolve; first [ exact H17 | vm_compute; reflexivity ].
      * aj_grows.
      * apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        exact Hslra.
      * intros a Ha.
        assert (Hab : (bv_unsigned rsp - 48 <= bv_unsigned a
                       /\ bv_unsigned a + 8 <= bv_unsigned rsp - 8)%Z).
        { repeat destruct Ha as [<-|Ha]; try (exfalso; exact Ha); u_norm; lia. }
        rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        apply Hsl. exact Ha.
      * rewrite !rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes, ?length_skipn; u_norm; lia).
        pose proof (rdn_skipn source_segs mem (length rest) p rest k Hread Hk2)
          as Hsk.
        rewrite word_add_nat_Z in Hsk by lia.
        rewrite length_skipn. exact Hsk.
Qed.

Lemma source_success : forall regs (r grant : word),
  (bv_unsigned tot <= bv_unsigned grant)%Z ->
  (bv_unsigned r + bv_unsigned grant <= bv_unsigned rsp - stack_max_size)%Z ->
  (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + bv_unsigned tot <= bv_unsigned rsp - stack_max_size)%Z ->
  region_free (segments_reserved source_segs) r tot = true ->
  reg_get regs 1 = (0x110e0 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 8 = r + tot ->
  reg_get regs 9 = r ->
  reg_get regs 10 = r + tot ->
  reg_get regs 18 = argcN ->
  reg_get regs 19 = Z_to_bv 64 (bv_unsigned rsp + 8) ->
  to_wallexit source_segs (Z_to_bv 64 1) [jout av] (Z_to_bv 64 0)
    (mkst regs 0x111e4 (zmem fmem r grant) rrom).
Proof.
  intros regs r grant Hgrant Hgrantceil Hr0 Hceil Hfree
    H1 H2 H8 H9 H10 H18 H19.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof tot_ge1 as Htg1. pose proof totN_bound as Htb.
  pose proof totn_bound as HtbZ. pose proof totn_ge1 as Htgn1.
  split; [rewrite jout_len_nat; lia|].
  pose proof u_tot as Hut.
  pose proof (u64_range r) as Hur.
  assert (HgrantceilN :
      (bv_unsigned r + bv_unsigned grant <= bv_unsigned rsp - 8388608)%Z)
    by exact Hgrantceil.
  assert (HceilN : (bv_unsigned r + bv_unsigned tot <= bv_unsigned rsp - 8388608)%Z)
    by exact Hceil.
  assert (Hurt : bv_unsigned (r + tot) = (bv_unsigned r + bv_unsigned tot)%Z)
    by (apply u_add_small; lia).
  set (mem0 := zmem fmem r grant).
  (* SEVEN instructions in ONE reflective block: [raw_syscall]'s [ret]
     (literal because [ra] is pinned), main's "the brk moved where we
     asked" test and the five constants the copy loop runs on.  No
     memory traffic; one branch. *)
  sym_block source_segs 7%nat [false] (@nil expr)
    [((1 : reg), ELit 0x110e0); ((8 : reg), EVar 32); ((10 : reg), EVar 33);
     ((9 : reg), EVar 34)]
    [r + tot; r + tot; r] (@nil word) RA HRA.
  { (* [bne s0,a0] at 0x110e0 -> not taken: the grant is what was asked *)
    apply negb_false_iff; rewrite bv_eqb_Z; apply Z.eqb_refl. }
  1-4: (getr_resolve;
        first [ exact H8 | exact H10 | exact H9 | (rewrite H1; bveq) ]).
  (* the nested copy loops *)
  lazymatch goal with
  | |- to_wall_tail _ _ (mkst ?R _ _ _) _ _ =>
    edestruct (source_copy_outer r grant Hgrant Hgrantceil Hr0 Hceil Hfree
                 (length av) 1%nat R)
      as (regsC & HagC & H8C & H13C & HmsC)
  end.
  { lia. } { pose proof Hge2; lia. } { lia. }
  1-7: (sym_regs HRA;
        first [ reflexivity | assumption
              | (getr_resolve; regupd_resolve; assumption)
              | (f_equal; lia) | (apply bv_eq; u_norm; lia) | bveq ]).
  eapply msteps_to_wall_tail; [ exact HmsC | ].
  pose proof (u64_range (r + nat_to_word (totn - 1))) as Hurn.
  (* the executor spells the [sb]'s address with an explicit [+0] *)
  assert (Hsba : Z_to_bv 64 (bv_unsigned (r + nat_to_word (totn - 1)) + 0)
                 = r + nat_to_word (totn - 1))
    by (apply bv_eq; rewrite u_Z2bv by lia; lia).
  (* TWENTY-FIVE instructions in ONE reflective block: the trailing
     newline store, the drain loop's first trip, main's three write
     arguments and the [jal] into musl's write wrapper, the wrapper's
     frame push and its [ra] spill, [__syscall_cp] and
     [__syscall_cp_c]'s seven moves, stopping at the write [ecall].
     Two stores and one branch; the four registers the run reads out of
     the copy loop ([sp], [s0], [a3], [s4]) are pinned. *)
  set (memJ := wbytes mem0 r (jout av)).
  set (memW1 := wbytes memJ (Z_to_bv 64 (bv_unsigned rsp - 56))
                  (word_to_le_bytes 8 (0x11170 : word))).
  match goal with
  |- to_wall_tail _ _ (mkst _ _ _ _) _ _ =>
    sym_block source_segs 25%nat [true] (@nil expr)
      [((2 : reg), EVar 32); ((8 : reg), EVar 33); ((13 : reg), EVar 34);
       ((20 : reg), EVar 35)]
      [Z_to_bv 64 (bv_unsigned rsp - 48); tot;
       r + nat_to_word (totn - 1); r] (@nil word) RB HRB
  end.
  { (* [sd ra,8(sp)] at 0x11284 -> the wrapper's frame *)
    solve_store_ok_inv. }
  { (* [bnez s0] at 0x11148 -> taken, because [tot <> 0] *)
    apply negb_true_iff; rewrite bv_eqb_Z; apply Z.eqb_neq; u_norm; lia. }
  { (* [sb a5,0(a3)] at 0x11144 -> the newline at [r + totn - 1] *)
    rewrite Hsba; store_ok_peel; apply store_ok_zmem;
    rewrite ?word_add_nat; u_norm; lia. }
  { (* the [sp] pin *)
    getr_resolve; rewrite (HagC 2) by reg_neq_tac;
    sym_regs HRA; first [ exact H2 | sym_close ]. }
  { (* the [s0] pin *) getr_resolve; exact H8C. }
  { (* the [a3] pin *) getr_resolve; exact H13C. }
  { (* the [s4] pin *)
    getr_resolve; rewrite (HagC 20) by reg_neq_tac;
    sym_regs HRA; first [ exact H9 | sym_close ]. }
  rewrite Hsba.
  match goal with
  |- to_wall_tail _ _ (mkst _ _ ?M _) _ _ =>
     replace M with memW1
       by (unfold memW1, memJ, jout;
           rewrite wbytes_snoc, join1_tl_len_nat; reflexivity)
  end.
  eapply twt_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_112ec eq_refl) | ].
  apply twt_more; [rewrite jout_len_nat; lia|].
  apply (twl_write_rec source_segs (Z_to_bv 64 1)).
  - sym_regs HRB. vm_compute. reflexivity.
  - sym_regs HRB. sym_close.
  - rewrite (ms_read_bytes_rdn (run_segments source_segs inp rsp rmb)) by reflexivity;
      unfold run_segments; apply rdn_lift.
    cbn [ms_mem ms_regs].
    sym_regs HRB.
    rewrite jout_len_w.
    unfold memW1.
    rewrite rdn_wbytes_below
      by (rewrite ?length_N_to_le_bytes, ?jout_len_nat; u_norm; lia).
    unfold memJ.
    apply rdn_wbytes_hit.
    rewrite jout_len_nat. lia.
  - (* [vfs_write]'s [access_ok] on the whole joined buffer: the lemma
       first, so [sym_regs]' unsigned normalisation cannot hide the
       count's [bv_unsigned] from it *)
    apply Uaccess.access_okb_intro.
    cbn [ms_regs]. sym_regs HRB.
    pose proof rsp_hi_num.
    rewrite ?u_tot. unfold TASK_SIZE. lia.
  - rewrite jout_len_nat; lia.
  - (* the write-all retry loop, per delivered length *)
    intros k Hk1 Hk2.
    norm_pc.
    apply (src_put_wall (length (jout av)) (jout av) r k).
    + lia.
    + exact Hk1.
    + exact Hk2.
    + rewrite jout_len_nat; lia.
    + exact Hr0.
    + rewrite jout_len_nat; lia.
    + regupd_resolve; sym_regs HRB; sym_close.
    + regupd_resolve; sym_regs HRB; sym_close.
    + regupd_resolve; sym_regs HRB.
      match goal with |- ?x = _ => transitivity tot end;
        [ sym_close
        | unfold tot, nat_to_word, len_word; rewrite jout_len_nat; reflexivity ].
    + regupd_resolve; reflexivity.
    + regupd_resolve; sym_regs HRB; sym_close.
    + regupd_resolve; sym_regs HRB; vm_compute; reflexivity.
    + unfold memW1, memJ, mem0.
      repeat (eapply mem_grows_trans; [ | apply wbytes_grows ]).
      eapply mem_grows_trans; [ | apply zmem_grows ].
      unfold fmem.
      repeat (eapply mem_grows_trans; [ | apply wbytes_grows ]).
      apply mem_grows_refl.
    + unfold memW1. apply rdn_wbytes_hit8; u_norm; lia.
    + unfold memW1, memJ, mem0.
      repeat (rewrite rdn_wbytes_disjoint
                by (rewrite ?length_N_to_le_bytes, ?jout_len_nat; u_norm; lia)).
      rewrite rdn_zmem_out by (u_norm; lia).
      apply read_slot_ra.
    + intros a Ha.
      assert (Hab : (bv_unsigned rsp - 48 <= bv_unsigned a
                     /\ bv_unsigned a + 8 <= bv_unsigned rsp - 8)%Z).
      { repeat destruct Ha as [<-|Ha]; try (exfalso; exact Ha); u_norm; lia. }
      unfold memW1, memJ, mem0.
      repeat (rewrite rdn_wbytes_disjoint
                by (rewrite ?length_N_to_le_bytes, ?jout_len_nat; u_norm; lia)).
      rewrite rdn_zmem_out by (u_norm; lia).
      apply read_slot_0. exact Ha.
    + unfold memW1.
      rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes, ?jout_len_nat; u_norm; lia).
      unfold memJ. apply rdn_wbytes_hit. rewrite jout_len_nat. lia.
Qed.

(* ================================================================= *)
(* The outcome tree                                                   *)
(* ================================================================= *)

Hypothesis Hbrk_mod : (bv_unsigned rbrk mod page_size = 0)%Z.

Local Abbreviation RS := (run_segments source_segs inp rsp rmb).

(** The run's outcome set, over the run's segment list and initial model
    (the vDSO counter, and the vDSO pair in the brk ledger
    [State.init_reserved]).  [Hmb] is [Run.valid_mmap_base]'s floor, which
    keeps the vDSO pair far above the heap ([run_ledger_free]); [Hrd] is
    the stdout reader [Run.valid_input] pins, which the write node needs. *)
Lemma source_outcomes :
  (mmap_base_min <= bv_unsigned rmb)%Z ->
  in_channel_reader inp = true ->
  (bv_unsigned tot <= 65536)%Z ->
  to_outcomes RS
    (init_machine_state RS 0x11190 source_phdrs rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
       (init_model (segments_reserved RS) rbrk rmb rsp source_alloc_limit inp))
    (two_outcomes [] (Z_to_bv 64 4) [jout av] (Z_to_bv 64 0)).
Proof.
  intros Hmb Hrd Hcap.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof tot_ge1 as Htg1. pose proof totN_bound as Htb.
  pose proof u_tot as Hut.
  pose proof rbrk_lo_num as Hblo. pose proof rbrk_hi_num as Hbhi.
  (* the image's list is concrete, so the run's reservations split by
     computation; the vDSO pair reserves nothing *)
  assert (HresRS : segments_reserved RS = segments_reserved source_segs).
  { replace (segments_reserved RS)
      with (segments_reserved source_segs
            ++ segments_reserved (vdso_segments (in_kernel inp) rsp rmb))
      by reflexivity.
    rewrite segments_reserved_vdso, app_nil_r. reflexivity. }
  rewrite HresRS.
  (* fd 1 is the stdout channel and has a reader in the run's initial
     model ([with_vdso] keeps the descriptor table and the reader flag) *)
  assert (Hfd0 : fd1chan (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
                   (init_model (segments_reserved source_segs) rbrk rmb rsp
                      source_alloc_limit inp)))
    by exact (init_model_fd1chan (segments_reserved source_segs) rbrk rmb rsp
                source_alloc_limit inp Hrd).
  destruct (source_to_brk1 Hcap)
    as (regs3 & E1 & E2 & E8 & E10 & E18 & E19 & Hms).
  eapply tou_msteps; [exact (msteps_run source_segs inp rsp rmb _ _ Hms)|].
  apply (tou_brk_r RS _ _ (Z_to_bv 64 214)
           (T1 (init_reserved (segments_reserved source_segs) rmb rsp (in_kernel inp))
              source_alloc_limit (bv_unsigned rsp - stack_max_size) tot [jout av]));
    [reflexivity | vm_compute; reflexivity | | ].
  { (* per-resolution continuation *)
    intros r Hok.
    unfold ms_gpr in Hok |- *; cbn [ms_regs] in Hok |- *.
    rewrite arg_reg_0, E10 in Hok |- *.
    change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved source_segs) rmb rsp
                                      (in_kernel inp))
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
    assert (Hnw : (bv_unsigned r + bv_unsigned tot < 2^64)%Z)
      by (change (2^64)%Z with 18446744073709551616%Z; lia).
    assert (Hurt : bv_unsigned (r + tot)
                   = (bv_unsigned r + bv_unsigned tot)%Z)
      by (apply u_add_small; exact Hnw).
    assert (Hwant0 : r + tot <> Z_to_bv 64 0).
    { intro He. apply (f_equal bv_unsigned) in He.
      rewrite Hurt in He.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in He. lia. }
    assert (Hne2 : r <> r + tot).
    { intro He. apply (f_equal bv_unsigned) in He.
      rewrite Hurt in He. lia. }
    rewrite brk_zeros_query.
    rewrite (brk_unmaps_grow r rbrk) by lia.
    rewrite adv_brk, apply_zeros_nil. wlits.
    rewrite brk_model_query by exact Hok.
    rewrite m_vmmaps_with_vdso, m_vmmaps_init_model.
    cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_limit vm_mmap_base vm_init_sp].
    (* base is nonzero and non-wrapping: straight to the second brk *)
    destruct (source_to_brk2 regs3 r E1 E2 E8 E18 E19 Hrnz Hnw)
      as (regs5 & F1 & F2 & F8 & F9 & F10 & F18 & F19 & Hms2).
    eapply tou_msteps; [exact (msteps_run source_segs inp rsp rmb _ _ Hms2)|].
    apply (tou_brk_r RS _ _ (Z_to_bv 64 214)
             (T2 (r + tot) [jout av]));
      [reflexivity | vm_compute; reflexivity | | ].
        * (* per-resolution continuation at the second brk *)
          intros r2 Hok2.
          unfold ms_gpr in Hok2 |- *; cbn [ms_regs] in Hok2 |- *.
          rewrite arg_reg_0, F10 in Hok2 |- *.
          change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved source_segs) rmb rsp
                                            (in_kernel inp))
                              [] [] rbrk r source_alloc_limit rmb rsp)
                    (r + tot) r2) in Hok2.
          rewrite m_vmmaps_with_vmmaps. cbn [vm_brk].
          apply brk_r_ok_grow_iff in Hok2;
            [ | lia | lia | lia ].
          destruct (decide (r2 = r + tot)) as [-> | Hne].
          { (* success resolution *)
            destruct Hok2 as [_ Hgrow2].
            rewrite brk_grow_ok_aligned_grow in Hgrow2;
              [ cbn [vm_brk vm_reserved vm_maps] in Hgrow2;
                rewrite app_nil_r in Hgrow2
              | exact Hwant0
              | cbn [vm_brk]; lia
              | cbn [vm_brk]; rewrite Hurt; lia
              | cbn [vm_brk]; exact Hrmod ].
            apply andb_true_iff in Hgrow2; destruct Hgrow2 as [Hgrow2 Hbud].
            apply andb_true_iff in Hgrow2; destruct Hgrow2 as [Hle Hfree].
            apply Z.leb_le in Hle.
            set (grant := Z_to_bv 64
              (page_round_up_Z (bv_unsigned (r + tot)) - bv_unsigned r)).
            destruct (brk_aligned_grant_ok _ r tot grant _ _
                        Hurt Hurt eq_refl (alloc_top_page_lt _) Hle Hfree)
              as (HgrantU & Hgrant & Hphysceil & Hrawceil & Hrawfree & _).
            rewrite brk_zeros_aligned_grow;
              [ | exact Hwant0 | lia | rewrite Hurt; lia | exact Hrmod ].
            fold grant.
            rewrite brk_unmaps_grow by lia.
            rewrite adv_brk, apply_zeros_one. wlits.
            eapply tou_equiv;
              [ | intro o; apply (T2_succ_iff (r + tot) [jout av]) ].
            apply tou_wexit_eq.
            - apply fd1chan_brk_model. apply fd1chan_with_vmmaps. exact Hfd0.
            - apply to_wallexit_run.
              apply (source_success (regupd regs5 10 (r + tot)) r grant).
              + exact Hgrant.
              + exact Hphysceil.
              + lia.
              + exact Hrawceil.
              + (* the image's part of the run's ledger *)
                exact (region_free_init_reserved_img _ rmb rsp (in_kernel inp) r tot Hrawfree).
              + regupd_resolve. exact F1.
              + regupd_resolve. exact F2.
              + regupd_resolve. exact F8.
              + regupd_resolve. exact F9.
              + regupd_resolve. reflexivity.
              + regupd_resolve. exact F18.
              + regupd_resolve. exact F19.
            - apply jout_modeled. exact Hcap. }
          { (* failure resolution: r2 = r, exit 4 *)
            destruct Hok2 as [Hcase _].
            destruct Hcase as [Hc | Hc]; [exact (False_ind _ (Hne Hc)) |].
            subst r2.
            rewrite brk_zeros_keep.
            rewrite brk_unmaps_grow by lia.
            rewrite adv_brk, apply_zeros_nil. wlits.
            eapply tou_equiv;
              [ | intro o;
                  apply (T2_fail_iff (r + tot) [jout av] r Hne2) ].
            apply tou_wexit_eq.
            - apply fd1chan_brk_model. apply fd1chan_with_vmmaps. exact Hfd0.
            - (* ret ; bne s0,a0 taken ; exit 4 *)
              apply to_wallexit_run.
              stepjr SF_111e4 SD_111e4 (0x110e0 : word) ltac:(getr_resolve; regupd_resolve; exact F1).
              eapply tw_step;
                [ reflexivity
                | eapply step_bne_tk;
                  [ exact SF_110e0 | reflexivity | exact SD_110e0
                  | getr_resolve; regupd_resolve; rewrite F8;
                    apply c_eq_neq; rewrite Hurt; lia ]
                | norm_pc ].
              apply source_exit4. regupd_resolve. exact F2.
            - apply Forall_nil. }
        * (* set identity at the second node *)
          intro o.
          unfold ms_gpr; cbn [ms_regs].
          rewrite arg_reg_0, F10.
          change (T1 (init_reserved (segments_reserved source_segs) rmb rsp (in_kernel inp))
                     source_alloc_limit (bv_unsigned rsp - stack_max_size) tot
                     [jout av] r o <->
                  (exists r2,
                     brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved source_segs)
                                               rmb rsp (in_kernel inp))
                                 [] [] rbrk r source_alloc_limit rmb rsp)
                       (r + tot) r2
                     /\ T2 (r + tot) [jout av] r2 o)).
          apply (T1_iff_T2 (init_reserved (segments_reserved source_segs) rmb rsp (in_kernel inp))
                   source_alloc_limit rbrk rmb rsp tot [jout av] r);
            [exact Hrnz | lia | exact Hnw]. }
  { (* set identity at the first node: the query resolves to rbrk only *)
    intro o.
    unfold ms_gpr; cbn [ms_regs].
    rewrite arg_reg_0, E10.
    apply (twoU_iff_T1 (init_reserved (segments_reserved source_segs) rmb rsp (in_kernel inp))
             source_alloc_limit (bv_unsigned rsp - stack_max_size) tot (jout av) rbrk).
    - intro r0.
      change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved source_segs) rmb rsp
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
      + exact Hbrk_lo.
      + lia.
      + unfold page_size. lia.
      + unfold page_size. change source_alloc_limit with 0x400000000%Z. lia.
      + unfold page_size. lia.
    - intro Hc. apply (f_equal bv_unsigned) in Hc.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
Qed.

End Ge2Main.

End SourceProof.
