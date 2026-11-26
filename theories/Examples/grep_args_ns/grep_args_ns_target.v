(** * grep-args-ns TARGET binary (Zig ReleaseSmall).

    PROOF-SIDE FILE (not part of the trusted specification).  Symbolic
    execution of the target image from its entry point to the exit
    [ecall], concluding the two [to_wexit] derivations [Proof.v] glues
    (one per input branch: [argc >= 2] and [argc < 2]).  See [Proof.v]'s
    header for the program and the proof shape.

    The run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  As in [grep_args_ns_source.v], the derivations step over the
    image's own [target_segs], the states carry the run's rom, and the
    whole chain is carried to the run's list at the entry lemmas
    ([RunSegmentsLift.to_wallexit_run]). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec WallSim StepTac MuslStrlen StreamSim StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Common Require Import Footprint SymExec SymBranch SymSide SymTac.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import grep_args_ns_code.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import grep_args_ns_defs.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry, so the FP register file and
    [fcsr] of every state below are [fx0]'s; no instruction here touches
    them. *)
#[local] Instance grep_args_ns_target_fx : FPState := fx0.

(* ######################################################################### *)
(* TARGET binary                                                              *)
(* ######################################################################### *)

Section TargetProof.

Variable inp : ProcInput.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.

(** The argv and envp lists of the launch. *)
Local Abbreviation av := (in_argv inp).
Local Abbreviation ev := (in_envp inp).

(** The initial stack pointer, program break and mmap base are
    QUANTIFIED (ASLR): the whole section is generic over them,
    independent of the source binary's. *)
Variable asp abrk amb : word.

(** The target run's own entry draw, independent of the source's
    ([Run.ExecEntry]'s [en_draw]; see the source file). *)
Variable arnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned asp)%Z.
Hypothesis Hsp_hi : (bv_unsigned asp <= sp_window_hi)%Z.

(** The launch conjunct of the entry predicate (see the source file). *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry asp abrk amb arnd) inp.

Lemma asp_lo_num : (0x7fff80000000 <= bv_unsigned asp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma asp_hi_num : (bv_unsigned asp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x100115c%N.
Proof. vm_compute. reflexivity. Qed.

Definition aargcN : word := len_word av.
(** The initial overlay, with the entry point [init_mkst] passes to it. *)
Definition awmem : word -> option byte :=
  wrap_mem inp amb target_phdrs (0x100115c : word) asp arnd.
(** The run's rom: the image's segments, then the vDSO pair. *)
Definition arom : word -> option byte := seg_rom (run_segments target_segs inp asp amb).

Lemma u_aargcN : bv_unsigned aargcN = Z.of_nat (length av).
Proof.
  pose proof (valid_argv_len av Hva).
  unfold aargcN, len_word. apply u_Z2bv; lia.
Qed.

(** No-overflow bound for the initial stack image (feeds the stack-read
    lemmas' side conditions). *)
Lemma target_bsb_nw :
  (bv_unsigned asp
   + Z.of_nat (length (entry_stack_image inp amb target_phdrs (0x100115c : word) asp arnd))
   < 2^64)%Z.
Proof.
  pose proof (bsb_bound Sv48 inp amb target_phdrs (0x100115c : word) asp abrk arnd Hvl Hlau).
  pose proof asp_hi_num. lia.
Qed.

(** The two frames: _start's (2 slots) then run's (8 slots), all below
    the initial sp, in execution order (innermost = first store). *)
Definition afmem : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    awmem
    (Z_to_bv 64 (bv_unsigned asp - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))       (* _start: sd ra,8(sp)  *)
    (Z_to_bv 64 (bv_unsigned asp - 0x10)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* _start: sd s0,0(sp)  *)
    (Z_to_bv 64 (bv_unsigned asp - 0x18)) (word_to_le_bytes 8 (0x100117c : word)))(* run: sd ra,56(sp)    *)
    (Z_to_bv 64 (bv_unsigned asp - 0x20)) (word_to_le_bytes 8 asp))               (* run: sd s0,48(sp)    *)
    (Z_to_bv 64 (bv_unsigned asp - 0x28)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* run: sd s1,40(sp)    *)
    (Z_to_bv 64 (bv_unsigned asp - 0x30)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* run: sd s2,32(sp)    *)
    (Z_to_bv 64 (bv_unsigned asp - 0x38)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* run: sd s3,24(sp)    *)
    (Z_to_bv 64 (bv_unsigned asp - 0x40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* run: sd s4,16(sp)    *)
    (Z_to_bv 64 (bv_unsigned asp - 0x48)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* run: sd s5,8(sp)     *)
    (Z_to_bv 64 (bv_unsigned asp - 0x50)) (word_to_le_bytes 8 (Z_to_bv 64 0)).    (* run: sd s6,0(sp)     *)

(** Reads at or above the initial sp see through the frame stores. *)
Lemma rdn_afmem_above : forall (a : word) n,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn target_segs afmem a n = rdn target_segs awmem a n.
Proof.
  intros a n Ha Hn. pose proof asp_lo_num. pose proof asp_hi_num. unfold afmem.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia)).
  reflexivity.
Qed.

(** Reads over [awmem] at/above sp defer to the raw stack bytes. *)
Lemma rdn_awmem_stack : forall (a : word) n,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn target_segs awmem a n
  = rdn target_segs
      (stack_to_mem asp (entry_stack_image inp amb target_phdrs (0x100115c : word) asp arnd)) a n.
Proof. intros a n Ha Hn. apply rdn_wrap_stack_above; assumption. Qed.

Lemma aread_argc :
  rdn target_segs afmem asp 8%nat = Some (word_le8 aargcN).
Proof.
  pose proof asp_hi_num.
  rewrite rdn_afmem_above by lia. rewrite rdn_awmem_stack by lia.
  apply read_argc. exact target_bsb_nw.
Qed.

Lemma aread_ptr : forall k, (k < length av)%nat ->
  rdn target_segs afmem (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * Z.of_nat k)) 8%nat
  = Some (word_le8 (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k)).
Proof.
  intros k Hk.
  pose proof asp_hi_num. pose proof asp_lo_num.
  pose proof (valid_argv_len av Hva) as Hlen.
  assert (HkZ : (Z.of_nat k <= 1024)%Z) by lia.
  replace (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * Z.of_nat k))
    with (asp + nat_to_word (8 + 8 * k)) by (rewrite word_add_nat; f_equal; lia).
  rewrite rdn_afmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_awmem_stack by (rewrite word_add_nat; u_norm; lia).
  apply read_argv_ptr_k; [assumption | exact target_bsb_nw].
Qed.

Lemma target_ptr_bounds : forall k, (k < length av)%nat ->
  (bv_unsigned asp <= bv_unsigned (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k))%Z /\
  (bv_unsigned (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k)
   + Z.of_nat (length (nth k av [])) + 1 < 2^64)%Z.
Proof. intros k Hk. exact (argv_ptr_bounds Sv48 inp amb asp abrk arnd k Hlau Hk). Qed.

Lemma aread_str_byte : forall k j, (k < length av)%nat ->
  (j <= length (nth k av []))%nat ->
  rdn target_segs afmem (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k + nat_to_word j) 1%nat
  = Some [byte_at (nth k av []) j].
Proof.
  intros k j Hk Hj.
  destruct (target_ptr_bounds k Hk) as [Hge Hup].
  pose proof (valid_argv_str_len av k Hva Hk) as Hslen.
  pose proof (u64_range asp). pose proof (u64_range (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k)).
  rewrite rdn_afmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_awmem_stack by (rewrite word_add_nat; u_norm; lia).
  eapply read_argv_byte_k; eassumption.
Qed.

Lemma aread_str : forall k, (k < length av)%nat ->
  rdn target_segs afmem (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k) (length (nth k av []))
  = Some (nth k av []).
Proof.
  intros k Hk.
  destruct (target_ptr_bounds k Hk) as [Hge Hup].
  rewrite rdn_afmem_above by lia.
  rewrite rdn_awmem_stack by lia.
  eapply read_argv_str_k; eassumption.
Qed.

(** The '\n' byte in the target image at 0x1000158. *)
Lemma aseg_rom_newline : seg_rom target_segs 0x1000158 = Some (Z_to_bv 8 10).
Proof. vm_refl. Qed.

Lemma aread_newline : rdn target_segs afmem 0x1000158 1%nat = Some [Z_to_bv 8 10].
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. unfold afmem.
  repeat (rewrite rdn_wbytes_below
            by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia)).
  cbn [rdn].
  unfold awmem.
  rewrite (wrap_mem_below Sv48 inp amb target_phdrs (0x100115c : word) asp abrk arnd 0x1000158 Hlau)
    by (rewrite stack_max_size_val; imm_norm; lia).
  rewrite aseg_rom_newline. reflexivity.
Qed.

(** Frame-slot read-back. *)
Lemma aread_slot_ra :
  rdn target_segs afmem (Z_to_bv 64 (bv_unsigned asp - 0x18)) 8%nat
  = Some (word_to_le_bytes 8 (0x100117c : word)).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. unfold afmem.
  repeat first
    [ rewrite rdn_wbytes_hit8 by (u_norm; lia)
    | rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; u_norm; lia) ].
  reflexivity.
Qed.

Lemma aread_slot_s0 :
  rdn target_segs afmem (Z_to_bv 64 (bv_unsigned asp - 0x20)) 8%nat
  = Some (word_to_le_bytes 8 asp).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. unfold afmem.
  repeat first
    [ rewrite rdn_wbytes_hit8 by (u_norm; lia)
    | rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; u_norm; lia) ].
  reflexivity.
Qed.

Lemma aread_slot_0 : forall a : word,
  In a [Z_to_bv 64 (bv_unsigned asp - 0x50); Z_to_bv 64 (bv_unsigned asp - 0x48);
        Z_to_bv 64 (bv_unsigned asp - 0x40); Z_to_bv 64 (bv_unsigned asp - 0x38);
        Z_to_bv 64 (bv_unsigned asp - 0x30); Z_to_bv 64 (bv_unsigned asp - 0x28)] ->
  rdn target_segs afmem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros a Ha. pose proof asp_lo_num. pose proof asp_hi_num. unfold afmem.
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

Lemma aread_slot_d8 : rdn target_segs afmem (Z_to_bv 64 (bv_unsigned asp - 0x28)) 8%nat
  = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. apply aread_slot_0. right; right; right; right; right; left; reflexivity. Qed.
Lemma aread_slot_d0 : rdn target_segs afmem (Z_to_bv 64 (bv_unsigned asp - 0x30)) 8%nat
  = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. apply aread_slot_0. right; right; right; right; left; reflexivity. Qed.
Lemma aread_slot_c8 : rdn target_segs afmem (Z_to_bv 64 (bv_unsigned asp - 0x38)) 8%nat
  = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. apply aread_slot_0. right; right; right; left; reflexivity. Qed.
Lemma aread_slot_c0 : rdn target_segs afmem (Z_to_bv 64 (bv_unsigned asp - 0x40)) 8%nat
  = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. apply aread_slot_0. right; right; left; reflexivity. Qed.
Lemma aread_slot_b8 : rdn target_segs afmem (Z_to_bv 64 (bv_unsigned asp - 0x48)) 8%nat
  = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. apply aread_slot_0. right; left; reflexivity. Qed.
Lemma aread_slot_b0 : rdn target_segs afmem (Z_to_bv 64 (bv_unsigned asp - 0x50)) 8%nat
  = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. apply aread_slot_0. left; reflexivity. Qed.


(* ================================================================= *)
(* Target epilogue: 0x1001280 (a0 := s4; reload; ret; exit)            *)
(* ================================================================= *)

(** Every frame-slot read the epilogue's eight [ld]s fall through to is
    one of the [aread_slot_*] facts above; one dispatcher closes the
    whole [SCReadBase] batch.  The [lazymatch] is load-bearing: letting
    [exact] try the wrong slot lemma makes unification unfold [rdn] over
    the segment image. *)
Ltac t_slot_rd :=
  eexists; split;
  [ lazymatch goal with
    | |- rdn _ _ (Z_to_bv 64 (_ - 24)) _ = _ => exact aread_slot_ra
    | |- rdn _ _ (Z_to_bv 64 (_ - 32)) _ = _ => exact aread_slot_s0
    | |- _ =>
        apply aread_slot_0; cbn [In];
        first [ left; reflexivity | right; left; reflexivity
              | do 2 right; left; reflexivity | do 3 right; left; reflexivity
              | do 4 right; left; reflexivity | do 5 right; left; reflexivity ]
    end
  | first [ vm_closed | apply bytes_le_to_Z_8 ] ].

Lemma target_epilogue : forall regs code,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 0x50) ->
  reg_get regs 20 = code -> (bv_unsigned code < 256)%Z ->
  wexit1 target_segs (mkst regs 0x1001280 afmem arom) [] code.
Proof.
  intros regs code H2 H20 Hc.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  (* 0x1001280 .. 0x10012a8: a0 := s4, reload the eight callee-saved
     slots, pop the frame and [ret].  Naming the reloaded [ra] in the
     read script resolves the [ret], so the block runs on through the
     Zig entry stub's exit tail at 0x100117c and stops at the [ecall]. *)
  sym_block target_segs 15%nat (@nil bool)
    [ELit 0x100117c; EVar 33; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0]
    [((2 : reg), EVar 32)]
    [Z_to_bv 64 (bv_unsigned asp - 0x50)] [asp] RE HRE.
  1-8: t_slot_rd.
  { exact H2. }
  (* 0x1001180: ecall -- exit(code) *)
  chain_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ TF_1001180 eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRE. vm_closed.
  - sym_regs HRE. exact H20.
  - exact Hc.
Qed.


(* ================================================================= *)
(* slen: 0x10012e4..0x10012fc                                        *)
(* ================================================================= *)

Lemma aslen_loop : forall k, (k < length av)%nat ->
  forall d j regs,
  (j + d = length (nth k av []))%nat ->
  reg_get regs 10 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k ->
  reg_get regs 11 = nat_to_word j ->
  exists regs',
    (forall r : reg, r <> 11 -> r <> 12 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 11 = nat_to_word (S (length (nth k av []))) /\
    msteps target_segs (mkst regs 0x10012e8 afmem arom)
                      (mkst regs' 0x10012f8 afmem arom).
Proof.
  intros k Hk.
  pose proof (target_ptr_bounds k Hk) as [Hge Hlt].
  pose proof (valid_argv_str_len av k Hva Hk) as Hslen.
  pose proof (valid_argv_str_nz av k Hva Hk) as Hsnz.
  set (ptr := cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k) in *.
  set (s := nth k av []) in *.
  induction d as [|d IH]; intros j regs Hjd Hr10 Hr11.
  - (* base: j = length s, byte is the NUL sentinel *)
    assert (Hj : j = length s) by lia.
    set (regs1 := regupd regs 12 (ptr + nat_to_word j)).
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x10012e8 afmem arom)
                 = MachineOk (mkst regs1 0x10012ec afmem arom)).
    { rewrite (step_add target_segs regs 0x10012e8 afmem arom _ 12 10 11
                 TF_10012e8 eq_refl TD_10012e8).
      reduce_bv_eqb_ifs.
      getr_resolve. rewrite Hr10, Hr11. wlits. reflexivity. }
    set (regs2 := regupd regs1 12 (Z_to_bv 64 0)).
    assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x10012ec afmem arom)
                 = MachineOk (mkst regs2 0x10012f0 afmem arom)).
    { rewrite (step_lbu target_segs regs1 0x10012ec afmem arom _ 12 12 _ (Z_to_bv 8 0)
                 TF_10012ec eq_refl TD_10012ec).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve.
        rewrite v_addi_0.
        assert (Hjle : (j <= length (nth k av []))%nat) by (unfold s in Hjd; lia).
        pose proof (aread_str_byte k j Hk Hjle) as Hrd.
        assert (Hb0 : byte_at (nth k av []) j = Z_to_bv 8 0).
        { unfold s in Hj. rewrite Hj. apply byte_at_len. }
        rewrite Hb0 in Hrd. exact Hrd. }
    set (regs3 := regupd regs2 11 (nat_to_word (S j))).
    assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x10012f0 afmem arom)
                 = MachineOk (mkst regs3 0x10012f4 afmem arom)).
    { rewrite (step_addi target_segs regs2 0x10012f0 afmem arom _ 11 11 _
                 TF_10012f0 eq_refl TD_10012f0).
      reduce_bv_eqb_ifs.
      unfold regs3, regs2, regs1. getr_resolve. rewrite Hr11.
      rewrite v_addi_Sj by lia. wlits. reflexivity. }
    assert (E4 : RiscvSemantics.step target_segs (mkst regs3 0x10012f4 afmem arom)
                 = MachineOk (mkst regs3 0x10012f8 afmem arom)).
    { rewrite (step_bne_ft target_segs regs3 0x10012f4 afmem arom _ 12 0 _
                 TF_10012f4 eq_refl TD_10012f4).
      - wlits. reflexivity.
      - unfold regs3, regs2. getr_resolve. exact c_eq_0_true. }
    exists regs3. split; [|split].
    + intros r H11 H12. unfold regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs3. rewrite regupd_same. rewrite Hj. reflexivity.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      apply mst_refl.
  - (* step: j < length s, in-string byte is nonzero *)
    assert (Hjlt : (j < length s)%nat) by lia.
    set (b := byte_at s j).
    assert (Hbnz : b <> Z_to_bv 8 0) by (apply byte_at_nz; [exact Hsnz | exact Hjlt]).
    set (regs1 := regupd regs 12 (ptr + nat_to_word j)).
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x10012e8 afmem arom)
                 = MachineOk (mkst regs1 0x10012ec afmem arom)).
    { rewrite (step_add target_segs regs 0x10012e8 afmem arom _ 12 10 11
                 TF_10012e8 eq_refl TD_10012e8).
      reduce_bv_eqb_ifs.
      getr_resolve. rewrite Hr10, Hr11. wlits. reflexivity. }
    set (regs2 := regupd regs1 12 (Z_to_bv 64 (bv_unsigned b))).
    assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x10012ec afmem arom)
                 = MachineOk (mkst regs2 0x10012f0 afmem arom)).
    { rewrite (step_lbu target_segs regs1 0x10012ec afmem arom _ 12 12 _ b
                 TF_10012ec eq_refl TD_10012ec).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve.
        rewrite v_addi_0.
        unfold b, ptr, s. apply aread_str_byte;
          [exact Hk | unfold s in Hjlt; lia]. }
    set (regs3 := regupd regs2 11 (nat_to_word (S j))).
    assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x10012f0 afmem arom)
                 = MachineOk (mkst regs3 0x10012f4 afmem arom)).
    { rewrite (step_addi target_segs regs2 0x10012f0 afmem arom _ 11 11 _
                 TF_10012f0 eq_refl TD_10012f0).
      reduce_bv_eqb_ifs.
      unfold regs3, regs2, regs1. getr_resolve. rewrite Hr11.
      rewrite v_addi_Sj by lia. wlits. reflexivity. }
    assert (E4 : RiscvSemantics.step target_segs (mkst regs3 0x10012f4 afmem arom)
                 = MachineOk (mkst regs3 0x10012e8 afmem arom)).
    { rewrite (step_bne_tk target_segs regs3 0x10012f4 afmem arom _ 12 0 _
                 TF_10012f4 eq_refl TD_10012f4).
      - wlits. reflexivity.
      - unfold regs3, regs2. getr_resolve.
        apply c_eq_0_false. rewrite u_zext8. apply byte_nz_u. exact Hbnz. }
    assert (Hr10' : reg_get regs3 10 = ptr).
    { unfold regs3, regs2, regs1. regupd_resolve. exact Hr10. }
    assert (Hr11' : reg_get regs3 11 = nat_to_word (S j)) by apply regupd_same.
    destruct (IH (S j) regs3 ltac:(lia) Hr10' Hr11') as [regs' [Hag [H11 Hms]]].
    exists regs'. split; [|split].
    + intros r H11' H12'. rewrite (Hag r H11' H12').
      unfold regs3, regs2, regs1. rewrite !regupd_other by assumption.
      reflexivity.
    + exact H11.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      exact Hms.
Qed.

Lemma aslen : forall k RA regs, (k < length av)%nat ->
  reg_get regs 10 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k ->
  reg_get regs 1 = RA ->
  v_jalr RA 0 = RA ->
  exists regs',
    (forall r : reg, r <> 10 -> r <> 11 -> r <> 12 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 10 = nat_to_word (length (nth k av [])) /\
    msteps target_segs (mkst regs 0x10012e4 afmem arom)
                      (mkst regs' RA afmem arom).
Proof.
  intros k RA regs Hk Hr10 Hr1 Hvj.
  pose proof (valid_argv_str_len av k Hva Hk) as Hslen.
  set (regs1 := regupd regs 11 (nat_to_word 0)).
  assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x10012e4 afmem arom)
               = MachineOk (mkst regs1 0x10012e8 afmem arom)).
  { rewrite (step_addi target_segs regs 0x10012e4 afmem arom _ 11 0 _
               TF_10012e4 eq_refl TD_10012e4).
    reduce_bv_eqb_ifs. getr_resolve.
    replace (v_addi (Z_to_bv 64 0) (bv_signed (0%bv : bv 12)))
      with (nat_to_word 0) by bveq.
    wlits. reflexivity. }
  assert (Hr10_1 : reg_get regs1 10 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k)
    by (unfold regs1; rewrite regupd_other by reg_neq_tac; exact Hr10).
  assert (Hr11_1 : reg_get regs1 11 = nat_to_word 0) by apply regupd_same.
  destruct (aslen_loop k Hk (length (nth k av [])) 0 regs1
              ltac:(lia) Hr10_1 Hr11_1) as [regsL [HagL [H11L HmsL]]].
  set (regsR := regupd regsL 10 (nat_to_word (length (nth k av [])))).
  assert (E2 : RiscvSemantics.step target_segs (mkst regsL 0x10012f8 afmem arom)
               = MachineOk (mkst regsR 0x10012fc afmem arom)).
  { rewrite (step_addi target_segs regsL 0x10012f8 afmem arom _ 10 11 _
               TF_10012f8 eq_refl TD_10012f8).
    reduce_bv_eqb_ifs.
    getr_resolve. rewrite H11L.
    replace (nat_to_word (S (length (nth k av []))))
      with (nat_to_word (length (nth k av [])) + 1)
      by (rewrite <- (v_addi_Sj (length (nth k av []))) by lia; reflexivity).
    imm_norm. rewrite v_addi_pred. wlits. reflexivity. }
  assert (E3 : RiscvSemantics.step target_segs (mkst regsR 0x10012fc afmem arom)
               = MachineOk (mkst regsR RA afmem arom)).
  { rewrite (step_jalr_x0 target_segs regsR 0x10012fc afmem arom _ 1 _ RA
               TF_10012fc eq_refl TD_10012fc).
    - imm_norm. rewrite Hvj. reflexivity.
    - unfold regsR. getr_resolve.
      rewrite (HagL 1) by reg_neq_tac.
      unfold regs1. rewrite regupd_other by reg_neq_tac. exact Hr1. }
  exists regsR. split; [|split].
  - intros r H10 H11 H12. unfold regsR.
    rewrite regupd_other by assumption.
    rewrite (HagL r H11 H12).
    unfold regs1. rewrite regupd_other by assumption. reflexivity.
  - apply regupd_same.
  - eapply mst_step; [reflexivity | exact E1 |].
    eapply msteps_trans; [exact HmsL |].
    eapply mst_step; [reflexivity | exact E2 |].
    eapply mst_step; [reflexivity | exact E3 |].
    apply mst_refl.
Qed.


(* ================================================================= *)
(* put: 0x10012ac..0x10012e0                                          *)
(* ================================================================= *)

(** The put-style write-all retry loop at 0x10012c4: register-only, so
    memory and every register outside a0/a1/a2 carry through unchanged.
    [blez a0]'s error arm is dead: every delivery is nonempty. *)
Lemma tput_wall : forall (K : machine_state -> Prop) fuel
    (rest : list byte) (p RA : word) n regs mem,
  (length rest <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length rest)%nat ->
  (Z.of_nat (length rest) < 2^63)%Z ->
  (* the range [vfs_write]'s [access_ok] accepts ([WallSim.to_wall]'s write node) *)
  (bv_unsigned p + Z.of_nat (length rest) <= TASK_SIZE)%Z ->
  reg_get regs 1 = RA -> v_jalr RA 0 = RA ->
  reg_get regs 10 = len_word (firstn n rest) ->
  reg_get regs 11 = p ->
  reg_get regs 12 = len_word rest ->
  bv_unsigned (reg_get regs 17) = 64%Z ->
  reg_get regs 17 = Z_to_bv 64 64 ->
  rdn target_segs mem p (length rest) = Some rest ->
  (forall regs',
     (forall r : reg, r <> 10 -> r <> 11 -> r <> 12 -> r <> 17 ->
        reg_get regs' r = reg_get regs r) ->
     reg_get regs' 10 = Z_to_bv 64 0 ->
     K (mkst regs' RA mem arom)) ->
  to_wall_tail target_segs (Z_to_bv 64 1)
    (mkst regs (0x10012c4 : word) mem arom) (skipn n rest) K.
Proof.
  intros K fuel. induction fuel as [|fuel IH];
    intros rest p RA n regs mem Hfuel Hn1 Hn2 Hlen Htask
           H1 Hvj H10 H11 H12 H17 H17w Hread Hcont.
  { lia. }
  (* 0x10012c4: blez a0 falls through *)
  chain_step;
    [ reflexivity
    | eapply step_bge_ft;
      [ exact TF_10012c4 | reflexivity | exact TD_10012c4
      | getr_resolve; rewrite H10; apply c_lts_0_pos;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x10012c8: add a1,a1,a0 *)
  stepiv TF_10012c8 TD_10012c8 (p + nat_to_word n)
    ltac:(getr_resolve; rewrite H11, H10; apply v_add_len_firstn; lia).
  (* 0x10012cc: sub a2,a2,a0 *)
  stepiv TF_10012cc TD_10012cc (len_word (skipn n rest))
    ltac:(getr_resolve; rewrite H12, H10; apply v_sub_len_firstn; lia).
  destruct (Nat.eq_dec n (length rest)) as [-> | Hne].
  - rewrite skipn_all.
    chain_step;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact TF_10012d0 | reflexivity | exact TD_10012d0
        | getr_resolve; apply c_eq_0_of_u; reflexivity ]
      | norm_pc ].
    stepiv TF_10012d4 TD_10012d4 (Z_to_bv 64 0) ltac:(getr_resolve; bveq).
    chain_step;
      [ reflexivity
      | eapply step_jalr_x0 with (tgt := RA);
        [ exact TF_10012d8 | reflexivity | exact TD_10012d8
        | getr_resolve; regupd_resolve; exact H1 ]
      | idtac ].
    imm_norm. rewrite Hvj.
    apply twt_done. apply Hcont.
    + intros r Hx10 Hx11 Hx12 Hx17.
      repeat (rewrite regupd_other by assumption). reflexivity.
    + regupd_resolve. reflexivity.
  - chain_step;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact TF_10012d0 | reflexivity | exact TD_10012d0
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* 0x10012bc: li a0,1 *)
    stepiv TF_10012bc TD_10012bc (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* 0x10012c0: ecall *)
    eapply twt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_10012c0 eq_refl) |].
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
      (* the state's rom is the run's; the buffer read is the image's *)
      rewrite (ms_read_bytes_rdn (run_segments target_segs inp asp amb)) by reflexivity.
      unfold run_segments. apply rdn_lift.
      cbn [ms_mem].
      replace (word_to_nat (len_word (skipn n rest)))
        with (length (skipn n rest))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      pose proof (SeqExec.rdn_skipn target_segs mem (length rest) p rest n
                    Hread Hn2) as Hsk.
      rewrite length_skipn. exact Hsk.
    + match goal with
      | |- access_okb (reg_get ?R 11) (bv_unsigned (reg_get ?R 12)) = true =>
          replace (reg_get R 11) with (p + nat_to_word n)
            by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word (skipn n rest))
            by (regupd_resolve; reflexivity)
      end.
      apply Uaccess.access_okb_intro.
      pose proof (u64_range p).
      rewrite word_add_nat, u_Z2bv by (unfold TASK_SIZE in Htask; lia).
      rewrite u_len_word by (rewrite length_skipn; lia).
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
        rewrite word_add_nat, u_Z2bv by (unfold TASK_SIZE in Htask; lia).
        rewrite length_skipn. lia.
      * regupd_resolve; exact H1.
      * exact Hvj.
      * regupd_resolve; reflexivity.
      * regupd_resolve; reflexivity.
      * regupd_resolve; reflexivity.
      * regupd_resolve; exact H17.
      * regupd_resolve; exact H17w.
      * pose proof (SeqExec.rdn_skipn target_segs mem (length rest) p rest n
                      Hread Hn2) as Hsk.
        rewrite length_skipn. exact Hsk.
      * intros regs'' Hag H0.
        apply Hcont; [ | exact H0 ].
        intros r Hx10 Hx11 Hx12 Hx17.
        rewrite (Hag r Hx10 Hx11 Hx12 Hx17).
        repeat (rewrite regupd_other by assumption). reflexivity.
Qed.

(** put(buf, len) with len >= 1: one write syscall, returns 0 to ra. *)
Lemma tput_pos : forall regs mem buf B L RA bufs code,
  reg_get regs 10 = B -> reg_get regs 11 = L ->
  (1 <= bv_unsigned L)%Z -> (bv_unsigned L < 2^63)%Z ->
  (* the range [vfs_write]'s [access_ok] accepts *)
  (bv_unsigned B + bv_unsigned L <= TASK_SIZE)%Z ->
  reg_get regs 1 = RA -> v_jalr RA 0 = RA ->
  rdn target_segs mem B (word_to_nat L) = Some buf ->
  (forall regs',
     (forall r : reg, r <> 10 -> r <> 11 -> r <> 12 -> r <> 17 -> reg_get regs' r = reg_get regs r) ->
     reg_get regs' 10 = Z_to_bv 64 0 ->
     wexit1 target_segs (mkst regs' RA mem arom) bufs code) ->
  wexit1 target_segs (mkst regs 0x10012ac mem arom) (buf :: bufs) code.
Proof.
  intros regs mem buf B L RA bufs code H10 H11 HL1 HL63 Htask H1 Hvj Hread Hcont.
  pose proof (rdn_length _ _ _ _ _ Hread) as Hbl.
  pose proof (u64_range L) as HuL.
  assert (HbufL : Z.of_nat (length buf) = bv_unsigned L)
    by (rewrite Hbl; unfold word_to_nat; rewrite Z2Nat.id by lia; reflexivity).
  assert (Hlw : len_word buf = L)
    by (unfold len_word; rewrite HbufL; apply bv_eq;
        rewrite u_Z2bv by lia; reflexivity).
  split; [lia|].
  (* a2 := a1 (= L) *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := L);
      [ exact TF_10012ac | reflexivity | exact TD_10012ac | reflexivity
      | getr_resolve; rewrite H11; apply v_addi_0 ]
    | norm_pc ].
  (* a1 := a0 (= B) *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := B);
      [ exact TF_10012b0 | reflexivity | exact TD_10012b0 | reflexivity
      | getr_resolve; regupd_resolve; rewrite H10; apply v_addi_0 ]
    | norm_pc ].
  (* a7 := 64 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 64);
      [ exact TF_10012b4 | reflexivity | exact TD_10012b4 | reflexivity
      | getr_resolve; exact v_addi_0_64 ]
    | norm_pc ].
  (* beqz a2 falls through (L >= 1) *)
  chain_step;
    [ reflexivity
    | eapply step_beq_ft;
      [ exact TF_10012b8 | reflexivity | exact TD_10012b8
      | getr_resolve; regupd_resolve;
        apply c_eq_0_false; lia ]
    | norm_pc ].
  (* a0 := 1; ecall *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 1);
      [ exact TF_10012bc | reflexivity | exact TD_10012bc | reflexivity
      | getr_resolve; exact v_addi_0_1 ]
    | norm_pc ].
  chain_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ TF_10012c0 eq_refl) | ].
  apply twt_more; [lia|].
  apply (twl_write_rec target_segs (Z_to_bv 64 1)).
  - getr_resolve. vm_compute. reflexivity.
  - regupd_resolve. reflexivity.
  - (* the state's rom is the run's; the buffer read is the image's *)
    rewrite (ms_read_bytes_rdn (run_segments target_segs inp asp amb)) by reflexivity.
    unfold run_segments. apply rdn_lift.
    cbn [ms_mem ms_regs]. regupd_resolve. exact Hread.
  - regupd_resolve. apply Uaccess.access_okb_intro. exact Htask.
  - lia.
  - (* the put-style retry loop, per delivered length *)
    intros n Hn1 Hn2.
    norm_pc.
    eapply (tput_wall _ (length buf) buf B RA n).
    + lia.
    + exact Hn1.
    + exact Hn2.
    + lia.
    + rewrite HbufL. exact Htask.
    + regupd_resolve; exact H1.
    + exact Hvj.
    + regupd_resolve; reflexivity.
    + regupd_resolve; reflexivity.
    + regupd_resolve; symmetry; exact Hlw.
    + regupd_resolve; vm_compute; reflexivity.
    + regupd_resolve; bveq.
    + rewrite Hbl. exact Hread.
    + intros regs' Hag H0.
      apply Hcont; [ | exact H0 ].
      intros r Hx10 Hx11 Hx12 Hx17.
      rewrite (Hag r Hx10 Hx11 Hx12 Hx17).
      repeat (rewrite regupd_other by assumption). reflexivity.
Qed.


(** put(buf, 0): no syscall, returns 0 to ra. *)
Lemma tput_zero : forall regs mem RA bufs code,
  reg_get regs 11 = Z_to_bv 64 0 ->
  reg_get regs 1 = RA -> v_jalr RA 0 = RA ->
  (forall regs',
     (forall r : reg, r <> 10 -> r <> 11 -> r <> 12 -> r <> 17 -> reg_get regs' r = reg_get regs r) ->
     reg_get regs' 10 = Z_to_bv 64 0 ->
     wexit1 target_segs (mkst regs' RA mem arom) bufs code) ->
  wexit1 target_segs (mkst regs 0x10012ac mem arom) bufs code.
Proof.
  intros regs mem RA bufs code H11 H1 Hvj Hcont.
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact TF_10012ac | reflexivity | exact TD_10012ac | reflexivity
      | getr_resolve; rewrite H11; apply v_addi_0 ]
    | norm_pc ].
  stepi TF_10012b0 TD_10012b0.
  stepi TF_10012b4 TD_10012b4.
  (* beqz a2 taken (a2 = 0) -> 0x10012d4 *)
  chain_step;
    [ reflexivity
    | eapply step_beq_tk;
      [ exact TF_10012b8 | reflexivity | exact TD_10012b8
      | getr_resolve; regupd_resolve;
        exact c_eq_0_true ]
    | norm_pc ].
  (* a0 := 0; ret *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact TF_10012d4 | reflexivity | exact TD_10012d4 | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | norm_pc ].
  chain_step;
    [ reflexivity
    | eapply step_jalr_x0 with (tgt := RA);
      [ exact TF_10012d8 | reflexivity | exact TD_10012d8
      | getr_resolve; regupd_resolve; exact H1 ]
    | ].
  imm_norm. rewrite Hvj.
  apply Hcont.
  - intros r Hx10 Hx11 Hx12 Hx17.
    repeat (rewrite regupd_other by assumption). reflexivity.
  - regupd_resolve. reflexivity.
Qed.


(* ================================================================= *)
(* Target inner compare loop vs [prefix_eqb]                           *)
(* ================================================================= *)

(** Pointer increment: [addi p,p,1] advances a pointer-plus-index by
    one index step (hypothesis-free: both sides are the same wrap). *)
Lemma v_addi_ptr_S : forall (p : word) (j : nat),
  v_addi (p + nat_to_word j) 1 = p + nat_to_word (S j).
Proof.
  intros p j.
  change (v_addi (p + nat_to_word j) 1)
    with (p + nat_to_word j + nat_to_word 1).
  rewrite nat_to_word_add_merge. do 2 f_equal. lia.
Qed.

(** From 0x1001220 with a3 = nn - j (count down), a4 = &hay[i+j],
    a5 = &pat[j]: exits to 0x1001248 when the remaining pattern matches,
    to 0x100123c at the first mismatch.  Clobbers a3-a5, a6, a7. *)
Lemma acmp : forall k, (k < length av)%nat -> (2 <= length av)%nat ->
  forall i d j regs,
  (j + d = length (nth 1 av []))%nat ->
  (i + length (nth 1 av []) <= length (nth k av []))%nat ->
  reg_get regs 13 = nat_to_word d ->
  reg_get regs 14 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k + nat_to_word (i + j) ->
  reg_get regs 15 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1 + nat_to_word j ->
  exists regs',
    (forall r : reg, r <> 13 -> r <> 14 -> r <> 15 -> r <> 16 -> r <> 17 ->
       reg_get regs' r = reg_get regs r) /\
    msteps target_segs (mkst regs 0x1001220 afmem arom)
      (mkst regs'
        (if prefix_eqb (skipn j (nth 1 av [])) (nth k av []) (i + j)
         then 0x1001248 else 0x100123c)
        afmem arom).
Proof.
  intros k Hk H2le.
  pose proof (target_ptr_bounds k Hk) as [Hgeh Hlth].
  pose proof (target_ptr_bounds 1 ltac:(lia)) as [Hgep Hltp].
  pose proof (valid_argv_str_len av k Hva Hk) as Hhlen.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as Hplen.
  intros i d. revert i.
  induction d as [|d IH]; intros i j regs Hjd Hin Hr13 Hr14 Hr15.
  - (* count exhausted: whole pattern matched *)
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001220 afmem arom)
                 = MachineOk (mkst regs 0x1001248 afmem arom)).
    { rewrite (step_beq_tk target_segs regs 0x1001220 afmem arom _ 13 0 _
                 TF_1001220 eq_refl TD_1001220).
      - wlits. reflexivity.
      - getr_resolve. rewrite Hr13. exact c_eq_0_true. }
    exists regs. split.
    + intros; reflexivity.
    + replace (skipn j (nth 1 av [])) with (@nil byte)
        by (symmetry; apply skipn_all2; lia).
      cbn [prefix_eqb].
      eapply mst_step; [reflexivity | exact E1 |].
      apply mst_refl.
  - (* compare byte j *)
    assert (Hjlt : (j < length (nth 1 av []))%nat) by lia.
    assert (HijN : (i + j < length (nth k av []))%nat) by lia.
    set (bh := byte_at (nth k av []) (i + j)).
    set (bp := byte_at (nth 1 av []) j).
    (* beqz a3 falls through (a3 = S d <> 0) *)
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001220 afmem arom)
                 = MachineOk (mkst regs 0x1001224 afmem arom)).
    { rewrite (step_beq_ft target_segs regs 0x1001220 afmem arom _ 13 0 _
                 TF_1001220 eq_refl TD_1001220).
      - wlits. reflexivity.
      - getr_resolve. rewrite Hr13. apply c_eq_0_false.
        rewrite u_ntw by lia. lia. }
    (* a6 := hay[i+j]; a7 := pat[j] *)
    set (regs1 := regupd regs 16 (Z_to_bv 64 (bv_unsigned bh))).
    assert (E2 : RiscvSemantics.step target_segs (mkst regs 0x1001224 afmem arom)
                 = MachineOk (mkst regs1 0x1001228 afmem arom)).
    { rewrite (step_lbu target_segs regs 0x1001224 afmem arom _ 16 14 _ bh
                 TF_1001224 eq_refl TD_1001224).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - getr_resolve. rewrite Hr14.
        rewrite v_addi_0.
        unfold bh. apply aread_str_byte; [exact Hk | lia]. }
    set (regs2 := regupd regs1 17 (Z_to_bv 64 (bv_unsigned bp))).
    assert (E3 : RiscvSemantics.step target_segs (mkst regs1 0x1001228 afmem arom)
                 = MachineOk (mkst regs2 0x100122c afmem arom)).
    { rewrite (step_lbu target_segs regs1 0x1001228 afmem arom _ 17 15 _ bp
                 TF_1001228 eq_refl TD_1001228).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite Hr15.
        rewrite v_addi_0.
        unfold bp. apply aread_str_byte; [lia | lia]. }
    (* a5 += 1; a4 += 1; a3 -= 1 *)
    set (regs3 := regupd regs2 15 (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1 + nat_to_word (S j))).
    assert (E4 : RiscvSemantics.step target_segs (mkst regs2 0x100122c afmem arom)
                 = MachineOk (mkst regs3 0x1001230 afmem arom)).
    { rewrite (step_addi target_segs regs2 0x100122c afmem arom _ 15 15 _
                 TF_100122c eq_refl TD_100122c).
      reduce_bv_eqb_ifs.
      unfold regs3, regs2, regs1. getr_resolve. rewrite Hr15.
      imm_norm. rewrite v_addi_ptr_S. wlits. reflexivity. }
    set (regs4 := regupd regs3 14 (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k + nat_to_word (i + S j))).
    assert (E5 : RiscvSemantics.step target_segs (mkst regs3 0x1001230 afmem arom)
                 = MachineOk (mkst regs4 0x1001234 afmem arom)).
    { rewrite (step_addi target_segs regs3 0x1001230 afmem arom _ 14 14 _
                 TF_1001230 eq_refl TD_1001230).
      reduce_bv_eqb_ifs.
      unfold regs4, regs3, regs2, regs1. getr_resolve. rewrite Hr14.
      imm_norm. rewrite v_addi_ptr_S.
      replace (S (i + j)) with (i + S j)%nat by lia.
      wlits. reflexivity. }
    set (regs5 := regupd regs4 13 (nat_to_word d)).
    assert (E6 : RiscvSemantics.step target_segs (mkst regs4 0x1001234 afmem arom)
                 = MachineOk (mkst regs5 0x1001238 afmem arom)).
    { rewrite (step_addi target_segs regs4 0x1001234 afmem arom _ 13 13 _
                 TF_1001234 eq_refl TD_1001234).
      reduce_bv_eqb_ifs.
      unfold regs5, regs4, regs3, regs2, regs1. getr_resolve. rewrite Hr13.
      replace (nat_to_word (S d)) with (nat_to_word d + 1)
        by (rewrite <- (v_addi_Sj d) by lia; reflexivity).
      imm_norm. rewrite v_addi_pred. wlits. reflexivity. }
    (* the spec byte comparison *)
    assert (Hspec : prefix_eqb (skipn j (nth 1 av [])) (nth k av []) (i + j)
                    = (bv_eqb bh bp
                       && prefix_eqb (skipn (S j) (nth 1 av [])) (nth k av [])
                            (S (i + j)))%bool).
    { rewrite (skipn_nth (nth 1 av []) j (Z_to_bv 8 0) Hjlt). cbn [prefix_eqb].
      rewrite <- (nth_lt_byte_at (nth 1 av []) j Hjlt).
      reflexivity. }
    destruct (bv_eqb bh bp) eqn:Heqb.
    + (* equal: loop *)
      assert (E7 : RiscvSemantics.step target_segs (mkst regs5 0x1001238 afmem arom)
                   = MachineOk (mkst regs5 0x1001220 afmem arom)).
      { rewrite (step_beq_tk target_segs regs5 0x1001238 afmem arom _ 16 17 _
                   TF_1001238 eq_refl TD_1001238).
        - wlits. reflexivity.
        - unfold regs5, regs4, regs3, regs2, regs1. getr_resolve.
          rewrite c_eq_small, bv_eqb_zext. exact Heqb. }
      assert (Hr13' : reg_get regs5 13 = nat_to_word d) by apply regupd_same.
      assert (Hr14' : reg_get regs5 14 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k + nat_to_word (i + S j)).
      { unfold regs5. rewrite regupd_other by reg_neq_tac.
        apply regupd_same. }
      assert (Hr15' : reg_get regs5 15 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1 + nat_to_word (S j)).
      { unfold regs5, regs4. rewrite !regupd_other by reg_neq_tac.
        apply regupd_same. }
      destruct (IH i (S j) regs5 ltac:(lia) ltac:(lia)
                  Hr13' Hr14' Hr15') as [regs' [Hag Hms]].
      exists regs'. split.
      * intros r H13 H14 H15 H16 H17. rewrite (Hag r H13 H14 H15 H16 H17).
        unfold regs5, regs4, regs3, regs2, regs1.
        rewrite !regupd_other by assumption. reflexivity.
      * rewrite Hspec. cbn [andb].
        rewrite <- plus_n_Sm in Hms.
        eapply mst_step; [reflexivity | exact E1 |].
        eapply mst_step; [reflexivity | exact E2 |].
        eapply mst_step; [reflexivity | exact E3 |].
        eapply mst_step; [reflexivity | exact E4 |].
        eapply mst_step; [reflexivity | exact E5 |].
        eapply mst_step; [reflexivity | exact E6 |].
        eapply mst_step; [reflexivity | exact E7 |].
        exact Hms.
    + (* mismatch: exit to 0x100123c *)
      assert (E7 : RiscvSemantics.step target_segs (mkst regs5 0x1001238 afmem arom)
                   = MachineOk (mkst regs5 0x100123c afmem arom)).
      { rewrite (step_beq_ft target_segs regs5 0x1001238 afmem arom _ 16 17 _
                   TF_1001238 eq_refl TD_1001238).
        - wlits. reflexivity.
        - unfold regs5, regs4, regs3, regs2, regs1. getr_resolve.
          rewrite c_eq_small, bv_eqb_zext. exact Heqb. }
      exists regs5. split.
      * intros r H13 H14 H15 H16 H17.
        unfold regs5, regs4, regs3, regs2, regs1.
        rewrite !regupd_other by assumption. reflexivity.
      * rewrite Hspec. cbn [andb].
        eapply mst_step; [reflexivity | exact E1 |].
        eapply mst_step; [reflexivity | exact E2 |].
        eapply mst_step; [reflexivity | exact E3 |].
        eapply mst_step; [reflexivity | exact E4 |].
        eapply mst_step; [reflexivity | exact E5 |].
        eapply mst_step; [reflexivity | exact E6 |].
        eapply mst_step; [reflexivity | exact E7 |].
        apply mst_refl.
Qed.


(* ================================================================= *)
(* Target scan loop vs [scan_from]                                     *)
(* ================================================================= *)

(** The wrapping add of [nat_to_word 0] is the identity (hypothesis-free). *)
Lemma word_add_0_r : forall x : word, x + nat_to_word 0 = x.
Proof.
  intro x. apply bv_eq. rewrite word_add_nat.
  rewrite u_Z2bv by (pose proof (u64_range x); lia). lia.
Qed.

(** From 0x100120c with a1 = i, a2 = &hay[i], a0 = nn >= 1, s5 = hn,
    s2 = &pat, s4 unchanged: exits to 0x1001248 iff the pattern occurs
    at some position >= i, else to 0x1001274.
    Clobbers a1-a5, a6, a7. *)
Lemma ascan : forall k, (k < length av)%nat -> (2 <= length av)%nat ->
  forall f i regs,
  (1 <= length (nth 1 av []))%nat ->
  (length (nth 1 av []) <= length (nth k av []))%nat ->
  (i + f = S (length (nth k av []) - length (nth 1 av [])))%nat ->
  reg_get regs 11 = nat_to_word i ->
  reg_get regs 12 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k + nat_to_word i ->
  reg_get regs 10 = nat_to_word (length (nth 1 av [])) ->
  reg_get regs 21 = nat_to_word (length (nth k av [])) ->
  reg_get regs 18 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1 ->
  exists regs',
    (forall r : reg, r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 ->
       r <> 16 -> r <> 17 -> reg_get regs' r = reg_get regs r) /\
    msteps target_segs (mkst regs 0x100120c afmem arom)
      (mkst regs'
        (if scan_from (nth k av []) (nth 1 av []) i f
         then 0x1001248 else 0x1001274) afmem arom).
Proof.
  intros k Hk H2le.
  pose proof (target_ptr_bounds k Hk) as [Hgeh Hlth].
  pose proof (target_ptr_bounds 1 ltac:(lia)) as [Hgep Hltp].
  pose proof (valid_argv_str_len av k Hva Hk) as Hhlen.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as Hplen.
  induction f as [|f IH]; intros i regs Hnn1 Hnnhn Hif Hr11 Hr12 Hr10 Hr21 Hr18.
  - (* fuel exhausted *)
    set (regs1 := regupd regs 13
           (nat_to_word (i + length (nth 1 av [])))).
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x100120c afmem arom)
                 = MachineOk (mkst regs1 0x1001210 afmem arom)).
    { rewrite (step_add target_segs regs 0x100120c afmem arom _ 13 11 10
                 TF_100120c eq_refl TD_100120c).
      reduce_bv_eqb_ifs.
      getr_resolve. rewrite Hr11, Hr10.
      rewrite v_add_ntw. wlits. reflexivity. }
    (* bltu s5,a3 taken: hn < i + nn *)
    assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x1001210 afmem arom)
                 = MachineOk (mkst regs1 0x1001274 afmem arom)).
    { rewrite (step_bltu_tk target_segs regs1 0x1001210 afmem arom _ 21 13 _
                 TF_1001210 eq_refl TD_1001210).
      - wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite Hr21.
        rewrite c_ltu_ltb. apply Z.ltb_lt. rewrite !u_ntw by lia. lia. }
    exists regs1. split.
    + intros r H11 H12 H13 H14 H15 H16 H17. unfold regs1.
      rewrite regupd_other by assumption. reflexivity.
    + cbn [scan_from].
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      apply mst_refl.
  - (* compare at i, then recurse *)
    assert (Hin : (i + length (nth 1 av []) <= length (nth k av []))%nat) by lia.
    set (regs1 := regupd regs 13
           (nat_to_word (i + length (nth 1 av [])))).
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x100120c afmem arom)
                 = MachineOk (mkst regs1 0x1001210 afmem arom)).
    { rewrite (step_add target_segs regs 0x100120c afmem arom _ 13 11 10
                 TF_100120c eq_refl TD_100120c).
      reduce_bv_eqb_ifs.
      getr_resolve. rewrite Hr11, Hr10.
      rewrite v_add_ntw. wlits. reflexivity. }
    assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x1001210 afmem arom)
                 = MachineOk (mkst regs1 0x1001214 afmem arom)).
    { rewrite (step_bltu_ft target_segs regs1 0x1001210 afmem arom _ 21 13 _
                 TF_1001210 eq_refl TD_1001210).
      - wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite Hr21.
        rewrite c_ltu_ltb. apply Z.ltb_ge. rewrite !u_ntw by lia. lia. }
    (* a3 := nn; a4 := a2; a5 := s2 *)
    set (regs2 := regupd regs1 13 (nat_to_word (length (nth 1 av [])))).
    assert (E3 : RiscvSemantics.step target_segs (mkst regs1 0x1001214 afmem arom)
                 = MachineOk (mkst regs2 0x1001218 afmem arom)).
    { rewrite (step_addi target_segs regs1 0x1001214 afmem arom _ 13 10 _
                 TF_1001214 eq_refl TD_1001214).
      reduce_bv_eqb_ifs.
      unfold regs2, regs1. getr_resolve. rewrite Hr10.
      rewrite v_addi_0. wlits. reflexivity. }
    set (regs3 := regupd regs2 14 (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k + nat_to_word (i + 0))).
    assert (E4 : RiscvSemantics.step target_segs (mkst regs2 0x1001218 afmem arom)
                 = MachineOk (mkst regs3 0x100121c afmem arom)).
    { rewrite (step_addi target_segs regs2 0x1001218 afmem arom _ 14 12 _
                 TF_1001218 eq_refl TD_1001218).
      reduce_bv_eqb_ifs.
      unfold regs3, regs2, regs1. getr_resolve. rewrite Hr12.
      rewrite v_addi_0.
      rewrite Nat.add_0_r. wlits. reflexivity. }
    set (regs4 := regupd regs3 15 (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1 + nat_to_word 0)).
    assert (E5 : RiscvSemantics.step target_segs (mkst regs3 0x100121c afmem arom)
                 = MachineOk (mkst regs4 0x1001220 afmem arom)).
    { rewrite (step_addi target_segs regs3 0x100121c afmem arom _ 15 18 _
                 TF_100121c eq_refl TD_100121c).
      reduce_bv_eqb_ifs.
      unfold regs4, regs3, regs2, regs1. getr_resolve. rewrite Hr18.
      rewrite v_addi_0.
      rewrite word_add_0_r. wlits. reflexivity. }
    assert (Hr13_4 : reg_get regs4 13 = nat_to_word (length (nth 1 av []))).
    { unfold regs4, regs3. rewrite !regupd_other by reg_neq_tac.
      apply regupd_same. }
    assert (Hr14_4 : reg_get regs4 14 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k + nat_to_word (i + 0)).
    { unfold regs4. rewrite regupd_other by reg_neq_tac.
      apply regupd_same. }
    assert (Hr15_4 : reg_get regs4 15 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1 + nat_to_word 0)
      by apply regupd_same.
    destruct (acmp k Hk H2le i (length (nth 1 av [])) 0 regs4
                ltac:(lia) Hin Hr13_4 Hr14_4 Hr15_4) as [regsC [HagC HmsC]].
    rewrite skipn_O, Nat.add_0_r in HmsC.
    cbn [scan_from].
    destruct (prefix_eqb (nth 1 av []) (nth k av []) i) eqn:Epre.
    + (* match *)
      exists regsC. split.
      * intros r H11 H12 H13 H14 H15 H16 H17.
        rewrite (HagC r H13 H14 H15 H16 H17).
        unfold regs4, regs3, regs2, regs1.
        rewrite !regupd_other by assumption. reflexivity.
      * cbn [orb].
        eapply mst_step; [reflexivity | exact E1 |].
        eapply mst_step; [reflexivity | exact E2 |].
        eapply mst_step; [reflexivity | exact E3 |].
        eapply mst_step; [reflexivity | exact E4 |].
        eapply mst_step; [reflexivity | exact E5 |].
        exact HmsC.
    + (* no match at i: a1 += 1; a2 += 1; loop *)
      assert (HrC : forall r : reg, r <> 13 -> r <> 14 -> r <> 15 -> r <> 16 ->
                      r <> 17 -> reg_get regsC r = reg_get regs4 r).
      { intros. apply HagC; assumption. }
      set (regsD := regupd regsC 11 (nat_to_word (S i))).
      assert (E6 : RiscvSemantics.step target_segs (mkst regsC 0x100123c afmem arom)
                   = MachineOk (mkst regsD 0x1001240 afmem arom)).
      { rewrite (step_addi target_segs regsC 0x100123c afmem arom _ 11 11 _
                   TF_100123c eq_refl TD_100123c).
        reduce_bv_eqb_ifs.
        unfold regsD. getr_resolve.
        rewrite (HrC 11) by reg_neq_tac.
        unfold regs4, regs3, regs2, regs1.
        rewrite !regupd_other by reg_neq_tac.
        rewrite Hr11. rewrite v_addi_Sj by lia. wlits. reflexivity. }
      set (regsE := regupd regsD 12
             (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k + nat_to_word (S i))).
      assert (E7 : RiscvSemantics.step target_segs (mkst regsD 0x1001240 afmem arom)
                   = MachineOk (mkst regsE 0x1001244 afmem arom)).
      { rewrite (step_addi target_segs regsD 0x1001240 afmem arom _ 12 12 _
                   TF_1001240 eq_refl TD_1001240).
        reduce_bv_eqb_ifs.
        unfold regsE, regsD. getr_resolve.
        rewrite (HrC 12) by reg_neq_tac.
        unfold regs4, regs3, regs2, regs1.
        rewrite !regupd_other by reg_neq_tac.
        rewrite Hr12. imm_norm. rewrite v_addi_ptr_S. wlits. reflexivity. }
      assert (E8 : RiscvSemantics.step target_segs (mkst regsE 0x1001244 afmem arom)
                   = MachineOk (mkst regsE 0x100120c afmem arom)).
      { rewrite (step_jal_x0 target_segs regsE 0x1001244 afmem arom _ _
                   TF_1001244 eq_refl TD_1001244).
        wlits. reflexivity. }
      assert (HagE : forall r : reg, r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 ->
                       r <> 15 -> r <> 16 -> r <> 17 -> reg_get regsE r = reg_get regs r).
      { intros r H11 H12 H13 H14 H15 H16 H17.
        unfold regsE, regsD. rewrite !regupd_other by assumption.
        rewrite (HrC r H13 H14 H15 H16 H17).
        unfold regs4, regs3, regs2, regs1.
        rewrite !regupd_other by assumption. reflexivity. }
      assert (Hr11E : reg_get regsE 11 = nat_to_word (S i)).
      { unfold regsE. rewrite regupd_other by reg_neq_tac.
        apply regupd_same. }
      assert (Hr12E : reg_get regsE 12 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k + nat_to_word (S i))
        by apply regupd_same.
      assert (Hr10E : reg_get regsE 10 = nat_to_word (length (nth 1 av [])))
        by (rewrite (HagE 10) by reg_neq_tac; exact Hr10).
      assert (Hr21E : reg_get regsE 21 = nat_to_word (length (nth k av [])))
        by (rewrite (HagE 21) by reg_neq_tac; exact Hr21).
      assert (Hr18E : reg_get regsE 18 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1)
        by (rewrite (HagE 18) by reg_neq_tac; exact Hr18).
      destruct (IH (S i) regsE Hnn1 Hnnhn ltac:(lia)
                  Hr11E Hr12E Hr10E Hr21E Hr18E) as [regs' [Hag' Hms']].
      exists regs'. split.
      * intros r H11 H12 H13 H14 H15 H16 H17.
        rewrite (Hag' r H11 H12 H13 H14 H15 H16 H17).
        apply HagE; assumption.
      * cbn [orb].
        eapply mst_step; [reflexivity | exact E1 |].
        eapply mst_step; [reflexivity | exact E2 |].
        eapply mst_step; [reflexivity | exact E3 |].
        eapply mst_step; [reflexivity | exact E4 |].
        eapply mst_step; [reflexivity | exact E5 |].
        eapply msteps_trans; [exact HmsC |].
        eapply mst_step; [reflexivity | exact E6 |].
        eapply mst_step; [reflexivity | exact E7 |].
        eapply mst_step; [reflexivity | exact E8 |].
        exact Hms'.
Qed.


(* ================================================================= *)
(* Match output: 0x1001248 -> 0x1001274                               *)
(* ================================================================= *)

(** On the match path the target writes argv[i] (skipping the zero-length
    write when it is empty) then "\n", each via put; both puts succeed with
    a0 = 0.  Clobbers ra, a0-a2, a7, and s4 (the [li s4,3]). *)
Lemma aoutput : forall i regs bufs code, (i < length av)%nat ->
  reg_get regs 20 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) i ->
  reg_get regs 21 = nat_to_word (length (nth i av [])) ->
  reg_get regs 19 = (0x1000158 : word) ->
  (forall regs',
     (forall r : reg, r <> 1 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 17 ->
        r <> 20 -> reg_get regs' r = reg_get regs r) ->
     wexit1 target_segs (mkst regs' 0x1001274 afmem arom) bufs code) ->
  wexit1 target_segs (mkst regs 0x1001248 afmem arom)
    ((match nth i av [] with
      | [] => [[Z_to_bv 8 10]] | _ :: _ => [nth i av []; [Z_to_bv 8 10]] end) ++ bufs) code.
Proof.
  intros i regs bufs code Hi Hr20 Hr21 Hr19 Hcont.
  pose proof (target_ptr_bounds i Hi) as [Hge Hlt].
  pose proof (valid_argv_str_len av i Hva Hi) as Hslen.
  destruct (nth i av []) as [|b0 srest] eqn:Ea.
  - (* empty argument: only the newline is written *)
    cbn [length] in Hr21, Hslen. cbn [app].
    (* mv a0,s4; mv a1,s5; auipc ra; call put *)
    stepi TF_1001248 TD_1001248.
    stepi TF_100124c TD_100124c.
    stepi TF_1001250 TD_1001250.
    stepjr TF_1001254 TD_1001254 (0x1001250 : word) ltac:(getr_resolve; bveq).
    eapply tput_zero with (RA := (0x1001258 : word));
      [ regupd_resolve; getr_resolve; rewrite Hr21; bveq
      | regupd_resolve; bveq
      | bveq
      | ].
    intros regs1 Hag1 H10_1.
    (* li s4,3; bnez a0 falls through *)
    stepi TF_1001258 TD_1001258.
    chain_step;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact TF_100125c | reflexivity | exact TD_100125c
        | getr_resolve; rewrite H10_1; exact c_eq_0_true ]
      | norm_pc ].
    (* li a1,1; mv a0,s3; auipc ra; call put (newline) *)
    stepi TF_1001260 TD_1001260.
    stepi TF_1001264 TD_1001264.
    stepi TF_1001268 TD_1001268.
    stepjr TF_100126c TD_100126c (0x1001268 : word) ltac:(getr_resolve; bveq).
    eapply tput_pos with (B := (0x1000158 : word)) (L := Z_to_bv 64 1)
                         (buf := [Z_to_bv 8 10]) (RA := (0x1001270 : word));
      [ regupd_resolve; getr_resolve; rewrite (Hag1 19) by reg_neq_tac;
        regupd_resolve; rewrite Hr19; apply v_addi_0
      | regupd_resolve; getr_resolve; bveq
      | u_norm; lia
      | u_norm; lia
      | apply Z.leb_le; vm_compute; reflexivity
      | regupd_resolve; bveq
      | bveq
      | exact aread_newline
      | ].
    intros regs2 Hag2 H10_2.
    (* bnez a0 falls through -> 0x1001274 *)
    chain_step;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact TF_1001270 | reflexivity | exact TD_1001270
        | getr_resolve; rewrite H10_2; exact c_eq_0_true ]
      | norm_pc ].
    apply Hcont.
    intros r Hx1 Hx10 Hx11 Hx12 Hx17 Hx20.
    rewrite (Hag2 r Hx10 Hx11 Hx12 Hx17).
    repeat (rewrite regupd_other by assumption).
    rewrite (Hag1 r Hx10 Hx11 Hx12 Hx17).
    repeat (rewrite regupd_other by assumption). reflexivity.
  - (* nonempty argument: write it, then the newline *)
    rewrite <- Ea in *.
    assert (Hnn : (1 <= length (nth i av []))%nat) by (rewrite Ea; cbn; lia).
    cbn [app].
    stepi TF_1001248 TD_1001248.
    stepi TF_100124c TD_100124c.
    stepi TF_1001250 TD_1001250.
    stepjr TF_1001254 TD_1001254 (0x1001250 : word) ltac:(getr_resolve; bveq).
    eapply tput_pos with (B := cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) i)
                         (L := nat_to_word (length (nth i av [])))
                         (buf := nth i av []) (RA := (0x1001258 : word));
      [ regupd_resolve; getr_resolve; rewrite Hr20; apply v_addi_0
      | regupd_resolve; getr_resolve; rewrite Hr21; apply v_addi_0
      | rewrite u_ntw by lia; lia
      | rewrite u_ntw by lia; lia
      | rewrite u_ntw by lia; exact (argv_str_task inp amb asp abrk arnd Hlau i Hi)
      | regupd_resolve; bveq
      | bveq
      | rewrite word_to_nat_ntw by lia; apply aread_str; exact Hi
      | ].
    intros regs1 Hag1 H10_1.
    stepi TF_1001258 TD_1001258.
    chain_step;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact TF_100125c | reflexivity | exact TD_100125c
        | getr_resolve; rewrite H10_1; exact c_eq_0_true ]
      | norm_pc ].
    stepi TF_1001260 TD_1001260.
    stepi TF_1001264 TD_1001264.
    stepi TF_1001268 TD_1001268.
    stepjr TF_100126c TD_100126c (0x1001268 : word) ltac:(getr_resolve; bveq).
    eapply tput_pos with (B := (0x1000158 : word)) (L := Z_to_bv 64 1)
                         (buf := [Z_to_bv 8 10]) (RA := (0x1001270 : word));
      [ regupd_resolve; getr_resolve; rewrite (Hag1 19) by reg_neq_tac;
        regupd_resolve; rewrite Hr19; apply v_addi_0
      | regupd_resolve; getr_resolve; bveq
      | u_norm; lia
      | u_norm; lia
      | apply Z.leb_le; vm_compute; reflexivity
      | regupd_resolve; bveq
      | bveq
      | exact aread_newline
      | ].
    intros regs2 Hag2 H10_2.
    chain_step;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact TF_1001270 | reflexivity | exact TD_1001270
        | getr_resolve; rewrite H10_2; exact c_eq_0_true ]
      | norm_pc ].
    apply Hcont.
    intros r Hx1 Hx10 Hx11 Hx12 Hx17 Hx20.
    rewrite (Hag2 r Hx10 Hx11 Hx12 Hx17).
    repeat (rewrite regupd_other by assumption).
    rewrite (Hag1 r Hx10 Hx11 Hx12 Hx17).
    repeat (rewrite regupd_other by assumption). reflexivity.
Qed.


(* ================================================================= *)
(* One argument: 0x10011d4 -> 0x1001274                               *)
(* ================================================================= *)

Lemma target_arg : forall i regs bufs code,
  (2 <= length av)%nat -> (2 <= i)%nat -> (i < length av)%nat ->
  reg_get regs 8 = Z_to_bv 64 (bv_unsigned asp + 8) ->
  reg_get regs 9 = aargcN ->
  reg_get regs 18 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1 ->
  reg_get regs 19 = (0x1000158 : word) ->
  reg_get regs 22 = nat_to_word i ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 0x50) ->
  (forall regs',
     reg_get regs' 8 = Z_to_bv 64 (bv_unsigned asp + 8) -> reg_get regs' 9 = aargcN ->
     reg_get regs' 18 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1 -> reg_get regs' 19 = (0x1000158 : word) ->
     reg_get regs' 22 = nat_to_word i -> reg_get regs' 2 = Z_to_bv 64 (bv_unsigned asp - 0x50) ->
     wexit1 target_segs (mkst regs' 0x1001274 afmem arom) bufs code) ->
  wexit1 target_segs (mkst regs 0x10011d4 afmem arom)
    (arg_bufs (nth 1 av []) (nth i av []) ++ bufs) code.
Proof.
  intros i regs bufs code H2le H2i Hi Hr8 Hr9 Hr18 Hr19 Hr22 Hr2 Hcont.
  pose proof (valid_argv_len av Hva) as Hargc.
  pose proof (target_ptr_bounds i Hi) as [Hgeh Hlth].
  pose proof (target_ptr_bounds 1 ltac:(lia)) as [Hgep Hltp].
  pose proof (valid_argv_str_len av i Hva Hi) as Hhlen.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as Hplen.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  assert (HiN : (Z.of_nat i <= 1024)%Z) by lia.
  assert (Hfit : (bv_unsigned asp + 8 + 8 * Z.of_nat i < 2^64)%Z) by lia.
  (* --- 0x10011d4..0x10011dc: index the argv table, load &argv[i] --- *)
  set (regs1 := regupd regs 10 (Z_to_bv 64 (8 * Z.of_nat i))).
  assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x10011d4 afmem arom)
               = MachineOk (mkst regs1 0x10011d8 afmem arom)).
  { rewrite (step_slli target_segs regs 0x10011d4 afmem arom _ 10 22 _
               TF_10011d4 eq_refl TD_10011d4).
    reduce_bv_eqb_ifs. getr_resolve.
    rewrite Hr22. rewrite v_slli3_nat by lia. wlits. reflexivity. }
  set (regs2 := regupd regs1 10 (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * Z.of_nat i))).
  assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x10011d8 afmem arom)
               = MachineOk (mkst regs2 0x10011dc afmem arom)).
  { rewrite (step_add target_segs regs1 0x10011d8 afmem arom _ 10 8 10
               TF_10011d8 eq_refl TD_10011d8).
    reduce_bv_eqb_ifs.
    unfold regs2, regs1. getr_resolve. rewrite Hr8.
    replace (v_add (Z_to_bv 64 (bv_unsigned asp + 8)) (Z_to_bv 64 (8 * Z.of_nat i)))
      with (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * Z.of_nat i))
      by (apply bv_eq; rewrite v_add_small by (u_norm; lia); u_norm; lia).
    wlits. reflexivity. }
  set (regs3 := regupd regs2 20 (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) i)).
  assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x10011dc afmem arom)
               = MachineOk (mkst regs3 0x10011e0 afmem arom)).
  { rewrite (step_ld target_segs regs2 0x10011dc afmem arom _ 20 10 _
               (word_le8 (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) i)) (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) i)
               TF_10011dc eq_refl TD_10011dc).
    - reduce_bv_eqb_ifs. wlits. reflexivity.
    - unfold regs2. getr_resolve.
      rewrite v_addi_0.
      apply aread_ptr. exact Hi.
    - exact (bytes_le_n_to_le_8 _). }
  set (regs4 := regupd regs3 10 (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) i)).
  assert (E4 : RiscvSemantics.step target_segs (mkst regs3 0x10011e0 afmem arom)
               = MachineOk (mkst regs4 0x10011e4 afmem arom)).
  { rewrite (step_addi target_segs regs3 0x10011e0 afmem arom _ 10 20 _
               TF_10011e0 eq_refl TD_10011e0).
    reduce_bv_eqb_ifs.
    unfold regs4, regs3. getr_resolve. rewrite v_addi_0. wlits. reflexivity. }
  set (regs5 := regupd regs4 1 (0x10011e4 : word)).
  assert (E5 : RiscvSemantics.step target_segs (mkst regs4 0x10011e4 afmem arom)
               = MachineOk (mkst regs5 0x10011e8 afmem arom)).
  { rewrite (step_auipc target_segs regs4 0x10011e4 afmem arom _ 1 _
               TF_10011e4 eq_refl TD_10011e4).
    reduce_bv_eqb_ifs. wlits. reflexivity. }
  set (regs6 := regupd regs5 1 (0x10011ec : word)).
  assert (E6 : RiscvSemantics.step target_segs (mkst regs5 0x10011e8 afmem arom)
               = MachineOk (mkst regs6 0x10012e4 afmem arom)).
  { rewrite (step_jalr_link target_segs regs5 0x10011e8 afmem arom _ 1 1 _
               (0x10011e4 : word) TF_10011e8 eq_refl TD_10011e8).
    - wlits. reflexivity.
    - reflexivity.
    - unfold regs5. getr_resolve. reflexivity. }
  (* --- slen(argv[i]) --- *)
  assert (H10_6 : reg_get regs6 10 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) i).
  { unfold regs6, regs5, regs4. regupd_resolve. reflexivity. }
  assert (H1_6 : reg_get regs6 1 = (0x10011ec : word)) by (unfold regs6; apply regupd_same).
  destruct (aslen i (0x10011ec : word) regs6 Hi H10_6 H1_6 ltac:(bveq))
    as [regsH [HagH [H10H HmsH]]].
  set (regs7 := regupd regsH 21 (nat_to_word (length (nth i av [])))).
  assert (E7 : RiscvSemantics.step target_segs (mkst regsH 0x10011ec afmem arom)
               = MachineOk (mkst regs7 0x10011f0 afmem arom)).
  { rewrite (step_addi target_segs regsH 0x10011ec afmem arom _ 21 10 _
               TF_10011ec eq_refl TD_10011ec).
    reduce_bv_eqb_ifs.
    unfold regs7. getr_resolve. rewrite H10H.
    rewrite v_addi_0. wlits. reflexivity. }
  set (regs8 := regupd regs7 10 (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1)).
  assert (E8 : RiscvSemantics.step target_segs (mkst regs7 0x10011f0 afmem arom)
               = MachineOk (mkst regs8 0x10011f4 afmem arom)).
  { rewrite (step_addi target_segs regs7 0x10011f0 afmem arom _ 10 18 _
               TF_10011f0 eq_refl TD_10011f0).
    reduce_bv_eqb_ifs.
    unfold regs8, regs7. getr_resolve. rewrite (HagH 18) by reg_neq_tac.
    unfold regs6, regs5, regs4, regs3, regs2, regs1.
    rewrite !regupd_other by reg_neq_tac. rewrite Hr18.
    rewrite v_addi_0. wlits. reflexivity. }
  set (regs9 := regupd regs8 1 (0x10011f4 : word)).
  assert (E9 : RiscvSemantics.step target_segs (mkst regs8 0x10011f4 afmem arom)
               = MachineOk (mkst regs9 0x10011f8 afmem arom)).
  { rewrite (step_auipc target_segs regs8 0x10011f4 afmem arom _ 1 _
               TF_10011f4 eq_refl TD_10011f4).
    reduce_bv_eqb_ifs. wlits. reflexivity. }
  set (regs10 := regupd regs9 1 (0x10011fc : word)).
  assert (E10 : RiscvSemantics.step target_segs (mkst regs9 0x10011f8 afmem arom)
                = MachineOk (mkst regs10 0x10012e4 afmem arom)).
  { rewrite (step_jalr_link target_segs regs9 0x10011f8 afmem arom _ 1 1 _
               (0x10011f4 : word) TF_10011f8 eq_refl TD_10011f8).
    - wlits. reflexivity.
    - reflexivity.
    - unfold regs9. getr_resolve. reflexivity. }
  (* --- slen(argv[1]) --- *)
  assert (H10_10 : reg_get regs10 10 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1).
  { unfold regs10, regs9, regs8. regupd_resolve. reflexivity. }
  assert (H1_10 : reg_get regs10 1 = (0x10011fc : word)) by (unfold regs10; apply regupd_same).
  destruct (aslen 1 (0x10011fc : word) regs10 ltac:(lia) H10_10 H1_10 ltac:(bveq))
    as [regsP [HagP [H10P HmsP]]].
  (* common prefix machine steps from 0x10011d4 to 0x10011fc *)
  assert (HmsPre : msteps target_segs (mkst regs 0x10011d4 afmem arom)
                          (mkst regsP 0x10011fc afmem arom)).
  { eapply mst_step; [reflexivity | exact E1 |].
    eapply mst_step; [reflexivity | exact E2 |].
    eapply mst_step; [reflexivity | exact E3 |].
    eapply mst_step; [reflexivity | exact E4 |].
    eapply mst_step; [reflexivity | exact E5 |].
    eapply mst_step; [reflexivity | exact E6 |].
    eapply msteps_trans; [exact HmsH |].
    eapply mst_step; [reflexivity | exact E7 |].
    eapply mst_step; [reflexivity | exact E8 |].
    eapply mst_step; [reflexivity | exact E9 |].
    eapply mst_step; [reflexivity | exact E10 |].
    eapply msteps_trans; [exact HmsP |]. apply mst_refl. }
  (* transport the loop invariant to regsP *)
  assert (H20P : reg_get regsP 20 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) i).
  { rewrite (HagP 20) by reg_neq_tac.
    unfold regs10, regs9, regs8. rewrite !regupd_other by reg_neq_tac.
    unfold regs7. rewrite regupd_other by reg_neq_tac.
    rewrite (HagH 20) by reg_neq_tac.
    unfold regs6, regs5, regs4. rewrite !regupd_other by reg_neq_tac.
    unfold regs3. apply regupd_same. }
  assert (H21P : reg_get regsP 21 = nat_to_word (length (nth i av []))).
  { rewrite (HagP 21) by reg_neq_tac.
    unfold regs10, regs9, regs8. rewrite !regupd_other by reg_neq_tac.
    unfold regs7. apply regupd_same. }
  assert (H18P : reg_get regsP 18 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1).
  { rewrite (HagP 18) by reg_neq_tac.
    unfold regs10, regs9, regs8. rewrite !regupd_other by reg_neq_tac.
    unfold regs7. rewrite regupd_other by reg_neq_tac.
    rewrite (HagH 18) by reg_neq_tac.
    unfold regs6, regs5, regs4, regs3, regs2, regs1.
    rewrite !regupd_other by reg_neq_tac. exact Hr18. }
  assert (H19P : reg_get regsP 19 = (0x1000158 : word)).
  { rewrite (HagP 19) by reg_neq_tac.
    unfold regs10, regs9, regs8. rewrite !regupd_other by reg_neq_tac.
    unfold regs7. rewrite regupd_other by reg_neq_tac.
    rewrite (HagH 19) by reg_neq_tac.
    unfold regs6, regs5, regs4, regs3, regs2, regs1.
    rewrite !regupd_other by reg_neq_tac. exact Hr19. }
  assert (H22P : reg_get regsP 22 = nat_to_word i).
  { rewrite (HagP 22) by reg_neq_tac.
    unfold regs10, regs9, regs8. rewrite !regupd_other by reg_neq_tac.
    unfold regs7. rewrite regupd_other by reg_neq_tac.
    rewrite (HagH 22) by reg_neq_tac.
    unfold regs6, regs5, regs4, regs3, regs2, regs1.
    rewrite !regupd_other by reg_neq_tac. exact Hr22. }
  assert (H2P : reg_get regsP 2 = Z_to_bv 64 (bv_unsigned asp - 0x50)).
  { rewrite (HagP 2) by reg_neq_tac.
    unfold regs10, regs9, regs8. rewrite !regupd_other by reg_neq_tac.
    unfold regs7. rewrite regupd_other by reg_neq_tac.
    rewrite (HagH 2) by reg_neq_tac.
    unfold regs6, regs5, regs4, regs3, regs2, regs1.
    rewrite !regupd_other by reg_neq_tac. exact Hr2. }
  assert (H8P : reg_get regsP 8 = Z_to_bv 64 (bv_unsigned asp + 8)).
  { rewrite (HagP 8) by reg_neq_tac.
    unfold regs10, regs9, regs8. rewrite !regupd_other by reg_neq_tac.
    unfold regs7. rewrite regupd_other by reg_neq_tac.
    rewrite (HagH 8) by reg_neq_tac.
    unfold regs6, regs5, regs4, regs3, regs2, regs1.
    rewrite !regupd_other by reg_neq_tac. exact Hr8. }
  assert (H9P : reg_get regsP 9 = aargcN).
  { rewrite (HagP 9) by reg_neq_tac.
    unfold regs10, regs9, regs8. rewrite !regupd_other by reg_neq_tac.
    unfold regs7. rewrite regupd_other by reg_neq_tac.
    rewrite (HagH 9) by reg_neq_tac.
    unfold regs6, regs5, regs4, regs3, regs2, regs1.
    rewrite !regupd_other by reg_neq_tac. exact Hr9. }
  (* --- case analysis on the pattern / containment --- *)
  destruct (Nat.eq_dec (length (nth 1 av [])) 0) as [Hnn0 | Hnn].
  - (* empty pattern: always matches *)
    assert (Hcont_b : contains_b (nth i av []) (nth 1 av []) = true)
      by (unfold contains_b; rewrite Hnn0; reflexivity).
    unfold arg_bufs. rewrite Hcont_b.
    eapply msteps_to_wallexit; [exact HmsPre |].
    chain_step;
      [ reflexivity
      | eapply step_beq_tk;
        [ exact TF_10011fc | reflexivity | exact TD_10011fc
        | getr_resolve; rewrite H10P, Hnn0; exact c_eq_0_true ]
      | norm_pc ].
    eapply aoutput; [ exact Hi | exact H20P | exact H21P | exact H19P | ].
    intros regsF HagF. apply Hcont.
    + rewrite (HagF 8) by reg_neq_tac. exact H8P.
    + rewrite (HagF 9) by reg_neq_tac. exact H9P.
    + rewrite (HagF 18) by reg_neq_tac. exact H18P.
    + rewrite (HagF 19) by reg_neq_tac. exact H19P.
    + rewrite (HagF 22) by reg_neq_tac. exact H22P.
    + rewrite (HagF 2) by reg_neq_tac. exact H2P.
  - (* nonempty pattern *)
    assert (Hnn1 : (1 <= length (nth 1 av []))%nat) by lia.
    destruct (le_lt_dec (length (nth 1 av [])) (length (nth i av [])))
      as [Hle | Hgt].
    + (* nn <= hn: scan *)
      assert (Hcont_b : contains_b (nth i av []) (nth 1 av [])
              = scan_from (nth i av []) (nth 1 av []) 0
                  (S (length (nth i av []) - length (nth 1 av [])))).
      { unfold contains_b.
        rewrite (proj2 (Nat.eqb_neq _ 0) Hnn).
        rewrite (proj2 (Nat.ltb_ge _ _) Hle). reflexivity. }
      set (regsQ1 := regupd regsP 11 (nat_to_word 0)).
      set (regsQ2 := regupd regsQ1 12 (cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) i)).
      assert (E11 : RiscvSemantics.step target_segs (mkst regsP 0x10011fc afmem arom)
                    = MachineOk (mkst regsP 0x1001200 afmem arom)).
      { rewrite (step_beq_ft target_segs regsP 0x10011fc afmem arom _ 10 0 _
                   TF_10011fc eq_refl TD_10011fc).
        - wlits. reflexivity.
        - getr_resolve. rewrite H10P. apply c_eq_0_false.
          rewrite u_ntw by lia. lia. }
      assert (E12 : RiscvSemantics.step target_segs (mkst regsP 0x1001200 afmem arom)
                    = MachineOk (mkst regsP 0x1001204 afmem arom)).
      { rewrite (step_bltu_ft target_segs regsP 0x1001200 afmem arom _ 21 10 _
                   TF_1001200 eq_refl TD_1001200).
        - wlits. reflexivity.
        - getr_resolve. rewrite H21P, H10P. rewrite c_ltu_ltb.
          apply Z.ltb_ge. rewrite !u_ntw by lia. lia. }
      assert (E13 : RiscvSemantics.step target_segs (mkst regsP 0x1001204 afmem arom)
                    = MachineOk (mkst regsQ1 0x1001208 afmem arom)).
      { rewrite (step_addi target_segs regsP 0x1001204 afmem arom _ 11 0 _
                   TF_1001204 eq_refl TD_1001204).
        reduce_bv_eqb_ifs. getr_resolve.
        replace (v_addi (Z_to_bv 64 0) (bv_signed (0%bv : bv 12)))
          with (nat_to_word 0) by bveq.
        wlits. reflexivity. }
      assert (E14 : RiscvSemantics.step target_segs (mkst regsQ1 0x1001208 afmem arom)
                    = MachineOk (mkst regsQ2 0x100120c afmem arom)).
      { rewrite (step_addi target_segs regsQ1 0x1001208 afmem arom _ 12 20 _
                   TF_1001208 eq_refl TD_1001208).
        reduce_bv_eqb_ifs.
        unfold regsQ2, regsQ1. getr_resolve. rewrite H20P.
        rewrite v_addi_0. wlits. reflexivity. }
      assert (HmsQ : msteps target_segs (mkst regsP 0x10011fc afmem arom)
                            (mkst regsQ2 0x100120c afmem arom)).
      { eapply mst_step; [reflexivity | exact E11 |].
        eapply mst_step; [reflexivity | exact E12 |].
        eapply mst_step; [reflexivity | exact E13 |].
        eapply mst_step; [reflexivity | exact E14 |].
        apply mst_refl. }
      assert (H11Q : reg_get regsQ2 11 = nat_to_word 0).
      { unfold regsQ2. rewrite regupd_other by reg_neq_tac.
        unfold regsQ1. apply regupd_same. }
      assert (H12Q : reg_get regsQ2 12 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) i + nat_to_word 0).
      { unfold regsQ2. rewrite regupd_same. rewrite word_add_0_r. reflexivity. }
      assert (H10Q : reg_get regsQ2 10 = nat_to_word (length (nth 1 av []))).
      { unfold regsQ2. rewrite regupd_other by reg_neq_tac.
        unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H10P. }
      assert (H21Q : reg_get regsQ2 21 = nat_to_word (length (nth i av []))).
      { unfold regsQ2. rewrite regupd_other by reg_neq_tac.
        unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H21P. }
      assert (H18Q : reg_get regsQ2 18 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1).
      { unfold regsQ2. rewrite regupd_other by reg_neq_tac.
        unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H18P. }
      destruct (ascan i Hi H2le
                  (S (length (nth i av []) - length (nth 1 av []))) 0 regsQ2
                  Hnn1 Hle ltac:(lia) H11Q H12Q H10Q H21Q H18Q)
        as [regsS [HagS HmsS]].
      unfold arg_bufs. rewrite Hcont_b.
      eapply msteps_to_wallexit; [exact HmsPre |].
      eapply msteps_to_wallexit; [exact HmsQ |].
      eapply msteps_to_wallexit; [exact HmsS |].
      destruct (scan_from (nth i av []) (nth 1 av []) 0
                  (S (length (nth i av []) - length (nth 1 av [])))) eqn:Esc.
      * (* match *)
        assert (H20S : reg_get regsS 20 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) i).
        { rewrite (HagS 20) by reg_neq_tac.
          unfold regsQ2. rewrite regupd_other by reg_neq_tac.
          unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H20P. }
        assert (H21S : reg_get regsS 21 = nat_to_word (length (nth i av []))).
        { rewrite (HagS 21) by reg_neq_tac.
          unfold regsQ2. rewrite regupd_other by reg_neq_tac.
          unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H21P. }
        assert (H19S : reg_get regsS 19 = (0x1000158 : word)).
        { rewrite (HagS 19) by reg_neq_tac.
          unfold regsQ2. rewrite regupd_other by reg_neq_tac.
          unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H19P. }
        eapply aoutput; [ exact Hi | exact H20S | exact H21S | exact H19S | ].
        intros regsF HagF. apply Hcont.
        -- rewrite (HagF 8) by reg_neq_tac. rewrite (HagS 8) by reg_neq_tac.
           unfold regsQ2. rewrite regupd_other by reg_neq_tac.
           unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H8P.
        -- rewrite (HagF 9) by reg_neq_tac. rewrite (HagS 9) by reg_neq_tac.
           unfold regsQ2. rewrite regupd_other by reg_neq_tac.
           unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H9P.
        -- rewrite (HagF 18) by reg_neq_tac. rewrite (HagS 18) by reg_neq_tac.
           unfold regsQ2. rewrite regupd_other by reg_neq_tac.
           unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H18P.
        -- rewrite (HagF 19) by reg_neq_tac. rewrite (HagS 19) by reg_neq_tac.
           unfold regsQ2. rewrite regupd_other by reg_neq_tac.
           unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H19P.
        -- rewrite (HagF 22) by reg_neq_tac. rewrite (HagS 22) by reg_neq_tac.
           unfold regsQ2. rewrite regupd_other by reg_neq_tac.
           unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H22P.
        -- rewrite (HagF 2) by reg_neq_tac. rewrite (HagS 2) by reg_neq_tac.
           unfold regsQ2. rewrite regupd_other by reg_neq_tac.
           unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H2P.
      * (* no match *)
        cbn [app]. apply Hcont.
        -- rewrite (HagS 8) by reg_neq_tac.
           unfold regsQ2. rewrite regupd_other by reg_neq_tac.
           unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H8P.
        -- rewrite (HagS 9) by reg_neq_tac.
           unfold regsQ2. rewrite regupd_other by reg_neq_tac.
           unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H9P.
        -- rewrite (HagS 18) by reg_neq_tac.
           unfold regsQ2. rewrite regupd_other by reg_neq_tac.
           unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H18P.
        -- rewrite (HagS 19) by reg_neq_tac.
           unfold regsQ2. rewrite regupd_other by reg_neq_tac.
           unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H19P.
        -- rewrite (HagS 22) by reg_neq_tac.
           unfold regsQ2. rewrite regupd_other by reg_neq_tac.
           unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H22P.
        -- rewrite (HagS 2) by reg_neq_tac.
           unfold regsQ2. rewrite regupd_other by reg_neq_tac.
           unfold regsQ1. rewrite regupd_other by reg_neq_tac. exact H2P.
    + (* hn < nn: no match without scanning *)
      assert (Hcont_b : contains_b (nth i av []) (nth 1 av []) = false).
      { unfold contains_b.
        rewrite (proj2 (Nat.eqb_neq _ 0) Hnn).
        rewrite (proj2 (Nat.ltb_lt _ _) Hgt). reflexivity. }
      unfold arg_bufs. rewrite Hcont_b. cbn [app].
      eapply msteps_to_wallexit; [exact HmsPre |].
      chain_step;
        [ reflexivity
        | eapply step_beq_ft;
          [ exact TF_10011fc | reflexivity | exact TD_10011fc
          | getr_resolve; rewrite H10P; apply c_eq_0_false;
            rewrite u_ntw by lia; lia ]
        | norm_pc ].
      chain_step;
        [ reflexivity
        | eapply step_bltu_tk;
          [ exact TF_1001200 | reflexivity | exact TD_1001200
          | getr_resolve; rewrite H21P, H10P; rewrite c_ltu_ltb;
            apply Z.ltb_lt; rewrite !u_ntw by lia; lia ]
        | norm_pc ].
      apply Hcont.
      * exact H8P.
      * exact H9P.
      * exact H18P.
      * exact H19P.
      * exact H22P.
      * exact H2P.
Qed.


(* ================================================================= *)
(* Outer loop                                                         *)
(* ================================================================= *)

Lemma target_loop : forall m i regs,
  (2 <= length av)%nat -> (2 <= i)%nat -> (i + S m = length av)%nat ->
  reg_get regs 8 = Z_to_bv 64 (bv_unsigned asp + 8) ->
  reg_get regs 9 = aargcN ->
  reg_get regs 18 = cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1 ->
  reg_get regs 19 = (0x1000158 : word) ->
  reg_get regs 22 = nat_to_word i ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 0x50) ->
  wexit1 target_segs (mkst regs 0x10011d4 afmem arom)
    (grep_bufs (nth 1 av []) (skipn i av)) (Z_to_bv 64 0).
Proof.
  intros m. induction m as [|m IH];
    intros i regs H2le H2i Him Hr8 Hr9 Hr18 Hr19 Hr22 Hr2;
    pose proof (valid_argv_len av Hva) as Hargc.
  - (* last argument: process it, then fall out of the loop and exit 0 *)
    rewrite (skipn_nth av i [] ltac:(lia)).
    cbn [grep_bufs flat_map].
    replace (skipn (S i) av) with (@nil (list byte))
      by (symmetry; apply skipn_all2; lia).
    cbn [flat_map].
    apply target_arg; try assumption; try lia.
    intros regs' H8' H9' H18' H19' H22' H2'.
    pose proof u_aargcN as HuA.
    pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
    (* 0x1001274 .. 0x100127c: bump the index, leave the loop
       (S i = argc) and set the exit code to 0. *)
    sym_block target_segs 3%nat [false] (@nil expr)
      [((22 : reg), EVar 32); ((9 : reg), EVar 33)]
      [nat_to_word i; aargcN] (@nil word) RE HRE.
    { (* bne s6,s1 falls through: S i = argc *) rewrite u_ntw by lia. sym_br. }
    { exact H22'. }
    { exact H9'. }
    apply target_epilogue.
    + sym_regs HRE. exact H2'.
    + sym_regs HRE. reflexivity.
    + u_norm; lia.
  - (* process argv[i], loop back *)
    rewrite (skipn_nth av i [] ltac:(lia)).
    cbn [grep_bufs flat_map].
    change (flat_map (arg_bufs (nth 1 av [])) (skipn (S i) av))
      with (grep_bufs (nth 1 av []) (skipn (S i) av)).
    apply target_arg; try assumption; try lia.
    intros regs' H8' H9' H18' H19' H22' H2'.
    pose proof u_aargcN as HuA.
    (* 0x1001274 .. 0x1001278: bump the index and branch back to the
       loop head (S i < argc). *)
    sym_block target_segs 2%nat [true] (@nil expr)
      [((22 : reg), EVar 32); ((9 : reg), EVar 33)]
      [nat_to_word i; aargcN] (@nil word) RE HRE.
    { (* bne s6,s1 taken: S i < argc *) rewrite u_ntw by lia. sym_br. }
    { exact H22'. }
    { exact H9'. }
    apply (IH (S i)); try lia.
    + sym_regs HRE. exact H8'.
    + sym_regs HRE. reflexivity.
    + sym_regs HRE. exact H18'.
    + sym_regs HRE. exact H19'.
    + sym_regs HRE. apply bv_eq; rewrite ?u_ntw by lia; u_norm; lia.
    + sym_regs HRE. exact H2'.
Qed.

(** Program entry, argc >= 2. *)
(** The two [SCReadBase] obligations the entry block raises: argc at
    [asp], and the [pat] pointer argv[1] eight bytes further up.  Both
    are reads of the INITIAL stack image ([SCReadBase] is stated against
    the base memory, so the frame overlay never has to be peeled). *)
Ltac t_read_argc :=
  eexists; split;
  [ match goal with |- rdn _ _ ?a _ = _ =>
      replace a with asp by (apply bv_eq; u_norm; lia) end;
    rewrite rdn_wrap_stack_above by lia;
    apply read_argc; exact target_bsb_nw
  | apply bytes_le_n_to_le_8 ].

Ltac t_read_ptr1 :=
  eexists; split;
  [ match goal with |- rdn _ _ ?a _ = _ =>
      replace a with (asp + nat_to_word (8 + 8 * 1))
        by (rewrite word_add_nat; apply bv_eq; u_norm; lia) end;
    rewrite rdn_wrap_stack_above by (rewrite word_add_nat; u_norm; lia);
    apply read_argv_ptr_k; [lia | exact target_bsb_nw]
  | apply bytes_le_n_to_le_8 ].

(** Program entry, argc >= 2.  The run's segment list is the image's
    followed by the vDSO pair; the derivation below is the image's own,
    carried over whole. *)
Lemma target_wexit_ge2 : (2 <= length av)%nat ->
  wexit1 (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) 0x100115c target_phdrs
       asp amb arnd inp)
    (grep_bufs (nth 1 av []) (skipn 2 av)) (Z_to_bv 64 0).
Proof.
  intros H2le. apply to_wallexit_run.
  pose proof (valid_argv_len av Hva) as Hargc.
  pose proof u_aargcN as HuA.
  pose proof (target_ptr_bounds 1 ltac:(lia)) as [Hgep Hltp].
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  rewrite init_mkst. norm_pc.
  (* 0x100115c .. 0x10011cc: the Zig entry stub and [run]'s prologue --
     two frames, ten callee-save stores, argc and the [pat] pointer --
     in ONE block, stopping at the loop-entry test 0x10011d0.  The
     callee-saved registers are pinned to 0 so the frame stores land in
     [afmem]'s spelling. *)
  sym_block target_segs 25%nat [true] [EVar 33; EVar 34]
    [((2 : reg), EVar 32); ((1 : reg), ELit 0); ((8 : reg), ELit 0);
     ((9 : reg), ELit 0); ((18 : reg), ELit 0); ((19 : reg), ELit 0);
     ((20 : reg), ELit 0); ((21 : reg), ELit 0); ((22 : reg), ELit 0)]
    [asp] [aargcN; cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1] RE HRE.
  all: try solve [ solve_store_ok ].
  { (* ld s2,8(s0): the [pat] pointer argv[1] *) t_read_ptr1. }
  { (* bltu a1,a0 taken: argc >= 2 *) sym_br. }
  { (* ld a0,0(s0): argc *) t_read_argc. }
  (* the block's exit memory IS [afmem] *)
  match goal with
  | |- to_wexit _ (mkst _ _ ?m _) _ _ =>
    replace m with afmem by (unfold afmem, awmem; reflexivity)
  | |- wexit1 _ (mkst _ _ ?m _) _ _ =>
    replace m with afmem by (unfold afmem, awmem; reflexivity) end.
  destruct (Nat.eq_dec (length av) 2) as [Hav2 | Hav3].
  - (* argc = 2: no args to process, straight to exit 0 *)
    rewrite (skipn_all2 av) by lia. cbn [grep_bufs flat_map].
    chain_step;
      [ reflexivity
      | eapply step_beq_tk;
        [ exact TF_10011d0 | reflexivity | exact TD_10011d0
        | sym_regs HRE; rewrite c_eq_small; unfold bv_eqb; apply Z.eqb_eq;
          u_norm; lia ]
      | norm_pc ].
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 0);
        [ exact TF_100127c | reflexivity | exact TD_100127c | reflexivity
        | getr_resolve; apply v_addi_0 ]
      | norm_pc ].
    apply target_epilogue.
    + sym_regs HRE. reflexivity.
    + apply regupd_same.
    + u_norm; lia.
  - (* argc >= 3: the loop runs from i = 2 *)
    chain_step;
      [ reflexivity
      | eapply step_beq_ft;
        [ exact TF_10011d0 | reflexivity | exact TD_10011d0
        | sym_regs HRE; rewrite c_eq_small; unfold bv_eqb; apply Z.eqb_neq;
          u_norm; lia ]
      | norm_pc ].
    apply (target_loop (length av - 3) 2); try assumption; try lia.
    + sym_regs HRE. reflexivity.
    + sym_regs HRE. reflexivity.
    + sym_regs HRE. reflexivity.
    + sym_regs HRE. bveq.
    + sym_regs HRE. bveq.
    + sym_regs HRE. reflexivity.
Qed.

(** Program entry, argc < 2: exit 2, no output. *)
Lemma target_wexit_lt2 : (length av < 2)%nat ->
  wexit1 (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) 0x100115c target_phdrs
       asp amb arnd inp)
    [] (Z_to_bv 64 2).
Proof.
  intros Hlt2. apply to_wallexit_run.
  pose proof (valid_argv_len av Hva) as Hargc.
  pose proof u_aargcN as HuA.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  rewrite init_mkst. norm_pc.
  (* 0x100115c .. 0x10011b8: same entry stub and prologue, but the
     [bltu a1,a0] falls through (argc <= 1), so [run] sets its exit
     code to 2 and jumps straight to the epilogue at 0x1001280. *)
  sym_block target_segs 22%nat [false] [EVar 33]
    [((2 : reg), EVar 32); ((1 : reg), ELit 0); ((8 : reg), ELit 0);
     ((9 : reg), ELit 0); ((18 : reg), ELit 0); ((19 : reg), ELit 0);
     ((20 : reg), ELit 0); ((21 : reg), ELit 0); ((22 : reg), ELit 0)]
    [asp] [aargcN] RE HRE.
  all: try solve [ solve_store_ok ].
  { (* bltu a1,a0 falls through: argc <= 1 *) sym_br. }
  { (* ld a0,0(s0): argc *) t_read_argc. }
  match goal with
  | |- to_wexit _ (mkst _ _ ?m _) _ _ =>
    replace m with afmem by (unfold afmem, awmem; reflexivity)
  | |- wexit1 _ (mkst _ _ ?m _) _ _ =>
    replace m with afmem by (unfold afmem, awmem; reflexivity) end.
  apply target_epilogue.
  - sym_regs HRE. reflexivity.
  - sym_regs HRE. reflexivity.
  - u_norm; lia.
Qed.

End TargetProof.
