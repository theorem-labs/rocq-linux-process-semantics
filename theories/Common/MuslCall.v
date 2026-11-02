(** * Common.MuslCall — ADDRESS-PARAMETRIC summaries of musl's [write]
      wrapper and its [__syscall_cp] / [__syscall_ret] tail.

    PROTOTYPE / EXPLORATION, built on [Common/Hoare.v].

    Every example re-proves this code inline, at its own addresses:
    ~90 lines of [modprint_ns_source.v], and again in [cat1024_ns],
    [conditional_bug_ns], [grep_args_ns], [tail1_ns], [oob_read_bug_ns],
    [brk_rev_ns], [mmap_upper_ns], [alloc_join_ns].  The BYTES are
    identical in all of them — the soft-float musl build emits the same
    object, and the whole [write]/[__syscall_cp]/[__syscall_ret] blob is
    position-independent (every internal transfer is pc-relative).  Only
    the load address differs.

    So the summaries below are proved ONCE, in a section over

      - [segs]: any segment image, and
      - [B]:    the address the blob is loaded at,

    with the blob's FETCH facts as hypotheses.  The DECODE facts are
    statements about instruction words, not about an image, so they are
    proved here rather than assumed.  A per-binary instantiation supplies
    16 [SF_*] lemmas from its generated [*_code.v] and nothing else; see
    [theories/Examples/modprint_ns/modprint_ns_hoare.v].

    Blob layout, relative to [B] (musl-gcc -Os, RV64 soft-float):

      +0x00  write:          addi sp,sp,-16
      +0x04                  mv a3,a2
      +0x08                  li a6,0
      +0x0c                  mv a2,a1
      +0x10                  li a5,0
      +0x14                  mv a1,a0
      +0x18                  li a4,0
      +0x1c                  li a0,64          ; SYS_write
      +0x20                  sd ra,8(sp)
      +0x24                  jal ra,+0x6c      ; -> __syscall_cp
      +0x28                  ld ra,8(sp)
      +0x2c                  addi sp,sp,16
      +0x30                  j +4              ; -> __syscall_ret
      +0x34  __syscall_ret:  lui a5,0xfffff
      +0x38                  bltu a5,a0,+8     ; errno branch (not taken)
      +0x3c                  ret
      ...    (+0x40..+0x68: the errno tail, unreachable on success)
      +0x6c  __syscall_cp_c: mv a7,a0 / mv a0,a1 / mv a1,a2 / mv a2,a3
      +0x7c                  mv a3,a4 / mv a4,a5 / mv a5,a6
      +0x88                  ecall
      +0x8c                  ret
      +0x90  __syscall_cp:   j -0x24           ; -> __syscall_cp_c

    Two summaries, because a [triple] cannot cross the [ecall] (the
    syscall is not an [msteps] step):

      [musl_write_enter] : [B+0x00] -> [B+0x88], the pc at which the
                           caller applies [CatSim]'s [tw_write_ret];
      [musl_write_leave] : [B+0x8c] -> the caller's return address, the
                           post-syscall path back through
                           [__syscall_ret]'s not-taken errno branch.

    [musl_write_wexit] glues them around the syscall and hands the whole
    call to a [to_wexit] continuation — that is the form a per-binary
    proof actually applies. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.Common Require Import
  ExitSim PropExec CatExec CatSim SeqExec StepTac Hoare WallSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* ========================================================================= *)
(* Tactics for an ADDRESS-PARAMETRIC chain                                    *)
(* ========================================================================= *)

(** [StepTac]'s [norm_pc] must NOT be used here: it calls [word_lit],
    which [vm_compute]s the pc — and the pc of an address-parametric
    summary contains the free variable [B].  ([vm_compute] on an open
    [bv] term allocates until the process dies, with no Rocq error.)

    The replacement keeps the pc in the [at_ B d] normal form of
    [Hoare.v]: [at_addi]/[at_btgt] absorb the step lemmas' [v_addi pc 4]
    and [btgt pc imm], and [at_fold] folds the resulting literal offset
    sum.  Nothing is ever computed on a term mentioning [B]. *)
End WithFP1.
Ltac at_fold :=
  repeat match goal with
  | |- context [at_ ?b (?x + ?y)] =>
      let z := eval cbv in (x + y)%Z in change (x + y)%Z with z
  end.

Section WithFP2.
Context {fx : FPState}.

(** [SeqExec.getr_resolve] ends with [rewrite ?getr_nz], which turns a
    LEFTOVER [getr regs r] on the section's opaque register file into
    [reg_get regs r] — and then the summary's [getr]-shaped hypotheses no
    longer apply.  [gres] is the same peeling without that last step. *)
End WithFP2.
Ltac gres :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ];
  rewrite ?getr_zero.

Ltac apc := reduce_bv_eqb_ifs; imm_norm; rewrite ?at_addi, ?at_btgt; at_fold.

Section WithFP4.
Context {fx : FPState}.

(** One straight-line step of the chain, with the writeback value named. *)
End WithFP4.
Ltac hstepv F D vv tac :=
  eapply mst_step;
  [ reflexivity
  | eapply step_addi_at with (v := vv);
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | apc ].

Section WithFP5.
Context {fx : FPState}.

(* ========================================================================= *)
(* Instruction words and their decodings                                      *)
(* ========================================================================= *)

(** The blob's 26 relevant words.  These are IMAGE-INDEPENDENT: a decode
    fact is a statement about a 32-bit word, so it belongs here and not in
    a per-binary [*_code.v]. *)

Definition Wsp16m : bv 32 := 4278255891.   (* addi sp,sp,-16    *)
Definition Wmv_a3a2 : bv 32 := 394899.
Definition Wli_a6_0 : bv 32 := 2067.
Definition Wmv_a2a1 : bv 32 := 362003.
Definition Wli_a5_0 : bv 32 := 1939.
Definition Wmv_a1a0 : bv 32 := 329107.
Definition Wli_a4_0 : bv 32 := 1811.
Definition Wli_a0_64 : bv 32 := 67110163.
Definition Wsd_ra8 : bv 32 := 1127459.
Definition Wjal_cp : bv 32 := 113246447.   (* jal ra,+108       *)
Definition Wld_ra8 : bv 32 := 8466563.
Definition Wsp16p : bv 32 := 16843027.     (* addi sp,sp,16     *)
Definition Wj4 : bv 32 := 4194415.         (* j +4              *)
Definition Wlui_a5 : bv 32 := 4294965175.  (* lui a5,0xfffff    *)
Definition Wbltu : bv 32 := 11002979.      (* bltu a5,a0,+8     *)
Definition Wret : bv 32 := 32871.          (* jalr x0,0(ra)     *)
Definition Wmv_a7a0 : bv 32 := 329875.
Definition Wmv_a0a1 : bv 32 := 361747.
Definition Wmv_a1a2 : bv 32 := 394643.
Definition Wmv_a2a3 : bv 32 := 427539.
Definition Wmv_a3a4 : bv 32 := 460435.
Definition Wmv_a4a5 : bv 32 := 493331.
Definition Wmv_a5a6 : bv 32 := 526227.
Definition Wecall : bv 32 := 115.
Definition Wj_cpc : bv 32 := 4259311727.   (* j -36             *)

Lemma D_sp16m : decode_any Wsp16m = Some (OpImm ALU_ADD 2 2 4080, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_mv_a3a2 : decode_any Wmv_a3a2 = Some (OpImm ALU_ADD 13 12 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_li_a6_0 : decode_any Wli_a6_0 = Some (OpImm ALU_ADD 16 0 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_mv_a2a1 : decode_any Wmv_a2a1 = Some (OpImm ALU_ADD 12 11 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_li_a5_0 : decode_any Wli_a5_0 = Some (OpImm ALU_ADD 15 0 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_mv_a1a0 : decode_any Wmv_a1a0 = Some (OpImm ALU_ADD 11 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_li_a4_0 : decode_any Wli_a4_0 = Some (OpImm ALU_ADD 14 0 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_li_a0_64 : decode_any Wli_a0_64 = Some (OpImm ALU_ADD 10 0 64, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_sd_ra8 : decode_any Wsd_ra8 = Some (Store SZ8 2 1 8, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_jal_cp : decode_any Wjal_cp = Some (Jal 1 108, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_ld_ra8 : decode_any Wld_ra8 = Some (Load SZ8 true 1 2 8, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_sp16p : decode_any Wsp16p = Some (OpImm ALU_ADD 2 2 16, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_j4 : decode_any Wj4 = Some (Jal 0 4, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_lui_a5 : decode_any Wlui_a5 = Some (Lui 15 1048575, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_bltu : decode_any Wbltu = Some (Branch BC_LTU 15 10 8, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_ret : decode_any Wret = Some (Jalr 0 1 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_mv_a7a0 : decode_any Wmv_a7a0 = Some (OpImm ALU_ADD 17 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_mv_a0a1 : decode_any Wmv_a0a1 = Some (OpImm ALU_ADD 10 11 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_mv_a1a2 : decode_any Wmv_a1a2 = Some (OpImm ALU_ADD 11 12 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_mv_a2a3 : decode_any Wmv_a2a3 = Some (OpImm ALU_ADD 12 13 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_mv_a3a4 : decode_any Wmv_a3a4 = Some (OpImm ALU_ADD 13 14 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_mv_a4a5 : decode_any Wmv_a4a5 = Some (OpImm ALU_ADD 14 15 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_mv_a5a6 : decode_any Wmv_a5a6 = Some (OpImm ALU_ADD 15 16 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma D_j_cpc : decode_any Wj_cpc = Some (Jal 0 2097116, 4%Z). Proof. vm_refl_bv. Qed.

Lemma E_ecall : is_ecall Wecall = true. Proof. reflexivity. Qed.

(* ========================================================================= *)
(* The section: any image, any load address                                   *)
(* ========================================================================= *)

Section MuslWrite.

Variable segs : list Segment.
Variable B : word.

(** The 25 fetch facts.  This is the ENTIRE per-binary interface: an
    instantiation discharges each with one [SF_*] from its generated
    [*_code.v]. *)
Hypothesis F00 : fetch_word segs (at_ B 0x00) = Some Wsp16m.
Hypothesis F04 : fetch_word segs (at_ B 0x04) = Some Wmv_a3a2.
Hypothesis F08 : fetch_word segs (at_ B 0x08) = Some Wli_a6_0.
Hypothesis F0c : fetch_word segs (at_ B 0x0c) = Some Wmv_a2a1.
Hypothesis F10 : fetch_word segs (at_ B 0x10) = Some Wli_a5_0.
Hypothesis F14 : fetch_word segs (at_ B 0x14) = Some Wmv_a1a0.
Hypothesis F18 : fetch_word segs (at_ B 0x18) = Some Wli_a4_0.
Hypothesis F1c : fetch_word segs (at_ B 0x1c) = Some Wli_a0_64.
Hypothesis F20 : fetch_word segs (at_ B 0x20) = Some Wsd_ra8.
Hypothesis F24 : fetch_word segs (at_ B 0x24) = Some Wjal_cp.
Hypothesis F28 : fetch_word segs (at_ B 0x28) = Some Wld_ra8.
Hypothesis F2c : fetch_word segs (at_ B 0x2c) = Some Wsp16p.
Hypothesis F30 : fetch_word segs (at_ B 0x30) = Some Wj4.
Hypothesis F34 : fetch_word segs (at_ B 0x34) = Some Wlui_a5.
Hypothesis F38 : fetch_word segs (at_ B 0x38) = Some Wbltu.
Hypothesis F3c : fetch_word segs (at_ B 0x3c) = Some Wret.
Hypothesis F6c : fetch_word segs (at_ B 0x6c) = Some Wmv_a7a0.
Hypothesis F70 : fetch_word segs (at_ B 0x70) = Some Wmv_a0a1.
Hypothesis F74 : fetch_word segs (at_ B 0x74) = Some Wmv_a1a2.
Hypothesis F78 : fetch_word segs (at_ B 0x78) = Some Wmv_a2a3.
Hypothesis F7c : fetch_word segs (at_ B 0x7c) = Some Wmv_a3a4.
Hypothesis F80 : fetch_word segs (at_ B 0x80) = Some Wmv_a4a5.
Hypothesis F84 : fetch_word segs (at_ B 0x84) = Some Wmv_a5a6.
Hypothesis F88 : fetch_word segs (at_ B 0x88) = Some Wecall.
Hypothesis F8c : fetch_word segs (at_ B 0x8c) = Some Wret.
Hypothesis F90 : fetch_word segs (at_ B 0x90) = Some Wj_cpc.

(** The blob's clobber set: [ra], [sp] and the argument registers.  Every
    callee-saved register is outside it, so a caller keeps its [s*] and
    its frame pointer across the call for free (see [Hoare.triple_frame]
    and [Hoare.frameable_reg]). *)
Definition musl_clob : regset :=
  fun r => r = 1 \/ r = 2 \/ r = 10 \/ r = 11 \/ r = 12 \/ r = 13
           \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17.

Ltac in_clob :=
  unfold musl_clob;
  repeat first [ left; reflexivity | right ]; reflexivity.

(** Its write set: the one stack slot the wrapper spills [ra] into. *)
Definition musl_wset (sp0 : word) : memset :=
  fun x => exists i, (0 <= i < 8)%Z /\ x = at_ sp0 (-8 + i).

(* ------------------------------------------------------------------ *)
(* Summary 1: entry -> the ecall                                        *)
(* ------------------------------------------------------------------ *)

Lemma musl_write_enter :
  forall (k sp0 fd buf len : word) (mem0 : word -> option byte),
  triple segs musl_clob (musl_wset sp0)
    (fun regs mem _ =>
       mem = mem0
       /\ getr regs 1 = k /\ getr regs 2 = sp0
       /\ getr regs 10 = fd /\ getr regs 11 = buf /\ getr regs 12 = len
       /\ RiscvSemantics.store_ok segs mem0 (at_ sp0 (-8)) 8%nat = true)
    (at_ B 0x00) (at_ B 0x88)
    (fun regs mem _ =>
       mem = wbytes mem0 (at_ sp0 (-8)) (word_to_le_bytes 8 k)
       /\ getr regs 1 = at_ B 0x28 /\ getr regs 2 = at_ sp0 (-16)
       /\ getr regs 10 = fd /\ getr regs 11 = buf /\ getr regs 12 = len
       /\ getr regs 17 = Z_to_bv 64 64).
Proof.
  intros k sp0 fd buf len mem0.
  apply triple_intro.
  intros regs mem rom (Hmem & Hra & Hsp & H10 & H11 & H12 & Hok). subst mem.
  eexists; eexists; split; [|split; [|split]].
  - (* the instruction chain *)
    (* +0x00 addi sp,sp,-16 *)
    hstepv F00 D_sp16m (at_ sp0 (-16))
      ltac:(gres; rewrite Hsp; imm_norm; reflexivity).
    (* +0x04 mv a3,a2 *)
    hstepv F04 D_mv_a3a2 len
      ltac:(gres; rewrite H12; rewrite v_addi_0; reflexivity).
    (* +0x08 li a6,0 *)
    hstepv F08 D_li_a6_0 (Z_to_bv 64 0)
      ltac:(gres; rewrite v_addi_0; reflexivity).
    (* +0x0c mv a2,a1 *)
    hstepv F0c D_mv_a2a1 buf
      ltac:(gres; rewrite H11; rewrite v_addi_0; reflexivity).
    (* +0x10 li a5,0 *)
    hstepv F10 D_li_a5_0 (Z_to_bv 64 0)
      ltac:(gres; rewrite v_addi_0; reflexivity).
    (* +0x14 mv a1,a0 *)
    hstepv F14 D_mv_a1a0 fd
      ltac:(gres; rewrite H10; rewrite v_addi_0; reflexivity).
    (* +0x18 li a4,0 *)
    hstepv F18 D_li_a4_0 (Z_to_bv 64 0)
      ltac:(gres; rewrite v_addi_0; reflexivity).
    (* +0x1c li a0,64 *)
    hstepv F1c D_li_a0_64 (Z_to_bv 64 64)
      ltac:(gres; exact v_addi_0_64).
    (* +0x20 sd ra,8(sp) *)
    eapply mst_step;
      [ reflexivity
      | eapply step_sd_at with (a := at_ sp0 (-8)) (v := k);
        [ exact F20 | reflexivity | exact D_sd_ra8
        | gres; imm_norm; rewrite at_addi; reflexivity
        | gres; exact Hra
        | exact Hok ]
      | apc ].
    (* +0x24 jal ra,__syscall_cp *)
    eapply mst_step;
      [ reflexivity
      | eapply step_jal_link; [ exact F24 | reflexivity | exact D_jal_cp ]
      | apc ].
    (* +0x90 j __syscall_cp_c *)
    eapply mst_step;
      [ reflexivity
      | exact (step_jal_x0 _ _ _ _ _ _ _ F90 eq_refl D_j_cpc)
      | apc ].
    (* +0x6c..+0x84: the raw-syscall register shuffle *)
    hstepv F6c D_mv_a7a0 (Z_to_bv 64 64)
      ltac:(gres; rewrite v_addi_0; reflexivity).
    hstepv F70 D_mv_a0a1 fd
      ltac:(gres; rewrite v_addi_0; reflexivity).
    hstepv F74 D_mv_a1a2 buf
      ltac:(gres; rewrite v_addi_0; reflexivity).
    hstepv F78 D_mv_a2a3 len
      ltac:(gres; rewrite v_addi_0; reflexivity).
    hstepv F7c D_mv_a3a4 (Z_to_bv 64 0)
      ltac:(gres; rewrite v_addi_0; reflexivity).
    hstepv F80 D_mv_a4a5 (Z_to_bv 64 0)
      ltac:(gres; rewrite v_addi_0; reflexivity).
    hstepv F84 D_mv_a5a6 (Z_to_bv 64 0)
      ltac:(gres; rewrite v_addi_0; reflexivity).
    apply mst_refl.
  - (* the postcondition *)
    split; [reflexivity|].
    repeat split; gres; reflexivity.
  - (* register footprint *)
    repeat (apply regs_agree_upd; [in_clob|]). apply regs_agree_refl.
  - (* memory footprint *)
    apply mem_agree_wbytes; [|apply mem_agree_refl].
    intros i Hi. unfold musl_wset.
    rewrite length_N_to_le_bytes in Hi.
    exists i. split; [lia|]. exact (at_at sp0 (-8) i).
Qed.

(* ------------------------------------------------------------------ *)
(* Summary 2: the post-syscall return path                              *)
(* ------------------------------------------------------------------ *)

(** [__syscall_ret]'s errno window: a return value at or above
    [-4096 mod 2^64] is an errno.  [write] of a fully readable buffer
    never lands there. *)
Definition errno_lo : word := Z_to_bv 64 18446744073709547520.

Lemma not_errno : forall rv : word,
  (bv_unsigned rv <= 18446744073709547520)%Z -> c_ltu errno_lo rv = false.
Proof.
  intros rv H. unfold c_ltu, bv_ltu, errno_lo.
  apply Z.ltb_ge. rewrite u_Z2bv by lia. lia.
Qed.

Lemma musl_write_leave :
  forall (k sp0 rv : word) (mem1 : word -> option byte),
  ret_ok k -> ret_ok (at_ B 0x28) ->
  triple segs musl_clob (musl_wset sp0)
    (fun regs mem _ =>
       mem = mem1
       /\ getr regs 1 = at_ B 0x28 /\ getr regs 2 = at_ sp0 (-16)
       /\ getr regs 10 = rv
       /\ rdn segs mem1 (at_ sp0 (-8)) 8%nat = Some (word_to_le_bytes 8 k)
       /\ c_ltu errno_lo rv = false)
    (at_ B 0x8c) k
    (fun regs mem _ =>
       mem = mem1 /\ getr regs 1 = k /\ getr regs 2 = sp0 /\ getr regs 10 = rv).
Proof.
  intros k sp0 rv mem1 Hk Hr28.
  unfold ret_ok in Hk, Hr28.
  apply triple_intro.
  intros regs mem rom (Hmem & H1 & H2 & H10 & Hrd & Hlt). subst mem.
  eexists; eexists; split; [|split; [|split]].
  - (* +0x8c ret -> +0x28 *)
    eapply mst_step;
      [ reflexivity
      | eapply step_jalr_x0 with (tgt := at_ B 0x28);
        [ exact F8c | reflexivity | exact D_ret | gres; exact H1 ]
      | apc; rewrite Hr28 ].
    (* +0x28 ld ra,8(sp) *)
    eapply mst_step;
      [ reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 k) (v := k);
        [ exact F28 | reflexivity | exact D_ld_ra8
        | gres; rewrite H2; imm_norm; rewrite at_addi; exact Hrd
        | exact (bytes_le_to_Z_8 k) ]
      | apc ].
    (* +0x2c addi sp,sp,16 *)
    hstepv F2c D_sp16p sp0
      ltac:(gres; rewrite H2; imm_norm; rewrite at_addi; exact (at_0 sp0)).
    (* +0x30 j __syscall_ret *)
    eapply mst_step;
      [ reflexivity
      | exact (step_jal_x0 _ _ _ _ _ _ _ F30 eq_refl D_j4)
      | apc ].
    (* +0x34 lui a5,0xfffff *)
    eapply mst_step;
      [ reflexivity
      | eapply step_lui_at with (v := errno_lo);
        [ exact F34 | reflexivity | exact D_lui_a5 | reflexivity
        | unfold errno_lo; bveq ]
      | apc ].
    (* +0x38 bltu a5,a0 NOT taken *)
    eapply mst_step;
      [ reflexivity
      | eapply step_bltu_ft;
        [ exact F38 | reflexivity | exact D_bltu
        | gres; rewrite H10; exact Hlt ]
      | apc ].
    (* +0x3c ret -> the caller *)
    eapply mst_step;
      [ reflexivity
      | eapply step_jalr_x0 with (tgt := k);
        [ exact F3c | reflexivity | exact D_ret | gres; reflexivity ]
      | apc; rewrite Hk ].
    apply mst_refl.
  - split; [reflexivity|]. repeat split; gres; first [ reflexivity | assumption ].
  - repeat (apply regs_agree_upd; [in_clob|]). apply regs_agree_refl.
  - apply mem_agree_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* The whole call, syscall included                                     *)
(* ------------------------------------------------------------------ *)

(** [write(1, buf, len)] from entry to return, handing the [ecall] to
    [SeqExec]'s [tw_write_ret] and the return to the caller's
    continuation.  The environment may deliver any nonempty prefix of
    the buffer, so the continuation is the delivered-length family: a0
    holds [len_word (firstn n out)] for the chosen [n] (never in the
    errno window, so [__syscall_ret]'s branch is not taken for ANY
    delivery).  THIS is the lemma a per-binary proof applies: one
    [eapply] replaces the ~90 lines each example spends walking this
    code. *)
Lemma musl_write_wexit :
  forall (regs : bvmap 5 word) (mem rom : word -> option byte)
         (k sp0 buf len : word) (out : list byte)
         (bufs : list (list byte)) (code : word),
  rom = seg_rom segs ->
  ret_ok k -> ret_ok (at_ B 0x28) ->
  getr regs 1 = k -> getr regs 2 = sp0 ->
  getr regs 10 = Z_to_bv 64 1 -> getr regs 11 = buf -> getr regs 12 = len ->
  RiscvSemantics.store_ok segs mem (at_ sp0 (-8)) 8%nat = true ->
  (bv_unsigned (at_ sp0 (-8)) + 8 <= 2^64)%Z ->
  (bv_unsigned len <= 18446744073709547520)%Z ->
  rdn segs (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k))
      buf (word_to_nat len) = Some out ->
  (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
  access_okb buf (bv_unsigned len) = true ->
  (1 <= length out)%nat ->
  (forall regs' n, (1 <= n)%nat -> (n <= length out)%nat ->
     getr regs' 1 = k -> getr regs' 2 = sp0 ->
     getr regs' 10 = len_word (firstn n out) ->
     to_wexit segs
       (mkst regs' k (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k)) rom)
       bufs code) ->
  to_wexit segs (mkst regs (at_ B 0x00) mem rom) (out :: bufs) code.
Proof.
  intros regs mem rom k sp0 buf len out bufs code
         Hrom Hk Hr28 H1 H2 H10 H11 H12 Hok Hnw Hlen Hread Hacc Hnb Hcont.
  set (mem1 := wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k)).
  pose proof (rdn_length _ _ _ _ _ Hread) as Hlout.
  pose proof (u64_range len) as Hlr.
  assert (HoutZ : Z.of_nat (length out) = bv_unsigned len).
  { rewrite Hlout. unfold word_to_nat. rewrite Z2Nat.id by lia. reflexivity. }
  (* entry -> the ecall *)
  eapply triple_wexit;
    [ apply (musl_write_enter k sp0 (Z_to_bv 64 1) buf len mem)
    | repeat split; eassumption
    | ].
  intros regs1 mem1' (Hm1 & Q1 & Q2 & Q10 & Q11 & Q12 & Q17). subst mem1'.
  (* the ecall itself *)
  eapply tw_step; [ reflexivity | apply (step_ecall _ _ _ _ _ _ F88 eq_refl) | ].
  apply tw_write_ret.
  - rewrite Q17. vm_compute. reflexivity.
  - rewrite <- getr_nz by reg_neq_tac. exact Q10.
  - rewrite (ms_read_bytes_rdn segs) by (cbn [mkst]; exact Hrom).
    cbn [ms_mem ms_regs].
    rewrite <- !getr_nz by reg_neq_tac. rewrite Q11, Q12. exact Hread.
  - rewrite <- !getr_nz by reg_neq_tac. rewrite Q11, Q12. exact Hacc.
  - exact Hnb.
  - (* back from the kernel: __syscall_ret, then the caller *)
    intros n Hn1 Hn2.
    assert (Hru : bv_unsigned (len_word (firstn n out)) = Z.of_nat n).
    { rewrite (len_word_unsigned (firstn n out));
        rewrite length_firstn; unfold two_pow_64; lia. }
    rewrite at_addi. cbn [Z.add].
    eapply triple_wexit;
      [ apply (musl_write_leave k sp0 (len_word (firstn n out)) mem1 Hk Hr28)
      | | ].
    + repeat split.
      * rewrite getr_other by reg_neq_tac. exact Q1.
      * rewrite getr_other by reg_neq_tac. exact Q2.
      * rewrite getr_same by reg_neq_tac. reflexivity.
      * unfold mem1. apply rdn_wbytes_hit8. exact Hnw.
      * apply not_errno. rewrite Hru. lia.
    + intros regs2 mem2 (Hm2 & R1 & R2 & R10). subst mem2.
      apply (Hcont regs2 n); assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* The whole call, for a PUT-LOOP caller                                *)
(* ------------------------------------------------------------------ *)

(** [write(1, buf, len)] from entry to return, handing the [ecall] to
    [WallSim]'s write node and — per delivered length [n] — the return
    path back through [__syscall_ret] to the CALLER'S retry-loop
    obligation: a [to_wall_tail] of the remainder [skipn n out] down to
    an arbitrary continuation predicate [k].  This is the summary a
    per-binary proof applies when the caller wraps the call in a
    put-style retry loop (so its trace contribution is ALL of [out]).

    SHARES 27 LINES WITH [musl_write_wexit] ABOVE — its whole 13-line
    hypothesis list, and four blocks of proof body.

    It is not folded because the two lemmas' conclusions live in
    different inductive families with no bridge between them —
    [SeqExec.to_wexit] (node intro [tw_write_ret]) and
    [WallSim.to_wall_tail] (node intro [twl_write_rec], closure
    [msteps_to_wall_tail]).  [WallSim.to_wallexit] bridges [to_wall] to
    [to_wexit] only in the buffer-LIST form, not the tail form, so
    neither lemma is an instance of the other; generalizing over the
    family needs three interface hypotheses (msteps closure, ecall step,
    node intro) whose statements come to about what the shared body
    costs.  The hypothesis lists are identical precisely BECAUSE the two
    calls are the same code — the difference is only what the caller
    does with the return.

    What the available folds are actually worth, measured rather than
    guessed: an arithmetic lemma over the two [len_word (firstn n out)]
    preambles nets about -1; an [Ltac] for the write-node side
    conditions and another for the [musl_write_leave] ones net -3 each,
    and both would resolve caller-local hypothesis names ([Q1], [Q10],
    [Hrom], [Hru], ...) dynamically, which couples every future call
    site to that naming.  The only fold that pays properly is turning
    the shared hypothesis list into one [Definition], about -8, and it
    changes both lemmas' statements and moves two call sites
    ([conditional_bug_ns_hoare.v:96], [modprint_ns_hoare.v:103]).  That
    is a follow-up on main, not an append to this branch.

    A cleaner win exists and is worth taking first: this lemma's
    continuation hypothesis carries [regs_agree musl_clob regs regs'],
    its only consumer ([conditional_bug_ns_hoare.v:103]) binds it and
    never uses it, and the proof pays three lines of
    [regs_agree_trans]/[regs_agree_upd] to supply it.  Dropping it
    removes about four lines here and one unused binder there, with no
    other consumer affected. *)
Lemma musl_write_wall :
  forall (k : machine_state -> Prop)
         (regs : bvmap 5 word) (mem rom : word -> option byte)
         (kra sp0 buf len : word) (out : list byte),
  rom = seg_rom segs ->
  ret_ok kra -> ret_ok (at_ B 0x28) ->
  getr regs 1 = kra -> getr regs 2 = sp0 ->
  getr regs 10 = Z_to_bv 64 1 -> getr regs 11 = buf -> getr regs 12 = len ->
  RiscvSemantics.store_ok segs mem (at_ sp0 (-8)) 8%nat = true ->
  (bv_unsigned (at_ sp0 (-8)) + 8 <= 2^64)%Z ->
  (bv_unsigned len <= 18446744073709547520)%Z ->
  rdn segs (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra))
      buf (word_to_nat len) = Some out ->
  access_okb buf (bv_unsigned len) = true ->
  (1 <= length out)%nat ->
  (forall regs' n, (1 <= n)%nat -> (n <= length out)%nat ->
     regs_agree musl_clob regs regs' ->
     getr regs' 1 = kra -> getr regs' 2 = sp0 ->
     getr regs' 10 = len_word (firstn n out) ->
     to_wall_tail segs (Z_to_bv 64 1)
       (mkst regs' kra (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra)) rom)
       (skipn n out) k) ->
  to_wall_tail segs (Z_to_bv 64 1) (mkst regs (at_ B 0x00) mem rom) out k.
Proof.
  intros k regs mem rom kra sp0 buf len out
         Hrom Hk Hr28 H1 H2 H10 H11 H12 Hok Hnw Hlen Hread Hacc Hnb Hcont.
  set (mem1 := wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra)) in *.
  pose proof (rdn_length _ _ _ _ _ Hread) as Hlout.
  pose proof (u64_range len) as Hlr.
  assert (HoutZ : Z.of_nat (length out) = bv_unsigned len).
  { rewrite Hlout. unfold word_to_nat. rewrite Z2Nat.id by lia. reflexivity. }
  (* entry -> the ecall *)
  destruct (musl_write_enter kra sp0 (Z_to_bv 64 1) buf len mem regs mem rom
              (conj eq_refl (conj H1 (conj H2 (conj H10 (conj H11 (conj H12 Hok)))))))
    as (regs1 & mem1' & Hst1 & (Hm1 & Q1 & Q2 & Q10 & Q11 & Q12 & Q17) & Hag1 & _).
  subst mem1'.
  eapply msteps_to_wall_tail; [exact Hst1|].
  (* the ecall itself *)
  eapply twt_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ F88 eq_refl) |].
  apply twt_more; [exact Hnb|].
  apply (twl_write_rec segs (Z_to_bv 64 1)).
  - rewrite Q17. vm_compute. reflexivity.
  - rewrite <- getr_nz by reg_neq_tac. exact Q10.
  - rewrite (ms_read_bytes_rdn segs) by (cbn [mkst]; exact Hrom).
    cbn [ms_mem ms_regs].
    rewrite <- !getr_nz by reg_neq_tac. rewrite Q11, Q12. exact Hread.
  - rewrite <- !getr_nz by reg_neq_tac. rewrite Q11, Q12. exact Hacc.
  - exact Hnb.
  - (* back from the kernel: __syscall_ret, then the caller's put loop *)
    intros n Hn1 Hn2.
    assert (Hru : bv_unsigned (len_word (firstn n out)) = Z.of_nat n).
    { rewrite (len_word_unsigned (firstn n out));
        rewrite length_firstn; unfold two_pow_64; lia. }
    rewrite at_addi. cbn [Z.add].
    destruct (musl_write_leave kra sp0 (len_word (firstn n out)) mem1 Hk Hr28
                (regupd regs1 10 (len_word (firstn n out))) mem1 rom)
      as (regs2 & mem2 & Hst2 & (Hm2 & R1 & R2 & R10) & Hag2 & _).
    { repeat split.
      - rewrite getr_other by reg_neq_tac. exact Q1.
      - rewrite getr_other by reg_neq_tac. exact Q2.
      - rewrite getr_same by reg_neq_tac. reflexivity.
      - unfold mem1. apply rdn_wbytes_hit8. exact Hnw.
      - apply not_errno. rewrite Hru. lia. }
    subst mem2.
    eapply msteps_to_wall_tail; [exact Hst2|].
    apply (Hcont regs2 n); try assumption.
    eapply regs_agree_trans; [ exact Hag1 | ].
    eapply regs_agree_trans; [ | exact Hag2 ].
    apply regs_agree_upd; [ unfold musl_clob; tauto | apply regs_agree_refl ].
Qed.

(* ------------------------------------------------------------------ *)
(* What a caller keeps across the call                                  *)
(* ------------------------------------------------------------------ *)

(** The frame rule at this summary's footprints, as the caller sees it:
    any callee-saved register and any buffer disjoint from the one
    spilled stack slot survives the whole [write] call — including the
    syscall — with no help from the summary's postcondition.  This is
    what the current per-binary proofs cannot express: they re-derive
    every surviving fact by re-walking the chain. *)
Lemma musl_write_frame :
  forall (sp0 : word) (r : reg) (v a : word) (n : nat) (bs : list byte),
  ~ musl_clob r ->
  (forall i, (0 <= i < Z.of_nat n)%Z ->
     ~ musl_wset sp0 (Z_to_bv 64 (bv_unsigned a + i))) ->
  frameable musl_clob (musl_wset sp0)
    (fun regs mem _ => getr regs r = v /\ rdn segs mem a n = Some bs).
Proof.
  intros sp0 r v a n bs Hr Ha.
  apply frameable_and; [ apply frameable_reg; exact Hr
                       | apply frameable_rdn; exact Ha ].
Qed.

End MuslWrite.
End WithFP5.
