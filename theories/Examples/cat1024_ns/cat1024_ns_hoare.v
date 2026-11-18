(** * cat1024-ns: the SAME musl [write] summary, a THIRD load address —
      and a different behaviour shape.

    PROTOTYPE / EXPLORATION.  PROOF-SIDE FILE.

    The blob [modprint_ns] loads at 0x11098 and [conditional_bug_ns] at
    0x110fc sits at 0x11104 here, so the 26 [SF_*] rebasings below are
    again the whole per-binary interface to [Common/MuslCall.v].

    What is NEW here is the hand-off.  [cat1024_ns] is a streaming
    example: its writes are not [CatSim.to_wexit] but
    [StreamSim.to_wr]/[lh_next], so [MuslCall.musl_write_wexit] — which
    bakes in [CatSim.tw_write_ret] — does not apply.  The two halves of
    the summary do: [musl_write_enter] and [musl_write_leave] are plain
    [triple]s, and [Hoare.triple_msteps] turns each into the [msteps] both
    shape relations consume.  [cat_write_twr] below is that glue, and it
    is the only thing this file proves. *)

(** STATUS: this instantiation is complete and proved, but
    [cat1024_ns_source.v] does not currently call it — with the
    reflective executor's read script the same 26-instruction blob runs
    inside a [sym_block], which is shorter here.  The file is kept
    because it is the second binary the address-parametric summary was
    instantiated at (the evidence that the blob really is byte-identical
    across binaries), and because [cat_write_twr] is the STREAMING
    (StreamSim) hand-off of the summary — [modprint_ns] only exercises
    the [to_wexit] one. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import
  PropExec CatExec CatSim SeqExec WallSim StreamSim StepTac Hoare MuslCall.
From LinuxProcessSemantics.Examples.cat1024_ns Require Import
  cat1024_ns_code cat1024_ns_defs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** Every state here is one the source reaches from process entry, where
    the FP register file is empty and [fcsr] is zero ([PropExec.fx0]). *)
#[local] Instance cat1024_ns_hoare_fx : FPState := fx0.

(** This binary's load address for the blob. *)
Definition CATB : word := 0x11104.

Lemma fetch_at : forall segs (b : word) (d : Z) (a : word) w,
  at_ b d = a -> fetch_word segs a = Some w -> fetch_word segs (at_ b d) = Some w.
Proof. intros segs b d a w Ha Hf. rewrite Ha. exact Hf. Qed.

Ltac fat SF := refine (fetch_at _ _ _ _ _ _ SF); unfold at_, CATB; bveq.

Lemma f00 : fetch_word source_segs (at_ CATB 0x00) = Some Wsp16m. Proof. fat SF_11104. Qed.
Lemma f04 : fetch_word source_segs (at_ CATB 0x04) = Some Wmv_a3a2. Proof. fat SF_11108. Qed.
Lemma f08 : fetch_word source_segs (at_ CATB 0x08) = Some Wli_a6_0. Proof. fat SF_1110c. Qed.
Lemma f0c : fetch_word source_segs (at_ CATB 0x0c) = Some Wmv_a2a1. Proof. fat SF_11110. Qed.
Lemma f10 : fetch_word source_segs (at_ CATB 0x10) = Some Wli_a5_0. Proof. fat SF_11114. Qed.
Lemma f14 : fetch_word source_segs (at_ CATB 0x14) = Some Wmv_a1a0. Proof. fat SF_11118. Qed.
Lemma f18 : fetch_word source_segs (at_ CATB 0x18) = Some Wli_a4_0. Proof. fat SF_1111c. Qed.
Lemma f1c : fetch_word source_segs (at_ CATB 0x1c) = Some Wli_a0_64. Proof. fat SF_11120. Qed.
Lemma f20 : fetch_word source_segs (at_ CATB 0x20) = Some Wsd_ra8. Proof. fat SF_11124. Qed.
Lemma f24 : fetch_word source_segs (at_ CATB 0x24) = Some Wjal_cp. Proof. fat SF_11128. Qed.
Lemma f28 : fetch_word source_segs (at_ CATB 0x28) = Some Wld_ra8. Proof. fat SF_1112c. Qed.
Lemma f2c : fetch_word source_segs (at_ CATB 0x2c) = Some Wsp16p. Proof. fat SF_11130. Qed.
Lemma f30 : fetch_word source_segs (at_ CATB 0x30) = Some Wj4. Proof. fat SF_11134. Qed.
Lemma f34 : fetch_word source_segs (at_ CATB 0x34) = Some Wlui_a5. Proof. fat SF_11138. Qed.
Lemma f38 : fetch_word source_segs (at_ CATB 0x38) = Some Wbltu. Proof. fat SF_1113c. Qed.
Lemma f3c : fetch_word source_segs (at_ CATB 0x3c) = Some Wret. Proof. fat SF_11140. Qed.
Lemma f6c : fetch_word source_segs (at_ CATB 0x6c) = Some Wmv_a7a0. Proof. fat SF_11170. Qed.
Lemma f70 : fetch_word source_segs (at_ CATB 0x70) = Some Wmv_a0a1. Proof. fat SF_11174. Qed.
Lemma f74 : fetch_word source_segs (at_ CATB 0x74) = Some Wmv_a1a2. Proof. fat SF_11178. Qed.
Lemma f78 : fetch_word source_segs (at_ CATB 0x78) = Some Wmv_a2a3. Proof. fat SF_1117c. Qed.
Lemma f7c : fetch_word source_segs (at_ CATB 0x7c) = Some Wmv_a3a4. Proof. fat SF_11180. Qed.
Lemma f80 : fetch_word source_segs (at_ CATB 0x80) = Some Wmv_a4a5. Proof. fat SF_11184. Qed.
Lemma f84 : fetch_word source_segs (at_ CATB 0x84) = Some Wmv_a5a6. Proof. fat SF_11188. Qed.
Lemma f88 : fetch_word source_segs (at_ CATB 0x88) = Some Wecall. Proof. fat SF_1118c. Qed.
Lemma f8c : fetch_word source_segs (at_ CATB 0x8c) = Some Wret. Proof. fat SF_11190. Qed.
Lemma f90 : fetch_word source_segs (at_ CATB 0x90) = Some Wj_cpc. Proof. fat SF_11194. Qed.

(** The two triples take only the fetch facts their own proofs use —
    section discharge drops the rest — so the argument lists differ. *)
Definition cat_write_enter := musl_write_enter source_segs CATB f00 f04 f08 f0c f10 f14 f18 f1c f20 f24 f6c f70 f74 f78 f7c f80 f84 f90.
Definition cat_write_leave := musl_write_leave source_segs CATB f28 f2c f30 f34 f38 f3c f8c.

(** [write(1, buf, len)] from the wrapper's entry back to the caller, in
    the STREAMING shape: the pending write is handed to [twr_here_rec]
    and, PER DELIVERED LENGTH [n], the post-syscall path back through
    [__syscall_ret] is folded into the caller's write-all-tail
    obligation on the remainder [skipn n bs] (WallSim's [to_wall_tail];
    the caller's own put loop decides between looping back to the read
    head and reissuing the write).

    Compare [musl_write_wexit], which does the same around
    [SeqExec.tw_write_ret].  The two differ only in which shape relation
    the [ecall] is discharged into; everything about the INSTRUCTIONS
    comes from the same two triples. *)
Lemma cat_write_twr :
  forall (LH : machine_state -> Prop)
         (regs : bvmap 5 word) (mem : word -> option byte)
         (k sp0 buf len : word) (bs : list byte),
  (bv_unsigned k mod 2 = 0)%Z ->
  getr regs 1 = k -> getr regs 2 = sp0 ->
  getr regs 10 = Z_to_bv 64 1 -> getr regs 11 = buf -> getr regs 12 = len ->
  RiscvSemantics.store_ok source_segs mem (at_ sp0 (-8)) 8%nat = true ->
  (bv_unsigned (at_ sp0 (-8)) + 8 <= 2^64)%Z ->
  (bv_unsigned len <= 18446744073709547520)%Z ->
  rdn source_segs (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k))
      buf (word_to_nat len) = Some bs ->
  (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
  access_okb buf (bv_unsigned len) = true ->
  (1 <= length bs)%nat ->
  (forall n regs', (1 <= n)%nat -> (n <= length bs)%nat ->
     regs_agree musl_clob regs regs' ->
     getr regs' 1 = k -> getr regs' 2 = sp0 ->
     getr regs' 10 = len_word (firstn n bs) ->
     to_wall_tail source_segs (Z_to_bv 64 1)
       (mkst regs' k (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k))
          (seg_rom source_segs))
       (skipn n bs) (lh_next source_segs LH)) ->
  to_wr source_segs LH bs
    (mkst regs (0x11104 : word) mem (seg_rom source_segs)).
Proof.
  intros LH regs mem k sp0 buf len bs Hev H1 H2 H10 H11 H12 Hok Hnw Hlen Hread
         Hacc Hnb Hcont.
  assert (Hk : ret_ok k) by (apply ret_ok_even; exact Hev).
  assert (Hr28 : ret_ok (at_ CATB 0x28))
    by (apply ret_ok_even; unfold at_, CATB; vm_compute; reflexivity).
  assert (Hlbs : (Z.of_nat (length bs) <= 18446744073709547520)%Z).
  { rewrite (rdn_length _ _ _ _ _ Hread).
    unfold word_to_nat. pose proof (u64_range len).
    rewrite Z2Nat.id by lia. exact Hlen. }
  replace (0x11104 : word) with (at_ CATB 0x00) by (unfold at_, CATB; bveq).
  (* entry -> the ecall.  NOTE: the triple is applied directly rather than
     through [Hoare.triple_msteps], because the caller needs the
     [regs_agree] component — its loop-head invariant mentions [gp] and
     [s0], which survive precisely because they are outside [musl_clob].
     [triple_msteps]/[triple_wexit] both drop that component. *)
  destruct (cat_write_enter k sp0 (Z_to_bv 64 1) buf len mem
              regs mem (seg_rom source_segs)
              ltac:(repeat split; assumption))
    as (regs1 & mem1 & Hst & (Hm & Q1 & Q2 & Q10 & Q11 & Q12 & Q17) & Hag1 & _).
  eapply msteps_to_wr; [ exact Hst | ]. subst mem1.
  (* the ecall itself *)
  eapply twr_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ f88 eq_refl) | ].
  apply twr_here_rec.
  - rewrite Q17. vm_compute. reflexivity.
  - rewrite <- getr_nz by reg_neq_tac. exact Q10.
  - rewrite (ms_read_bytes_rdn source_segs) by reflexivity.
    cbn [ms_mem ms_regs].
    rewrite <- !getr_nz by reg_neq_tac. rewrite Q11, Q12. exact Hread.
  - rewrite <- !getr_nz by reg_neq_tac. rewrite Q11, Q12. exact Hacc.
  - exact Hnb.
  - (* back from the kernel: [__syscall_ret], then the caller's put loop *)
    intros n Hn1 Hn2.
    rewrite at_addi. cbn [Z.add].
    destruct (cat_write_leave k sp0 (len_word (firstn n bs))
                (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k)) Hk Hr28
                (regupd regs1 10 (len_word (firstn n bs)))
                (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k))
                (seg_rom source_segs)
                ltac:(repeat split;
                      [ rewrite getr_other by reg_neq_tac; exact Q1
                      | rewrite getr_other by reg_neq_tac; exact Q2
                      | rewrite getr_same by reg_neq_tac; reflexivity
                      | apply rdn_wbytes_hit8; exact Hnw
                      | apply not_errno;
                        rewrite u_len_word_firstn by lia; lia ]))
      as (regs2 & mem2 & Hst2 & (Hm2 & R1 & R2 & R10) & Hag2 & _). subst mem2.
    assert (Hag : regs_agree musl_clob regs regs2).
    { eapply regs_agree_trans; [ exact Hag1 | ].
      eapply regs_agree_trans; [ | exact Hag2 ].
      apply regs_agree_upd; [ unfold musl_clob; tauto | apply regs_agree_refl ]. }
    eapply msteps_to_wall_tail; [ exact Hst2 | ].
    apply (Hcont n regs2 Hn1 Hn2 Hag R1 R2 R10).
Qed.
