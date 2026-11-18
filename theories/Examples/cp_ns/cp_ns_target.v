(** * cp-ns, target binary (Zig ReleaseSmall, raw ecalls).

    PROOF-SIDE FILE (not part of the trusted specification).

    _start saves ra/s0, calls run() (0x10011b8) with argc/argv, and
    exits with its return value.  run() checks argc, issues the two
    openats, then a register-only read/write loop over the static
    1024-byte buffer at 0x1002298 (loop head 0x100120c), then closes
    both fds.  Each failure path loads its exit code into a1 and jumps
    to the shared tail at 0x1001268.

    Deliverables, over the run's segment list [target_segs ++ vt]:
    - [target_wexit_lt3] : argc < 3 -> to_wexit [] 2 (CatSim glue);
    - [target_ge3]       : argc >= 3 -> to_floop [cp_outcomes], the same
      outcome set [cp_ns_source.source_ge3] derives: the copy of a
      regular file a word offset reaches the end of runs to its end
      ([target_loop]); a file of 2^64 bytes or more and /dev/urandom are
      copied forever, a silent loop ([tgt_endless_anchored]).

    Conventions as in cp_ns_source.v.  The loop body is factored into
    three [msteps] chain lemmas ([tgt_head_to_read],
    [tgt_read_to_write], [tgt_write_to_head]) shared by the bounded
    [to_fout] loop and the endless one.

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Sys.Prelude.
From LinuxProcessSemantics.Common Require Import SimInv ExitSim PropExec CatExec CatSim SeqExec StepTac StreamExec StreamSim FileSim ErrEscape StoreOk SymExec SymTac RunSegmentsLift FileSimWalk FileSimLoop.
From LinuxProcessSemantics.Examples.cp_ns Require Import cp_ns_code cp_ns_defs.
From LinuxProcessSemantics.Examples.cp_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.cp_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them. *)
#[local] Instance cp_ns_target_fx : FPState := fx0.

Definition tbuf : word := 0x1002298.

Lemma u_tbuf : bv_unsigned tbuf = 0x1002298%Z.
Proof. reflexivity. Qed.

(** [bv_unsigned x = 0] closes a [beqz] whose operand is not literally
    zero (the executor's [sub] of a register from itself). *)
Lemma c_eq_0_of_u : forall x : word, bv_unsigned x = 0%Z ->
  c_eq x (Z_to_bv 64 0) = true.
Proof.
  intros x Hx. unfold c_eq. apply bv_eqb_eq. apply bv_eq.
  rewrite Hx. reflexivity.
Qed.

Lemma tfd3_ne_fd4 : Z_to_bv 64 3 <> Z_to_bv 64 4.
Proof. intro Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc. Qed.

(** Normalize the pc of a [to_fout] / [to_floop] goal's head state to its
    literal form (continuation states arrive with [v_addi pc 4]). *)
Local Ltac tfnorm_pc :=
  try lazymatch goal with
  | |- to_fout _ (mkst _ ?p _ _) _ _ => wlit p
  end.

Local Ltac tflnorm_pc :=
  try lazymatch goal with
  | |- to_floop _ (mkst _ ?p _ _) _ _ => wlit p
  end.

(** A fact about a reflective block's EXIT register file, read back
    through its [regs_ok] [H]. *)
Local Ltac t_out H :=
  sym_regs H; rewrite ?getr_nz by reg_neq_tac;
  first [ assumption | sym_close | (vm_compute; reflexivity) ].

(** Store-permission side goals against the target image. *)
Local Ltac t_ro :=
  first [ apply target_store_ok; imm_norm; u_norm; lia | solve_store_ok_inv ].

Section TargetProof.

(** The segments the run appends after the image's own: the vDSO pair
    ([Run.run_segments]).  Nothing below reads them. *)
Variable vt : list Segment.

Local Abbreviation rsegs := (target_segs ++ vt).
Local Abbreviation trom := (seg_rom (target_segs ++ vt)).
Local Abbreviation TFv F := (fetch_word_app _ vt _ _ F).

(* ================================================================= *)
(* The copy-loop body chains (shared by the bounded to_fout loop and  *)
(* the endless one).  The target loop is register-only: no stack       *)
(* traffic, so the chains are generic in the memory.                   *)
(* Loop head 0x100120c:  li a7,63; li a2,1024; mv a0,a4; mv a1,a5      *)
(*   (read ecall at 0x100121c).                                        *)
(* ================================================================= *)

(** Loop head 0x100120c to the read ecall record. *)
Lemma tgt_head_to_read : forall regs mem fdin fdout,
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 13 = fdout -> reg_get regs 14 = fdin ->
  reg_get regs 15 = tbuf ->
  exists regs',
    bv_unsigned (getr regs' 17) = 63%Z /\
    reg_get regs' 10 = fdin /\ reg_get regs' 11 = tbuf /\
    reg_get regs' 12 = Z_to_bv 64 1024 /\
    reg_get regs' 1 = (0x10011b0 : word) /\
    reg_get regs' 13 = fdout /\ reg_get regs' 14 = fdin /\
    reg_get regs' 15 = tbuf /\
    msteps rsegs (mkst regs (0x100120c : word) mem trom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := (0x100121c : word);
         ms_svc_pending := Some (getr regs' 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := trom |}.
Proof.
  intros regs mem fdin fdout H1 H13 H14 H15.
  (* 0x100120c .. 0x100121c — the whole loop head in ONE reflective
     block: [li a7,63], [li a2,1024] and the two argument moves.  Pure
     register traffic, so there are no side conditions and no pins. *)
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781836) mem trom)
    5%nat (@nil bool) (@nil expr) (@nil (reg * expr)) (@nil word)
    (@nil word) R HR Hms.
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  9: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_100121c) eq_refl)
      | apply mst_refl ]. }
  all: t_out HR.
Qed.

(** Post-read state (0x1001220, a0 = the block length, 1..1024) to the
    write ecall record. *)
Lemma tgt_read_to_write : forall regs mem fdin fdout cnt,
  reg_get regs 10 = cnt ->
  (1 <= bv_unsigned cnt)%Z -> (bv_unsigned cnt <= 1024)%Z ->
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 13 = fdout -> reg_get regs 14 = fdin ->
  reg_get regs 15 = tbuf ->
  exists regs',
    bv_unsigned (getr regs' 17) = 64%Z /\
    reg_get regs' 10 = fdout /\ reg_get regs' 11 = tbuf /\
    reg_get regs' 12 = cnt /\
    reg_get regs' 1 = (0x10011b0 : word) /\
    reg_get regs' 13 = fdout /\ reg_get regs' 14 = fdin /\
    reg_get regs' 15 = tbuf /\
    msteps rsegs (mkst regs (0x1001220 : word) mem trom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := (0x100123c : word);
         ms_svc_pending := Some (getr regs' 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := trom |}.
Proof.
  intros regs mem fdin fdout cnt H10 Hc1 Hc2 H1 H13 H14 H15.
  (* 0x1001220 .. 0x100123c — 7 instructions in ONE reflective block:
     the three not-taken guards on the delivered count, the two
     argument moves and [li a7,64].  The count enters as the single
     pin, which is what makes all three branch conditions decidable. *)
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781856) mem trom)
    8%nat [false; false; false] (@nil expr) [((10 : reg), EVar 32)] [cnt]
    (@nil word) R HR Hms.
  { apply c_eq_0_false; lia. }
  { apply c_eq_0_false; lia. }
  { apply c_lts_pos_0; lia. }
  { rewrite getr_nz by reg_neq_tac; exact H10. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  9: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_100123c) eq_refl)
      | apply mst_refl ]. }
  all: t_out HR.
Qed.

(** Post-write state (0x1001240, a0 = a2 = the full count) back to the
    loop head. *)
Lemma tgt_write_to_head : forall regs mem fdin fdout cnt,
  reg_get regs 10 = cnt -> reg_get regs 12 = cnt ->
  (1 <= bv_unsigned cnt)%Z -> (bv_unsigned cnt <= 1024)%Z ->
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 13 = fdout -> reg_get regs 14 = fdin ->
  reg_get regs 15 = tbuf ->
  exists regs',
    reg_get regs' 1 = (0x10011b0 : word) /\
    reg_get regs' 13 = fdout /\ reg_get regs' 14 = fdin /\
    reg_get regs' 15 = tbuf /\
    msteps rsegs (mkst regs (0x1001240 : word) mem trom)
      (mkst regs' (0x100120c : word) mem trom).
Proof.
  intros regs mem fdin fdout cnt H10 H12 Hc1 Hc2 H1 H13 H14 H15.
  (* 0x1001240 .. 0x100120c — 4 instructions in ONE reflective block:
     the not-taken [blez], the buffer/count update and the taken
     [beqz] back to the loop head.  The fuel is EXACTLY the body
     length: one more and the executor would run into the next
     iteration. *)
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781888) mem trom)
    4%nat [false; true] (@nil expr)
    [((10 : reg), EVar 32); ((12 : reg), EVar 32)] [cnt]
    (@nil word) R HR Hms.
  { apply c_eq_0_of_u; rewrite v_sub_small by lia; lia. }
  { apply negb_false_iff; apply c_lts_0_pos; lia. }
  { rewrite getr_nz by reg_neq_tac; exact H10. }
  { rewrite getr_nz by reg_neq_tac; exact H12. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  5: { eapply msteps_trans; [ exact Hms | ]. sym_pc_lit. apply mst_refl. }
  all: t_out HR.
Qed.

(** EOF (the read delivered 0 bytes): the not-taken [bltz], [mv a2,a0],
    the taken [beqz] into the shutdown tail and the first [close]'s two
    argument loads.  5 instructions in ONE reflective block; both branch
    conditions compare literals, so neither leaves a side condition. *)
Lemma tgt_eof_to_close : forall regs mem fdin fdout,
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 10 = Z_to_bv 64 0 ->
  reg_get regs 13 = fdout -> reg_get regs 14 = fdin ->
  exists regs',
    bv_unsigned (getr regs' 17) = 57%Z /\
    reg_get regs' 10 = fdin /\
    reg_get regs' 1 = (0x10011b0 : word) /\
    reg_get regs' 13 = fdout /\
    msteps rsegs (mkst regs (0x1001220 : word) mem trom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := (0x1001280 : word);
         ms_svc_pending := Some (getr regs' 17); ms_resv := None;
         ms_fcsr := fp_csr; ms_mem := mem; ms_rom := trom |}.
Proof.
  intros regs mem fdin fdout H1 H10 H13 H14.
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781856) mem trom)
    6%nat [false; true] (@nil expr)
    [((10 : reg), ELit 0); ((14 : reg), EVar 32)] [fdin]
    (@nil word) R HR Hms.
  { rewrite getr_nz by reg_neq_tac; rewrite H10; bveq. }
  { rewrite getr_nz by reg_neq_tac; exact H14. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  5: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_1001280) eq_refl)
      | apply mst_refl ]. }
  all: t_out HR.
Qed.

(** Between the two [close] ecalls: [li a7,57] and [mv a0,a3]. *)
Lemma tgt_close_to_close : forall regs mem fdout,
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 13 = fdout ->
  exists regs',
    bv_unsigned (getr regs' 17) = 57%Z /\
    reg_get regs' 10 = fdout /\
    reg_get regs' 1 = (0x10011b0 : word) /\
    msteps rsegs (mkst regs (0x1001284 : word) mem trom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := (0x100128c : word);
         ms_svc_pending := Some (getr regs' 17); ms_resv := None;
         ms_fcsr := fp_csr; ms_mem := mem; ms_rom := trom |}.
Proof.
  intros regs mem fdout H1 H13.
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781956) mem trom)
    3%nat (@nil bool) (@nil expr)
    [((13 : reg), EVar 32)] [fdout] (@nil word) R HR Hms.
  { rewrite getr_nz by reg_neq_tac; exact H13. }
  exists R.
  refine (conj _ (conj _ (conj _ _))).
  4: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_100128c) eq_refl)
      | apply mst_refl ]. }
  all: t_out HR.
Qed.

(** The success tail after both closes: [li a5,0], the [j] into the
    shared exit tail, [mv a0,a5], the [ret] into _start (the [ra] pin)
    and the exit(93) load.  The executor stops at the [ecall]. *)
Lemma tgt_loop_exit0 : forall regs mem model fsv,
  reg_get regs 1 = (0x10011b0 : word) ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x1001290 : word) mem trom) model
    (fun o => o = (Z_to_bv 64 0, fsv)).
Proof.
  intros regs mem model fsv H1 Hfs.
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781968) mem trom)
    6%nat (@nil bool) (@nil expr)
    [((1 : reg), ELit 0x10011b0)] (@nil word) (@nil word) R HR Hms.
  { rewrite getr_nz by reg_neq_tac; rewrite H1; bveq. }
  eapply tfo_msteps.
  { eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10011b4) eq_refl)
      | apply mst_refl ]. }
  apply tfo_exit_rec.
  - t_out HR.
  - t_out HR.
  - vm_compute; reflexivity.
  - exact Hfs.
Qed.

(** The end of the copy, from the return of a read that delivered 0
    bytes: both closes, exit 0. *)
Lemma tgt_eof_tail : forall regs mem model fdin fdout e_in e_out fsv,
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 10 = Z_to_bv 64 0 ->
  reg_get regs 13 = fdout -> reg_get regs 14 = fdin ->
  fdin <> fdout ->
  (bv_unsigned fdin < 2 ^ 31)%Z -> (bv_unsigned fdout < 2 ^ 31)%Z ->
  fd_lookup (m_fds model) fdin = Some e_in ->
  fd_lookup (m_fds model) fdout = Some e_out ->
  m_halted model = None -> m_vm_lazy model = [] ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x1001220 : word) mem trom) model
    (fun o => o = (Z_to_bv 64 0, fsv)).
Proof.
  intros regs mem model fdin fdout e_in e_out fsv H1 H10 H13 H14 Hneq Hfin31 Hfout31
    Hfdin Hfdout Hh Hlazy Hfs.
  (* bltz ft; mv a2,a0; beqz taken -> 0x1001278; li a7,57; mv a0,a4 *)
  destruct (tgt_eof_to_close regs mem fdin fdout H1 H10 H13 H14)
    as (regsE & E17 & E10 & E1 & E13 & HmsE).
  eapply tfo_msteps; [ exact HmsE | ].
  eapply tfo_close_rec with (fdv := fdin).
  { exact E17. }
  { exact E10. }
  { exact Hfdin. }
  { fd32_ok. }
  { exact Hh. }
  { exact Hlazy. }
  (* li a7,57; mv a0,a3 *)
  tfnorm_pc.
  match goal with |- to_fout _ (mkst ?RG _ ?MM _) _ _ =>
    destruct (tgt_close_to_close RG MM fdout)
      as (regsF & F17 & F10 & F1 & HmsF)
  end;
    [ regupd_resolve; exact E1 | regupd_resolve; exact E13 | ].
  eapply tfo_msteps; [ exact HmsF | ].
  eapply tfo_close_rec with (fdv := fdout).
  { exact F17. }
  { exact F10. }
  { model_simp.
    rewrite fd_lookup_remove_neq by congruence.
    exact Hfdout. }
  { fd32_ok. }
  { model_simp. exact Hh. }
  { exact Hlazy. }
  (* li a5,0; j -> 0x1001268; mv a0,a5; ret; li a7,93; ecall *)
  tfnorm_pc.
  apply tgt_loop_exit0.
  + regupd_resolve; exact F1.
  + model_simp. exact Hfs.
Qed.

(* ================================================================= *)
(* The copy loop, a source a word offset reaches the end of.          *)
(* ================================================================= *)

(** Loop-head register pins. *)
Definition tLH (fdin fdout : word) (regs : bvmap 5 word) : Prop :=
  reg_get regs 1 = (0x10011b0 : word) /\
  reg_get regs 13 = fdout /\ reg_get regs 14 = fdin /\
  reg_get regs 15 = tbuf.

(** The model after [k] bytes of the source inode [i]'s bytes [D] are
    copied into the destination [fe_d] the second open handed out on
    the image [fs1] ([cp_ns_defs.cp_dst_at], [cp_ns_defs.cp_fs_at]). *)
Definition tMI (fs1 : Fs.Fs) (i : Fs.ino) (D : list byte) (fdin fdout : word)
    (fe_d : FdEntry) (k : nat) (model : Model) : Prop :=
  m_halted model = None /\
  m_vm_lazy model = [] /\
  fd_lookup (m_fds model) fdin = Some (FdFile i (nat_to_word k)) /\
  fd_lookup (m_fds model) fdout = Some (cp_dst_at fe_d k) /\
  m_fs model = cp_fs_at fe_d fs1 D k.

Lemma target_loop : forall fs1 i D fdin fdout fe_d,
  Fs.fs_ino_data fs1 i = D ->
  fdin <> fdout ->
  (bv_unsigned fdin < 2 ^ 31)%Z -> (bv_unsigned fdout < 2 ^ 31)%Z ->
  (Z.of_nat (length D) < 2^64)%Z ->
  cp_dst_ok fe_d fs1 ->
  forall rem k regs mem model,
  (length D - k < rem)%nat -> (k <= length D)%nat ->
  tLH fdin fdout regs -> tMI fs1 i D fdin fdout fe_d k model ->
  to_fout rsegs (mkst regs (0x100120c : word) mem trom) model
    (fun o => o = (Z_to_bv 64 0, cp_copied fe_d fs1 D)).
Proof.
  intros fs1 i D fdin fdout fe_d HD Hneq Hfin31 Hfout31 HDlen Hdst.
  (* a file destination is not the source's inode once that holds bytes:
     the destination's open left it empty *)
  assert (Hij : forall j o, fe_d = FdFileW j o -> D <> [] -> i <> j).
  { intros j o He HDne Hie. subst j.
    destruct Hdst as [(j' & Hj' & Hd) | [Hj' | Hj']]; rewrite He in Hj';
      try discriminate Hj'.
    injection Hj' as <- _. apply HDne. rewrite <- HD. exact Hd. }
  induction rem as [|rem IH]; intros k regs mem model Hrem Hk HLH HMI.
  { lia. }
  destruct HLH as (H1 & H13 & H14 & H15).
  destruct HMI as (Hh & Hlazy & Hfdin & Hfdout & Hfs).
  assert (HkZ : (Z.of_nat k < 2^64)%Z) by lia.
  set (chunk := file_read D (nat_to_word k) (Z_to_bv 64 1024)).
  assert (Hclen : length chunk = Nat.min 1024 (length D - k)%nat)
    by (unfold chunk; apply cp_chunk_len; exact HkZ).
  assert (Hc1024 : (length chunk <= 1024)%nat) by lia.
  (* ---- read call ---- *)
  destruct (tgt_head_to_read regs mem fdin fdout H1 H13 H14 H15)
    as (regsR & R17 & R10 & R11 & R12 & R1 & R13 & R14 & R15 & HmsR).
  eapply tfo_msteps; [exact HmsR|].
  eapply tfo_read_rec with (p := i) (off := nat_to_word k) (data := D)
    (buf := tbuf) (cnt := Z_to_bv 64 1024) (fdv := fdin).
  { exact R17. } { exact R10. } { exact R11. } { exact R12. }
  { exact Hfdin. }
  { fd32_ok. }
  { rewrite Hfs. apply cp_fs_at_data_src; [exact HD | exact Hk | exact Hij]. }
  { exact (target_buf_wseg vt). }
  { rewrite u_Z2bv by lia. unfold rw_bytes_max. lia. }
  { rewrite u_Z2bv by lia. lia. }
  { (* the buffer is a link-time constant far under [State.TASK_SIZE] *)
    apply access_okb_intro. rewrite u_tbuf.
    rewrite u_Z2bv by lia. unfold TASK_SIZE. lia. }
  { exact Hh. }
  { exact Hlazy. }
  fold chunk.
  destruct (Nat.eq_dec k (length D)) as [Heq | HneD].
  - (* ================= EOF: close both, exit 0 ================= *)
    assert (Hchn : chunk = [])
      by (unfold chunk; apply file_read_nil; rewrite wtn_ntw by lia; lia).
    rewrite Hchn. cbn [write_to_mem].
    replace (len_word (@nil byte)) with (Z_to_bv 64 0) by reflexivity.
    tfnorm_pc.
    apply (tgt_eof_tail _ _ _ fdin fdout (FdFile i (nat_to_word k + Z_to_bv 64 0))
             (cp_dst_at fe_d k)).
    + regupd_resolve; exact R1.
    + regupd_resolve; reflexivity.
    + regupd_resolve; exact R13.
    + regupd_resolve; exact R14.
    + exact Hneq.
    + exact Hfin31.
    + exact Hfout31.
    + model_simp. apply fd_lookup_insert_eq.
    + model_simp. rewrite fd_lookup_insert_neq by congruence. exact Hfdout.
    + exact Hh.
    + exact Hlazy.
    + model_simp. rewrite Hfs, Heq. apply cp_fs_at_final.
  - (* ================= one more chunk: write it back ================= *)
    assert (HkltD : (k < length D)%nat) by lia.
    assert (Hc1 : (1 <= length chunk)%nat) by lia.
    assert (HuLen : bv_unsigned (len_word chunk) = Z.of_nat (length chunk))
      by (apply u_len_word; lia).
    assert (Haok : access_okb tbuf (bv_unsigned (len_word chunk)) = true).
    { apply access_okb_intro. rewrite u_tbuf, HuLen. unfold TASK_SIZE. lia. }
    destruct (tgt_read_to_write (regupd regsR 10 (len_word chunk))
        (write_to_mem mem tbuf chunk) fdin fdout (len_word chunk)
        ltac:(regupd_resolve; reflexivity)
        ltac:(lia) ltac:(lia)
        ltac:(regupd_resolve; exact R1)
        ltac:(regupd_resolve; exact R13)
        ltac:(regupd_resolve; exact R14)
        ltac:(regupd_resolve; exact R15))
      as (regsW & W17 & W10 & W11 & W12 & W1 & W13 & W14 & W15 & HmsW).
    eapply tfo_msteps.
    { norm_pc. exact HmsW. }
    assert (Hrd : rdn rsegs (write_to_mem mem tbuf chunk) tbuf
                    (word_to_nat (len_word chunk)) = Some chunk).
    { rewrite wtn_len_word by lia.
      apply rdn_write_to_mem. rewrite u_tbuf. lia. }
    (* what follows the write, whatever the destination took *)
    assert (Hnext : forall model',
      tMI fs1 i D fdin fdout fe_d (k + length chunk) model' ->
      to_fout rsegs (mkst (regupd regsW 10 (len_word chunk)) (v_addi (0x100123c : word) 4)
                          (write_to_mem mem tbuf chunk) trom)
        model' (fun o => o = (Z_to_bv 64 0, cp_copied fe_d fs1 D))).
    { intros model' HMI'.
      destruct (tgt_write_to_head (regupd regsW 10 (len_word chunk))
          (write_to_mem mem tbuf chunk) fdin fdout (len_word chunk)
          ltac:(regupd_resolve; reflexivity)
          ltac:(regupd_resolve; exact W12)
          ltac:(lia) ltac:(lia)
          ltac:(regupd_resolve; exact W1)
          ltac:(regupd_resolve; exact W13)
          ltac:(regupd_resolve; exact W14)
          ltac:(regupd_resolve; exact W15))
        as (regsH & G1 & G13 & G14 & G15 & HmsH).
      eapply tfo_msteps.
      { norm_pc. exact HmsH. }
      apply (IH (k + length chunk)%nat).
      { lia. }
      { lia. }
      { unfold tLH. auto. }
      { exact HMI'. } }
    destruct Hdst as [(j & -> & Hjd) | [-> | ->]].
    + (* a regular file: it takes the chunk at offset [k] *)
      eapply tfo_write_rec with (p := j) (off := nat_to_word k)
        (data := firstn k D) (bs := chunk) (buf := tbuf)
        (cnt := len_word chunk) (fdv := fdout).
      { exact W17. } { exact W10. } { exact W11. } { exact W12. }
      { model_simp.
        rewrite fd_lookup_insert_neq by congruence.
        exact Hfdout. }
      { fd32_ok. }
      { exact Hrd. }
      { rewrite HuLen. unfold rw_bytes_max. lia. }
      { model_simp. rewrite Hfs. apply cp_fs_at_data_dst. exact Hjd. }
      { apply file_gap_in_range.
        rewrite u_ntw by lia. rewrite length_firstn. unfold rw_bytes_max. lia. }
      { exact Haok. }
      { model_simp. exact Hh. }
      { exact Hlazy. }
      apply Hnext.
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      { model_simp. exact Hh. }
      { exact Hlazy. }
      { model_simp.
        rewrite fd_lookup_insert_neq by congruence.
        rewrite fd_lookup_insert_eq.
        rewrite len_word_ntw, ntw_add. reflexivity. }
      { model_simp.
        rewrite fd_lookup_insert_eq.
        rewrite len_word_ntw, ntw_add. reflexivity. }
      { model_simp. rewrite Hfs.
        unfold chunk.
        rewrite cp_fs_at_step by lia.
        rewrite <- cp_chunk_len by exact HkZ.
        reflexivity. }
    + (* /dev/null: the count *)
      eapply tfo_write_null_rec with (rd := false).
      { exact W17. } { exact W10. } { exact W11. } { exact W12. }
      { model_simp.
        rewrite fd_lookup_insert_neq by congruence.
        exact Hfdout. }
      { fd32_ok. }
      { exact Haok. }
      { rewrite HuLen. unfold rw_bytes_max. lia. }
      { model_simp. exact Hh. }
      { exact Hlazy. }
      apply Hnext.
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      { model_simp. exact Hh. }
      { exact Hlazy. }
      { model_simp.
        rewrite fd_lookup_insert_eq.
        rewrite len_word_ntw, ntw_add. reflexivity. }
      { model_simp.
        rewrite fd_lookup_insert_neq by congruence.
        exact Hfdout. }
      { model_simp. rewrite Hfs. reflexivity. }
    + (* /dev/urandom: the whole count of a readable buffer *)
      eapply tfo_write_urandom_rec with (rd := false) (bs := chunk).
      { exact W17. } { exact W10. } { exact W11. } { exact W12. }
      { model_simp.
        rewrite fd_lookup_insert_neq by congruence.
        exact Hfdout. }
      { fd32_ok. }
      { exact Hrd. }
      { exact Haok. }
      { rewrite HuLen. unfold page_size. lia. }
      { model_simp. exact Hh. }
      { exact Hlazy. }
      apply Hnext.
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      { model_simp. exact Hh. }
      { exact Hlazy. }
      { model_simp.
        rewrite fd_lookup_insert_eq.
        rewrite len_word_ntw, ntw_add. reflexivity. }
      { model_simp.
        rewrite fd_lookup_insert_neq by congruence.
        exact Hfdout. }
      { model_simp. rewrite Hfs. reflexivity. }
Qed.

(* ================================================================= *)
(* The endless copies: a silent loop over the read anchors            *)
(* ================================================================= *)

(** Loop read-anchor register pins ([tgt_head_to_read]'s conclusion). *)
Definition tRpins (regs : bvmap 5 word) (fdin fdout : word) : Prop :=
  bv_unsigned (getr regs 17) = 63%Z /\
  reg_get regs 10 = fdin /\ reg_get regs 11 = tbuf /\
  reg_get regs 12 = Z_to_bv 64 1024 /\
  reg_get regs 1 = (0x10011b0 : word) /\
  reg_get regs 13 = fdout /\ reg_get regs 14 = fdin /\
  reg_get regs 15 = tbuf.

Definition trdrec (regs : bvmap 5 word) (mem : word -> option byte)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := (0x100121c : word);
     ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := trom |}.

(** THE READ ANCHORS of an endless copy: the read ecall of the loop, the
    source and destination descriptors as [cp_ns_defs.cp_emodel] keeps
    them.  The loop is register-only, so any memory. *)
Definition tAnchor (c : config) : Prop :=
  exists fdin fdout regs mem model,
    fdin <> fdout /\ fd32 fdin = fdin /\ fd32 fdout = fdout /\
    tRpins regs fdin fdout /\
    cp_emodel fdin fdout model /\ c = mkCfg (trdrec regs mem) model.

(** From the write's return back to the next read anchor. *)
Lemma tgt_endless_next : forall regs mem model fdin fdout cnt,
  fdin <> fdout -> fd32 fdin = fdin -> fd32 fdout = fdout ->
  reg_get regs 10 = cnt -> reg_get regs 12 = cnt ->
  (1 <= bv_unsigned cnt)%Z -> (bv_unsigned cnt <= 1024)%Z ->
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 13 = fdout -> reg_get regs 14 = fdin ->
  reg_get regs 15 = tbuf ->
  cp_emodel fdin fdout model ->
  fpath rsegs tAnchor (mkCfg (mkst regs (0x1001240 : word) mem trom) model).
Proof.
  intros regs mem model fdin fdout cnt Hne Hfin32 Hfout32 H10 H12 Hc1 Hc2 H1 H13 H14
    H15 HM.
  destruct (tgt_write_to_head regs mem fdin fdout cnt H10 H12 Hc1 Hc2 H1 H13 H14 H15)
    as (regsH & G1 & G13 & G14 & G15 & HmsH).
  destruct (tgt_head_to_read regsH mem fdin fdout G1 G13 G14 G15)
    as (regsR & Q17 & Q10 & Q11 & Q12 & Q1 & Q13 & Q14 & Q15 & HmsR).
  pose proof HM as (Hh & Hlazy & _).
  eapply fpath_msteps; [exact HmsH | exact Hh | exact Hlazy |].
  eapply fpath_msteps; [exact HmsR | exact Hh | exact Hlazy |].
  apply fp_anchor.
  exists fdin, fdout, regsR, mem, model.
  split; [exact Hne|]. split; [exact Hfin32|]. split; [exact Hfout32|].
  split; [unfold tRpins; tauto|].
  split; [exact HM | reflexivity].
Qed.

(** The write of an endless copy, from its ecall: whatever the
    destination is, the one resolution is silent and the loop goes on to
    the next read anchor. *)
Lemma tgt_endless_write : forall regsW mem model fdin fdout chunk si,
  fdin <> fdout -> fd32 fdin = fdin -> fd32 fdout = fdout ->
  bv_unsigned (getr regsW 17) = 64%Z ->
  reg_get regsW 10 = fdout -> reg_get regsW 11 = tbuf ->
  reg_get regsW 12 = len_word chunk ->
  reg_get regsW 1 = (0x10011b0 : word) ->
  reg_get regsW 13 = fdout -> reg_get regsW 14 = fdin ->
  reg_get regsW 15 = tbuf ->
  (1 <= length chunk <= 1024)%nat ->
  m_halted model = None -> m_vm_lazy model = [] ->
  cp_esrc fdin model si -> cp_edst fdout model si ->
  fpath rsegs tAnchor
    (mkCfg {| ms_regs := regsW; ms_fregs := fp_regs; ms_pc_val := (0x100123c : word);
              ms_svc_pending := Some (getr regsW 17); ms_resv := None; ms_fcsr := fp_csr;
              ms_mem := write_to_mem mem tbuf chunk; ms_rom := trom |} model).
Proof.
  intros regsW mem model fdin fdout chunk si Hne Hfin32 Hfout32 W17 W10 W11 W12 W1 W13
    W14 W15 Hlen Hh Hlazy Hsrc Hdst.
  assert (HuLen : bv_unsigned (len_word chunk) = Z.of_nat (length chunk))
    by (apply u_len_word; lia).
  assert (Haok : access_okb tbuf (bv_unsigned (len_word chunk)) = true).
  { apply access_okb_intro. rewrite u_tbuf, HuLen. unfold TASK_SIZE. lia. }
  assert (Hrd : rdn rsegs (write_to_mem mem tbuf chunk) tbuf
                  (word_to_nat (len_word chunk)) = Some chunk).
  { rewrite wtn_len_word by lia.
    apply rdn_write_to_mem. rewrite u_tbuf. lia. }
  (* from the write's return, whatever the destination took *)
  assert (Hnext : forall model',
    cp_emodel fdin fdout model' ->
    fpath rsegs tAnchor
      (mkCfg (mkst (regupd regsW 10 (len_word chunk)) (v_addi (0x100123c : word) 4)
                   (write_to_mem mem tbuf chunk) trom) model')).
  { intros model' HM'.
    match goal with
    | |- fpath _ _ (mkCfg (mkst _ ?p _ _) _) => replace p with (0x1001240 : word) by bveq
    end.
    apply (tgt_endless_next _ _ model' fdin fdout (len_word chunk) Hne Hfin32 Hfout32).
    - regupd_resolve; reflexivity.
    - regupd_resolve; exact W12.
    - lia.
    - lia.
    - regupd_resolve; exact W1.
    - regupd_resolve; exact W13.
    - regupd_resolve; exact W14.
    - regupd_resolve; exact W15.
    - exact HM'. }
  match goal with
  | |- fpath _ _ (mkCfg ?REC _) => set (wrec := REC)
  end.
  assert (HgW0 : ms_gpr wrec 0 = fdout)
    by (unfold wrec; rewrite record_gpr, arg_reg_0; exact W10).
  assert (HgW1 : ms_gpr wrec 1 = tbuf)
    by (unfold wrec; rewrite record_gpr, arg_reg_1; exact W11).
  assert (HgW2 : ms_gpr wrec 2 = len_word chunk)
    by (unfold wrec; rewrite record_gpr, arg_reg_2; exact W12).
  destruct Hdst as [(j & off & Hfd & Hoff & Hsi) | [(rd & Hfd) | (rd & Hfd)]].
  - (* a regular file [j], not the source: it takes the chunk *)
    destruct (write_file_spec rsegs wrec model (getr regsW 17) j off
                (Fs.fs_ino_data (m_fs model) j) chunk W17
                ltac:(rewrite HgW0; exact Hfd)
                ltac:(rewrite HgW0; exact Hfout32)
                ltac:(rewrite HgW1, HgW2;
                      rewrite read_bytes_map_read_byte;
                      rewrite (ms_read_bytes_rdn rsegs wrec) by reflexivity;
                      unfold wrec; cbn [ms_mem]; exact Hrd)
                ltac:(rewrite HgW1, HgW2; exact Haok)
                ltac:(rewrite HgW2, HuLen; unfold rw_bytes_max; lia)
                eq_refl
                ltac:(apply file_gap_in_range; unfold rw_bytes_max; lia)
                ltac:(apply w_is0_pos; rewrite HgW2, HuLen; lia))
      as [Huniq Hnu].
    rewrite ?HgW0, ?HgW1, ?HgW2 in Huniq.
    apply (fpath_sys_det rsegs tAnchor wrec model (getr regsW 17) _ _ eq_refl Hh Hlazy
             Huniq Hnu).
    + model_simp. exact Hh.
    + exact Hlazy.
    + unfold wrec. rewrite adv_eff_ret_copyins.
      apply Hnext.
      split; [model_simp; exact Hh|]. split; [exact Hlazy|].
      exists si. split.
      * apply cp_esrc_write; [exact Hne | exact Hsi | exact Hsrc].
      * apply cp_edst_write; [lia | exact Hoff | exact Hsi].
  - (* /dev/null: the count *)
    destruct (write_null_spec_rec rsegs regsW (0x100123c : word)
                (write_to_mem mem tbuf chunk) trom model
                fdout rd tbuf (len_word chunk) W17 W10 W11 W12 Hfd Hfout32 Haok
                ltac:(rewrite HuLen; unfold rw_bytes_max; lia))
      as [Huniq Hnu].
    apply (fpath_sys_det rsegs tAnchor wrec model (getr regsW 17) _ _ eq_refl Hh Hlazy
             Huniq Hnu).
    + exact Hh.
    + exact Hlazy.
    + unfold wrec. rewrite adv_eff_ret.
      apply Hnext.
      split; [exact Hh|]. split; [exact Hlazy|].
      exists si. split; [exact Hsrc|].
      right. left. exists rd. exact Hfd.
  - (* /dev/urandom: the whole count of a readable buffer *)
    destruct (write_urandom_spec_rec rsegs regsW (0x100123c : word)
                (write_to_mem mem tbuf chunk) model
                fdout rd tbuf (len_word chunk) chunk W17 W10 W11 W12 Hfd Hfout32 Hrd Haok
                ltac:(rewrite HuLen; unfold page_size; lia))
      as [Huniq Hnu].
    apply (fpath_sys_det rsegs tAnchor wrec model (getr regsW 17) _ _ eq_refl Hh Hlazy
             Huniq Hnu).
    + exact Hh.
    + exact Hlazy.
    + unfold wrec. rewrite adv_eff_ret_copyins.
      apply Hnext.
      split; [exact Hh|]. split; [exact Hlazy|].
      exists si. split; [exact Hsrc|].
      right. right. exists rd. exact Hfd.
Qed.

(** EVERY READ ANCHOR IS SILENT ONTO A PATH TO THE NEXT ONE
    ([cp_ns_source.src_endless_anchored]'s twin). *)
Lemma tgt_endless_anchored : fanchored rsegs tAnchor.
Proof.
  intros a Ha.
  destruct Ha as (fdin & fdout & regs & mem & model & Hne & Hfin32 & Hfout32 & Hpins
                  & HM & ->).
  destruct Hpins as (R17 & R10 & R11 & R12 & R1 & R13 & R14 & R15).
  destruct HM as (Hh & Hlazy & si & Hsrc & Hdst).
  exists (trdrec regs mem), model, (getr regs 17).
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hh|]. split; [exact Hlazy|].
  assert (Hg0 : ms_gpr (trdrec regs mem) 0 = fdin)
    by (unfold trdrec; rewrite record_gpr, arg_reg_0; exact R10).
  assert (Hg1 : ms_gpr (trdrec regs mem) 1 = tbuf)
    by (unfold trdrec; rewrite record_gpr, arg_reg_1; exact R11).
  assert (Hg2 : ms_gpr (trdrec regs mem) 2 = Z_to_bv 64 1024)
    by (unfold trdrec; rewrite record_gpr, arg_reg_2; exact R12).
  (* what follows a read that delivered [chunk] *)
  assert (Hafter : forall chunk model',
    (1 <= length chunk <= 1024)%nat ->
    m_halted model' = None -> m_vm_lazy model' = [] ->
    cp_esrc fdin model' si -> cp_edst fdout model' si ->
    fpath rsegs tAnchor
      (mkCfg (mkst (regupd regs 10 (len_word chunk)) (0x1001220 : word)
                   (write_to_mem mem tbuf chunk) trom) model')).
  { intros chunk model' Hlen Hh' Hl' Hsrc' Hdst'.
    assert (HuLen : bv_unsigned (len_word chunk) = Z.of_nat (length chunk))
      by (apply u_len_word; lia).
    destruct (tgt_read_to_write (regupd regs 10 (len_word chunk))
                (write_to_mem mem tbuf chunk) fdin fdout (len_word chunk))
      as (regsW & W17 & W10 & W11 & W12 & W1 & W13 & W14 & W15 & HmsW);
      [ regupd_resolve; reflexivity | lia | lia
      | regupd_resolve; exact R1 | regupd_resolve; exact R13
      | regupd_resolve; exact R14 | regupd_resolve; exact R15 | ].
    eapply fpath_msteps; [exact HmsW | exact Hh' | exact Hl' |].
    exact (tgt_endless_write regsW mem model' fdin fdout chunk si Hne Hfin32 Hfout32
             W17 W10 W11 W12 W1 W13 W14 W15 Hlen Hh' Hl' Hsrc' Hdst'). }
  destruct si as [i|].
  - (* a regular file of 2^64 bytes or more: every word offset is inside it *)
    destruct Hsrc as (off & Hfin & Hbig).
    destruct (wseg_ok_wdef rsegs tbuf (Z_to_bv 64 1024) (trdrec regs mem)
                (target_buf_wseg vt)) as [w Hw].
    destruct (read_file_spec rsegs (trdrec regs mem) model (getr regs 17) i off
                (Fs.fs_ino_data (m_fs model) i) w R17
                ltac:(rewrite Hg0; exact Hfin)
                ltac:(rewrite Hg0; exact Hfin32)
                eq_refl
                ltac:(rewrite Hg1, Hg2; exact Hw)
                ltac:(rewrite Hg2; rewrite u_Z2bv by lia; unfold rw_bytes_max; lia)
                ltac:(rewrite Hg2; rewrite u_Z2bv by lia; lia)
                ltac:(rewrite Hg1, Hg2; apply access_okb_intro;
                      rewrite u_tbuf; rewrite u_Z2bv by lia; unfold TASK_SIZE; lia))
      as [Huniq Hnu].
    split; [exact Hnu|].
    intros eff m' evs Hs.
    destruct (Huniq eff m' evs Hs) as (-> & -> & ->).
    rewrite Hg0, Hg1, Hg2.
    set (chunk := file_read (Fs.fs_ino_data (m_fs model) i) off (Z_to_bv 64 1024)).
    assert (Hc : (1 <= length chunk <= 1024)%nat).
    { unfold chunk. rewrite length_file_read, wtn_1024.
      pose proof (u64_range off) as Hr.
      assert (Hoff : Z.of_nat (word_to_nat off) = bv_unsigned off)
        by (unfold word_to_nat; rewrite Z2Nat.id; lia).
      lia. }
    assert (Hcne : chunk <> []) by (intro He; rewrite He in Hc; cbn in Hc; lia).
    rewrite (delivered_writes_ne tbuf chunk Hcne).
    unfold trdrec. rewrite adv_apply_write.
    match goal with
    | |- context [mkst _ ?p _ _] => replace p with (0x1001220 : word) by bveq
    end.
    split; [reflexivity|]. split; [exact Hh|]. split; [exact Hlazy|].
    apply (Hafter chunk); [exact Hc | exact Hh | exact Hlazy | |].
    + cbn [cp_esrc]. exists (off + len_word chunk). split.
      * model_simp. apply fd_lookup_insert_eq.
      * exact Hbig.
    + apply cp_edst_read; [exact Hne | exact Hdst].
  - (* /dev/urandom: the whole count, from the declared endless stream *)
    destruct Hsrc as (Hfin & Hinf).
    destruct (read_urandom_spec_rec rsegs regs (0x100121c : word) mem trom model fdin false
                tbuf (Z_to_bv 64 1024) R17 R10 R11 R12 Hfin Hfin32 (target_buf_wseg vt)
                ltac:(rewrite u_Z2bv by lia; unfold page_size; lia)
                ltac:(apply access_okb_intro; rewrite u_tbuf; rewrite u_Z2bv by lia;
                      unfold TASK_SIZE; lia)
                Hinf)
      as [Huniq Hnu].
    split; [exact Hnu|].
    intros eff m' evs Hs.
    destruct (Huniq eff m' evs Hs) as (-> & -> & ->).
    change (bv_unsigned (Z_to_bv 64 1024)) with 1024%Z.
    set (chunk := fst (stream_take_z (m_urandom model) 1024)).
    assert (Hcn : Z.of_nat (length chunk) = 1024%Z)
      by (apply stream_take_z_infinite_length; [exact Hinf | lia]).
    assert (Hc : (1 <= length chunk <= 1024)%nat) by lia.
    assert (Hlw : len_word chunk = Z_to_bv 64 1024)
      by (unfold len_word; rewrite Hcn; reflexivity).
    assert (Hcne : chunk <> []) by (intro He; rewrite He in Hcn; cbn in Hcn; lia).
    rewrite (delivered_writes_ne tbuf chunk Hcne).
    unfold trdrec. rewrite adv_apply_write.
    match goal with
    | |- context [mkst _ ?p _ _] => replace p with (0x1001220 : word) by bveq
    end.
    split; [reflexivity|]. split; [exact Hh|]. split; [exact Hlazy|].
    rewrite <- Hlw.
    apply (Hafter chunk); [exact Hc | exact Hh | exact Hlazy | |].
    + cbn [cp_esrc]. split; [exact Hfin|].
      exact (stream_take_z_infinite_rest (m_urandom model) 1024 Hinf).
    + exact Hdst.
Qed.

(* ================================================================= *)
(* From the entry point: prologue, argc test, the two opens           *)
(* ================================================================= *)

Variable inp : ProcInput.
Local Abbreviation av := (in_argv inp).
Local Abbreviation ev := (in_envp inp).
Local Abbreviation fs0 := (in_fs inp).
Hypothesis Hva : valid_argv av.
Hypothesis Hvl : valid_launch inp.

(** The initial stack pointer, the program break and the mmap base
    (ASLR). *)
Variable asp abrk amb : word.

(** The target run's own entry draw, independent of the source's. *)
Variable arnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned asp)%Z.
Hypothesis Hsp_hi : (bv_unsigned asp <= sp_window_hi)%Z.

(** The fifth conjunct of [Run.valid_entry_va] ([create_elf_tables] and
    [setup_arg_pages], fs/binfmt_elf.c and fs/exec.c, Linux v6.18.46,
    commit 1f99e9ab748f): it bounds the entry block, places argv's
    strings and places the stack-store window. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry asp abrk amb arnd) inp.

Local Abbreviation src := (nth 1 (in_argv inp) []).
Local Abbreviation dst := (nth 2 (in_argv inp) []).

Lemma asp_lo_num : (0x7fff80000000 <= bv_unsigned asp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma asp_hi_num : (bv_unsigned asp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Definition argcN : word := len_word av.
Definition wmem : word -> option byte :=
  wrap_mem inp amb target_phdrs (Z_to_bv 64 (Z.of_N 0x1001190)) asp arnd.

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
Proof.
  pose proof (valid_argv_len av Hva).
  unfold argcN, len_word. apply u_Z2bv; lia.
Qed.

Lemma target_bsb_nw : forall entry : word,
  (bv_unsigned asp
   + Z.of_nat (length (entry_stack_image inp amb target_phdrs entry asp arnd)) < 2^64)%Z.
Proof.
  intros entry.
  pose proof (bsb_bound Sv48 inp amb target_phdrs entry asp abrk arnd Hvl Hlau).
  pose proof asp_hi_num. lia.
Qed.

(** Memory after _start's two saves (ra = 0, s0 = 0). *)
Definition fmem : word -> option byte :=
  wbytes (wbytes wmem
    (Z_to_bv 64 (bv_unsigned asp - 8))  (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned asp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

Lemma rdn_fmem_above : forall (a : word) n,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn rsegs fmem a n = rdn rsegs wmem a n.
Proof.
  intros a n Ha Hn. pose proof asp_lo_num. pose proof asp_hi_num. unfold fmem.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; u_norm; lia)).
  reflexivity.
Qed.

Lemma rdn_wmem_stack : forall (a : word) n,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn rsegs wmem a n
  = rdn rsegs (stack_to_mem asp (entry_stack_image inp amb target_phdrs
                                   (Z_to_bv 64 (Z.of_N 0x1001190)) asp arnd)) a n.
Proof. intros a n Ha Hn. unfold wmem. apply rdn_wrap_stack_above; assumption. Qed.

Lemma read_argc_w :
  rdn rsegs wmem asp 8%nat = Some (word_le8 argcN).
Proof.
  pose proof asp_hi_num.
  rewrite rdn_wmem_stack by lia.
  apply read_argc. apply target_bsb_nw.
Qed.

Definition psrc : word := cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1.
Definition pdst : word := cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 2.

Section Ge3.

Hypothesis Hge3 : (3 <= length av)%nat.

Lemma psrc_bounds :
  (bv_unsigned asp <= bv_unsigned psrc)%Z /\
  (bv_unsigned psrc + Z.of_nat (length src) + 1 < 2^64)%Z.
Proof. unfold psrc. exact (argv_ptr_bounds Sv48 inp amb asp abrk arnd 1 Hlau ltac:(lia)). Qed.

Lemma pdst_bounds :
  (bv_unsigned asp <= bv_unsigned pdst)%Z /\
  (bv_unsigned pdst + Z.of_nat (length dst) + 1 < 2^64)%Z.
Proof. unfold pdst. exact (argv_ptr_bounds Sv48 inp amb asp abrk arnd 2 Hlau ltac:(lia)). Qed.

(** argv pointer slots at asp+16 / asp+24. *)
Lemma read_psrc_f :
  rdn rsegs fmem (asp + nat_to_word (8 + 8 * 1)) 8%nat
    = Some (word_le8 psrc).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num.
  rewrite rdn_fmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
  unfold psrc. apply read_argv_ptr_k; [lia | apply target_bsb_nw].
Qed.

Lemma read_pdst_f :
  rdn rsegs fmem (asp + nat_to_word (8 + 8 * 2)) 8%nat
    = Some (word_le8 pdst).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num.
  rewrite rdn_fmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
  unfold pdst. apply read_argv_ptr_k; [lia | apply target_bsb_nw].
Qed.

(** The pathname fetch of each operand ([FileSimWalk.read_cstr_argv]). *)
Lemma target_cstr_src :
  read_cstr (mrb rsegs fmem) psrc
  = if Nat.ltb (length src) path_max then CstrOk src else CstrTooLong.
Proof.
  unfold psrc.
  apply (read_cstr_argv rsegs fmem inp amb target_phdrs (Z_to_bv 64 (Z.of_N 0x1001190))
           asp abrk arnd 1 Hva Hlau ltac:(lia)).
  intros a n Ha Hn. exact (rdn_fmem_above a n Ha Hn).
Qed.

Lemma target_cstr_dst :
  read_cstr (mrb rsegs fmem) pdst
  = if Nat.ltb (length dst) path_max then CstrOk dst else CstrTooLong.
Proof.
  unfold pdst.
  apply (read_cstr_argv rsegs fmem inp amb target_phdrs (Z_to_bv 64 (Z.of_N 0x1001190))
           asp abrk arnd 2 Hva Hlau ltac:(lia)).
  intros a n Ha Hn. exact (rdn_fmem_above a n Ha Hn).
Qed.

(* ================================================================= *)
(* _start + run()'s head, to the first openat ecall                   *)
(* ================================================================= *)

(** run() checks argc and goes straight to
    [openat(AT_FDCWD, argv[1], O_RDONLY, 0)]; each error tail loads its
    own code into a1.  a5 carries the argv base (asp + 8) across both
    openats. *)
Lemma target_to_open1 :
  exists regs1,
    reg_get regs1 1 = (0x10011b0 : word) /\
    reg_get regs1 15 = Z_to_bv 64 (bv_unsigned asp + 8) /\
    bv_unsigned (getr regs1 17) = 56%Z /\
    reg_get regs1 10 = AT_FDCWD /\
    reg_get regs1 11 = psrc /\
    reg_get regs1 12 = Z_to_bv 64 0 /\
    msteps rsegs
      (init_machine_state rsegs 0x1001190 target_phdrs asp amb arnd inp)
      (mkst regs1 (0x10011d8 : word) fmem trom).
Proof.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  pose proof (valid_argv_len av Hva) as HargcLe.
  destruct psrc_bounds as [Hslo Hshi].
  (* 0x1001190 .. 0x10011d8 — 16 instructions in ONE reflective block:
     _start's frame and two zero saves, the argc/argv reads, the [jalr]
     into run(), the not-taken [bgeu] argc check, the argv[1] reload
     and the four openat argument [li]s.  The executor stops at the
     [ecall]; the read script names the two stack loads. *)
  sym_block_ex (target_segs ++ vt)
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 asp)
          (Z_to_bv 64 16781712) wmem trom)
    20%nat [false] [EVar 33; EVar 34] [((2 : reg), EVar 32)]
    [asp] [argcN; psrc] R HR Hms.
  { exists (word_le8 psrc); split;
      [ replace (Z_to_bv 64 (bv_unsigned asp + 16))
          with (asp + nat_to_word (8 + 8 * 1))
          by (rewrite word_add_nat; apply bv_eq; u_norm; lia);
        rewrite <- rdn_fmem_above by (rewrite word_add_nat; u_norm; lia);
        apply read_psrc_f
      | exact (bytes_le_n_to_le_8 _) ]. }
  { apply negb_false_iff; apply Z.ltb_lt; u_norm; rewrite ?u_argcN; lia. }
  { exists (word_le8 argcN); split;
      [ replace (Z_to_bv 64 (bv_unsigned asp + 0)) with asp
          by (apply bv_eq; u_norm; lia);
        exact read_argc_w
      | exact (bytes_le_n_to_le_8 _) ]. }
  { t_ro. }
  { t_ro. }
  (* the block's exit memory IS [fmem]: the two zero saves *)
  match type of Hms with msteps _ _ (mkst _ _ ?M _) => assert (HM : M = fmem) end.
  { unfold fmem. sym_mem_norm.
    rewrite !getr_nz by reg_neq_tac. reflexivity. }
  rewrite HM in Hms. clear HM.
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  7: { rewrite init_mkst. sym_chain Hms. apply mst_refl. }
  all: t_out HR.
Qed.

(** Shared exit tail: from 0x1001268 with a1 = code. *)
Lemma target_err_exit : forall regs mem model code fsv,
  reg_get regs 11 = code -> reg_get regs 1 = (0x10011b0 : word) ->
  (bv_unsigned code < 256)%Z ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x1001268 : word) mem trom) model
    (fun o => o = (code, fsv)).
Proof.
  intros regs mem model code fsv H11 H1 Hc Hfs.
  (* 0x1001268 .. 0x10011b4 — 4 instructions in ONE reflective block:
     [mv a0,a1], the [ret] into _start's tail (the [ra] pin) and the
     exit(93) load.  The executor stops at the [ecall]. *)
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781928) mem trom)
    5%nat (@nil bool) (@nil expr)
    [((1 : reg), ELit 0x10011b0); ((11 : reg), EVar 32)] [code]
    (@nil word) R HR Hms.
  { rewrite getr_nz by reg_neq_tac; rewrite H1; bveq. }
  { rewrite getr_nz by reg_neq_tac; exact H11. }
  eapply tfo_msteps.
  { eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10011b4) eq_refl)
      | apply mst_refl ]. }
  apply tfo_exit_rec.
  - t_out HR.
  - t_out HR.
  - exact Hc.
  - exact Hfs.
Qed.

(** From the open1 errno continuation (0x10011dc): li a1,3, then the
    shared tail — exit 3. *)
Lemma tgt_open1_err_tail : forall regs e mem model fsv,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  reg_get regs 10 = errno_ret e ->
  reg_get regs 1 = (0x10011b0 : word) ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x10011dc : word) mem trom) model
    (fun o => o = (Z_to_bv 64 3, fsv)).
Proof.
  intros regs e mem model fsv He1 He2 H10 H1 Hfs.
  (* the taken [bltz] on the errno return and the error tail's
     [li a1,3] — one reflective block, exact fuel so that it lands on
     the shared exit tail at 0x1001268. *)
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781788) mem trom)
    3%nat [true] (@nil expr) [((10 : reg), EVar 32)] [errno_ret e]
    (@nil word) R HR Hms.
  { apply c_lts_errno; lia. }
  { rewrite getr_nz by reg_neq_tac; exact H10. }
  eapply tfo_msteps; [ exact Hms | ].
  sym_pc_lit.
  apply target_err_exit.
  - t_out HR.
  - t_out HR.
  - rewrite u_Z2bv by lia; lia.
  - exact Hfs.
Qed.

(** From the open2 errno continuation (0x10011fc): exit 4. *)
Lemma tgt_open2_err_tail : forall regs e mem model fsv,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  reg_get regs 10 = errno_ret e ->
  reg_get regs 1 = (0x10011b0 : word) ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x10011fc : word) mem trom) model
    (fun o => o = (Z_to_bv 64 4, fsv)).
Proof.
  intros regs e mem model fsv He1 He2 H10 H1 Hfs.
  (* the taken [bltz] on the errno return and the error tail's
     [li a1,4] — one reflective block, exact fuel so it lands on the
     shared exit tail at 0x1001268. *)
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781820) mem trom)
    2%nat [true] (@nil expr) [((10 : reg), EVar 32)] [errno_ret e]
    (@nil word) R HR Hms.
  { apply c_lts_errno; lia. }
  { rewrite getr_nz by reg_neq_tac; exact H10. }
  eapply tfo_msteps; [ exact Hms | ].
  sym_pc_lit.
  apply target_err_exit.
  - t_out HR.
  - t_out HR.
  - rewrite u_Z2bv by lia; lia.
  - exact Hfs.
Qed.

(** From the read errno continuation (0x1001220): exit 5 (the folder
    read, which answers -EISDIR). *)
Lemma tgt_read_err_tail : forall regs e mem model fsv,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  reg_get regs 10 = errno_ret e ->
  reg_get regs 1 = (0x10011b0 : word) ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x1001220 : word) mem trom) model
    (fun o => o = (Z_to_bv 64 5, fsv)).
Proof.
  intros regs e mem model fsv He1 He2 H10 H1 Hfs.
  (* the taken [bltz] on the errno return and the error tail's
     [li a1,5] — one reflective block, exact fuel so it lands on the
     shared exit tail at 0x1001268. *)
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781856) mem trom)
    3%nat [true] (@nil expr) [((10 : reg), EVar 32)] [errno_ret e]
    (@nil word) R HR Hms.
  { apply c_lts_errno; lia. }
  { rewrite getr_nz by reg_neq_tac; exact H10. }
  eapply tfo_msteps; [ exact Hms | ].
  sym_pc_lit.
  apply target_err_exit.
  - t_out HR.
  - t_out HR.
  - rewrite u_Z2bv by lia; lia.
  - exact Hfs.
Qed.

(** After the first open succeeds: from 0x10011dc to the second openat
    ecall (bltz ft; mv a4,a0; ld a1,16(a5); the four li's; ecall). *)
Lemma tgt_to_open2 : forall regs fd,
  reg_get regs 10 = fd -> (bv_unsigned fd < 2 ^ 31)%Z ->
  reg_get regs 15 = Z_to_bv 64 (bv_unsigned asp + 8) ->
  reg_get regs 1 = (0x10011b0 : word) ->
  exists regs2,
    bv_unsigned (getr regs2 17) = 56%Z /\
    reg_get regs2 10 = AT_FDCWD /\
    reg_get regs2 11 = pdst /\
    reg_get regs2 12 = Z_to_bv 64 577 /\
    reg_get regs2 14 = fd /\
    reg_get regs2 1 = (0x10011b0 : word) /\
    msteps rsegs (mkst regs (0x10011dc : word) fmem trom)
      {| ms_regs := regs2; ms_fregs := fp_regs; ms_pc_val := (0x10011f8 : word);
         ms_svc_pending := Some (getr regs2 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := fmem; ms_rom := trom |}.
Proof.
  intros regs fd H10 Hlt H15 H1.
  pose proof asp_lo_num. pose proof asp_hi_num.
  destruct pdst_bounds as [Hplo Hphi].
  (* 0x10011dc .. 0x10011f8 — 7 instructions in ONE reflective block:
     the not-taken [bltz], [mv a4,a0], the argv[2] reload off the
     pinned argv base and the four openat argument [li]s.  The
     executor stops at the [ecall]. *)
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781788) fmem trom)
    8%nat [false] [EVar 34]
    [((10 : reg), EVar 32); ((15 : reg), EVar 33)]
    [fd; Z_to_bv 64 (bv_unsigned asp + 8)] [pdst] R HR Hms.
  { exists (word_le8 pdst); split;
      [ replace (Z_to_bv 64 (bv_unsigned asp + 24))
          with (asp + nat_to_word (8 + 8 * 2))
          by (rewrite word_add_nat; apply bv_eq; u_norm; lia);
        apply read_pdst_f
      | exact (bytes_le_n_to_le_8 _) ]. }
  { apply c_lts_pos_0; lia. }
  { rewrite getr_nz by reg_neq_tac; exact H10. }
  { rewrite getr_nz by reg_neq_tac; exact H15. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  7: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10011f8) eq_refl)
      | apply mst_refl ]. }
  all: t_out HR.
Qed.

(** After the second open succeeds: from 0x10011fc to the loop head. *)
Lemma tgt_open2_to_loop : forall regs fd fd2,
  reg_get regs 10 = fd2 -> (bv_unsigned fd2 < 2 ^ 31)%Z ->
  reg_get regs 14 = fd ->
  reg_get regs 1 = (0x10011b0 : word) ->
  exists regsH,
    reg_get regsH 1 = (0x10011b0 : word) /\
    reg_get regsH 13 = fd2 /\ reg_get regsH 14 = fd /\
    reg_get regsH 15 = tbuf /\
    msteps rsegs (mkst regs (0x10011fc : word) fmem trom)
                 (mkst regsH (0x100120c : word) fmem trom).
Proof.
  intros regs fd fd2 H10 Hlt2 H14 H1.
  (* 0x10011fc .. 0x100120c — 4 instructions in ONE reflective block:
     the not-taken [bltz], [mv a3,a0] and the [lui]/[addi] pair that
     materializes the buffer address.  Exact fuel: the next
     instruction is the loop head itself. *)
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781820) fmem trom)
    4%nat [false] (@nil expr) [((10 : reg), EVar 32)] [fd2]
    (@nil word) R HR Hms.
  { apply c_lts_pos_0; lia. }
  { rewrite getr_nz by reg_neq_tac; exact H10. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  5: { eapply msteps_trans; [ exact Hms | ]. sym_pc_lit. apply mst_refl. }
  all: t_out HR.
Qed.

(* ================================================================= *)
(* The result                                                         *)
(* ================================================================= *)

(** argc >= 3: the same outcome set as the source's. *)
Lemma target_ge3 : forall m0,
  m_fds m0 = fds0 -> m_fs m0 = fs0 -> m_cwd m0 = in_cwd inp ->
  m_urandom m0 = in_urandom inp ->
  m_halted m0 = None -> m_vm_lazy m0 = [] ->
  stream_infinite (in_urandom inp) ->
  (op_walked src = true -> open_answered true fs0 (in_cwd inp) src) ->
  (op_walked dst = true -> open_answered false fs0 (in_cwd inp) dst) ->
  to_floop rsegs (init_machine_state rsegs 0x1001190 target_phdrs asp amb arnd inp) m0
    (cp_outcomes fs0 (in_cwd inp) src dst).
Proof.
  intros m0 Hfds Hfs Hcwd Hur Hh Hlazy Hinf Hans1 Hans2.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  destruct target_to_open1
    as (regs1 & H1 & H15 & H17 & H10 & H11 & H12 & Hms).
  eapply tfl_msteps.
  { eapply msteps_trans; [exact Hms|].
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10011d8) eq_refl)
      | apply mst_refl ]. }
  apply (tfl_open_operand_rec rsegs regs1 (0x10011d8 : word) fmem m0 src true
           (fun o => o = (Z_to_bv 64 3, fs0))
           (fun o => match open_arm true fs0 (in_cwd inp) src with
                     | inl (fe_s, _) =>
                         o = (Z_to_bv 64 4, fs0)
                         \/ (op_walked dst = true /\
                             match open_arm false fs0 (in_cwd inp) dst with
                             | inl (fe_d, ofs) => cp_copy (cp_fs1 fs0 ofs) fe_s fe_d o
                             | inr _ => False
                             end)
                     | inr _ => False
                     end)).
  - exact H17.
  - exact H10.
  - exact H12.
  - rewrite H11. exact target_cstr_src.
  - intros _. apply proc_self_fd_no_slash.
    exact (valid_argv_no_slash av 0 Hva ltac:(lia)).
  - intros Hw. rewrite Hfs, Hcwd. exact (Hans1 Hw).
  - rewrite Hfds. exact cp_free1.
  - exact Hh.
  - exact Hlazy.
  - (* the first open answers an errno: exit 3 *)
    intros r Hr. tfnorm_pc.
    destruct (addr_is_error_b_errno r Hr) as (e & He1 & He2 & ->).
    apply (tgt_open1_err_tail (regupd regs1 10 (errno_ret e)) e fmem m0 fs0).
    + lia.
    + lia.
    + regupd_resolve; reflexivity.
    + regupd_resolve; exact H1.
    + exact Hfs.
  - (* a descriptor on the source operand *)
    intros fe_s ofs1 Harm1.
    rewrite Hfs, Hcwd in Harm1.
    destruct (open_arm_rd_cases _ _ _ _ _ Harm1) as [-> Hkind].
    apply (tfl_equiv rsegs _ _
             (fun o => o = (Z_to_bv 64 4, fs0)
                       \/ (op_walked dst = true /\
                           match open_arm false fs0 (in_cwd inp) dst with
                           | inl (fe_d, ofs) => cp_copy (cp_fs1 fs0 ofs) fe_s fe_d o
                           | inr _ => False
                           end))).
    2:{ intro o. rewrite Harm1. split; intro Ho; exact Ho. }
    assert (Hfd1 : alloc_fd (m_fds m0) = Z_to_bv 64 3) by (rewrite Hfds; exact cp_fd1).
    rewrite Hfd1.
    tflnorm_pc.
    destruct (tgt_to_open2 (regupd regs1 10 (Z_to_bv 64 3)) (Z_to_bv 64 3))
      as (regs2 & J17 & J10 & J11 & J12 & J14 & J1 & Hms2);
      [ regupd_resolve; reflexivity | vm_compute; reflexivity
      | regupd_resolve; exact H15 | regupd_resolve; exact H1 | ].
    eapply tfl_msteps; [exact Hms2|].
    set (m1 := open_model m0 (Z_to_bv 64 3) fe_s None).
    assert (Hm1fds : m_fds m1 = fd_insert fds0 (Z_to_bv 64 3) fe_s)
      by (unfold m1; rewrite open_model_fds, Hfds; reflexivity).
    assert (Hm1fs : m_fs m1 = fs0) by (unfold m1; rewrite open_model_fs; exact Hfs).
    assert (Hm1cwd : m_cwd m1 = in_cwd inp)
      by (unfold m1; rewrite open_model_cwd; exact Hcwd).
    assert (Hm1ur : m_urandom m1 = in_urandom inp)
      by (unfold m1; rewrite open_model_urandom; exact Hur).
    assert (Hm1h : m_halted m1 = None)
      by (unfold m1; rewrite open_model_halted; exact Hh).
    assert (Hm1l : m_vm_lazy m1 = [])
      by (unfold m1; rewrite open_model_lazy; exact Hlazy).
    apply (tfl_open_operand_rec rsegs regs2 (0x10011f8 : word) fmem m1 dst false
             (fun o => o = (Z_to_bv 64 4, fs0))
             (fun o => match open_arm false fs0 (in_cwd inp) dst with
                       | inl (fe_d, ofs) => cp_copy (cp_fs1 fs0 ofs) fe_s fe_d o
                       | inr _ => False
                       end)).
    + exact J17.
    + exact J10.
    + exact J12.
    + rewrite J11. exact target_cstr_dst.
    + intros _. apply proc_self_fd_no_slash.
      exact (valid_argv_no_slash av 1 Hva ltac:(lia)).
    + intros Hw. rewrite Hm1fs, Hm1cwd. exact (Hans2 Hw).
    + rewrite Hm1fds. exact (cp_free2 fe_s).
    + exact Hm1h.
    + exact Hm1l.
    + (* the second open answers an errno: exit 4 *)
      intros r Hr. tfnorm_pc.
      destruct (addr_is_error_b_errno r Hr) as (e & He1 & He2 & ->).
      apply (tgt_open2_err_tail (regupd regs2 10 (errno_ret e)) e fmem m1 fs0).
      * lia.
      * lia.
      * regupd_resolve; reflexivity.
      * regupd_resolve; exact J1.
      * exact Hm1fs.
    + (* both descriptors: the copy *)
      intros fe_d ofs2 Harm2.
      rewrite Hm1fs, Hm1cwd in Harm2.
      apply (tfl_equiv rsegs _ _ (cp_copy (cp_fs1 fs0 ofs2) fe_s fe_d)).
      2:{ intro o. rewrite Harm2. split; intro Ho; exact Ho. }
      assert (Hfd2 : alloc_fd (m_fds m1) = Z_to_bv 64 4)
        by (rewrite Hm1fds; exact (cp_fd2 fe_s)).
      rewrite Hfd2.
      set (m2 := open_model m1 (Z_to_bv 64 4) fe_d ofs2).
      assert (Hm2fds : m_fds m2 = fd_insert (fd_insert fds0 (Z_to_bv 64 3) fe_s)
                                    (Z_to_bv 64 4) fe_d)
        by (unfold m2; rewrite open_model_fds, Hm1fds; reflexivity).
      assert (Hm2fs : m_fs m2 = cp_fs1 fs0 ofs2)
        by (unfold m2, cp_fs1; rewrite open_model_fs, Hm1fs; reflexivity).
      assert (Hm2ur : m_urandom m2 = in_urandom inp)
        by (unfold m2; rewrite open_model_urandom; exact Hm1ur).
      assert (Hm2h : m_halted m2 = None)
        by (unfold m2; rewrite open_model_halted; exact Hm1h).
      assert (Hm2l : m_vm_lazy m2 = [])
        by (unfold m2; rewrite open_model_lazy; exact Hm1l).
      assert (Hl3 : fd_lookup (m_fds m2) (Z_to_bv 64 3) = Some fe_s)
        by (rewrite Hm2fds; vm_compute; reflexivity).
      assert (Hl4 : fd_lookup (m_fds m2) (Z_to_bv 64 4) = Some fe_d)
        by (rewrite Hm2fds; vm_compute; reflexivity).
      assert (Hdok : cp_dst_ok fe_d (cp_fs1 fs0 ofs2))
        by exact (cp_dst_ok_arm _ _ _ _ _ Harm2).
      tflnorm_pc.
      destruct (tgt_open2_to_loop (regupd regs2 10 (Z_to_bv 64 4))
                  (Z_to_bv 64 3) (Z_to_bv 64 4))
        as (regsH & K1 & K13 & K14 & K15 & HmsH);
        [ regupd_resolve; reflexivity | vm_compute; reflexivity
        | regupd_resolve; exact J14 | regupd_resolve; exact J1 | ].
      eapply tfl_msteps; [exact HmsH|].
      assert (Haok : access_okb tbuf (bv_unsigned (Z_to_bv 64 1024)) = true).
      { apply access_okb_intro. rewrite u_tbuf, u_Z2bv by lia. unfold TASK_SIZE. lia. }
      destruct Hkind as [(i & ->) | [(k & ->) | [-> | ->]]].
      * (* a regular file *)
        destruct (Z_lt_le_dec (Z.of_nat (length (Fs.fs_ino_data (cp_fs1 fs0 ofs2) i)))
                    (2^64)) as [Hsmall | Hbig].
        -- (* a word offset reaches its end: the copy ends *)
           apply to_floop_of_fout.
           apply (tfo_equiv rsegs _ _
                    (fun o => o = (Z_to_bv 64 0,
                                   cp_copied fe_d (cp_fs1 fs0 ofs2)
                                     (Fs.fs_ino_data (cp_fs1 fs0 ofs2) i)))).
           2:{ intro o. cbn [cp_copy]. split.
               - intros [_ Ho]. exact Ho.
               - intros Ho. split; [exact Hsmall | exact Ho]. }
           apply (target_loop (cp_fs1 fs0 ofs2) i (Fs.fs_ino_data (cp_fs1 fs0 ofs2) i)
                    (Z_to_bv 64 3) (Z_to_bv 64 4) fe_d eq_refl tfd3_ne_fd4
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                    Hsmall Hdok
                    (S (length (Fs.fs_ino_data (cp_fs1 fs0 ofs2) i))) 0%nat).
           ++ lia.
           ++ lia.
           ++ exact (conj K1 (conj K13 (conj K14 K15))).
           ++ unfold tMI.
              refine (conj Hm2h (conj Hm2l (conj Hl3 (conj _ _)))).
              ** rewrite Hl4.
                 destruct Hdok as [(j & Hj & _) | [Hj | Hj]]; rewrite Hj; reflexivity.
              ** rewrite Hm2fs.
                 destruct Hdok as [(j & Hj & _) | [Hj | Hj]]; rewrite Hj; reflexivity.
        -- (* 2^64 bytes or more: copied forever *)
           destruct (tgt_head_to_read regsH fmem (Z_to_bv 64 3) (Z_to_bv 64 4)
                       K1 K13 K14 K15)
             as (regsR & R17 & R10 & R11 & R12 & R1 & R13 & R14 & R15 & HmsR).
           eapply tfl_msteps; [exact HmsR|].
           apply (tfl_loop rsegs _ _ (fpath rsegs tAnchor)).
           ++ exact (fsilent_fpath rsegs tAnchor tgt_endless_anchored).
           ++ apply fp_anchor.
              exists (Z_to_bv 64 3), (Z_to_bv 64 4), regsR, fmem, m2.
              split; [exact tfd3_ne_fd4|].
              split; [fd32_ok|]. split; [fd32_ok|].
              split; [unfold tRpins; tauto|].
              split; [|reflexivity].
              split; [exact Hm2h|]. split; [exact Hm2l|].
              exists (Some i). split.
              ** cbn [cp_esrc]. exists (Z_to_bv 64 0). split; [exact Hl3|].
                 rewrite Hm2fs. exact Hbig.
              ** apply (cp_edst_open (Z_to_bv 64 4) m2 fe_d (Some i) Hl4).
                 --- rewrite Hm2fs. exact Hdok.
                 --- intros j Hj Hij. injection Hij as <-.
                     rewrite Hm2fs in Hj. rewrite Hj in Hbig. cbn in Hbig. lia.
           ++ intros o Ho. cbn [cp_copy] in Ho. destruct Ho as [Hlt _]. lia.
      * (* a folder: -EISDIR, exit 5 *)
        apply to_floop_of_fout.
        destruct (tgt_head_to_read regsH fmem (Z_to_bv 64 3) (Z_to_bv 64 4)
                    K1 K13 K14 K15)
          as (regsR & R17 & R10 & R11 & R12 & R1 & R13 & R14 & R15 & HmsR).
        eapply tfo_msteps; [exact HmsR|].
        eapply tfo_read_dir_rec.
        -- exact R17.
        -- exact R10.
        -- exact R11.
        -- exact R12.
        -- exact Hl3.
        -- fd32_ok.
        -- exact Haok.
        -- exact Hm2h.
        -- exact Hm2l.
        -- tfnorm_pc.
           apply (tfo_equiv rsegs _ _ (fun o => o = (Z_to_bv 64 5, m_fs m2))).
           2:{ intro o. rewrite Hm2fs. cbn [cp_copy]. split; intro Ho; exact Ho. }
           apply (tgt_read_err_tail (regupd regsR 10 (errno_ret EISDIR)) EISDIR fmem m2
                    (m_fs m2)).
           ++ unfold EISDIR; lia.
           ++ unfold EISDIR; lia.
           ++ regupd_resolve; reflexivity.
           ++ regupd_resolve; exact R1.
           ++ reflexivity.
      * (* /dev/null: the first read answers 0, both closes, exit 0 *)
        apply to_floop_of_fout.
        destruct (tgt_head_to_read regsH fmem (Z_to_bv 64 3) (Z_to_bv 64 4)
                    K1 K13 K14 K15)
          as (regsR & R17 & R10 & R11 & R12 & R1 & R13 & R14 & R15 & HmsR).
        eapply tfo_msteps; [exact HmsR|].
        eapply tfo_read_null_rec.
        -- exact R17.
        -- exact R10.
        -- exact R11.
        -- exact R12.
        -- exact Hl3.
        -- fd32_ok.
        -- exact Haok.
        -- exact Hm2h.
        -- exact Hm2l.
        -- tfnorm_pc.
           apply (tfo_equiv rsegs _ _ (fun o => o = (Z_to_bv 64 0, m_fs m2))).
           2:{ intro o. rewrite Hm2fs. cbn [cp_copy]. split; intro Ho; exact Ho. }
           apply (tgt_eof_tail (regupd regsR 10 (Z_to_bv 64 0)) fmem m2
                    (Z_to_bv 64 3) (Z_to_bv 64 4) (FdDevNull true false) fe_d (m_fs m2)).
           ++ regupd_resolve; exact R1.
           ++ regupd_resolve; reflexivity.
           ++ regupd_resolve; exact R13.
           ++ regupd_resolve; exact R14.
           ++ exact tfd3_ne_fd4.
           ++ vm_compute; reflexivity.
           ++ vm_compute; reflexivity.
           ++ exact Hl3.
           ++ exact Hl4.
           ++ exact Hm2h.
           ++ exact Hm2l.
           ++ reflexivity.
      * (* /dev/urandom: copied forever *)
        destruct (tgt_head_to_read regsH fmem (Z_to_bv 64 3) (Z_to_bv 64 4)
                    K1 K13 K14 K15)
          as (regsR & R17 & R10 & R11 & R12 & R1 & R13 & R14 & R15 & HmsR).
        eapply tfl_msteps; [exact HmsR|].
        apply (tfl_loop rsegs _ _ (fpath rsegs tAnchor)).
        -- exact (fsilent_fpath rsegs tAnchor tgt_endless_anchored).
        -- apply fp_anchor.
           exists (Z_to_bv 64 3), (Z_to_bv 64 4), regsR, fmem, m2.
           split; [exact tfd3_ne_fd4|].
           split; [fd32_ok|]. split; [fd32_ok|].
           split; [unfold tRpins; tauto|].
           split; [|reflexivity].
           split; [exact Hm2h|]. split; [exact Hm2l|].
           exists None. split.
           ++ cbn [cp_esrc]. split; [exact Hl3|]. rewrite Hm2ur. exact Hinf.
           ++ apply (cp_edst_open (Z_to_bv 64 4) m2 fe_d None Hl4).
              ** rewrite Hm2fs. exact Hdok.
              ** intros j _ Hij. discriminate Hij.
        -- intros o Ho. exact Ho.
    + (* the outcome set at the second open *)
      intro o. rewrite Hm1fs, Hm1cwd. unfold open_ok.
      destruct (open_arm false fs0 (in_cwd inp) dst) as [[fe_d ofs]|e]; cbv beta iota.
      * split.
        -- intros [Ho | (Hw & Ho)];
             [ left; exact Ho | right; split; [exact Hw | split; [reflexivity | exact Ho]] ].
        -- intros [Ho | (Hw & _ & Ho)]; [ left; exact Ho | right; split; [exact Hw | exact Ho] ].
      * split.
        -- intros [Ho | (_ & Ho)]; [ left; exact Ho | contradiction ].
        -- intros [Ho | (_ & Hf & _)]; [ left; exact Ho | discriminate Hf ].
  - (* the outcome set at the first open *)
    intro o. unfold cp_outcomes, open_ok. rewrite Hfs, Hcwd.
    destruct (open_arm true fs0 (in_cwd inp) src) as [[fe ofs]|e]; cbv beta iota.
    + split.
      * intros [Ho | (Hw & Ho)];
          [ left; exact Ho | right; split; [exact Hw | split; [reflexivity | exact Ho]] ].
      * intros [Ho | (Hw & _ & Ho)]; [ left; exact Ho | right; split; [exact Hw | exact Ho] ].
    + split.
      * intros [Ho | (_ & Ho)]; [ left; exact Ho | contradiction ].
      * intros [Ho | (_ & Hf & _)]; [ left; exact Ho | discriminate Hf ].
Qed.

End Ge3.

(* ================================================================= *)
(* argc < 3: no output, exit 2 (CatSim shape)                          *)
(* ================================================================= *)

Lemma target_wexit_lt3 : (length av < 3)%nat ->
  to_wexit rsegs
    (init_machine_state rsegs 0x1001190 target_phdrs asp amb arnd inp)
    [] (Z_to_bv 64 2).
Proof.
  intros Hlt3.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  pose proof (valid_argv_len av Hva) as HargcLe.
  rewrite init_mkst. norm_pc.
  (* addi sp,sp,-16 *)
  stepiv (TFv TF_1001190) TD_1001190 (Z_to_bv 64 (bv_unsigned asp - 16))
    ltac:(getr_resolve; sp_norm; first [ reflexivity | f_equal; lia ]).
  (* sd ra,8(sp) *)
  step_intro;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned asp - 8))
                             (v := Z_to_bv 64 0);
      [ exact (TFv TF_1001194) | reflexivity | exact TD_1001194
      | getr_resolve; regupd_resolve; sp_norm;
        first [ reflexivity | f_equal; lia | apply bv_eq; u_norm; lia ]
      | getr_resolve; regupd_resolve; reflexivity
      | t_ro ]
    | step_simpl ].
  (* sd s0,0(sp) *)
  step_intro;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned asp - 16))
                             (v := Z_to_bv 64 0);
      [ exact (TFv TF_1001198) | reflexivity | exact TD_1001198
      | getr_resolve; regupd_resolve; sp_norm;
        first [ reflexivity | f_equal; lia | apply bv_eq; u_norm; lia ]
      | getr_resolve; regupd_resolve; reflexivity
      | t_ro ]
    | step_simpl ].
  (* addi s0,sp,16 *)
  stepiv (TFv TF_100119c) TD_100119c asp
    ltac:(getr_resolve; regupd_resolve; sp_norm; apply bv_eq; u_norm; lia).
  (* ld a0,0(s0): argc *)
  step_intro;
    [ reflexivity
    | eapply step_ld with (bs := word_le8 argcN) (v := argcN);
      [ exact (TFv TF_10011a0) | reflexivity | exact TD_10011a0
      | match goal with |- rdn _ _ ?ad _ = _ =>
          replace ad with asp
            by (getr_resolve; regupd_resolve; rewrite v_addi_0; reflexivity)
        end;
        repeat (rewrite rdn_wbytes_disjoint
                  by (rewrite ?length_N_to_le_bytes; u_norm; lia));
        fold wmem; apply read_argc_w
      | exact (bytes_le_n_to_le_8 _) ]
    | step_simpl ].
  (* addi a1,s0,8 *)
  stepiv (TFv TF_10011a4) TD_10011a4 (Z_to_bv 64 (bv_unsigned asp + 8))
    ltac:(getr_resolve; regupd_resolve; sp_norm;
          first [ reflexivity | f_equal; lia ]).
  (* auipc ra,0 *)
  stepi (TFv TF_10011a8) TD_10011a8.
  (* jalr ra,16(ra) *)
  stepjr (TFv TF_10011ac) TD_10011ac (0x10011a8 : word)
    ltac:(getr_resolve; regupd_resolve; bveq).
  (* mv a5,a1 : the argv base *)
  stepiv (TFv TF_10011b8) TD_10011b8 (Z_to_bv 64 (bv_unsigned asp + 8))
    ltac:(getr_resolve; regupd_resolve; imm_norm; apply v_addi_0).
  (* li a1,2 *)
  stepiv (TFv TF_10011bc) TD_10011bc (Z_to_bv 64 2) ltac:(getr_resolve; bveq).
  (* bgeu a1,a0 taken (argc <= 2) -> the exit tail at 0x1001268 *)
  step_intro;
    [ reflexivity
    | eapply step_bgeu_tk;
      [ exact (TFv TF_10011c0) | reflexivity | exact TD_10011c0
      | getr_resolve; regupd_resolve;
        rewrite c_ltu_ltb; apply Z.ltb_ge;
        u_norm; rewrite ?u_argcN; lia ]
    | norm_pc ].
  (* mv a0,a1 (= 2) *)
  stepiv (TFv TF_1001268) TD_1001268 (Z_to_bv 64 2)
    ltac:(getr_resolve; regupd_resolve; imm_norm; apply v_addi_0).
  (* ret -> 0x10011b0 *)
  stepjr (TFv TF_100126c) TD_100126c (0x10011b0 : word)
    ltac:(getr_resolve; regupd_resolve; bveq).
  (* li a7,93 *)
  stepiv (TFv TF_10011b0) TD_10011b0 (Z_to_bv 64 93) ltac:(getr_resolve; bveq).
  (* ecall -> exit 2 *)
  step_intro;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10011b4) eq_refl) | ].
  apply tw_exit_coden.
  - getr_resolve; regupd_resolve; vm_compute; reflexivity.
  - regupd_resolve; reflexivity.
  - vm_compute; reflexivity.
Qed.

End TargetProof.
