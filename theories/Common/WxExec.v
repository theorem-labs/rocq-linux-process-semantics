(** * Common.WxExec — step lemmas for code in a WRITABLE executable (w+x) segment

    PROOF-SIDE FILE (not part of the trusted specification).

    [RiscvSemantics.step] fetches an instruction from an immutable
    (x and not w) segment with the static [fetch_word], and from a
    WRITABLE executable (w+x) segment — the merged RWX layout GNU ld's
    default [-z noseparate-code] produces — with the overlay-aware
    [fetch_word_ov], which reads the writable overlay first and the
    segment image underneath.  The per-example generated
    fetch facts for a w+x image are stated over the STATIC projection
    [fetch_word_wx] (a pure function of the snapshot, closed by
    [vm_refl]); this file supplies the bridge that turns them into
    [fetch_word_ov] facts, and the per-instruction step lemmas that
    consume them:

    - [mem_clear m lo hi] — the FRAME INVARIANT a w+x example's proof
      carries: the overlay misses the whole [.text] range [lo, hi).
      Established at [init_machine_state] ([mem_clear_wrap]: the
      initial overlay is the stack image, far above every loaded
      segment) and preserved by each store the program makes
      ([mem_clear_wbytes]: the store target is disjoint from the text
      range — data stores in the same RWX segment are fine, only a
      store OVER the code would break it, i.e. self-modifying code is
      exactly what the invariant excludes).
    - [fetch_word_ov_of_wx] — under the invariant, the overlay-aware
      fetch of an address inside the clear range rewrites to the static
      [fetch_word_wx], so the generated lemma closes the fetch.
    - [wx_fetch]/[wx_fetch_intro] — the two facts a step needs
      ([fetch_word] declines: nothing immutable-executable covers the
      pc; [fetch_word_ov] succeeds), packed as one premise so the
      per-instruction lemmas below stay one-premise-per-concern.
      [fetch_word_none_no_ro_exec] discharges the first over a whole
      image at once: an image with NO immutable executable segment
      (e.g. the single-RWX-segment layout) never satisfies the static
      fetch anywhere.
    - [step_*_wx] — mirrors of the [PropExec]/[SeqExec]/[MmapSim]
      per-instruction step lemmas with the fetch premise replaced by
      [wx_fetch]; conclusions are IDENTICAL, so everything downstream
      of a step (chain relations, register/memory normalization,
      [rdn] reads) is shared with the immutable-code examples.

    Only the instruction shapes the w+x example actually walks are
    mirrored; extend the family as new w+x examples need more. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec MmapSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

Section WithFP1.
Context {fx : FPState}.

(* ################################################################# *)
(* find_segment inversion                                            *)
(* ################################################################# *)

Lemma find_segment_in : forall segs (a n : Z) seg,
  find_segment segs a n = Some seg -> In seg segs.
Proof.
  induction segs as [|s rest IH]; intros a n seg H; [discriminate|].
  cbn in H. destruct (_ && _)%bool.
  - injection H as <-. left; reflexivity.
  - right; eauto.
Qed.

Lemma find_segment_range : forall segs (a n : Z) seg,
  find_segment segs a n = Some seg ->
  (Z.of_N (seg_base seg) <= a)%Z /\
  (a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.
Proof.
  induction segs as [|s rest IH]; intros a n seg H; [discriminate|].
  cbn in H.
  destruct (Z.leb (Z.of_N (seg_base s)) a) eqn:Hlo;
    destruct (Z.leb (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:Hhi;
    cbn in H; eauto.
  injection H as <-. split; [apply Z.leb_le, Hlo | apply Z.leb_le, Hhi].
Qed.

(* ################################################################# *)
(* The static fetch declines everywhere on an all-w+x image           *)
(* ################################################################# *)

(** No segment of the image is executable WITHOUT being writable — true
    of the single-RWX-segment layout, checked once per image by
    [vm_compute].  Then the static [fetch_word] (gate [x /\ ~w])
    declines at EVERY address, which is the first half of [wx_fetch]
    at every step, discharged once instead of per pc. *)
Definition no_ro_exec (segs : list Segment) : bool :=
  forallb (fun s => negb (seg_executable s && negb (seg_writable s))) segs.

Lemma code_read_none_no_ro_exec : forall segs (a : word) n,
  no_ro_exec segs = true ->
  code_read segs a n = None.
Proof.
  intros segs a n Hro. unfold code_read.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hfs;
    [|reflexivity].
  apply find_segment_in in Hfs.
  eapply forallb_forall in Hro; [|exact Hfs].
  destruct (seg_executable seg && negb (seg_writable seg)); [discriminate|].
  reflexivity.
Qed.

Lemma fetch_word_none_no_ro_exec : forall segs (pc : word),
  no_ro_exec segs = true ->
  fetch_word segs pc = None.
Proof.
  intros segs pc Hro. unfold fetch_word.
  destruct (negb _); [reflexivity|].
  rewrite code_read_none_no_ro_exec by exact Hro. reflexivity.
Qed.

(* ################################################################# *)
(* The frame invariant: the overlay misses the text range            *)
(* ################################################################# *)

Definition mem_clear (m : word -> option byte) (lo hi : Z) : Prop :=
  forall a : word, (lo <= bv_unsigned a < hi)%Z -> m a = None.

(** Established at [init_machine_state]: the initial overlay is the
    stack image plus its zero window, both inside the [valid_sp] ASLR
    window far above every loaded segment. *)
Lemma mem_clear_wrap : forall ph (sp : word) argv envp lo hi uid hw rnd,
  (hi <= bv_unsigned sp - stack_max_size)%Z ->
  mem_clear (wrap_mem ph sp argv envp uid hw rnd) lo hi.
Proof.
  intros ph sp argv envp lo hi uid hw rnd Hhi a Ha.
  pose proof (stack_window_lo_ge sp (entry_stack_image ph sp argv envp uid hw rnd)) as Hge.
  unfold wrap_mem, stack_to_mem.
  unfold stack_max_size in Hhi.
  assert (Hblo : Z.leb (bv_unsigned sp) (bv_unsigned a) = false)
    by (apply Z.leb_gt; lia).
  rewrite Hblo.
  assert (Hwlo : Z.leb (stack_window_lo sp (entry_stack_image ph sp argv envp uid hw rnd))
                       (bv_unsigned a) = false)
    by (apply Z.leb_gt; unfold stack_max_size in *; lia).
  rewrite Hwlo. reflexivity.
Qed.

(** Preserved by a store whose target range is disjoint from the clear
    range — every store an ordinary (non-self-modifying) w+x program
    makes.  The no-wrap bound keeps the write walk from wrapping into
    the range from above. *)
Lemma mem_clear_wbytes : forall m (addr : word) bs lo hi,
  mem_clear m lo hi ->
  (hi <= bv_unsigned addr \/ bv_unsigned addr + Z.of_nat (length bs) <= lo)%Z ->
  (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  mem_clear (wbytes m addr bs) lo hi.
Proof.
  intros m addr bs lo hi Hcc Hdisj Hnw a Ha.
  destruct Hdisj as [Habove | Hbelow].
  - rewrite wbytes_below by lia. apply Hcc; lia.
  - rewrite wbytes_above by lia. apply Hcc; lia.
Qed.

(** [word_to_le_bytes n v] really is [n] bytes (feeds the length
    side conditions of [mem_clear_wbytes]). *)
Lemma length_Z_to_le_bytes : forall n z, length (Z_to_le_bytes n z) = n.
Proof.
  induction n as [|n IH]; intro z; [reflexivity|].
  cbn [Z_to_le_bytes length]. now rewrite IH.
Qed.

Lemma length_word_to_le_bytes : forall n (v : word),
  length (word_to_le_bytes n v) = n.
Proof. intros. apply length_Z_to_le_bytes. Qed.

(* ################################################################# *)
(* The fetch bridge: overlay-aware fetch = static fetch under clear    *)
(* ################################################################# *)

(** Under a clear overlay, the per-segment overlay-first read is the
    static image read. *)
Lemma seg_ov_read_bytes_static : forall n m seg (addr : word),
  (forall a : word,
     (bv_unsigned addr <= bv_unsigned a < bv_unsigned addr + Z.of_nat n)%Z ->
     m a = None) ->
  (bv_unsigned addr + Z.of_nat n <= 2^64)%Z ->
  (Z.of_N (seg_base seg) <= bv_unsigned addr)%Z ->
  seg_ov_read_bytes m seg addr n
  = segment_read_bytes seg.(seg_bytes)
      (Z.to_N (bv_unsigned addr - Z.of_N (seg_base seg))) n.
Proof.
  induction n as [|n IH]; intros m seg addr Hclear Hnw Hbase; [reflexivity|].
  cbn [seg_ov_read_bytes segment_read_bytes].
  rewrite Hclear by (cbn [Z.of_nat]; lia).
  destruct (segment_byte_at (seg_bytes seg)
              (Z.to_N (bv_unsigned addr - Z.of_N (seg_base seg))))
    as [b|] eqn:Hb; [|reflexivity].
  destruct n as [|n'].
  - cbn [seg_ov_read_bytes segment_read_bytes]. reflexivity.
  - assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
      by (apply u_add1; lia).
    rewrite IH by (rewrite Hu1; try lia;
                   intros a Ha; apply Hclear; lia).
    replace (Z.to_N (bv_unsigned (addr + 1) - Z.of_N (seg_base seg)))
      with (Z.to_N (bv_unsigned addr - Z.of_N (seg_base seg)) + 1)%N
      by (rewrite Hu1; lia).
    reflexivity.
Qed.

(** The bridge: an address whose 4 fetched bytes lie inside the clear
    range fetches through the overlay exactly what the static w+x
    projection says — so a generated [fetch_word_wx] lemma closes the
    overlay-aware fetch at every step. *)
Lemma fetch_word_ov_of_wx : forall segs m (pc : word) w lo hi,
  mem_clear m lo hi ->
  (lo <= bv_unsigned pc)%Z ->
  (bv_unsigned pc + 4 <= hi)%Z ->
  (hi <= 2^64)%Z ->
  fetch_word_wx segs pc = Some w ->
  fetch_word_ov segs m pc = Some w.
Proof.
  intros segs m pc w lo hi Hcc Hlo Hhi Hceil Hwx.
  unfold fetch_word_wx, fetch_word_ov in *.
  destruct (negb (Z.eqb (bv_unsigned pc mod 2) 0)%Z); [discriminate|].
  unfold code_read_wx, code_read_ov in *.
  destruct (find_segment segs (bv_unsigned pc) (Z.of_N 4)) as [seg|] eqn:Hfs;
    [|discriminate].
  destruct (seg_executable seg && seg_writable seg); [|discriminate].
  apply find_segment_range in Hfs.
  rewrite seg_ov_read_bytes_static
    with (n := N.to_nat 4)
    by (cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add];
        first [ lia
              | intros a Ha; apply Hcc; cbn [Z.of_nat] in *; lia ]).
  exact Hwx.
Qed.

(* ################################################################# *)
(* The packed fetch premise, and the step-to-decode reduction         *)
(* ################################################################# *)

(** What one w+x step needs of the fetch: the static (immutable-code)
    fetch declines and the overlay-aware fetch yields [w]. *)
Definition wx_fetch (segs : list Segment) (m : word -> option byte)
    (pc : word) (w : bv 32) : Prop :=
  fetch_word segs pc = None /\ fetch_word_ov segs m pc = Some w.

(** The one constructor a proof uses per step: image-level [no_ro_exec]
    (checked once), the carried [mem_clear] invariant, the pc-in-text
    bounds, and the generated static fetch fact. *)
Lemma wx_fetch_intro : forall segs m (pc : word) w lo hi,
  no_ro_exec segs = true ->
  mem_clear m lo hi ->
  (lo <= bv_unsigned pc)%Z ->
  (bv_unsigned pc + 4 <= hi)%Z ->
  (hi <= 2^64)%Z ->
  fetch_word_wx segs pc = Some w ->
  wx_fetch segs m pc w.
Proof.
  intros segs m pc w lo hi Hro Hcc Hlo Hhi Hceil Hwx.
  split.
  - apply fetch_word_none_no_ro_exec, Hro.
  - eapply fetch_word_ov_of_wx; eauto.
Qed.

(** The step pipeline for a w+x fetch: identical to
    [PropExec.step_pipeline] except that the fetch dispatch takes the
    second branch.  Keep the two in sync. *)
End WithFP1.
Ltac wx_step_pipeline Hwx Hecall Hdecode :=
  let Hn := fresh "Hn" in
  let Hov := fresh "Hov" in
  destruct Hwx as [Hn Hov];
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val ms_mem mkst];
  rewrite Hn;
  cbv beta iota;
  rewrite Hov;
  cbv beta iota;
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
  rewrite ?bv_eqb0_is_x0.

Section WithFP2.
Context {fx : FPState}.

(* ################################################################# *)
(* Per-instruction step lemmas (w+x fetch)                            *)
(*                                                                   *)
(* Statements and proofs mirror PropExec/SeqExec/MmapSim; only the    *)
(* fetch premise differs.  Conclusions are IDENTICAL.                 *)
(* ################################################################# *)

Lemma step_opimm_gen_wx : forall segs regs pc mem rom w op rd rs (imm : bv 12),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op rd rs imm Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_addi_wx : forall segs regs pc mem rom w rd rs (imm : bv 12),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (v_addi (getr regs rs) (bv_signed imm)))
                  (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_opimm_gen_wx by eassumption.
  rewrite alu_addi. reflexivity.
Qed.

(** [step_addi_wx] with the writeback value pre-normalized
    ([SeqExec.step_addi_at]'s twin). *)
Lemma step_addi_at_wx : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hwx He Hd Hrd Hv.
  rewrite (step_addi_wx segs regs pc mem rom w rd rs imm Hwx He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_shiftimm_gen_wx : forall segs regs pc mem rom w op rd rs (sh : bv 6),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op rd rs sh Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_slli_wx : forall segs regs pc mem rom w rd rs (sh : bv 6),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SLL rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (v_slli (getr regs rs) (bv_unsigned sh)))
                  (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_shiftimm_gen_wx by eassumption.
  rewrite alu_slli. reflexivity.
Qed.

Lemma step_op_gen_wx : forall segs regs pc mem rom w op rd rs1 rs2,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_add_wx : forall segs regs pc mem rom w rd rs1 rs2,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_ADD rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (v_add (getr regs rs1) (getr regs rs2)))
                  (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op_gen_wx by eassumption.
  rewrite alu_add. reflexivity.
Qed.

Lemma step_lui_wx : forall segs regs pc mem rom w rd (imm : bv 20),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.

Lemma step_auipc_wx : forall segs regs pc mem rom w rd (imm : bv 20),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.

Lemma step_jal_link_wx : forall segs regs pc mem rom w rd (imm : bv 21),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                  (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_addsext;
    reflexivity.
Qed.

Lemma step_jalr_gen_wx : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                  (jalr_tgt (getr regs rs1) (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 imm Hwx Hecall Hdecode.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_jalr, ?b_npc4; reflexivity.
Qed.

(** [ret] / tail jump, target named ([SeqExec.step_jalr_x0]'s twin). *)
Lemma step_jalr_x0_wx : forall segs regs pc mem rom w rs1 (imm : bv 12) tgt,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Jalr 0 rs1 imm, 4%Z) ->
  getr regs rs1 = tgt ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_jalr tgt (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 imm tgt Hwx He Hd Ht.
  rewrite (step_jalr_gen_wx segs regs pc mem rom w 0 rs1 imm Hwx He Hd).
  rewrite Ht. reflexivity.
Qed.

Lemma step_ecall_wx : forall segs regs pc mem rom w,
  wx_fetch segs mem pc w -> is_ecall w = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
               ms_svc_pending := Some (getr regs 17);
               ms_resv := None; ms_fcsr := fp_csr;
               ms_mem := mem; ms_rom := rom |}.
Proof.
  intros segs regs pc mem rom w [Hn Hov] Hecall.
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses.
  cbn [ms_pc ms_pc_val ms_mem mkst].
  rewrite Hn. cbv beta iota.
  rewrite Hov. cbv beta iota.
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses.
  rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

Lemma step_lbu_wx : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (Z_to_bv 64 (bv_unsigned b)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm b Hwx Hecall Hdecode Hread.
  assert (Hz : zext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = Z_to_bv 64 (bv_unsigned b)).
  { rewrite le_word_1, b_extract8_id. apply bv_eq.
    unfold zext. rewrite bv_zero_extend_unsigned by lia.
    rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
    pose proof (u8_range b). change (bv_modulus 64) with (2^64)%Z. lia. }
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma step_ld_wx : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hwx Hecall Hdecode Hread Hv.
  assert (Hz : bv_extract 0 64 v = v).
  { apply bv_eq.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_unsigned. }
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma step_sd_val_wx : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 8 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hwx Hecall Hdecode Hok.
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4.
  reflexivity.
Qed.

(** [step_sd_val_wx] with address and value pre-normalized
    ([SeqExec.step_sd_at]'s twin). *)
Lemma step_sd_at_wx : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 v)) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hwx He Hd Ha Hv Hok.
  rewrite (step_sd_val_wx segs regs pc mem rom w rs1 rs2 imm Hwx He Hd).
  - rewrite Ha, Hv. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

Lemma step_sb_val_wx : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 1 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hwx Hecall Hdecode Hok.
  assert (Hsb : forall u : word,
    Z_to_le_bytes 1%nat (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u).
  { intro u. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
    f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_wrap. lia. }
  wx_step_pipeline Hwx Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, Hsb, b_npc4.
  reflexivity.
Qed.

(** [step_sb_val_wx] with address, value and stored byte pre-normalized
    ([MmapSim.step_sb_at]'s twin). *)
Lemma step_sb_at_wx : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12)
                             (a v : word) (b : byte),
  wx_fetch segs mem pc w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  Z_to_bv 8 (bv_unsigned v) = b ->
  RiscvSemantics.store_ok segs mem a 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v b Hwx He Hd Ha Hv Hb Hok.
  rewrite (step_sb_val_wx segs regs pc mem rom w rs1 rs2 imm Hwx He Hd);
    [| rewrite Ha; exact Hok].
  rewrite Ha, Hv.
  unfold word_to_le_bytes. cbn [Z_to_le_bytes].
  rewrite Hb. reflexivity.
Qed.
End WithFP2.
