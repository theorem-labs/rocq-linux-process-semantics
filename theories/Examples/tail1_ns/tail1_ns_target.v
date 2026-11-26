(** * tail1-ns, target binary (Zig ReleaseSmall, raw syscalls).

    PROOF-SIDE FILE (not part of the trusted specification).

    The target keeps everything in registers: a1 = rb, t0 = cur,
    a6 = done, a3 = cur_n, a4 = done_n, a5 = 10.  The loop head is
    0x10011d4 (li a7,63 ; li a2,1024 ; li a0,0 ; ecall).  A '\n' copies
    cur into done with a pointer loop at 0x1001210 and appends the
    newline; a long line exits 3 via 0x100125c; EOF writes the last line
    with the helper at 0x10012b4 and exits 0 through 0x1001260.

    Counts/indices are [nat_to_word], walking pointers
    are [base + nat_to_word j], sp slots [Z_to_bv 64 (bv_unsigned tsp - k)].

    The run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  The section takes the pair as a variable [vt] and every
    derivation steps over [target_segs ++ vt]; [Proof.v] instantiates it.
    The stack stores need the entry predicate's launch conjunct
    [Run.entry_launch_ok_va] and [Run.valid_launch]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim WallSim StreamSim DrainSim StepTac ListFacts StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Common Require Import Footprint SymExec SymTac SymBranch SymSide.
From LinuxProcessSemantics.Examples.tail1_ns Require Import tail1_ns_code tail1_ns_defs.
From LinuxProcessSemantics.Examples.tail1_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.tail1_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them. *)
#[local] Instance tail1_ns_target_fx : FPState := fx0.

Definition t_rb : word := 0x10022ec.
Definition t_cur : word := 0x10026ec.
Definition t_done : word := 0x10036ec.

Lemma u_t_rb : bv_unsigned t_rb = 0x10022ec%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma u_t_cur : bv_unsigned t_cur = 0x10026ec%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma u_t_done : bv_unsigned t_done = 0x10036ec%Z.
Proof. vm_compute. reflexivity. Qed.

(** Collapse [bv_unsigned] of the buffer bases, [base + nat_to_word j]
    offsets and canonical sp-relative addresses to plain [Z]. *)
Local Ltac unormT :=
  imm_norm;
  pose proof u_t_rb; pose proof u_t_cur; pose proof u_t_done;
  rewrite ?word_add_nat;
  rewrite ?u_Z2bv by (rewrite ?u_t_rb, ?u_t_cur, ?u_t_done; lia);
  rewrite ?u_t_rb, ?u_t_cur, ?u_t_done.

(* ================================================================= *)
(* Spelling bridges between the reflective executor and the tactic    *)
(* layer's memory lemmas.                                            *)
(*                                                                    *)
(* The executor writes an address as [Z_to_bv 64 (bv_unsigned b + k)]  *)
(* (the [saddr] normal form) and a stored byte as                     *)
(* [word_to_le_bytes 1 v]; the read-back lemmas are stated over the    *)
(* base word and a singleton byte list.  These three collapse the      *)
(* difference, once, instead of a [replace] per access.               *)
(* ================================================================= *)
Lemma u0_id : forall x : word, Z_to_bv 64 (bv_unsigned x + 0)%Z = x.
Proof.
  intro x. rewrite Z.add_0_r. apply bv_eq.
  apply u_Z2bv; apply (u64_range x).
Qed.

Lemma wle1_byte : forall b : byte,
  word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof.
  intro b. pose proof (u8_range b).
  rewrite N_to_le_bytes_1_small, u_Z2bv by lia.
  f_equal. apply Z_to_bv_bv_unsigned.
Qed.

Lemma zext_byte_u : forall b : byte,
  bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intro b. pose proof (u8_range b). apply u_Z2bv; lia. Qed.

(** A buffer base held in a register as a LITERAL, indexed by a
    [nat_to_word]: the executor's [saddr] normal form puts the literal in
    the offset, the read-back lemmas put it in the base. *)
Lemma addr_base_ntw : forall (base : word) (z : Z) (n : nat),
  bv_unsigned base = z -> (Z.of_nat n < 2^64)%Z ->
  Z_to_bv 64 (bv_unsigned (nat_to_word n) + z) = base + nat_to_word n.
Proof.
  intros base z n Hb Hn. rewrite word_add_nat.
  f_equal. rewrite u_ntw by lia. lia.
Qed.

(** A register-register shift by a literal amount: the executor spells
    every shift as the register form, the library's division lemma is
    stated for the immediate form. *)
Lemma v_srl_lit : forall (x : word) (sh : Z), (0 <= sh < 64)%Z ->
  v_srl x (Z_to_bv 64 sh) = v_srli x sh.
Proof.
  intros x sh Hsh. unfold v_srl, v_srli.
  rewrite u_Z2bv by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

(** The target's "is this line already 4096 bytes long" test, compiled as
    [srli t1,a3,0xc ; bnez t1]. *)
Local Ltac srli_test :=
  unfold bv_eqb;
  rewrite (v_srl_lit _ 12) by lia;
  rewrite v_srli_div by lia;
  rewrite u_ntw by lia;
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.

(** [x0] reads as zero.  The executor keeps it as the opaque [EVar 0]
    (it never special-cases a register), so a [snez rd,rs] whose rs1 is
    [x0] denotes an OPEN [bv] term — and handing one of those to [bveq]
    does not fail, it allocates until the process dies.  Collapsing the
    read first is what keeps the closers vm-safe. *)
Lemma getr_x0z : forall rs : bvmap 5 word, getr rs 0 = Z_to_bv 64 0.
Proof. reflexivity. Qed.

(** Collapse every [bv_unsigned] of a counter or literal to [Z]. *)
Local Ltac lenlia := try (cbn [length] in * ); lia.
Local Ltac lennorm := try (cbn [length] in * ); try lia.
Local Ltac numnorm :=
  rewrite ?u_ntw by lennorm;
  rewrite ?u_Z2bv by (rewrite ?u_ntw by lennorm; lennorm);
  try (cbn [length] in * ).

(** The generic [SCBr] closer: push the comparison down to [Z] and hand
    it to [lia].  Deliberately [vm_compute]-free (an operand is routinely
    an open [nat_to_word]); the [reflexivity] alternative is what closes
    a branch whose operands the pins made literal. *)
Local Ltac scbr :=
  first
  [ reflexivity
  | (rewrite ?negb_true_iff, ?negb_false_iff;
     unfold bv_lts, bv_ltu, bv_eqb;
     rewrite ?bv_signed_small by (numnorm; lia);
     numnorm;
     first [ apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge ];
     lia) ].

(** Closers for the two obligation shapes a counting loop leaves. *)
(* An [addi rd,rs,1] on a [nat_to_word] counter. *)
Local Ltac ntw_succ :=
  apply bv_eq; rewrite u_Z2bv by (rewrite u_ntw by lia; lia);
  rewrite !u_ntw by lia; lia.

(* A [beq]/[bne] between two [nat_to_word] counters, possibly with a
   literal displacement.  Deliberately [vm_compute]-free. *)
Local Ltac brz :=
  rewrite ?negb_true_iff, ?negb_false_iff;
  unfold bv_eqb;
  rewrite ?u_Z2bv by (rewrite ?u_ntw by lia; lia);
  rewrite ?u_ntw by lia;
  first [ apply Z.eqb_eq | apply Z.eqb_neq ]; lia.

(* A register the caller pinned as a LITERAL: the pin obligation is
   stated against [Z_to_bv 64 z] and the caller's hypothesis against the
   numeral the example gave the constant. *)
Local Ltac pin_lit c :=
  lazymatch goal with
  | |- _ = Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with c by bveq
  end.

(** [sym_sc_auto] closes an [SCFlat] by [lia] once the address's base is
    bounded; a buffer base plus an index is an opaque atom until the
    range fact is posed. *)
Local Ltac scflat :=
  rewrite ?u_ntw by lia; unormT;
  repeat match goal with
  | |- context [bv_unsigned ?x] =>
      lazymatch goal with
      | H : (0 <= bv_unsigned x < _)%Z |- _ => fail
      | _ => pose proof (u64_range x)
      end
  end;
  repeat split; lia.

(** [sym_block_ex] leaves the block's [msteps] as a HYPOTHESIS, and
    [SymTac]'s normalizers all act on the goal.  This is the same
    normalization applied to a hypothesis: unfold the valuation, put the
    log's addresses into the tactic layer's spelling, and collapse the
    one-byte stores. *)
Local Ltac hms_norm H :=
  rewrite ?adenot_var, ?adenot_lit, ?bdenot_var, ?bdenot_lit,
          ?edenot_lit, ?edenot_var in H;
  cbn [Eplus Nat.ltb Nat.leb Nat.sub Nat.add Z.of_nat nth app fst snd
       a_base a_off e_addr e_width e_val] in H;
  rewrite ?u0_id, ?wle1_byte in H.

Section TargetProof.

(** The segments the run appends after the image's own: the vDSO pair
    ([Run.run_segments]).  Nothing below reads them. *)
Variable vt : list Segment.

Variable inp : ProcInput.
Variable Hvl : valid_launch inp.

(** The initial stack pointer, the program break and the mmap base are
    QUANTIFIED (ASLR). *)
Variable tsp tbrk tmb : word.

(** The target run's own draw, independent of the source's (the
    [ed_random] and [ed_top] halves of [Run.ExecEntry]'s [en_draw]; see
    the source file).  Named [arnd] like every other target section, and
    deliberately NOT after the stack pointer beside it: this file calls
    that one [tsp] where the other target sections call it [asp], and one
    file naming the draw differently is exactly what would let a reader —
    or a grep for a cross-role mix-up — miss one. *)
Variable arnd : EntryDraw.
Variable Hsp_lo : (sp_window_lo <= bv_unsigned tsp)%Z.
Variable Hsp_hi : (bv_unsigned tsp <= sp_window_hi)%Z.

(** The launch conjunct of [Run.valid_entry_va]; see the source file. *)
Variable Hlau : entry_launch_ok_va Sv48 (mkEntry tsp tbrk tmb arnd) inp.

(** The run's segment list, and a fetch fact of the image carried to it. *)
Local Abbreviation rsegs := (target_segs ++ vt).
Local Abbreviation TFv F := (fetch_word_app _ vt _ _ F).

Lemma tsp_lo_num : (0x7fff80000000 <= bv_unsigned tsp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma tsp_hi_num : (bv_unsigned tsp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Definition twmem : word -> option byte :=
  wrap_mem inp tmb target_phdrs (Z_to_bv 64 (Z.of_N 0x1001190)) tsp arnd.
Definition trom : word -> option byte := seg_rom rsegs.

(* ================================================================= *)
(* Background memory: _start's and main's ra slots over twmem, in     *)
(* execution order.  [tsp-8] = 0 ; [tsp-24] = 0x10011a0.              *)
(* ================================================================= *)
Definition tgt_bg : word -> option byte :=
  wbytes (wbytes twmem
    (Z_to_bv 64 (bv_unsigned tsp - 8))  (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned tsp - 24)) (word_to_le_bytes 8 (0x10011a0 : word)).

(** [bgt_ok mem]: [mem] agrees with [tgt_bg] at or above [tsp-32], and
    is still writable wherever [twmem] was.  The loop-head predicates
    quantify [mem] existentially, so the [store_ok] bound the stack
    stores need has to travel with it; [mem_grows] is the weakest thing
    that carries it (the overlay only ever gains addresses).

    The two clauses sit under ONE [forall], and [bgt_ok] is SEALED
    ([Opaque], just below the preservation lemmas).  Both are needed to
    keep [repeat split] — which the scripts below use to establish the
    loop-head predicates, of which [bgt_ok] is a conjunct — from taking
    it apart into halves that none of the preservation lemmas match. *)
Definition bgt_ok (mem : word -> option byte) : Prop :=
  forall (a : word) (n : nat),
    ((bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
     (bv_unsigned tsp - 32 <= bv_unsigned a)%Z ->
     rdn rsegs mem a n = rdn rsegs tgt_bg a n)
    /\ (twmem a <> None -> mem a <> None).

(** The two projections; [bgt_grows] is what the store-bound dispatcher
    reaches for (via [store_ok_db]), and both are the only way past the
    seal below. *)
Lemma bgt_agree_of : forall mem, bgt_ok mem ->
  forall (a : word) (n : nat),
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    (bv_unsigned tsp - 32 <= bv_unsigned a)%Z ->
    rdn rsegs mem a n = rdn rsegs tgt_bg a n.
Proof. intros mem H a n. apply (H a n). Qed.

Lemma bgt_grows : forall mem, bgt_ok mem -> mem_grows twmem mem.
Proof. intros mem H x. apply (H x 0%nat). Qed.

Local Hint Resolve bgt_grows : store_ok_db.

Lemma bgt_ok_bg : bgt_ok tgt_bg.
Proof.
  assert (Hg : mem_grows twmem tgt_bg) by (unfold tgt_bg; solve_mem_grows).
  intros a n. split; [reflexivity | apply Hg].
Qed.

Lemma bgt_ok_wbytes_below : forall mem (addr : word) bs,
  bgt_ok mem ->
  (bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned tsp - 32)%Z ->
  bgt_ok (wbytes mem addr bs).
Proof.
  intros mem addr bs Hm Hlt. pose proof (bgt_grows _ Hm) as Hg.
  assert (Hg' : mem_grows twmem (wbytes mem addr bs)) by solve_mem_grows.
  intros a n. split; [|apply Hg']. intros Hnw Ha.
  rewrite rdn_wbytes_disjoint by lia. apply (bgt_agree_of _ Hm); assumption.
Qed.

Lemma bgt_ok_wtm_below : forall mem (buf : word) data,
  bgt_ok mem ->
  (bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned tsp - 32)%Z ->
  bgt_ok (write_to_mem mem buf data).
Proof.
  intros mem buf data Hm Hlt. pose proof (bgt_grows _ Hm) as Hg.
  assert (Hg' : mem_grows twmem (write_to_mem mem buf data)) by solve_mem_grows.
  intros a n. split; [|apply Hg']. intros Hnw Ha.
  pose proof (u64_range tsp).
  rewrite rdn_wtm_out by first [ lia | left; lia ].
  apply (bgt_agree_of _ Hm); assumption.
Qed.

(* Everything below reaches [bgt_ok] only through the lemmas above; seal
   it so [repeat split] leaves it alone (see the note at the
   definition). *)
Opaque bgt_ok.

(** Read main's saved ra back through any [bgt_ok] memory. *)
Lemma bgt_read_ra : forall mem, bgt_ok mem ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned tsp - 24)) 8%nat
  = Some (word_to_le_bytes 8 (0x10011a0 : word)).
Proof.
  intros mem Hm. pose proof tsp_lo_num. pose proof tsp_hi_num.
  rewrite (bgt_agree_of _ Hm) by (u_norm; lia).
  unfold tgt_bg. apply rdn_wbytes_hit8. u_norm; lia.
Qed.

(* ================================================================= *)
(* Exit tail: from 0x1001260 with a0 = code reach exit(code).         *)
(* ================================================================= *)
Lemma tgt_exit_tail : forall code regs mem,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned tsp - 32) ->
  reg_get regs 10 = code -> bgt_ok mem ->
  to_exit rsegs code (mkst regs 0x1001260 mem trom).
Proof.
  intros code regs mem H2 H10 Hbg.
  pose proof tsp_lo_num as Hlo. pose proof tsp_hi_num as Hhi.
  (* 0x1001260..0x10011a4: ld ra ; addi sp ; ret ; li a7,93 ; (ecall) *)
  sym_block (target_segs ++ vt) 5%nat (@nil bool) [ELit 0x10011a0]
    [((2 : reg), EVar 32)]
    [Z_to_bv 64 (bv_unsigned tsp - 32)] (@nil word) R HR.
  { (* the reloaded [ra] is main's return point *)
    exists (word_to_le_bytes 8 (0x10011a0 : word)). split;
      [ apply bgt_read_ra; exact Hbg | vm_compute; reflexivity ]. }
  { exact H2. }
  eapply te_step;
    [reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10011a4) eq_refl) |].
  apply te_here_rec.
  - sym_regs HR; vm_compute; reflexivity.
  - sym_regs HR. exact H10.
Qed.

(* ================================================================= *)
(* List helpers                                                      *)
(* ================================================================= *)
(* [firstn_snoc_nth] (= ListFacts's [firstn_S_nth]), [firstn_all_len] and
   [skipn_cons_nth] now come from Common/ListFacts; [procs_skipn_step]
   stays local (uses the [procs] fold). *)
Lemma procs_skipn_step : forall bs i a, (i < length bs)%nat ->
  procs f a (skipn i bs) =
  match f a (nth i bs (Z_to_bv 8 0)) with
  | Some a' => procs f a' (skipn (S i) bs)
  | None => None
  end.
Proof.
  intros bs i a Hi. rewrite (skipn_cons_nth bs i (Z_to_bv 8 0) Hi). reflexivity.
Qed.

(* ================================================================= *)
(* The pointer copy loop at 0x1001210: cur[j..) -> done[j..)          *)
(* ================================================================= *)
Lemma copy_loop_t : forall (k j : nat) (cur : list byte) (R : bvmap 5 word) mem,
  (length cur - S j = k)%nat -> (j < length cur)%nat ->
  (Z.of_nat (length cur) <= 4096)%Z ->
  reg_get R 6 = nat_to_word (length cur - j) ->
  reg_get R 14 = t_cur + nat_to_word j ->
  reg_get R 17 = t_done + nat_to_word j ->
  bgt_ok mem ->
  rdn rsegs mem t_cur (length cur) = Some cur ->
  rdn rsegs mem t_done j = Some (firstn j cur) ->
  exists mem' (R' : bvmap 5 word),
    msteps rsegs (mkst R 0x1001210 mem trom) (mkst R' 0x1001228 mem' trom) /\
    reg_get R' 2 = reg_get R 2 /\ reg_get R' 5 = reg_get R 5 /\
    reg_get R' 10 = reg_get R 10 /\ reg_get R' 11 = reg_get R 11 /\
    reg_get R' 12 = reg_get R 12 /\ reg_get R' 13 = reg_get R 13 /\
    reg_get R' 15 = reg_get R 15 /\ reg_get R' 16 = reg_get R 16 /\
    bgt_ok mem' /\
    rdn rsegs mem' t_cur (length cur) = Some cur /\
    rdn rsegs mem' t_done (length cur) = Some cur /\
    (forall (a : word) (n : nat),
       (bv_unsigned a + Z.of_nat n <= bv_unsigned t_done)%Z ->
       rdn rsegs mem' a n = rdn rsegs mem a n).
Proof.
  pose proof tsp_lo_num as Hlo. pose proof tsp_hi_num as Hhi.
  intro k. induction k as [|k IH];
    intros j cur R mem Hk Hj Hcap H6 H14 H17 Hbg Hcur Hdone.
  - (* last byte: after the body, t1 = 0 and bnez falls through *)
    assert (Hsj : S j = length cur) by lia.
    sym_block_ex (target_segs ++ vt) (mkst R (Z_to_bv 64 16781840%Z) mem trom)
        6%nat [false] (@nil expr)
        [((6 : reg), EVar 32); ((14 : reg), EVar 33); ((17 : reg), EVar 34)]
        [nat_to_word (length cur - j); t_cur + nat_to_word j;
         t_done + nat_to_word j]
        [Z_to_bv 64 (bv_unsigned (nth j cur (Z_to_bv 8 0)))] R2 HR2 Hms.
    { (* bnez t1 NOT taken: this was the last byte *)
      replace (length cur - j)%nat with 1%nat by lia. vm_compute. reflexivity. }
    { scflat. }
    { rewrite u0_id. apply target_store_ok; unormT; lia. }
    { scflat. }
    { rewrite u0_id. exists [nth j cur (Z_to_bv 8 0)]. split;
        [ apply (rdn_nth rsegs mem (length cur) t_cur cur j Hcur Hj)
        | rewrite bytes_le_to_Z_1; symmetry; apply zext_byte_u ]. }
    { exact H6. }
    { exact H14. }
    { exact H17. }
    hms_norm Hms.
    replace (Z_to_bv 64 16781840%Z) with (0x1001210 : word) in Hms by bveq.
    replace (Z_to_bv 64 16781864%Z) with (0x1001228 : word) in Hms by bveq.
    exists (wbytes mem (t_done + nat_to_word j) [nth j cur (Z_to_bv 8 0)]), R2.
    repeat split; try exact Hms; try (sym_regs HR2; reflexivity).
    + apply bgt_ok_wbytes_below; [exact Hbg|]. cbn [length]. unormT. lia.
    + rewrite rdn_wbytes1_out
        by (unormT; first [ lia | left; lia | right; lia ]).
      exact Hcur.
    + assert (HdSj : rdn rsegs
                       (wbytes mem (t_done + nat_to_word j)
                          [nth j cur (Z_to_bv 8 0)]) t_done (S j)
                     = Some (firstn (S j) cur)).
      { replace (t_done + nat_to_word j)
          with (t_done + nat_to_word (length (firstn j cur)))
          by (rewrite length_firstn, Nat.min_l by lia; reflexivity).
        rewrite (firstn_S_nth byte cur j (Z_to_bv 8 0) Hj).
        replace (S j) with (length (firstn j cur) + 1)%nat
          by (rewrite length_firstn; lia).
        apply rdn_snoc_store.
        - rewrite u_t_done, length_firstn. rewrite Nat.min_l by lia. lia.
        - rewrite length_firstn, Nat.min_l by lia. exact Hdone. }
      rewrite Hsj, firstn_all_len in HdSj. exact HdSj.
    + intros a n Ha.
      rewrite rdn_wbytes1_out
        by (unormT; first [ lia | left; lia | right; lia ]).
      reflexivity.
  - (* middle byte: after the body, t1 <> 0 and bnez loops back *)
    assert (Hsj : (S j < length cur)%nat) by lia.
    set (mem' := wbytes mem (t_done + nat_to_word j) [nth j cur (Z_to_bv 8 0)]).
    assert (Hbody : exists rg, msteps rsegs (mkst R 0x1001210 mem trom)
                      (mkst rg 0x1001210 mem' trom)
                    /\ reg_get rg 6 = nat_to_word (length cur - S j)
                    /\ reg_get rg 14 = t_cur + nat_to_word (S j)
                    /\ reg_get rg 17 = t_done + nat_to_word (S j)
                    /\ reg_get rg 2 = reg_get R 2 /\ reg_get rg 5 = reg_get R 5
                    /\ reg_get rg 10 = reg_get R 10
                    /\ reg_get rg 11 = reg_get R 11
                    /\ reg_get rg 12 = reg_get R 12
                    /\ reg_get rg 13 = reg_get R 13
                    /\ reg_get rg 15 = reg_get R 15
                    /\ reg_get rg 16 = reg_get R 16).
    { sym_block_ex (target_segs ++ vt) (mkst R (Z_to_bv 64 16781840%Z) mem trom)
          6%nat [true] (@nil expr)
          [((6 : reg), EVar 32); ((14 : reg), EVar 33); ((17 : reg), EVar 34)]
          [nat_to_word (length cur - j); t_cur + nat_to_word j;
           t_done + nat_to_word j]
          [Z_to_bv 64 (bv_unsigned (nth j cur (Z_to_bv 8 0)))] R2 HR2 Hms.
      { (* bnez t1 IS taken: bytes remain *)
        apply negb_true_iff. unfold bv_eqb.
        rewrite u_Z2bv by (rewrite u_ntw by lia; lia).
        rewrite u_ntw by lia.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
        apply Z.eqb_neq. lia. }
      { scflat. }
      { rewrite u0_id. apply target_store_ok; unormT; lia. }
      { scflat. }
      { rewrite u0_id. exists [nth j cur (Z_to_bv 8 0)]. split;
          [ apply (rdn_nth rsegs mem (length cur) t_cur cur j Hcur Hj)
          | rewrite bytes_le_to_Z_1; symmetry; apply zext_byte_u ]. }
      { exact H6. }
      { exact H14. }
      { exact H17. }
      hms_norm Hms.
      replace (Z_to_bv 64 16781840%Z) with (0x1001210 : word) in Hms by bveq.
      exists R2. split; [exact Hms|].
      repeat split.
      all: sym_regs HR2.
      1: apply bv_eq; rewrite u_Z2bv by (rewrite u_ntw by lia; lia);
         rewrite !u_ntw by lia; lia.
      1-2: unormT; f_equal; lia.
      all: reflexivity. }
    destruct Hbody as (rg & Hms & G6 & G14 & G17 & G2 & G5 & G10 & G11
                       & G12 & G13 & G15 & G16).
    assert (Hbg' : bgt_ok mem').
    { apply bgt_ok_wbytes_below; [exact Hbg|].
      cbn [length]. unormT. lia. }
    assert (Hcur' : rdn rsegs mem' t_cur (length cur) = Some cur).
    { unfold mem'.
      rewrite rdn_wbytes1_out
        by (unormT; first [ lia | left; lia | right; lia ]).
      exact Hcur. }
    assert (Hdone' : rdn rsegs mem' t_done (S j) = Some (firstn (S j) cur)).
    { unfold mem'.
      replace (t_done + nat_to_word j)
        with (t_done + nat_to_word (length (firstn j cur)))
        by (rewrite length_firstn, Nat.min_l by lia; reflexivity).
      rewrite (firstn_S_nth byte cur j (Z_to_bv 8 0) Hj).
      replace (S j) with (length (firstn j cur) + 1)%nat
        by (rewrite length_firstn; lia).
      apply rdn_snoc_store.
      - rewrite u_t_done, length_firstn. rewrite Nat.min_l by lia. lia.
      - rewrite length_firstn, Nat.min_l by lia. exact Hdone. }
    destruct (IH (S j) cur rg mem' ltac:(lia) Hsj Hcap G6 G14 G17
                Hbg' Hcur' Hdone')
      as (mem'' & R'' & Hs'' & E2 & E5 & E10 & E11 & E12 & E13 & E15 & E16
          & Hbg'' & Hcur'' & Hdone'' & Hframe'').
    exists mem'', R''. split; [eapply msteps_trans; [exact Hms | exact Hs'']|].
    rewrite E2, E5, E10, E11, E12, E13, E15, E16.
    rewrite G2, G5, G10, G11, G12, G13, G15, G16.
    repeat split; try assumption.
    intros a n Ha. rewrite (Hframe'' a n Ha). unfold mem'.
    rewrite rdn_wbytes1_out
      by (unormT; first [ lia | left; lia | right; lia ]).
    reflexivity.
Qed.

(* ================================================================= *)
(* The full copy phase: from the beqz at 0x100120c.                   *)
(* ================================================================= *)
Lemma copy_full_t : forall (cur : list byte) (R : bvmap 5 word) mem,
  (Z.of_nat (length cur) <= 4096)%Z ->
  reg_get R 6 = nat_to_word (length cur) ->
  reg_get R 13 = nat_to_word (length cur) ->
  reg_get R 14 = t_cur -> reg_get R 17 = t_done ->
  bgt_ok mem ->
  rdn rsegs mem t_cur (length cur) = Some cur ->
  exists mem' (R' : bvmap 5 word),
    msteps rsegs (mkst R 0x100120c mem trom) (mkst R' 0x1001228 mem' trom) /\
    reg_get R' 2 = reg_get R 2 /\ reg_get R' 5 = reg_get R 5 /\
    reg_get R' 10 = reg_get R 10 /\ reg_get R' 11 = reg_get R 11 /\
    reg_get R' 12 = reg_get R 12 /\ reg_get R' 13 = reg_get R 13 /\
    reg_get R' 15 = reg_get R 15 /\ reg_get R' 16 = reg_get R 16 /\
    bgt_ok mem' /\
    rdn rsegs mem' t_cur (length cur) = Some cur /\
    rdn rsegs mem' t_done (length cur) = Some cur /\
    (forall (a : word) (n : nat),
       (bv_unsigned a + Z.of_nat n <= bv_unsigned t_done)%Z ->
       rdn rsegs mem' a n = rdn rsegs mem a n).
Proof.
  intros cur R mem Hcap H6 H13 H14 H17 Hbg Hcur.
  destruct cur as [|c0 curr].
  - (* nothing to copy: beqz a3 taken *)
    exists mem, R. split.
    { eapply mst_step; [reflexivity |
        eapply step_beq_tk; [ exact (TFv TF_100120c) | reflexivity | exact TD_100120c
          | getr_resolve; rewrite H13; exact c_eq_0_true ]
        | norm_pc ].
      apply mst_refl. }
    repeat split; try reflexivity; try assumption;
      try (intros a n _; reflexivity).
  - (* beqz a3 falls through into the loop *)
    assert (Hlen : (0 < length (c0 :: curr))%nat) by (cbn [length]; lia).
    assert (Hstep0 : msteps rsegs (mkst R 0x100120c mem trom)
                       (mkst R 0x1001210 mem trom)).
    { eapply mst_step; [reflexivity |
        eapply step_beq_ft; [ exact (TFv TF_100120c) | reflexivity | exact TD_100120c
          | getr_resolve; rewrite H13; apply c_eq_0_false;
            rewrite u_ntw by lia; cbn [length]; lia ]
        | norm_pc ].
      apply mst_refl. }
    destruct (copy_loop_t (length (c0 :: curr) - 1) 0 (c0 :: curr) R mem
                ltac:(lia) Hlen Hcap
                ltac:(rewrite Nat.sub_0_r; exact H6)
                ltac:(rewrite H14; symmetry; apply word_add_0)
                ltac:(rewrite H17; symmetry; apply word_add_0)
                Hbg Hcur ltac:(reflexivity))
      as (mem' & R' & Hs & E2 & E5 & E10 & E11 & E12 & E13 & E15 & E16
          & Hbg' & Hcur' & Hdone' & Hframe').
    exists mem', R'. split; [eapply msteps_trans; [exact Hstep0 | exact Hs]|].
    repeat split; assumption.
Qed.

(* ================================================================= *)
(* Loop-head predicate                                                *)
(* ================================================================= *)
Definition tgt_LH (a : A) (ms : machine_state) : Prop :=
  exists regs mem,
    ms = mkst regs 0x10011d4 mem trom /\
    reg_get regs 2 = Z_to_bv 64 (bv_unsigned tsp - 32) /\
    reg_get regs 5 = t_cur /\ reg_get regs 16 = t_done /\
    reg_get regs 15 = Z_to_bv 64 10 /\ reg_get regs 11 = t_rb /\
    reg_get regs 13 = nat_to_word (length (fst a)) /\
    reg_get regs 14 = nat_to_word (length (snd a)) /\
    bgt_ok mem /\
    rdn rsegs mem t_cur (length (fst a)) = Some (fst a) /\
    rdn rsegs mem t_done (length (snd a)) = Some (snd a) /\
    (Z.of_nat (length (fst a)) <= 4096)%Z /\
    (Z.of_nat (length (snd a)) <= 4097)%Z.

(* ================================================================= *)
(* Byte-loop head predicate (at 0x10011f4)                            *)
(* ================================================================= *)
Definition BLHt (cur done bs : list byte) (i : nat) (ms : machine_state) : Prop :=
  exists regs mem,
    ms = mkst regs 0x10011f4 mem trom /\
    reg_get regs 2 = Z_to_bv 64 (bv_unsigned tsp - 32) /\
    reg_get regs 5 = t_cur /\ reg_get regs 16 = t_done /\
    reg_get regs 15 = Z_to_bv 64 10 /\ reg_get regs 11 = t_rb /\
    reg_get regs 13 = nat_to_word (length cur) /\
    reg_get regs 14 = nat_to_word (length done) /\
    reg_get regs 12 = nat_to_word i /\
    reg_get regs 10 = nat_to_word (length bs) /\
    bgt_ok mem /\
    rdn rsegs mem t_rb (length bs) = Some bs /\
    rdn rsegs mem t_cur (length cur) = Some cur /\
    rdn rsegs mem t_done (length done) = Some done /\
    (Z.of_nat (length cur) <= 4096)%Z /\ (Z.of_nat (length done) <= 4097)%Z /\
    (Z.of_nat (length bs) <= 1024)%Z /\ (i < length bs)%nat.

(* State at 0x1001250 (the a2 increment), after processing byte i. *)
Definition C4t (cur done bs : list byte) (i : nat) (ms : machine_state) : Prop :=
  exists regs mem,
    ms = mkst regs 0x1001250 mem trom /\
    reg_get regs 2 = Z_to_bv 64 (bv_unsigned tsp - 32) /\
    reg_get regs 5 = t_cur /\ reg_get regs 16 = t_done /\
    reg_get regs 15 = Z_to_bv 64 10 /\ reg_get regs 11 = t_rb /\
    reg_get regs 13 = nat_to_word (length cur) /\
    reg_get regs 14 = nat_to_word (length done) /\
    reg_get regs 12 = nat_to_word i /\
    reg_get regs 10 = nat_to_word (length bs) /\
    bgt_ok mem /\
    rdn rsegs mem t_rb (length bs) = Some bs /\
    rdn rsegs mem t_cur (length cur) = Some cur /\
    rdn rsegs mem t_done (length done) = Some done /\
    (Z.of_nat (length cur) <= 4096)%Z /\ (Z.of_nat (length done) <= 4097)%Z /\
    (Z.of_nat (length bs) <= 1024)%Z /\ (i < length bs)%nat.

Lemma msteps_to_exit_t : forall code ms ms',
  msteps rsegs ms ms' -> to_exit rsegs code ms' ->
  to_exit rsegs code ms.
Proof.
  intros code ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hstep H IH]; [auto|].
  intro Hex. eapply te_step; [exact Hsvc | exact Hstep | apply IH; exact Hex].
Qed.

(* ================================================================= *)
(* The byte loop                                                      *)
(* ================================================================= *)
Lemma byte_loop_t : forall (k : nat) cur done bs i ms,
  (length bs - i = k)%nat -> BLHt cur done bs i ms ->
  match procs f (cur, done) (skipn i bs) with
  | Some a' => exists msL, msteps rsegs ms msL /\ tgt_LH a' msL
  | None => to_exit rsegs ec ms
  end.
Proof.
  intro k. induction k as [|k IH];
    intros cur done bs i ms Hk HBLH;
    destruct HBLH as (regs & mem & -> & H2 & H5 & H16 & H15 & H11 & H13 & H14
                      & H12 & H10 & Hbg & Hrb & Hcur & Hdone
                      & Hcurcap & Hdonecap & Hbscap & Hi);
    pose proof tsp_lo_num as Hlo; pose proof tsp_hi_num as Hhi.
  { lia. }
  remember (nth i bs (Z_to_bv 8 0)) as b eqn:Hbdef.
  (* Dispatch helper at 0x1001250 (uses IH). *)
  assert (Hdisp : forall cur' done' st, C4t cur' done' bs i st ->
    match procs f (cur', done') (skipn (S i) bs) with
    | Some a'' => exists msL, msteps rsegs st msL /\ tgt_LH a'' msL
    | None => to_exit rsegs ec st end).
  { intros cur' done' st HC4.
    destruct HC4 as (rg & mm & -> & G2 & G5 & G16 & G15 & G11 & G13 & G14
                     & G12 & G10 & Hbg' & Hrb' & Hcur' & Hdone'
                     & Hcurcap' & Hdonecap' & Hbscap' & Hlt).
    destruct (Nat.eq_dec (S i) (length bs)) as [Heq | Hne].
    - (* the block is exhausted: [addi a2,a2,1 ; beq a2,a0] back to the
         read loop head *)
      rewrite skipn_all2 by lia. cbn [procs].
      sym_block_ex (target_segs ++ vt) (mkst rg (Z_to_bv 64 16781904%Z) mm trom)
        2%nat [true] (@nil expr)
        [((12 : reg), EVar 32); ((10 : reg), EVar 33)]
        [nat_to_word i; nat_to_word (length bs)] (@nil word) Rn HRn Hms.
      { brz. }
      { exact G12. }
      { exact G10. }
      hms_norm Hms.
      replace (Z_to_bv 64 16781904%Z) with (0x1001250 : word) in Hms by bveq.
      replace (Z_to_bv 64 16781780%Z) with (0x10011d4 : word) in Hms by bveq.
      exists (mkst Rn 0x10011d4 mm trom). split; [exact Hms|].
      unfold tgt_LH. do 2 eexists. split; [reflexivity|].
      cbn [fst snd].
      repeat split;
        try (sym_regs HRn; first [ reflexivity | assumption | ntw_succ ]);
        try assumption.
    - assert (Hlt2 : (S i < length bs)%nat) by lia.
      (* one more byte: [addi a2,a2,1 ; beq not taken ; j] back to the
         byte-loop head *)
      sym_block_ex (target_segs ++ vt) (mkst rg (Z_to_bv 64 16781904%Z) mm trom)
        3%nat [false] (@nil expr)
        [((12 : reg), EVar 32); ((10 : reg), EVar 33)]
        [nat_to_word i; nat_to_word (length bs)] (@nil word) Rn HRn Hms.
      { brz. }
      { exact G12. }
      { exact G10. }
      hms_norm Hms.
      replace (Z_to_bv 64 16781904%Z) with (0x1001250 : word) in Hms by bveq.
      replace (Z_to_bv 64 16781812%Z) with (0x10011f4 : word) in Hms by bveq.
      assert (HB2 : BLHt cur' done' bs (S i) (mkst Rn 0x10011f4 mm trom)).
      { unfold BLHt. do 2 eexists. split; [reflexivity|].
        repeat split;
          try (sym_regs HRn; first [ reflexivity | assumption | ntw_succ ]);
          try assumption; try lia. }
      pose proof (IH cur' done' bs (S i) (mkst Rn 0x10011f4 mm trom)
                    ltac:(lia) HB2) as Hih.
      revert Hih.
      destruct (procs f (cur', done') (skipn (S i) bs)) as [a''|].
      + intros (msL & Hs & HL). exists msL.
        split; [eapply msteps_trans; [exact Hms | exact Hs] | exact HL].
      + intro Hih. eapply msteps_to_exit_t; [exact Hms | exact Hih]. }
  destruct (bv_eqb b (Z_to_bv 8 10)) eqn:Eb.
  - (* ===== newline byte ===== *)
    assert (Hf : f (cur, done) b = Some ([], cur ++ [Z_to_bv 8 10]))
      by (unfold f; rewrite Eb; reflexivity).
    replace (procs f (cur, done) (skipn i bs))
      with (procs f ([], cur ++ [Z_to_bv 8 10]) (skipn (S i) bs))
      by (rewrite (procs_skipn_step bs i (cur, done) Hi);
          rewrite <- Hbdef, Hf; reflexivity).
    (* 0x10011f4..0x100120c: load rb[i], bne falls through, the three mvs *)
    assert (Hac : exists Rac, msteps rsegs (mkst regs 0x10011f4 mem trom)
                     (mkst Rac 0x100120c mem trom)
                  /\ reg_get Rac 6 = nat_to_word (length cur)
                  /\ reg_get Rac 13 = nat_to_word (length cur)
                  /\ reg_get Rac 14 = t_cur /\ reg_get Rac 17 = t_done
                  /\ reg_get Rac 2 = Z_to_bv 64 (bv_unsigned tsp - 32)
                  /\ reg_get Rac 5 = t_cur /\ reg_get Rac 16 = t_done
                  /\ reg_get Rac 15 = Z_to_bv 64 10 /\ reg_get Rac 11 = t_rb
                  /\ reg_get Rac 12 = nat_to_word i
                  /\ reg_get Rac 10 = nat_to_word (length bs)).
    { sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781812%Z) mem trom)
        6%nat [false] (@nil expr)
        [((11 : reg), ELit 16786156); ((15 : reg), ELit 10);
         ((5 : reg), ELit 16787180); ((16 : reg), ELit 16791276);
         ((12 : reg), EVar 32); ((13 : reg), EVar 33)]
        [nat_to_word i; nat_to_word (length cur)]
        [Z_to_bv 64 (bv_unsigned b)] Rac HRac Hms.
      { (* bne a7,a5 NOT taken: this byte IS the newline *)
        apply negb_false_iff. rewrite c_eq_zext10. exact Eb. }
      { scflat. }
      { (* the loaded byte comes out of the read buffer *)
        rewrite (addr_base_ntw t_rb 16786156 i u_t_rb ltac:(lia)).
        exists [b]. split;
          [ rewrite Hbdef;
            apply (rdn_nth rsegs mem (length bs) t_rb bs i Hrb Hi)
          | rewrite bytes_le_to_Z_1; symmetry; apply zext_byte_u ]. }
      { pin_lit t_rb; exact H11. }
      { exact H15. }
      { pin_lit t_cur; exact H5. }
      { pin_lit t_done; exact H16. }
      { exact H12. }
      { exact H13. }
      hms_norm Hms.
      replace (Z_to_bv 64 16781812%Z) with (0x10011f4 : word) in Hms by bveq.
      replace (Z_to_bv 64 16781836%Z) with (0x100120c : word) in Hms by bveq.
      exists Rac. split; [exact Hms|].
      repeat split;
        try (sym_regs HRac; first [ reflexivity | assumption | bveq ]). }
    destruct Hac as (Rac & Hms_ac & GRac6 & GRac13 & GRac14 & GRac17 & GRac2
                     & GRac5 & GRac16 & GRac15 & GRac11 & GRac12 & GRac10).
    destruct (copy_full_t cur Rac mem Hcurcap GRac6 GRac13 GRac14 GRac17 Hbg Hcur)
      as (mem_c & Rc & Hcopy & Cc2 & Cc5 & Cc10 & Cc11 & Cc12 & Cc13 & Cc15
          & Cc16 & Hbg_c & Hcur_c & Hdone_c & Hframe_c).
    (* 0x1001228..0x1001250: append the newline, reset the counters *)
    set (memD := wbytes mem_c (t_done + nat_to_word (length cur))
                   [Z_to_bv 8 10]).
    assert (Hc4 : exists Rd, msteps rsegs (mkst Rc 0x1001228 mem_c trom)
                     (mkst Rd 0x1001250 memD trom)
                  /\ reg_get Rd 2 = Z_to_bv 64 (bv_unsigned tsp - 32)
                  /\ reg_get Rd 5 = t_cur /\ reg_get Rd 16 = t_done
                  /\ reg_get Rd 15 = Z_to_bv 64 10 /\ reg_get Rd 11 = t_rb
                  /\ reg_get Rd 13 = nat_to_word 0
                  /\ reg_get Rd 14 = nat_to_word (S (length cur))
                  /\ reg_get Rd 12 = nat_to_word i
                  /\ reg_get Rd 10 = nat_to_word (length bs)).
    { sym_block_ex (target_segs ++ vt) (mkst Rc (Z_to_bv 64 16781864%Z) mem_c trom)
        5%nat (@nil bool) (@nil expr)
        [((16 : reg), ELit 16791276); ((15 : reg), ELit 10);
         ((13 : reg), EVar 32)]
        [nat_to_word (length cur)] (@nil word) Rd HRd Hms.
      { scflat. }
      { rewrite (addr_base_ntw t_done 16791276 (length cur) u_t_done
                   ltac:(lia)).
        apply target_store_ok; unormT; lia. }
      { pin_lit t_done. exact (eq_trans Cc16 GRac16). }
      { exact (eq_trans Cc15 GRac15). }
      { exact (eq_trans Cc13 GRac13). }
      hms_norm Hms.
      rewrite (addr_base_ntw t_done 16791276 (length cur) u_t_done ltac:(lia))
        in Hms.
      replace (word_to_le_bytes 1 (Z_to_bv 64 10)) with [Z_to_bv 8 10] in Hms
        by (vm_compute; reflexivity).
      replace (Z_to_bv 64 16781864%Z) with (0x1001228 : word) in Hms by bveq.
      replace (Z_to_bv 64 16781904%Z) with (0x1001250 : word) in Hms by bveq.
      exists Rd. split; [exact Hms|].
      repeat split;
        try (sym_regs HRd;
             first [ reflexivity
                   | exact (eq_trans Cc2 GRac2)
                   | exact (eq_trans Cc5 GRac5)
                   | exact (eq_trans Cc11 GRac11)
                   | exact (eq_trans Cc12 GRac12)
                   | exact (eq_trans Cc10 GRac10)
                   | ntw_succ | bveq ]). }
    destruct Hc4 as (Rd & Hms_d & GRd2 & GRd5 & GRd16 & GRd15 & GRd11
                     & GRd13 & GRd14 & GRd12 & GRd10).
    assert (HC4 : C4t [] (cur ++ [Z_to_bv 8 10]) bs i (mkst Rd 0x1001250 memD trom)).
    { unfold C4t. do 2 eexists. split; [reflexivity|].
      repeat split; try assumption.
      - rewrite GRd14. f_equal. rewrite length_app. cbn [length]. lia.
      - apply bgt_ok_wbytes_below; [exact Hbg_c|].
        cbn [length]. unormT. lia.
      - unfold memD.
        rewrite rdn_wbytes1_out
          by (unormT; first [ lia | left; lia | right; lia ]).
        rewrite (Hframe_c t_rb (length bs)) by (unormT; lia).
        exact Hrb.
      - unfold memD. rewrite length_app. cbn [length].
        apply rdn_snoc_store.
        + rewrite u_t_done. lia.
        + exact Hdone_c.
      - cbn [length]. lia.
      - rewrite length_app. cbn [length]. lia. }
    pose proof (Hdisp [] (cur ++ [Z_to_bv 8 10]) (mkst Rd 0x1001250 memD trom) HC4)
      as Hd.
    assert (Hall : msteps rsegs (mkst regs 0x10011f4 mem trom)
                     (mkst Rd 0x1001250 memD trom)).
    { eapply msteps_trans; [exact Hms_ac |].
      eapply msteps_trans; [exact Hcopy | exact Hms_d]. }
    revert Hd.
    destruct (procs f ([], cur ++ [Z_to_bv 8 10]) (skipn (S i) bs)) as [a''|].
    + intros (msL & Hs & HL). exists msL.
      split; [eapply msteps_trans; [exact Hall | exact Hs] | exact HL].
    + intro Hd. eapply msteps_to_exit_t; [exact Hall | exact Hd].
  - (* ===== non-newline byte ===== *)
    destruct (Z.leb_spec 4096 (Z.of_nat (length cur))) as [Hge | Hlt].
    + (* line full: abort with exit 3 *)
      assert (Hf : f (cur, done) b = None).
      { unfold f. rewrite Eb.
        rewrite (proj2 (Z.leb_le 4096 (Z.of_nat (length cur))) Hge).
        reflexivity. }
      replace (procs f (cur, done) (skipn i bs)) with (@None A)
        by (rewrite (procs_skipn_step bs i (cur, done) Hi);
            rewrite <- Hbdef, Hf; reflexivity).
      cbv iota.
      assert (Hc4096 : Z.of_nat (length cur) = 4096%Z) by lia.
      (* 0x10011f4..0x100125c: the byte is not '\n' and cur is full *)
      sym_block (target_segs ++ vt) 6%nat [true; true] (@nil expr)
        [((11 : reg), ELit 16786156); ((15 : reg), ELit 10);
         ((12 : reg), EVar 32); ((13 : reg), EVar 33)]
        [nat_to_word i; nat_to_word (length cur)]
        [Z_to_bv 64 (bv_unsigned b)] Rx HRx.
      { (* bnez t1 IS taken: |cur| = 4096 so the shift is nonzero *)
        apply negb_true_iff. srli_test.
        apply Z.eqb_neq. rewrite Hc4096. vm_compute. discriminate. }
      { (* bne a7,a5 IS taken: the byte is not the newline *)
        apply negb_true_iff. rewrite c_eq_zext10. exact Eb. }
      { scflat. }
      { rewrite (addr_base_ntw t_rb 16786156 i u_t_rb ltac:(lia)).
        exists [b]. split;
          [ rewrite Hbdef;
            apply (rdn_nth rsegs mem (length bs) t_rb bs i Hrb Hi)
          | rewrite bytes_le_to_Z_1; symmetry; apply zext_byte_u ]. }
      { pin_lit t_rb; exact H11. }
      { exact H15. }
      { exact H12. }
      { exact H13. }
      apply tgt_exit_tail;
        [ sym_regs HRx; exact H2 | sym_regs HRx; reflexivity | exact Hbg ].
    + (* append the byte to cur *)
      assert (Hf : f (cur, done) b = Some (cur ++ [b], done)).
      { unfold f. rewrite Eb.
        rewrite (proj2 (Z.leb_gt 4096 (Z.of_nat (length cur))) Hlt).
        reflexivity. }
      replace (procs f (cur, done) (skipn i bs))
        with (procs f (cur ++ [b], done) (skipn (S i) bs))
        by (rewrite (procs_skipn_step bs i (cur, done) Hi);
            rewrite <- Hbdef, Hf; reflexivity).
      set (memC := wbytes mem (t_cur + nat_to_word (length cur)) [b]).
      assert (Hc4 : exists Rd, msteps rsegs (mkst regs 0x10011f4 mem trom)
                       (mkst Rd 0x1001250 memC trom)
                    /\ reg_get Rd 2 = Z_to_bv 64 (bv_unsigned tsp - 32)
                    /\ reg_get Rd 5 = t_cur /\ reg_get Rd 16 = t_done
                    /\ reg_get Rd 15 = Z_to_bv 64 10 /\ reg_get Rd 11 = t_rb
                    /\ reg_get Rd 13 = nat_to_word (S (length cur))
                    /\ reg_get Rd 14 = nat_to_word (length done)
                    /\ reg_get Rd 12 = nat_to_word i
                    /\ reg_get Rd 10 = nat_to_word (length bs)).
      { sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781812%Z) mem trom)
          8%nat [true; false] (@nil expr)
          [((11 : reg), ELit 16786156); ((15 : reg), ELit 10);
           ((5 : reg), ELit 16787180);
           ((12 : reg), EVar 32); ((13 : reg), EVar 33)]
          [nat_to_word i; nat_to_word (length cur)]
          [Z_to_bv 64 (bv_unsigned b)] Rd HRd Hms.
        { scflat. }
        { rewrite (addr_base_ntw t_cur 16787180 (length cur) u_t_cur
                     ltac:(lia)).
          apply target_store_ok; unormT; lia. }
        { (* bnez t1 NOT taken: |cur| < 4096 *)
          apply negb_false_iff. srli_test.
          apply Z.eqb_eq. apply Z.div_small. lia. }
        { (* bne a7,a5 IS taken: the byte is not the newline *)
          apply negb_true_iff. rewrite c_eq_zext10. exact Eb. }
        { scflat. }
        { rewrite (addr_base_ntw t_rb 16786156 i u_t_rb ltac:(lia)).
          exists [b]. split;
            [ rewrite Hbdef;
              apply (rdn_nth rsegs mem (length bs) t_rb bs i Hrb Hi)
            | rewrite bytes_le_to_Z_1; symmetry; apply zext_byte_u ]. }
        { pin_lit t_rb; exact H11. }
        { exact H15. }
        { pin_lit t_cur; exact H5. }
        { exact H12. }
        { exact H13. }
        hms_norm Hms.
        rewrite (addr_base_ntw t_cur 16787180 (length cur) u_t_cur ltac:(lia))
          in Hms.
        replace (Z_to_bv 64 16781812%Z) with (0x10011f4 : word) in Hms by bveq.
        replace (Z_to_bv 64 16781904%Z) with (0x1001250 : word) in Hms by bveq.
        exists Rd. split; [unfold memC; exact Hms|].
        repeat split;
          try (sym_regs HRd;
               first [ reflexivity | assumption | ntw_succ | bveq ]). }
      destruct Hc4 as (Rd & Hms_d & GRd2 & GRd5 & GRd16 & GRd15 & GRd11
                       & GRd13 & GRd14 & GRd12 & GRd10).
      assert (HC4 : C4t (cur ++ [b]) done bs i (mkst Rd 0x1001250 memC trom)).
      { unfold C4t. do 2 eexists. split; [reflexivity|].
        repeat split; try assumption.
        - rewrite GRd13. f_equal. rewrite length_app. cbn [length]. lia.
        - apply bgt_ok_wbytes_below; [exact Hbg|].
          cbn [length]. unormT. lia.
        - unfold memC.
          rewrite rdn_wbytes1_out
            by (unormT; first [ lia | left; lia | right; lia ]).
          exact Hrb.
        - unfold memC. rewrite length_app. cbn [length].
          apply rdn_snoc_store.
          + rewrite u_t_cur. lia.
          + exact Hcur.
        - unfold memC.
          rewrite rdn_wbytes1_out
            by (unormT; first [ lia | left; lia | right; lia ]).
          exact Hdone.
        - rewrite length_app. cbn [length]. lia. }
      pose proof (Hdisp (cur ++ [b]) done (mkst Rd 0x1001250 memC trom) HC4) as Hd.
      revert Hd.
      destruct (procs f (cur ++ [b], done) (skipn (S i) bs)) as [a''|].
      * intros (msL & Hs & HL). exists msL.
        split; [eapply msteps_trans; [exact Hms_d | exact Hs] | exact HL].
      * intro Hd. eapply msteps_to_exit_t; [exact Hms_d | exact Hd].
Qed.

(* ================================================================= *)
(* The EOF write's put-style retry loop at 0x10012cc                  *)
(* ================================================================= *)

(** The write helper at 0x10012b4 issues its [ecall] at 0x10012c8 and
    then loops: [blez a0] (whose error arm is dead — every delivery is
    nonempty), [add a1,a1,a0], [sub a2,a2,a0], [bnez a2] back to the
    [li a0,1] at 0x10012c4.  The loop is REGISTER-ONLY, so memory is
    untouched throughout and the whole remainder [skipn n rest] leaves
    across one or more possibly-short channel writes.  On the last
    delivery the helper returns 0 to its [ra] (always 0x10012a0, the
    single [jalr] call site at 0x100129c), whence main's
    [snez a0,a0 ; slliw a0,a0,2] computes exit code 0 and falls into
    the exit tail.

    Induction on [fuel >= length rest]; the remainder strictly shrinks
    because every delivery is nonempty. *)
Lemma tgt_put_wall : forall fuel (rest : list byte) (p : word) n regs mem,
  (length rest <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length rest)%nat ->
  (Z.of_nat (length rest) < 2^63)%Z ->
  reg_get regs 1 = (0x10012a0 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned tsp - 32) ->
  reg_get regs 10 = len_word (firstn n rest) ->
  reg_get regs 11 = p ->
  reg_get regs 12 = len_word rest ->
  bv_unsigned (reg_get regs 17) = 64%Z ->
  reg_get regs 17 = Z_to_bv 64 64 ->
  bgt_ok mem ->
  rdn rsegs mem p (length rest) = Some rest ->
  (* the caller's buffer passes [access_ok], so every remainder does *)
  (bv_unsigned p + Z.of_nat (length rest) <= TASK_SIZE)%Z ->
  to_wall_tail rsegs (Z_to_bv 64 1)
    (mkst regs (0x10012cc : word) mem trom) (skipn n rest)
    (to_exit rsegs (Z_to_bv 64 0)).
Proof.
  induction fuel as [|fuel IH];
    intros rest p n regs mem Hfuel Hn1 Hn2 Hlen H1 H2 H10 H11 H12 H17 H17w
           Hbg Hread Hpa.
  { lia. }
  (* 0x10012cc: blez a0 falls through — the delivery is nonempty *)
  chain_step;
    [ reflexivity
    | eapply step_bge_ft;
      [ exact (TFv TF_10012cc) | reflexivity | exact TD_10012cc
      | getr_resolve; rewrite H10; apply c_lts_0_pos;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x10012d0: add a1,a1,a0 — bump the pointer *)
  stepiv (TFv TF_10012d0) TD_10012d0 (p + nat_to_word n)
    ltac:(getr_resolve; rewrite H11, H10; apply v_add_len_firstn; lia).
  (* 0x10012d4: sub a2,a2,a0 — decrement the count *)
  stepiv (TFv TF_10012d4) TD_10012d4 (len_word (skipn n rest))
    ltac:(getr_resolve; rewrite H12, H10; apply v_sub_len_firstn; lia).
  destruct (Nat.eq_dec n (length rest)) as [-> | Hne].
  - (* full delivery: bnez not taken, the helper returns 0 *)
    rewrite skipn_all.
    chain_step;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact (TFv TF_10012d8) | reflexivity | exact TD_10012d8
        | getr_resolve; apply c_eq_0_of_u; reflexivity ]
      | norm_pc ].
    (* 0x10012dc: li a0,0 ; 0x10012e0: ret *)
    stepiv (TFv TF_10012dc) TD_10012dc (Z_to_bv 64 0) ltac:(getr_resolve; bveq).
    stepjr (TFv TF_10012e0) TD_10012e0 (0x10012a0 : word)
      ltac:(getr_resolve; regupd_resolve; exact H1).
    apply twt_done.
    (* 0x10012a0..0x10012a8: snez a0,a0 ; slliw a0,a0,2 ; j exit tail *)
    stepi (TFv TF_10012a0) TD_10012a0.
    stepi (TFv TF_10012a4) TD_10012a4.
    stepj (TFv TF_10012a8) TD_10012a8.
    apply tgt_exit_tail.
    + regupd_resolve. exact H2.
    + getr_resolve. regupd_resolve. bveq.
    + exact Hbg.
  - (* short delivery: bnez taken, reissue on the remainder *)
    chain_step;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact (TFv TF_10012d8) | reflexivity | exact TD_10012d8
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* 0x10012c4: li a0,1 *)
    stepiv (TFv TF_10012c4) TD_10012c4 (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* 0x10012c8: the reissued write *)
    eapply twt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10012c8) eq_refl) |].
    apply twt_more; [rewrite length_skipn; lia|].
    apply (twl_write_rec rsegs (Z_to_bv 64 1)).
    + getr_resolve; regupd_resolve; exact H17.
    + regupd_resolve; reflexivity.
    + match goal with
      | |- ms_read_bytes _ (reg_get ?R 11) (reg_get ?R 12) = Some _ =>
          replace (reg_get R 11) with (p + nat_to_word n)
            by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word (skipn n rest))
            by (regupd_resolve; reflexivity)
      end.
      rewrite (ms_read_bytes_rdn rsegs) by reflexivity.
      cbn [ms_mem].
      replace (word_to_nat (len_word (skipn n rest)))
        with (length (skipn n rest))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      pose proof (SeqExec.rdn_skipn rsegs mem (length rest) p rest n
                    Hread Hn2) as Hsk.
      rewrite length_skipn. exact Hsk.
    + (* the remainder's range passes [access_ok]: inside the buffer *)
      match goal with
      | |- access_okb (reg_get ?R 11) (bv_unsigned (reg_get ?R 12)) = true =>
          replace (reg_get R 11) with (p + nat_to_word n)
            by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word (skipn n rest))
            by (regupd_resolve; reflexivity)
      end.
      apply access_okb_intro.
      pose proof (u64_range p). unfold TASK_SIZE in Hpa |- *.
      rewrite u_len_word by (rewrite length_skipn; lia).
      rewrite length_skipn, word_add_nat.
      rewrite u_Z2bv by lia.
      lia.
    + rewrite length_skipn; lia.
    + intros m Hm1 Hm2.
      norm_pc.
      eapply (IH (skipn n rest) (p + nat_to_word n) m).
      * rewrite length_skipn; lia.
      * exact Hm1.
      * exact Hm2.
      * rewrite length_skipn; lia.
      * regupd_resolve; exact H1.
      * regupd_resolve; exact H2.
      * regupd_resolve; reflexivity.
      * regupd_resolve; reflexivity.
      * regupd_resolve; reflexivity.
      * regupd_resolve; exact H17.
      * regupd_resolve; exact H17w.
      * exact Hbg.
      * pose proof (SeqExec.rdn_skipn rsegs mem (length rest) p rest n
                      Hread Hn2) as Hsk.
        rewrite length_skipn. exact Hsk.
      * rewrite length_skipn, word_add_nat.
        pose proof (u64_range p). unfold TASK_SIZE in Hpa |- *.
        rewrite u_Z2bv by lia. lia.
Qed.

(* ================================================================= *)
(* EOF continuation: from the post-read state (a0 = 0, pc 0x10011e4)  *)
(* write the last line (if any) and exit 0.                           *)
(* ================================================================= *)
Lemma tgt_eof_to_out : forall (R : bvmap 5 word) mem cur done,
  reg_get R 2 = Z_to_bv 64 (bv_unsigned tsp - 32) ->
  reg_get R 10 = Z_to_bv 64 0 ->
  reg_get R 13 = nat_to_word (length cur) ->
  reg_get R 14 = nat_to_word (length done) ->
  bgt_ok mem ->
  rdn rsegs mem t_cur (length cur) = Some cur ->
  rdn rsegs mem t_done (length done) = Some done ->
  (Z.of_nat (length cur) <= 4096)%Z -> (Z.of_nat (length done) <= 4097)%Z ->
  to_out rsegs (out (cur, done)) (mkst R 0x10011e4 mem trom).
Proof.
  intros R mem cur done H2 H10 H13 H14 Hbg Hcur Hdone Hcurcap Hdonecap.
  pose proof tsp_lo_num as Hlo. pose proof tsp_hi_num as Hhi.
  destruct cur as [|c cur'].
  - (* cur empty: the last line is [done] *)
    destruct done as [|d done'].
    + (* nothing at all: exit 0 with no write.  0x10011e4..0x10012b0 runs
         straight through to the exit tail. *)
      change (out ([], [])) with (@nil byte).
      apply tout_exit.
      sym_block (target_segs ++ vt) 6%nat [false; true; true; true] (@nil expr)
        [((10 : reg), ELit 0); ((13 : reg), ELit 0); ((14 : reg), ELit 0)]
        (@nil word) (@nil word) Rx HRx.
      { exact H10. }
      { exact H13. }
      { exact H14. }
      apply tgt_exit_tail;
        [ sym_regs HRx; exact H2 | sym_regs HRx; sym_close | exact Hbg ].
    + (* write [done], then exit 0.  0x10011e4..0x10012c4 is one block
         across the [jalr] into the write helper. *)
      change (out ([], d :: done')) with (d :: done').
      sym_block (target_segs ++ vt) 14%nat [false; true; true; false; false] (@nil expr)
        [((10 : reg), ELit 0); ((13 : reg), ELit 0); ((14 : reg), EVar 32)]
        [nat_to_word (length (d :: done'))] (@nil word) Rx HRx.
      { (* beqz a2 falls through: the line is nonempty *) scbr. }
      { (* beqz a4 falls through: [done] is nonempty *) scbr. }
      { exact H10. }
      { exact H13. }
      { exact H14. }
      eapply tout_step;
        [reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10012c8) eq_refl) |].
      apply tout_wr_rec.
      * sym_regs HRx; vm_compute; reflexivity.
      * sym_regs HRx; sym_close.
      * assert (Q11 : reg_get Rx 11 = t_done) by (sym_regs HRx; bveq).
        assert (Q12 : reg_get Rx 12 = nat_to_word (length (d :: done')))
          by (sym_regs HRx; sym_close).
        rewrite Q11, Q12.
        rewrite (ms_read_bytes_rdn rsegs) by reflexivity.
        cbn [ms_mem]. rewrite word_to_nat_ntw by lenlia.
        exact Hdone.
      * (* the line's range passes [access_ok]: a link-time buffer *)
        replace (reg_get Rx 11) with t_done by (sym_regs HRx; bveq).
        replace (reg_get Rx 12) with (nat_to_word (length (d :: done')))
          by (sym_regs HRx; sym_close).
        apply access_okb_intro.
        rewrite u_ntw by lenlia. rewrite u_t_done. unfold TASK_SIZE. lenlia.
      * (* the line is nonempty *) cbn [length]; lia.
      * (* 0x10012cc: the put-style retry loop, per delivered length *)
        assert (Q11 : reg_get Rx 11 = t_done) by (sym_regs HRx; bveq).
        assert (Q12 : reg_get Rx 12 = nat_to_word (length (d :: done')))
          by (sym_regs HRx; sym_close).
        intros n Hn1 Hn2. norm_pc.
        eapply (tgt_put_wall (length (d :: done')) (d :: done') t_done n).
        { lia. }
        { exact Hn1. }
        { exact Hn2. }
        { cbn [length] in *. lia. }
        { regupd_resolve; sym_regs HRx; sym_close. }
        { regupd_resolve; sym_regs HRx; exact H2. }
        { regupd_resolve; reflexivity. }
        { regupd_resolve; exact Q11. }
        { regupd_resolve; exact Q12. }
        { regupd_resolve; sym_regs HRx; vm_compute; reflexivity. }
        { regupd_resolve; sym_regs HRx; sym_close. }
        { exact Hbg. }
        { exact Hdone. }
        { rewrite u_t_done. unfold TASK_SIZE. lenlia. }
  - (* cur nonempty: the last line is [cur] *)
    change (out (c :: cur', done)) with (c :: cur').
    sym_block (target_segs ++ vt) 14%nat [false; true; false; false] (@nil expr)
      [((10 : reg), ELit 0); ((13 : reg), EVar 32)]
      [nat_to_word (length (c :: cur'))] (@nil word) Rx HRx.
    { (* beqz a2 falls through: the line is nonempty *) scbr. }
    { (* beqz a3 falls through: [cur] is nonempty *) scbr. }
    { exact H10. }
    { exact H13. }
    eapply tout_step;
      [reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10012c8) eq_refl) |].
    apply tout_wr_rec.
    + sym_regs HRx; vm_compute; reflexivity.
    + sym_regs HRx; sym_close.
    + assert (Q11 : reg_get Rx 11 = t_cur) by (sym_regs HRx; bveq).
      assert (Q12 : reg_get Rx 12 = nat_to_word (length (c :: cur')))
        by (sym_regs HRx; sym_close).
      rewrite Q11, Q12.
      rewrite (ms_read_bytes_rdn rsegs) by reflexivity.
      cbn [ms_mem]. rewrite word_to_nat_ntw by lenlia.
      exact Hcur.
    + (* the line's range passes [access_ok]: a link-time buffer *)
      replace (reg_get Rx 11) with t_cur by (sym_regs HRx; bveq).
      replace (reg_get Rx 12) with (nat_to_word (length (c :: cur')))
        by (sym_regs HRx; sym_close).
      apply access_okb_intro.
      rewrite u_ntw by lenlia. rewrite u_t_cur. unfold TASK_SIZE. lenlia.
    + (* the line is nonempty *) cbn [length]; lia.
    + (* 0x10012cc: the put-style retry loop, per delivered length *)
      assert (Q11 : reg_get Rx 11 = t_cur) by (sym_regs HRx; bveq).
      assert (Q12 : reg_get Rx 12 = nat_to_word (length (c :: cur')))
        by (sym_regs HRx; sym_close).
      intros n Hn1 Hn2. norm_pc.
      eapply (tgt_put_wall (length (c :: cur')) (c :: cur') t_cur n).
      { lia. }
      { exact Hn1. }
      { exact Hn2. }
      { cbn [length] in *. lia. }
      { regupd_resolve; sym_regs HRx; sym_close. }
      { regupd_resolve; sym_regs HRx; exact H2. }
      { regupd_resolve; reflexivity. }
      { regupd_resolve; exact Q11. }
      { regupd_resolve; exact Q12. }
      { regupd_resolve; sym_regs HRx; vm_compute; reflexivity. }
      { regupd_resolve; sym_regs HRx; sym_close. }
      { exact Hbg. }
      { exact Hcur. }
      { rewrite u_t_cur. unfold TASK_SIZE. lenlia. }
Qed.

(* ================================================================= *)
(* Per-block continuation: from the post-read state (a0 = |bs|,       *)
(* pc 0x10011e4) fold the block and reach the loop head or exit 3.    *)
(* ================================================================= *)
Lemma tgt_post_read_dispatch : forall (R : bvmap 5 word) mem cur done bs,
  reg_get R 2 = Z_to_bv 64 (bv_unsigned tsp - 32) ->
  reg_get R 5 = t_cur -> reg_get R 16 = t_done ->
  reg_get R 15 = Z_to_bv 64 10 -> reg_get R 11 = t_rb ->
  reg_get R 13 = nat_to_word (length cur) ->
  reg_get R 14 = nat_to_word (length done) ->
  reg_get R 10 = nat_to_word (length bs) ->
  bgt_ok mem ->
  rdn rsegs mem t_rb (length bs) = Some bs ->
  rdn rsegs mem t_cur (length cur) = Some cur ->
  rdn rsegs mem t_done (length done) = Some done ->
  (Z.of_nat (length cur) <= 4096)%Z -> (Z.of_nat (length done) <= 4097)%Z ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= 1024)%Z ->
  match procs f (cur, done) bs with
  | Some a' => lh_next rsegs tgt_LH a' (mkst R 0x10011e4 mem trom)
  | None => to_exit rsegs ec (mkst R 0x10011e4 mem trom)
  end.
Proof.
  intros R mem cur done bs H2 H5 H16 H15 H11 H13 H14 H10 Hbg Hrb Hcur Hdone
         Hcurcap Hdonecap Hblo Hbhi.
  pose proof tsp_lo_num as Hlo. pose proof tsp_hi_num as Hhi.
  (* 0x10011e4..0x10011f4: the three non-EOF tests on the read result,
     then the byte index is zeroed. *)
  sym_block_ex (target_segs ++ vt) (mkst R (Z_to_bv 64 16781796) mem trom)
    4%nat [false; false; false] (@nil expr)
    [((10 : reg), EVar 32)] [nat_to_word (length bs)] (@nil word) RG HRG Hms.
  { (* beqz a0 falls through: the block is nonempty *) scbr. }
  { (* beqz a0 falls through *) scbr. }
  { (* bltz a0 falls through: the count is non-negative *) scbr. }
  { exact H10. }
  replace (Z_to_bv 64 16781796) with (0x10011e4 : word) in Hms by bveq.
  replace (Z_to_bv 64 16781812) with (0x10011f4 : word) in Hms by bveq.
  assert (HBLH : BLHt cur done bs 0 (mkst RG 0x10011f4 mem trom)).
  { unfold BLHt. do 2 eexists. split; [reflexivity|].
    repeat split; try assumption; try lia;
      try (sym_regs HRG; first [ assumption | sym_close ]). }
  pose proof (byte_loop_t (length bs) cur done bs 0 (mkst RG 0x10011f4 mem trom)
                ltac:(lia) HBLH) as Hbl.
  rewrite skipn_O in Hbl.
  revert Hbl.
  destruct (procs f (cur, done) bs) as [a'|].
  - intros (msL & HmsL & HL).
    exists msL. split; [ eapply msteps_trans; [exact Hms | exact HmsL] | exact HL ].
  - intro Hbl. eapply msteps_to_exit_t; [exact Hms | exact Hbl].
Qed.

(* ================================================================= *)
(* One loop iteration: the DrainSim per-binary obligation.            *)
(* ================================================================= *)
Lemma tgt_LH_to_rd : forall a ms,
  tgt_LH a ms -> to_rd rsegs (Z_to_bv 64 1024) f out ec tgt_LH a ms.
Proof.
  intros a ms HLH.
  destruct a as [cur done].
  destruct HLH as (regs & mem & -> & H2 & H5 & H16 & H15 & H11 & H13 & H14
                   & Hbg & Hcur & Hdone & Hcurcap & Hdonecap).
  cbn [fst snd] in *.
  pose proof tsp_lo_num as Hlo. pose proof tsp_hi_num as Hhi.
  (* 0x10011d4: li a7,63 ; li a2,1024 ; li a0,0 ; (ecall) *)
  sym_block (target_segs ++ vt) 3%nat (@nil bool) (@nil expr) (@nil (reg * expr))
    (@nil word) (@nil word) RG HRG.
  eapply trd_step;
    [reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10011e0) eq_refl) |].
  apply trd_here_rec with (buf := t_rb).
  - sym_regs HRG; vm_compute; reflexivity.
  - sym_regs HRG; sym_close.
  - sym_regs HRG; exact H11.
  - sym_regs HRG; sym_close.
  - apply target_rb_wseg.
  - (* the buffer is a link-time constant far under [State.TASK_SIZE], so the range passes [access_ok] *)
    apply access_okb_intro. rewrite u_t_rb.
    change (bv_unsigned (Z_to_bv 64 1024)) with 1024%Z.
    unfold TASK_SIZE. lia.
  - (* EOF continuation *)
    norm_pc.
    apply tgt_eof_to_out;
      [ sym_regs HRG; exact H2
      | sym_regs HRG; sym_close
      | sym_regs HRG; exact H13
      | sym_regs HRG; exact H14
      | exact Hbg
      | exact Hcur
      | exact Hdone
      | exact Hcurcap
      | exact Hdonecap ].
  - (* the emitted line fits one modeled write *)
    apply out_modeled; [exact Hcurcap | exact Hdonecap].
  - (* per-block continuation *)
    intros bs Hblo Hbhi.
    wlits.
    apply tgt_post_read_dispatch;
      try assumption;
      try (sym_regs HRG;
           first [ reflexivity | assumption | apply len_word_nat | sym_close ]).
    + apply bgt_ok_wtm_below; [ exact Hbg | unormT; lia ].
    + apply rdn_write_to_mem. unormT. lia.
    + rewrite rdn_wtm_out
        by (unormT; first [ lia | left; lia | right; lia ]).
      exact Hcur.
    + rewrite rdn_wtm_out
        by (unormT; first [ lia | left; lia | right; lia ]).
      exact Hdone.
Qed.

(* ================================================================= *)
(* From the initial state to the loop head                            *)
(* ================================================================= *)
Lemma tgt_init_to_rd :
  to_rd rsegs (Z_to_bv 64 1024) f out ec tgt_LH a0
    (init_machine_state rsegs 0x1001190 target_phdrs tsp tmb arnd inp).
Proof.
  pose proof tsp_lo_num as Hlo. pose proof tsp_hi_num as Hhi.
  rewrite init_mkst. norm_pc.
  (* 0x1001190..0x10011d4: _start's frame and call into main, then
     main's frame and register setup.  One block across the [jalr];
     its exit memory IS [tgt_bg]. *)
  sym_block (target_segs ++ vt) 15%nat (@nil bool) (@nil expr)
    [((1 : reg), ELit 0); ((2 : reg), EVar 32)]
    [tsp] (@nil word) RG HRG.
  1-2: solve_store_ok_inv.
  (* at the loop head with a0 = ([], []) *)
  apply tgt_LH_to_rd.
  unfold tgt_LH, a0. do 2 eexists. split; [reflexivity|].
  cbn [fst snd length].
  repeat split;
    try (sym_regs HRG; first [ reflexivity | sym_close ]);
    try (exact bgt_ok_bg);
    try reflexivity;
    try lia.
Qed.

End TargetProof.


