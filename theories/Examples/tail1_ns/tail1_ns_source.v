(** * tail1-ns, source binary (musl-gcc -Os).  PROOF-SIDE FILE.

    Conventions: bytes are [byte = bv 8], machine values [word = bv 64];
    counts/indices live in registers as [nat_to_word]; sp-relative
    addresses in the canonical [Z_to_bv 64 (bv_unsigned rsp - k)] form.

    The run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  The section takes the pair as a variable [vt] and every
    derivation steps over [source_segs ++ vt]; [Proof.v] instantiates it.
    The stack bounds come from the entry predicate's launch conjunct
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
#[local] Instance tail1_ns_source_fx : FPState := fx0.

Definition rb_base : word := 0x13008.
Definition cur_base : word := 0x14410.
Definition done_base : word := 0x13408.

Lemma u_rb_base : bv_unsigned rb_base = 0x13008%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma u_cur_base : bv_unsigned cur_base = 0x14410%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma u_done_base : bv_unsigned done_base = 0x13408%Z.
Proof. vm_compute. reflexivity. Qed.

(** Collapse [bv_unsigned] of the buffer bases, [base + nat_to_word j]
    offsets and canonical sp-relative addresses to plain [Z] (window
    bounds and index bounds must be in context for the [lia] sides). *)
Local Ltac unorm :=
  imm_norm;
  pose proof u_rb_base; pose proof u_cur_base; pose proof u_done_base;
  rewrite ?word_add_nat;
  rewrite ?u_Z2bv by (rewrite ?u_rb_base, ?u_cur_base, ?u_done_base; lia);
  rewrite ?u_rb_base, ?u_cur_base, ?u_done_base.

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
    every shift as the register form, [_start]'s [slli a0,3] included. *)
Lemma v_sll_lit : forall (x : word) (sh : Z), (0 <= sh < 64)%Z ->
  v_sll x (Z_to_bv 64 sh) = v_slli x sh.
Proof.
  intros x sh Hsh. unfold v_sll, v_slli.
  rewrite u_Z2bv by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

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
  rewrite ?u_ntw by lia; unorm;
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

Section SourceProof.

(** The segments the run appends after the image's own: the vDSO pair
    ([Run.run_segments]).  Nothing below reads them. *)
Variable vt : list Segment.

Variable inp : ProcInput.
Variable Hva : valid_argv (in_argv inp).
Variable Hvl : valid_launch inp.

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
Variable Hsp_lo : (sp_window_lo <= bv_unsigned rsp)%Z.
Variable Hsp_hi : (bv_unsigned rsp <= sp_window_hi)%Z.

(** The fifth conjunct of [Run.valid_entry_va]: this placement is one a
    Linux launch can give ([create_elf_tables] and [setup_arg_pages],
    fs/binfmt_elf.c and fs/exec.c, Linux v6.18.46, commit
    1f99e9ab748f).  With [Hvl] it bounds the entry block
    ([StepTac.bsb_bound]) and places the stack-store window
    ([StoreOk.store_ok_wrap_window_valid]). *)
Variable Hlau : entry_launch_ok_va Sv48 (mkEntry rsp rbrk rmb rrnd) inp.

(** The run's segment list, and a fetch fact of the image carried to it. *)
Local Abbreviation rsegs := (source_segs ++ vt).
Local Abbreviation SFv F := (fetch_word_app _ vt _ _ F).

Lemma rsp_lo_num : (0x7fff80000000 <= bv_unsigned rsp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma rsp_hi_num : (bv_unsigned rsp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Definition argcN : word := len_word (in_argv inp).
Definition wmem : word -> option byte :=
  wrap_mem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x11154)) rsp rrnd.
Definition rrom : word -> option byte := seg_rom rsegs.

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length (in_argv inp)).
Proof.
  pose proof (valid_argv_len (in_argv inp) Hva).
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

(** The pointer _start stores into musl's [environ] slot at 0x13000. *)
Definition envp_ptr : word :=
  Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat (length (in_argv inp)) + 8).

Lemma envp_ptr_eq :
  Z_to_bv 64 (bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
                             (v_sll argcN (Z_to_bv 64 3))) + 8) = envp_ptr.
Proof.
  pose proof rsp_hi_num. pose proof rsp_lo_num.
  rewrite alu_add, (v_sll_lit argcN 3) by lia.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hlen.
  apply bv_eq. unfold envp_ptr.
  rewrite !Z_to_bv_unsigned.
  rewrite v_add_small
    by (rewrite u_Z2bv by lia; rewrite v_slli_3 by (rewrite u_argcN; lia);
        rewrite u_argcN; lia).
  rewrite u_Z2bv by lia.
  rewrite v_slli_3 by (rewrite u_argcN; lia).
  rewrite u_argcN.
  f_equal; lia.
Qed.

(* ================================================================= *)
(* Background memory: _start's environ store and main's saved-register *)
(* frame over wmem, in execution order.                               *)
(*   environ @ 0x13000 = envp_ptr ; ra @ rsp-8 = 0x11180 ;            *)
(*   s0..s3 @ rsp-16 .. rsp-40 = 0.  (gcc 15 saves only ra/s0..s3;    *)
(*   the 48-byte frame's bottom slot 0(sp) = rsp-48 is never touched.) *)
(* ================================================================= *)
Definition src_bg : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes wmem
    0x13000  (word_to_le_bytes 8 envp_ptr))
    (Z_to_bv 64 (bv_unsigned rsp - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 8))  (word_to_le_bytes 8 (0x11180 : word)).

(** [bg_ok mem]: [mem] agrees with [src_bg] on everything at or above the
    frame bottom [rsp-48].  All wrapper scratch and all buffer stores lie
    strictly below [rsp-48], so this is preserved throughout.
    (New no-overflow premise, inherited from [rdn_ext].)

    …and it is still writable wherever [wmem] was: every machine store
    targets the frame or the wrapper scratch, i.e. the RLIMIT_STACK
    window [wmem] zero-maps, and [mem] is quantified existentially in
    [src_LH], so the [store_ok] bound has to travel with it.

    The two clauses sit under ONE [forall], and [bg_ok] is SEALED
    ([Opaque], just below the preservation lemmas).  Both are needed to
    keep [repeat split] — which the scripts below use to establish the
    loop-head predicates, of which [bg_ok] is a conjunct — from taking
    it apart into halves that none of the preservation lemmas match. *)
Definition bg_ok (mem : word -> option byte) : Prop :=
  forall (a : word) (n : nat),
    ((bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
     (bv_unsigned rsp - 48 <= bv_unsigned a)%Z ->
     rdn rsegs mem a n = rdn rsegs src_bg a n)
    /\ (wmem a <> None -> mem a <> None).

(** The two projections; [bg_grows] is what the store-bound dispatcher
    reaches for (via [store_ok_db]), and both are the only way past the
    seal below. *)
Lemma bg_agree_of : forall mem, bg_ok mem ->
  forall (a : word) (n : nat),
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    (bv_unsigned rsp - 48 <= bv_unsigned a)%Z ->
    rdn rsegs mem a n = rdn rsegs src_bg a n.
Proof. intros mem H a n. apply (H a n). Qed.

Lemma bg_grows : forall mem, bg_ok mem -> mem_grows wmem mem.
Proof. intros mem H x. apply (H x 0%nat). Qed.

Local Hint Resolve bg_grows : store_ok_db.

Lemma bg_ok_bg : bg_ok src_bg.
Proof.
  assert (Hg : mem_grows wmem src_bg) by (unfold src_bg; solve_mem_grows).
  intros a n. split; [reflexivity | apply Hg].
Qed.

Lemma bg_ok_wbytes_below : forall mem (addr : word) bs,
  bg_ok mem ->
  (bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned rsp - 48)%Z ->
  bg_ok (wbytes mem addr bs).
Proof.
  intros mem addr bs Hm Hlt. pose proof (bg_grows _ Hm) as Hg.
  assert (Hg' : mem_grows wmem (wbytes mem addr bs)) by solve_mem_grows.
  intros a n. split; [|apply Hg']. intros Hnw Ha.
  rewrite rdn_wbytes_disjoint by lia. apply (bg_agree_of _ Hm); assumption.
Qed.

Lemma bg_ok_wtm_below : forall mem (buf : word) data,
  bg_ok mem ->
  (bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned rsp - 48)%Z ->
  bg_ok (write_to_mem mem buf data).
Proof.
  intros mem buf data Hm Hlt. pose proof (bg_grows _ Hm) as Hg.
  assert (Hg' : mem_grows wmem (write_to_mem mem buf data)) by solve_mem_grows.
  intros a n. split; [|apply Hg']. intros Hnw Ha.
  pose proof (u64_range rsp).
  rewrite rdn_wtm_out by first [ lia | left; lia ].
  apply (bg_agree_of _ Hm); assumption.
Qed.

(** 8-byte scratch stores below the frame preserve bg_ok. *)
Lemma bg_ok_scr8 : forall mem (a : word) v,
  bg_ok mem -> (bv_unsigned a + 8 <= bv_unsigned rsp - 48)%Z ->
  bg_ok (wbytes mem a (word_to_le_bytes 8 v)).
Proof.
  intros mem a v Hm Ha. apply bg_ok_wbytes_below; [exact Hm|].
  rewrite length_N_to_le_bytes. lia.
Qed.

(* Everything below reaches [bg_ok] only through the lemmas above; seal
   it so [repeat split] leaves it alone (see the note at the
   definition). *)
Opaque bg_ok.

(* ================================================================= *)
(* Frame-slot reads through a bg_ok memory.                          *)
(* ================================================================= *)
Local Ltac slot_read :=
  unfold src_bg;
  repeat first
    [ rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia)
    | rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia) ];
  apply rdn_wbytes_hit8; u_norm; lia.

Lemma bg_read_ra : forall mem, bg_ok mem ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
  = Some (word_to_le_bytes 8 (0x11180 : word)).
Proof.
  intros mem Hm. pose proof rsp_lo_num. pose proof rsp_hi_num.
  rewrite (bg_agree_of _ Hm) by (u_norm; lia). slot_read.
Qed.
Lemma bg_read_s0 : forall mem, bg_ok mem ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 16)) 8%nat
  = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros mem Hm. pose proof rsp_lo_num. pose proof rsp_hi_num.
  rewrite (bg_agree_of _ Hm) by (u_norm; lia). slot_read.
Qed.
Lemma bg_read_s1 : forall mem, bg_ok mem ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 24)) 8%nat
  = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros mem Hm. pose proof rsp_lo_num. pose proof rsp_hi_num.
  rewrite (bg_agree_of _ Hm) by (u_norm; lia). slot_read.
Qed.
Lemma bg_read_s2 : forall mem, bg_ok mem ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 32)) 8%nat
  = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros mem Hm. pose proof rsp_lo_num. pose proof rsp_hi_num.
  rewrite (bg_agree_of _ Hm) by (u_norm; lia). slot_read.
Qed.
Lemma bg_read_s3 : forall mem, bg_ok mem ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 40)) 8%nat
  = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros mem Hm. pose proof rsp_lo_num. pose proof rsp_hi_num.
  rewrite (bg_agree_of _ Hm) by (u_norm; lia). slot_read.
Qed.

(* ================================================================= *)
(* List helpers                                                      *)
(* ================================================================= *)

(* [firstn_snoc_nth] and [firstn_all_len] now come from Common/ListFacts
   (the snoc-peel fact is ListFacts's [firstn_S_nth]). *)

(* ================================================================= *)
(* The copy loop: cur[0..|cur|) -> done[0..|cur|)                    *)
(* ================================================================= *)
Lemma copy_loop : forall (k j : nat) (cur : list byte) (R : bvmap 5 word) mem,
  (length cur - j = k)%nat -> (j <= length cur)%nat ->
  (Z.of_nat (length cur) <= 4096)%Z ->
  reg_get R 15 = nat_to_word j -> reg_get R 8 = nat_to_word (length cur) ->
  reg_get R 18 = cur_base -> reg_get R 19 = done_base ->
  bg_ok mem ->
  rdn rsegs mem cur_base (length cur) = Some cur ->
  rdn rsegs mem done_base j = Some (firstn j cur) ->
  exists mem' (R' : bvmap 5 word),
    msteps rsegs (mkst R 0x11080 mem rrom) (mkst R' 0x11084 mem' rrom) /\
    reg_get R' 2 = reg_get R 2 /\ reg_get R' 3 = reg_get R 3 /\
    reg_get R' 8 = reg_get R 8 /\ reg_get R' 9 = reg_get R 9 /\
    reg_get R' 18 = reg_get R 18 /\ reg_get R' 19 = reg_get R 19 /\
    reg_get R' 10 = reg_get R 10 /\ reg_get R' 14 = reg_get R 14 /\
    reg_get R' 11 = reg_get R 11 /\ reg_get R' 12 = reg_get R 12 /\
    reg_get R' 13 = reg_get R 13 /\
    bg_ok mem' /\
    rdn rsegs mem' cur_base (length cur) = Some cur /\
    rdn rsegs mem' done_base (length cur) = Some cur /\
    (forall (a : word) (n : nat),
       (bv_unsigned a + Z.of_nat n <= bv_unsigned done_base)%Z ->
       rdn rsegs mem' a n = rdn rsegs mem a n).
Proof.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  intro k. induction k as [|k IH];
    intros j cur R mem Hk Hj Hcap H15 H8 H18 H19 Hbg Hcur Hdone.
  - (* j = length cur : bne a5,s0 falls through to 0x11084 *)
    assert (Hjeq : j = length cur) by lia. subst j.
    rewrite firstn_all_len in Hdone.
    exists mem, R. split.
    { eapply mst_step; [reflexivity |
        eapply step_bne_ft; [ exact (SFv SF_11080) | reflexivity | exact SD_11080 |
          getr_resolve; rewrite H15, H8; apply c_eq_refl ]
        | norm_pc; apply mst_refl ]. }
    repeat split; try reflexivity; try assumption;
      try (intros a n _; reflexivity).
  - (* j < length cur : execute one copy body, recurse *)
    assert (Hjlt : (j < length cur)%nat) by lia.
    set (mem' := wbytes mem (done_base + nat_to_word j) [nth j cur (Z_to_bv 8 0)]).
    (* Execute one copy body: 6 instructions ending back at 0x11080. *)
    assert (Hpre : exists rg, msteps rsegs (mkst R 0x11080 mem rrom)
                     (mkst rg 0x11080 mem' rrom)
                   /\ reg_get rg 15 = nat_to_word (S j)
                   /\ reg_get rg 8 = reg_get R 8 /\ reg_get rg 18 = reg_get R 18
                   /\ reg_get rg 19 = reg_get R 19
                   /\ reg_get rg 2 = reg_get R 2 /\ reg_get rg 3 = reg_get R 3
                   /\ reg_get rg 9 = reg_get R 9
                   /\ reg_get rg 10 = reg_get R 10 /\ reg_get rg 14 = reg_get R 14
                   /\ reg_get rg 11 = reg_get R 11 /\ reg_get rg 12 = reg_get R 12
                   /\ reg_get rg 13 = reg_get R 13).
    { sym_block_ex (source_segs ++ vt) (mkst R (Z_to_bv 64 69760%Z) mem rrom)
        6%nat [true] (@nil expr)
        [((15 : reg), EVar 32); ((8 : reg), EVar 33);
         ((18 : reg), ELit 82960); ((19 : reg), ELit 78856)]
        [nat_to_word j; nat_to_word (length cur)]
        [Z_to_bv 64 (bv_unsigned (nth j cur (Z_to_bv 8 0)))] R2 HR2 Hms.
      { scflat. }
      { rewrite (addr_base_ntw done_base 78856 j u_done_base ltac:(lia)).
        apply source_store_ok; unorm; lia. }
      { scflat. }
      { (* the copied byte comes out of [cur] *)
        rewrite (addr_base_ntw cur_base 82960 j u_cur_base ltac:(lia)).
        exists [nth j cur (Z_to_bv 8 0)]. split;
          [ apply (rdn_nth rsegs mem (length cur) cur_base cur j Hcur Hjlt)
          | rewrite bytes_le_to_Z_1; symmetry; apply zext_byte_u ]. }
      { (* bne a5,s0 taken: bytes remain *) brz. }
      { exact H15. }
      { exact H8. }
      { pin_lit cur_base. exact H18. }
      { pin_lit done_base. exact H19. }
      hms_norm Hms.
      rewrite (addr_base_ntw done_base 78856 j u_done_base ltac:(lia)) in Hms.
      replace (Z_to_bv 64 69760%Z) with (0x11080 : word) in Hms by bveq.
      exists R2. split; [exact Hms|].
      repeat split; sym_regs HR2;
        rewrite ?getr_nz by reg_neq_tac;
        first [ reflexivity | ntw_succ | (symmetry; assumption)
              | (rewrite H18; bveq) | (rewrite H19; bveq) ]. }
    destruct Hpre as (rg & Hpre & Hrg15 & Hrg8 & Hrg18 & Hrg19 & Hrg2 & Hrg3
                      & Hrg9 & Hrg10 & Hrg14 & Hrg11 & Hrg12 & Hrg13).
    assert (Hbg' : bg_ok mem').
    { apply bg_ok_wbytes_below; [exact Hbg|]. cbn [length]. unorm. lia. }
    assert (Hcur' : rdn rsegs mem' cur_base (length cur) = Some cur).
    { unfold mem'.
      rewrite rdn_wbytes1_out
        by (unorm; first [ lia | left; lia | right; lia ]).
      exact Hcur. }
    assert (Hdone' : rdn rsegs mem' done_base (S j) = Some (firstn (S j) cur)).
    { unfold mem'.
      replace (done_base + nat_to_word j)
        with (done_base + nat_to_word (length (firstn j cur)))
        by (rewrite length_firstn, Nat.min_l by lia; reflexivity).
      rewrite (firstn_S_nth byte cur j (Z_to_bv 8 0) Hjlt).
      replace (S j) with (length (firstn j cur) + 1)%nat
        by (rewrite length_firstn; lia).
      apply rdn_snoc_store.
      - rewrite u_done_base, length_firstn. rewrite Nat.min_l by lia. lia.
      - rewrite length_firstn, Nat.min_l by lia. exact Hdone. }
    destruct (IH (S j) cur rg mem' ltac:(lia) ltac:(lia) Hcap
                Hrg15 ltac:(rewrite Hrg8; exact H8)
                ltac:(rewrite Hrg18; exact H18) ltac:(rewrite Hrg19; exact H19)
                Hbg' Hcur' Hdone')
      as (mem'' & R'' & Hstep'' & E2 & E3 & E8 & E9 & E18 & E19 & E10 & E14
          & E11 & E12 & E13 & Hbg'' & Hcur'' & Hdone'' & Hframe'').
    exists mem'', R''. split; [eapply msteps_trans; [exact Hpre | exact Hstep'']|].
    rewrite E2, E3, E8, E9, E18, E19, E10, E14, E11, E12, E13.
    rewrite Hrg2, Hrg3, Hrg8, Hrg9, Hrg18, Hrg19, Hrg10, Hrg14,
      Hrg11, Hrg12, Hrg13.
    repeat split; try assumption.
    intros a n Ha. rewrite (Hframe'' a n Ha). unfold mem'.
    rewrite rdn_wbytes1_out
      by (unorm; first [ lia | left; lia | right; lia ]).
    reflexivity.
Qed.

(* ================================================================= *)
(* Loop-head predicate                                               *)
(* ================================================================= *)
Definition src_LH (a : A) (ms : machine_state) : Prop :=
  exists regs mem,
    ms = mkst regs 0x11030 mem rrom /\
    reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs 3 = (0x13800 : word) /\
    reg_get regs 8 = nat_to_word (length (fst a)) /\
    reg_get regs 9 = nat_to_word (length (snd a)) /\
    reg_get regs 18 = cur_base /\ reg_get regs 19 = done_base /\
    bg_ok mem /\
    rdn rsegs mem cur_base (length (fst a)) = Some (fst a) /\
    rdn rsegs mem done_base (length (snd a)) = Some (snd a) /\
    (Z.of_nat (length (fst a)) <= 4096)%Z /\
    (Z.of_nat (length (snd a)) <= 4097)%Z.

(* ================================================================= *)
(* Epilogue: from 0x110ec (a0 = code, sp = rsp-48) reach exit(code). *)
(* ================================================================= *)
(* [bltu a0,-4096] on a small non-negative count: __syscall_ret's error
   test, which every in-model return falls through. *)
Local Ltac sysret_ok :=
  unfold bv_ltu;
  replace (bv_unsigned (Z_to_bv 64 (-4096))) with 18446744073709547520%Z
    by (vm_compute; reflexivity);
  rewrite u_ntw by lenlia; apply Z.ltb_ge; lenlia.

(* A reloaded frame slot: the executor's [SCReadBase] obligation, closed
   by the slot's read-back lemma. *)
Local Ltac eslot v lem Hbg :=
  exists (word_to_le_bytes 8 v); split;
    [ apply lem; exact Hbg | vm_compute; reflexivity ].

Lemma epilogue_exit : forall code regs mem,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 10 = code -> bg_ok mem ->
  to_exit rsegs code (mkst regs 0x110ec mem rrom).
Proof.
  intros code regs mem H2 H10 Hbg.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  (* 0x110ec..0x11180: reload ra/s0..s3, pop the frame, [ret] into
     _start's tail, li a7,93 — one block across the return. *)
  sym_block (source_segs ++ vt) 9%nat (@nil bool) [ELit 70016]
    [((2 : reg), EVar 32)]
    [Z_to_bv 64 (bv_unsigned rsp - 48)] (@nil word) R HR.
  (* the reloads, in reverse execution order *)
  { eslot (Z_to_bv 64 0) bg_read_s3 Hbg. }
  { eslot (Z_to_bv 64 0) bg_read_s2 Hbg. }
  { eslot (Z_to_bv 64 0) bg_read_s1 Hbg. }
  { eslot (Z_to_bv 64 0) bg_read_s0 Hbg. }
  { eslot (0x11180 : word) bg_read_ra Hbg. }
  { exact H2. }
  eapply te_step;
    [reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_11184) eq_refl) |].
  apply te_here_rec.
  - sym_regs HR; vm_compute; reflexivity.
  - sym_regs HR. exact H10.
Qed.

(** The success return path: [li a0,0 ; snez a0,a0 ; slliw a0,a0,2]
    computes the exit code 0 from the put-loop's [w] result before
    falling into the epilogue.  (gcc 15 shares this tail with the
    write-error path, which enters at 0x110e4 with a0 = -1 and so
    yields 4 — dead in this model.) *)
Lemma epilogue_exit0 : forall regs mem,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) -> bg_ok mem ->
  to_exit rsegs (Z_to_bv 64 0) (mkst regs 0x110e0 mem rrom).
Proof.
  intros regs mem H2 Hbg.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  sym_block (source_segs ++ vt) 3%nat (@nil bool) (@nil expr) (@nil (reg * expr))
    (@nil word) (@nil word) R HR.
  apply epilogue_exit;
    [ sym_regs HR; exact H2
    | sym_regs HR; rewrite ?getr_x0z; bveq
    | exact Hbg ].
Qed.

(* ================================================================= *)
(* procs over a suffix                                               *)
(* ================================================================= *)
(* [skipn_cons_nth] now comes from Common/ListFacts. *)

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
(* Byte-loop head predicate (at 0x11058)                            *)
(* ================================================================= *)
Definition BLH (cur done bs : list byte) (i : nat) (ms : machine_state) : Prop :=
  exists regs mem,
    ms = mkst regs 0x11058 mem rrom /\
    reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs 3 = (0x13800 : word) /\
    reg_get regs 8 = nat_to_word (length cur) /\
    reg_get regs 9 = nat_to_word (length done) /\
    reg_get regs 18 = cur_base /\ reg_get regs 19 = done_base /\
    reg_get regs 10 = nat_to_word (length bs) /\
    reg_get regs 14 = nat_to_word i /\
    reg_get regs 11 = rb_base /\ reg_get regs 12 = Z_to_bv 64 4096 /\
    reg_get regs 13 = Z_to_bv 64 10 /\
    bg_ok mem /\
    rdn rsegs mem rb_base (length bs) = Some bs /\
    rdn rsegs mem cur_base (length cur) = Some cur /\
    rdn rsegs mem done_base (length done) = Some done /\
    (Z.of_nat (length cur) <= 4096)%Z /\ (Z.of_nat (length done) <= 4097)%Z /\
    (Z.of_nat (length bs) <= 1024)%Z /\ (i < length bs)%nat.

(* State at 0x11098 (the blt loop-back test), after processing byte i-1. *)
Definition C4 (cur done bs : list byte) (i : nat) (ms : machine_state) : Prop :=
  exists regs mem,
    ms = mkst regs 0x11098 mem rrom /\
    reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs 3 = (0x13800 : word) /\
    reg_get regs 8 = nat_to_word (length cur) /\
    reg_get regs 9 = nat_to_word (length done) /\
    reg_get regs 18 = cur_base /\ reg_get regs 19 = done_base /\
    reg_get regs 10 = nat_to_word (length bs) /\
    reg_get regs 14 = nat_to_word i /\
    reg_get regs 11 = rb_base /\ reg_get regs 12 = Z_to_bv 64 4096 /\
    reg_get regs 13 = Z_to_bv 64 10 /\
    bg_ok mem /\
    rdn rsegs mem rb_base (length bs) = Some bs /\
    rdn rsegs mem cur_base (length cur) = Some cur /\
    rdn rsegs mem done_base (length done) = Some done /\
    (Z.of_nat (length cur) <= 4096)%Z /\ (Z.of_nat (length done) <= 4097)%Z /\
    (Z.of_nat (length bs) <= 1024)%Z /\ (i <= length bs)%nat.

Lemma msteps_to_exit : forall code ms ms',
  msteps rsegs ms ms' -> to_exit rsegs code ms' ->
  to_exit rsegs code ms.
Proof.
  intros code ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hstep H IH]; [auto|].
  intro Hex. eapply te_step; [exact Hsvc | exact Hstep | apply IH; exact Hex].
Qed.

Lemma byte_loop : forall (k : nat) cur done bs i ms,
  (length bs - i = k)%nat -> BLH cur done bs i ms ->
  match procs f (cur, done) (skipn i bs) with
  | Some a' => exists msL, msteps rsegs ms msL /\ src_LH a' msL
  | None => to_exit rsegs ec ms
  end.
Proof.
  intro k. induction k as [|k IH];
    intros cur done bs i ms Hk HBLH;
    destruct HBLH as (regs & mem & -> & H2 & H3 & H8 & H9 & H18 & H19
                      & H10 & H14 & H11 & H12 & H13 & Hbg & Hrb & Hcur & Hdone
                      & Hcurcap & Hdonecap & Hbscap & Hi);
    pose proof rsp_lo_num as Hlo; pose proof rsp_hi_num as Hhi.
  { lia. }
  remember (nth i bs (Z_to_bv 8 0)) as b eqn:Hbdef.
  (* Dispatch helper at 0x11098 (uses IH). *)
  assert (Hdisp : forall cur' done' st, C4 cur' done' bs (S i) st ->
    match procs f (cur', done') (skipn (S i) bs) with
    | Some a'' => exists msL, msteps rsegs st msL /\ src_LH a'' msL
    | None => to_exit rsegs ec st end).
  { intros cur' done' st HC4.
    destruct HC4 as (rg & mm & -> & G2 & G3 & G8 & G9 & G18 & G19
                     & G10 & G14 & G11 & G12 & G13 & Hbg' & Hrb' & Hcur' & Hdone'
                     & Hcurcap' & Hdonecap' & Hbscap' & Hle).
    destruct (Nat.eq_dec (S i) (length bs)) as [Heq | Hne].
    - rewrite skipn_all2 by lia. cbn [procs].
      eexists. split.
      + eapply mst_step; [reflexivity |
          eapply step_blt_ft; [ exact (SFv SF_11098) | reflexivity | exact SD_11098
            | getr_resolve; rewrite G14, G10;
              rewrite c_lts_ntw by lia; apply Z.ltb_ge; lia ]
          | norm_pc ].
        stepj (SFv SF_1109c) SD_1109c. apply mst_refl.
      + unfold src_LH. do 2 eexists. split; [reflexivity|].
        repeat split; try assumption.
    - assert (Hlt2 : (S i < length bs)%nat) by lia.
      assert (HBLH' : BLH cur' done' bs (S i) (mkst rg 0x11058 mm rrom)).
      { unfold BLH. do 2 eexists. split; [reflexivity|]. repeat split; assumption. }
      assert (Hbody : msteps rsegs (mkst rg 0x11098 mm rrom)
                        (mkst rg 0x11058 mm rrom)).
      { eapply mst_step; [reflexivity |
          eapply step_blt_tk; [ exact (SFv SF_11098) | reflexivity | exact SD_11098
            | getr_resolve; rewrite G14, G10;
              rewrite c_lts_ntw by lia; apply Z.ltb_lt; lia ]
          | norm_pc ].
        apply mst_refl. }
      pose proof (IH cur' done' bs (S i) (mkst rg 0x11058 mm rrom)
                    ltac:(lia) HBLH') as Hih.
      destruct (procs f (cur', done') (skipn (S i) bs)) as [a''|] eqn:Ep.
      + destruct Hih as (msL & Hs & HL). exists msL.
        split; [eapply msteps_trans; [exact Hbody | exact Hs] | exact HL].
      + eapply msteps_to_exit; [exact Hbody | exact Hih]. }
  (* Load the byte: 0x11058 add a5,a1,a4 ; 0x1105c lbu a5,0(a5). *)
  destruct (bv_eqb b (Z_to_bv 8 10)) eqn:Eb.
  - (* ===== newline byte ===== *)
    assert (Hf : f (cur, done) b = Some ([], cur ++ [Z_to_bv 8 10]))
      by (unfold f; rewrite Eb; reflexivity).
    replace (procs f (cur, done) (skipn i bs))
      with (procs f ([], cur ++ [Z_to_bv 8 10]) (skipn (S i) bs))
      by (rewrite (procs_skipn_step bs i (cur, done) Hi);
          rewrite <- Hbdef, Hf; reflexivity).
    (* Step 0x11058..0x11080 (into the copy loop head). *)
    assert (Hac : exists Rac, msteps rsegs (mkst regs 0x11058 mem rrom)
                     (mkst Rac 0x11080 mem rrom)
                  /\ reg_get Rac 15 = nat_to_word 0
                  /\ reg_get Rac 8 = nat_to_word (length cur)
                  /\ reg_get Rac 18 = cur_base
                  /\ reg_get Rac 19 = done_base
                  /\ reg_get Rac 2 = Z_to_bv 64 (bv_unsigned rsp - 48)
                  /\ reg_get Rac 3 = (0x13800 : word)
                  /\ reg_get Rac 9 = nat_to_word (length done)
                  /\ reg_get Rac 10 = nat_to_word (length bs)
                  /\ reg_get Rac 14 = nat_to_word i
                  /\ reg_get Rac 11 = rb_base
                  /\ reg_get Rac 12 = Z_to_bv 64 4096
                  /\ reg_get Rac 13 = Z_to_bv 64 10).
    { sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 69720%Z) mem rrom)
        5%nat [false] (@nil expr)
        [((11 : reg), ELit 77832); ((13 : reg), ELit 10); ((14 : reg), EVar 32)]
        [nat_to_word i] [Z_to_bv 64 (bv_unsigned b)] Rac HRac Hms.
      { (* bne a5,a3 NOT taken: this byte IS the newline *)
        apply negb_false_iff. rewrite c_eq_zext10. exact Eb. }
      { scflat. }
      { rewrite (addr_base_ntw rb_base 77832 i u_rb_base ltac:(lia)).
        exists [b]. split;
          [ rewrite Hbdef;
            apply (rdn_nth rsegs mem (length bs) rb_base bs i Hrb Hi)
          | rewrite bytes_le_to_Z_1; symmetry; apply zext_byte_u ]. }
      { pin_lit rb_base. exact H11. }
      { exact H13. }
      { exact H14. }
      hms_norm Hms.
      replace (Z_to_bv 64 69720%Z) with (0x11058 : word) in Hms by bveq.
      replace (Z_to_bv 64 69760%Z) with (0x11080 : word) in Hms by bveq.
      exists Rac. split; [exact Hms|].
      repeat split; sym_regs HRac;
        rewrite ?getr_nz by reg_neq_tac;
        first [ reflexivity | assumption | bveq ]. }
    destruct Hac as (Rac & Hms_ac & GRac15 & GRac8 & GRac18 & GRac19 & GRac2
                     & GRac3 & GRac9 & GRac10 & GRac14 & GRac11
                     & GRac12 & GRac13).
    destruct (copy_loop (length cur) 0 cur Rac mem ltac:(lia) ltac:(lia) Hcurcap
                GRac15 GRac8 GRac18 GRac19 Hbg Hcur ltac:(reflexivity))
      as (mem_c & Rc & Hcopy & Cc2 & Cc3 & Cc8 & Cc9 & Cc18 & Cc19 & Cc10
          & Cc14 & Cc11 & Cc12 & Cc13 & Hbg_c & Hcur_c & Hdone_c & Hframe_c).
    (* Step 0x11084..0x11098: add a5 ; addi s1 ; sb done[|cur|]=10 ; li s0 ;
       addi a4. *)
    set (memD := wbytes mem_c (done_base + nat_to_word (length cur))
                   [Z_to_bv 8 10]).
    assert (Hc4 : exists Rd, msteps rsegs (mkst Rc 0x11084 mem_c rrom)
                     (mkst Rd 0x11098 memD rrom)
                  /\ reg_get Rd 2 = Z_to_bv 64 (bv_unsigned rsp - 48)
                  /\ reg_get Rd 3 = (0x13800 : word)
                  /\ reg_get Rd 8 = nat_to_word 0
                  /\ reg_get Rd 9 = nat_to_word (S (length cur))
                  /\ reg_get Rd 18 = cur_base /\ reg_get Rd 19 = done_base
                  /\ reg_get Rd 10 = nat_to_word (length bs)
                  /\ reg_get Rd 14 = nat_to_word (S i)
                  /\ reg_get Rd 11 = rb_base
                  /\ reg_get Rd 12 = Z_to_bv 64 4096
                  /\ reg_get Rd 13 = Z_to_bv 64 10).
    { sym_block_ex (source_segs ++ vt) (mkst Rc (Z_to_bv 64 69764%Z) mem_c rrom)
        5%nat (@nil bool) (@nil expr)
        [((19 : reg), ELit 78856); ((8 : reg), EVar 32);
         ((13 : reg), ELit 10); ((14 : reg), EVar 33)]
        [nat_to_word (length cur); nat_to_word i] (@nil word) Rd HRd Hms.
      { scflat. }
      { rewrite (addr_base_ntw done_base 78856 (length cur) u_done_base
                   ltac:(lia)).
        apply source_store_ok; unorm; lia. }
      { pin_lit done_base. exact (eq_trans Cc19 GRac19). }
      { exact (eq_trans Cc8 GRac8). }
      { exact (eq_trans Cc13 GRac13). }
      { exact (eq_trans Cc14 GRac14). }
      hms_norm Hms.
      rewrite (addr_base_ntw done_base 78856 (length cur) u_done_base
                 ltac:(lia)) in Hms.
      replace (word_to_le_bytes 1 (Z_to_bv 64 10)) with [Z_to_bv 8 10] in Hms
        by (vm_compute; reflexivity).
      replace (Z_to_bv 64 69764%Z) with (0x11084 : word) in Hms by bveq.
      replace (Z_to_bv 64 69784%Z) with (0x11098 : word) in Hms by bveq.
      exists Rd. split; [unfold memD; exact Hms|].
      repeat split; sym_regs HRd;
        rewrite ?getr_nz by reg_neq_tac;
        rewrite ?Cc2, ?Cc3, ?Cc8, ?Cc9, ?Cc18, ?Cc19, ?Cc10, ?Cc14,
                ?Cc11, ?Cc12, ?Cc13;
        first [ reflexivity | ntw_succ | assumption | bveq ]. }
    destruct Hc4 as (Rd & Hms_d & GRd2 & GRd3 & GRd8 & GRd9 & GRd18 & GRd19
                     & GRd10 & GRd14 & GRd11 & GRd12 & GRd13).
    (* Assemble C4 for a' = ([], cur ++ [10]). *)
    assert (HC4 : C4 [] (cur ++ [Z_to_bv 8 10]) bs (S i)
                    (mkst Rd 0x11098 memD rrom)).
    { unfold C4. do 2 eexists. split; [reflexivity|].
      repeat split; try assumption.
      - rewrite GRd9. f_equal. rewrite length_app. cbn [length]. lia.
      - (* bg_ok memD *)
        apply bg_ok_wbytes_below; [exact Hbg_c|].
        cbn [length]. unorm. lia.
      - (* rb read-back through memD *)
        unfold memD.
        rewrite rdn_wbytes1_out
          by (unorm; first [ lia | left; lia | right; lia ]).
        rewrite (Hframe_c rb_base (length bs)) by (unorm; lia).
        exact Hrb.
      - (* done' = cur ++ [10] read-back *)
        unfold memD. rewrite length_app. cbn [length].
        apply rdn_snoc_store.
        + rewrite u_done_base. lia.
        + exact Hdone_c.
      - (* |cur'| <= 4096 *) cbn [length]; lia.
      - (* |done'| <= 4097 *) rewrite length_app; cbn [length]; lia. }
    pose proof (Hdisp [] (cur ++ [Z_to_bv 8 10]) (mkst Rd 0x11098 memD rrom) HC4)
      as Hd.
    assert (Hall : msteps rsegs (mkst regs 0x11058 mem rrom)
                     (mkst Rd 0x11098 memD rrom)).
    { eapply msteps_trans; [exact Hms_ac |].
      eapply msteps_trans; [exact Hcopy | exact Hms_d]. }
    revert Hd.
    destruct (procs f ([], cur ++ [Z_to_bv 8 10]) (skipn (S i) bs)) as [a''|].
    + intros (msL & Hs & HL). exists msL.
      split; [eapply msteps_trans; [exact Hall | exact Hs] | exact HL].
    + intro Hd. eapply msteps_to_exit; [exact Hall | exact Hd].
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
      (* 0x11058..0x110ec: the byte is not a newline and the line is
         already 4096 bytes, so main jumps to exit(3). *)
      sym_block (source_segs ++ vt) 6%nat [true; true] (@nil expr)
        [((11 : reg), ELit 77832); ((13 : reg), ELit 10);
         ((14 : reg), EVar 32); ((8 : reg), EVar 33); ((12 : reg), ELit 4096)]
        [nat_to_word i; nat_to_word (length cur)]
        [Z_to_bv 64 (bv_unsigned b)] Rx HRx.
      { (* the line is already 4096 bytes *) scbr. }
      { (* bne a5,a3 taken: this byte is not the newline *)
        apply negb_true_iff. rewrite c_eq_zext10. exact Eb. }
      { scflat. }
      { (* the byte comes out of the read buffer *)
        rewrite (addr_base_ntw rb_base 77832 i u_rb_base ltac:(lia)).
        exists [b]. split;
          [ rewrite Hbdef;
            apply (rdn_nth rsegs mem (length bs) rb_base bs i Hrb Hi)
          | rewrite bytes_le_to_Z_1; symmetry; apply zext_byte_u ]. }
      { pin_lit rb_base. exact H11. }
      { exact H13. }
      { exact H14. }
      { exact H8. }
      { exact H12. }
      apply epilogue_exit;
        [ sym_regs HRx; exact H2 | sym_regs HRx; sym_close | exact Hbg ].
    + (* append the byte to cur *)
      assert (Hf : f (cur, done) b = Some (cur ++ [b], done)).
      { unfold f. rewrite Eb.
        rewrite (proj2 (Z.leb_gt 4096 (Z.of_nat (length cur))) Hlt).
        reflexivity. }
      replace (procs f (cur, done) (skipn i bs))
        with (procs f (cur ++ [b], done) (skipn (S i) bs))
        by (rewrite (procs_skipn_step bs i (cur, done) Hi);
            rewrite <- Hbdef, Hf; reflexivity).
      set (memC := wbytes mem (cur_base + nat_to_word (length cur)) [b]).
      assert (Hc4 : exists Rd, msteps rsegs (mkst regs 0x11058 mem rrom)
                       (mkst Rd 0x11098 memC rrom)
                    /\ reg_get Rd 2 = Z_to_bv 64 (bv_unsigned rsp - 48)
                    /\ reg_get Rd 3 = (0x13800 : word)
                    /\ reg_get Rd 8 = nat_to_word (S (length cur))
                    /\ reg_get Rd 9 = nat_to_word (length done)
                    /\ reg_get Rd 18 = cur_base /\ reg_get Rd 19 = done_base
                    /\ reg_get Rd 10 = nat_to_word (length bs)
                    /\ reg_get Rd 14 = nat_to_word (S i)
                    /\ reg_get Rd 11 = rb_base
                    /\ reg_get Rd 12 = Z_to_bv 64 4096
                    /\ reg_get Rd 13 = Z_to_bv 64 10).
      { sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 69720%Z) mem rrom)
          9%nat [true; false] (@nil expr)
          [((11 : reg), ELit 77832); ((13 : reg), ELit 10);
           ((14 : reg), EVar 32); ((8 : reg), EVar 33);
           ((12 : reg), ELit 4096); ((18 : reg), ELit 82960)]
          [nat_to_word i; nat_to_word (length cur)]
          [Z_to_bv 64 (bv_unsigned b)] Rd HRd Hms.
        { scflat. }
        { rewrite (addr_base_ntw cur_base 82960 (length cur) u_cur_base
                     ltac:(lia)).
          apply source_store_ok; unorm; lia. }
        { (* beq s0,a2 falls through: the line still has room *) scbr. }
        { (* bne a5,a3 taken: this byte is not the newline *)
          apply negb_true_iff. rewrite c_eq_zext10. exact Eb. }
        { scflat. }
        { rewrite (addr_base_ntw rb_base 77832 i u_rb_base ltac:(lia)).
          exists [b]. split;
            [ rewrite Hbdef;
              apply (rdn_nth rsegs mem (length bs) rb_base bs i Hrb Hi)
            | rewrite bytes_le_to_Z_1; symmetry; apply zext_byte_u ]. }
        { pin_lit rb_base. exact H11. }
        { exact H13. }
        { exact H14. }
        { exact H8. }
        { exact H12. }
        { pin_lit cur_base. exact H18. }
        hms_norm Hms.
        rewrite (addr_base_ntw cur_base 82960 (length cur) u_cur_base
                   ltac:(lia)) in Hms.
        replace (Z_to_bv 64 69720%Z) with (0x11058 : word) in Hms by bveq.
        replace (Z_to_bv 64 69784%Z) with (0x11098 : word) in Hms by bveq.
        exists Rd. split; [unfold memC; exact Hms|].
        repeat split; sym_regs HRd;
          rewrite ?getr_nz by reg_neq_tac;
          first [ reflexivity | ntw_succ | assumption | bveq ]. }
      destruct Hc4 as (Rd & Hms_d & GRd2 & GRd3 & GRd8 & GRd9 & GRd18 & GRd19
                       & GRd10 & GRd14 & GRd11 & GRd12 & GRd13).
      assert (HC4 : C4 (cur ++ [b]) done bs (S i) (mkst Rd 0x11098 memC rrom)).
      { unfold C4. do 2 eexists. split; [reflexivity|].
        repeat split; try assumption.
        - rewrite GRd8. f_equal. rewrite length_app. cbn [length]. lia.
        - apply bg_ok_wbytes_below; [exact Hbg|]. cbn [length]. unorm. lia.
        - unfold memC.
          rewrite rdn_wbytes1_out
            by (unorm; first [ lia | left; lia | right; lia ]).
          exact Hrb.
        - unfold memC. rewrite length_app. cbn [length].
          apply rdn_snoc_store.
          + rewrite u_cur_base. lia.
          + exact Hcur.
        - unfold memC.
          rewrite rdn_wbytes1_out
            by (unorm; first [ lia | left; lia | right; lia ]).
          exact Hdone.
        - rewrite length_app. cbn [length]. lia. }
      pose proof (Hdisp (cur ++ [b]) done (mkst Rd 0x11098 memC rrom) HC4) as Hd.
      revert Hd.
      destruct (procs f (cur ++ [b], done) (skipn (S i) bs)) as [a''|].
      * intros (msL & Hs & HL). exists msL.
        split; [eapply msteps_trans; [exact Hms_d | exact Hs] | exact HL].
      * intro Hd. eapply msteps_to_exit; [exact Hms_d | exact Hd].
Qed.

(* ================================================================= *)
(* The two put-style write-all retry loops                            *)
(* ================================================================= *)

(** The [sub]/[add] the retry loop performs on its count/pointer, in
    the [nat_to_word] spelling the symbolic pins use (the [len_word]
    forms are [WallSim]'s [v_sub_len_firstn]/[v_add_len_firstn]). *)
Lemma v_sub_ntw : forall (m k : nat), (k <= m)%nat -> (Z.of_nat m < 2^64)%Z ->
  v_sub (nat_to_word m) (nat_to_word k) = nat_to_word (m - k).
Proof.
  intros m k Hk Hm. apply bv_eq.
  rewrite v_sub_small by (rewrite !u_ntw by lia; lia).
  rewrite !u_ntw by lia. lia.
Qed.

Lemma v_add_ntw : forall (p : word) (k : nat),
  v_add p (nat_to_word k) = p + nat_to_word k.
Proof.
  intros p k. unfold v_add. apply bv_eq.
  rewrite Z_to_bv_unsigned, bv_add_unsigned. reflexivity.
Qed.

(** gcc compiles the two EOF writes as two copies of the same put-style
    retry loop, differing only in which callee-saved register holds the
    pointer and which the count:

      done: head 0x11118 (a2=s1 count, a1=s0 ptr), ra = 0x11128
      cur : head 0x110c0 (a2=s0 count, a1=s1 ptr), ra = 0x110d0

    Both call musl's [write] at 0x111e0, so each iteration runs the
    wrapper frame/shuffle, [__syscall_cp]'s trampoline and its seven
    shuffles down to the [ecall] at 0x11268, and comes back at 0x1126c
    through [__syscall_ret]'s error test into [blez a0 ; sub ; add ;
    bnez].  Every delivery is nonempty, so the remainder strictly
    shrinks; the loop's only memory effect is the wrapper's [sd ra,8(sp)]
    at [rsp-56], below the [bg_ok] window.  On the last delivery both
    fall into 0x110e0, the exit-code-0 tail.

    The two proofs below are near-copies as a result: their
    short-delivery arms — the 49 lines from the wrapper [sym_block] down
    to the recursive call — are identical but for a single line, the pin
    list, where the pointer and count registers swap.  That pair is
    deliberately not factored into a shared tactic.  Ltac1 resolves a
    free identifier in a term when the tactic is defined rather than
    against the goal it runs on, so every context name the arm mentions
    has to become a parameter: [rsp], [p], [n], [rest], [mem], [RC],
    [HRC], [Q2], [Q8], [Q9], [Hread], [Hn2], [Hsk], [m], [Hm1], [Hm2],
    [IH] and [Hbg] — eighteen, all passed identically at both sites,
    beside the two register indices that actually differ.  A
    twenty-argument tactic is a worse interface than the copy it
    removes; this is the same measurement recorded for
    [MuslCall.musl_write_wall].  So keep the two arms in step by hand,
    and note that the pin list is the only line entitled to differ.

    Induction on [fuel >= length rest]. *)

Lemma src_put_wall_done : forall fuel (rest : list byte) (p : word) n regs mem,
  (length rest <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length rest)%nat ->
  (Z.of_nat (length rest) <= 4097)%Z ->
  (0x13000 <= bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) <= 0x16000)%Z ->
  reg_get regs 1 = (0x11208 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ->
  reg_get regs 8 = p ->
  reg_get regs 9 = nat_to_word (length rest) ->
  reg_get regs 10 = nat_to_word n ->
  bg_ok mem ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8%nat
    = Some (word_to_le_bytes 8 (0x11128 : word)) ->
  rdn rsegs mem p (length rest) = Some rest ->
  to_wall_tail rsegs (Z_to_bv 64 1)
    (mkst regs (0x1126c : word) mem rrom) (skipn n rest)
    (to_exit rsegs (Z_to_bv 64 0)).
Proof.
  induction fuel as [|fuel IH];
    intros rest p n regs mem Hfuel Hn1 Hn2 Hlen Hplo Hphi
           H1 H2 H8 H9 H10 Hbg Hra Hread.
  { lia. }
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  assert (Hpn : bv_unsigned (p + nat_to_word n)
                = (bv_unsigned p + Z.of_nat n)%Z)
    by (rewrite word_add_nat; apply u_Z2bv; lia).
  (* 0x1126c..0x11130: pop the wrapper frame, pass __syscall_ret, then
     main's [blez a0 ; sub s1,s1,a0 ; add s0,s0,a0]. *)
  sym_block (source_segs ++ vt) 10%nat [false; false] [ELit 69928]
    [((1 : reg), ELit 70152); ((2 : reg), EVar 32); ((8 : reg), EVar 33);
     ((9 : reg), EVar 34); ((10 : reg), EVar 35)]
    [Z_to_bv 64 (bv_unsigned rsp - 64); p; nat_to_word (length rest);
     nat_to_word n] (@nil word) RB HRB.
  all: try (first [ scbr | sysret_ok
                  | (exists (word_to_le_bytes 8 (0x11128 : word)); split;
                     [ exact Hra | vm_compute; reflexivity ])
                  | (pin_lit (0x11208 : word); exact H1)
                  | exact H2 | exact H8 | exact H9 | exact H10 ]).
  assert (Q2 : reg_get RB 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    by (sym_regs HRB; sym_close).
  assert (Q8 : reg_get RB 8 = p + nat_to_word n)
    by (sym_regs HRB; apply v_add_ntw).
  assert (Q9 : reg_get RB 9 = nat_to_word (length rest - n))
    by (sym_regs HRB; apply v_sub_ntw; lia).
  destruct (Nat.eq_dec n (length rest)) as [-> | Hne].
  - (* full delivery: bnez not taken, j into the exit-code-0 tail *)
    rewrite skipn_all.
    step_intro;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact (SFv SF_11134) | reflexivity | exact SD_11134
        | getr_resolve; rewrite Q9; apply c_eq_0_of_u;
          rewrite u_ntw by lia; lia ]
      | norm_pc ].
    stepj (SFv SF_11138) SD_11138.
    apply twt_done.
    apply epilogue_exit0; [ exact Q2 | exact Hbg ].
  - (* short delivery: bnez taken, reissue on the remainder *)
    step_intro;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact (SFv SF_11134) | reflexivity | exact SD_11134
        | getr_resolve; rewrite Q9; apply c_eq_0_false;
          rewrite u_ntw by lia; lia ]
      | norm_pc ].
    (* 0x11118..0x11268: main's three arguments, musl's wrapper frame,
       shuffle and [sd ra,8(sp)] spill, __syscall_cp's trampoline and
       shuffles.  The executor stops of its own accord at the ecall. *)
    sym_block (source_segs ++ vt) 40%nat (@nil bool) (@nil expr)
      [((2 : reg), EVar 32); ((8 : reg), EVar 33); ((9 : reg), EVar 34)]
      [Z_to_bv 64 (bv_unsigned rsp - 48); p + nat_to_word n;
       nat_to_word (length rest - n)] (@nil word) RC HRC.
    all: try (first [ (apply source_store_ok; imm_norm; u_norm; lia)
                    | solve_store_ok_inv
                    | exact Q2 | exact Q8 | exact Q9 ]).
    eapply twt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_11268) eq_refl) |].
    apply twt_more; [rewrite length_skipn; lia|].
    apply (twl_write_rec rsegs (Z_to_bv 64 1)).
    + sym_regs HRC; vm_compute; reflexivity.
    + sym_regs HRC; sym_close.
    + match goal with
      | |- ms_read_bytes _ (reg_get ?R 11) (reg_get ?R 12) = Some _ =>
          replace (reg_get R 11) with (p + nat_to_word n)
            by (sym_regs HRC; sym_close);
          replace (reg_get R 12) with (nat_to_word (length rest - n))
            by (sym_regs HRC; sym_close)
      end.
      rewrite (ms_read_bytes_rdn rsegs) by reflexivity.
      cbn [ms_mem]. rewrite word_to_nat_ntw by lia.
      rewrite !rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; u_norm; lia).
      pose proof (SeqExec.rdn_skipn rsegs mem (length rest) p rest n
                    Hread Hn2) as Hsk.
      exact Hsk.
    + (* the remainder's range passes [access_ok]: inside .data/.bss *)
      match goal with
      | |- access_okb (reg_get ?R 11) (bv_unsigned (reg_get ?R 12)) = true =>
          replace (reg_get R 11) with (p + nat_to_word n)
            by (sym_regs HRC; sym_close);
          replace (reg_get R 12) with (nat_to_word (length rest - n))
            by (sym_regs HRC; sym_close)
      end.
      apply access_okb_intro.
      rewrite Hpn, u_ntw by lia. unfold TASK_SIZE. lia.
    + rewrite length_skipn; lia.
    + intros m Hm1 Hm2.
      norm_pc.
      eapply (IH (skipn n rest) (p + nat_to_word n) m).
      * rewrite length_skipn; lia.
      * exact Hm1.
      * exact Hm2.
      * rewrite length_skipn; lia.
      * lia.
      * rewrite length_skipn; lia.
      * regupd_resolve; sym_regs HRC; sym_close.
      * regupd_resolve; sym_regs HRC; sym_close.
      * regupd_resolve; sym_regs HRC; sym_close.
      * regupd_resolve; sym_regs HRC; rewrite length_skipn; sym_close.
      * regupd_resolve; apply len_word_firstn_nat; exact Hm2.
      * apply bg_ok_scr8; [ exact Hbg | u_norm; lia ].
      * apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite !rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes, ?length_skipn; u_norm; lia).
        pose proof (SeqExec.rdn_skipn rsegs mem (length rest) p rest n
                      Hread Hn2) as Hsk.
        rewrite length_skipn. exact Hsk.
Qed.

Lemma src_put_wall_cur : forall fuel (rest : list byte) (p : word) n regs mem,
  (length rest <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length rest)%nat ->
  (Z.of_nat (length rest) <= 4097)%Z ->
  (0x13000 <= bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) <= 0x16000)%Z ->
  reg_get regs 1 = (0x11208 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ->
  reg_get regs 9 = p ->
  reg_get regs 8 = nat_to_word (length rest) ->
  reg_get regs 10 = nat_to_word n ->
  bg_ok mem ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8%nat
    = Some (word_to_le_bytes 8 (0x110d0 : word)) ->
  rdn rsegs mem p (length rest) = Some rest ->
  to_wall_tail rsegs (Z_to_bv 64 1)
    (mkst regs (0x1126c : word) mem rrom) (skipn n rest)
    (to_exit rsegs (Z_to_bv 64 0)).
Proof.
  induction fuel as [|fuel IH];
    intros rest p n regs mem Hfuel Hn1 Hn2 Hlen Hplo Hphi
           H1 H2 H9 H8 H10 Hbg Hra Hread.
  { lia. }
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  assert (Hpn : bv_unsigned (p + nat_to_word n)
                = (bv_unsigned p + Z.of_nat n)%Z)
    by (rewrite word_add_nat; apply u_Z2bv; lia).
  (* 0x1126c..0x110d8: as above, with s0 the count and s1 the pointer. *)
  sym_block (source_segs ++ vt) 10%nat [false; false] [ELit 69840]
    [((1 : reg), ELit 70152); ((2 : reg), EVar 32); ((9 : reg), EVar 33);
     ((8 : reg), EVar 34); ((10 : reg), EVar 35)]
    [Z_to_bv 64 (bv_unsigned rsp - 64); p; nat_to_word (length rest);
     nat_to_word n] (@nil word) RB HRB.
  all: try (first [ scbr | sysret_ok
                  | (exists (word_to_le_bytes 8 (0x110d0 : word)); split;
                     [ exact Hra | vm_compute; reflexivity ])
                  | (pin_lit (0x11208 : word); exact H1)
                  | exact H2 | exact H8 | exact H9 | exact H10 ]).
  assert (Q2 : reg_get RB 2 = Z_to_bv 64 (bv_unsigned rsp - 48))
    by (sym_regs HRB; sym_close).
  assert (Q9 : reg_get RB 9 = p + nat_to_word n)
    by (sym_regs HRB; apply v_add_ntw).
  assert (Q8 : reg_get RB 8 = nat_to_word (length rest - n))
    by (sym_regs HRB; apply v_sub_ntw; lia).
  destruct (Nat.eq_dec n (length rest)) as [-> | Hne].
  - (* full delivery: bnez not taken, fall into the exit-code-0 tail *)
    rewrite skipn_all.
    step_intro;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact (SFv SF_110dc) | reflexivity | exact SD_110dc
        | getr_resolve; rewrite Q8; apply c_eq_0_of_u;
          rewrite u_ntw by lia; lia ]
      | norm_pc ].
    apply twt_done.
    apply epilogue_exit0; [ exact Q2 | exact Hbg ].
  - (* short delivery: bnez taken, reissue on the remainder *)
    step_intro;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact (SFv SF_110dc) | reflexivity | exact SD_110dc
        | getr_resolve; rewrite Q8; apply c_eq_0_false;
          rewrite u_ntw by lia; lia ]
      | norm_pc ].
    (* 0x110c0..0x11268: the reissued write, down to the ecall. *)
    sym_block (source_segs ++ vt) 40%nat (@nil bool) (@nil expr)
      [((2 : reg), EVar 32); ((9 : reg), EVar 33); ((8 : reg), EVar 34)]
      [Z_to_bv 64 (bv_unsigned rsp - 48); p + nat_to_word n;
       nat_to_word (length rest - n)] (@nil word) RC HRC.
    all: try (first [ (apply source_store_ok; imm_norm; u_norm; lia)
                    | solve_store_ok_inv
                    | exact Q2 | exact Q8 | exact Q9 ]).
    eapply twt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_11268) eq_refl) |].
    apply twt_more; [rewrite length_skipn; lia|].
    apply (twl_write_rec rsegs (Z_to_bv 64 1)).
    + sym_regs HRC; vm_compute; reflexivity.
    + sym_regs HRC; sym_close.
    + match goal with
      | |- ms_read_bytes _ (reg_get ?R 11) (reg_get ?R 12) = Some _ =>
          replace (reg_get R 11) with (p + nat_to_word n)
            by (sym_regs HRC; sym_close);
          replace (reg_get R 12) with (nat_to_word (length rest - n))
            by (sym_regs HRC; sym_close)
      end.
      rewrite (ms_read_bytes_rdn rsegs) by reflexivity.
      cbn [ms_mem]. rewrite word_to_nat_ntw by lia.
      rewrite !rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; u_norm; lia).
      pose proof (SeqExec.rdn_skipn rsegs mem (length rest) p rest n
                    Hread Hn2) as Hsk.
      exact Hsk.
    + (* the remainder's range passes [access_ok]: inside .data/.bss *)
      match goal with
      | |- access_okb (reg_get ?R 11) (bv_unsigned (reg_get ?R 12)) = true =>
          replace (reg_get R 11) with (p + nat_to_word n)
            by (sym_regs HRC; sym_close);
          replace (reg_get R 12) with (nat_to_word (length rest - n))
            by (sym_regs HRC; sym_close)
      end.
      apply access_okb_intro.
      rewrite Hpn, u_ntw by lia. unfold TASK_SIZE. lia.
    + rewrite length_skipn; lia.
    + intros m Hm1 Hm2.
      norm_pc.
      eapply (IH (skipn n rest) (p + nat_to_word n) m).
      * rewrite length_skipn; lia.
      * exact Hm1.
      * exact Hm2.
      * rewrite length_skipn; lia.
      * lia.
      * rewrite length_skipn; lia.
      * regupd_resolve; sym_regs HRC; sym_close.
      * regupd_resolve; sym_regs HRC; sym_close.
      * regupd_resolve; sym_regs HRC; sym_close.
      * regupd_resolve; sym_regs HRC; rewrite length_skipn; sym_close.
      * regupd_resolve; apply len_word_firstn_nat; exact Hm2.
      * apply bg_ok_scr8; [ exact Hbg | u_norm; lia ].
      * apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite !rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes, ?length_skipn; u_norm; lia).
        pose proof (SeqExec.rdn_skipn rsegs mem (length rest) p rest n
                      Hread Hn2) as Hsk.
        rewrite length_skipn. exact Hsk.
Qed.

(* ================================================================= *)
(* EOF continuation: from the post-read state (a0 = 0, pc 0x1126c,    *)
(* sp = rsp-64) run the return path, write the last line, exit 0.     *)
(* ================================================================= *)
Lemma eof_to_out : forall (R : bvmap 5 word) mem cur done,
  reg_get R 1 = (0x111d4 : word) ->
  reg_get R 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ->
  reg_get R 10 = Z_to_bv 64 0 ->
  reg_get R 8 = nat_to_word (length cur) ->
  reg_get R 9 = nat_to_word (length done) ->
  bg_ok mem ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8%nat
    = Some (word_to_le_bytes 8 (0x11040 : word)) ->
  rdn rsegs mem cur_base (length cur) = Some cur ->
  rdn rsegs mem done_base (length done) = Some done ->
  (Z.of_nat (length cur) <= 4096)%Z -> (Z.of_nat (length done) <= 4097)%Z ->
  to_out rsegs (out (cur, done)) (mkst R 0x1126c mem rrom).
Proof.
  intros R mem cur done H1 H2 H10 H8 H9 Hbg Hra Hcur Hdone Hcurcap Hdonecap.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  (* 0x1126c..0x110b4: return through the read wrapper and
     __syscall_ret into main's EOF test.  One block across two [ret]s:
     the reloaded return address is named by the read script. *)
  sym_block (source_segs ++ vt) 9%nat [false; false; true] [ELit 69696]
    [((1 : reg), ELit 70100); ((2 : reg), EVar 32); ((10 : reg), ELit 0)]
    [Z_to_bv 64 (bv_unsigned rsp - 64)] (@nil word) R0 HR0.
  { exists (word_to_le_bytes 8 (0x11040 : word)). split;
      [ exact Hra | vm_compute; reflexivity ]. }
  { pin_lit (0x111d4 : word). exact H1. }
  { exact H2. }
  { exact H10. }
  destruct cur as [|c cur'].
  - (* cur empty: the last line is [done] *)
    destruct done as [|d done'].
    + (* nothing at all: exit 0 with no write.  0x110b4..0x110ec falls
         straight into the epilogue. *)
      change (out ([], [])) with (@nil byte).
      apply tout_exit.
      sym_block (source_segs ++ vt) 3%nat [true; true] (@nil expr)
        [((8 : reg), ELit 0); ((9 : reg), ELit 0)] (@nil word) (@nil word) R1 HR1.
      { sym_regs HR0; exact H8. }
      { sym_regs HR0; exact H9. }
      apply epilogue_exit;
        [ sym_regs HR1; sym_regs HR0; sym_close
        | sym_regs HR1; sym_close | exact Hbg ].
    + (* write [done], then exit 0.  0x110b4..0x11268 is one block across
         the call into musl's write and __syscall_cp_c's shuffles. *)
      change (out ([], d :: done')) with (d :: done').
      sym_block (source_segs ++ vt) 28%nat [true; false] (@nil expr)
        [((2 : reg), EVar 32); ((8 : reg), ELit 0); ((9 : reg), EVar 33)]
        [Z_to_bv 64 (bv_unsigned rsp - 48);
         nat_to_word (length (d :: done'))] (@nil word) R1 HR1.
      { first [ apply source_store_ok; unorm; lia | solve_store_ok_inv ]. }
      { (* beqz s1 falls through: [done] is nonempty *) scbr. }
      { sym_regs HR0; exact H8. }
      { sym_regs HR0; exact H9. }
      eapply tout_step;
        [reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_11268) eq_refl) |].
      apply tout_wr_rec.
      * sym_regs HR1; vm_compute; reflexivity.
      * sym_regs HR1; sym_close.
      * assert (Q11 : reg_get R1 11 = done_base) by (sym_regs HR1; bveq).
        assert (Q12 : reg_get R1 12 = nat_to_word (length (d :: done')))
          by (sym_regs HR1; sym_close).
        rewrite Q11, Q12.
        rewrite (ms_read_bytes_rdn rsegs) by reflexivity.
        cbn [ms_mem]. rewrite word_to_nat_ntw by lenlia.
        rewrite rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes; unorm; lia).
        exact Hdone.
      * (* the line's range passes [access_ok]: a link-time buffer *)
        replace (reg_get R1 11) with done_base by (sym_regs HR1; bveq).
        replace (reg_get R1 12) with (nat_to_word (length (d :: done')))
          by (sym_regs HR1; sym_close).
        apply access_okb_intro.
        rewrite u_ntw by lenlia. rewrite u_done_base. unfold TASK_SIZE. lenlia.
      * (* the line is nonempty *) cbn [length]; lia.
      * (* 0x1126c: the put-style retry loop, per delivered length *)
        intros n Hn1 Hn2. norm_pc.
        eapply (src_put_wall_done (length (d :: done')) (d :: done')
                  done_base n).
        { lia. }
        { exact Hn1. }
        { exact Hn2. }
        { lenlia. }
        { rewrite u_done_base; lia. }
        { rewrite u_done_base; lenlia. }
        { sym_regs HR1; sym_close. }
        { sym_regs HR1; sym_close. }
        { sym_regs HR1; sym_close. }
        { sym_regs HR1; sym_close. }
        { regupd_resolve; apply len_word_firstn_nat; lenlia. }
        { apply bg_ok_scr8; [ exact Hbg | u_norm; lia ]. }
        { apply rdn_wbytes_hit8; u_norm; lia. }
        { rewrite rdn_wbytes_below
            by (rewrite ?length_N_to_le_bytes; unorm; lia).
          exact Hdone. }
  - (* cur nonempty: the last line is [cur] *)
    change (out (c :: cur', done)) with (c :: cur').
    sym_block (source_segs ++ vt) 26%nat [false] (@nil expr)
      [((2 : reg), EVar 32); ((8 : reg), EVar 33)]
      [Z_to_bv 64 (bv_unsigned rsp - 48);
       nat_to_word (length (c :: cur'))] (@nil word) R1 HR1.
    { first [ apply source_store_ok; unorm; lia | solve_store_ok_inv ]. }
    { (* beqz s0 falls through: [cur] is nonempty *) scbr. }
    { sym_regs HR0; exact H8. }
    eapply tout_step;
      [reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_11268) eq_refl) |].
    apply tout_wr_rec.
    + sym_regs HR1; vm_compute; reflexivity.
    + sym_regs HR1; sym_close.
    + assert (Q11 : reg_get R1 11 = cur_base) by (sym_regs HR1; bveq).
      assert (Q12 : reg_get R1 12 = nat_to_word (length (c :: cur')))
        by (sym_regs HR1; sym_close).
      rewrite Q11, Q12.
      rewrite (ms_read_bytes_rdn rsegs) by reflexivity.
      cbn [ms_mem]. rewrite word_to_nat_ntw by lenlia.
      rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; unorm; lia).
      exact Hcur.
    + (* the line's range passes [access_ok]: a link-time buffer *)
      replace (reg_get R1 11) with cur_base by (sym_regs HR1; bveq).
      replace (reg_get R1 12) with (nat_to_word (length (c :: cur')))
        by (sym_regs HR1; sym_close).
      apply access_okb_intro.
      rewrite u_ntw by lenlia. rewrite u_cur_base. unfold TASK_SIZE. lenlia.
    + (* the line is nonempty *) cbn [length]; lia.
    + (* 0x1126c: the put-style retry loop, per delivered length *)
      intros n Hn1 Hn2. norm_pc.
      eapply (src_put_wall_cur (length (c :: cur')) (c :: cur')
                cur_base n).
      { lia. }
      { exact Hn1. }
      { exact Hn2. }
      { lenlia. }
      { rewrite u_cur_base; lia. }
      { rewrite u_cur_base; lenlia. }
      { sym_regs HR1; sym_close. }
      { sym_regs HR1; sym_close. }
      { sym_regs HR1; sym_close. }
      { sym_regs HR1; sym_close. }
      { regupd_resolve; apply len_word_firstn_nat; lenlia. }
      { apply bg_ok_scr8; [ exact Hbg | u_norm; lia ]. }
      { apply rdn_wbytes_hit8; u_norm; lia. }
      { rewrite rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes; unorm; lia).
        exact Hcur. }
Qed.

(* ================================================================= *)
(* Per-block continuation: from the post-read state (a0 = |bs|,       *)
(* pc 0x1126c) fold the block and reach the loop head or exit 3.      *)
(* ================================================================= *)
Lemma post_read_dispatch : forall (R : bvmap 5 word) mem cur done bs,
  reg_get R 1 = (0x111d4 : word) ->
  reg_get R 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ->
  reg_get R 3 = (0x13800 : word) ->
  reg_get R 8 = nat_to_word (length cur) ->
  reg_get R 9 = nat_to_word (length done) ->
  reg_get R 18 = cur_base -> reg_get R 19 = done_base ->
  reg_get R 10 = nat_to_word (length bs) ->
  bg_ok mem ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8%nat
    = Some (word_to_le_bytes 8 (0x11040 : word)) ->
  rdn rsegs mem rb_base (length bs) = Some bs ->
  rdn rsegs mem cur_base (length cur) = Some cur ->
  rdn rsegs mem done_base (length done) = Some done ->
  (Z.of_nat (length cur) <= 4096)%Z -> (Z.of_nat (length done) <= 4097)%Z ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= 1024)%Z ->
  match procs f (cur, done) bs with
  | Some a' => lh_next rsegs src_LH a' (mkst R 0x1126c mem rrom)
  | None => to_exit rsegs ec (mkst R 0x1126c mem rrom)
  end.
Proof.
  intros R mem cur done bs H1 H2 H3 H8 H9 H18 H19 H10 Hbg Hra Hrb Hcur Hdone
         Hcurcap Hdonecap Hblo Hbhi.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  (* 0x1126c..0x11058: return through the read wrapper and
     __syscall_ret, take main's two non-EOF tests and set the byte loop
     up.  One block; the byte loop is entered at 0x11058. *)
  sym_block_ex (source_segs ++ vt) (mkst R (Z_to_bv 64 70252) mem rrom)
    13%nat [false; false; false] [ELit 69696]
    [((1 : reg), ELit 70100); ((2 : reg), EVar 32); ((3 : reg), ELit 79872);
     ((10 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp - 64); nat_to_word (length bs)]
    (@nil word) RG HRG Hms.
  { (* beqz a0 falls through: the block is nonempty *) scbr. }
  { (* bltz a0 falls through: the count is non-negative *) scbr. }
  { (* bltu a0,-4096 falls through: not an error return *) sysret_ok. }
  { exists (word_to_le_bytes 8 (0x11040 : word)). split;
      [ exact Hra | vm_compute; reflexivity ]. }
  { pin_lit (0x111d4 : word). exact H1. }
  { exact H2. }
  { pin_lit (0x13800 : word). exact H3. }
  { exact H10. }
  replace (Z_to_bv 64 70252) with (0x1126c : word) in Hms by bveq.
  replace (Z_to_bv 64 69720) with (0x11058 : word) in Hms by bveq.
  assert (HBLH : BLH cur done bs 0 (mkst RG 0x11058 mem rrom)).
  { unfold BLH. do 2 eexists. split; [reflexivity|].
    repeat split; try assumption; try lia;
      try (sym_regs HRG; first [ assumption | sym_close ]). }
  pose proof (byte_loop (length bs) cur done bs 0 (mkst RG 0x11058 mem rrom)
                ltac:(lia) HBLH) as Hbl.
  rewrite skipn_O in Hbl.
  revert Hbl.
  destruct (procs f (cur, done) bs) as [a'|].
  - intros (msL & HmsL & HL).
    exists msL. split; [ eapply msteps_trans; [exact Hms | exact HmsL] | exact HL ].
  - intro Hbl. eapply msteps_to_exit; [exact Hms | exact Hbl].
Qed.

(* ================================================================= *)
(* One loop iteration: the DrainSim per-binary obligation.            *)
(* ================================================================= *)
Lemma src_LH_to_rd : forall a ms,
  src_LH a ms -> to_rd rsegs (Z_to_bv 64 1024) f out ec src_LH a ms.
Proof.
  intros a ms HLH.
  destruct a as [cur done].
  destruct HLH as (regs & mem & -> & H2 & H3 & H8 & H9 & H18 & H19
                   & Hbg & Hcur & Hdone & Hcurcap & Hdonecap).
  cbn [fst snd] in *.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  (* 0x11030..0x11268: main's read call, musl's read wrapper and
     __syscall_cp_c's argument shuffles — one block up to the ecall. *)
  sym_block (source_segs ++ vt) 23%nat (@nil bool) (@nil expr)
    [((2 : reg), EVar 32); ((3 : reg), ELit 79872)]
    [Z_to_bv 64 (bv_unsigned rsp - 48)] (@nil word) RG HRG.
  { first [ apply source_store_ok; unorm; lia | solve_store_ok_inv ]. }
  { exact H2. }
  { pin_lit (0x13800 : word). exact H3. }
  eapply trd_step;
    [reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_11268) eq_refl) |].
  apply trd_here_rec with (buf := rb_base).
  - sym_regs HRG; vm_compute; reflexivity.
  - sym_regs HRG; first [ reflexivity | sym_close ].
  - sym_regs HRG; first [ reflexivity | sym_close ].
  - sym_regs HRG; first [ reflexivity | sym_close ].
  - apply source_rb_wseg.
  - (* the buffer is a link-time constant far under [State.TASK_SIZE], so the range passes [access_ok] *)
    apply access_okb_intro. rewrite u_rb_base.
    change (bv_unsigned (Z_to_bv 64 1024)) with 1024%Z.
    unfold TASK_SIZE. lia.
  - (* EOF continuation *)
    norm_pc.
    apply eof_to_out;
      [ sym_regs HRG; sym_close
      | sym_regs HRG; sym_close
      | sym_regs HRG; sym_close
      | sym_regs HRG; exact H8
      | sym_regs HRG; exact H9
      | apply bg_ok_scr8; [ exact Hbg | u_norm; lia ]
      | apply rdn_wbytes_hit8; u_norm; lia
      | rewrite rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes; unorm; lia);
        exact Hcur
      | rewrite rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes; unorm; lia);
        exact Hdone
      | exact Hcurcap
      | exact Hdonecap ].
  - (* the emitted line fits one modeled write *)
    apply out_modeled; [exact Hcurcap | exact Hdonecap].
  - (* per-block continuation *)
    intros bs Hblo Hbhi.
    wlits.
    apply post_read_dispatch;
      try assumption;
      try (sym_regs HRG;
           first [ reflexivity | assumption | apply len_word_nat | sym_close ]).
    + apply bg_ok_wtm_below;
        [ apply bg_ok_scr8; [ exact Hbg | u_norm; lia ]
        | unorm; lia ].
    + rewrite rdn_wtm_out
        by (rewrite ?length_N_to_le_bytes; unorm;
            first [ lia | left; lia | right; lia ]).
      apply rdn_wbytes_hit8; u_norm; lia.
    + apply rdn_write_to_mem. unorm. lia.
    + rewrite rdn_wtm_out
        by (rewrite ?length_N_to_le_bytes; unorm;
            first [ lia | left; lia | right; lia ]).
      rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; unorm; lia).
      exact Hcur.
    + rewrite rdn_wtm_out
        by (rewrite ?length_N_to_le_bytes; unorm;
            first [ lia | left; lia | right; lia ]).
      rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; unorm; lia).
      exact Hdone.
Qed.

(* ================================================================= *)
(* From the initial state to the loop head                            *)
(* ================================================================= *)
Lemma src_init_to_rd :
  to_rd rsegs (Z_to_bv 64 1024) f out ec src_LH a0
    (init_machine_state rsegs 0x11154 source_phdrs rsp rmb rrnd inp).
Proof.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargc.
  assert (Hargc_rd : rdn rsegs wmem rsp 8%nat = Some (word_le8 argcN)).
  { unfold wmem.
    rewrite rdn_wrap_stack_above by lia.
    apply read_argc. apply source_bsb_nw. }
  rewrite init_mkst. norm_pc.
  (* 0x11154..0x11030: _start reads argc, stores [environ], calls main,
     and main's prologue saves ra/s0..s3 and sets the buffers up.  One
     block; its exit memory IS [src_bg], modulo the [environ] value. *)
  sym_block (source_segs ++ vt) 23%nat (@nil bool) [EVar 33]
    [((2 : reg), EVar 32); ((8 : reg), ELit 0); ((9 : reg), ELit 0);
     ((18 : reg), ELit 0); ((19 : reg), ELit 0)]
    [rsp] [argcN] RG HRG.
  1-5: solve_store_ok_inv.
  { apply source_store_ok; unorm; lia. }
  { rewrite u0_id. exists (word_le8 argcN). split;
      [ exact Hargc_rd | exact (bytes_le_n_to_le_8 _) ]. }
  rewrite envp_ptr_eq.
  apply src_LH_to_rd.
  unfold src_LH, a0. do 2 eexists. split; [reflexivity|].
  cbn [fst snd length].
  repeat split;
    try (sym_regs HRG; first [ reflexivity | sym_close ]);
    try (exact bg_ok_bg);
    try reflexivity;
    try lia.
Qed.

End SourceProof.
