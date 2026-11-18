(** * cat1024-ns, source binary (musl-gcc -Os, read/write wrappers).

    PROOF-SIDE FILE (not part of the trusted specification).

    The source loops at 0x11010: main calls musl's read() wrapper
    (arg-shuffle, __syscall_cp, __syscall_ret), tests the return, and on
    bytes calls the write() wrapper with the full count (which the model
    always completes), then loops.  EOF returns 0 through main's
    epilogue into _start's exit(93) tail.

    The loop-head invariant [src_LH] pins sp (= initial sp - 32, main's
    frame), gp, s0 = the buffer address, and a [mem_ok] memory:
    agreement with the post-prologue memory [fmem] outside the scratch
    window [rsp-40, rsp-16) — the wrappers' saved-ra slot at rsp-40
    together with main's two put-loop spill slots at rsp-32 (pointer)
    and rsp-24 (count) — and the 1024-byte buffer window.

    Sp-relative addresses/register values are in the canonical
    [Z_to_bv 64 (bv_unsigned rsp - k)] form, pc and rodata constants
    in numeral-literal form, block lengths as [len_word bs]; all range
    bookkeeping is in [Z] over [bv_unsigned].

    The run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  The section takes the pair as a variable [vt] and every
    derivation steps over [source_segs ++ vt]; [Proof.v] instantiates it.
    The stack bounds come from the entry predicate's launch conjunct
    [Run.entry_launch_ok_va] and [Run.valid_launch]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamExec WallSim StreamSim StoreOk Footprint SymExec SymTac RunSegmentsLift.
(** NOT imported, deliberately: [Common/MuslCall.v]'s summary of the musl
    [write] blob, instantiated for this binary at 0x11104 in
    [cat1024_ns_hoare.v].  Both routes over that blob were proved; this
    file takes the reflective one.  The summary and the executor are
    ALTERNATIVES for a blob like this, and which one wins depends on
    whether the caller can name the values the blob reloads: here the
    read script ([ELit 0x11020] for the wrapper's saved [ra]) resolves
    every [ret] in the blob, so the executor runs straight through all
    26 instructions and the summary would only add its ten premises.
    [modprint_ns_source.v] is the other case, and shows the two
    composing: there the summary covers the blob and [sym_block] the
    straight lines on both sides of it. *)
From LinuxProcessSemantics.Examples.cat1024_ns Require Import cat1024_ns_code cat1024_ns_defs.
From LinuxProcessSemantics.Examples.cat1024_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.cat1024_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them. *)
#[local] Instance cat1024_ns_source_fx : FPState := fx0.

(** The source buffer (bss) and musl's environ slot. *)
Definition src_buf : word := 0x13008.

Lemma u_src_buf : bv_unsigned src_buf = 0x13008%Z.
Proof. reflexivity. Qed.

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
  wrap_mem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x11078)) rsp rrnd.
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
  v_addi (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli argcN 3)) 8 = envp_ptr.
Proof.
  pose proof rsp_hi_num. pose proof rsp_lo_num.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hlen.
  apply bv_eq. unfold envp_ptr, v_addi.
  rewrite !Z_to_bv_unsigned.
  rewrite v_add_small
    by (rewrite u_Z2bv by lia; rewrite v_slli_3 by (rewrite u_argcN; lia);
        rewrite u_argcN; lia).
  rewrite u_Z2bv by lia.
  rewrite v_slli_3 by (rewrite u_argcN; lia).
  rewrite u_argcN.
  f_equal; lia.
Qed.

(** Memory after _start's environ store and main()'s prologue: the
    environ slot, then main's two callee-save slots below the initial
    sp, in execution order.  All stored values are constants of the
    initial state (s0 = 0, main's ra = 0x110a4).  gcc 15 keeps only
    s0 (and ra) live across the calls, so the prologue saves two
    registers where gcc 9 saved four; the put loop's pointer/count now
    live in stack spill slots instead of s1/s2. *)
Definition fmem : word -> option byte :=
  wbytes (wbytes (wbytes wmem
    0x13000 (word_to_le_bytes 8 envp_ptr))                                     (* sd a2,0(t1)  [environ] *)
    (Z_to_bv 64 (bv_unsigned rsp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))   (* sd s0,16(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 8))  (word_to_le_bytes 8 (0x110a4 : word)). (* sd ra,24(sp) *)

(** Memories that agree with [fmem] outside the scratch window
    [rsp-40, rsp-16) and the buffer window [0x13008, 0x13408).
    (New no-overflow hypothesis, mirroring [rdn_ext].) *)
Definition mem_agree (mem : word -> option byte) : Prop :=
  forall (a : word) (n : nat),
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    ((bv_unsigned rsp - 16 <= bv_unsigned a)%Z \/
     ((bv_unsigned a + Z.of_nat n <= bv_unsigned rsp - 40)%Z /\
      ((0x13408 <= bv_unsigned a)%Z \/
       (bv_unsigned a + Z.of_nat n <= 0x13008)%Z))) ->
    rdn rsegs mem a n = rdn rsegs fmem a n.

(** …and are still writable wherever the initial overlay was.  The
    stack stores in the loop body target [rsp-40, rsp-16), inside the
    RLIMIT_STACK window [wmem] zero-maps; [mem] is existentially
    quantified in [src_LH], so the [store_ok] bound has to travel with
    it.  [mem_grows] is the weakest thing that does: the overlay only
    ever gains addresses. *)
Definition mem_ok (mem : word -> option byte) : Prop :=
  mem_grows wmem mem /\ mem_agree mem.

(** The writability projection, registered so the shared store-bound
    dispatcher can find it under the existential [mem] of [src_LH]. *)
Lemma mem_ok_grows : forall mem, mem_ok mem -> mem_grows wmem mem.
Proof. intros mem [H _]. exact H. Qed.

Local Hint Resolve mem_ok_grows : store_ok_db.

Lemma fmem_ok : mem_ok fmem.
Proof. split; [unfold fmem; solve_mem_grows | intros a n _ _; reflexivity]. Qed.

(** An 8-byte store inside the scratch window preserves [mem_ok]. *)
Lemma mem_ok_scratch8 : forall mem (a : word) v,
  mem_ok mem ->
  (bv_unsigned rsp - 40 <= bv_unsigned a)%Z ->
  (bv_unsigned a + 8 <= bv_unsigned rsp - 16)%Z ->
  mem_ok (wbytes mem a (word_to_le_bytes 8 v)).
Proof.
  intros mem a v [Hg Hm] Hlo Hhi. split; [solve_mem_grows|].
  intros a' n Hnw Hd.
  pose proof rsp_hi_num.
  destruct Hd as [Hd | [Hd1 Hd2]].
  - rewrite rdn_wbytes_disjoint by (rewrite ?length_N_to_le_bytes; lia).
    apply Hm; [exact Hnw | left; exact Hd].
  - rewrite rdn_wbytes_below by (rewrite ?length_N_to_le_bytes; lia).
    apply Hm; [exact Hnw | right; split; assumption].
Qed.

(** A block delivered into the buffer preserves [mem_ok]. *)
Lemma mem_ok_buf : forall mem bs,
  mem_ok mem -> (Z.of_nat (length bs) <= 1024)%Z ->
  mem_ok (write_to_mem mem src_buf bs).
Proof.
  intros mem bs [Hg Hm] Hlen. split; [solve_mem_grows|].
  intros a n Hnw Hd. pose proof rsp_lo_num.
  destruct Hd as [Hd | [Hd1 Hd2]].
  - rewrite rdn_wtm_out
      by (rewrite ?u_src_buf; first [ lia | left; lia ]).
    apply Hm; [exact Hnw | left; exact Hd].
  - rewrite rdn_wtm_out
      by (rewrite ?u_src_buf;
          first [ lia
                | destruct Hd2 as [H2|H2]; [left; lia | right; lia] ]).
    apply Hm; [exact Hnw | right; split; assumption].
Qed.

(* ================================================================= *)
(* Frame-slot reads through a [mem_ok] memory                        *)
(* ================================================================= *)

Lemma read_ra_slot_m : forall mem, mem_ok mem ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
  = Some (word_to_le_bytes 8 (0x110a4 : word)).
Proof.
  intros mem [Hg Hm]. pose proof rsp_lo_num. pose proof rsp_hi_num.
  rewrite Hm by (u_norm; first [ lia | left; lia ]). unfold fmem.
  apply rdn_wbytes_hit8; u_norm; lia.
Qed.

Lemma read_s0_slot_m : forall mem, mem_ok mem ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 16)) 8%nat
  = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros mem [Hg Hm]. pose proof rsp_lo_num. pose proof rsp_hi_num.
  rewrite Hm by (u_norm; first [ lia | left; lia ]). unfold fmem.
  rewrite rdn_wbytes_below by (rewrite ?length_N_to_le_bytes; u_norm; lia).
  apply rdn_wbytes_hit8; u_norm; lia.
Qed.

(* ================================================================= *)
(* The loop-head invariant                                           *)
(* ================================================================= *)

Definition src_LH (ms : machine_state) : Prop :=
  exists regs mem,
    ms = mkst regs 0x11010 mem rrom /\
    reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 32) /\
    reg_get regs 3 = (0x13800 : word) /\
    reg_get regs 8 = src_buf /\
    mem_ok mem.

(* ================================================================= *)
(* Local step tactics                                                *)
(* ================================================================= *)

(** A jalr x0 (ret) to a concrete target. *)
Local Ltac sret F D tt0 :=
  stepjr F D tt0 ltac:(getr_resolve; bveq).

(** Normalize a computed address/value equation ([v_addi]-headed LHS)
    against its canonical form. *)
(** The [rewrite]-with-hypotheses pass lets the same tactic work past a
    summary or a [sym_block], where the register file is an opaque
    variable and its live values are only known through hypotheses. *)
Local Ltac addr_tac :=
  getr_resolve; regupd_resolve;
  repeat match goal with
  | H : reg_get ?R ?r = _ |- context [reg_get ?R ?r] => rewrite H
  end;
  sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].

(** A store-double with pre-normalized address and value. *)
Local Ltac ssd F D aexp vexp vtac :=
  step_intro;
  [ reflexivity
  | eapply step_sd_at with (a := aexp) (v := vexp);
    [ exact F | reflexivity | exact D
    | addr_tac
    | vtac
    | first [ apply source_store_ok; imm_norm; u_norm; lia
            | solve_store_ok_inv ] ]
  | step_simpl ].

(** A load-double of a known 8-byte slot. *)
Local Ltac sld F D aexp vexp readtac :=
  step_intro;
  [ reflexivity
  | eapply step_ld with (bs := word_to_le_bytes 8 vexp) (v := vexp);
    [ exact F | reflexivity | exact D
    | match goal with |- rdn _ _ ?ad _ = _ =>
        replace ad with aexp by addr_tac
      end; readtac
    | exact (bytes_le_to_Z_8 _) ]
  | step_simpl ].

(** The [bltu a5,a0] fall-through in __syscall_ret on a delivered block
    (a5 = -4096 as unsigned, a0 = the block length). *)
Local Ltac bltu_ret_ft F D Hbhi :=
  step_intro;
  [ reflexivity
  | eapply step_bltu_ft;
    [ exact F | reflexivity | exact D
    | getr_resolve;
      rewrite c_ltu_ltb; apply Z.ltb_ge;
      match goal with |- context [bv_unsigned (v_lui ?z)] =>
        replace (bv_unsigned (v_lui z)) with 18446744073709547520%Z
          by (vm_compute; reflexivity)
      end;
      rewrite u_len_word by lia; lia ]
  | norm_pc ].

(** The three registers [src_LH] pins, as symbolic-executor entry
    facts: [sp] is the frame base (a value, carried at index 32), [gp]
    and [s0] are absolute literals. *)
Definition src_pins : list (reg * expr) :=
  [((2 : reg), EVar 32); ((3 : reg), ELit 0x13800); ((8 : reg), ELit 0x13008)].

(* ================================================================= *)
(* The put-loop retry recursion                                      *)
(* ================================================================= *)

(** After a (possibly short) write delivery of [n] bytes the machine
    sits at 0x11190 (the wrapper's post-ecall [ret]) with
    a0 = [len_word (firstn n bs)].  The run pops the wrapper frame,
    passes [__syscall_ret], reloads the pointer/count spills, updates
    them, and either falls back to the read-loop head (full delivery,
    [bnez] not taken) or reissues the write on the remainder through
    the put-loop head 0x11030 — a [WallSim.to_wall_tail] of
    [skipn n bs] down to [lh_next].  Induction on
    [fuel >= length bs]; the remainder strictly shrinks because every
    delivery is nonempty.

    The state is characterized abstractly: registers by the facts the
    path consumes (ra = 0x1112c inside the wrapper, sp = rsp-48, gp/s0
    for the loop head, a0 = the delivered length), memory by [mem_ok]
    plus the three scratch-slot contents (wrapper ra spill = 0x11040,
    pointer spill = [p], count spill = [len_word bs]) and the
    readability of the remaining bytes at [p]. *)
Lemma src_put_wall : forall fuel (bs : list byte) (p : word) n regs mem,
  (length bs <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length bs)%nat ->
  (Z.of_nat (length bs) <= 1024)%Z ->
  (0x13008 <= bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length bs) <= 0x13408)%Z ->
  reg_get regs 10 = len_word (firstn n bs) ->
  reg_get regs 1 = (0x1112c : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 3 = (0x13800 : word) ->
  reg_get regs 8 = src_buf ->
  mem_ok mem ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 40)) 8%nat
    = Some (word_to_le_bytes 8 (0x11040 : word)) ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 32)) 8%nat
    = Some (word_to_le_bytes 8 p) ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 24)) 8%nat
    = Some (word_to_le_bytes 8 (len_word bs)) ->
  rdn rsegs mem p (length bs) = Some bs ->
  to_wall_tail rsegs (Z_to_bv 64 1)
    (mkst regs (0x11190 : word) mem rrom)
    (skipn n bs) (lh_next rsegs src_LH).
Proof.
  induction fuel as [|fuel IH];
    intros bs p n regs mem Hfuel Hn1 Hn2 Hlen Hplo Hphi
           H10 H1 H2 H3 H8 Hmok Hra Hptr Hcnt Hread.
  { lia. }
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  (* 0x11190: __syscall_cp_c's ret, back into the write wrapper *)
  stepjr (SFv SF_11190) SD_11190 (0x1112c : word) ltac:(getr_resolve; exact H1).
  (* 0x1112c: ld ra,8(sp) — the wrapper's saved ra (0x11040) *)
  sld (SFv SF_1112c) SD_1112c (Z_to_bv 64 (bv_unsigned rsp - 40)) (0x11040 : word)
    ltac:(exact Hra).
  (* 0x11130: addi sp,sp,16 — pop the wrapper frame *)
  stepiv (SFv SF_11130) SD_11130 (Z_to_bv 64 (bv_unsigned rsp - 32))
    ltac:(getr_resolve; rewrite H2; sp_norm; f_equal; lia).
  (* 0x11134: j __syscall_ret *)
  stepj (SFv SF_11134) SD_11134.
  (* 0x11138: lui a5,0xfffff *)
  stepi (SFv SF_11138) SD_11138.
  (* 0x1113c: bltu a5,a0 falls through (the delivery is no error) *)
  step_intro;
    [ reflexivity
    | eapply step_bltu_ft;
      [ exact (SFv SF_1113c) | reflexivity | exact SD_1113c
      | getr_resolve; rewrite H10;
        rewrite c_ltu_ltb; apply Z.ltb_ge;
        match goal with |- context [bv_unsigned (v_lui ?z)] =>
          replace (bv_unsigned (v_lui z)) with 18446744073709547520%Z
            by (vm_compute; reflexivity)
        end;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x11140: ret — back into main's put loop at 0x11040 *)
  stepjr (SFv SF_11140) SD_11140 (0x11040 : word) ltac:(getr_resolve; reflexivity).
  (* 0x11040: blez a0 falls through (the delivery is nonempty) *)
  step_intro;
    [ reflexivity
    | eapply step_bge_ft;
      [ exact (SFv SF_11040) | reflexivity | exact SD_11040
      | getr_resolve; rewrite H10; apply c_lts_0_pos;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x11044: ld a2,8(sp) — the count spill *)
  sld (SFv SF_11044) SD_11044 (Z_to_bv 64 (bv_unsigned rsp - 24)) (len_word bs)
    ltac:(exact Hcnt).
  (* 0x11048: ld a1,0(sp) — the pointer spill *)
  sld (SFv SF_11048) SD_11048 (Z_to_bv 64 (bv_unsigned rsp - 32)) p
    ltac:(exact Hptr).
  (* 0x1104c: sub a2,a2,a0 — the count decrement *)
  stepiv (SFv SF_1104c) SD_1104c (len_word (skipn n bs))
    ltac:(getr_resolve; rewrite H10; apply v_sub_len_firstn; lia).
  (* 0x11050: add a1,a1,a0 — the pointer bump *)
  stepiv (SFv SF_11050) SD_11050 (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
    ltac:(getr_resolve; rewrite H10; apply v_add_len_firstn_Z; lia).
  destruct (Nat.eq_dec n (length bs)) as [-> | Hne].
  - (* full delivery: bnez not taken, j back to the read-loop head *)
    rewrite skipn_all.
    step_intro;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact (SFv SF_11054) | reflexivity | exact SD_11054
        | getr_resolve; apply c_eq_0_of_u; reflexivity ]
      | norm_pc ].
    (* 0x11058: j 0x11010 *)
    stepj (SFv SF_11058) SD_11058.
    apply twt_done.
    unfold lh_next. eexists. split; [apply mst_refl|].
    unfold src_LH. do 2 eexists. split; [reflexivity|].
    split; [regupd_resolve; reflexivity|].
    split; [regupd_resolve; exact H3|].
    split; [regupd_resolve; exact H8|].
    exact Hmok.
  - (* short delivery: bnez taken, reissue on the remainder *)
    step_intro;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact (SFv SF_11054) | reflexivity | exact SD_11054
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* 0x11030: li a0,1 *)
    stepiv (SFv SF_11030) SD_11030 (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* 0x11034: sd a2,8(sp) — respill the count *)
    ssd (SFv SF_11034) SD_11034 (Z_to_bv 64 (bv_unsigned rsp - 24))
      (len_word (skipn n bs))
      ltac:(getr_resolve; reflexivity).
    (* 0x11038: sd a1,0(sp) — respill the pointer *)
    ssd (SFv SF_11038) SD_11038 (Z_to_bv 64 (bv_unsigned rsp - 32))
      (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
      ltac:(getr_resolve; reflexivity).
    (* 0x1103c: jal write() *)
    stepj (SFv SF_1103c) SD_1103c.
    (* the wrapper: frame, arg shuffle, ra spill, __syscall_cp *)
    stepiv (SFv SF_11104) SD_11104 (Z_to_bv 64 (bv_unsigned rsp - 48))
      ltac:(getr_resolve; sp_norm; f_equal; lia).
    stepiv (SFv SF_11108) SD_11108 (len_word (skipn n bs))
      ltac:(getr_resolve; apply v_addi_0).
    stepi (SFv SF_1110c) SD_1110c.
    stepiv (SFv SF_11110) SD_11110 (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
      ltac:(getr_resolve; apply v_addi_0).
    stepi (SFv SF_11114) SD_11114.
    stepiv (SFv SF_11118) SD_11118 (Z_to_bv 64 1)
      ltac:(getr_resolve; apply v_addi_0).
    stepi (SFv SF_1111c) SD_1111c.
    stepiv (SFv SF_11120) SD_11120 (Z_to_bv 64 64) ltac:(getr_resolve; bveq).
    ssd (SFv SF_11124) SD_11124 (Z_to_bv 64 (bv_unsigned rsp - 40)) (0x11040 : word)
      ltac:(getr_resolve; bveq).
    stepj (SFv SF_11128) SD_11128.
    (* 0x11194: __syscall_cp's trampoline into __syscall_cp_c *)
    stepj (SFv SF_11194) SD_11194.
    (* __syscall_cp_c's seven shuffles *)
    stepiv (SFv SF_11170) SD_11170 (Z_to_bv 64 64) ltac:(getr_resolve; apply v_addi_0).
    stepiv (SFv SF_11174) SD_11174 (Z_to_bv 64 1) ltac:(getr_resolve; apply v_addi_0).
    stepiv (SFv SF_11178) SD_11178 (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
      ltac:(getr_resolve; apply v_addi_0).
    stepiv (SFv SF_1117c) SD_1117c (len_word (skipn n bs))
      ltac:(getr_resolve; apply v_addi_0).
    stepi (SFv SF_11180) SD_11180.
    stepi (SFv SF_11184) SD_11184.
    stepi (SFv SF_11188) SD_11188.
    (* ecall: the reissued write *)
    eapply twt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_1118c) eq_refl) |].
    apply twt_more; [rewrite length_skipn; lia|].
    apply (twl_write_rec rsegs (Z_to_bv 64 1)).
    + getr_resolve; reflexivity.
    + regupd_resolve; reflexivity.
    + (* the remainder read back at the bumped pointer *)
      match goal with
      | |- ms_read_bytes _ (reg_get ?R 11) (reg_get ?R 12) = Some _ =>
          replace (reg_get R 11)
            with (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
            by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word (skipn n bs))
            by (regupd_resolve; reflexivity)
      end.
      rewrite (ms_read_bytes_rdn rsegs) by reflexivity.
      cbn [ms_mem].
      replace (word_to_nat (len_word (skipn n bs)))
        with (length (skipn n bs))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      rewrite !rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes, ?length_skipn; u_norm; lia).
      pose proof (rdn_skipn rsegs mem (length bs) p bs n Hread Hn2)
        as Hsk.
      rewrite word_add_nat_Z in Hsk by lia.
      rewrite length_skipn. exact Hsk.
    + (* the remainder's range passes [access_ok]: inside the buffer *)
      match goal with
      | |- access_okb (reg_get ?R 11) (bv_unsigned (reg_get ?R 12)) = true =>
          replace (reg_get R 11)
            with (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
            by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word (skipn n bs))
            by (regupd_resolve; reflexivity)
      end.
      apply access_okb_intro.
      rewrite u_len_word by (rewrite length_skipn; lia).
      rewrite length_skipn. u_norm. unfold TASK_SIZE. lia.
    + rewrite length_skipn; lia.
    + (* the (shorter) remainder, by induction *)
      intros m Hm1 Hm2.
      norm_pc.
      apply (IH (skipn n bs) (Z_to_bv 64 (bv_unsigned p + Z.of_nat n)) m).
      * rewrite length_skipn; lia.
      * exact Hm1.
      * exact Hm2.
      * rewrite length_skipn; lia.
      * u_norm; lia.
      * u_norm; rewrite length_skipn; lia.
      * regupd_resolve; reflexivity.
      * regupd_resolve; bveq.
      * regupd_resolve; reflexivity.
      * regupd_resolve; exact H3.
      * regupd_resolve; exact H8.
      * repeat first
          [ assumption
          | apply mem_ok_scratch8; [ | u_norm; lia | u_norm; lia ] ].
      * apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite !rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite !rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes, ?length_skipn; u_norm; lia).
        pose proof (rdn_skipn rsegs mem (length bs) p bs n Hread Hn2)
          as Hsk.
        rewrite word_add_nat_Z in Hsk by lia.
        rewrite length_skipn. exact Hsk.
Qed.

(* ================================================================= *)
(* One loop iteration                                                *)
(* ================================================================= *)

Lemma src_LH_to_rd : forall ms,
  src_LH ms -> to_rd rsegs src_LH (Z_to_bv 64 1024) ms.
Proof.
  intros ms (regs & mem & -> & H2 & H3 & H8 & Hmok).
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  (* 0x11010 .. 0x1118c — 22 instructions in ONE reflective block:
     main's three read() arguments, the [jal] into the wrapper, its
     frame and eight-register shuffle, the [sd ra,8(sp)] spill at
     rsp-40, __syscall_cp's [j] and seven more shuffles.  The executor
     stops of its own accord at the [ecall].  Two side conditions (the
     spill's address arithmetic and its writability) and three pins
     (the invariant's sp/gp/s0). *)
  sym_block (source_segs ++ vt) 40%nat (@nil bool) (@nil expr) src_pins
    [Z_to_bv 64 (bv_unsigned rsp - 32)] (@nil word) R1 HR1.
  { sym_addr_norm;
    first [ apply source_store_ok; imm_norm; u_norm; lia | solve_store_ok_inv ]. }
  { rewrite getr_nz by reg_neq_tac; exact H2. }
  { rewrite getr_nz by reg_neq_tac; rewrite H3; bveq. }
  { rewrite getr_nz by reg_neq_tac; rewrite H8; bveq. }
  (* ecall: the pending read *)
  eapply trd_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_1118c) eq_refl) |].
  apply trd_here_rec with (buf := src_buf).
  - sym_regs HR1; sym_close.
  - sym_regs HR1; sym_close.
  - sym_regs HR1; sym_close.
  - sym_regs HR1; sym_close.
  - apply source_buf_wseg.
  - (* the buffer is a link-time constant far under [State.TASK_SIZE], so the range passes [access_ok] *)
    apply access_okb_intro. rewrite u_src_buf.
    change (bv_unsigned (Z_to_bv 64 1024)) with 1024%Z.
    unfold TASK_SIZE. lia.
  - (* ================= EOF continuation: exit 0 =================
       0x11190 .. 0x110a8 — 14 instructions in ONE reflective block:
       __syscall_cp_c's [ret], the read wrapper's reload/pop, the [j]
       into __syscall_ret, its [bltu] fall-through and [ret], main's
       taken [beqz], main's two epilogue reloads, [addi sp,sp,32],
       [ret] into _start, and the exit(93) load.  Three of the four
       [ret]s only resolve because the READ SCRIPT names the return
       addresses the reloads produce. *)
    norm_pc.
    sym_block (source_segs ++ vt) 20%nat [false; true]
      [ELit 0x11020; ELit 0x110a4; ELit 0]
      [((1 : reg), ELit 0x110f8); ((2 : reg), EVar 32); ((10 : reg), ELit 0)]
      [Z_to_bv 64 (bv_unsigned rsp - 48)] (@nil word) R2 HR2.
    (* what is LEFT of the eight side conditions: the three reloads.
       The two branch decisions have literal operands and the three
       [SCFlat]s follow from the [sp] window, so [sym_block] closed
       them; so did all four pins, out of the previous block's exit
       register file. *)
    { exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
        [ rewrite !rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; u_norm; lia);
          apply read_s0_slot_m; assumption
        | exact (bytes_le_to_Z_8 _) ]. }
    { exists (word_to_le_bytes 8 (0x110a4 : word)); split;
        [ rewrite !rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; u_norm; lia);
          apply read_ra_slot_m; assumption
        | exact (bytes_le_to_Z_8 _) ]. }
    { exists (word_to_le_bytes 8 (0x11020 : word)); split;
        [ apply rdn_wbytes_hit8; u_norm; lia
        | exact (bytes_le_to_Z_8 _) ]. }
    eapply te_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_110a8) eq_refl) |].
    apply te_here_rec0.
    + sym_regs HR2; sym_close.
    + sym_regs HR2; sym_close.
  - (* ================= bytes continuation: echo write ================= *)
    intros bs Hblo Hbhi.
    norm_pc.
    (* 0x11190 .. 0x1118c — 33 instructions in ONE reflective block: the
       read wrapper's return path, __syscall_ret's [bltu]/[ret], main's
       two fall-through branches, the put-loop head's two spills, the
       [jal] into write(), its frame, eight-register shuffle and ra
       spill, and __syscall_cp's [j] plus seven more shuffles.  Three
       stores land in the symbolic log; the executor stops at the write
       [ecall]. *)
    sym_block (source_segs ++ vt) 40%nat [false; false; false] [ELit 0x11020]
      [((1 : reg), ELit 0x110f8); ((2 : reg), EVar 32);
       ((8 : reg), ELit 0x13008); ((10 : reg), EVar 33)]
      [Z_to_bv 64 (bv_unsigned rsp - 48); len_word bs] (@nil word) R2 HR2.
    (* what is left of the eleven side conditions: the three spills'
       writability, the three branch decisions (whose operands are the
       symbolic block length), and the wrapper's ra reload. *)
    { first [ apply source_store_ok; imm_norm; u_norm; lia
            | solve_store_ok_inv ]. }
    { first [ apply source_store_ok; imm_norm; u_norm; lia
            | solve_store_ok_inv ]. }
    { first [ apply source_store_ok; imm_norm; u_norm; lia
            | solve_store_ok_inv ]. }
    { apply c_lts_pos_0; rewrite u_len_word by lia; lia. }
    { apply c_eq_0_false; rewrite u_len_word by lia; lia. }
    { rewrite c_ltu_ltb; apply Z.ltb_ge;
      match goal with |- context [bv_unsigned ?z] =>
        lazymatch z with
        | Z_to_bv 64 (-4096) =>
            replace (bv_unsigned z) with 18446744073709547520%Z
              by (vm_compute; reflexivity)
        end
      end;
      rewrite u_len_word by lia; lia. }
    { exists (word_to_le_bytes 8 (0x11020 : word)); split;
        [ rewrite rdn_wtm_out
            by (rewrite ?u_src_buf; u_norm; first [ lia | left; lia ]);
          apply rdn_wbytes_hit8; u_norm; lia
        | exact (bytes_le_to_Z_8 _) ]. }
    (* ecall: the pending write *)
    eapply twr_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_1118c) eq_refl) |].
    apply twr_here_rec.
    + sym_regs HR2; sym_close.
    + sym_regs HR2; sym_close.
    + (* the buffer bytes read back *)
      match goal with
      | |- ms_read_bytes _ (reg_get ?R 11) (reg_get ?R 12) = Some bs =>
          replace (reg_get R 11) with src_buf by (sym_regs HR2; sym_close);
          replace (reg_get R 12) with (len_word bs) by (sym_regs HR2; sym_close)
      end.
      rewrite (ms_read_bytes_rdn rsegs) by reflexivity.
      cbn [ms_mem].
      replace (word_to_nat (len_word bs)) with (length bs)
        by (unfold word_to_nat; rewrite u_len_word by lia;
            rewrite Nat2Z.id; reflexivity).
      rewrite !rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes, ?u_src_buf; u_norm; lia).
      apply rdn_write_to_mem. rewrite u_src_buf. lia.
    + (* the buffer range passes [access_ok]: a link-time address *)
      match goal with
      | |- access_okb (reg_get ?R 11) (bv_unsigned (reg_get ?R 12)) = true =>
          replace (reg_get R 11) with src_buf by (sym_regs HR2; sym_close);
          replace (reg_get R 12) with (len_word bs) by (sym_regs HR2; sym_close)
      end.
      apply access_okb_intro. rewrite u_src_buf.
      rewrite u_len_word by lia. unfold TASK_SIZE. lia.
    + (* the block is nonempty *)
      lia.
    + (* the write-all retry loop, per delivered length *)
      intros n Hn1 Hn2.
      norm_pc.
      apply (src_put_wall (length bs) bs src_buf n).
      * lia.
      * exact Hn1.
      * exact Hn2.
      * lia.
      * rewrite u_src_buf; lia.
      * rewrite u_src_buf; lia.
      * regupd_resolve; reflexivity.
      * regupd_resolve; sym_regs HR2; sym_close.
      * regupd_resolve; sym_regs HR2; sym_close.
      * regupd_resolve; sym_regs HR2; sym_regs HR1; sym_close.
      * regupd_resolve; sym_regs HR2; sym_regs HR1; sym_close.
      * repeat first
          [ assumption
          | apply mem_ok_scratch8; [ | u_norm; lia | u_norm; lia ]
          | apply mem_ok_buf; [ | lia ] ].
      * apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite !rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite !rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes, ?u_src_buf; u_norm; lia).
        apply rdn_write_to_mem. rewrite u_src_buf. lia.
Qed.

(* ================================================================= *)
(* From the initial state to the loop head                           *)
(* ================================================================= *)

Lemma src_init_to_rd :
  to_rd rsegs src_LH (Z_to_bv 64 1024)
    (init_machine_state rsegs 0x11078 source_phdrs rsp rmb rrnd inp).
Proof.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargc.
  assert (Hargc_rd : rdn rsegs wmem rsp 8%nat = Some (word_le8 argcN)).
  { unfold wmem. rewrite rdn_wrap_stack_above by lia.
    apply read_argc. apply source_bsb_nw. }
  rewrite init_mkst. norm_pc.
  (* _start: auipc gp,0x2 ; addi gp,gp,1928 *)
  stepi (SFv SF_11078) SD_11078.
  stepiv (SFv SF_1107c) SD_1107c (0x13800 : word) ltac:(getr_resolve; bveq).
  (* ld a0,0(sp): a0 := argc *)
  step_intro;
    [ reflexivity
    | eapply step_ld with (bs := word_le8 argcN) (v := argcN);
      [ exact (SFv SF_11080) | reflexivity | exact SD_11080
      | match goal with |- rdn _ _ ?ad _ = _ =>
          replace ad with rsp
            by (getr_resolve; rewrite v_addi_0; reflexivity)
        end; exact Hargc_rd
      | exact (bytes_le_n_to_le_8 _) ]
    | step_simpl ].
  (* addi a1,sp,8 ; slli t0,a0,3 ; add a2,a1,t0 ; addi a2,a2,8 *)
  stepiv (SFv SF_11084) SD_11084 (Z_to_bv 64 (bv_unsigned rsp + 8))
    ltac:(getr_resolve; sp_norm; f_equal; lia).
  stepi (SFv SF_11088) SD_11088.
  stepi (SFv SF_1108c) SD_1108c.
  stepiv (SFv SF_11090) SD_11090 envp_ptr ltac:(getr_resolve; exact envp_ptr_eq).
  (* auipc t1,0x2 ; addi t1,t1,-148 ; sd a2,0(t1): environ := envp_ptr *)
  stepi (SFv SF_11094) SD_11094.
  stepiv (SFv SF_11098) SD_11098 (0x13000 : word) ltac:(getr_resolve; bveq).
  ssd (SFv SF_1109c) SD_1109c (0x13000 : word) envp_ptr ltac:(getr_resolve; reflexivity).
  (* jal main *)
  stepj (SFv SF_110a0) SD_110a0.
  (* main prologue: addi sp,sp,-32 ; sd s0,16(sp) ; sd ra,24(sp) ;
     addi s0,gp,-2040 (s0 := buf) *)
  stepiv (SFv SF_11000) SD_11000 (Z_to_bv 64 (bv_unsigned rsp - 32))
    ltac:(getr_resolve; sp_norm; f_equal; lia).
  ssd (SFv SF_11004) SD_11004 (Z_to_bv 64 (bv_unsigned rsp - 16)) (Z_to_bv 64 0)
    ltac:(getr_resolve; reflexivity).
  ssd (SFv SF_11008) SD_11008 (Z_to_bv 64 (bv_unsigned rsp - 8)) (0x110a4 : word)
    ltac:(getr_resolve; bveq).
  stepiv (SFv SF_1100c) SD_1100c src_buf ltac:(getr_resolve; bveq).
  (* at the loop head *)
  apply src_LH_to_rd.
  unfold src_LH. do 2 eexists. split; [reflexivity|].
  split; [regupd_resolve; reflexivity|].
  split; [regupd_resolve; reflexivity|].
  split.
  - regupd_resolve; reflexivity.
  - exact fmem_ok.
Qed.

End SourceProof.
