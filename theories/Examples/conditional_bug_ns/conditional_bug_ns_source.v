(** * conditional-bug-ns SOURCE binary (musl-gcc -Os).

    PROOF-SIDE FILE (not part of the trusted specification).

    Delivers the four [to_wexit] derivations of the source binary plus the
    universal SOURCE-ERROR ESCAPE witness for the 'o' arm:

      - [source_wexit_lt2]   : argc < 2            -> no output, exit 2
      - [source_wexit_n]     : argv[1][0] = 'n'    -> no output, exit 0
      - [source_wexit_h]     : argv[1][0] = 'h'    -> "hello\n", exit 0
      - [source_wexit_other] : any other first byte (not 'n'/'h'/'o')
                                                   -> no output, exit 3
      - [source_err_o]       : argv[1][0] = 'o'    -> the machine runs into
        the illegal volatile load from unmapped address 64 ([msteps] to a
        state whose next step is [MachineFault]); with
        [Common.ErrEscape.err_escape_strong_equiv] proves that every
        execution errors — a genuine fault, so the run is still
        [Equivalence.modeled] — and therefore frees the target.

    STEPPING.  Every instruction of every path is executed by
    [Common/SymTac.v]'s reflective [sym_block], except the musl [write]
    blob, which is [Common/MuslCall.v]'s address-parametric summary
    (instantiated in [conditional_bug_ns_hoare.v]).  The five paths share
    the same crt entry + dispatch prologue; each is ONE block, taken all
    the way to its [ecall] (or, on the 'o' arm, to the faulting load),
    with the dispatch encoded as a branch script rather than as a chain
    of per-instruction step lemmas.  What is left per path is exactly the
    mathematical content: the image reads, the store legality, and the
    branch conditions.

    The run reads [Run.run_segments] (the image's segments, then the vDSO
    pair): each derivation steps over [source_segs ++ vt] with the pair an
    abstract tail [vt], except that the 'o' arm's fault needs the pair
    above address 64 ([conditional_bug_ns_defs.srom_64_none_run]).  The
    stack bounds come from the entry predicate's launch conjunct
    [Run.entry_launch_ok_va] and [Run.valid_launch]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec ErrEscape StepTac StreamSim WallSim StoreOk RunSegmentsLift.
(** The musl [write] blob at 0x110fc is not walked here: it is
    [Common/MuslCall.v]'s address-parametric summary, instantiated at this
    binary's addresses in [conditional_bug_ns_hoare.v]. *)
From LinuxProcessSemantics.Common Require Import Hoare MuslCall.
From LinuxProcessSemantics.Common Require Import Footprint SymExec SymTac SymBranch SymSide.
From LinuxProcessSemantics.Examples.conditional_bug_ns Require Import conditional_bug_ns_code conditional_bug_ns_defs conditional_bug_ns_hoare.
From LinuxProcessSemantics.Examples.conditional_bug_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.conditional_bug_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them. *)
#[local] Instance conditional_bug_ns_source_fx : FPState := fx0.

Section SourceProof.

Variable inp : ProcInput.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hvl : valid_launch inp.

(** The initial stack pointer, the program break and the mmap base are
    QUANTIFIED (ASLR): the whole section is generic over them. *)
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
    ([StepTac.bsb_bound]), places argv's strings, and puts [rsp] at or
    below the stack VMA's end, which the stack-store window needs. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry rsp rbrk rmb rrnd) inp.

Lemma rsp_lo_num : (0x7fff80000000 <= bv_unsigned rsp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma rsp_hi_num : (bv_unsigned rsp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Definition argcN : word := len_word (in_argv inp).

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length (in_argv inp)).
Proof.
  pose proof (valid_argv_len (in_argv inp) Hva).
  unfold argcN, len_word. apply u_Z2bv; lia.
Qed.

(** No-overflow bound for the initial stack image (feeds the stack-read
    lemmas' side conditions), for any entry word the auxv carries. *)
Lemma source_bsb_nw : forall entry : word,
  (bv_unsigned rsp
   + Z.of_nat (length (entry_stack_image inp rmb source_phdrs entry rsp rrnd)) < 2^64)%Z.
Proof.
  intros entry.
  pose proof (bsb_bound Sv48 inp rmb source_phdrs entry rsp rbrk rrnd Hvl Hlau).
  pose proof rsp_hi_num. lia.
Qed.

(** The pointer _start stores into musl's [__environ] slot at 0x13000. *)
Definition envp_ptr : word :=
  Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat (length (in_argv inp)) + 8).

(** The value _start computes in a2 equals [envp_ptr]. *)
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

(** The argv[1] string pointer: the strings sit at the TOP of the entry
    block, below the stack VMA's end. *)
Definition ptr1 : word :=
  cat_argv_ptr (ed_top rrnd) (in_argv inp) (in_envp inp) (in_execfn inp) 1.

Lemma ptr1_bounds : (2 <= length (in_argv inp))%nat ->
  (bv_unsigned rsp <= bv_unsigned ptr1)%Z /\
  (bv_unsigned ptr1 + Z.of_nat (length (nth 1 (in_argv inp) [])) + 1 < 2^64)%Z.
Proof.
  intro H. unfold ptr1.
  exact (argv_ptr_bounds Sv48 inp rmb rsp rbrk rrnd 1 Hlau ltac:(lia)).
Qed.

(** argv pointer 1 at [rsp + 16]. *)
Lemma read_ptr1 : forall segs entry, (2 <= length (in_argv inp))%nat ->
  rdn segs (stack_to_mem rsp (entry_stack_image inp rmb source_phdrs entry rsp rrnd))
      (rsp + nat_to_word (8 + 8 * 1)) 8%nat
  = Some (word_le8 ptr1).
Proof.
  intros segs entry H. unfold ptr1.
  apply read_argv_ptr_k; [lia | apply source_bsb_nw].
Qed.

(** The first byte of argv[1] (its NUL if the string is empty). *)
Lemma read_b : forall segs entry, (2 <= length (in_argv inp))%nat ->
  rdn segs (stack_to_mem rsp (entry_stack_image inp rmb source_phdrs entry rsp rrnd)) ptr1 1%nat
  = Some [byte_at (nth 1 (in_argv inp) []) 0].
Proof.
  intros segs entry H. unfold ptr1, byte_at.
  rewrite <- (word_add_0 (cat_argv_ptr (ed_top rrnd) (in_argv inp) (in_envp inp)
                            (in_execfn inp) 1)).
  apply (read_argv_byte_k Sv48 segs inp rmb source_phdrs entry rsp rbrk rrnd 1 0 Hlau);
    lia.
Qed.

(** The dispatched byte, zero-extended into a machine word.  This is the
    value the [lbu] at 0x11014 leaves in a5, and — because the reflective
    executor takes the loaded word as a caller-supplied NAME (the
    [rvals] argument of [sym_block]) — the one spelling in which both
    the load's [SCReadBase] obligation and the three dispatch branches
    are stated. *)
Definition bval : word := Z_to_bv 64 (bv_unsigned (byte_at (nth 1 (in_argv inp) []) 0)).

Lemma u_bval : bv_unsigned bval = bv_unsigned (byte_at (nth 1 (in_argv inp) []) 0).
Proof.
  unfold bval. pose proof (u8_range (byte_at (nth 1 (in_argv inp) []) 0)).
  apply u_Z2bv; lia.
Qed.

(* ================================================================= *)
(* The prologue's image obligations, shared by all five paths.        *)
(* ================================================================= *)

(** Every block below starts at the crt entry, so every one of them
    raises the same side conditions about the initial image: the
    [ld a0,0(sp)] of argc, the [sd a2,0(t1)] into musl's [__environ]
    slot, and — on the four paths that get that far — the [ld a5,8(a1)]
    of argv[1] and the [lbu] of its first byte.  They are stated once
    here, against the BASE memory the executor's [SCReadBase] /
    [SCStoreOk] obligations are phrased in (the store log is lifted
    monotonically, so no overlay peeling is needed). *)

Ltac cb_read_argc :=
  replace (Z_to_bv 64 (bv_unsigned rsp + 0)) with rsp by (apply bv_eq; u_norm; lia);
  exists (word_le8 argcN); split;
    [ rewrite rdn_wrap_stack_above by lia; apply read_argc; apply source_bsb_nw
    | apply bytes_le_n_to_le_8 ].

Ltac cb_store_environ := apply source_store_ok; u_norm; lia.

Ltac cb_read_ptr1 Hge2 :=
  replace (Z_to_bv 64 (bv_unsigned rsp + 16)) with (rsp + nat_to_word (8 + 8 * 1))
    by (rewrite word_add_nat; f_equal; cbn [Z.of_nat Nat.add Nat.mul]; lia);
  exists (word_le8 ptr1); split;
    [ rewrite rdn_wrap_stack_above by (rewrite ?word_add_nat; u_norm; lia);
      apply read_ptr1; exact Hge2
    | apply bytes_le_n_to_le_8 ].

Ltac cb_read_byte Hge2 :=
  replace (Z_to_bv 64 (bv_unsigned ptr1 + 0)) with ptr1 by (apply bv_eq; u_norm; lia);
  exists [byte_at (nth 1 (in_argv inp) []) 0]; split;
    [ rewrite rdn_wrap_stack_above by lia; apply read_b; exact Hge2
    | cbn [bytes_le_to_Z]; rewrite Z.shiftl_0_l, Z.lor_0_r; symmetry; exact u_bval ].

(** The [bge a5,a0] at 0x11004, in both directions. *)
Ltac cb_argc_br :=
  rewrite ?negb_true_iff, ?negb_false_iff;
  rewrite bv_lts_small by (u_norm; rewrite ?u_argcN; lia);
  first [ apply Z.ltb_ge | apply Z.ltb_lt ]; u_norm; rewrite u_argcN; lia.

(* ================================================================= *)
(* argc < 2: exit 2, no output.                                       *)
(* ================================================================= *)

Lemma source_wexit_lt2 : (length (in_argv inp) < 2)%nat ->
  to_wexit (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) 0x110a4 source_phdrs
       rsp rmb rrnd inp)
    [] (Z_to_bv 64 2).
Proof.
  intros Hlt2.
  unfold run_segments.
  generalize (vdso_segments (in_kernel inp) rsp rmb) as vt. intros vt.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargc.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  rewrite init_mkst. norm_pc.
  (* crt [_start], [main]'s [bge] taken, [li a0,2], [ret], crt's exit
     tail — FIFTEEN instructions, one block, stopping at the [ecall]. *)
  sym_block (source_segs ++ vt) 20%nat [true] (@nil expr)
    [((2 : reg), EVar 32)] [rsp] [argcN] RA HRA.
  { (* [bge a5,a0] taken: 1 >= argc *) cb_argc_br. }
  { (* [sd a2,0(t1)] -> musl's [__environ] slot at 0x13000 *) cb_store_environ. }
  { (* [ld a0,0(sp)] -> argc, out of the initial stack image *) cb_read_argc. }
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ (fetch_word_app _ _ _ _ SF_110d4) eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRA; sym_close.
  - sym_regs HRA; sym_close.
  - u_norm; lia.
Qed.

Optimize Heap.

(* ================================================================= *)
(* argv[1][0] = 'n': exit 0, no output.                               *)
(* ================================================================= *)

Lemma source_wexit_n : (2 <= length (in_argv inp))%nat ->
  byte_at (nth 1 (in_argv inp) []) 0 = Z_to_bv 8 110 ->
  to_wexit (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) 0x110a4 source_phdrs
       rsp rmb rrnd inp)
    [] (Z_to_bv 64 0).
Proof.
  intros Hge2 Hb.
  unfold run_segments.
  generalize (vdso_segments (in_kernel inp) rsp rmb) as vt. intros vt.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargc.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  destruct (ptr1_bounds Hge2) as [Hp1 Hp2].
  rewrite init_mkst. norm_pc.
  sym_block (source_segs ++ vt) 25%nat [false; true] (@nil expr)
    [((2 : reg), EVar 32)] [rsp] [argcN; ptr1; bval] RA HRA.
  { (* [beq a5,a4] taken: the byte is 'n' *)
    unfold bval; rewrite Hb; vm_compute; reflexivity. }
  { (* [lbu a5,0(a5)] -> the first byte of argv[1] *) cb_read_byte Hge2. }
  { (* [ld a5,8(a1)] -> the argv[1] pointer *) cb_read_ptr1 Hge2. }
  { (* [bge a5,a0] falls through: argc >= 2 *) cb_argc_br. }
  { (* [sd a2,0(t1)] -> musl's [__environ] slot *) cb_store_environ. }
  { (* [ld a0,0(sp)] -> argc *) cb_read_argc. }
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ (fetch_word_app _ _ _ _ SF_110d4) eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRA; sym_close.
  - sym_regs HRA; sym_close.
  - u_norm; lia.
Qed.

Optimize Heap.

(* ================================================================= *)
(* Any other first byte (not 'n'/'h'/'o'): exit 3, no output.         *)
(* ================================================================= *)

Lemma source_wexit_other : (2 <= length (in_argv inp))%nat ->
  byte_at (nth 1 (in_argv inp) []) 0 <> Z_to_bv 8 110 ->
  byte_at (nth 1 (in_argv inp) []) 0 <> Z_to_bv 8 104 ->
  byte_at (nth 1 (in_argv inp) []) 0 <> Z_to_bv 8 111 ->
  to_wexit (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) 0x110a4 source_phdrs
       rsp rmb rrnd inp)
    [] (Z_to_bv 64 3).
Proof.
  intros Hge2 Hn110 Hn104 Hn111.
  unfold run_segments.
  generalize (vdso_segments (in_kernel inp) rsp rmb) as vt. intros vt.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargc.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  destruct (ptr1_bounds Hge2) as [Hp1 Hp2].
  rewrite init_mkst. norm_pc.
  sym_block (source_segs ++ vt) 30%nat [false; false; true; true] (@nil expr)
    [((2 : reg), EVar 32)] [rsp] [argcN; ptr1; bval] RA HRA.
  { (* [bne a5,a4] taken at 0x11088: the byte is not 'o' *)
    rewrite negb_true_iff; unfold bval;
    apply c_eq_zext_lit_false; [lia | exact Hn111]. }
  { (* [bne a5,a4] taken at 0x11020: the byte is not 'h' *)
    rewrite negb_true_iff; unfold bval;
    apply c_eq_zext_lit_false; [lia | exact Hn104]. }
  { (* [beq a5,a4] falls through: the byte is not 'n' *)
    unfold bval; apply c_eq_zext_lit_false; [lia | exact Hn110]. }
  { cb_read_byte Hge2. }
  { cb_read_ptr1 Hge2. }
  { cb_argc_br. }
  { cb_store_environ. }
  { cb_read_argc. }
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ (fetch_word_app _ _ _ _ SF_110d4) eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRA; sym_close.
  - sym_regs HRA; sym_close.
  - u_norm; lia.
Qed.

Optimize Heap.

(* ================================================================= *)
(* argv[1][0] = 'h': write "hello\n", exit 0.                          *)
(* ================================================================= *)

(** The initial writable overlay: the put-loop invariant carries
    [mem_grows] over it, which is what makes the loop's stack respills
    legal ([store_ok] is monotone under overlay growth).  The entry
    word is the one [init_mkst] names. *)
Definition cbwmem : word -> option byte :=
  wrap_mem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x110a4)) rsp rrnd.

Lemma cb_sok8 : forall vt (mem : word -> option byte) (a : word),
  mem_grows cbwmem mem ->
  (bv_unsigned rsp - 48 <= bv_unsigned a)%Z ->
  (bv_unsigned a + 8 <= bv_unsigned rsp)%Z ->
  RiscvSemantics.store_ok (source_segs ++ vt) mem a 8%nat = true.
Proof.
  intros vt mem a Hg Hlo Hhi.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  eapply store_ok_mono; [exact Hg|].
  unfold cbwmem.
  eapply store_ok_wrap_window_valid;
    [ exact Hvl | exact Hlau
    | unfold stack_window_reach, stack_max_size; lia | lia ].
Qed.

Local Ltac cb_grows := unfold cbwmem; solve_mem_grows.

Local Ltac cb_sok := apply cb_sok8; [ cb_grows | u_norm; lia | u_norm; lia ].

(** A store-double / load-double with pre-normalized address+value. *)
Local Ltac cb_ssd F D aexp vexp vtac := stepsd F D aexp vexp vtac ltac:(cb_sok).

Local Ltac cb_sld F D aexp vexp readtac := stepld F D aexp vexp readtac.

(** The put-style retry loop after a (possibly short) write delivery:
    from the post-write state at 0x11048 (main's return point from the
    musl [write] wrapper) — a0 = the delivered length, the offered
    pointer/count in the two spill slots at sp+0/sp+8 — the loop runs
    [blez a0] (fall-through), reloads the spills, updates them, and
    either falls into the exit-0 tail ([bnez] not taken, full delivery)
    or respills and reissues the write through the wrapper.  Induction
    on [fuel >= length bs], over the run's list [source_segs ++ vt]. *)
Lemma src_put_wall : forall vt fuel (bs : list byte) (p : word) n regs mem,
  (length bs <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length bs)%nat ->
  (Z.of_nat (length bs) <= 6)%Z ->
  (0x12000 <= bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length bs) <= 0x12006)%Z ->
  reg_get regs 10 = len_word (firstn n bs) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 32) ->
  mem_grows cbwmem mem ->
  rdn (source_segs ++ vt) mem (Z_to_bv 64 (bv_unsigned rsp - 32)) 8%nat
    = Some (word_to_le_bytes 8 p) ->
  rdn (source_segs ++ vt) mem (Z_to_bv 64 (bv_unsigned rsp - 24)) 8%nat
    = Some (word_to_le_bytes 8 (len_word bs)) ->
  rdn (source_segs ++ vt) mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
    = Some (word_to_le_bytes 8 (0x110d0 : word)) ->
  rdn (source_segs ++ vt) mem p (length bs) = Some bs ->
  to_wall_tail (source_segs ++ vt) (Z_to_bv 64 1)
    (mkst regs (0x11048 : word) mem (seg_rom (source_segs ++ vt)))
    (skipn n bs)
    (to_wallexit (source_segs ++ vt) (Z_to_bv 64 1) [] (Z_to_bv 64 0)).
Proof.
  intros vt fuel.
  induction fuel as [|fuel IH];
    intros bs p n regs mem Hfuel Hn1 Hn2 Hlen Hplo Hphi
           H10 H2 Hgrow Hptr Hcnt Hra Hread.
  { lia. }
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  (* 0x11048: blez a0 falls through (the delivery is nonempty) *)
  step_intro;
    [ reflexivity
    | eapply step_bge_ft;
      [ exact (fetch_word_app _ _ _ _ SF_11048) | reflexivity | exact SD_11048
      | getr_resolve; rewrite H10; apply c_lts_0_pos;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x1104c: ld a2,8(sp) — the count spill *)
  cb_sld (fetch_word_app _ vt _ _ SF_1104c) SD_1104c
    (Z_to_bv 64 (bv_unsigned rsp - 24)) (len_word bs)
    ltac:(exact Hcnt).
  (* 0x11050: ld a1,0(sp) — the pointer spill *)
  cb_sld (fetch_word_app _ vt _ _ SF_11050) SD_11050
    (Z_to_bv 64 (bv_unsigned rsp - 32)) p
    ltac:(exact Hptr).
  (* 0x11054: sub a2,a2,a0 — the count decrement *)
  stepiv (fetch_word_app _ vt _ _ SF_11054) SD_11054 (len_word (skipn n bs))
    ltac:(getr_resolve; rewrite H10; apply v_sub_len_firstn; lia).
  (* 0x11058: add a1,a1,a0 — the pointer bump *)
  stepiv (fetch_word_app _ vt _ _ SF_11058) SD_11058 (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
    ltac:(getr_resolve; rewrite H10; apply v_add_len_firstn_Z; lia).
  destruct (Nat.eq_dec n (length bs)) as [-> | Hne].
  - (* full delivery: bnez not taken, fall into the exit-0 tail *)
    rewrite skipn_all.
    step_intro;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact (fetch_word_app _ _ _ _ SF_1105c) | reflexivity | exact SD_1105c
        | getr_resolve; apply c_eq_0_of_u; reflexivity ]
      | norm_pc ].
    (* 0x11060: li a0,0 *)
    stepiv (fetch_word_app _ vt _ _ SF_11060) SD_11060 (Z_to_bv 64 0) ltac:(getr_resolve; bveq).
    (* 0x11064: ld ra,24(sp) — main's return address 0x110d0 *)
    cb_sld (fetch_word_app _ vt _ _ SF_11064) SD_11064 (Z_to_bv 64 (bv_unsigned rsp - 8))
      (0x110d0 : word) ltac:(exact Hra).
    (* 0x11068: sltu a0,x0,a0 (a0 = 0) ; 0x1106c: sllw a0,a0,2 *)
    stepi (fetch_word_app _ vt _ _ SF_11068) SD_11068.
    stepi (fetch_word_app _ vt _ _ SF_1106c) SD_1106c.
    (* 0x11070: addi sp,sp,32 — pop main's frame (sp is dead past here) *)
    stepi (fetch_word_app _ vt _ _ SF_11070) SD_11070.
    (* 0x11074: ret -> 0x110d0 (crt exit tail) *)
    stepjr (fetch_word_app _ vt _ _ SF_11074) SD_11074 (0x110d0 : word)
      ltac:(getr_resolve; reflexivity).
    (* 0x110d0: li a7,93 *)
    stepiv (fetch_word_app _ vt _ _ SF_110d0) SD_110d0 (Z_to_bv 64 93) ltac:(getr_resolve; bveq).
    apply twt_done. cbn [to_wallexit].
    eapply tw_step;
      [ reflexivity
      | apply (step_ecall _ _ _ _ _ _ (fetch_word_app _ _ _ _ SF_110d4) eq_refl) | ].
    apply tw_exit_coden.
    + getr_resolve; reflexivity.
    + regupd_resolve; getr_resolve; bveq.
    + vm_compute; reflexivity.
  - (* short delivery: bnez taken, respill and reissue *)
    step_intro;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact (fetch_word_app _ _ _ _ SF_1105c) | reflexivity | exact SD_1105c
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* 0x11038: li a0,1 *)
    stepiv (fetch_word_app _ vt _ _ SF_11038) SD_11038 (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* 0x1103c: sd a2,8(sp) — respill the count *)
    cb_ssd (fetch_word_app _ vt _ _ SF_1103c) SD_1103c (Z_to_bv 64 (bv_unsigned rsp - 24))
      (len_word (skipn n bs)) ltac:(getr_resolve; reflexivity).
    (* 0x11040: sd a1,0(sp) — respill the pointer *)
    cb_ssd (fetch_word_app _ vt _ _ SF_11040) SD_11040 (Z_to_bv 64 (bv_unsigned rsp - 32))
      (Z_to_bv 64 (bv_unsigned p + Z.of_nat n)) ltac:(getr_resolve; reflexivity).
    (* 0x11044: jal ra,write — into the wrapper at 0x110fc *)
    stepj (fetch_word_app _ vt _ _ SF_11044) SD_11044.
    (* the whole wrapper call, by the summary *)
    assert (Hs40 : at_ (Z_to_bv 64 (bv_unsigned rsp - 32)) (-8)
                   = Z_to_bv 64 (bv_unsigned rsp - 40))
      by (unfold at_; u_norm; f_equal; lia).
    eapply (cb_write_call vt _ _ _ (0x11048 : word)
              (Z_to_bv 64 (bv_unsigned rsp - 32))
              (Z_to_bv 64 (bv_unsigned p + Z.of_nat n))
              (len_word (skipn n bs)));
      rewrite ?Hs40.
    + vm_compute; reflexivity.
    + getr_resolve; bveq.
    + getr_resolve; rewrite H2; reflexivity.
    + getr_resolve; reflexivity.
    + getr_resolve; reflexivity.
    + getr_resolve; reflexivity.
    + cb_sok.
    + u_norm; lia.
    + rewrite u_len_word by (rewrite length_skipn; lia);
      rewrite length_skipn; lia.
    + (* the remainder read back at the bumped pointer *)
      replace (word_to_nat (len_word (skipn n bs)))
        with (length (skipn n bs))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      rewrite !rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes, ?length_skipn; u_norm; lia).
      pose proof (rdn_skipn (source_segs ++ vt) mem (length bs) p bs n Hread Hn2)
        as Hsk.
      rewrite word_add_nat_Z in Hsk by lia.
      rewrite length_skipn. exact Hsk.
    + (* the remainder's range passes [access_ok]: inside .rodata *)
      apply access_okb_intro.
      rewrite u_len_word by (rewrite length_skipn; lia).
      rewrite length_skipn. u_norm. unfold TASK_SIZE. lia.
    + rewrite length_skipn; lia.
    + (* the (shorter) remainder, by induction *)
      intros regs'' m Hm1 Hm2 R1 R2 R10.
      apply (IH (skipn n bs) (Z_to_bv 64 (bv_unsigned p + Z.of_nat n)) m).
      * rewrite length_skipn; lia.
      * exact Hm1.
      * exact Hm2.
      * rewrite length_skipn; lia.
      * rewrite u_Z2bv by lia; lia.
      * rewrite u_Z2bv by lia; rewrite length_skipn; lia.
      * exact R10.
      * exact R2.
      * cb_grows.
      * rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite !rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite !rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        exact Hra.
      * rewrite !rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes, ?length_skipn; u_norm; lia).
        pose proof (rdn_skipn (source_segs ++ vt) mem (length bs) p bs n Hread Hn2)
          as Hsk.
        rewrite word_add_nat_Z in Hsk by lia.
        rewrite length_skipn. exact Hsk.
Qed.

Lemma source_wexit_h : (2 <= length (in_argv inp))%nat ->
  byte_at (nth 1 (in_argv inp) []) 0 = Z_to_bv 8 104 ->
  to_wallexit (run_segments source_segs inp rsp rmb) (Z_to_bv 64 1) [hello] (Z_to_bv 64 0)
    (init_machine_state (run_segments source_segs inp rsp rmb) 0x110a4 source_phdrs
       rsp rmb rrnd inp).
Proof.
  intros Hge2 Hb.
  unfold run_segments.
  generalize (vdso_segments (in_kernel inp) rsp rmb) as vt. intros vt.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargc.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  destruct (ptr1_bounds Hge2) as [Hp1 Hp2].
  split; [cbn; lia|].
  rewrite init_mkst. norm_pc.
  (* ---------------- crt _start + main: 0x110a4 .. 0x11044 ----------------
     TWENTY-NINE instructions in ONE reflective block: the crt entry
     sequence, the whole three-way dispatch on the first byte of argv[1]
     falling through to the 'h' arm, main's frame push, the three
     spills, and the [jal] into musl's [write] — which leaves the goal
     standing exactly at the blob's entry, 0x110fc, where the summary
     takes over. *)
  sym_block (source_segs ++ vt) 29%nat [false; false; false] (@nil expr)
    [((2 : reg), EVar 32)] [rsp] [argcN; ptr1; bval] RA HRA.
  { (* [sd a1,0(sp)] at 0x11040 *) solve_store_ok. }
  { (* [sd a2,8(sp)] at 0x1103c *) solve_store_ok. }
  { (* [sd ra,24(sp)] at 0x1102c *) solve_store_ok. }
  { (* [bne a5,a4] falls through at 0x11020: the byte IS 'h' *)
    rewrite negb_false_iff; unfold bval; rewrite Hb; vm_compute; reflexivity. }
  { (* [beq a5,a4] falls through at 0x11018: 'h' is not 'n' *)
    unfold bval; rewrite Hb; vm_compute; reflexivity. }
  { cb_read_byte Hge2. }
  { cb_read_ptr1 Hge2. }
  { cb_argc_br. }
  { cb_store_environ. }
  { cb_read_argc. }

  (* ---------------- musl write ---------------- *)
  (* 0x110fc..0x11138 -- musl's [write] wrapper, [__syscall_cp], the write
     [ecall] and [__syscall_ret]'s not-taken errno branch -- used to be
     ~165 lines of hand-stepped chain here.  The blob is
     position-independent and byte-identical in every example, so it is
     proved ONCE over an abstract load address in [Common/MuslCall.v] and
     instantiated at this binary's 0x110fc in
     [conditional_bug_ns_hoare.v].  The block above hands it its five
     register preconditions through [sym_regs]. *)
  assert (Hs40 : at_ (Z_to_bv 64 (bv_unsigned rsp - 32)) (-8)
                 = Z_to_bv 64 (bv_unsigned rsp - 40))
    by (unfold at_; u_norm; f_equal; lia).
  assert (Hu12000 : bv_unsigned (0x12000 : word) = 0x12000%Z)
    by (vm_compute; reflexivity).
  eapply (cb_write_call vt _ _ _ (0x11048 : word)
            (Z_to_bv 64 (bv_unsigned rsp - 32)) (0x12000 : word)
            (Z_to_bv 64 6));
    rewrite ?Hs40.
  - (* the caller's return address is even *) vm_compute; reflexivity.
  - (* ra: main's return point *) sym_regs HRA; sym_close.
  - (* sp *) sym_regs HRA; sym_close.
  - (* a0 = 1 (stdout) *) sym_regs HRA; sym_close.
  - (* a1 = the string *) sym_regs HRA; sym_close.
  - (* a2 = 6 *) sym_regs HRA; sym_close.
  - (* the wrapper's own [ra] spill slot is storable *) solve_store_ok.
  - (* ... and does not wrap *) u_norm; lia.
  - (* 6 is not in [__syscall_ret]'s errno window *) u_norm; lia.
  - (* the six bytes of "hello\n", straight from the image *)
    replace (word_to_nat (Z_to_bv 64 6)) with 6%nat by (vm_compute; reflexivity).
    rewrite !rdn_wbytes_below
      by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
    erewrite rdn_ext;
      [ apply srom_hello
      | imm_norm; lia
      | intros x Hx; revert Hx; imm_norm; intros Hx;
        eapply wrap_mem_below; [exact Hlau | rewrite stack_max_size_val; lia] ].
  - (* the string's range passes [access_ok]: a link-time address *)
    vm_compute; reflexivity.
  - (* "hello\n" is nonempty *) cbn; lia.
  - (* back from [write], at 0x11048: the put-loop invariant *)
    intros regs' n Hn1 Hn2 R1 R2 R10.
    apply (src_put_wall vt (length hello) hello (0x12000 : word) n).
    + lia.
    + exact Hn1.
    + exact Hn2.
    + cbn; lia.
    + rewrite Hu12000; lia.
    + rewrite Hu12000; cbn; lia.
    + exact R10.
    + exact R2.
    + (* the whole overlay chain grows out of the initial stack image *)
      cb_grows.
    + (* the pointer spill at sp+0, past the wrapper's [ra] spill *)
      rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
      rewrite rdn_wbytes_hit8 by (u_norm; lia).
      first [ reflexivity | do 2 f_equal; bveq ].
    + (* the count spill at sp+8 *)
      rewrite !rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
      rewrite rdn_wbytes_hit8 by (u_norm; lia).
      first [ reflexivity | do 2 f_equal; bveq ].
    + (* main's [ra] spill at sp+24 *)
      rewrite !rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
      rewrite rdn_wbytes_hit8 by (u_norm; lia).
      first [ reflexivity | do 2 f_equal; bveq ].
    + (* the six bytes of "hello\n" *)
      change (length hello) with 6%nat.
      rewrite !rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
      erewrite rdn_ext;
        [ apply srom_hello
        | imm_norm; lia
        | intros x Hx; revert Hx; imm_norm; intros Hx;
          eapply wrap_mem_below; [exact Hlau | rewrite stack_max_size_val; lia] ].
Qed.

Optimize Heap.

(* ================================================================= *)
(* argv[1][0] = 'o': the machine reaches the illegal load at 0x1108c. *)
(* ================================================================= *)

Lemma source_err_o : (2 <= length (in_argv inp))%nat ->
  byte_at (nth 1 (in_argv inp) []) 0 = Z_to_bv 8 111 ->
  exists ms',
    msteps (run_segments source_segs inp rsp rmb)
      (init_machine_state (run_segments source_segs inp rsp rmb) 0x110a4 source_phdrs
         rsp rmb rrnd inp) ms'
    /\ ms_svc_pending ms' = None
    /\ RiscvSemantics.step (run_segments source_segs inp rsp rmb) ms' = MachineFault.
Proof.
  intros Hge2 Hb.
  (* The fault needs the vDSO pair above address 64; everything else
     treats it as an abstract tail [vt]. *)
  pose proof (srom_64_none_run (in_kernel inp) rsp rmb) as H64.
  pose proof (vvar_64_run (in_kernel inp) rsp rmb) as Hvv.
  revert H64 Hvv.
  unfold run_segments.
  generalize (vdso_segments (in_kernel inp) rsp rmb) as vt. intros vt H64 Hvv.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargc.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  destruct (ptr1_bounds Hge2) as [Hp1 Hp2].
  (* The reached state is the WITNESS of an existential, so the block has
     to produce its exit register file BEFORE the [exists] is
     instantiated: [sym_block_ex] is [sym_block] with the [destruct]
     moved out of the goal, which is exactly that. *)
  sym_block_ex (source_segs ++ vt)
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
          (Z_to_bv 64 0x110a4)
          (wrap_mem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x110a4)) rsp rrnd)
          (seg_rom (source_segs ++ vt)))
    23%nat [false; false; true; false] (@nil expr)
    [((2 : reg), EVar 32)] [rsp] [argcN; ptr1; bval] RA HRA Hms.
  { (* [bne a5,a4] falls through at 0x11088: the byte IS 'o' *)
    rewrite negb_false_iff; unfold bval; rewrite Hb; vm_compute; reflexivity. }
  { (* [bne a5,a4] taken at 0x11020: 'o' is not 'h' *)
    rewrite negb_true_iff; unfold bval; rewrite Hb; vm_compute; reflexivity. }
  { (* [beq a5,a4] falls through at 0x11018: 'o' is not 'n' *)
    unfold bval; rewrite Hb; vm_compute; reflexivity. }
  { cb_read_byte Hge2. }
  { cb_read_ptr1 Hge2. }
  { cb_argc_br. }
  { cb_store_environ. }
  { cb_read_argc. }
  rewrite init_mkst.
  match type of Hms with msteps _ _ ?st => exists st end.
  split; [exact Hms | split; [reflexivity |]].
  (* 0x1108c: lbu a5,64(zero) -- address 64 is unmapped: MachineFault *)
  match goal with |- context [Z_to_bv 64 69772] =>
    replace (Z_to_bv 64 69772) with (0x1108c : word) by bveq end.
  eapply step_lbu_fault;
    [ exact (fetch_word_app _ _ _ _ SF_1108c) | reflexivity | exact SD_1108c | | ].
  - sym_regs HRA.
    match goal with |- rdn _ _ ?a _ = _ =>
      replace a with (Z_to_bv 64 64) by bveq end.
    rewrite rdn_wbytes_below
      by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
    erewrite rdn_ext;
      [ exact H64
      | u_norm; lia
      | intros x Hx; revert Hx; u_norm; intros Hx;
        eapply wrap_mem_below; [exact Hlau | rewrite stack_max_size_val; lia] ].
  - (* ... and no byte of it is a vvar byte: a fault, not the model's
       decline *)
    sym_regs HRA.
    match goal with |- range_meets_vvar _ ?a _ = _ =>
      replace a with (Z_to_bv 64 64) by bveq end.
    exact Hvv.
Qed.

End SourceProof.
