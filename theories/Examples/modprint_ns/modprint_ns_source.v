(** * modprint-ns SOURCE binary (musl-gcc -Os).

    PROOF-SIDE FILE (not part of the trusted specification).

    Delivers the single [to_wexit] derivation of the source binary:

      - [source_wexit] : for every input, write(1, mod_buf argc, 2)
                         then exit 0.

    The binary is straight-line from entry to exit — crt [_start], then
    [main], then musl's [write] wrapper down to the [ecall], then back
    out through [__syscall_ret] (whose error branch is not taken: the
    modeled write of a fully readable 2-byte buffer returns 2) and
    finally the [exit] ecall.  There is no branch anywhere that depends
    on the input, so there is exactly one lemma here.

    The run reads [Run.run_segments] (the image's segments, then the vDSO
    pair): the derivation steps over [source_segs ++ vt] with the pair an
    abstract tail [vt], and the stack bounds come from the entry
    predicate's launch conjunct [Run.entry_launch_ok_va] and
    [Run.valid_launch]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec MmapSim NumPrint StepTac StreamSim StoreOk RunSegmentsLift.
(** Not [Import]ed: its [argcN]/[envp_ptr] are instantiated below under the
    per-binary names, so the qualified reference is the readable one. *)
From LinuxProcessSemantics.Common Require ArgvEnv.
(** The musl [write] blob at 0x11098 is not walked here: it is
    [Common/MuslCall.v]'s address-parametric summary, instantiated at this
    binary's addresses in [modprint_ns_hoare.v]. *)
From LinuxProcessSemantics.Common Require Import Hoare MuslCall.
From LinuxProcessSemantics.Common Require Import Footprint SymExec SymTac.
From LinuxProcessSemantics.Examples.modprint_ns Require Import modprint_ns_code modprint_ns_defs modprint_ns_hoare.
From LinuxProcessSemantics.Examples.modprint_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.modprint_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivation runs from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them. *)
#[local] Instance modprint_ns_source_fx : FPState := fx0.

(* ========================================================================= *)
(* main's epilogue and the crt exit tail, as a STANDALONE lemma              *)
(* ========================================================================= *)

(** The DEMONSTRATION of [SymTac.sym_block_ex] (see its docstring and the
    "what a LOOP needs" section of [Common/SHAPE_ALGEBRA.md]).

    The six instructions from 0x11034 to the [exit] ecall at 0x11070 —
    main's [ld ra,8(sp)] / [addi sp,sp,16] / [ret], then crt's
    [li a0,0] / [li a7,93] — used to be executed by a [sym_block]
    sitting INSIDE [source_wexit]'s single goal, and could not be
    anything else: [sym_block] binds the exit register file to a
    goal-local variable, so no statement of the form "there EXISTS a
    register file such that ... and the machine steps to it" could be
    written down, let alone proved.

    Here it is exactly that statement, standalone, over an abstract
    entry register file, an abstract memory and an abstract frame base.
    Everything the block needs of its caller is a hypothesis:

      - [Hsp]  — where the frame is (the block's only pinned register);
      - [Hnw]  — that the frame does not wrap (what the [SCFlat] of the
                 reload needs, and the one thing the enclosing proof
                 used to supply implicitly from the [rsp] window);
      - [Hrd]  — that _start's return address is in the [ra] spill slot,
                 which is the [SCReadBase] of the [ld]: the caller's
                 memory layout stays at the CALL SITE, where it belongs.

    and everything it gives back is in the conclusion: the two registers
    the [exit] ecall reads, and the [msteps]. *)
Lemma source_main_epilogue :
  forall (vt : list Segment) (regs : bvmap 5 word) (mem rom : word -> option byte) (sp0 : word),
  getr regs 2 = sp0 ->
  (bv_unsigned sp0 + 16 <= 2 ^ 64)%Z ->
  (exists bs, rdn (source_segs ++ vt) mem (Z_to_bv 64 (bv_unsigned sp0 + 8)) 8%nat = Some bs
              /\ bytes_le_to_Z bs = 0x1106c%Z) ->
  exists R,
       getr R 10 = Z_to_bv 64 0
    /\ getr R 17 = Z_to_bv 64 93
    /\ msteps (source_segs ++ vt)
         (mkst regs (Z_to_bv 64 0x11034) mem rom)
         (mkst R (Z_to_bv 64 0x11070) mem rom).
Proof.
  intros vt regs mem rom sp0 Hsp Hnw Hrd.
  pose proof (u64_range sp0) as Hu.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 0x11034) mem rom)
    6%nat (@nil bool) [ELit 0x1106c]
    [((2 : reg), EVar 32)] [sp0] (@nil word) R H Hms.
  { (* [ld ra,8(sp)] -> _start's return address, out of main's frame *)
    destruct Hrd as (bs & Hr & Hv). exists bs. split;
      [ exact Hr | rewrite Hv; vm_compute; reflexivity ]. }
  { (* the [sp] pin *) exact Hsp. }
  exists R. split; [|split];
    [ sym_regs H; sym_close | sym_regs H; sym_close | exact Hms ].
Qed.

Section SourceProof.

Variable inp : ProcInput.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hvl : valid_launch inp.

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
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned rsp)%Z.
Hypothesis Hsp_hi : (bv_unsigned rsp <= sp_window_hi)%Z.

(** The fifth conjunct of [Run.valid_entry_va]: this placement is one a
    Linux launch can give ([create_elf_tables] and [setup_arg_pages],
    fs/binfmt_elf.c and fs/exec.c, Linux v6.18.46, commit
    1f99e9ab748f).  With [Hvl] it bounds the entry block
    ([StepTac.bsb_bound]) and puts [rsp] at or below the stack VMA's
    end, which is what the stack-store window needs. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry rsp rbrk rmb rrnd) inp.

(** The startup scaffolding — sp-window bounds as raw hex, [argc] as a
    word, the initial stack image's no-overflow bound, and musl's
    [__environ] pointer — is proved ONCE, generically, in
    [Common/ArgvEnv.v]; this section only instantiates it at the source's
    [rsp].  [modprint_ns_target.v] instantiates the same lemmas at [asp].
    Do not re-derive them here: the point of ArgvEnv is that a change to
    the sp window or to [entry_stack_image]'s signature is a one-file
    change. *)

Lemma rsp_lo_num : (0x7fff80000000 <= bv_unsigned rsp)%Z.
Proof. apply (ArgvEnv.sp_lo_num rsp); assumption. Qed.
Lemma rsp_hi_num : (bv_unsigned rsp <= 0x800000000000)%Z.
Proof. apply (ArgvEnv.sp_hi_num rsp); assumption. Qed.

Definition argcN : word := ArgvEnv.argcN inp.

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length (in_argv inp)).
Proof. apply (ArgvEnv.u_argcN inp); assumption. Qed.

Lemma source_bsb_nw : forall entry : word,
  (bv_unsigned rsp
   + Z.of_nat (length (entry_stack_image inp rmb source_phdrs entry rsp rrnd)) < 2^64)%Z.
Proof.
  intros entry.
  apply (ArgvEnv.bsb_nw Sv48 inp rmb source_phdrs entry rsp rbrk rrnd); assumption.
Qed.

(** The pointer _start stores into musl's [__environ] slot at 0x13010. *)
Definition envp_ptr : word := ArgvEnv.envp_ptr inp rsp.

Lemma envp_ptr_eq :
  v_addi (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli argcN 3)) 8 = envp_ptr.
Proof. apply (ArgvEnv.envp_ptr_eq inp rsp); assumption. Qed.

(** The value the block's [sb] stores into [out[0]].  The executor
    leaves the digit in the ISA's own spelling — a [remu] by the
    [addiw]-computed divisor, sign-extended and offset by 48 — and this
    is where that becomes the spec's ASCII digit.  It is the same three
    arithmetic facts the per-instruction proof used ([v_addiw_zero_7],
    [v_remu_7], [v_addiw_digit]); the difference is that they are
    discharged ONCE about the block's result instead of once per
    instruction, in the middle of the stepping. *)
Lemma stored_digit_val : (0 <= Z.of_nat (length (in_argv inp)) < 2^64)%Z ->
  v_addiw (mul_div M_REMU argcN (v_addiw (v_lw (Z_to_bv 64 0)) 7)) 48
  = Z_to_bv 64 (48 + Z.of_nat (length (in_argv inp)) mod 7).
Proof.
  intro Hn.
  pose proof (mod_rem_range (Z.of_nat (length (in_argv inp))) ltac:(lia)) as Hrem.
  replace (v_addiw (v_lw (Z_to_bv 64 0)) 7) with (Z_to_bv 64 7) by bveq.
  rewrite m_remu by (vm_compute; discriminate).
  replace argcN with (Z_to_bv 64 (Z.of_nat (length (in_argv inp))))
    by (apply bv_eq; rewrite u_argcN, u_Z2bv by lia; reflexivity).
  rewrite v_remu_7 by lia.
  apply v_addiw_digit; exact Hrem.
Qed.

(* ================================================================= *)
(* The single behavior: write the digit and a newline, then exit 0.   *)
(* ================================================================= *)

Lemma source_wexit :
  to_wexit (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) 0x11044 source_phdrs
       rsp rmb rrnd inp)
    (mod_bufs (Z.of_nat (length (in_argv inp)))) (Z_to_bv 64 0).
Proof.
  (* the run's list is the image's followed by the vDSO pair; nothing
     below reads the pair, so it stays an abstract tail [vt] *)
  unfold run_segments.
  generalize (vdso_segments (in_kernel inp) rsp rmb) as vt. intros vt.
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargc.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  pose proof (mod_rem_range (Z.of_nat (length (in_argv inp))) ltac:(lia)) as Hrem.
  unfold mod_bufs. rewrite mod_buf_bytes by lia.
  rewrite init_mkst. norm_pc.
  (* ---------------- crt _start + main: 0x11044 .. 0x11030 ----------------
     TWENTY-THREE instructions in ONE reflective block: the whole crt
     entry sequence (gp setup, the [ld a0,0(sp)] of argc, the envp
     pointer arithmetic and its store into musl's [__environ] slot, the
     [jal] into main) and the whole of main up to the [jal] into write
     (the .sbss [lw], the frame push, [addiw]/[remu]/[addiw] digit
     arithmetic, the [sd] of _start's return address and the [sb] of the
     digit into the output buffer).

     Two loads and three stores across two bases -- the ASLR stack and
     the absolute writable page -- so ten side conditions come back; the
     six [SCFlat]s follow from the sp window and [sym_block] closes
     them, as it does the [sp] pin out of the initial state.  What is
     left below is exactly the four memory facts this binary's image
     supplies plus the [argc] read. *)
  sym_block (source_segs ++ vt) 23%nat (@nil bool) (@nil expr)
    [((2 : reg), EVar 32)] [rsp] [argcN; Z_to_bv 64 0] RA HRA.
  { (* [sb a0,0(a1)] at 0x11024 -> out[0], in the writable page *)
    apply source_store_ok; u_norm; lia. }
  { (* [sd ra,8(sp)] at 0x1101c -> the RLIMIT_STACK window *)
    solve_store_ok. }
  { (* [lw a5,8(a5)] at 0x11004 -> modulus_base = 0, read out of .sbss *)
    replace (Z_to_bv 64 77832) with (0x13008 : word) by bveq;
    exists [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; split;
      [ erewrite rdn_ext;
        [ apply srom_zero4
        | imm_norm; lia
        | intros x Hx; revert Hx; imm_norm; intros Hx;
          eapply wrap_mem_below; [exact Hlau | rewrite stack_max_size_val; lia] ]
      | reflexivity ]. }
  { (* [sd a2,0(t1)] at 0x11064 -> musl's [__environ] slot at 0x13010 *)
    apply source_store_ok; u_norm; lia. }
  { (* [ld a0,0(sp)] at 0x1104c -> argc, out of the initial stack image *)
    replace (Z_to_bv 64 (bv_unsigned rsp + 0)) with rsp
      by (apply bv_eq; u_norm; lia);
    exists (word_le8 argcN); split;
      [ rewrite rdn_wrap_stack_above by lia;
        apply read_argc; apply source_bsb_nw
      | apply bytes_le_n_to_le_8 ]. }
  (* The digit the [sb] left in the log, in the spec's spelling. *)
  rewrite (stored_digit_val ltac:(lia)),
          N_to_le_bytes_1_small, (stored_digit _ Hrem).

  (* ---------------- musl write ---------------- *)
  (* 0x11098..0x110d4 -- musl's [write] wrapper, [__syscall_cp], the write
     [ecall] and [__syscall_ret]'s not-taken errno branch -- used to be
     ~195 lines of hand-stepped chain here.  That code is
     position-independent and byte-identical in every example, so it is
     proved ONCE over an abstract load address in [Common/MuslCall.v] and
     instantiated at this binary's 0x11098 in [modprint_ns_hoare.v]. *)
  assert (Hs24 : at_ (Z_to_bv 64 (bv_unsigned rsp - 16)) (-8)
                 = Z_to_bv 64 (bv_unsigned rsp - 24))
    by (unfold at_; u_norm; f_equal; lia).
  eapply (modprint_write_call vt _ _ (Z_to_bv 64 (bv_unsigned rsp - 16))
            (0x13000 : word));
    rewrite ?Hs24.
  (* The executor -> triple SEAM: the summary's precondition is four
     register values and they are read straight out of the block's exit
     register file.  No glue lemma; [sym_regs] is the same tactic the
     symbolic layer uses everywhere else. *)
  - (* ra: main's return point *) sym_regs HRA; sym_close.
  - (* sp *) sym_regs HRA; sym_close.
  - (* a0 = 1 (stdout) *) sym_regs HRA; sym_close.
  - (* a1 = out *) sym_regs HRA; sym_close.
  - (* a2 = 2 *) sym_regs HRA; sym_close.
  - (* the wrapper's own [ra] spill slot is storable *) solve_store_ok.
  - (* ... and does not wrap *) u_norm; lia.
  - (* the two buffer bytes: out[0] from the [sb], out[1] from the image *)
    apply (rdn_app (source_segs ++ vt) _ 1%nat 1%nat _
             [Z_to_bv 8 (48 + Z.of_nat (length (in_argv inp)) mod 7)] [nl]).
    + (* out[0]: the stored digit (skip write's later ra save) *)
      rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
      apply (rdn_wbytes_hit (source_segs ++ vt)
               [Z_to_bv 8 (48 + Z.of_nat (length (in_argv inp)) mod 7)]).
      cbn [length];
        match goal with |- (bv_unsigned ?a + _ <= _)%Z =>
          pose proof (u64_range a) end; lia.
    + (* out[1]: the newline, straight from the image *)
      match goal with |- rdn _ _ ?a _ = _ =>
        replace a with (0x13001 : word) by bveq end.
      rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
      rewrite rdn_wbytes_disjoint by (cbn [length]; imm_norm; u_norm; lia).
      rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
      rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
      erewrite rdn_ext;
        [ apply srom_nl
        | imm_norm; lia
        | intros x Hx; revert Hx; imm_norm; intros Hx;
          eapply wrap_mem_below; [exact Hlau | rewrite stack_max_size_val; lia] ].
  - (* the buffer range passes [access_ok]: a link-time address *)
    vm_compute. reflexivity.
  - (* back from [write], at 0x11034 with sp and ra restored *)
    (* ---------------- back in main + crt exit: 0x11034 .. 0x11070 ------
       SIX instructions in ONE reflective block, across the summary
       boundary.  The triple -> executor SEAM: the summary hands back an
       OPAQUE register file, and the two things this block needs of it
       are exactly the two things the summary's postcondition states --
       [sp] (pinned in as the frame base) and, through the reload, [ra].

       This stretch used to be a [sym_block] here, in this goal.  It is
       now [source_main_epilogue] above -- the SAME block, executed by
       the same executor, but proved standalone against an abstract
       register file, memory and frame base -- and all that is left at
       the call site is naming its three hypotheses and consuming its
       [msteps] with [sym_chain].  Nothing downstream changed: the
       [ecall] tail below is character-for-character what it was, except
       that its two register facts are now read off the lemma's
       conclusion instead of out of a block-local [regs_ok]. *)
    intros regs' n Hn1 Hn2 R1 R2 R10.
    match goal with
    | |- to_wexit _ (mkst _ _ ?m _) _ _ =>
        assert (HE : exists R,
                   getr R 10 = Z_to_bv 64 0
                /\ getr R 17 = Z_to_bv 64 93
                /\ msteps (source_segs ++ vt)
                     (mkst regs' (Z_to_bv 64 0x11034) m (seg_rom (source_segs ++ vt)))
                     (mkst R (Z_to_bv 64 0x11070) m (seg_rom (source_segs ++ vt))))
    end.
    { apply (source_main_epilogue vt regs' _ _ (Z_to_bv 64 (bv_unsigned rsp - 16)));
      [ (* the frame base: the summary restored the caller's [sp] *)
        exact R2
      | (* the frame does not wrap *) u_norm; lia
      | (* [ld ra,8(sp)] -> _start's return address, out of main's frame:
           past the wrapper's own [ra] spill and past the digit byte *)
        replace (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 16)))
          with (bv_unsigned rsp - 16)%Z by (u_norm; lia);
        replace (bv_unsigned rsp - 16 + 8)%Z with (bv_unsigned rsp - 8)%Z by lia;
        eexists; split;
          [ rewrite !rdn_wbytes_disjoint
              by (cbn [length]; rewrite ?length_N_to_le_bytes;
                  imm_norm; u_norm; lia);
            rewrite rdn_wbytes_hit8 by (u_norm; lia); reflexivity
          | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ] ]. }
    destruct HE as (RB & HB10 & HB17 & Hms).
    sym_chain Hms.
    (* ---------------- crt exit: the [ecall] at 0x11070 ---------------- *)
    eapply tw_step;
      [ reflexivity | apply (step_ecall _ _ _ _ _ _ (fetch_word_app _ _ _ _ SF_11070) eq_refl) | ].
    apply tw_exit_coden.
    + rewrite HB17. vm_compute. reflexivity.
    + rewrite <- getr_nz by reg_neq_tac. exact HB10.
    + u_norm; lia.
Qed.

End SourceProof.