(** * modprint_ns — REFLECTIVE symbolic execution WITH MEMORY.

    EXPLORATION / PROTOTYPE (see [Common/SymExec.v], [Common/Footprint.v]).

    [modprint_ns_symdemo.v] compares the reflective and tactic routes on
    a 7-instruction ALU-only block.  This file does the thing that block
    could not: it runs the executor over the memory-containing part of
    the real proof.

    BLOCK 1 — the whole pre-syscall execution, 41 instructions from the
    crt entry at 0x11044 to the [ecall] at 0x11120:

      _start  0x11044..0x11068   auipc/addi/**ld a0,0(sp)**/addi/slli/
                                 add/addi/addi/**sd a2,0(t1)**/jal
      main    0x11000..0x11030   lui/**lw a5,8(a5)**/lui/addi/addiw/remu/
                                 li/**sd ra,8(sp)**/addiw/**sb a0,0(a1)**/
                                 addi/li/jal
      write   0x11098..0x110bc   addi/6 x li-mv/**sd ra,8(sp)**/jal
      cp      0x11128, 0x11104..0x1111c  j / 7 x li

    That is 2 loads and 4 stores across THREE different bases: the ASLR
    stack ([sp], symbolic), musl's [__environ] slot at 0x13010 and the
    output buffer at 0x13000 (both absolute).  In the tactic proof
    ([modprint_ns_source.v:88-373]) this span is ~285 lines.

    Note what the executor does NOT need a side condition for: the
    [lw a5,8(a5)] at 0x11004 reads 0x13008 with the [sd] to 0x13010
    already in the log.  Same base, offsets 0x13008+4 <= 0x13010, so the
    skip is decided by [Z] arithmetic and costs nothing.  The tactic
    proof pays a [rdn_wbytes_below] with a [length]/[imm_norm]/[u_norm]/
    [lia] script for exactly that step.

    BLOCK 2 — the return path at 0x11034, which RELOADS a slot the log
    wrote.  [ld ra,8(sp)] at [sp-8] has to look past the [sd] at [sp-24]
    (same base, disjoint by arithmetic — free) and the [sb] at 0x13000
    (DIFFERENT base — one [SCDisjoint] obligation), and then hits.
    Because the hit gives [ra] as a literal, the [ret] two instructions
    later resolves to a concrete pc and the executor runs on through the
    crt exit sequence to the [ecall] at 0x11070. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import
  ExitSim PropExec CatExec CatSim SeqExec MmapSim NumPrint StepTac StreamSim
  StoreOk Footprint SymExec.
From LinuxProcessSemantics.Common Require ArgvEnv.
From LinuxProcessSemantics.Examples.modprint_ns Require Import
  modprint_ns_code modprint_ns_defs SourceMemImage TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The blocks' states carry the FP state of process entry; no
    instruction here touches it. *)
#[local] Instance modprint_ns_memdemo_fx : FPState := fx0.

(* ========================================================================= *)
(* BLOCK 1: 0x11044 .. 0x11120, over the real initial process image          *)
(* ========================================================================= *)

Section Block1.

Variable inp : ProcInput.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hvl : valid_launch inp.

Variable rsp rbrk rmb : word.

(** The entry stack draw this run was started with
    ([Run.ExecEntry]'s [en_draw]): the 16 AT_RANDOM bytes the kernel
    picks afresh at every [execve], and the stack VMA's end
    [StackLayout.ed_top].  This proof may assume NOTHING about either
    beyond the launch conjunct below, exactly as it may assume nothing
    about where the stack landed. *)
Variable rrnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned rsp)%Z.
Hypothesis Hsp_hi : (bv_unsigned rsp <= sp_window_hi)%Z.
(** The launch conjunct of [Run.valid_entry_va] ([create_elf_tables] and
    [setup_arg_pages], fs/binfmt_elf.c and fs/exec.c, Linux v6.18.46,
    commit 1f99e9ab748f): with [Hvl] it bounds the entry block and
    places the stack-store window. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry rsp rbrk rmb rrnd) inp.

Variable rom : word -> option byte.
Variable regs : bvmap 5 word.
Hypothesis Hsp : getr regs 2 = rsp.

Lemma dsp_lo : (0x7fff80000000 <= bv_unsigned rsp)%Z.
Proof. apply (ArgvEnv.sp_lo_num rsp); assumption. Qed.
Lemma dsp_hi : (bv_unsigned rsp <= 0x800000000000)%Z.
Proof. apply (ArgvEnv.sp_hi_num rsp); assumption. Qed.

(** The base memory: the initial process image.  Everything the block
    stores lands in the symbolic log ON TOP of this; every side
    condition is stated against THIS memory, never against a
    partially-built [wbytes] chain. *)
Definition dmem : word -> option byte :=
  wrap_mem inp rmb source_phdrs (Z_to_bv 64 0x11044) rsp rrnd.

Lemma dbsb_nw :
  (bv_unsigned rsp
     + Z.of_nat (length (entry_stack_image inp rmb source_phdrs (Z_to_bv 64 0x11044)
                           rsp rrnd)) < 2^64)%Z.
Proof.
  apply (ArgvEnv.bsb_nw Sv48 inp rmb source_phdrs (Z_to_bv 64 0x11044) rsp rbrk rrnd);
    assumption.
Qed.

(** Registers 0..31 are the entry register file; 32 and 33 are the two
    words this run reads out of the base memory — [argc] at [sp] and
    [modulus_base] at 0x13008.  Nothing else about memory is assumed. *)
Definition dE : env := Eplus regs [ArgvEnv.argcN inp; Z_to_bv 64 0].

Lemma dE_sp : bdenot dE (SBVar 2) = rsp.
Proof.
  unfold dE, Eplus, bdenot. cbn [Nat.ltb Nat.leb].
  rewrite <- Hsp; f_equal; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma dE_lit : bdenot dE SBLit = Z_to_bv 64 0.
Proof. reflexivity. Qed.

Definition mss_entry : sym_state := SS 0x11044 sr_id [] 32.

Definition mss_exit : sym_state :=
  Eval vm_compute in fst (sym_exec source_segs 60 [] [] mss_entry []).
Definition mscs : list sidecond :=
  Eval vm_compute in snd (sym_exec source_segs 60 [] [] mss_entry []).

(** The twelve side conditions, in the order the executor emitted them.
    Six are address arithmetic ([SCFlat], one [lia] each), four are
    store legality against the INITIAL memory (the existing per-image
    probes, with no overlay peeling), two are reads out of the image. *)
Lemma mscs_ok : scs_denot source_segs dmem dE mscs.
Proof.
  pose proof dsp_lo. pose proof dsp_hi.
  unfold mscs, scs_denot.
  repeat (apply Forall_cons; [cbn [sc_denot]|]); [| | | | | | | | | | | |apply Forall_nil].
  (* sd ra,8(sp) at 0x110b8 : sp-24 *)
  - unfold sc_flat; cbn [a_base a_off]; rewrite dE_sp; repeat split; lia.
  - unfold adenot, v_addi; cbn [a_base a_off]; rewrite dE_sp.
    unfold dmem; solve_store_ok.
  (* sb a0,0(a1) at 0x11024 : 0x13000 *)
  - unfold sc_flat; cbn [a_base a_off]; rewrite dE_lit, u_Z_to_bv64_0;
      repeat split; lia.
  - unfold adenot; cbn [a_base a_off]; rewrite dE_lit.
    match goal with |- context [ v_addi ?x ?k ] =>
      replace (v_addi x k) with (0x13000 : word) by bveq end.
    rewrite <- (app_nil_r source_segs). apply source_store_ok; imm_norm; lia.
  (* sd ra,8(sp) at 0x1101c : sp-8 *)
  - unfold sc_flat; cbn [a_base a_off]; rewrite dE_sp; repeat split; lia.
  - unfold adenot, v_addi; cbn [a_base a_off]; rewrite dE_sp.
    unfold dmem; solve_store_ok.
  (* lw a5,8(a5) at 0x11004 : 0x13008, read out of the image *)
  - unfold sc_flat; cbn [a_base a_off]; rewrite dE_lit, u_Z_to_bv64_0;
      repeat split; lia.
  - unfold adenot; cbn [a_base a_off]; rewrite dE_lit.
    match goal with |- context [ v_addi ?x ?k ] =>
      replace (v_addi x k) with (0x13008 : word) by bveq end.
    exists [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]. split.
    + unfold dmem. erewrite rdn_ext;
        [ rewrite <- (app_nil_r source_segs); apply srom_zero4
        | imm_norm; lia
        | intros x Hx; revert Hx; imm_norm; intros Hx;
          eapply wrap_mem_below; [exact Hlau | rewrite stack_max_size_val; lia] ].
    + reflexivity.
  (* sd a2,0(t1) at 0x11064 : 0x13010 *)
  - unfold sc_flat; cbn [a_base a_off]; rewrite dE_lit, u_Z_to_bv64_0;
      repeat split; lia.
  - unfold adenot; cbn [a_base a_off]; rewrite dE_lit.
    match goal with |- context [ v_addi ?x ?k ] =>
      replace (v_addi x k) with (0x13010 : word) by bveq end.
    rewrite <- (app_nil_r source_segs). apply source_store_ok; imm_norm; lia.
  (* ld a0,0(sp) at 0x1104c : argc, read out of the initial stack image *)
  - unfold sc_flat; cbn [a_base a_off]; rewrite dE_sp; repeat split; lia.
  - unfold adenot; cbn [a_base a_off]; rewrite dE_sp, v_addi_0.
    exists (word_le8 (ArgvEnv.argcN inp)). split.
    + unfold dmem. rewrite rdn_wrap_stack_above by lia.
      apply read_argc. exact dbsb_nw.
    + apply bytes_le_n_to_le_8.
Qed.

(** 41 instructions — 35 ALU/control, 2 loads, 4 stores — in ONE
    application of [sym_exec_sound]. *)
Lemma block1 :
  exists regs',
    msteps source_segs (mkst regs (Z_to_bv 64 0x11044) dmem rom)
                       (mkst regs' (Z_to_bv 64 0x11120)
                             (mem_denot dE dmem (s_log mss_exit)) rom)
    /\ getr regs' 17 = Z_to_bv 64 64
    /\ getr regs' 10 = Z_to_bv 64 1
    /\ getr regs' 11 = Z_to_bv 64 0x13000
    /\ getr regs' 12 = Z_to_bv 64 2.
Proof.
  Time (
  assert (Hst : st_ok dE dmem rom mss_entry
                  (mkst regs (Z_to_bv 64 0x11044) dmem rom))
    by (exists regs; split;
        [reflexivity | split; [apply regs_ok_Eplus | exact I]]);
  destruct (sym_exec_sound source_segs 60 [] [] mss_entry [] mss_exit mscs
              dE dmem rom _ ltac:(vm_compute; reflexivity) mscs_ok Hst)
    as (ms' & Hms & (regs' & -> & Hr' & _));
  exists regs'; split; [exact Hms|];
  repeat split; rewrite (Hr' _);
  repeat match goal with
  | |- context [sr_get ?a ?b] =>
      let v := eval vm_compute in (sr_get a b) in change (sr_get a b) with v
  end; reflexivity).
Qed.

End Block1.

(* ========================================================================= *)
(* BLOCK 2: 0x11034 .. 0x11070 — a reload that hits the log                  *)
(* ========================================================================= *)

Section Block2.

Variable base rom : word -> option byte.
Variable regs : bvmap 5 word.

(** The frame base.  It is a SYMBOLIC value carried in the valuation at
    index 32, not the concrete [sp] register: the register holds
    [rsp - 16] at this point, and the log was written at [rsp - 8] and
    [rsp - 24] from other frames.  This is exactly the shape a heap
    pointer or an argv-derived pointer has. *)
Variable rsp : word.
Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned rsp)%Z.
Hypothesis Hhi : (bv_unsigned rsp <= 0x800000000000)%Z.
Hypothesis Hsp : getr regs 2 = Z_to_bv 64 (bv_unsigned rsp - 16).

(** The digit byte and the [__environ] pointer that block 1 stored;
    opaque here. *)
Variables dig envp : word.

Definition E2 : env := Eplus regs [rsp; dig; envp].

(** The store log block 1 left behind, most recent first. *)
Definition log2 : list sentry :=
  [ SE (SA (SBVar 32) (-24)) 8 (ELit 0x11034)
  ; SE (SA SBLit 0x13000) 1 (EVar 33)
  ; SE (SA (SBVar 32) (-8)) 8 (ELit 0x1106c)
  ; SE (SA SBLit 0x13010) 8 (EVar 34) ].

Definition mss2_entry : sym_state :=
  SS 0x11034 (sr_upd sr_id (ridx 2) (EAlu ALU_ADD (EVar 32) (ELit (-16))))
     log2 35.

Definition mss2_exit : sym_state :=
  Eval vm_compute in fst (sym_exec source_segs 10 [] [] mss2_entry []).
Definition mscs2 : list sidecond :=
  Eval vm_compute in snd (sym_exec source_segs 10 [] [] mss2_entry []).

Lemma E2_sp : bdenot E2 (SBVar 32) = rsp.
Proof. reflexivity. Qed.

Lemma E2_lit : bdenot E2 SBLit = Z_to_bv 64 0.
Proof. reflexivity. Qed.

Lemma log2_flat : log_flat E2 log2.
Proof.
  unfold log2, log_flat. cbn [a_base a_off].
  rewrite E2_sp, E2_lit, u_Z_to_bv64_0. repeat split; lia.
Qed.

(** TWO side conditions for the whole block: the reload's address is
    flat, and it does not alias the byte written into the output buffer.
    The other two log entries are dismissed by [Z] arithmetic. *)
Lemma mscs2_ok : scs_denot source_segs base E2 mscs2.
Proof.
  unfold mscs2, scs_denot.
  repeat (apply Forall_cons; [cbn [sc_denot]|]); [| |apply Forall_nil].
  - unfold sc_flat; cbn [a_base a_off]; rewrite E2_sp; repeat split; lia.
  - unfold adenot, v_addi; cbn [a_base a_off];
      rewrite E2_sp, E2_lit, u_Z_to_bv64_0.
    u_norm; repeat split; lia.
Qed.

Lemma block2 :
  exists regs',
    msteps source_segs
      (mkst regs (Z_to_bv 64 0x11034) (mem_denot E2 base log2) rom)
      (mkst regs' (Z_to_bv 64 0x11070) (mem_denot E2 base log2) rom)
    /\ getr regs' 17 = Z_to_bv 64 93
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x1106c.
Proof.
  Time (
  assert (Hst : st_ok E2 base rom mss2_entry
                  (mkst regs (Z_to_bv 64 0x11034) (mem_denot E2 base log2) rom))
    by (exists regs; split;
        [reflexivity
        | split; [| exact log2_flat];
          apply regs_ok_pin; [apply regs_ok_Eplus|];
          cbn [edenot E2 Eplus]; rewrite Hsp, alu_add, v_add_lit;
          f_equal; lia]);
  destruct (sym_exec_sound source_segs 10 [] [] mss2_entry [] mss2_exit mscs2
              E2 base rom _ ltac:(vm_compute; reflexivity) mscs2_ok Hst)
    as (ms' & Hms & (regs' & -> & Hr' & _));
  exists regs'; split; [exact Hms|];
  repeat split; rewrite (Hr' _);
  repeat match goal with
  | |- context [sr_get ?a ?b] =>
      let v := eval vm_compute in (sr_get a b) in change (sr_get a b) with v
  end; reflexivity).
Qed.

End Block2.

(** No axioms beyond the ones the memory images already use (Rocq's
    primitive ints/strings, which the [.hex] snapshots are built on). *)
Print Assumptions block1.
Print Assumptions block2.
