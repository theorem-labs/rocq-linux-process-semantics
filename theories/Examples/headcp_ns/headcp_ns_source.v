(** * headcp-ns, source binary (musl-gcc -Os, raw_syscall opens, libc
    read/write/close wrappers).

    PROOF-SIDE FILE (not part of the trusted specification).

    _start (0x11100) sets gp, stores the envp pointer into musl's environ
    slot at 0x13000, and calls main (0x11000).  main issues the two openats
    through the crt's raw_syscall (0x11134, register-only), then a SINGLE
    read(fdin, buf, 128) and a SINGLE write(fdout, buf, r) through the same
    raw_syscall, then closes both fds through musl's [close] and returns 0
    through the epilogue into _start's exit tail.  The 128-byte buffer lives
    at 0x13008 (gp - 2040).

    Deliverables, over the run's segment list [source_segs ++ vt]:
    - [source_wexit_lt3] : argc < 3 -> to_wexit [] 2 (CatSim glue);
    - [source_ge3]       : argc >= 3 -> to_fout [hc_outcomes], whatever
      each operand's open answers ([FileSimWalk.tfo_open_operand_rec]),
      and on both descriptors whatever the first one is (a regular file,
      a folder, /dev/null, /dev/urandom) and the second one is (a regular
      file, /dev/null, /dev/urandom).

    Sp-relative addresses/register values are in the canonical
    [Z_to_bv 64 (bv_unsigned rsp - k)] form, pc and rodata
    constants in numeral-literal form, the chunk length as
    [len_word chunk]; all range bookkeeping is in [Z] over
    [bv_unsigned].

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Sys.Prelude.
From LinuxProcessSemantics.Common Require Import SimInv ExitSim PropExec CatExec CatSim SeqExec StepTac StreamExec StreamSim ErrEscape FileSim ListFacts StoreOk SymExec SymTac RunSegmentsLift FileSimWalk.
From LinuxProcessSemantics.Examples.headcp_ns Require Import headcp_ns_code headcp_ns_defs.
From LinuxProcessSemantics.Examples.headcp_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.headcp_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them. *)
#[local] Instance headcp_ns_source_fx : FPState := fx0.

Definition sbuf : word := 0x13008.

Lemma u_sbuf : bv_unsigned sbuf = 0x13008%Z.
Proof. reflexivity. Qed.

(** Normalize the pc of a [to_fout] goal's head state to its literal
    form (FileSim continuation states arrive with [v_addi pc 4]). *)
Ltac fnorm_pc :=
  try lazymatch goal with
  | |- to_fout _ (mkst _ ?p _ _) _ _ => wlit p
  end.

(** The register-shift spelling the reflective executor leaves behind for
    an [slli rd,rs,3]: [SymExec] models the shift as [v_sll] against a
    literal shift amount, where the tactic layer's lemmas are stated
    against the immediate form [v_slli]. *)
Lemma v_sll_3 : forall x : word, v_sll x (Z_to_bv 64 3) = v_slli x 3.
Proof.
  intro x. unfold v_sll, v_slli.
  replace (bv_unsigned (Z_to_bv 64 3) mod 64)%Z with 3%Z
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma fd4_ne_fd3 : Z_to_bv 64 4 <> Z_to_bv 64 3.
Proof. intro Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc. Qed.

Section SourceProof.

(** The segments the run appends after the image's own: the vDSO pair
    ([Run.run_segments]).  Nothing below reads them. *)
Variable vt : list Segment.

Variable inp : ProcInput.
Local Abbreviation av := (in_argv inp).
Local Abbreviation ev := (in_envp inp).
Local Abbreviation fs0 := (in_fs inp).
Hypothesis Hva : valid_argv av.
Hypothesis Hvl : valid_launch inp.

(** The initial stack pointer, the program break and the mmap base are
    QUANTIFIED (ASLR): the whole section is generic over them. *)
Variable rsp rbrk rmb : word.

(** The entry stack draw this run was started with
    ([Run.ExecEntry]'s [en_draw]): the 16 AT_RANDOM bytes the kernel
    picks afresh at every [execve], and the stack VMA's end
    [StackLayout.ed_top].  This proof may assume NOTHING about either
    beyond the launch conjunct below. *)
Variable rrnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned rsp)%Z.
Hypothesis Hsp_hi : (bv_unsigned rsp <= sp_window_hi)%Z.

(** The fifth conjunct of [Run.valid_entry_va]: this placement is one a
    Linux launch can give ([create_elf_tables] and [setup_arg_pages],
    fs/binfmt_elf.c and fs/exec.c, Linux v6.18.46, commit
    1f99e9ab748f).  With [Hvl] it bounds the entry block
    ([StepTac.bsb_bound]), places argv's strings, and places the
    stack-store window ([StoreOk.store_ok_wrap_window_valid]). *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry rsp rbrk rmb rrnd) inp.

(** The run's segment list, its read-only backing, and a fetch fact of
    the image carried to it. *)
Local Abbreviation rsegs := (source_segs ++ vt).
Local Abbreviation rrom := (seg_rom (source_segs ++ vt)).
Local Abbreviation SFv F := (fetch_word_app _ vt _ _ F).

(** The two operands. *)
Local Abbreviation src := (nth 1 (in_argv inp) []).
Local Abbreviation dst := (nth 2 (in_argv inp) []).

Lemma rsp_lo_num : (0x7fff80000000 <= bv_unsigned rsp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma rsp_hi_num : (bv_unsigned rsp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Definition argcN : word := len_word av.
Definition wmem : word -> option byte :=
  wrap_mem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x11100)) rsp rrnd.

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
Proof.
  pose proof (valid_argv_len av Hva).
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

(** The pointer _start stores into musl's [environ] slot at 0x13000. *)
Definition envp_ptr : word :=
  Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat (length av) + 8).

Lemma envp_ptr_eq :
  v_addi (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli argcN 3)) 8 = envp_ptr.
Proof.
  pose proof rsp_hi_num. pose proof rsp_lo_num.
  pose proof (valid_argv_len av Hva) as Hlen.
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

(** Memory after _start's environ store. *)
Definition emem : word -> option byte :=
  wbytes wmem (0x13000 : word) (word_to_le_bytes 8 envp_ptr).

(** [envp_ptr_eq] again, in the spelling the reflective executor's
    [add]/[slli] pair leaves behind. *)
Lemma envp_ptr_eq_sym :
  Z_to_bv 64 (bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
                                         (v_sll argcN (Z_to_bv 64 3))) + 8)
  = envp_ptr.
Proof.
  rewrite alu_add, v_sll_3. exact envp_ptr_eq.
Qed.

(** Memory after main()'s prologue: the three callee-save slots below the
    initial sp, in execution order.  All stored values are constants of
    the initial state (s* = 0, main's ra = 0x1112c). *)
Definition fmem : word -> option byte :=
  wbytes (wbytes (wbytes emem
    (Z_to_bv 64 (bv_unsigned rsp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))   (* sd s0,32(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))   (* sd s1,24(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 8))  (word_to_le_bytes 8 (0x1112c : word)). (* sd ra,40(sp) *)

Lemma grows_fmem : mem_grows wmem fmem.
Proof.
  unfold fmem, emem.
  repeat (eapply mem_grows_trans; [ | apply wbytes_grows ]).
  apply mem_grows_refl.
Qed.

Lemma rdn_emem_above : forall (a : word) n,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn rsegs emem a n = rdn rsegs wmem a n.
Proof.
  intros a n Ha Hn. pose proof rsp_lo_num. unfold emem.
  rewrite rdn_wbytes_disjoint
    by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
  reflexivity.
Qed.

Lemma rdn_fmem_above : forall (a : word) n,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn rsegs fmem a n = rdn rsegs wmem a n.
Proof.
  intros a n Ha Hn. pose proof rsp_lo_num. pose proof rsp_hi_num. unfold fmem.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; u_norm; lia)).
  apply rdn_emem_above; assumption.
Qed.

Lemma rdn_wmem_stack : forall (a : word) n,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn rsegs wmem a n
  = rdn rsegs (stack_to_mem rsp (entry_stack_image inp rmb source_phdrs
                                   (Z_to_bv 64 (Z.of_N 0x11100)) rsp rrnd)) a n.
Proof. intros a n Ha Hn. unfold wmem. apply rdn_wrap_stack_above; assumption. Qed.

Lemma read_argc_w :
  rdn rsegs wmem rsp 8%nat = Some (word_le8 argcN).
Proof.
  pose proof rsp_hi_num.
  rewrite rdn_wmem_stack by lia.
  apply read_argc. apply source_bsb_nw.
Qed.

(** Frame-slot reads out of [fmem]. *)
Local Ltac fmem_slot :=
  unfold fmem;
  repeat first
    [ rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; u_norm; lia)
    | rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; u_norm; lia) ];
  apply rdn_wbytes_hit8; u_norm; lia.

Lemma fmem_ra_slot :
  rdn rsegs fmem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
  = Some (word_to_le_bytes 8 (0x1112c : word)).
Proof. pose proof rsp_lo_num. pose proof rsp_hi_num. fmem_slot. Qed.

Lemma fmem_s0_slot :
  rdn rsegs fmem (Z_to_bv 64 (bv_unsigned rsp - 16)) 8%nat
  = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. pose proof rsp_lo_num. pose proof rsp_hi_num. fmem_slot. Qed.

Lemma fmem_s1_slot :
  rdn rsegs fmem (Z_to_bv 64 (bv_unsigned rsp - 24)) 8%nat
  = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. pose proof rsp_lo_num. pose proof rsp_hi_num. fmem_slot. Qed.

Definition psrc : word := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1.
Definition pdst : word := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 2.

(* ================================================================= *)
(* Local step tactics                                                *)
(* ================================================================= *)

(** Store-permission side goals against the source image. *)
Local Ltac s_ro :=
  first [ apply source_store_ok; imm_norm; u_norm; lia | solve_store_ok_inv ].

(** A reflective block's ENTRY pin, discharged from the caller's
    [reg_get regs r = v] hypothesis [H]. *)
Local Ltac s_pin H :=
  rewrite getr_nz by reg_neq_tac; rewrite H;
  first [ reflexivity | bveq ].

(** A fact about a reflective block's EXIT register file, read back
    through its [regs_ok] [H] and closed against the caller's
    entry-state hypotheses. *)
Local Ltac s_out H :=
  sym_regs H; rewrite ?getr_nz by reg_neq_tac;
  first [ assumption | sym_close | (vm_compute; reflexivity) ].

(** Register values that are constants of the current chain. *)
Local Ltac vconst :=
  getr_resolve; regupd_resolve;
  first [ apply v_addi_0 | reflexivity | bveq ].

(** sp-relative value/address whose base register is IN the chain. *)
Local Ltac spn :=
  getr_resolve; regupd_resolve; sp_norm;
  first [ reflexivity | f_equal; lia ].

(* ================================================================= *)
(* The shared epilogue + exit tail                                   *)
(* ================================================================= *)

(** From main's epilogue at 0x110e4: reload the three callee-save slots,
    pop the frame, return into _start's exit tail. *)
Lemma source_exit_tail : forall regs mem model code fsv,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 10 = code -> (bv_unsigned code < 256)%Z ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
    = Some (word_to_le_bytes 8 (0x1112c : word)) ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 16)) 8%nat
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 24)) 8%nat
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs 0x110e4 mem rrom) model
    (fun o => o = (code, fsv)).
Proof.
  intros regs mem model code fsv H2 H10 Hc Hra Hs0 Hs1 Hfs.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  (* 0x110e4 .. 0x11130 — 7 instructions in ONE reflective block: the
     three callee-save reloads, the frame pop, the [ret] into _start's
     exit tail and the exit(93) load. *)
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 69860) mem rrom) 8%nat
    (@nil bool) [ELit 0x1112c; ELit 0; ELit 0] [((2 : reg), EVar 32)]
    [Z_to_bv 64 (bv_unsigned rsp - 48)] (@nil word) R HR Hms.
  { exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ exact Hs1 | rewrite bytes_le_to_Z_8; reflexivity ]. }
  { exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ exact Hs0 | rewrite bytes_le_to_Z_8; reflexivity ]. }
  { exists (word_to_le_bytes 8 (0x1112c : word)); split;
      [ exact Hra | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]. }
  { exact H2. }
  eapply tfo_msteps.
  { eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_11130) eq_refl)
      | apply mst_refl ]. }
  apply tfo_exit_rec.
  - sym_regs HR; vm_compute; reflexivity.
  - sym_regs HR; exact H10.
  - exact Hc.
  - exact Hfs.
Qed.

(* ================================================================= *)
(* main's read / write / close chain, as shared reflective blocks     *)
(* ================================================================= *)

(** The spill of the read count into main's 8(sp) slot, made across the
    write call. *)
Definition spill_at (mem : word -> option byte) (cnt : word)
    : word -> option byte :=
  wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 40)) (word_to_le_bytes 8 cnt).

(** A memory with the chain's stores on top of one that grew from
    [wmem]. *)
Local Ltac hc_grows Hg :=
  unfold spill_at;
  repeat (eapply mem_grows_trans; [ | apply wbytes_grows ]);
  exact Hg.

(** Peel the chain's overlays (the buffer write, the count spill and the
    two [close] [ra] spills) off a frame-slot read. *)
Local Ltac hc_peel :=
  unfold spill_at;
  repeat first
    [ rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; u_norm; lia)
    | rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; u_norm; lia) ].

Lemma rdn_spill_cnt : forall mem cnt,
  rdn rsegs (spill_at mem cnt) (Z_to_bv 64 (bv_unsigned rsp - 40)) 8%nat
    = Some (word_to_le_bytes 8 cnt).
Proof.
  intros mem cnt. pose proof rsp_lo_num. pose proof rsp_hi_num.
  unfold spill_at. apply rdn_wbytes_hit8; u_norm; lia.
Qed.

(** From raw_syscall's [ret] after the SECOND open to the read ecall:
    [mv s0,a0], the not-taken [bltz], the read() argument moves, the
    [jal] back into raw_syscall and its shuffles. *)
Lemma src_open2_to_read : forall regs mem fdin fdout spv,
  reg_get regs 1 = (0x11068 : word) ->
  reg_get regs 2 = spv ->
  reg_get regs 3 = (0x13800 : word) ->
  reg_get regs 9 = fdin ->
  reg_get regs 10 = fdout ->
  (bv_unsigned fdout < 2^31)%Z ->
  exists regs',
    bv_unsigned (getr regs' 17) = 63%Z /\
    reg_get regs' 10 = fdin /\
    reg_get regs' 11 = sbuf /\
    reg_get regs' 12 = Z_to_bv 64 128 /\
    reg_get regs' 1 = (0x11094 : word) /\
    reg_get regs' 2 = spv /\
    reg_get regs' 3 = (0x13800 : word) /\
    reg_get regs' 8 = fdout /\
    reg_get regs' 9 = fdin /\
    msteps rsegs (mkst regs (0x11154 : word) mem rrom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := (0x11150 : word);
         ms_svc_pending := Some (getr regs' 17); ms_resv := None;
         ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rrom |}.
Proof.
  intros regs mem fdin fdout spv H1 H2 H3 H9 H10 Hlt.
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 69972) mem rrom)
    20%nat [false] (@nil expr)
    [((1 : reg), ELit 0x11068); ((3 : reg), ELit 0x13800);
     ((9 : reg), EVar 32); ((10 : reg), EVar 33)]
    [fdin; fdout] (@nil word) R HR Hms.
  { apply c_lts_pos_0; lia. }
  { s_pin H1. }
  { s_pin H3. }
  { s_pin H9. }
  { s_pin H10. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
  10: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_11150) eq_refl)
      | apply mst_refl ]. }
  all: s_out HR.
Qed.

(** From raw_syscall's [ret] after the read to the write ecall:
    [mv a3,a0], the not-taken [bltz], the write() argument moves, the
    spill of the count to 8(sp), the [jal] back into raw_syscall and its
    shuffles. *)
Lemma src_read_to_write : forall regs mem fdin fdout cnt,
  reg_get regs 1 = (0x11094 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 3 = (0x13800 : word) ->
  reg_get regs 8 = fdout ->
  reg_get regs 9 = fdin ->
  reg_get regs 10 = cnt ->
  (bv_unsigned cnt <= 128)%Z ->
  mem_grows wmem mem ->
  exists regs',
    bv_unsigned (getr regs' 17) = 64%Z /\
    reg_get regs' 10 = fdout /\
    reg_get regs' 11 = sbuf /\
    reg_get regs' 12 = cnt /\
    reg_get regs' 1 = (0x110c0 : word) /\
    reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs' 8 = fdout /\
    reg_get regs' 9 = fdin /\
    msteps rsegs (mkst regs (0x11154 : word) mem rrom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := (0x11150 : word);
         ms_svc_pending := Some (getr regs' 17); ms_resv := None;
         ms_fcsr := fp_csr; ms_mem := spill_at mem cnt; ms_rom := rrom |}.
Proof.
  intros regs mem fdin fdout cnt H1 H2 H3 H8 H9 H10 Hc Hg.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 69972) mem rrom)
    20%nat [false] (@nil expr)
    [((1 : reg), ELit 0x11094); ((2 : reg), EVar 32); ((3 : reg), ELit 0x13800);
     ((8 : reg), EVar 33); ((10 : reg), EVar 34)]
    [Z_to_bv 64 (bv_unsigned rsp - 48); fdout; cnt] (@nil word) R HR Hms.
  { store_ok_peel; eapply store_ok_mono; [ exact Hg | ]; solve_store_ok. }
  { apply c_lts_pos_0; lia. }
  { s_pin H1. }
  { s_pin H2. }
  { s_pin H3. }
  { s_pin H8. }
  { s_pin H10. }
  match type of Hms with msteps _ _ (mkst _ _ ?M _) => assert (HM : M = spill_at mem cnt) end.
  { unfold spill_at. sym_mem_norm. reflexivity. }
  rewrite HM in Hms. clear HM.
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  9: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_11150) eq_refl)
      | apply mst_refl ]. }
  all: s_out HR.
Qed.

(** From raw_syscall's [ret] after the write to the [sext.w a0,s1] that
    feeds the first [close]: the reload of the spilled count, the
    not-taken [bne] that compares it with the delivered count. *)
Lemma src_write_to_ret : forall regs mem fdin fdout cnt,
  reg_get regs 1 = (0x110c0 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 8 = fdout ->
  reg_get regs 9 = fdin ->
  reg_get regs 10 = cnt ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 40)) 8%nat
    = Some (word_to_le_bytes 8 cnt) ->
  exists regs',
    reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs' 8 = fdout /\
    reg_get regs' 9 = fdin /\
    msteps rsegs (mkst regs (0x11154 : word) mem rrom)
      (mkst regs' (0x110d0 : word) mem rrom).
Proof.
  intros regs mem fdin fdout cnt H1 H2 H8 H9 H10 Hrd.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 69972) mem rrom)
    5%nat [false] [EVar 35]
    [((1 : reg), ELit 0x110c0); ((2 : reg), EVar 32);
     ((9 : reg), EVar 33); ((10 : reg), EVar 34)]
    [Z_to_bv 64 (bv_unsigned rsp - 48); fdin; cnt] [cnt] R HR Hms.
  { apply negb_false_iff; apply c_eq_refl. }
  { exists (word_to_le_bytes 8 cnt); split;
      [ match goal with |- rdn _ _ ?ad _ = _ =>
          replace ad with (Z_to_bv 64 (bv_unsigned rsp - 40))
            by (apply bv_eq; u_norm; lia)
        end; exact Hrd
      | exact (bytes_le_to_Z_8 _) ]. }
  { s_pin H1. }
  { s_pin H2. }
  { s_pin H9. }
  { s_pin H10. }
  exists R.
  refine (conj _ (conj _ (conj _ _))).
  4: { eapply msteps_trans; [ exact Hms | ]. sym_pc_lit. apply mst_refl. }
  all: s_out HR.
Qed.

(** musl's [close] wrapper, entry (0x1115c) to the close ecall: the
    16-byte frame with its [ra] spill, the [jal]/[ret] through the empty
    [__aio_close], the __syscall_cp argument moves and shuffles.  Used by
    BOTH closes. *)
Lemma src_close_call : forall regs mem fdv raM s0v s1v,
  reg_get regs 1 = raM ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 8 = s0v ->
  reg_get regs 9 = s1v ->
  reg_get regs 10 = fdv ->
  mem_grows wmem mem ->
  exists regs',
    bv_unsigned (getr regs' 17) = 57%Z /\
    reg_get regs' 10 = fdv /\
    reg_get regs' 1 = (0x11188 : word) /\
    reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 64) /\
    reg_get regs' 8 = s0v /\
    reg_get regs' 9 = s1v /\
    msteps rsegs (mkst regs (0x1115c : word) mem rrom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := (0x11204 : word);
         ms_svc_pending := Some (getr regs' 17); ms_resv := None;
         ms_fcsr := fp_csr;
         ms_mem := wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 56))
                          (word_to_le_bytes 8 raM);
         ms_rom := rrom |}.
Proof.
  intros regs mem fdv raM s0v s1v H1 H2 H8 H9 H10 Hg.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 69980) mem rrom)
    21%nat (@nil bool) (@nil expr)
    [((1 : reg), EVar 32); ((2 : reg), EVar 33); ((10 : reg), EVar 34)]
    [raM; Z_to_bv 64 (bv_unsigned rsp - 48); fdv] (@nil word) R HR Hms.
  { store_ok_peel; eapply store_ok_mono; [ exact Hg | ]; solve_store_ok. }
  { s_pin H1. }
  { s_pin H2. }
  { s_pin H10. }
  match type of Hms with msteps _ _ (mkst _ _ ?M _) =>
    assert (HM : M = wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 56))
                             (word_to_le_bytes 8 raM))
  end.
  { sym_mem_norm. reflexivity. }
  rewrite HM in Hms. clear HM.
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  7: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_11204) eq_refl)
      | apply mst_refl ]. }
  all: s_out HR.
Qed.

(** The close tail: __syscall_cp_c's [ret], the not-taken -ENOSYS
    retry test, __syscall_ret's frameless success path, the [ra]
    reload and the frame pop.  The caller supplies the final [ret] to
    [raM]. *)
Lemma src_close_tail : forall regs mem raM s0v s1v,
  reg_get regs 1 = (0x11188 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ->
  reg_get regs 8 = s0v ->
  reg_get regs 9 = s1v ->
  reg_get regs 10 = Z_to_bv 64 0 ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8%nat
    = Some (word_to_le_bytes 8 raM) ->
  exists regs',
    reg_get regs' 1 = raM /\
    reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs' 8 = s0v /\
    reg_get regs' 9 = s1v /\
    reg_get regs' 10 = Z_to_bv 64 0 /\
    msteps rsegs (mkst regs (0x11208 : word) mem rrom)
      (mkst regs' (0x111a4 : word) mem rrom).
Proof.
  intros regs mem raM s0v s1v H1 H2 H8 H9 H10 Hrd.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 70152) mem rrom)
    12%nat [false; false] [EVar 33]
    [((1 : reg), ELit 0x11188); ((2 : reg), EVar 32); ((10 : reg), ELit 0)]
    [Z_to_bv 64 (bv_unsigned rsp - 64)] [raM] R HR Hms.
  { exists (word_to_le_bytes 8 raM); split;
      [ match goal with |- rdn _ _ ?ad _ = _ =>
          replace ad with (Z_to_bv 64 (bv_unsigned rsp - 56))
            by (apply bv_eq; u_norm; lia)
        end; exact Hrd
      | exact (bytes_le_to_Z_8 _) ]. }
  { s_pin H1. }
  { s_pin H2. }
  { s_pin H10. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  6: { eapply msteps_trans; [ exact Hms | ]. sym_pc_lit. apply mst_refl. }
  all: s_out HR.
Qed.

(* ================================================================= *)
(* argc >= 3: to the first openat                                    *)
(* ================================================================= *)

Section Ge3.

Hypothesis Hge3 : (3 <= length av)%nat.

Lemma psrc_bounds :
  (bv_unsigned rsp <= bv_unsigned psrc)%Z /\
  (bv_unsigned psrc + Z.of_nat (length src) + 1 < 2^64)%Z.
Proof. unfold psrc. exact (argv_ptr_bounds Sv48 inp rmb rsp rbrk rrnd 1 Hlau ltac:(lia)). Qed.

Lemma pdst_bounds :
  (bv_unsigned rsp <= bv_unsigned pdst)%Z /\
  (bv_unsigned pdst + Z.of_nat (length dst) + 1 < 2^64)%Z.
Proof. unfold pdst. exact (argv_ptr_bounds Sv48 inp rmb rsp rbrk rrnd 2 Hlau ltac:(lia)). Qed.

(** argv pointer slots at rsp+16 / rsp+24. *)
Lemma read_psrc_e :
  rdn rsegs emem (Z_to_bv 64 (bv_unsigned rsp + 16)) 8%nat
  = Some (word_le8 psrc).
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  replace (Z_to_bv 64 (bv_unsigned rsp + 16))
    with (rsp + nat_to_word (8 + 8 * 1))
    by (rewrite word_add_nat; f_equal; lia).
  rewrite rdn_emem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
  unfold psrc. apply read_argv_ptr_k; [lia | apply source_bsb_nw].
Qed.

Lemma read_pdst_f :
  rdn rsegs fmem (Z_to_bv 64 (bv_unsigned rsp + 24)) 8%nat
  = Some (word_le8 pdst).
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  replace (Z_to_bv 64 (bv_unsigned rsp + 24))
    with (rsp + nat_to_word (8 + 8 * 2))
    by (rewrite word_add_nat; f_equal; lia).
  rewrite rdn_fmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
  unfold pdst. apply read_argv_ptr_k; [lia | apply source_bsb_nw].
Qed.

(** The pathname fetch of each operand: the string, or [CstrTooLong]
    when it does not fit in PATH_MAX ([FileSimWalk.read_cstr_argv]). *)
Lemma source_cstr_src :
  read_cstr (mrb rsegs fmem) psrc
  = if Nat.ltb (length src) path_max then CstrOk src else CstrTooLong.
Proof.
  unfold psrc.
  apply (read_cstr_argv rsegs fmem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x11100))
           rsp rbrk rrnd 1 Hva Hlau ltac:(lia)).
  intros a n Ha Hn. exact (rdn_fmem_above a n Ha Hn).
Qed.

Lemma source_cstr_dst :
  read_cstr (mrb rsegs fmem) pdst
  = if Nat.ltb (length dst) path_max then CstrOk dst else CstrTooLong.
Proof.
  unfold pdst.
  apply (read_cstr_argv rsegs fmem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x11100))
           rsp rbrk rrnd 2 Hva Hlau ltac:(lia)).
  intros a n Ha Hn. exact (rdn_fmem_above a n Ha Hn).
Qed.

(** _start + main's head, through raw_syscall, to the first openat
    ecall. *)
Lemma source_to_open1 :
  exists regs1,
    reg_get regs1 1 = (0x1103c : word) /\
    reg_get regs1 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs1 3 = (0x13800 : word) /\
    reg_get regs1 8 = Z_to_bv 64 (bv_unsigned rsp + 8) /\
    bv_unsigned (getr regs1 17) = 56%Z /\
    reg_get regs1 10 = AT_FDCWD /\
    reg_get regs1 11 = psrc /\
    reg_get regs1 12 = Z_to_bv 64 0 /\
    msteps rsegs
      (init_machine_state rsegs 0x11100 source_phdrs rsp rmb rrnd inp)
      {| ms_regs := regs1; ms_fregs := fp_regs; ms_pc_val := 0x11150;
         ms_svc_pending := Some (getr regs1 17);
         ms_resv := None; ms_fcsr := fp_csr; ms_mem := fmem; ms_rom := rrom |}.
Proof.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  pose proof (valid_argv_len av Hva) as HargcLe.
  destruct psrc_bounds as [Hplo Hphi].
  (* 0x11100 .. 0x11150 — ONE reflective block: the whole crt entry (gp,
     the [environ] store, the [jal] into main), main's not-taken [bge],
     the argv[1] reload, the frame push with its three callee-save
     stores, the openat argument setup, the [jal] into raw_syscall and
     its register shuffles.  The executor stops at the [ecall]. *)
  sym_block_ex (source_segs ++ vt)
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
          (Z_to_bv 64 69888) wmem rrom)
    40%nat [false] [EVar 33; EVar 34]
    [((2 : reg), EVar 32); ((8 : reg), ELit 0); ((9 : reg), ELit 0)]
    [rsp] [argcN; psrc] R HR Hms.
  { exists (word_le8 psrc); split;
      [ rewrite <- rdn_emem_above by (u_norm; lia); exact read_psrc_e
      | exact (bytes_le_n_to_le_8 _) ]. }
  { s_ro. }
  { s_ro. }
  { s_ro. }
  { apply negb_false_iff.
    change (bv_lts (Z_to_bv 64 2) argcN) with (c_lts (Z_to_bv 64 2) argcN).
    rewrite c_lts_small by (u_norm; rewrite ?u_argcN; lia).
    apply Z.ltb_lt; u_norm; rewrite u_argcN; lia. }
  { s_ro. }
  { exists (word_le8 argcN); split;
      [ replace (Z_to_bv 64 (bv_unsigned rsp + 0)) with rsp
          by (apply bv_eq; u_norm; lia);
        exact read_argc_w
      | exact (bytes_le_n_to_le_8 _) ]. }
  (* Re-spell the block's exit memory as [fmem]. *)
  match type of Hms with msteps _ _ (mkst _ _ ?M _) => assert (HM : M = fmem) end.
  { unfold fmem, emem. sym_mem_norm. rewrite envp_ptr_eq_sym. reflexivity. }
  rewrite HM in Hms. clear HM.
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  9: {
    rewrite init_mkst.
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_11150) eq_refl)
      | apply mst_refl ]. }
  all: sym_regs HR; first [ sym_close | (vm_compute; reflexivity) ].
Qed.

(** After the first open answers an error (a0 signed-negative): exit 3
    through the epilogue.  [X] is the returned value. *)
Lemma source_exit3 : forall regs model X fsv,
  reg_get regs 1 = (0x1103c : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 10 = X ->
  c_lts X (Z_to_bv 64 0) = true ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs 0x11154 fmem rrom) model
    (fun o => o = (Z_to_bv 64 3, fsv)).
Proof.
  intros regs model X fsv H1 H2 H10 Hneg Hfs.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  (* raw_syscall's [ret] (resolved by the [ra] pin), [mv s1,a0],
     [li a0,3] and the taken [bltz s1] into main's epilogue. *)
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 69972) fmem rrom)
    4%nat [true] (@nil expr)
    [((1 : reg), ELit 0x1103c); ((10 : reg), EVar 32)] [X] (@nil word) R HR Hms.
  { exact Hneg. }
  { s_pin H1. }
  { s_pin H10. }
  eapply tfo_msteps; [ exact Hms | ].
  sym_pc_lit.
  apply source_exit_tail.
  - s_out HR.
  - s_out HR.
  - vm_compute; reflexivity.
  - apply fmem_ra_slot.
  - apply fmem_s0_slot.
  - apply fmem_s1_slot.
  - exact Hfs.
Qed.

(** After the second open answers an error: exit 4 through the
    epilogue. *)
Lemma source_exit4 : forall regs model X fsv,
  reg_get regs 1 = (0x11068 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 10 = X ->
  c_lts X (Z_to_bv 64 0) = true ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs 0x11154 fmem rrom) model
    (fun o => o = (Z_to_bv 64 4, fsv)).
Proof.
  intros regs model X fsv H1 H2 H10 Hneg Hfs.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  (* raw_syscall's [ret], [mv s0,a0], [li a0,4] and the taken [bltz s0]
     into main's epilogue. *)
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 69972) fmem rrom)
    4%nat [true] (@nil expr)
    [((1 : reg), ELit 0x11068); ((10 : reg), EVar 32)] [X]
    (@nil word) R HR Hms.
  { exact Hneg. }
  { s_pin H1. }
  { s_pin H10. }
  eapply tfo_msteps; [ exact Hms | ].
  sym_pc_lit.
  apply source_exit_tail.
  - s_out HR.
  - s_out HR.
  - vm_compute; reflexivity.
  - apply fmem_ra_slot.
  - apply fmem_s0_slot.
  - apply fmem_s1_slot.
  - exact Hfs.
Qed.

(** From the first open's descriptor (fd in a0) to the second openat
    ecall. *)
Lemma source_open1_to_open2 : forall regs fd,
  reg_get regs 1 = (0x1103c : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 3 = (0x13800 : word) ->
  reg_get regs 8 = Z_to_bv 64 (bv_unsigned rsp + 8) ->
  reg_get regs 10 = fd ->
  (bv_unsigned fd < 2^31)%Z ->
  exists regs2,
    reg_get regs2 1 = (0x11068 : word) /\
    reg_get regs2 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs2 3 = (0x13800 : word) /\
    reg_get regs2 9 = fd /\
    bv_unsigned (getr regs2 17) = 56%Z /\
    reg_get regs2 10 = AT_FDCWD /\
    reg_get regs2 11 = pdst /\
    reg_get regs2 12 = Z_to_bv 64 577 /\
    msteps rsegs (mkst regs 0x11154 fmem rrom)
      {| ms_regs := regs2; ms_fregs := fp_regs; ms_pc_val := 0x11150;
         ms_svc_pending := Some (getr regs2 17);
         ms_resv := None; ms_fcsr := fp_csr; ms_mem := fmem; ms_rom := rrom |}.
Proof.
  intros regs fd H1 H2 H3 H8 H10 Hlt.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  destruct pdst_bounds as [Hplo Hphi].
  (* raw_syscall's [ret], [mv s1,a0], the not-taken [bltz], the argv[2]
     reload off the saved [s0], the openat argument [li]s, the [jal] back
     into raw_syscall and its shuffles. *)
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 69972) fmem rrom)
    24%nat [false] [EVar 34]
    [((1 : reg), ELit 0x1103c); ((8 : reg), EVar 32); ((10 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp + 8); fd] [pdst] R HR Hms.
  { exists (word_le8 pdst); split;
      [ exact read_pdst_f | exact (bytes_le_n_to_le_8 _) ]. }
  { apply c_lts_pos_0; lia. }
  { s_pin H1. }
  { s_pin H8. }
  { s_pin H10. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  9: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_11150) eq_refl)
      | apply mst_refl ]. }
  all: s_out HR.
Qed.

(* ================================================================= *)
(* After the read: the write, both closes, exit 0                     *)
(* ================================================================= *)

(** From raw_syscall's [ret] after a read that delivered [bs] into the
    buffer: the write of exactly those bytes on fd 4, both closes, exit
    0.  The write lands whole whatever fd 4 is ([hc_dst_ok]): a regular
    file empty at offset 0 takes the bytes, /dev/null and /dev/urandom
    answer the count. *)
Lemma src_after_read : forall regs mem model bs fe1 fe_d fsv,
  reg_get regs 1 = (0x11094 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 3 = (0x13800 : word) ->
  reg_get regs 8 = Z_to_bv 64 4 ->
  reg_get regs 9 = Z_to_bv 64 3 ->
  reg_get regs 10 = len_word bs ->
  (length bs <= 128)%nat ->
  mem_grows wmem mem ->
  rdn rsegs mem sbuf (length bs) = Some bs ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
    = Some (word_to_le_bytes 8 (0x1112c : word)) ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 16)) 8%nat
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 24)) 8%nat
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  fd_lookup (m_fds model) (Z_to_bv 64 3) = Some fe1 ->
  fd_lookup (m_fds model) (Z_to_bv 64 4) = Some fe_d ->
  m_fs model = fsv ->
  hc_dst_ok fe_d fsv ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout rsegs (mkst regs 0x11154 mem rrom) model
    (fun o => o = (Z_to_bv 64 0, hc_written fe_d fsv bs)).
Proof.
  intros regs mem model bs fe1 fe_d fsv H1 H2 H3 H8 H9 H10 Hlen Hg Hbuf Hra Hs0 Hs1
    Hfd1 Hfd2 Hfs Hok Hh Hlazy.
  subst fsv.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  assert (HNc : bv_unsigned (len_word bs) = Z.of_nat (length bs)) by (apply u_len_word; lia).
  destruct (src_read_to_write regs mem (Z_to_bv 64 3) (Z_to_bv 64 4) (len_word bs))
    as (regs4 & L17 & L10 & L11 & L12 & L1 & L2 & L8 & L9 & Hms4);
    [ exact H1 | exact H2 | exact H3 | exact H8 | exact H9 | exact H10 | lia | exact Hg | ].
  eapply tfo_msteps; [ exact Hms4 | ].
  (* what follows the write, whatever it wrote *)
  assert (Hafter : forall model',
    fd_lookup (m_fds model') (Z_to_bv 64 3) = Some fe1 ->
    (exists e2, fd_lookup (m_fds model') (Z_to_bv 64 4) = Some e2) ->
    m_halted model' = None -> m_vm_lazy model' = [] ->
    to_fout rsegs (mkst (regupd regs4 10 (len_word bs)) (v_addi (0x11150 : word) 4)
                        (spill_at mem (len_word bs)) rrom) model'
      (fun o => o = (Z_to_bv 64 0, m_fs model'))).
  { intros model' G1 [e2 G2] Gh Gl.
    fnorm_pc.
    destruct (src_write_to_ret (regupd regs4 10 (len_word bs)) (spill_at mem (len_word bs))
                (Z_to_bv 64 3) (Z_to_bv 64 4) (len_word bs))
      as (regs5 & M2 & M8 & M9 & Hms5);
      [ regupd_resolve; exact L1 | regupd_resolve; exact L2
      | regupd_resolve; exact L8 | regupd_resolve; exact L9
      | regupd_resolve; reflexivity | apply rdn_spill_cnt | ].
    eapply tfo_msteps; [ exact Hms5 | ].
    eapply tfo_msteps.
    { stepiwv (SFv SF_110d0) SD_110d0 (Z_to_bv 64 3)
        ltac:(getr_resolve; rewrite M9; apply v_addiw_id; vm_compute; reflexivity).
      stepj (SFv SF_110d4) SD_110d4.
      apply mst_refl. }
    match goal with |- to_fout _ (mkst ?RG _ ?MM _) _ _ =>
      destruct (src_close_call RG MM (Z_to_bv 64 3) (0x110d8 : word)
                  (Z_to_bv 64 4) (Z_to_bv 64 3))
        as (regs6 & N17 & N10 & N1 & N2 & N8 & N9 & Hms6)
    end;
      [ getr_resolve; regupd_resolve; bveq
      | regupd_resolve; exact M2 | regupd_resolve; exact M8
      | regupd_resolve; exact M9 | regupd_resolve; reflexivity
      | hc_grows Hg | ].
    eapply tfo_msteps; [ exact Hms6 | ].
    eapply tfo_close_rec with (fdv := Z_to_bv 64 3).
    - exact N17.
    - exact N10.
    - exact G1.
    - fd32_ok.
    - exact Gh.
    - exact Gl.
    - fnorm_pc.
      match goal with |- to_fout _ (mkst ?RG _ ?MM _) _ _ =>
        destruct (src_close_tail RG MM (0x110d8 : word) (Z_to_bv 64 4) (Z_to_bv 64 3))
          as (regs7 & P1 & P2 & P8 & P9 & P10 & Hms7)
      end;
        [ regupd_resolve; exact N1 | regupd_resolve; exact N2
        | regupd_resolve; exact N8 | regupd_resolve; exact N9
        | regupd_resolve; reflexivity
        | apply rdn_wbytes_hit8; u_norm; lia | ].
      eapply tfo_msteps; [ exact Hms7 | ].
      eapply tfo_msteps.
      { stepjr (SFv SF_111a4) SD_111a4 (0x110d8 : word) ltac:(getr_resolve; exact P1).
        stepiwv (SFv SF_110d8) SD_110d8 (Z_to_bv 64 4)
          ltac:(getr_resolve; rewrite P8; apply v_addiw_id; vm_compute; reflexivity).
        stepj (SFv SF_110dc) SD_110dc.
        apply mst_refl. }
      match goal with |- to_fout _ (mkst ?RG _ ?MM _) _ _ =>
        destruct (src_close_call RG MM (Z_to_bv 64 4) (0x110e0 : word)
                    (Z_to_bv 64 4) (Z_to_bv 64 3))
          as (regs8 & Q17 & Q10 & Q1 & Q2 & Q8 & Q9 & Hms8)
      end;
        [ getr_resolve; regupd_resolve; bveq
        | regupd_resolve; exact P2 | regupd_resolve; exact P8
        | regupd_resolve; exact P9 | regupd_resolve; reflexivity
        | hc_grows Hg | ].
      eapply tfo_msteps; [ exact Hms8 | ].
      eapply tfo_close_rec with (fdv := Z_to_bv 64 4).
      + exact Q17.
      + exact Q10.
      + model_simp. rewrite fd_lookup_remove_neq by exact fd4_ne_fd3. exact G2.
      + fd32_ok.
      + exact Gh.
      + exact Gl.
      + (* the second close tail; li a0,0; main's epilogue *)
        fnorm_pc.
        match goal with |- to_fout _ (mkst ?RG _ ?MM _) _ _ =>
          destruct (src_close_tail RG MM (0x110e0 : word) (Z_to_bv 64 4) (Z_to_bv 64 3))
            as (regs9 & S1 & S2 & S8 & S9 & S10 & Hms9)
        end;
          [ regupd_resolve; exact Q1 | regupd_resolve; exact Q2
          | regupd_resolve; exact Q8 | regupd_resolve; exact Q9
          | regupd_resolve; reflexivity
          | apply rdn_wbytes_hit8; u_norm; lia | ].
        eapply tfo_msteps; [ exact Hms9 | ].
        eapply tfo_msteps.
        { stepjr (SFv SF_111a4) SD_111a4 (0x110e0 : word) ltac:(getr_resolve; exact S1).
          stepiv (SFv SF_110e0) SD_110e0 (Z_to_bv 64 0) ltac:(vconst).
          apply mst_refl. }
        apply source_exit_tail.
        * regupd_resolve; exact S2.
        * regupd_resolve; reflexivity.
        * vm_compute; reflexivity.
        * hc_peel. exact Hra.
        * hc_peel. exact Hs0.
        * hc_peel. exact Hs1.
        * reflexivity. }
  assert (Hrd : rdn rsegs (spill_at mem (len_word bs)) sbuf (word_to_nat (len_word bs))
                = Some bs).
  { replace (word_to_nat (len_word bs)) with (length bs)
      by (unfold word_to_nat; rewrite HNc, Nat2Z.id; reflexivity).
    unfold spill_at.
    rewrite rdn_wbytes_below
      by (rewrite ?length_N_to_le_bytes, ?u_sbuf; u_norm; lia).
    exact Hbuf. }
  assert (Haok : access_okb sbuf (bv_unsigned (len_word bs)) = true).
  { apply access_okb_intro. rewrite u_sbuf, HNc. unfold TASK_SIZE. lia. }
  destruct Hok as [(j & -> & Hdata) | [-> | ->]].
  - (* a regular file, empty at offset 0: it takes the bytes *)
    eapply tfo_write_rec with (p := j) (off := Z_to_bv 64 0)
      (data := Fs.fs_ino_data (m_fs model) j) (bs := bs).
    + exact L17.
    + exact L10.
    + exact L11.
    + exact L12.
    + exact Hfd2.
    + fd32_ok.
    + exact Hrd.
    + rewrite HNc. unfold rw_bytes_max. lia.
    + reflexivity.
    + rewrite Hdata. apply file_gap_in_range.
      rewrite u_Z2bv by lia. unfold rw_bytes_max. cbn [length]. lia.
    + exact Haok.
    + exact Hh.
    + exact Hlazy.
    + eapply tfo_equiv; [ apply Hafter | ].
      * model_simp. rewrite fd_lookup_insert_neq by (intro Hc; exact (fd4_ne_fd3 (eq_sym Hc))).
        exact Hfd1.
      * eexists. model_simp. apply fd_lookup_insert_eq.
      * exact Hh.
      * exact Hlazy.
      * intro o. split; intro Ho; exact Ho.
  - (* /dev/null: the count *)
    eapply tfo_write_null_rec.
    + exact L17.
    + exact L10.
    + exact L11.
    + exact L12.
    + exact Hfd2.
    + fd32_ok.
    + exact Haok.
    + rewrite HNc. unfold rw_bytes_max. lia.
    + exact Hh.
    + exact Hlazy.
    + eapply tfo_equiv; [ apply Hafter | ].
      * exact Hfd1.
      * exists (FdDevNull false true). exact Hfd2.
      * exact Hh.
      * exact Hlazy.
      * intro o. split; intro Ho; exact Ho.
  - (* /dev/urandom: the whole count of a readable buffer *)
    eapply tfo_write_urandom_rec with (bs := bs).
    + exact L17.
    + exact L10.
    + exact L11.
    + exact L12.
    + exact Hfd2.
    + fd32_ok.
    + exact Hrd.
    + exact Haok.
    + rewrite HNc. unfold page_size. lia.
    + exact Hh.
    + exact Hlazy.
    + eapply tfo_equiv; [ apply Hafter | ].
      * exact Hfd1.
      * exists (FdUrandom false true). exact Hfd2.
      * exact Hh.
      * exact Hlazy.
      * intro o. split; intro Ho; exact Ho.
Qed.

(* ================================================================= *)
(* The result                                                         *)
(* ================================================================= *)

(** argc >= 3: the outcome set, from any model with the entry's
    descriptor table, image, working folder and random stream, for
    every operand the model answers the open of. *)
Lemma source_ge3 : forall m0,
  m_fds m0 = fds0 -> m_fs m0 = fs0 -> m_cwd m0 = in_cwd inp ->
  m_urandom m0 = in_urandom inp ->
  m_halted m0 = None -> m_vm_lazy m0 = [] ->
  stream_infinite (in_urandom inp) ->
  (op_walked src = true -> open_answered true fs0 (in_cwd inp) src) ->
  (op_walked dst = true -> open_answered false fs0 (in_cwd inp) dst) ->
  to_fout rsegs (init_machine_state rsegs 0x11100 source_phdrs rsp rmb rrnd inp) m0
    (hc_outcomes fs0 (in_cwd inp) (in_urandom inp) src dst).
Proof.
  intros m0 Hfds Hfs Hcwd Hur Hh Hlazy Hinf Hans1 Hans2.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  destruct source_to_open1
    as (regs1 & H1 & H2 & H3 & H8 & H17 & H10 & H11 & H12 & Hms).
  eapply tfo_msteps; [exact Hms|].
  apply (tfo_open_operand_rec rsegs regs1 (0x11150 : word) fmem m0 src true
           (fun o => o = (Z_to_bv 64 3, fs0))
           (fun o => match open_arm true fs0 (in_cwd inp) src with
                     | inl (fe_s, _) =>
                         o = (Z_to_bv 64 4, fs0)
                         \/ (op_walked dst = true /\
                             match open_arm false fs0 (in_cwd inp) dst with
                             | inl (fe_d, ofs) =>
                                 hc_copy (hc_fs1 fs0 ofs) (in_urandom inp) fe_s fe_d o
                             | inr _ => False
                             end)
                     | inr _ => False
                     end)).
  - exact H17.
  - exact H10.
  - exact H12.
  - rewrite H11. exact source_cstr_src.
  - intros _. apply proc_self_fd_no_slash.
    exact (valid_argv_no_slash av 0 Hva ltac:(lia)).
  - intros Hw. rewrite Hfs, Hcwd. exact (Hans1 Hw).
  - rewrite Hfds. exact hc_free1.
  - exact Hh.
  - exact Hlazy.
  - (* the first open answers an errno: exit 3 *)
    intros r Hr. fnorm_pc.
    apply (source_exit3 (regupd regs1 10 r) m0 r fs0).
    + regupd_resolve; exact H1.
    + regupd_resolve; exact H2.
    + regupd_resolve; reflexivity.
    + destruct (addr_is_error_b_errno r Hr) as (e & He1 & He2 & ->).
      apply c_lts_errno; assumption.
    + exact Hfs.
  - (* a descriptor on the source operand *)
    intros fe_s ofs1 Harm1.
    rewrite Hfs, Hcwd in Harm1.
    destruct (open_arm_rd_cases _ _ _ _ _ Harm1) as [-> Hkind].
    apply (tfo_equiv rsegs _ _
             (fun o => o = (Z_to_bv 64 4, fs0)
                       \/ (op_walked dst = true /\
                           match open_arm false fs0 (in_cwd inp) dst with
                           | inl (fe_d, ofs) =>
                               hc_copy (hc_fs1 fs0 ofs) (in_urandom inp) fe_s fe_d o
                           | inr _ => False
                           end))).
    2:{ intro o. rewrite Harm1. split; intro Ho; exact Ho. }
    assert (Hfd1 : alloc_fd (m_fds m0) = Z_to_bv 64 3) by (rewrite Hfds; exact hc_fd1).
    rewrite Hfd1.
    fnorm_pc.
    destruct (source_open1_to_open2 (regupd regs1 10 (Z_to_bv 64 3)) (Z_to_bv 64 3))
      as (regs2 & G1 & G2 & G3 & G9 & G17 & G10 & G11 & G12 & Hms2);
      [ regupd_resolve; exact H1 | regupd_resolve; exact H2
      | regupd_resolve; exact H3 | regupd_resolve; exact H8
      | regupd_resolve; reflexivity | vm_compute; reflexivity | ].
    eapply tfo_msteps; [exact Hms2|].
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
    apply (tfo_open_operand_rec rsegs regs2 (0x11150 : word) fmem m1 dst false
             (fun o => o = (Z_to_bv 64 4, fs0))
             (fun o => match open_arm false fs0 (in_cwd inp) dst with
                       | inl (fe_d, ofs) =>
                           hc_copy (hc_fs1 fs0 ofs) (in_urandom inp) fe_s fe_d o
                       | inr _ => False
                       end)).
    + exact G17.
    + exact G10.
    + exact G12.
    + rewrite G11. exact source_cstr_dst.
    + intros _. apply proc_self_fd_no_slash.
      exact (valid_argv_no_slash av 1 Hva ltac:(lia)).
    + intros Hw. rewrite Hm1fs, Hm1cwd. exact (Hans2 Hw).
    + rewrite Hm1fds. exact (hc_free2 fe_s).
    + exact Hm1h.
    + exact Hm1l.
    + (* the second open answers an errno: exit 4 *)
      intros r Hr. fnorm_pc.
      apply (source_exit4 (regupd regs2 10 r) m1 r fs0).
      * regupd_resolve; exact G1.
      * regupd_resolve; exact G2.
      * regupd_resolve; reflexivity.
      * destruct (addr_is_error_b_errno r Hr) as (e & He1 & He2 & ->).
        apply c_lts_errno; assumption.
      * exact Hm1fs.
    + (* both descriptors: the read *)
      intros fe_d ofs2 Harm2.
      rewrite Hm1fs, Hm1cwd in Harm2.
      apply (tfo_equiv rsegs _ _ (hc_copy (hc_fs1 fs0 ofs2) (in_urandom inp) fe_s fe_d)).
      2:{ intro o. rewrite Harm2. split; intro Ho; exact Ho. }
      assert (Hfd2 : alloc_fd (m_fds m1) = Z_to_bv 64 4)
        by (rewrite Hm1fds; exact (hc_fd2 fe_s)).
      rewrite Hfd2.
      set (m2 := open_model m1 (Z_to_bv 64 4) fe_d ofs2).
      assert (Hm2fds : m_fds m2 = fd_insert (fd_insert fds0 (Z_to_bv 64 3) fe_s)
                                    (Z_to_bv 64 4) fe_d)
        by (unfold m2; rewrite open_model_fds, Hm1fds; reflexivity).
      assert (Hm2fs : m_fs m2 = hc_fs1 fs0 ofs2)
        by (unfold m2, hc_fs1; rewrite open_model_fs, Hm1fs; reflexivity).
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
      assert (Hdok : hc_dst_ok fe_d (m_fs m2))
        by (rewrite Hm2fs; exact (hc_dst_ok_arm _ _ _ _ _ Harm2)).
      fnorm_pc.
      destruct (src_open2_to_read (regupd regs2 10 (Z_to_bv 64 4)) fmem
                  (Z_to_bv 64 3) (Z_to_bv 64 4) (Z_to_bv 64 (bv_unsigned rsp - 48)))
        as (regs3 & K17 & K10 & K11 & K12 & K1 & K2 & K3 & K8 & K9 & Hms3);
        [ regupd_resolve; exact G1 | regupd_resolve; exact G2
        | regupd_resolve; exact G3 | regupd_resolve; exact G9
        | regupd_resolve; reflexivity | vm_compute; reflexivity | ].
      eapply tfo_msteps; [ exact Hms3 | ].
      assert (Haok : access_okb sbuf (bv_unsigned (Z_to_bv 64 128)) = true).
      { apply access_okb_intro. rewrite u_sbuf, u_Z2bv by lia. unfold TASK_SIZE. lia. }
      destruct Hkind as [(i & ->) | [(k & ->) | [-> | ->]]].
      * (* a regular file: its first (up to) 128 bytes as they are now *)
        eapply tfo_read_rec with (p := i) (off := Z_to_bv 64 0)
          (data := Fs.fs_ino_data (m_fs m2) i) (buf := sbuf).
        -- exact K17.
        -- exact K10.
        -- exact K11.
        -- exact K12.
        -- exact Hl3.
        -- fd32_ok.
        -- reflexivity.
        -- exact (source_buf_wseg vt).
        -- rewrite u_Z2bv by lia. unfold rw_bytes_max. lia.
        -- rewrite u_Z2bv by lia. lia.
        -- exact Haok.
        -- exact Hm2h.
        -- exact Hm2l.
        -- fnorm_pc.
           set (bs := file_read (Fs.fs_ino_data (m_fs m2) i) (Z_to_bv 64 0) (Z_to_bv 64 128)).
           assert (Hbl : (length bs <= 128)%nat) by (unfold bs; apply hc_chunk_le).
           apply (tfo_equiv rsegs _ _
                    (fun o => o = (Z_to_bv 64 0, hc_written fe_d (m_fs m2) bs))).
           2:{ intro o. rewrite <- Hm2fs. split; intro Ho; exact Ho. }
           eapply src_after_read.
           ++ regupd_resolve; exact K1.
           ++ regupd_resolve; exact K2.
           ++ regupd_resolve; exact K3.
           ++ regupd_resolve; exact K8.
           ++ regupd_resolve; exact K9.
           ++ regupd_resolve; reflexivity.
           ++ exact Hbl.
           ++ eapply mem_grows_trans; [ exact grows_fmem | apply write_to_mem_grows ].
           ++ apply rdn_write_to_mem. rewrite u_sbuf. lia.
           ++ rewrite rdn_wtm_out by (rewrite ?u_sbuf; u_norm; first [ lia | left; lia ]).
              exact fmem_ra_slot.
           ++ rewrite rdn_wtm_out by (rewrite ?u_sbuf; u_norm; first [ lia | left; lia ]).
              exact fmem_s0_slot.
           ++ rewrite rdn_wtm_out by (rewrite ?u_sbuf; u_norm; first [ lia | left; lia ]).
              exact fmem_s1_slot.
           ++ model_simp. apply fd_lookup_insert_eq.
           ++ model_simp. rewrite fd_lookup_insert_neq by exact fd4_ne_fd3. exact Hl4.
           ++ reflexivity.
           ++ exact Hdok.
           ++ exact Hm2h.
           ++ exact Hm2l.
      * (* a folder: -EISDIR, exit 5 *)
        eapply tfo_read_dir_rec.
        -- exact K17.
        -- exact K10.
        -- exact K11.
        -- exact K12.
        -- exact Hl3.
        -- fd32_ok.
        -- exact Haok.
        -- exact Hm2h.
        -- exact Hm2l.
        -- fnorm_pc.
           apply (tfo_equiv rsegs _ _ (fun o => o = (Z_to_bv 64 5, m_fs m2))).
           2:{ intro o. rewrite <- Hm2fs. split; intro Ho; exact Ho. }
           (* raw_syscall's [ret] into main; [mv a3,a0]; [li a0,5]; the
              taken [bltz] into the epilogue *)
           eapply tfo_msteps.
           { norm_pc.
             stepjr (SFv SF_11154) SD_11154 (0x11094 : word)
               ltac:(getr_resolve; regupd_resolve; exact K1).
             stepiv (SFv SF_11094) SD_11094 (errno_ret EISDIR)
               ltac:(getr_resolve; regupd_resolve; apply v_addi_0).
             stepiv (SFv SF_11098) SD_11098 (Z_to_bv 64 5) ltac:(vconst).
             step_intro;
               [ reflexivity
               | eapply step_blt_tk;
                 [ exact (SFv SF_1109c) | reflexivity | exact SD_1109c
                 | getr_resolve; regupd_resolve; apply c_lts_errno;
                   unfold EISDIR; lia ]
               | norm_pc ].
             apply mst_refl. }
           apply source_exit_tail.
           ++ regupd_resolve; exact K2.
           ++ regupd_resolve; reflexivity.
           ++ vm_compute; reflexivity.
           ++ apply fmem_ra_slot.
           ++ apply fmem_s0_slot.
           ++ apply fmem_s1_slot.
           ++ reflexivity.
      * (* /dev/null: nothing *)
        eapply tfo_read_null_rec.
        -- exact K17.
        -- exact K10.
        -- exact K11.
        -- exact K12.
        -- exact Hl3.
        -- fd32_ok.
        -- exact Haok.
        -- exact Hm2h.
        -- exact Hm2l.
        -- fnorm_pc.
           apply (tfo_equiv rsegs _ _
                    (fun o => o = (Z_to_bv 64 0, hc_written fe_d (m_fs m2) []))).
           2:{ intro o. rewrite <- Hm2fs. split; intro Ho; exact Ho. }
           eapply src_after_read.
           ++ regupd_resolve; exact K1.
           ++ regupd_resolve; exact K2.
           ++ regupd_resolve; exact K3.
           ++ regupd_resolve; exact K8.
           ++ regupd_resolve; exact K9.
           ++ regupd_resolve; reflexivity.
           ++ cbn [length]. lia.
           ++ exact grows_fmem.
           ++ reflexivity.
           ++ exact fmem_ra_slot.
           ++ exact fmem_s0_slot.
           ++ exact fmem_s1_slot.
           ++ exact Hl3.
           ++ exact Hl4.
           ++ reflexivity.
           ++ exact Hdok.
           ++ exact Hm2h.
           ++ exact Hm2l.
      * (* /dev/urandom: the first 128 bytes of the declared stream *)
        eapply tfo_read_urandom_rec.
        -- exact K17.
        -- exact K10.
        -- exact K11.
        -- exact K12.
        -- exact Hl3.
        -- fd32_ok.
        -- exact (source_buf_wseg vt).
        -- rewrite u_Z2bv by lia. unfold page_size. lia.
        -- exact Haok.
        -- rewrite Hm2ur. exact Hinf.
        -- exact Hm2h.
        -- exact Hm2l.
        -- fnorm_pc.
           rewrite Hm2ur.
           change (bv_unsigned (Z_to_bv 64 128)) with 128%Z.
           set (bs := fst (stream_take_z (in_urandom inp) 128)).
           assert (Hbn : Z.of_nat (length bs) = 128%Z)
             by (apply stream_take_z_infinite_length; [exact Hinf | lia]).
           assert (Hlb : len_word bs = Z_to_bv 64 128)
             by (unfold len_word; rewrite Hbn; reflexivity).
           apply (tfo_equiv rsegs _ _
                    (fun o => o = (Z_to_bv 64 0, hc_written fe_d (m_fs m2) bs))).
           2:{ intro o. rewrite <- Hm2fs. split; intro Ho; exact Ho. }
           eapply src_after_read.
           ++ regupd_resolve; exact K1.
           ++ regupd_resolve; exact K2.
           ++ regupd_resolve; exact K3.
           ++ regupd_resolve; exact K8.
           ++ regupd_resolve; exact K9.
           ++ regupd_resolve. symmetry. exact Hlb.
           ++ lia.
           ++ eapply mem_grows_trans; [ exact grows_fmem | apply write_to_mem_grows ].
           ++ apply rdn_write_to_mem. rewrite u_sbuf. lia.
           ++ rewrite rdn_wtm_out by (rewrite ?u_sbuf; u_norm; first [ lia | left; lia ]).
              exact fmem_ra_slot.
           ++ rewrite rdn_wtm_out by (rewrite ?u_sbuf; u_norm; first [ lia | left; lia ]).
              exact fmem_s0_slot.
           ++ rewrite rdn_wtm_out by (rewrite ?u_sbuf; u_norm; first [ lia | left; lia ]).
              exact fmem_s1_slot.
           ++ exact Hl3.
           ++ exact Hl4.
           ++ reflexivity.
           ++ exact Hdok.
           ++ exact Hm2h.
           ++ exact Hm2l.
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
    intro o. unfold hc_outcomes, open_ok. rewrite Hfs, Hcwd.
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
(* argc < 3: no output, exit 2 (CatSim shape)                        *)
(* ================================================================= *)

Lemma source_wexit_lt3 : (length av < 3)%nat ->
  to_wexit rsegs
    (init_machine_state rsegs 0x11100 source_phdrs rsp rmb rrnd inp)
    [] (Z_to_bv 64 2).
Proof.
  intros Hlt3.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  pose proof (valid_argv_len av Hva) as HargcLe.
  rewrite init_mkst. norm_pc.
  (* _start: auipc gp,0x2 ; addi gp,gp,-1656 *)
  stepi (SFv SF_11100) SD_11100.
  stepiv (SFv SF_11104) SD_11104 (0x13800 : word) ltac:(getr_resolve; bveq).
  (* ld a0,0(sp): argc *)
  step_intro;
    [ reflexivity
    | eapply step_ld with (bs := word_le8 argcN) (v := argcN);
      [ exact (SFv SF_11108) | reflexivity | exact SD_11108
      | match goal with |- rdn _ _ ?ad _ = _ =>
          replace ad with rsp by (getr_resolve; rewrite v_addi_0; reflexivity)
        end; exact read_argc_w
      | exact (bytes_le_n_to_le_8 _) ]
    | step_simpl ].
  (* addi a1,sp,8 ; slli ; add ; addi *)
  stepiv (SFv SF_1110c) SD_1110c (Z_to_bv 64 (bv_unsigned rsp + 8)) ltac:(spn).
  stepi (SFv SF_11110) SD_11110.
  stepi (SFv SF_11114) SD_11114.
  stepiv (SFv SF_11118) SD_11118 envp_ptr ltac:(getr_resolve; exact envp_ptr_eq).
  (* auipc t1 ; addi t1 ; sd a2,0(t1) *)
  stepi (SFv SF_1111c) SD_1111c.
  stepiv (SFv SF_11120) SD_11120 (0x13000 : word) ltac:(getr_resolve; bveq).
  ssd (SFv SF_11124) SD_11124 (0x13000 : word) envp_ptr
    ltac:(getr_resolve; reflexivity) ltac:(s_ro).
  (* jal main *)
  stepj (SFv SF_11128) SD_11128.
  (* main: li a5,2 ; bge a5,a0 taken (argc <= 2) -> 0x110f8 *)
  stepiv (SFv SF_11000) SD_11000 (Z_to_bv 64 2) ltac:(vconst).
  step_intro;
    [ reflexivity
    | eapply step_bge_tk;
      [ exact (SFv SF_11004) | reflexivity | exact SD_11004
      | getr_resolve; regupd_resolve;
        rewrite c_lts_small by (u_norm; rewrite ?u_argcN; lia);
        apply Z.ltb_ge; u_norm; rewrite u_argcN; lia ]
    | norm_pc ].
  (* mv a0,a5 ; ret -> 0x1112c *)
  stepiv (SFv SF_110f8) SD_110f8 (Z_to_bv 64 2) ltac:(vconst).
  sret (SFv SF_110fc) SD_110fc (0x1112c : word).
  (* li a7,93 ; ecall -> exit 2 *)
  stepiv (SFv SF_1112c) SD_1112c (Z_to_bv 64 93) ltac:(vconst).
  step_intro;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_11130) eq_refl) | ].
  apply tw_exit_coden.
  - getr_resolve; reflexivity.
  - regupd_resolve; reflexivity.
  - vm_compute; reflexivity.
Qed.

End SourceProof.
