(** * cp-ns, source binary (musl-gcc -Os, syscall wrappers).

    PROOF-SIDE FILE (not part of the trusted specification).

    The opens and the copy loop's read/write go through the crt's
    raw_syscall (0x11160); close goes through musl's __syscall_cp
    (0x11238 -> 0x11214) and __syscall_ret (0x111dc).  The
    __syscall_ret error path is dead on every modeled resolution (close
    returns 0).  Copy loop head: 0x1107c; buffer at 0x13008.

    Deliverables, over the run's segment list [source_segs ++ vt]:
    - [source_wexit_lt3] : argc < 3 -> to_wexit [] 2 (CatSim glue);
    - [source_ge3]       : argc >= 3 -> to_floop [cp_outcomes], whatever
      each operand's open answers ([FileSimLoop.tfl_open_operand_rec]),
      and on both descriptors whatever the first one is (a regular file,
      a folder, /dev/null, /dev/urandom) and the second one is (a regular
      file, /dev/null, /dev/urandom).  The copy of a regular file runs to
      its end, or to [cp_ns_defs.cp_cut] where its read is -EINVAL
      ([source_loop]); /dev/urandom into a regular file runs to
      [cp_cut], where its write is -EINVAL ([source_uloop]); /dev/urandom
      into a device is copied forever, a silent loop
      ([src_endless_anchored], [FileSimLoop.tfl_loop]).

    Sp-relative addresses/register values are in the canonical
    [Z_to_bv 64 (bv_unsigned rsp - k)] form, pc and rodata
    constants in numeral-literal form, block lengths as [len_word bs];
    all range bookkeeping is in [Z] over [bv_unsigned].  The loop body
    is factored into three [msteps] chain lemmas ([src_head_to_read],
    [src_read_to_write], [src_write_to_head]) shared by the bounded
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
#[local] Instance cp_ns_source_fx : FPState := fx0.

Definition sbuf : word := 0x13008.

Lemma u_sbuf : bv_unsigned sbuf = 0x13008%Z.
Proof. reflexivity. Qed.

(** Zero-test outcome from an unsigned-level zero fact. *)
Lemma c_eq_0_of_u : forall x : word, bv_unsigned x = 0%Z ->
  c_eq x (Z_to_bv 64 0) = true.
Proof.
  intros x Hx. unfold c_eq, bv_eqb. rewrite Hx. reflexivity.
Qed.

(** [slli rd,rs,3] denotes as [v_sll x (Z_to_bv 64 3)] in the reflective
    executor, where the tactic layer's lemmas are stated for the
    immediate form [v_slli]. *)
Lemma v_sll_3 : forall x : word, v_sll x (Z_to_bv 64 3) = v_slli x 3.
Proof.
  intro x. unfold v_sll, v_slli.
  replace (bv_unsigned (Z_to_bv 64 3) mod 64)%Z with 3%Z
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma fd3_ne_fd4 : Z_to_bv 64 3 <> Z_to_bv 64 4.
Proof. intro Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc. Qed.

(** Normalize the pc of a [to_fout] / [to_floop] goal's head state to its
    literal form (continuation states arrive with [v_addi pc 4]). *)
Local Ltac fnorm_pc :=
  try lazymatch goal with
  | |- to_fout _ (mkst _ ?p _ _) _ _ => wlit p
  end.

Local Ltac flnorm_pc :=
  try lazymatch goal with
  | |- to_floop _ (mkst _ ?p _ _) _ _ => wlit p
  end.

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
    QUANTIFIED (ASLR): the whole section is generic over them.  This
    example never calls brk. *)
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
    stack-store window. *)
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
  wrap_mem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x1112c)) rsp rrnd.

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
Proof.
  pose proof (valid_argv_len av Hva).
  unfold argcN, len_word. apply u_Z2bv; lia.
Qed.

(** No-overflow bound for the initial stack image, for any entry word
    the auxv carries. *)
Lemma source_bsb_nw : forall entry : word,
  (bv_unsigned rsp
   + Z.of_nat (length (entry_stack_image inp rmb source_phdrs entry rsp rrnd)) < 2^64)%Z.
Proof.
  intros entry.
  pose proof (bsb_bound Sv48 inp rmb source_phdrs entry rsp rbrk rrnd Hvl Hlau).
  pose proof rsp_hi_num. lia.
Qed.

(** environ pointer _start stores at 0x13000. *)
Definition envp_val : word :=
  Z_to_bv 64 (bv_unsigned rsp + 16 + 8 * Z.of_nat (length av)).

Lemma envp_val_eq :
  v_addi (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli argcN 3)) 8 = envp_val.
Proof.
  pose proof rsp_hi_num. pose proof rsp_lo_num.
  pose proof (valid_argv_len av Hva) as Hlen.
  pose proof (Nat2Z.is_nonneg (length av)).
  apply bv_eq. unfold envp_val, v_addi.
  rewrite !Z_to_bv_unsigned.
  rewrite v_add_small
    by (rewrite u_Z2bv by lia; rewrite v_slli_3 by (rewrite u_argcN; lia);
        rewrite u_argcN; lia).
  rewrite u_Z2bv by lia.
  rewrite v_slli_3 by (rewrite u_argcN; lia).
  rewrite u_argcN.
  f_equal. lia.
Qed.

(** [envp_val_eq] again, in the spelling the executor's [add]/[slli] pair
    leaves behind. *)
Lemma envp_val_eq_sym :
  Z_to_bv 64 (bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
                                         (v_sll argcN (Z_to_bv 64 3))) + 8)
  = envp_val.
Proof. rewrite alu_add, v_sll_3. exact envp_val_eq. Qed.

Definition emem : word -> option byte :=
  wbytes wmem 0x13000 (word_to_le_bytes 8 envp_val).

(** main()'s 48-byte frame (execution order; sp = rsp - 48): s0@+32,
    s2@+16, ra@+40 (= 0x11158), s1@+24.  gcc 15 keeps only these four
    callee-saved slots; +8 and +0 are the copy loop's pointer/count spill
    slots, which the loop overwrites, so they are NOT part of the frame
    image or of [smem_inv]. *)
Definition fmem : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes emem
    (Z_to_bv 64 (bv_unsigned rsp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 8))  (word_to_le_bytes 8 (0x11158 : word)))
    (Z_to_bv 64 (bv_unsigned rsp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

(** Main's callee-saved frame slots read back — the loop-memory
    invariant.  Only the four slots the epilogue reloads. *)
Definition smem_inv (mem : word -> option byte) : Prop :=
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
    = Some (word_to_le_bytes 8 (0x11158 : word)) /\
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 16)) 8%nat
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 24)) 8%nat
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 32)) 8%nat
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  (* …and [mem] is still writable wherever the initial overlay was: the
     wrapper scratch stores below the frame need [store_ok], and [mem] is
     universally quantified here, so the bound has to travel with it. *)
  mem_grows wmem mem.

Lemma smem_inv_fmem : smem_inv fmem.
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. unfold smem_inv, fmem.
  repeat split; try (unfold emem; solve_mem_grows);
    repeat first
      [ rewrite rdn_wbytes_hit8 by (u_norm; lia)
      | rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia)
      | rewrite rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes; u_norm; lia) ];
    reflexivity.
Qed.

(** The writability projection, registered so the shared store-bound
    dispatcher finds it under an abstract loop memory. *)
Lemma smem_inv_grows : forall mem, smem_inv mem -> mem_grows wmem mem.
Proof. intros mem (_ & _ & _ & _ & H). exact H. Qed.

Local Hint Resolve smem_inv_grows : store_ok_db.

Lemma rdn_emem_above : forall (a : word) n,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn rsegs emem a n = rdn rsegs wmem a n.
Proof.
  intros a n Ha Hnw. pose proof rsp_lo_num. unfold emem.
  rewrite rdn_wbytes_disjoint
    by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
  reflexivity.
Qed.

Lemma rdn_fmem_above : forall (a : word) n,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn rsegs fmem a n = rdn rsegs wmem a n.
Proof.
  intros a n Ha Hnw. pose proof rsp_lo_num. pose proof rsp_hi_num.
  unfold fmem.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; u_norm; lia)).
  apply rdn_emem_above; assumption.
Qed.

Lemma rdn_wmem_stack : forall (a : word) n,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn rsegs wmem a n
  = rdn rsegs (stack_to_mem rsp (entry_stack_image inp rmb source_phdrs
                                   (Z_to_bv 64 (Z.of_N 0x1112c)) rsp rrnd)) a n.
Proof. intros a n Ha Hnw. unfold wmem. apply rdn_wrap_stack_above; assumption. Qed.

Lemma read_argc_w :
  rdn rsegs wmem rsp 8%nat = Some (word_le8 argcN).
Proof.
  pose proof rsp_hi_num.
  rewrite rdn_wmem_stack by lia.
  apply read_argc. apply source_bsb_nw.
Qed.

Definition psrc : word := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1.
Definition pdst : word := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 2.

(* ================================================================= *)
(* Step tactics (local; StepTac's stepi/stepiv/stepiwv/stepj on top)  *)
(* ================================================================= *)

(** Store-permission side goals against the source image. *)
Local Ltac s_ro :=
  first [ apply source_store_ok; imm_norm; u_norm; lia | solve_store_ok_inv ].

(** A fact about a reflective block's EXIT register file, read back
    through its [regs_ok] [H]. *)
Local Ltac s_out H :=
  sym_regs H; rewrite ?getr_nz by reg_neq_tac;
  first [ assumption | sym_close | (vm_compute; reflexivity) ].

Local Ltac addr_tac :=
  getr_resolve; regupd_resolve; sp_norm;
  first [ reflexivity | f_equal; lia | apply bv_eq; u_norm; lia | bveq ].

(** A jalr x0 (ret) to a concrete target. *)
Local Ltac sret F D tt0 :=
  stepjr F D tt0 ltac:(getr_resolve; regupd_resolve; first [ assumption | reflexivity | bveq ]).

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

(* ================================================================= *)
(* main's function epilogue (0x110fc): restore callee-saved, return   *)
(* to _start (0x11158), and exit(a0=code).                            *)
(* ================================================================= *)

Lemma source_fepilogue : forall regs mem model code fsv,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 10 = code -> (bv_unsigned code < 256)%Z ->
  smem_inv mem ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x110fc : word) mem rrom) model
    (fun o => o = (code, fsv)).
Proof.
  intros regs mem model code fsv H2 H10 Hc (Hra & Hs0 & Hs1 & Hs2 & Hg) Hfs.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  (* 0x110fc .. 0x1115c — 8 instructions in ONE reflective block: the
     four callee-save reloads, the frame pop, the [ret] into _start's
     tail (which resolves only because the READ SCRIPT names the
     reloaded [ra]) and the exit(93) load.  The executor stops at the
     [ecall]. *)
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 69884) mem rrom)
    9%nat (@nil bool) [ELit 0x11158; ELit 0; ELit 0; ELit 0]
    [((2 : reg), EVar 32)] [Z_to_bv 64 (bv_unsigned rsp - 48)]
    (@nil word) R HR Hms.
  { exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ exact Hs2 | rewrite bytes_le_to_Z_8; reflexivity ]. }
  { exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ exact Hs1 | rewrite bytes_le_to_Z_8; reflexivity ]. }
  { exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ exact Hs0 | rewrite bytes_le_to_Z_8; reflexivity ]. }
  { exists (word_to_le_bytes 8 (0x11158 : word)); split;
      [ exact Hra | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]. }
  { exact H2. }
  eapply tfo_msteps.
  { eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_1115c) eq_refl)
      | apply mst_refl ]. }
  apply tfo_exit_rec.
  - s_out HR.
  - s_out HR.
  - exact Hc.
  - exact Hfs.
Qed.

(* ================================================================= *)
(* close(fd) (0x11188): entry -> the close ecall (0x11230), and the   *)
(* tail (0x11234) back to the caller.  The syscall succeeds (ret 0).  *)
(* ================================================================= *)

(* [mem_grows]: the wrapper saves ra below the frame, and that store
   needs a writability bound on the (otherwise arbitrary) [mem]. *)
Lemma src_close_entry : forall regs mem fdv raM s0v g3 g9 g18,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 10 = fdv -> reg_get regs 1 = raM -> reg_get regs 8 = s0v ->
  reg_get regs 3 = g3 -> reg_get regs 9 = g9 -> reg_get regs 18 = g18 ->
  mem_grows wmem mem ->
  exists regs',
    bv_unsigned (getr regs' 17) = 57%Z /\ reg_get regs' 10 = fdv /\
    reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 64) /\
    reg_get regs' 1 = (0x111b4 : word) /\ reg_get regs' 8 = s0v /\
    reg_get regs' 3 = g3 /\ reg_get regs' 9 = g9 /\ reg_get regs' 18 = g18 /\
    msteps rsegs (mkst regs (0x11188 : word) mem rrom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := (0x11230 : word);
         ms_svc_pending := Some (getr regs' 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 56))
                          (word_to_le_bytes 8 raM);
         ms_rom := rrom |}.
Proof.
  intros regs mem fdv raM s0v g3 g9 g18 H2 H10 H1 H8 H3 H9 H18 Hg.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  (* 0x11188 .. 0x11230 - 20 instructions in ONE reflective block: the
     16-byte frame with its [ra] spill, the [jal]/[ret] through the empty
     [__aio_close], the six __syscall_cp argument moves, the [jal] into
     __syscall_cp, its [j] to __syscall_cp_c and the seven shuffles.  The
     only side condition is the [ra] spill's [store_ok], lifted through
     the caller's [mem_grows].  The executor stops at the [ecall]. *)
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 70024) mem rrom)
    21%nat (@nil bool) (@nil expr)
    [((1 : reg), EVar 32); ((2 : reg), EVar 33); ((10 : reg), EVar 34)]
    [raM; Z_to_bv 64 (bv_unsigned rsp - 48); fdv] (@nil word) R HR Hms.
  { store_ok_peel; eapply store_ok_mono; [ exact Hg | ]; solve_store_ok. }
  { rewrite getr_nz by reg_neq_tac; exact H1. }
  { rewrite getr_nz by reg_neq_tac; exact H2. }
  { rewrite getr_nz by reg_neq_tac; exact H10. }
  match type of Hms with msteps _ _ (mkst _ _ ?M _) =>
    assert (HM : M = wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 56))
                             (word_to_le_bytes 8 raM))
  end.
  { sym_mem_norm. reflexivity. }
  rewrite HM in Hms. clear HM.
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  9: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_11230) eq_refl)
      | apply mst_refl ]. }
  all: s_out HR.
Qed.

Lemma src_close_tail : forall regs mem raM s0v g3 g9 g18,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 64) ->
  reg_get regs 10 = Z_to_bv 64 0 ->
  reg_get regs 1 = (0x111b4 : word) -> reg_get regs 8 = s0v ->
  reg_get regs 3 = g3 -> reg_get regs 9 = g9 -> reg_get regs 18 = g18 ->
  v_jalr raM 0 = raM ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 56)) 8%nat
    = Some (word_to_le_bytes 8 raM) ->
  exists regs',
    reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs' 10 = Z_to_bv 64 0 /\ reg_get regs' 1 = raM /\
    reg_get regs' 8 = s0v /\ reg_get regs' 3 = g3 /\
    reg_get regs' 9 = g9 /\ reg_get regs' 18 = g18 /\
    msteps rsegs (mkst regs (0x11234 : word) mem rrom)
      (mkst regs' raM mem rrom).
Proof.
  intros regs mem raM s0v g3 g9 g18 H2 H10 H1 H8 H3 H9 H18 Hvj Hrd.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  (* 0x11234 .. 0x111d0 - 11 instructions in ONE reflective block:
     __syscall_cp_c's [ret], the not-taken -ENOSYS retry test,
     __syscall_ret's frameless success path, the [ra] reload named by
     the read script and the frame pop.  The caller-visible [ret] to the
     symbolic [raM] is the one step left to the tactic layer. *)
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 70196) mem rrom)
    11%nat [false; false] [EVar 33]
    [((1 : reg), ELit 0x111b4); ((2 : reg), EVar 32); ((10 : reg), ELit 0)]
    [Z_to_bv 64 (bv_unsigned rsp - 64)] [raM] R HR Hms.
  { exists (word_to_le_bytes 8 raM); split;
      [ match goal with |- rdn _ _ ?ad _ = _ =>
          replace ad with (Z_to_bv 64 (bv_unsigned rsp - 56))
            by (apply bv_eq; u_norm; lia)
        end; exact Hrd
      | exact (bytes_le_to_Z_8 _) ]. }
  { rewrite getr_nz by reg_neq_tac; rewrite H1; bveq. }
  { rewrite getr_nz by reg_neq_tac; exact H2. }
  { rewrite getr_nz by reg_neq_tac; rewrite H10; bveq. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  8: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity
      | eapply step_jalr_x0 with (tgt := raM);
        [ exact (SFv SF_111d0) | reflexivity | exact SD_111d0
        | s_out HR ]
      | imm_norm; rewrite Hvj ].
    apply mst_refl. }
  all: s_out HR.
Qed.

(* ================================================================= *)
(* The copy loop (head 0x1107c), through raw_syscall.  gcc 15 keeps    *)
(* the buffer base in s0 and spills the inner loop's running pointer   *)
(* and count to 0(sp)/8(sp) across the write call.                     *)
(* ================================================================= *)

(** The inner write loop's two spill slots: the running count at
    [rsp-40] (8(sp)) and the running buffer pointer at [rsp-48]
    (0(sp)).  A full write returns the whole count, so the pointer
    stored is always [sbuf] and the loop runs exactly one iteration. *)
Definition spill (mem : word -> option byte) (cnt : word)
    : word -> option byte :=
  wbytes (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 40))
                     (word_to_le_bytes 8 cnt))
         (Z_to_bv 64 (bv_unsigned rsp - 48)) (word_to_le_bytes 8 sbuf).

Lemma rdn_spill_cnt : forall mem cnt,
  rdn rsegs (spill mem cnt) (Z_to_bv 64 (bv_unsigned rsp - 40)) 8%nat
    = Some (word_to_le_bytes 8 cnt).
Proof.
  intros mem cnt. pose proof rsp_lo_num. pose proof rsp_hi_num. unfold spill.
  rewrite rdn_wbytes_disjoint
    by (rewrite ?length_N_to_le_bytes; u_norm; lia).
  apply rdn_wbytes_hit8; u_norm; lia.
Qed.

Lemma rdn_spill_ptr : forall mem cnt,
  rdn rsegs (spill mem cnt) (Z_to_bv 64 (bv_unsigned rsp - 48)) 8%nat
    = Some (word_to_le_bytes 8 sbuf).
Proof.
  intros mem cnt. pose proof rsp_lo_num. pose proof rsp_hi_num. unfold spill.
  apply rdn_wbytes_hit8; u_norm; lia.
Qed.

Lemma src_head_to_read : forall regs mem fdin fdout,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 3 = (0x13800 : word) ->
  reg_get regs 8 = sbuf ->
  reg_get regs 18 = fdin -> reg_get regs 9 = fdout ->
  exists regs',
    bv_unsigned (getr regs' 17) = 63%Z /\
    reg_get regs' 10 = fdin /\ reg_get regs' 11 = sbuf /\
    reg_get regs' 12 = Z_to_bv 64 1024 /\
    reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs' 1 = (0x1109c : word) /\
    reg_get regs' 3 = (0x13800 : word) /\
    reg_get regs' 8 = sbuf /\
    reg_get regs' 9 = fdout /\ reg_get regs' 18 = fdin /\
    msteps rsegs (mkst regs (0x1107c : word) mem rrom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := (0x1117c : word);
         ms_svc_pending := Some (getr regs' 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rrom |}.
Proof.
  intros regs mem fdin fdout H2 H3 H8 H18 H9.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  (* 0x1107c .. 0x1117c — 15 instructions in ONE reflective block: the
     seven read() argument moves, the [jal] into raw_syscall and its
     seven shuffles.  Pure register traffic; the buffer pointer and the
     input fd enter as pins.  The executor stops at the [ecall]. *)
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 69756) mem rrom)
    16%nat (@nil bool) (@nil expr)
    [((8 : reg), EVar 32); ((18 : reg), EVar 33)] [sbuf; fdin]
    (@nil word) R HR Hms.
  { rewrite getr_nz by reg_neq_tac; exact H8. }
  { rewrite getr_nz by reg_neq_tac; exact H18. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  11: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_1117c) eq_refl)
      | apply mst_refl ]. }
  all: s_out HR.
Qed.

(** Post-read (0x11180 ret -> 0x1109c; a0 = block length 1..1024) to the
    write ecall record. *)
Lemma src_read_to_write : forall regs mem fdin fdout cnt,
  reg_get regs 10 = cnt ->
  (1 <= bv_unsigned cnt)%Z -> (bv_unsigned cnt <= 1024)%Z ->
  reg_get regs 1 = (0x1109c : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 3 = (0x13800 : word) ->
  reg_get regs 8 = sbuf ->
  reg_get regs 9 = fdout -> reg_get regs 18 = fdin ->
  (* the two spill slots below the frame are machine stores *)
  mem_grows wmem mem ->
  exists regs',
    bv_unsigned (getr regs' 17) = 64%Z /\
    reg_get regs' 10 = fdout /\ reg_get regs' 11 = sbuf /\
    reg_get regs' 12 = cnt /\ reg_get regs' 8 = sbuf /\
    reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs' 1 = (0x110cc : word) /\
    reg_get regs' 3 = (0x13800 : word) /\
    reg_get regs' 9 = fdout /\ reg_get regs' 18 = fdin /\
    msteps rsegs (mkst regs (0x11180 : word) mem rrom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := (0x1117c : word);
         ms_svc_pending := Some (getr regs' 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := spill mem cnt; ms_rom := rrom |}.
Proof.
  intros regs mem fdin fdout cnt H10 Hc1 Hc2 H1 H2 H3 H8 H9 H18 Hg.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  (* 0x11180 .. 0x1117c — 20 instructions in ONE reflective block:
     raw_syscall's [ret], the two not-taken guards on the delivered
     count, the seven write() argument moves, the two spills of the
     running count/pointer, the [jal] back into raw_syscall and its
     seven shuffles.  The executor stops at the [ecall]. *)
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 70016) mem rrom)
    22%nat [false; false] (@nil expr)
    [((1 : reg), ELit 0x1109c); ((2 : reg), EVar 32); ((8 : reg), EVar 33);
     ((9 : reg), EVar 34); ((10 : reg), EVar 35)]
    [Z_to_bv 64 (bv_unsigned rsp - 48); sbuf; fdout; cnt]
    (@nil word) R HR Hms.
  { store_ok_peel; eapply store_ok_mono; [ exact Hg | ]; solve_store_ok. }
  { store_ok_peel; eapply store_ok_mono; [ exact Hg | ]; solve_store_ok. }
  { apply c_eq_0_false; lia. }
  { apply c_lts_pos_0; lia. }
  { rewrite getr_nz by reg_neq_tac; rewrite H1; bveq. }
  { rewrite getr_nz by reg_neq_tac; exact H2. }
  { rewrite getr_nz by reg_neq_tac; exact H8. }
  { rewrite getr_nz by reg_neq_tac; exact H9. }
  { rewrite getr_nz by reg_neq_tac; exact H10. }
  (* the block's exit memory IS [spill mem cnt] *)
  match type of Hms with
  | msteps _ _ (mkst _ _ ?M _) => assert (HM : M = spill mem cnt)
  end.
  { unfold spill. sym_mem_norm. reflexivity. }
  rewrite HM in Hms. clear HM.
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  11: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_1117c) eq_refl)
      | apply mst_refl ]. }
  all: s_out HR.
Qed.

(** Post-write (0x11180 ret -> 0x110cc; a0 = cnt written) back to the
    loop head (0x1107c). *)
Lemma src_write_to_head : forall regs mem fdin fdout cnt,
  reg_get regs 10 = cnt ->
  (1 <= bv_unsigned cnt)%Z -> (bv_unsigned cnt <= 1024)%Z ->
  reg_get regs 1 = (0x110cc : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 3 = (0x13800 : word) ->
  reg_get regs 8 = sbuf ->
  reg_get regs 9 = fdout -> reg_get regs 18 = fdin ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 40)) 8%nat
    = Some (word_to_le_bytes 8 cnt) ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 48)) 8%nat
    = Some (word_to_le_bytes 8 sbuf) ->
  exists regs',
    reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs' 3 = (0x13800 : word) /\
    reg_get regs' 8 = sbuf /\
    reg_get regs' 9 = fdout /\ reg_get regs' 18 = fdin /\
    msteps rsegs (mkst regs (0x11180 : word) mem rrom)
      (mkst regs' (0x1107c : word) mem rrom).
Proof.
  intros regs mem fdin fdout cnt H10 Hc1 Hc2 H1 H2 H3 H8 H9 H18 Hrc Hrp.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  (* 0x11180 .. 0x1107c — 8 instructions in ONE reflective block:
     raw_syscall's [ret], the not-taken [blez], the two spill reloads
     (named by the read script), the count/pointer update, the
     not-taken [bnez] and the [j] back to the loop head.  Exact fuel:
     one more and the executor would enter the next iteration. *)
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 70016) mem rrom)
    8%nat [false; false] [EVar 33; EVar 34]
    [((1 : reg), ELit 0x110cc); ((2 : reg), EVar 32); ((10 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp - 48); cnt] [sbuf] R HR Hms.
  { apply negb_false_iff; apply c_eq_0_of_u;
    rewrite v_sub_small by lia; lia. }
  { exists (word_to_le_bytes 8 sbuf); split;
      [ exact Hrp | exact (bytes_le_to_Z_8 _) ]. }
  { exists (word_to_le_bytes 8 cnt); split;
      [ exact Hrc | exact (bytes_le_to_Z_8 _) ]. }
  { apply negb_false_iff; apply c_lts_0_pos; lia. }
  { rewrite getr_nz by reg_neq_tac; rewrite H1; bveq. }
  { rewrite getr_nz by reg_neq_tac; exact H2. }
  { rewrite getr_nz by reg_neq_tac; exact H10. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  6: { eapply msteps_trans; [ exact Hms | ]. sym_pc_lit. apply mst_refl. }
  all: s_out HR.
Qed.

(** The register-only loop writes only the buffer (sbuf), disjoint from
    the main-frame slots, so [smem_inv] survives a buffer write. *)
Lemma smem_inv_wtm : forall mem (chunk : list byte),
  smem_inv mem -> (Z.of_nat (length chunk) <= 1024)%Z ->
  smem_inv (write_to_mem mem sbuf chunk).
Proof.
  intros mem chunk (Hra & Hs0 & Hs1 & Hs2 & Hg) Hlen.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  unfold smem_inv.
  repeat apply conj; try solve_mem_grows;
    (rewrite rdn_wtm_out by (rewrite ?u_sbuf; u_norm; first [ lia | left; lia ]);
     assumption).
Qed.

(** The two spill slots ([rsp-48, rsp-32)) are below every callee-saved
    slot the epilogue reloads ([rsp-32, rsp)), so [smem_inv] survives the
    inner loop's spills too. *)
Lemma smem_inv_spill : forall mem cnt,
  smem_inv mem -> smem_inv (spill mem cnt).
Proof.
  intros mem cnt (Hra & Hs0 & Hs1 & Hs2 & Hg).
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  unfold smem_inv, spill.
  repeat apply conj; try solve_mem_grows;
    (repeat rewrite rdn_wbytes_disjoint
       by (rewrite ?length_N_to_le_bytes; u_norm; lia);
     assumption).
Qed.

(* ================================================================= *)
(* End of the copy: both closes, exit 0                               *)
(* ================================================================= *)

(** From raw_syscall's [ret] after a read that delivered 0 bytes: the
    not-taken [bltz], the taken [beqz] into the shutdown tail, both
    closes, [li a0,0] and main's epilogue. *)
Lemma src_eof_tail : forall regs mem model fdin fdout e_in e_out fsv,
  reg_get regs 10 = Z_to_bv 64 0 ->
  reg_get regs 1 = (0x1109c : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 3 = (0x13800 : word) ->
  reg_get regs 8 = sbuf ->
  reg_get regs 9 = fdout -> reg_get regs 18 = fdin ->
  fdin <> fdout ->
  (bv_unsigned fdin < 2 ^ 31)%Z -> (bv_unsigned fdout < 2 ^ 31)%Z ->
  smem_inv mem ->
  fd_lookup (m_fds model) fdin = Some e_in ->
  fd_lookup (m_fds model) fdout = Some e_out ->
  m_halted model = None -> m_vm_lazy model = [] ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x11180 : word) mem rrom) model
    (fun o => o = (Z_to_bv 64 0, fsv)).
Proof.
  intros regs mem model fdin fdout e_in e_out fsv H10 H1 H2 H3 H8 H9 H18 Hneq
    Hfin31 Hfout31 Hsm Hfdin Hfdout Hh Hlazy Hfs.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  (* ret -> 0x1109c; bltz ft; beqz tk -> 0x110e8; sext.w a0,s2; jal close *)
  eapply tfo_msteps.
  { sret (SFv SF_11180) SD_11180 (0x1109c : word).
    step_intro;
      [ reflexivity
      | eapply step_blt_ft;
        [ exact (SFv SF_1109c) | reflexivity | exact SD_1109c
        | getr_resolve; regupd_resolve; rewrite ?H10; exact c_lts_0_0 ]
      | norm_pc ].
    step_intro;
      [ reflexivity
      | eapply step_beq_tk;
        [ exact (SFv SF_110a0) | reflexivity | exact SD_110a0
        | getr_resolve; regupd_resolve; rewrite ?H10; exact c_eq_0_true ]
      | norm_pc ].
    stepiwv (SFv SF_110e8) SD_110e8 fdin
      ltac:(getr_resolve; regupd_resolve; rewrite H18; apply v_addiw_id; exact Hfin31).
    stepj (SFv SF_110ec) SD_110ec.
    apply mst_refl. }
  (* close(fdin) *)
  match goal with
  | |- to_fout _ (mkst ?R _ ?M _) _ _ =>
      destruct (src_close_entry R M fdin (0x110f0 : word) sbuf
                  (0x13800 : word) fdout fdin
          ltac:(regupd_resolve; exact H2)
          ltac:(regupd_resolve; reflexivity)
          ltac:(regupd_resolve; bveq)
          ltac:(regupd_resolve; exact H8)
          ltac:(regupd_resolve; exact H3)
          ltac:(regupd_resolve; exact H9)
          ltac:(regupd_resolve; exact H18)
          ltac:(solve_mem_grows))
        as (regsB & B17 & B10 & B2 & B1 & B8 & B3 & B9 & B18 & HmsB)
  end.
  eapply tfo_msteps; [exact HmsB|].
  eapply tfo_close_rec with (fdv := fdin).
  { exact B17. }
  { exact B10. }
  { exact Hfdin. }
  { fd32_ok. }
  { exact Hh. }
  { exact Hlazy. }
  match goal with
  | |- to_fout _ (mkst ?R _ ?M _) _ _ =>
      destruct (src_close_tail R M (0x110f0 : word) sbuf
                  (0x13800 : word) fdout fdin
          ltac:(regupd_resolve; exact B2)
          ltac:(regupd_resolve; reflexivity)
          ltac:(regupd_resolve; exact B1)
          ltac:(regupd_resolve; exact B8)
          ltac:(regupd_resolve; exact B3)
          ltac:(regupd_resolve; exact B9)
          ltac:(regupd_resolve; exact B18)
          ltac:(bveq)
          ltac:(apply rdn_wbytes_hit8; u_norm; lia))
        as (regsC & C2 & C10 & C1 & C8 & C3 & C9 & C18 & HmsC)
  end.
  eapply tfo_msteps; [norm_pc; exact HmsC|].
  (* sext.w a0,s1; jal close *)
  eapply tfo_msteps.
  { stepiwv (SFv SF_110f0) SD_110f0 fdout
      ltac:(getr_resolve; rewrite C9; apply v_addiw_id; exact Hfout31).
    stepj (SFv SF_110f4) SD_110f4.
    apply mst_refl. }
  match goal with
  | |- to_fout _ (mkst ?R _ ?M _) _ _ =>
      destruct (src_close_entry R M fdout (0x110f8 : word) sbuf
                  (0x13800 : word) fdout fdin
          ltac:(regupd_resolve; exact C2)
          ltac:(regupd_resolve; reflexivity)
          ltac:(regupd_resolve; bveq)
          ltac:(regupd_resolve; exact C8)
          ltac:(regupd_resolve; exact C3)
          ltac:(regupd_resolve; exact C9)
          ltac:(regupd_resolve; exact C18)
          ltac:(solve_mem_grows))
        as (regsD & D17 & D10 & D2 & D1 & D8 & D3 & D9 & D18 & HmsD)
  end.
  eapply tfo_msteps; [exact HmsD|].
  eapply tfo_close_rec with (fdv := fdout).
  { exact D17. }
  { exact D10. }
  { model_simp.
    rewrite fd_lookup_remove_neq by congruence.
    exact Hfdout. }
  { fd32_ok. }
  { model_simp. exact Hh. }
  { exact Hlazy. }
  match goal with
  | |- to_fout _ (mkst ?R _ ?M _) _ _ =>
      destruct (src_close_tail R M (0x110f8 : word) sbuf
                  (0x13800 : word) fdout fdin
          ltac:(regupd_resolve; exact D2)
          ltac:(regupd_resolve; reflexivity)
          ltac:(regupd_resolve; exact D1)
          ltac:(regupd_resolve; exact D8)
          ltac:(regupd_resolve; exact D3)
          ltac:(regupd_resolve; exact D9)
          ltac:(regupd_resolve; exact D18)
          ltac:(bveq)
          ltac:(apply rdn_wbytes_hit8; u_norm; lia))
        as (regsE & E2 & E10 & E1 & E8 & E3 & E9 & E18 & HmsE)
  end.
  eapply tfo_msteps; [norm_pc; exact HmsE|].
  (* li a0,0; epilogue *)
  eapply tfo_msteps.
  { stepiv (SFv SF_110f8) SD_110f8 (Z_to_bv 64 0) ltac:(getr_resolve; bveq).
    apply mst_refl. }
  apply source_fepilogue with (code := Z_to_bv 64 0).
  { regupd_resolve; exact E2. }
  { regupd_resolve; reflexivity. }
  { rewrite u_Z2bv by lia; lia. }
  { destruct Hsm as (Fra & F16 & F24 & F32 & Fg).
    unfold smem_inv.
    repeat apply conj; try solve_mem_grows;
      repeat rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; u_norm; lia);
      assumption. }
  { model_simp. exact Hfs. }
Qed.

(** From the read errno continuation (0x11180 ret -> 0x1109c): exit 5.
    The folder read answers -EISDIR, and the read at [cp_ns_defs.cp_cut]
    -EINVAL, at whatever memory the loop has reached. *)
Lemma src_read_err_tail : forall regs e mem model fsv,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  reg_get regs 10 = errno_ret e ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 1 = (0x1109c : word) ->
  smem_inv mem ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x11180 : word) mem rrom) model
    (fun o => o = (Z_to_bv 64 5, fsv)).
Proof.
  intros regs e mem model fsv He1 He2 H10 H2 H1 Hsm Hfs.
  eapply tfo_msteps.
  { sret (SFv SF_11180) SD_11180 (0x1109c : word).
    step_intro;
      [ reflexivity
      | eapply step_blt_tk;
        [ exact (SFv SF_1109c) | reflexivity | exact SD_1109c
        | getr_resolve; regupd_resolve; rewrite H10; apply c_lts_errno; lia ]
      | norm_pc ].
    stepiv (SFv SF_1111c) SD_1111c (Z_to_bv 64 5) ltac:(getr_resolve; bveq).
    stepj (SFv SF_11120) SD_11120.
    apply mst_refl. }
  apply source_fepilogue with (code := Z_to_bv 64 5).
  - regupd_resolve; exact H2.
  - regupd_resolve; reflexivity.
  - rewrite u_Z2bv by lia; lia.
  - exact Hsm.
  - exact Hfs.
Qed.

(** From the write errno continuation (0x11180 ret -> 0x110cc): the taken
    [blez], [li a0,6] and main's epilogue, exit 6.  The write at
    [cp_ns_defs.cp_cut] answers -EINVAL. *)
Lemma src_write_err_tail : forall regs e mem model fsv,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  reg_get regs 10 = errno_ret e ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 1 = (0x110cc : word) ->
  smem_inv mem ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x11180 : word) mem rrom) model
    (fun o => o = (Z_to_bv 64 6, fsv)).
Proof.
  intros regs e mem model fsv He1 He2 H10 H2 H1 Hsm Hfs.
  eapply tfo_msteps.
  { sret (SFv SF_11180) SD_11180 (0x110cc : word).
    step_intro;
      [ reflexivity
      | eapply step_bge_tk;
        [ exact (SFv SF_110cc) | reflexivity | exact SD_110cc
        | getr_resolve; regupd_resolve; rewrite H10; apply c_lts_0_errno; lia ]
      | norm_pc ].
    stepiv (SFv SF_11124) SD_11124 (Z_to_bv 64 6) ltac:(getr_resolve; bveq).
    stepj (SFv SF_11128) SD_11128.
    apply mst_refl. }
  apply source_fepilogue with (code := Z_to_bv 64 6).
  - regupd_resolve; exact H2.
  - regupd_resolve; reflexivity.
  - rewrite u_Z2bv by lia; lia.
  - exact Hsm.
  - exact Hfs.
Qed.

(* ================================================================= *)
(* The copy loop over a regular file, to its end or to [cp_cut].      *)
(* ================================================================= *)

(** Loop-head register pins. *)
Definition sLH (fdin fdout : word) (regs : bvmap 5 word) : Prop :=
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
  reg_get regs 3 = (0x13800 : word) /\
  reg_get regs 8 = sbuf /\
  reg_get regs 18 = fdin /\ reg_get regs 9 = fdout.

(** The model after [k] bytes of the source inode [i]'s bytes [D] are
    copied into the destination [fe_d] the second open handed out on
    the image [fs1] ([cp_ns_defs.cp_dst_at], [cp_ns_defs.cp_fs_at]). *)
Definition sMI (fs1 : Fs.Fs) (i : Fs.ino) (D : list byte) (fdin fdout : word)
    (fe_d : FdEntry) (k : nat) (model : Model) : Prop :=
  m_halted model = None /\
  m_vm_lazy model = [] /\
  fd_lookup (m_fds model) fdin = Some (FdFile i (nat_to_word k)) /\
  fd_lookup (m_fds model) fdout = Some (cp_dst_at fe_d k) /\
  m_fs model = cp_fs_at fe_d fs1 D k.

Lemma source_loop : forall fs1 i D fdin fdout fe_d,
  Fs.fs_ino_data fs1 i = D ->
  fdin <> fdout ->
  (bv_unsigned fdin < 2 ^ 31)%Z -> (bv_unsigned fdout < 2 ^ 31)%Z ->
  cp_dst_ok fe_d fs1 ->
  forall rem k regs mem model,
  (cp_cut - k < rem)%nat -> (k <= length D)%nat -> (k <= cp_cut)%nat ->
  ((exists q, Z.of_nat k = (1024 * q)%Z) \/ k = length D) ->
  sLH fdin fdout regs -> smem_inv mem -> sMI fs1 i D fdin fdout fe_d k model ->
  to_fout rsegs (mkst regs (0x1107c : word) mem rrom) model
    (cp_file_outcome fe_d fs1 D).
Proof.
  intros fs1 i D fdin fdout fe_d HD Hneq Hfin31 Hfout31 Hdst.
  (* a file destination is not the source's inode once that holds bytes:
     the destination's open left it empty *)
  assert (Hij : forall j o, fe_d = FdFileW j o -> D <> [] -> i <> j).
  { intros j o He HDne Hie. subst j.
    destruct Hdst as [(j' & Hj' & Hd) | [Hj' | Hj']]; rewrite He in Hj';
      try discriminate Hj'.
    injection Hj' as <- _. apply HDne. rewrite <- HD. exact Hd. }
  induction rem as [|rem IH]; intros k regs mem model Hrem Hk Hkc Hdiv HLH Hsm HMI.
  { lia. }
  destruct HLH as (H2 & H3 & H8 & H18 & H9).
  destruct HMI as (Hh & Hlazy & Hfdin & Hfdout & Hfs).
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof cp_cut_Z as Hcut.
  assert (HkZ : (Z.of_nat k < 2^64)%Z) by lia.
  destruct (src_head_to_read regs mem fdin fdout H2 H3 H8 H18 H9)
    as (regsR & R17 & R10 & R11 & R12 & R2 & R1 & R3 & R8 & R9 & R18 & HmsR).
  eapply tfo_msteps; [exact HmsR|].
  assert (Haok1 : access_okb sbuf (bv_unsigned (Z_to_bv 64 1024)) = true).
  { (* the buffer is a link-time constant far under [State.TASK_SIZE] *)
    apply access_okb_intro. rewrite u_sbuf.
    rewrite u_Z2bv by lia. unfold TASK_SIZE. lia. }
  destruct (Nat.eq_dec k cp_cut) as [Hkcut | Hkcut].
  { (* ============ the read at [cp_cut]: -EINVAL, exit 5 ============ *)
    eapply tfo_read_einval_rec with (p := i) (off := nat_to_word k)
      (buf := sbuf) (cnt := Z_to_bv 64 1024) (fdv := fdin).
    { exact R17. } { exact R10. } { exact R11. } { exact R12. }
    { exact Hfdin. }
    { fd32_ok. }
    { exact Haok1. }
    { rewrite Hkcut, u_Z2bv by lia. apply cp_pos_at_cut. lia. }
    { exact Hh. }
    { exact Hlazy. }
    fnorm_pc.
    apply (tfo_equiv rsegs _ _ (fun o => o = (Z_to_bv 64 5, m_fs model))).
    2:{ intro o. unfold cp_file_outcome.
        replace (Z.of_nat (length D) <? 2 ^ 63 - 1024)%Z with false
          by (symmetry; apply Z.ltb_ge; lia).
        rewrite Hfs, <- Hkcut, (cp_fs_at_copied fe_d fs1 D k) by lia.
        split; intro Ho; exact Ho. }
    apply (src_read_err_tail (regupd regsR 10 (errno_ret EINVAL)) EINVAL mem model
             (m_fs model)).
    - unfold EINVAL; lia.
    - unfold EINVAL; lia.
    - regupd_resolve; reflexivity.
    - regupd_resolve; exact R2.
    - regupd_resolve; exact R1.
    - exact Hsm.
    - reflexivity. }
  (* below the cut the read passes the position test *)
  assert (Hkc' : (Z.of_nat k < Z.of_nat cp_cut)%Z) by lia.
  set (chunk := file_read D (nat_to_word k) (Z_to_bv 64 1024)).
  assert (Hclen : length chunk = Nat.min 1024 (length D - k)%nat)
    by (unfold chunk; apply cp_chunk_len; exact HkZ).
  assert (Hc1024 : (length chunk <= 1024)%nat) by lia.
  eapply tfo_read_rec with (p := i) (off := nat_to_word k) (data := D)
    (buf := sbuf) (cnt := Z_to_bv 64 1024) (fdv := fdin).
  { exact R17. } { exact R10. } { exact R11. } { exact R12. }
  { exact Hfdin. }
  { fd32_ok. }
  { rewrite Hfs. apply cp_fs_at_data_src; [exact HD | exact Hk | exact Hij]. }
  { exact (source_buf_wseg vt). }
  { rewrite u_Z2bv by lia. unfold rw_bytes_max. lia. }
  { rewrite u_Z2bv by lia. lia. }
  { exact Haok1. }
  { rewrite u_Z2bv by lia. apply cp_pos_ok; lia. }
  { exact Hh. }
  { exact Hlazy. }
  fold chunk.
  destruct (Nat.eq_dec k (length D)) as [Heq | HneD].
  - (* ================= EOF: close both, exit 0 ================= *)
    assert (Hchn : chunk = [])
      by (unfold chunk; apply file_read_nil; rewrite wtn_ntw by lia; lia).
    rewrite Hchn. cbn [write_to_mem].
    replace (len_word (@nil byte)) with (Z_to_bv 64 0) by reflexivity.
    fnorm_pc.
    apply (tfo_equiv rsegs _ _ (fun o => o = (Z_to_bv 64 0, cp_copied fe_d fs1 D))).
    2:{ intro o. unfold cp_file_outcome.
        replace (Z.of_nat (length D) <? 2 ^ 63 - 1024)%Z with true
          by (symmetry; apply Z.ltb_lt; lia).
        split; intro Ho; exact Ho. }
    apply (src_eof_tail _ _ _ fdin fdout (FdFile i (nat_to_word k + Z_to_bv 64 0))
             (cp_dst_at fe_d k)).
    + regupd_resolve; reflexivity.
    + regupd_resolve; exact R1.
    + regupd_resolve; exact R2.
    + regupd_resolve; exact R3.
    + regupd_resolve; exact R8.
    + regupd_resolve; exact R9.
    + regupd_resolve; exact R18.
    + exact Hneq.
    + exact Hfin31.
    + exact Hfout31.
    + exact Hsm.
    + model_simp. apply fd_lookup_insert_eq.
    + model_simp. rewrite fd_lookup_insert_neq by congruence. exact Hfdout.
    + exact Hh.
    + exact Hlazy.
    + model_simp. rewrite Hfs, Heq. apply cp_fs_at_final.
  - (* ================= one more chunk: write it back ================= *)
    assert (HkltD : (k < length D)%nat) by lia.
    destruct Hdiv as [(q & Hq) | HkD]; [|lia].
    (* a whole chunk fits before [cp_cut] *)
    assert (Hroom : (Z.of_nat k + 1024 <= Z.of_nat cp_cut)%Z)
      by exact (cp_room k q Hq Hkc').
    assert (Hc1 : (1 <= length chunk)%nat) by lia.
    assert (HuLen : bv_unsigned (len_word chunk) = Z.of_nat (length chunk))
      by (apply u_len_word; lia).
    assert (Haok : access_okb sbuf (bv_unsigned (len_word chunk)) = true).
    { apply access_okb_intro. rewrite u_sbuf, HuLen. unfold TASK_SIZE. lia. }
    eapply tfo_msteps.
    { norm_pc. apply mst_refl. }
    match goal with
    | |- to_fout _ (mkst ?R _ ?M _) _ _ =>
        destruct (src_read_to_write R M fdin fdout (len_word chunk)
            ltac:(regupd_resolve; reflexivity)
            ltac:(lia) ltac:(lia)
            ltac:(regupd_resolve; exact R1)
            ltac:(regupd_resolve; exact R2)
            ltac:(regupd_resolve; exact R3)
            ltac:(regupd_resolve; exact R8)
            ltac:(regupd_resolve; exact R9)
            ltac:(regupd_resolve; exact R18)
            ltac:(solve_mem_grows))
          as (regsW & W17 & W10 & W11 & W12 & W8 & W2 & W1 & W3 & W9 & W18 & HmsW)
    end.
    eapply tfo_msteps; [exact HmsW|].
    assert (Hrd : rdn rsegs (spill (write_to_mem mem sbuf chunk) (len_word chunk)) sbuf
                    (word_to_nat (len_word chunk)) = Some chunk).
    { rewrite wtn_len_word by lia.
      unfold spill.
      rewrite !rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes, ?u_sbuf; u_norm; lia).
      apply rdn_write_to_mem. rewrite u_sbuf. lia. }
    (* what follows the write, whatever the destination took *)
    assert (Hnext : forall model',
      sMI fs1 i D fdin fdout fe_d (k + length chunk) model' ->
      to_fout rsegs (mkst (regupd regsW 10 (len_word chunk)) (v_addi (0x1117c : word) 4)
                          (spill (write_to_mem mem sbuf chunk) (len_word chunk)) rrom)
        model' (cp_file_outcome fe_d fs1 D)).
    { intros model' HMI'.
      eapply tfo_msteps.
      { norm_pc. apply mst_refl. }
      match goal with
      | |- to_fout _ (mkst ?R _ ?M _) _ _ =>
          destruct (src_write_to_head R M fdin fdout (len_word chunk)
              ltac:(regupd_resolve; reflexivity)
              ltac:(lia) ltac:(lia)
              ltac:(regupd_resolve; exact W1)
              ltac:(regupd_resolve; exact W2)
              ltac:(regupd_resolve; exact W3)
              ltac:(regupd_resolve; exact W8)
              ltac:(regupd_resolve; exact W9)
              ltac:(regupd_resolve; exact W18)
              ltac:(apply rdn_spill_cnt)
              ltac:(apply rdn_spill_ptr))
            as (regsH & G2 & G3 & G8 & G9 & G18 & HmsH)
      end.
      eapply tfo_msteps; [exact HmsH|].
      apply (IH (k + length chunk)%nat).
      { lia. }
      { lia. }
      { lia. }
      { destruct (Nat.le_gt_cases 1024 (length D - k)) as [Hf | Hs].
        - left. exists (q + 1)%Z. rewrite Nat2Z.inj_add, Hq. lia.
        - right. lia. }
      { unfold sLH. auto. }
      { apply smem_inv_spill. apply smem_inv_wtm; [exact Hsm | lia]. }
      { exact HMI'. } }
    destruct Hdst as [(j & -> & Hjd) | [-> | ->]].
    + (* a regular file: it takes the chunk at offset [k] *)
      eapply tfo_write_rec with (p := j) (off := nat_to_word k)
        (data := firstn k D) (bs := chunk) (buf := sbuf)
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
      { rewrite HuLen. apply cp_pos_ok; lia. }
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
(* /dev/urandom into a regular file, to [cp_cut]                       *)
(* ================================================================= *)

(** The model after [k] bytes of the declared stream [ur] are copied from
    /dev/urandom into the destination file [j], empty in [fs1]
    ([cp_ns_defs.cp_ufs_at]). *)
Definition sMU (fs1 : Fs.Fs) (j : Fs.ino) (ur : InputStream) (fdin fdout : word)
    (k : nat) (model : Model) : Prop :=
  m_halted model = None /\
  m_vm_lazy model = [] /\
  fd_lookup (m_fds model) fdin = Some (FdUrandom true false) /\
  fd_lookup (m_fds model) fdout = Some (FdFileW j (nat_to_word k)) /\
  m_fs model = cp_ufs_at fs1 j ur k /\
  m_urandom model = snd (stream_take ur k).

(** Every read takes a whole 1024-byte chunk of the endless stream, and
    every write puts it at the destination's offset, until the write at
    [cp_cut] answers -EINVAL and both binaries exit 6, the file holding
    the stream's first [cp_cut] bytes. *)
Lemma source_uloop : forall fs1 j ur fdin fdout,
  Fs.fs_ino_data fs1 j = [] ->
  stream_infinite ur ->
  fdin <> fdout ->
  (bv_unsigned fdin < 2 ^ 31)%Z -> (bv_unsigned fdout < 2 ^ 31)%Z ->
  forall rem k regs mem model,
  (cp_cut - k < rem)%nat -> (k <= cp_cut)%nat ->
  (exists q, Z.of_nat k = (1024 * q)%Z) ->
  sLH fdin fdout regs -> smem_inv mem -> sMU fs1 j ur fdin fdout k model ->
  to_fout rsegs (mkst regs (0x1107c : word) mem rrom) model
    (fun o => o = (Z_to_bv 64 6, cp_copied (FdFileW j (Z_to_bv 64 0)) fs1
                                   (fst (stream_take ur cp_cut)))).
Proof.
  intros fs1 j ur fdin fdout Hj Hinf Hneq Hfin31 Hfout31.
  induction rem as [|rem IH]; intros k regs mem model Hrem Hkc (q & Hq) HLH Hsm HMU.
  { lia. }
  destruct HLH as (H2 & H3 & H8 & H18 & H9).
  destruct HMU as (Hh & Hlazy & Hfdin & Hfdout & Hfs & Hur).
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof cp_cut_Z as Hcut.
  assert (HkZ : (Z.of_nat k < 2^64)%Z) by lia.
  assert (Hinfk : stream_infinite (m_urandom model))
    by (rewrite Hur; exact (stream_infinite_rest k ur Hinf)).
  destruct (src_head_to_read regs mem fdin fdout H2 H3 H8 H18 H9)
    as (regsR & R17 & R10 & R11 & R12 & R2 & R1 & R3 & R8 & R9 & R18 & HmsR).
  eapply tfo_msteps; [exact HmsR|].
  eapply tfo_read_urandom_rec with (wr := false) (fdv := fdin) (buf := sbuf)
    (cnt := Z_to_bv 64 1024).
  { exact R17. } { exact R10. } { exact R11. } { exact R12. }
  { exact Hfdin. }
  { fd32_ok. }
  { exact (source_buf_wseg vt). }
  { rewrite u_Z2bv by lia. unfold page_size. lia. }
  { apply access_okb_intro. rewrite u_sbuf. rewrite u_Z2bv by lia.
    unfold TASK_SIZE. lia. }
  { exact Hinfk. }
  { exact Hh. }
  { exact Hlazy. }
  change (bv_unsigned (Z_to_bv 64 1024)) with 1024%Z.
  set (chunk := fst (stream_take_z (m_urandom model) 1024)).
  assert (Hcn : Z.of_nat (length chunk) = 1024%Z)
    by (apply stream_take_z_infinite_length; [exact Hinfk | lia]).
  assert (Hlw : len_word chunk = Z_to_bv 64 1024)
    by (unfold len_word; rewrite Hcn; reflexivity).
  assert (HuLen : bv_unsigned (len_word chunk) = 1024%Z)
    by (rewrite Hlw; apply u_Z2bv; lia).
  assert (Hchunk : chunk = fst (stream_take (snd (stream_take ur k)) 1024))
    by (unfold chunk; rewrite stream_take_z_eq, Hur; reflexivity).
  assert (Haok : access_okb sbuf (bv_unsigned (len_word chunk)) = true).
  { apply access_okb_intro. rewrite u_sbuf, HuLen. unfold TASK_SIZE. lia. }
  rewrite <- Hlw.
  eapply tfo_msteps.
  { norm_pc. apply mst_refl. }
  match goal with
  | |- to_fout _ (mkst ?R _ ?M _) _ _ =>
      destruct (src_read_to_write R M fdin fdout (len_word chunk)
          ltac:(regupd_resolve; reflexivity)
          ltac:(lia) ltac:(lia)
          ltac:(regupd_resolve; exact R1)
          ltac:(regupd_resolve; exact R2)
          ltac:(regupd_resolve; exact R3)
          ltac:(regupd_resolve; exact R8)
          ltac:(regupd_resolve; exact R9)
          ltac:(regupd_resolve; exact R18)
          ltac:(solve_mem_grows))
        as (regsW & W17 & W10 & W11 & W12 & W8 & W2 & W1 & W3 & W9 & W18 & HmsW)
  end.
  eapply tfo_msteps; [exact HmsW|].
  assert (Hsm' : smem_inv (spill (write_to_mem mem sbuf chunk) (len_word chunk))).
  { apply smem_inv_spill. apply smem_inv_wtm; [exact Hsm | lia]. }
  set (m1 := with_urandom (snd (stream_take_z (m_urandom model) 1024)) model).
  assert (Hm1fds : m_fds m1 = m_fds model) by reflexivity.
  assert (Hm1fs : m_fs m1 = m_fs model) by reflexivity.
  destruct (Nat.eq_dec k cp_cut) as [Hkcut | Hkcut].
  - (* ============ the write at [cp_cut]: -EINVAL, exit 6 ============ *)
    eapply tfo_write_einval_rec with (p := j) (off := nat_to_word k)
      (buf := sbuf) (cnt := len_word chunk) (fdv := fdout).
    { exact W17. } { exact W10. } { exact W11. } { exact W12. }
    { rewrite Hm1fds. exact Hfdout. }
    { fd32_ok. }
    { rewrite HuLen. unfold rw_bytes_max. lia. }
    { exact Haok. }
    { rewrite HuLen, Hkcut. apply cp_pos_at_cut. lia. }
    { exact Hh. }
    { exact Hlazy. }
    match goal with
    | |- context [mkst _ ?p _ _] => replace p with (0x11180 : word) by bveq
    end.
    apply (src_write_err_tail (regupd regsW 10 (errno_ret EINVAL)) EINVAL
             (spill (write_to_mem mem sbuf chunk) (len_word chunk)) m1).
    + unfold EINVAL; lia.
    + unfold EINVAL; lia.
    + regupd_resolve; reflexivity.
    + regupd_resolve; exact W2.
    + regupd_resolve; exact W1.
    + exact Hsm'.
    + rewrite Hm1fs, Hfs, <- Hkcut. apply cp_ufs_at_copied; [exact Hinf | lia].
  - (* ============ below the cut: the chunk lands at [k] ============ *)
    assert (Hkc' : (Z.of_nat k < Z.of_nat cp_cut)%Z) by lia.
    assert (Hroom : (Z.of_nat k + 1024 <= Z.of_nat cp_cut)%Z)
      by exact (cp_room k q Hq Hkc').
    assert (Hrd : rdn rsegs (spill (write_to_mem mem sbuf chunk) (len_word chunk)) sbuf
                    (word_to_nat (len_word chunk)) = Some chunk).
    { rewrite wtn_len_word by lia.
      unfold spill.
      rewrite !rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes, ?u_sbuf; u_norm; lia).
      apply rdn_write_to_mem. rewrite u_sbuf. lia. }
    assert (Hdata : Fs.fs_ino_data (m_fs m1) j = fst (stream_take ur k))
      by (rewrite Hm1fs, Hfs; apply cp_ufs_at_data; exact Hj).
    assert (Hdlen : length (fst (stream_take ur k)) = k)
      by exact (stream_take_infinite_length k ur Hinf).
    eapply tfo_write_rec with (p := j) (off := nat_to_word k)
      (data := fst (stream_take ur k)) (bs := chunk) (buf := sbuf)
      (cnt := len_word chunk) (fdv := fdout).
    { exact W17. } { exact W10. } { exact W11. } { exact W12. }
    { rewrite Hm1fds. exact Hfdout. }
    { fd32_ok. }
    { exact Hrd. }
    { rewrite HuLen. unfold rw_bytes_max. lia. }
    { exact Hdata. }
    { apply file_gap_in_range. rewrite u_ntw by lia. rewrite Hdlen.
      unfold rw_bytes_max. lia. }
    { exact Haok. }
    { rewrite HuLen. apply cp_pos_ok; lia. }
    { exact Hh. }
    { exact Hlazy. }
    eapply tfo_msteps.
    { norm_pc. apply mst_refl. }
    match goal with
    | |- to_fout _ (mkst ?R _ ?M _) _ _ =>
        destruct (src_write_to_head R M fdin fdout (len_word chunk)
            ltac:(regupd_resolve; reflexivity)
            ltac:(lia) ltac:(lia)
            ltac:(regupd_resolve; exact W1)
            ltac:(regupd_resolve; exact W2)
            ltac:(regupd_resolve; exact W3)
            ltac:(regupd_resolve; exact W8)
            ltac:(regupd_resolve; exact W9)
            ltac:(regupd_resolve; exact W18)
            ltac:(apply rdn_spill_cnt)
            ltac:(apply rdn_spill_ptr))
          as (regsH & G2 & G3 & G8 & G9 & G18 & HmsH)
    end.
    eapply tfo_msteps; [exact HmsH|].
    apply (IH (k + 1024)%nat).
    { lia. }
    { lia. }
    { exists (q + 1)%Z. rewrite Nat2Z.inj_add, Hq. lia. }
    { unfold sLH. auto. }
    { exact Hsm'. }
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    { model_simp. exact Hh. }
    { exact Hlazy. }
    { model_simp.
      rewrite fd_lookup_insert_neq by congruence.
      exact Hfdin. }
    { model_simp.
      rewrite fd_lookup_insert_eq.
      rewrite len_word_ntw.
      replace (length chunk) with 1024%nat by lia.
      rewrite ntw_add. reflexivity. }
    { model_simp. rewrite Hm1fs, Hfs.
      apply cp_ufs_at_step; [exact HkZ | exact Hchunk | exact Hinf]. }
    { transitivity (snd (stream_take_z (m_urandom model) 1024)); [reflexivity|].
      rewrite stream_take_z_eq, Hur.
      change (Z.to_nat 1024) with 1024%nat.
      (* over a variable count: the kernel check of the same equation at
         the numeral [1024] does not finish *)
      assert (E : forall n, snd (stream_take ur (k + n))
                            = snd (stream_take (snd (stream_take ur k)) n))
        by (intro n; rewrite (stream_take_add k n ur); reflexivity).
      rewrite E. reflexivity. }
Qed.

(* ================================================================= *)
(* The endless copies: a silent loop over the read anchors            *)
(* ================================================================= *)

(** Loop read-anchor register pins ([src_head_to_read]'s conclusion). *)
Definition sRpins (regs : bvmap 5 word) (fdin fdout : word) : Prop :=
  bv_unsigned (getr regs 17) = 63%Z /\
  reg_get regs 10 = fdin /\ reg_get regs 11 = sbuf /\
  reg_get regs 12 = Z_to_bv 64 1024 /\
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
  reg_get regs 1 = (0x1109c : word) /\
  reg_get regs 3 = (0x13800 : word) /\
  reg_get regs 8 = sbuf /\
  reg_get regs 9 = fdout /\ reg_get regs 18 = fdin.

Definition rdrec (regs : bvmap 5 word) (mem : word -> option byte)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := (0x1117c : word);
     ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rrom |}.

(** THE READ ANCHORS of an endless copy: the read ecall of the loop, the
    source and destination descriptors as [cp_ns_defs.cp_emodel] keeps
    them. *)
Definition sAnchor (c : config) : Prop :=
  exists fdin fdout regs mem model,
    fdin <> fdout /\ fd32 fdin = fdin /\ fd32 fdout = fdout /\
    sRpins regs fdin fdout /\ smem_inv mem /\
    cp_emodel fdin fdout model /\ c = mkCfg (rdrec regs mem) model.

(** From raw_syscall's [ret] after the write back to the next read
    anchor. *)
Lemma src_endless_next : forall regs mem model fdin fdout cnt,
  fdin <> fdout -> fd32 fdin = fdin -> fd32 fdout = fdout ->
  reg_get regs 10 = cnt ->
  (1 <= bv_unsigned cnt)%Z -> (bv_unsigned cnt <= 1024)%Z ->
  reg_get regs 1 = (0x110cc : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 3 = (0x13800 : word) ->
  reg_get regs 8 = sbuf ->
  reg_get regs 9 = fdout -> reg_get regs 18 = fdin ->
  smem_inv mem ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 40)) 8%nat
    = Some (word_to_le_bytes 8 cnt) ->
  rdn rsegs mem (Z_to_bv 64 (bv_unsigned rsp - 48)) 8%nat
    = Some (word_to_le_bytes 8 sbuf) ->
  cp_emodel fdin fdout model ->
  fpath rsegs sAnchor (mkCfg (mkst regs (0x11180 : word) mem rrom) model).
Proof.
  intros regs mem model fdin fdout cnt Hne Hfin32 Hfout32 H10 Hc1 Hc2 H1 H2 H3 H8
    H9 H18 Hsm Hrc Hrp HM.
  destruct (src_write_to_head regs mem fdin fdout cnt H10 Hc1 Hc2 H1 H2 H3 H8 H9 H18
              Hrc Hrp)
    as (regsH & G2 & G3 & G8 & G9 & G18 & HmsH).
  destruct (src_head_to_read regsH mem fdin fdout G2 G3 G8 G18 G9)
    as (regsR & Q17 & Q10 & Q11 & Q12 & Q2 & Q1 & Q3 & Q8 & Q9 & Q18 & HmsR).
  pose proof HM as (Hh & Hlazy & _).
  eapply fpath_msteps; [exact HmsH | exact Hh | exact Hlazy |].
  eapply fpath_msteps; [exact HmsR | exact Hh | exact Hlazy |].
  apply fp_anchor.
  exists fdin, fdout, regsR, mem, model.
  split; [exact Hne|]. split; [exact Hfin32|]. split; [exact Hfout32|].
  split; [unfold sRpins; tauto|].
  split; [exact Hsm|].
  split; [exact HM | reflexivity].
Qed.

(** The write of an endless copy, from its ecall: whichever device the
    destination is, the one resolution is silent and the loop goes on to
    the next read anchor. *)
Lemma src_endless_write : forall regsW mem model fdin fdout chunk,
  fdin <> fdout -> fd32 fdin = fdin -> fd32 fdout = fdout ->
  bv_unsigned (getr regsW 17) = 64%Z ->
  reg_get regsW 10 = fdout -> reg_get regsW 11 = sbuf ->
  reg_get regsW 12 = len_word chunk -> reg_get regsW 8 = sbuf ->
  reg_get regsW 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regsW 1 = (0x110cc : word) ->
  reg_get regsW 3 = (0x13800 : word) ->
  reg_get regsW 9 = fdout -> reg_get regsW 18 = fdin ->
  (1 <= length chunk <= 1024)%nat ->
  smem_inv mem ->
  m_halted model = None -> m_vm_lazy model = [] ->
  cp_esrc fdin model -> cp_edst fdout model ->
  fpath rsegs sAnchor
    (mkCfg {| ms_regs := regsW; ms_fregs := fp_regs; ms_pc_val := (0x1117c : word);
              ms_svc_pending := Some (getr regsW 17); ms_resv := None; ms_fcsr := fp_csr;
              ms_mem := spill (write_to_mem mem sbuf chunk) (len_word chunk);
              ms_rom := rrom |} model).
Proof.
  intros regsW mem model fdin fdout chunk Hne Hfin32 Hfout32 W17 W10 W11 W12 W8 W2
    W1 W3 W9 W18 Hlen Hsm Hh Hlazy Hsrc Hdst.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  assert (HuLen : bv_unsigned (len_word chunk) = Z.of_nat (length chunk))
    by (apply u_len_word; lia).
  assert (Haok : access_okb sbuf (bv_unsigned (len_word chunk)) = true).
  { apply access_okb_intro. rewrite u_sbuf, HuLen. unfold TASK_SIZE. lia. }
  assert (Hrd : rdn rsegs (spill (write_to_mem mem sbuf chunk) (len_word chunk)) sbuf
                  (word_to_nat (len_word chunk)) = Some chunk).
  { rewrite wtn_len_word by lia.
    unfold spill.
    rewrite !rdn_wbytes_below
      by (rewrite ?length_N_to_le_bytes, ?u_sbuf; u_norm; lia).
    apply rdn_write_to_mem. rewrite u_sbuf. lia. }
  assert (Hsm' : smem_inv (spill (write_to_mem mem sbuf chunk) (len_word chunk))).
  { apply smem_inv_spill. apply smem_inv_wtm; [exact Hsm | lia]. }
  (* from the write's return, whatever the destination took *)
  assert (Hnext : forall model',
    cp_emodel fdin fdout model' ->
    fpath rsegs sAnchor
      (mkCfg (mkst (regupd regsW 10 (len_word chunk)) (v_addi (0x1117c : word) 4)
                   (spill (write_to_mem mem sbuf chunk) (len_word chunk)) rrom) model')).
  { intros model' HM'.
    match goal with
    | |- fpath _ _ (mkCfg (mkst _ ?p _ _) _) => replace p with (0x11180 : word) by bveq
    end.
    apply (src_endless_next _ _ model' fdin fdout (len_word chunk) Hne Hfin32 Hfout32).
    - regupd_resolve; reflexivity.
    - lia.
    - lia.
    - regupd_resolve; exact W1.
    - regupd_resolve; exact W2.
    - regupd_resolve; exact W3.
    - regupd_resolve; exact W8.
    - regupd_resolve; exact W9.
    - regupd_resolve; exact W18.
    - exact Hsm'.
    - apply rdn_spill_cnt.
    - apply rdn_spill_ptr.
    - exact HM'. }
  match goal with
  | |- fpath _ _ (mkCfg ?REC _) => set (wrec := REC)
  end.
  assert (HgW0 : ms_gpr wrec 0 = fdout)
    by (unfold wrec; rewrite record_gpr, arg_reg_0; exact W10).
  assert (HgW1 : ms_gpr wrec 1 = sbuf)
    by (unfold wrec; rewrite record_gpr, arg_reg_1; exact W11).
  assert (HgW2 : ms_gpr wrec 2 = len_word chunk)
    by (unfold wrec; rewrite record_gpr, arg_reg_2; exact W12).
  destruct Hdst as [(rd & Hfd) | (rd & Hfd)].
  - (* /dev/null: the count *)
    destruct (write_null_spec_rec rsegs regsW (0x1117c : word)
                (spill (write_to_mem mem sbuf chunk) (len_word chunk)) rrom model
                fdout rd sbuf (len_word chunk) W17 W10 W11 W12 Hfd Hfout32 Haok
                ltac:(rewrite HuLen; unfold rw_bytes_max; lia))
      as [Huniq Hnu].
    apply (fpath_sys_det rsegs sAnchor wrec model (getr regsW 17) _ _ eq_refl Hh Hlazy
             Huniq Hnu).
    + exact Hh.
    + exact Hlazy.
    + unfold wrec. rewrite adv_eff_ret.
      apply Hnext.
      split; [exact Hh|]. split; [exact Hlazy|].
      split; [exact Hsrc|].
      left. exists rd. exact Hfd.
  - (* /dev/urandom: the whole count of a readable buffer *)
    destruct (write_urandom_spec_rec rsegs regsW (0x1117c : word)
                (spill (write_to_mem mem sbuf chunk) (len_word chunk)) model
                fdout rd sbuf (len_word chunk) chunk W17 W10 W11 W12 Hfd Hfout32 Hrd Haok
                ltac:(rewrite HuLen; unfold page_size; lia))
      as [Huniq Hnu].
    apply (fpath_sys_det rsegs sAnchor wrec model (getr regsW 17) _ _ eq_refl Hh Hlazy
             Huniq Hnu).
    + exact Hh.
    + exact Hlazy.
    + unfold wrec. rewrite adv_eff_ret_copyins.
      apply Hnext.
      split; [exact Hh|]. split; [exact Hlazy|].
      split; [exact Hsrc|].
      right. exists rd. exact Hfd.
Qed.

(** EVERY READ ANCHOR IS SILENT ONTO A PATH TO THE NEXT ONE: /dev/urandom
    delivers the whole count, and the device the write goes to takes the
    chunk whole ([src_endless_write]). *)
Lemma src_endless_anchored : fanchored rsegs sAnchor.
Proof.
  intros a Ha.
  destruct Ha as (fdin & fdout & regs & mem & model & Hne & Hfin32 & Hfout32 & Hpins
                  & Hsm & HM & ->).
  destruct Hpins as (R17 & R10 & R11 & R12 & R2 & R1 & R3 & R8 & R9 & R18).
  destruct HM as (Hh & Hlazy & Hsrc & Hdst).
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  exists (rdrec regs mem), model, (getr regs 17).
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hh|]. split; [exact Hlazy|].
  assert (Hg0 : ms_gpr (rdrec regs mem) 0 = fdin)
    by (unfold rdrec; rewrite record_gpr, arg_reg_0; exact R10).
  assert (Hg1 : ms_gpr (rdrec regs mem) 1 = sbuf)
    by (unfold rdrec; rewrite record_gpr, arg_reg_1; exact R11).
  assert (Hg2 : ms_gpr (rdrec regs mem) 2 = Z_to_bv 64 1024)
    by (unfold rdrec; rewrite record_gpr, arg_reg_2; exact R12).
  (* what follows a read that delivered [chunk] *)
  assert (Hafter : forall chunk model',
    (1 <= length chunk <= 1024)%nat ->
    m_halted model' = None -> m_vm_lazy model' = [] ->
    cp_esrc fdin model' -> cp_edst fdout model' ->
    fpath rsegs sAnchor
      (mkCfg (mkst (regupd regs 10 (len_word chunk)) (0x11180 : word)
                   (write_to_mem mem sbuf chunk) rrom) model')).
  { intros chunk model' Hlen Hh' Hl' Hsrc' Hdst'.
    assert (HuLen : bv_unsigned (len_word chunk) = Z.of_nat (length chunk))
      by (apply u_len_word; lia).
    destruct (src_read_to_write (regupd regs 10 (len_word chunk))
                (write_to_mem mem sbuf chunk) fdin fdout (len_word chunk))
      as (regsW & W17 & W10 & W11 & W12 & W8 & W2 & W1 & W3 & W9 & W18 & HmsW);
      [ regupd_resolve; reflexivity | lia | lia
      | regupd_resolve; exact R1 | regupd_resolve; exact R2
      | regupd_resolve; exact R3 | regupd_resolve; exact R8
      | regupd_resolve; exact R9 | regupd_resolve; exact R18
      | solve_mem_grows | ].
    eapply fpath_msteps; [exact HmsW | exact Hh' | exact Hl' |].
    exact (src_endless_write regsW mem model' fdin fdout chunk Hne Hfin32 Hfout32
             W17 W10 W11 W12 W8 W2 W1 W3 W9 W18 Hlen Hsm Hh' Hl' Hsrc' Hdst'). }
  (* /dev/urandom: the whole count, from the declared endless stream *)
  destruct Hsrc as (Hfin & Hinf).
  destruct (read_urandom_spec_rec rsegs regs (0x1117c : word) mem rrom model fdin false
              sbuf (Z_to_bv 64 1024) R17 R10 R11 R12 Hfin Hfin32 (source_buf_wseg vt)
              ltac:(rewrite u_Z2bv by lia; unfold page_size; lia)
              ltac:(apply access_okb_intro; rewrite u_sbuf; rewrite u_Z2bv by lia;
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
  rewrite (delivered_writes_ne sbuf chunk Hcne).
  unfold rdrec. rewrite adv_apply_write.
  match goal with
  | |- context [mkst _ ?p _ _] => replace p with (0x11180 : word) by bveq
  end.
  split; [reflexivity|]. split; [exact Hh|]. split; [exact Hlazy|].
  rewrite <- Hlw.
  apply (Hafter chunk); [exact Hc | exact Hh | exact Hlazy | |].
  + cbn [cp_esrc]. split; [exact Hfin|].
    exact (stream_take_z_infinite_rest (m_urandom model) 1024 Hinf).
  + exact Hdst.
Qed.

(* ================================================================= *)
(* argc >= 3                                                          *)
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
  rdn rsegs emem (rsp + nat_to_word (8 + 8 * 1)) 8%nat
    = Some (word_le8 psrc).
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  rewrite rdn_emem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
  unfold psrc. apply read_argv_ptr_k; [lia | apply source_bsb_nw].
Qed.

Lemma read_pdst_f :
  rdn rsegs fmem (rsp + nat_to_word (8 + 8 * 2)) 8%nat
    = Some (word_le8 pdst).
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
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
  apply (read_cstr_argv rsegs fmem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x1112c))
           rsp rbrk rrnd 1 Hva Hlau ltac:(lia)).
  intros a n Ha Hn. exact (rdn_fmem_above a n Ha Hn).
Qed.

Lemma source_cstr_dst :
  read_cstr (mrb rsegs fmem) pdst
  = if Nat.ltb (length dst) path_max then CstrOk dst else CstrTooLong.
Proof.
  unfold pdst.
  apply (read_cstr_argv rsegs fmem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x1112c))
           rsp rbrk rrnd 2 Hva Hlau ltac:(lia)).
  intros a n Ha Hn. exact (rdn_fmem_above a n Ha Hn).
Qed.

(* ============ _start + main's head, to the first openat ecall ==== *)
Lemma source_to_open1 :
  exists regs1,
    reg_get regs1 1 = (0x11040 : word) /\
    reg_get regs1 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs1 3 = (0x13800 : word) /\
    reg_get regs1 8 = Z_to_bv 64 (bv_unsigned rsp + 8) /\
    bv_unsigned (getr regs1 17) = 56%Z /\
    reg_get regs1 10 = AT_FDCWD /\
    reg_get regs1 11 = psrc /\
    reg_get regs1 12 = Z_to_bv 64 0 /\
    msteps rsegs
      (init_machine_state rsegs 0x1112c source_phdrs rsp rmb rrnd inp)
      (mkst regs1 (0x1117c : word) fmem rrom).
Proof.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  pose proof (valid_argv_len av Hva) as HargcLe.
  destruct psrc_bounds as [Hplo Hphi].
  (* 0x1112c .. 0x1117c - 34 instructions in ONE reflective block: the
     whole crt entry (gp, the [environ] store, the [jal] into main),
     main's not-taken [bge], the argv[1] reload, the frame push with its
     four callee-save stores, the openat argument setup, the [jal] into
     raw_syscall and its seven register shuffles.  The executor stops at
     the [ecall].  The read script names the two stack loads (argc and
     the argv[1] pointer); every store bound comes from the [sp] window
     or the .data window. *)
  sym_block_ex (source_segs ++ vt)
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
          (Z_to_bv 64 69932) wmem rrom)
    40%nat [false] [EVar 33; EVar 34]
    [((2 : reg), EVar 32); ((8 : reg), ELit 0); ((9 : reg), ELit 0);
     ((18 : reg), ELit 0)]
    [rsp] [argcN; psrc] R HR Hms.
  { exists (word_le8 psrc); split;
      [ match goal with |- rdn _ _ ?ad _ = _ =>
          replace ad with (rsp + nat_to_word (8 + 8 * 1))
            by (rewrite word_add_nat; apply bv_eq; u_norm; lia)
        end;
        rewrite <- rdn_emem_above by (rewrite word_add_nat; u_norm; lia);
        exact read_psrc_e
      | exact (bytes_le_n_to_le_8 _) ]. }
  { s_ro. }
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
  (* Re-spell the block's exit memory as [fmem]: the executor leaves the
     store log's denotation, which differs from the definition only in
     the [environ] pointer's [add]/[slli] spelling. *)
  match type of Hms with msteps _ _ (mkst _ _ ?M _) => assert (HM : M = fmem) end.
  { unfold fmem, emem. sym_mem_norm. rewrite envp_val_eq_sym. reflexivity. }
  rewrite HM in Hms. clear HM.
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  9: { rewrite init_mkst. eapply msteps_trans; [ exact Hms | ]. sym_pc_lit.
       apply mst_refl. }
  all: s_out HR.
Qed.

(* ================================================================= *)
(* From the open1 return to the second openat ecall instruction.      *)
(* ================================================================= *)

Lemma source_to_open2 : forall regs fdv,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 3 = (0x13800 : word) ->
  reg_get regs 8 = Z_to_bv 64 (bv_unsigned rsp + 8) ->
  reg_get regs 1 = (0x11040 : word) ->
  reg_get regs 10 = fdv -> (bv_unsigned fdv < 2 ^ 31)%Z ->
  exists regs2,
    reg_get regs2 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regs2 3 = (0x13800 : word) /\
    reg_get regs2 18 = fdv /\
    reg_get regs2 8 = Z_to_bv 64 (bv_unsigned rsp + 8) /\
    reg_get regs2 1 = (0x1106c : word) /\
    bv_unsigned (getr regs2 17) = 56%Z /\
    reg_get regs2 10 = AT_FDCWD /\
    reg_get regs2 11 = pdst /\
    reg_get regs2 12 = Z_to_bv 64 577 /\
    msteps rsegs (mkst regs (0x11180 : word) fmem rrom)
                 (mkst regs2 (0x1117c : word) fmem rrom).
Proof.
  intros regs fdv H2 H3 H8 H1 H10 Hlt.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  destruct pdst_bounds as [Hplo Hphi].
  (* 0x11180 .. 0x1117c - 19 instructions in ONE reflective block:
     raw_syscall's [ret], [mv s2,a0], the not-taken [bltz], the argv[2]
     reload off the saved [s0], the six openat argument [li]s, the [jal]
     back into raw_syscall and its seven shuffles.  The executor stops at
     the [ecall]. *)
  sym_pc_Z.
  sym_block_ex (source_segs ++ vt) (mkst regs (Z_to_bv 64 70016) fmem rrom)
    20%nat [false] [EVar 34]
    [((1 : reg), ELit 0x11040); ((8 : reg), EVar 32); ((10 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp + 8); fdv] [pdst] R HR Hms.
  { exists (word_le8 pdst); split;
      [ match goal with |- rdn _ _ ?ad _ = _ =>
          replace ad with (rsp + nat_to_word (8 + 8 * 2))
            by (rewrite word_add_nat; apply bv_eq; u_norm; lia)
        end; exact read_pdst_f
      | exact (bytes_le_n_to_le_8 _) ]. }
  { apply c_lts_pos_0; lia. }
  { rewrite getr_nz by reg_neq_tac; rewrite H1; bveq. }
  { rewrite getr_nz by reg_neq_tac; exact H8. }
  { rewrite getr_nz by reg_neq_tac; exact H10. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
            (conj _ (conj _ (conj _ _))))))))).
  10: { eapply msteps_trans; [ exact Hms | ]. sym_pc_lit. apply mst_refl. }
  all: s_out HR.
Qed.

(* ================================================================= *)
(* Shared error-exit tails.                                           *)
(* ================================================================= *)

Lemma src_open1_err_tail : forall regs e model fsv,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  reg_get regs 10 = errno_ret e ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 1 = (0x11040 : word) ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x11180 : word) fmem rrom) model
    (fun o => o = (Z_to_bv 64 3, fsv)).
Proof.
  intros regs e model fsv He1 He2 H10 H2 H1 Hfs.
  eapply tfo_msteps.
  { sret (SFv SF_11180) SD_11180 (0x11040 : word).
    stepiv (SFv SF_11040) SD_11040 (errno_ret e)
      ltac:(getr_resolve; rewrite H10; imm_norm; apply v_addi_0).
    stepiv (SFv SF_11044) SD_11044 (Z_to_bv 64 3) ltac:(getr_resolve; bveq).
    step_intro;
      [ reflexivity
      | eapply step_blt_tk;
        [ exact (SFv SF_11048) | reflexivity | exact SD_11048
        | getr_resolve; regupd_resolve; apply c_lts_errno; lia ]
      | norm_pc ].
    apply mst_refl. }
  apply source_fepilogue with (code := Z_to_bv 64 3).
  - regupd_resolve; exact H2.
  - regupd_resolve; reflexivity.
  - rewrite u_Z2bv by lia; lia.
  - apply smem_inv_fmem.
  - exact Hfs.
Qed.

Lemma src_open2_err_tail : forall regs e model fsv,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  reg_get regs 10 = errno_ret e ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 1 = (0x1106c : word) ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x11180 : word) fmem rrom) model
    (fun o => o = (Z_to_bv 64 4, fsv)).
Proof.
  intros regs e model fsv He1 He2 H10 H2 H1 Hfs.
  eapply tfo_msteps.
  { sret (SFv SF_11180) SD_11180 (0x1106c : word).
    stepiv (SFv SF_1106c) SD_1106c (errno_ret e)
      ltac:(getr_resolve; rewrite H10; imm_norm; apply v_addi_0).
    stepiv (SFv SF_11070) SD_11070 (Z_to_bv 64 4) ltac:(getr_resolve; bveq).
    step_intro;
      [ reflexivity
      | eapply step_blt_tk;
        [ exact (SFv SF_11074) | reflexivity | exact SD_11074
        | getr_resolve; regupd_resolve; apply c_lts_errno; lia ]
      | norm_pc ].
    apply mst_refl. }
  apply source_fepilogue with (code := Z_to_bv 64 4).
  - regupd_resolve; exact H2.
  - regupd_resolve; reflexivity.
  - rewrite u_Z2bv by lia; lia.
  - apply smem_inv_fmem.
  - exact Hfs.
Qed.

(** After the second open succeeds: to the copy-loop head 0x1107c. *)
Lemma src_open2_to_loop : forall regs fd fd2,
  reg_get regs 10 = fd2 ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 48) ->
  reg_get regs 3 = (0x13800 : word) ->
  reg_get regs 18 = fd ->
  reg_get regs 1 = (0x1106c : word) ->
  (bv_unsigned fd < 2 ^ 31)%Z -> (bv_unsigned fd2 < 2 ^ 31)%Z ->
  exists regsH,
    reg_get regsH 2 = Z_to_bv 64 (bv_unsigned rsp - 48) /\
    reg_get regsH 3 = (0x13800 : word) /\
    reg_get regsH 8 = sbuf /\
    reg_get regsH 18 = fd /\ reg_get regsH 9 = fd2 /\
    msteps rsegs (mkst regs (0x11180 : word) fmem rrom)
                 (mkst regsH (0x1107c : word) fmem rrom).
Proof.
  intros regs fd fd2 H10 H2 H3 H18 H1 Hlt Hlt2.
  eexists.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  6: {
    sret (SFv SF_11180) SD_11180 (0x1106c : word).
    stepiv (SFv SF_1106c) SD_1106c fd2
      ltac:(getr_resolve; rewrite H10; imm_norm; apply v_addi_0).
    stepiv (SFv SF_11070) SD_11070 (Z_to_bv 64 4) ltac:(getr_resolve; bveq).
    step_intro;
      [ reflexivity
      | eapply step_blt_ft;
        [ exact (SFv SF_11074) | reflexivity | exact SD_11074
        | getr_resolve; regupd_resolve; apply c_lts_pos_0; lia ]
      | norm_pc ].
    (* addi s0,gp,-2040 : the buffer base, hoisted out of the copy loop *)
    stepiv (SFv SF_11078) SD_11078 sbuf
      ltac:(getr_resolve; regupd_resolve; rewrite H3; bveq).
    apply mst_refl. }
  all: getr_resolve; regupd_resolve;
       first [ reflexivity | assumption | bveq | vm_compute; reflexivity ].
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
  to_floop rsegs (init_machine_state rsegs 0x1112c source_phdrs rsp rmb rrnd inp) m0
    (cp_outcomes fs0 (in_cwd inp) (in_urandom inp) src dst).
Proof.
  intros m0 Hfds Hfs Hcwd Hur Hh Hlazy Hinf Hans1 Hans2.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  destruct source_to_open1
    as (regs1 & H1 & H2 & H3 & H8 & H17 & H10 & H11 & H12 & Hms).
  eapply tfl_msteps.
  { eapply msteps_trans; [exact Hms|].
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_1117c) eq_refl)
      | apply mst_refl ]. }
  apply (tfl_open_operand_rec rsegs regs1 (0x1117c : word) fmem m0 src true
           (fun o => o = (Z_to_bv 64 3, fs0))
           (fun o => match open_arm true fs0 (in_cwd inp) src with
                     | inl (fe_s, _) =>
                         o = (Z_to_bv 64 4, fs0)
                         \/ (op_walked dst = true /\
                             match open_arm false fs0 (in_cwd inp) dst with
                             | inl (fe_d, ofs) => cp_copy (cp_fs1 fs0 ofs) (in_urandom inp) fe_s fe_d o
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
  - rewrite Hfds. exact cp_free1.
  - exact Hh.
  - exact Hlazy.
  - (* the first open answers an errno: exit 3 *)
    intros r Hr. fnorm_pc.
    destruct (addr_is_error_b_errno r Hr) as (e & He1 & He2 & ->).
    apply (src_open1_err_tail (regupd regs1 10 (errno_ret e)) e m0 fs0).
    + lia.
    + lia.
    + regupd_resolve; reflexivity.
    + regupd_resolve; exact H2.
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
                           | inl (fe_d, ofs) => cp_copy (cp_fs1 fs0 ofs) (in_urandom inp) fe_s fe_d o
                           | inr _ => False
                           end))).
    2:{ intro o. rewrite Harm1. split; intro Ho; exact Ho. }
    assert (Hfd1 : alloc_fd (m_fds m0) = Z_to_bv 64 3) by (rewrite Hfds; exact cp_fd1).
    rewrite Hfd1.
    flnorm_pc.
    destruct (source_to_open2 (regupd regs1 10 (Z_to_bv 64 3)) (Z_to_bv 64 3))
      as (regs2 & G2 & G3 & G18 & G8 & G1 & G17 & G10 & G11 & G12 & Hms2);
      [ regupd_resolve; exact H2 | regupd_resolve; exact H3
      | regupd_resolve; exact H8 | regupd_resolve; exact H1
      | regupd_resolve; reflexivity | vm_compute; reflexivity | ].
    eapply tfl_msteps.
    { eapply msteps_trans; [exact Hms2|].
      step_intro;
        [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_1117c) eq_refl)
        | apply mst_refl ]. }
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
    apply (tfl_open_operand_rec rsegs regs2 (0x1117c : word) fmem m1 dst false
             (fun o => o = (Z_to_bv 64 4, fs0))
             (fun o => match open_arm false fs0 (in_cwd inp) dst with
                       | inl (fe_d, ofs) => cp_copy (cp_fs1 fs0 ofs) (in_urandom inp) fe_s fe_d o
                       | inr _ => False
                       end)).
    + exact G17.
    + exact G10.
    + exact G12.
    + rewrite G11. exact source_cstr_dst.
    + intros _. apply proc_self_fd_no_slash.
      exact (valid_argv_no_slash av 1 Hva ltac:(lia)).
    + intros Hw. rewrite Hm1fs, Hm1cwd. exact (Hans2 Hw).
    + rewrite Hm1fds. exact (cp_free2 fe_s).
    + exact Hm1h.
    + exact Hm1l.
    + (* the second open answers an errno: exit 4 *)
      intros r Hr. fnorm_pc.
      destruct (addr_is_error_b_errno r Hr) as (e & He1 & He2 & ->).
      apply (src_open2_err_tail (regupd regs2 10 (errno_ret e)) e m1 fs0).
      * lia.
      * lia.
      * regupd_resolve; reflexivity.
      * regupd_resolve; exact G2.
      * regupd_resolve; exact G1.
      * exact Hm1fs.
    + (* both descriptors: the copy *)
      intros fe_d ofs2 Harm2.
      rewrite Hm1fs, Hm1cwd in Harm2.
      apply (tfl_equiv rsegs _ _ (cp_copy (cp_fs1 fs0 ofs2) (in_urandom inp) fe_s fe_d)).
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
      flnorm_pc.
      destruct (src_open2_to_loop (regupd regs2 10 (Z_to_bv 64 4))
                  (Z_to_bv 64 3) (Z_to_bv 64 4))
        as (regsH & K2 & K3 & K8 & K18 & K9 & HmsH);
        [ regupd_resolve; reflexivity | regupd_resolve; exact G2
        | regupd_resolve; exact G3 | regupd_resolve; exact G18
        | regupd_resolve; exact G1 | vm_compute; reflexivity
        | vm_compute; reflexivity | ].
      eapply tfl_msteps; [exact HmsH|].
      assert (Haok : access_okb sbuf (bv_unsigned (Z_to_bv 64 1024)) = true).
      { apply access_okb_intro. rewrite u_sbuf, u_Z2bv by lia. unfold TASK_SIZE. lia. }
      destruct Hkind as [(i & ->) | [(k & ->) | [-> | ->]]].
      * (* a regular file: copied to its end, or to [cp_cut] *)
        apply to_floop_of_fout.
        apply (source_loop (cp_fs1 fs0 ofs2) i (Fs.fs_ino_data (cp_fs1 fs0 ofs2) i)
                 (Z_to_bv 64 3) (Z_to_bv 64 4) fe_d eq_refl fd3_ne_fd4
                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                 Hdok (S cp_cut) 0%nat).
        -- lia.
        -- lia.
        -- lia.
        -- left. exists 0%Z. reflexivity.
        -- exact (conj K2 (conj K3 (conj K8 (conj K18 K9)))).
        -- exact smem_inv_fmem.
        -- unfold sMI.
           refine (conj Hm2h (conj Hm2l (conj Hl3 (conj _ _)))).
           ++ rewrite Hl4.
              destruct Hdok as [(j & Hj & _) | [Hj | Hj]]; rewrite Hj; reflexivity.
           ++ rewrite Hm2fs.
              destruct Hdok as [(j & Hj & _) | [Hj | Hj]]; rewrite Hj; reflexivity.
      * (* a folder: -EISDIR, exit 5 *)
        apply to_floop_of_fout.
        destruct (src_head_to_read regsH fmem (Z_to_bv 64 3) (Z_to_bv 64 4)
                    K2 K3 K8 K18 K9)
          as (regsR & R17 & R10 & R11 & R12 & R2 & R1 & R3 & R8 & R9 & R18 & HmsR).
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
        -- fnorm_pc.
           apply (tfo_equiv rsegs _ _ (fun o => o = (Z_to_bv 64 5, m_fs m2))).
           2:{ intro o. rewrite Hm2fs. cbn [cp_copy]. split; intro Ho; exact Ho. }
           apply (src_read_err_tail (regupd regsR 10 (errno_ret EISDIR)) EISDIR fmem m2
                    (m_fs m2)).
           ++ unfold EISDIR; lia.
           ++ unfold EISDIR; lia.
           ++ regupd_resolve; reflexivity.
           ++ regupd_resolve; exact R2.
           ++ regupd_resolve; exact R1.
           ++ exact smem_inv_fmem.
           ++ reflexivity.
      * (* /dev/null: the first read answers 0, both closes, exit 0 *)
        apply to_floop_of_fout.
        destruct (src_head_to_read regsH fmem (Z_to_bv 64 3) (Z_to_bv 64 4)
                    K2 K3 K8 K18 K9)
          as (regsR & R17 & R10 & R11 & R12 & R2 & R1 & R3 & R8 & R9 & R18 & HmsR).
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
        -- fnorm_pc.
           apply (tfo_equiv rsegs _ _ (fun o => o = (Z_to_bv 64 0, m_fs m2))).
           2:{ intro o. rewrite Hm2fs. cbn [cp_copy]. split; intro Ho; exact Ho. }
           apply (src_eof_tail (regupd regsR 10 (Z_to_bv 64 0)) fmem m2
                    (Z_to_bv 64 3) (Z_to_bv 64 4) (FdDevNull true false) fe_d (m_fs m2)).
           ++ regupd_resolve; reflexivity.
           ++ regupd_resolve; exact R1.
           ++ regupd_resolve; exact R2.
           ++ regupd_resolve; exact R3.
           ++ regupd_resolve; exact R8.
           ++ regupd_resolve; exact R9.
           ++ regupd_resolve; exact R18.
           ++ exact fd3_ne_fd4.
           ++ vm_compute; reflexivity.
           ++ vm_compute; reflexivity.
           ++ exact smem_inv_fmem.
           ++ exact Hl3.
           ++ exact Hl4.
           ++ exact Hm2h.
           ++ exact Hm2l.
           ++ reflexivity.
      * (* /dev/urandom *)
        destruct Hdok as [(j & -> & Hjd) | Hdev].
        -- (* into a regular file: copied to [cp_cut], where the write is
              -EINVAL, exit 6 *)
           apply to_floop_of_fout.
           cbn [cp_copy].
           apply (source_uloop (cp_fs1 fs0 ofs2) j (in_urandom inp)
                    (Z_to_bv 64 3) (Z_to_bv 64 4) Hjd Hinf fd3_ne_fd4
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                    (S cp_cut) 0%nat).
           ++ lia.
           ++ lia.
           ++ exists 0%Z. reflexivity.
           ++ exact (conj K2 (conj K3 (conj K8 (conj K18 K9)))).
           ++ exact smem_inv_fmem.
           ++ refine (conj Hm2h (conj Hm2l (conj Hl3 (conj Hl4 (conj _ _))))).
              ** rewrite Hm2fs. reflexivity.
              ** rewrite Hm2ur. reflexivity.
        -- (* into a device: copied forever *)
           destruct (src_head_to_read regsH fmem (Z_to_bv 64 3) (Z_to_bv 64 4)
                       K2 K3 K8 K18 K9)
             as (regsR & R17 & R10 & R11 & R12 & R2 & R1 & R3 & R8 & R9 & R18 & HmsR).
           eapply tfl_msteps; [exact HmsR|].
           apply (tfl_loop rsegs _ _ (fpath rsegs sAnchor)).
           ++ exact (fsilent_fpath rsegs sAnchor src_endless_anchored).
           ++ apply fp_anchor.
              exists (Z_to_bv 64 3), (Z_to_bv 64 4), regsR, fmem, m2.
              split; [exact fd3_ne_fd4|].
              split; [fd32_ok|]. split; [fd32_ok|].
              split; [unfold sRpins; tauto|].
              split; [exact smem_inv_fmem|].
              split; [|reflexivity].
              split; [exact Hm2h|]. split; [exact Hm2l|].
              split.
              ** cbn [cp_esrc]. split; [exact Hl3|]. rewrite Hm2ur. exact Hinf.
              ** exact (cp_edst_open (Z_to_bv 64 4) m2 fe_d Hl4 Hdev).
           ++ intros o Ho. cbn [cp_copy] in Ho.
              destruct Hdev as [-> | ->]; exact Ho.
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

Lemma source_wexit_lt3 : (length av < 3)%nat ->
  to_wexit rsegs
    (init_machine_state rsegs 0x1112c source_phdrs rsp rmb rrnd inp)
    [] (Z_to_bv 64 2).
Proof.
  intros Hlt3.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  pose proof (valid_argv_len av Hva) as HargcLe.
  rewrite init_mkst. norm_pc.
  (* auipc gp,0x2; addi gp,gp,-1760 -> 0x13800 *)
  stepi (SFv SF_1112c) SD_1112c.
  stepiv (SFv SF_11130) SD_11130 (0x13800 : word)
    ltac:(getr_resolve; regupd_resolve; bveq).
  (* ld a0,0(sp): argc *)
  step_intro;
    [ reflexivity
    | eapply step_ld with (bs := word_le8 argcN) (v := argcN);
      [ exact (SFv SF_11134) | reflexivity | exact SD_11134
      | match goal with |- rdn _ _ ?ad _ = _ =>
          replace ad with rsp
            by (getr_resolve; regupd_resolve; rewrite v_addi_0; reflexivity)
        end;
        exact read_argc_w
      | exact (bytes_le_n_to_le_8 _) ]
    | step_simpl ].
  (* addi a1,sp,8 *)
  stepiv (SFv SF_11138) SD_11138 (Z_to_bv 64 (bv_unsigned rsp + 8))
    ltac:(getr_resolve; regupd_resolve; sp_norm;
          first [ reflexivity | f_equal; lia ]).
  (* slli t0,a0,3; add a2,a1,t0; addi a2,a2,8 *)
  stepi (SFv SF_1113c) SD_1113c.
  stepi (SFv SF_11140) SD_11140.
  stepiv (SFv SF_11144) SD_11144 envp_val
    ltac:(getr_resolve; regupd_resolve; imm_norm; exact envp_val_eq).
  (* auipc t1,0x1; addi t1,t1,260 -> 0x13000 *)
  stepi (SFv SF_11148) SD_11148.
  stepiv (SFv SF_1114c) SD_1114c (0x13000 : word)
    ltac:(getr_resolve; regupd_resolve; bveq).
  (* sd a2,0(t1): the environ pointer *)
  ssd (SFv SF_11150) SD_11150 (0x13000 : word) envp_val
    ltac:(getr_resolve; regupd_resolve; reflexivity).
  (* jal main *)
  stepj (SFv SF_11154) SD_11154.
  (* li a5,2 *)
  stepiv (SFv SF_11000) SD_11000 (Z_to_bv 64 2) ltac:(getr_resolve; bveq).
  (* bge a5,a0 taken (argc <= 2) -> 0x11114 *)
  step_intro;
    [ reflexivity
    | eapply step_bge_tk;
      [ exact (SFv SF_11004) | reflexivity | exact SD_11004
      | getr_resolve; regupd_resolve;
        rewrite c_lts_small by (u_norm; rewrite ?u_argcN; lia);
        apply Z.ltb_ge; u_norm; rewrite ?u_argcN; lia ]
    | norm_pc ].
  (* mv a0,a5 : gcc 15 reuses the compare constant a5 = 2 as the exit code *)
  stepiv (SFv SF_11114) SD_11114 (Z_to_bv 64 2)
    ltac:(getr_resolve; regupd_resolve; imm_norm; apply v_addi_0).
  (* ret -> 0x11158 *)
  stepjr (SFv SF_11118) SD_11118 (0x11158 : word) ltac:(getr_resolve; regupd_resolve; bveq).
  (* li a7,93 *)
  stepiv (SFv SF_11158) SD_11158 (Z_to_bv 64 93) ltac:(getr_resolve; bveq).
  (* ecall -> exit 2 *)
  step_intro;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ (SFv SF_1115c) eq_refl) | ].
  apply tw_exit_coden.
  - getr_resolve; regupd_resolve; vm_compute; reflexivity.
  - regupd_resolve; reflexivity.
  - vm_compute; reflexivity.
Qed.

End SourceProof.
