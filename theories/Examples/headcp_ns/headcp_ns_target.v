(** * headcp-ns, target binary (Zig ReleaseSmall, raw ecalls).

    PROOF-SIDE FILE (not part of the trusted specification).

    _start saves ra/s0, calls run() (0x10011b8) with argc/argv, and
    exits with its return value.  run() checks argc, issues the two
    openats, then a SINGLE read of the static 128-byte buffer at
    0x1002278, a SINGLE write of exactly what was read, then closes both
    fds.  No loop.  Each failure path loads its exit code into a1 and
    jumps to the shared tail at 0x1001270.

    Deliverables, over the run's segment list [target_segs ++ vt]:
    - [target_wexit_lt3] : argc < 3 -> to_wexit [] 2 (CatSim glue);
    - [target_ge3]       : argc >= 3 -> to_fout [hc_outcomes], the same
      outcome set [headcp_ns_source.source_ge3] derives.

    Sp-relative values in the canonical
    [Z_to_bv 64 (bv_unsigned asp - k)] form, pc/rodata constants in
    numeral-literal form, the chunk length as [len_word chunk].

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Sys.Prelude.
From LinuxProcessSemantics.Common Require Import SimInv ExitSim PropExec CatExec CatSim SeqExec StepTac StreamExec StreamSim FileSim ListFacts StoreOk SymExec SymTac RunSegmentsLift FileSimWalk.
From LinuxProcessSemantics.Examples.headcp_ns Require Import headcp_ns_code headcp_ns_defs.
From LinuxProcessSemantics.Examples.headcp_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.headcp_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them. *)
#[local] Instance headcp_ns_target_fx : FPState := fx0.

Definition tbuf : word := 0x1002278.

Lemma u_tbuf : bv_unsigned tbuf = 0x1002278%Z.
Proof. reflexivity. Qed.

(** Normalize the pc of a [to_fout] goal's head state to its literal
    form (FileSim continuation states arrive with [v_addi pc 4]). *)
Ltac fnorm_pc :=
  try lazymatch goal with
  | |- to_fout _ (mkst _ ?p _ _) _ _ => wlit p
  end.

Lemma tfd4_ne_fd3 : Z_to_bv 64 4 <> Z_to_bv 64 3.
Proof. intro Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc. Qed.

Section TargetProof.

(** The segments the run appends after the image's own: the vDSO pair
    ([Run.run_segments]).  Nothing below reads them. *)
Variable vt : list Segment.

Variable inp : ProcInput.
Local Abbreviation av := (in_argv inp).
Local Abbreviation ev := (in_envp inp).
Local Abbreviation fs0 := (in_fs inp).
Hypothesis Hva : valid_argv av.
Hypothesis Hvl : valid_launch inp.

(** The initial stack pointer, the program break and the mmap base
    (ASLR), as the Lean twin names them. *)
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

Local Abbreviation rsegs := (target_segs ++ vt).
Local Abbreviation trom := (seg_rom (target_segs ++ vt)).
Local Abbreviation TFv F := (fetch_word_app _ vt _ _ F).

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

(* ================================================================= *)
(* Local step tactics                                                *)
(* ================================================================= *)

Local Ltac t_ro :=
  first [ apply target_store_ok; imm_norm; u_norm; lia | solve_store_ok_inv ].

Local Ltac vconst :=
  getr_resolve; regupd_resolve;
  first [ apply v_addi_0 | reflexivity | bveq ].

(** A reflective block's ENTRY pin, discharged from the caller's
    [reg_get regs r = v] hypothesis [H]. *)
Local Ltac t_pin H :=
  rewrite getr_nz by reg_neq_tac; rewrite H;
  first [ reflexivity | bveq ].

(** A fact about a reflective block's EXIT register file, read back
    through its [regs_ok] [H]. *)
Local Ltac t_out H :=
  sym_regs H; rewrite ?getr_nz by reg_neq_tac;
  first [ assumption | sym_close | (vm_compute; reflexivity) ].

(** Run a reflective block from the head state of the [to_fout] goal
    the tactic is standing in. *)
Local Ltac t_fo_block fuel dirs rds ps pvals rvals R H Hms :=
  sym_pc_Z;
  lazymatch goal with
  | |- to_fout _ ?ms _ _ =>
      sym_block_ex (target_segs ++ vt) ms fuel dirs rds ps pvals rvals R H Hms
  end.

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
    [openat(AT_FDCWD, argv[1], O_RDONLY, 0)]; a5 carries the argv base
    (asp + 8) across both openats. *)
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
  (* 0x1001190 .. 0x10011d8 — ONE reflective block: _start's frame, its
     two zero saves, the argc/argv reads, the [jalr] into run(), the
     not-taken [bgeu] argc check, the argv[1] reload and the four openat
     argument [li]s.  The executor stops at the [ecall]. *)
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
  (* The block's exit memory IS [fmem]. *)
  match type of Hms with msteps _ _ (mkst _ _ ?M _) => assert (HM : M = fmem) end.
  { unfold fmem. sym_mem_norm.
    rewrite !getr_nz by reg_neq_tac. reflexivity. }
  rewrite HM in Hms. clear HM.
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  7: { rewrite init_mkst. sym_chain Hms. apply mst_refl. }
  all: t_out HR.
Qed.

(** The two failed-open tails, each ONE reflective block: the taken
    [bltz] on the delivered errno, the exit-code load, the [j] to the
    shared tail at 0x1001270, [mv a0,a1], the [ret] into _start and the
    exit(93) load.  No memory traffic, so [mem] is arbitrary. *)
Lemma tgt_exit3 : forall regs mem model X fsv,
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 10 = X ->
  c_lts X (Z_to_bv 64 0) = true ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x10011dc : word) mem trom) model
    (fun o => o = (Z_to_bv 64 3, fsv)).
Proof.
  intros regs mem model X fsv H1 H10 Hneg Hfs.
  t_fo_block 7%nat [true] (@nil expr)
    [((1 : reg), ELit 0x10011b0); ((10 : reg), EVar 32)] [X]
    (@nil word) R HR Hms.
  { exact Hneg. }
  { t_pin H1. }
  { t_pin H10. }
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

Lemma tgt_exit4 : forall regs mem model X fsv,
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 10 = X ->
  c_lts X (Z_to_bv 64 0) = true ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x10011fc : word) mem trom) model
    (fun o => o = (Z_to_bv 64 4, fsv)).
Proof.
  intros regs mem model X fsv H1 H10 Hneg Hfs.
  t_fo_block 7%nat [true] (@nil expr)
    [((1 : reg), ELit 0x10011b0); ((10 : reg), EVar 32)] [X]
    (@nil word) R HR Hms.
  { exact Hneg. }
  { t_pin H1. }
  { t_pin H10. }
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

(** The successful first open, on to the second openat's ecall: the
    not-taken [bltz], [mv a4,a0] (the input fd), the argv[2] reload off
    [a5] and the four openat argument [li]s. *)
Lemma tgt_open1_to_open2 : forall regs fd,
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 10 = fd ->
  reg_get regs 15 = Z_to_bv 64 (bv_unsigned asp + 8) ->
  (bv_unsigned fd < 2^31)%Z ->
  exists regs2,
    bv_unsigned (getr regs2 17) = 56%Z /\
    reg_get regs2 10 = AT_FDCWD /\
    reg_get regs2 11 = pdst /\
    reg_get regs2 12 = Z_to_bv 64 577 /\
    reg_get regs2 1 = (0x10011b0 : word) /\
    reg_get regs2 14 = fd /\
    msteps rsegs (mkst regs (0x10011dc : word) fmem trom)
      {| ms_regs := regs2; ms_fregs := fp_regs; ms_pc_val := (0x10011f8 : word);
         ms_svc_pending := Some (getr regs2 17); ms_resv := None;
         ms_fcsr := fp_csr; ms_mem := fmem; ms_rom := trom |}.
Proof.
  intros regs fd H1 H10 H15 Hlt.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781788) fmem trom)
    8%nat [false] [EVar 34]
    [((10 : reg), EVar 32); ((15 : reg), EVar 33)]
    [fd; Z_to_bv 64 (bv_unsigned asp + 8)] [pdst] R HR Hms.
  { exists (word_le8 pdst); split;
      [ match goal with |- rdn _ _ ?ad _ = _ =>
          replace ad with (asp + nat_to_word (8 + 8 * 2))
            by (rewrite word_add_nat; apply bv_eq; u_norm; lia)
        end; apply read_pdst_f
      | exact (bytes_le_n_to_le_8 _) ]. }
  { apply c_lts_pos_0; lia. }
  { t_pin H10. }
  { t_pin H15. }
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

(** The successful second open, on to the read ecall: the not-taken
    [bltz], [mv a3,a0] (the output fd), the buffer pointer, the two
    [li]s and [mv a0,a4]. *)
Lemma tgt_open2_to_read : forall regs mem fdin fdout,
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 10 = fdout ->
  reg_get regs 14 = fdin ->
  (bv_unsigned fdout < 2^31)%Z ->
  exists regs3,
    bv_unsigned (getr regs3 17) = 63%Z /\
    reg_get regs3 10 = fdin /\
    reg_get regs3 11 = tbuf /\
    reg_get regs3 12 = Z_to_bv 64 128 /\
    reg_get regs3 1 = (0x10011b0 : word) /\
    reg_get regs3 13 = fdout /\
    reg_get regs3 14 = fdin /\
    msteps rsegs (mkst regs (0x10011fc : word) mem trom)
      {| ms_regs := regs3; ms_fregs := fp_regs; ms_pc_val := (0x1001218 : word);
         ms_svc_pending := Some (getr regs3 17); ms_resv := None;
         ms_fcsr := fp_csr; ms_mem := mem; ms_rom := trom |}.
Proof.
  intros regs mem fdin fdout H1 H10 H14 Hlt.
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781820) mem trom)
    8%nat [false] (@nil expr)
    [((10 : reg), EVar 32); ((14 : reg), EVar 33)]
    [fdout; fdin] (@nil word) R HR Hms.
  { apply c_lts_pos_0; lia. }
  { t_pin H10. }
  { t_pin H14. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  8: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_1001218) eq_refl)
      | apply mst_refl ]. }
  all: t_out HR.
Qed.

(** The read tail: the not-taken [bltz], [mv a2,a0] (the delivered
    count), [li a7,64] and [mv a0,a3] (the output fd). *)
Lemma tgt_read_to_write : forall regs mem fdin fdout cnt,
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 10 = cnt ->
  reg_get regs 11 = tbuf ->
  reg_get regs 13 = fdout ->
  reg_get regs 14 = fdin ->
  (bv_unsigned cnt <= 128)%Z ->
  exists regs',
    bv_unsigned (getr regs' 17) = 64%Z /\
    reg_get regs' 10 = fdout /\
    reg_get regs' 11 = tbuf /\
    reg_get regs' 12 = cnt /\
    reg_get regs' 1 = (0x10011b0 : word) /\
    reg_get regs' 13 = fdout /\
    reg_get regs' 14 = fdin /\
    msteps rsegs (mkst regs (0x100121c : word) mem trom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := (0x100122c : word);
         ms_svc_pending := Some (getr regs' 17); ms_resv := None;
         ms_fcsr := fp_csr; ms_mem := mem; ms_rom := trom |}.
Proof.
  intros regs mem fdin fdout cnt H1 H10 H11 H13 H14 Hc.
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781852) mem trom)
    5%nat [false] (@nil expr)
    [((10 : reg), EVar 32); ((13 : reg), EVar 33)]
    [cnt; fdout] (@nil word) R HR Hms.
  { apply c_lts_pos_0; lia. }
  { t_pin H10. }
  { t_pin H13. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  8: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_100122c) eq_refl)
      | apply mst_refl ]. }
  all: t_out HR.
Qed.

(** The write tail: the not-taken [bltz], [li a7,57] and [mv a0,a4],
    stopping at the first [close] ecall. *)
Lemma tgt_write_to_close : forall regs mem fdin fdout cnt,
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 10 = cnt ->
  reg_get regs 13 = fdout ->
  reg_get regs 14 = fdin ->
  (bv_unsigned cnt <= 128)%Z ->
  exists regs',
    bv_unsigned (getr regs' 17) = 57%Z /\
    reg_get regs' 10 = fdin /\
    reg_get regs' 1 = (0x10011b0 : word) /\
    reg_get regs' 13 = fdout /\
    msteps rsegs (mkst regs (0x1001230 : word) mem trom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := (0x100123c : word);
         ms_svc_pending := Some (getr regs' 17); ms_resv := None;
         ms_fcsr := fp_csr; ms_mem := mem; ms_rom := trom |}.
Proof.
  intros regs mem fdin fdout cnt H1 H10 H13 H14 Hc.
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781872) mem trom)
    4%nat [false] (@nil expr)
    [((10 : reg), EVar 32); ((14 : reg), EVar 33)]
    [cnt; fdin] (@nil word) R HR Hms.
  { apply c_lts_pos_0; lia. }
  { t_pin H10. }
  { t_pin H14. }
  exists R.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  5: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_100123c) eq_refl)
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
    msteps rsegs (mkst regs (0x1001240 : word) mem trom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := (0x1001248 : word);
         ms_svc_pending := Some (getr regs' 17); ms_resv := None;
         ms_fcsr := fp_csr; ms_mem := mem; ms_rom := trom |}.
Proof.
  intros regs mem fdout H1 H13.
  sym_pc_Z.
  sym_block_ex (target_segs ++ vt) (mkst regs (Z_to_bv 64 16781888) mem trom)
    3%nat (@nil bool) (@nil expr)
    [((13 : reg), EVar 32)] [fdout] (@nil word) R HR Hms.
  { t_pin H13. }
  exists R.
  refine (conj _ (conj _ (conj _ _))).
  4: {
    eapply msteps_trans; [ exact Hms | ].
    sym_pc_lit.
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_1001248) eq_refl)
      | apply mst_refl ]. }
  all: t_out HR.
Qed.

(** The success tail: [li a1,0], the [j] to the shared tail, [mv a0,a1],
    the [ret] into _start and the exit(93) load. *)
Lemma tgt_exit0 : forall regs mem model fsv,
  reg_get regs 1 = (0x10011b0 : word) ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x100124c : word) mem trom) model
    (fun o => o = (Z_to_bv 64 0, fsv)).
Proof.
  intros regs mem model fsv H1 Hfs.
  t_fo_block 6%nat (@nil bool) (@nil expr)
    [((1 : reg), ELit 0x10011b0)] (@nil word) (@nil word) R HR Hms.
  { t_pin H1. }
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

(** The failed-read tail: the taken [bltz] at 0x100121c, [li a1,5] and
    the shared exit tail. *)
Lemma tgt_exit5 : forall regs mem model X fsv,
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 10 = X ->
  c_lts X (Z_to_bv 64 0) = true ->
  m_fs model = fsv ->
  to_fout rsegs (mkst regs (0x100121c : word) mem trom) model
    (fun o => o = (Z_to_bv 64 5, fsv)).
Proof.
  intros regs mem model X fsv H1 H10 Hneg Hfs.
  t_fo_block 7%nat [true] (@nil expr)
    [((1 : reg), ELit 0x10011b0); ((10 : reg), EVar 32)] [X]
    (@nil word) R HR Hms.
  { exact Hneg. }
  { t_pin H1. }
  { t_pin H10. }
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

(* ================================================================= *)
(* After the read: the write, both closes, exit 0                     *)
(* ================================================================= *)

(** From the read's return with [bs] delivered into the buffer: the
    write of exactly those bytes on fd 4, both closes, exit 0.  The write
    lands whole whatever fd 4 is ([hc_dst_ok]). *)
Lemma tgt_after_read : forall regs mem model bs fe1 fe_d fsv,
  reg_get regs 1 = (0x10011b0 : word) ->
  reg_get regs 10 = len_word bs ->
  reg_get regs 11 = tbuf ->
  reg_get regs 13 = Z_to_bv 64 4 ->
  reg_get regs 14 = Z_to_bv 64 3 ->
  (length bs <= 128)%nat ->
  rdn rsegs mem tbuf (length bs) = Some bs ->
  fd_lookup (m_fds model) (Z_to_bv 64 3) = Some fe1 ->
  fd_lookup (m_fds model) (Z_to_bv 64 4) = Some fe_d ->
  m_fs model = fsv ->
  hc_dst_ok fe_d fsv ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout rsegs (mkst regs (0x100121c : word) mem trom) model
    (fun o => o = (Z_to_bv 64 0, hc_written fe_d fsv bs)).
Proof.
  intros regs mem model bs fe1 fe_d fsv H1 H10 H11 H13 H14 Hlen Hbuf
    Hfd1 Hfd2 Hfs Hok Hh Hlazy.
  subst fsv.
  assert (HNc : bv_unsigned (len_word bs) = Z.of_nat (length bs)) by (apply u_len_word; lia).
  destruct (tgt_read_to_write regs mem (Z_to_bv 64 3) (Z_to_bv 64 4) (len_word bs))
    as (regs4 & L17 & L10 & L11 & L12 & L1 & L13 & L14 & Hms4);
    [ exact H1 | exact H10 | exact H11 | exact H13 | exact H14 | rewrite HNc; lia | ].
  eapply tfo_msteps; [ exact Hms4 | ].
  (* what follows the write, whatever it wrote *)
  assert (Hafter : forall model',
    fd_lookup (m_fds model') (Z_to_bv 64 3) = Some fe1 ->
    (exists e2, fd_lookup (m_fds model') (Z_to_bv 64 4) = Some e2) ->
    m_halted model' = None -> m_vm_lazy model' = [] ->
    to_fout rsegs (mkst (regupd regs4 10 (len_word bs)) (v_addi (0x100122c : word) 4)
                        mem trom) model'
      (fun o => o = (Z_to_bv 64 0, m_fs model'))).
  { intros model' G1 [e2 G2] Gh Gl.
    fnorm_pc.
    destruct (tgt_write_to_close (regupd regs4 10 (len_word bs)) mem
                (Z_to_bv 64 3) (Z_to_bv 64 4) (len_word bs))
      as (regs5 & M17 & M10 & M1 & M13 & Hms5);
      [ regupd_resolve; exact L1 | regupd_resolve; reflexivity
      | regupd_resolve; exact L13 | regupd_resolve; exact L14
      | rewrite HNc; lia | ].
    eapply tfo_msteps; [ exact Hms5 | ].
    eapply tfo_close_rec with (fdv := Z_to_bv 64 3).
    - exact M17.
    - exact M10.
    - exact G1.
    - fd32_ok.
    - exact Gh.
    - exact Gl.
    - fnorm_pc.
      destruct (tgt_close_to_close (regupd regs5 10 (Z_to_bv 64 0)) mem (Z_to_bv 64 4))
        as (regs6 & N17 & N10 & N1 & Hms6);
        [ regupd_resolve; exact M1 | regupd_resolve; exact M13 | ].
      eapply tfo_msteps; [ exact Hms6 | ].
      eapply tfo_close_rec with (fdv := Z_to_bv 64 4).
      + exact N17.
      + exact N10.
      + model_simp. rewrite fd_lookup_remove_neq by exact tfd4_ne_fd3. exact G2.
      + fd32_ok.
      + exact Gh.
      + exact Gl.
      + (* li a1,0; j 0x1001270; exit tail *)
        fnorm_pc.
        apply tgt_exit0.
        * regupd_resolve; exact N1.
        * reflexivity. }
  assert (Hrd : rdn rsegs mem tbuf (word_to_nat (len_word bs)) = Some bs).
  { replace (word_to_nat (len_word bs)) with (length bs)
      by (unfold word_to_nat; rewrite HNc, Nat2Z.id; reflexivity).
    exact Hbuf. }
  assert (Haok : access_okb tbuf (bv_unsigned (len_word bs)) = true).
  { apply access_okb_intro. rewrite u_tbuf, HNc. unfold TASK_SIZE. lia. }
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
    + (* [rw_verify_area]: offset 0 plus at most 128 bytes *)
      unfold rw_pos_einvalb. rewrite HNc.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.ltb_ge. lia.
    + exact Hh.
    + exact Hlazy.
    + eapply tfo_equiv; [ apply Hafter | ].
      * model_simp. rewrite fd_lookup_insert_neq by (intro Hc; exact (tfd4_ne_fd3 (eq_sym Hc))).
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

(** argc >= 3: the same outcome set as the source's. *)
Lemma target_ge3 : forall m0,
  m_fds m0 = fds0 -> m_fs m0 = fs0 -> m_cwd m0 = in_cwd inp ->
  m_urandom m0 = in_urandom inp ->
  m_halted m0 = None -> m_vm_lazy m0 = [] ->
  stream_infinite (in_urandom inp) ->
  (op_walked src = true -> open_answered true fs0 (in_cwd inp) src) ->
  (op_walked dst = true -> open_answered false fs0 (in_cwd inp) dst) ->
  to_fout rsegs (init_machine_state rsegs 0x1001190 target_phdrs asp amb arnd inp) m0
    (hc_outcomes fs0 (in_cwd inp) (in_urandom inp) src dst).
Proof.
  intros m0 Hfds Hfs Hcwd Hur Hh Hlazy Hinf Hans1 Hans2.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  destruct target_to_open1
    as (regs1 & H1 & H15 & H17 & H10 & H11 & H12 & Hms).
  eapply tfo_msteps.
  { eapply msteps_trans; [exact Hms|].
    step_intro;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10011d8) eq_refl)
      | apply mst_refl ]. }
  apply (tfo_open_operand_rec rsegs regs1 (0x10011d8 : word) fmem m0 src true
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
  - rewrite H11. exact target_cstr_src.
  - intros _. apply proc_self_fd_no_slash.
    exact (valid_argv_no_slash av 0 Hva ltac:(lia)).
  - intros Hw. rewrite Hfs, Hcwd. exact (Hans1 Hw).
  - rewrite Hfds. exact hc_free1.
  - exact Hh.
  - exact Hlazy.
  - (* the first open answers an errno: exit 3 *)
    intros r Hr. fnorm_pc.
    apply (tgt_exit3 (regupd regs1 10 r) fmem m0 r fs0).
    + regupd_resolve; exact H1.
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
    destruct (tgt_open1_to_open2 (regupd regs1 10 (Z_to_bv 64 3)) (Z_to_bv 64 3))
      as (regs2 & J17 & J10 & J11 & J12 & J1 & J14 & Hms2);
      [ regupd_resolve; exact H1 | regupd_resolve; reflexivity
      | regupd_resolve; exact H15 | vm_compute; reflexivity | ].
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
    apply (tfo_open_operand_rec rsegs regs2 (0x10011f8 : word) fmem m1 dst false
             (fun o => o = (Z_to_bv 64 4, fs0))
             (fun o => match open_arm false fs0 (in_cwd inp) dst with
                       | inl (fe_d, ofs) =>
                           hc_copy (hc_fs1 fs0 ofs) (in_urandom inp) fe_s fe_d o
                       | inr _ => False
                       end)).
    + exact J17.
    + exact J10.
    + exact J12.
    + rewrite J11. exact target_cstr_dst.
    + intros _. apply proc_self_fd_no_slash.
      exact (valid_argv_no_slash av 1 Hva ltac:(lia)).
    + intros Hw. rewrite Hm1fs, Hm1cwd. exact (Hans2 Hw).
    + rewrite Hm1fds. exact (hc_free2 fe_s).
    + exact Hm1h.
    + exact Hm1l.
    + (* the second open answers an errno: exit 4 *)
      intros r Hr. fnorm_pc.
      apply (tgt_exit4 (regupd regs2 10 r) fmem m1 r fs0).
      * regupd_resolve; exact J1.
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
      destruct (tgt_open2_to_read (regupd regs2 10 (Z_to_bv 64 4)) fmem
                  (Z_to_bv 64 3) (Z_to_bv 64 4))
        as (regs3 & K17 & K10 & K11 & K12 & K1 & K13 & K14 & Hms3);
        [ regupd_resolve; exact J1 | regupd_resolve; reflexivity
        | regupd_resolve; exact J14 | vm_compute; reflexivity | ].
      eapply tfo_msteps; [ exact Hms3 | ].
      assert (Haok : access_okb tbuf (bv_unsigned (Z_to_bv 64 128)) = true).
      { apply access_okb_intro. rewrite u_tbuf, u_Z2bv by lia. unfold TASK_SIZE. lia. }
      destruct Hkind as [(i & ->) | [(k & ->) | [-> | ->]]].
      * (* a regular file: its first (up to) 128 bytes as they are now *)
        eapply tfo_read_rec with (p := i) (off := Z_to_bv 64 0)
          (data := Fs.fs_ino_data (m_fs m2) i) (buf := tbuf).
        -- exact K17.
        -- exact K10.
        -- exact K11.
        -- exact K12.
        -- exact Hl3.
        -- fd32_ok.
        -- reflexivity.
        -- exact (target_buf_wseg vt).
        -- rewrite u_Z2bv by lia. unfold rw_bytes_max. lia.
        -- rewrite u_Z2bv by lia. lia.
        -- exact Haok.
        -- (* [rw_verify_area]: offset 0 plus 128 bytes *) reflexivity.
        -- exact Hm2h.
        -- exact Hm2l.
        -- fnorm_pc.
           set (bs := file_read (Fs.fs_ino_data (m_fs m2) i) (Z_to_bv 64 0) (Z_to_bv 64 128)).
           assert (Hbl : (length bs <= 128)%nat) by (unfold bs; apply hc_chunk_le).
           apply (tfo_equiv rsegs _ _
                    (fun o => o = (Z_to_bv 64 0, hc_written fe_d (m_fs m2) bs))).
           2:{ intro o. rewrite <- Hm2fs. split; intro Ho; exact Ho. }
           eapply tgt_after_read.
           ++ regupd_resolve; exact K1.
           ++ regupd_resolve; reflexivity.
           ++ regupd_resolve; exact K11.
           ++ regupd_resolve; exact K13.
           ++ regupd_resolve; exact K14.
           ++ exact Hbl.
           ++ apply rdn_write_to_mem. rewrite u_tbuf. lia.
           ++ model_simp. apply fd_lookup_insert_eq.
           ++ model_simp. rewrite fd_lookup_insert_neq by exact tfd4_ne_fd3. exact Hl4.
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
           apply (tgt_exit5 (regupd regs3 10 (errno_ret EISDIR)) fmem m2
                    (errno_ret EISDIR) (m_fs m2)).
           ++ regupd_resolve; exact K1.
           ++ regupd_resolve; reflexivity.
           ++ apply c_lts_errno; unfold EISDIR; lia.
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
           eapply tgt_after_read.
           ++ regupd_resolve; exact K1.
           ++ regupd_resolve; reflexivity.
           ++ regupd_resolve; exact K11.
           ++ regupd_resolve; exact K13.
           ++ regupd_resolve; exact K14.
           ++ cbn [length]. lia.
           ++ reflexivity.
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
        -- exact (target_buf_wseg vt).
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
           eapply tgt_after_read.
           ++ regupd_resolve; exact K1.
           ++ regupd_resolve. symmetry. exact Hlb.
           ++ regupd_resolve; exact K11.
           ++ regupd_resolve; exact K13.
           ++ regupd_resolve; exact K14.
           ++ lia.
           ++ apply rdn_write_to_mem. rewrite u_tbuf. lia.
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
  (* ld a0,0(s0) : argc *)
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
  (* bgeu a1,a0 taken (argc <= 2) -> the exit tail at 0x1001270 *)
  step_intro;
    [ reflexivity
    | eapply step_bgeu_tk;
      [ exact (TFv TF_10011c0) | reflexivity | exact TD_10011c0
      | getr_resolve; regupd_resolve;
        rewrite c_ltu_ltb; apply Z.ltb_ge;
        u_norm; rewrite ?u_argcN; lia ]
    | norm_pc ].
  (* mv a0,a1 (= 2) *)
  stepiv (TFv TF_1001270) TD_1001270 (Z_to_bv 64 2)
    ltac:(getr_resolve; regupd_resolve; imm_norm; bveq).
  (* ret -> 0x10011b0 *)
  stepjr (TFv TF_1001274) TD_1001274 (0x10011b0 : word)
    ltac:(getr_resolve; regupd_resolve; bveq).
  (* li a7,93 *)
  stepiv (TFv TF_10011b0) TD_10011b0 (Z_to_bv 64 93) ltac:(getr_resolve; bveq).
  (* ecall -> exit 2 *)
  step_intro;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ (TFv TF_10011b4) eq_refl) | ].
  apply tw_exit_coden.
  - getr_resolve; reflexivity.
  - regupd_resolve; reflexivity.
  - vm_compute; reflexivity.
Qed.

End TargetProof.
