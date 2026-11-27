(** * mmap-upper-ns TARGET binary (Zig): frames, prologue, slen, early
      exits, the run up to the mmap ecall, and both mmap continuations.

    PROOF-SIDE FILE (not part of the trusted specification).

    Machine plan (see the disassembly comments in mmap_upper_ns_code.v):

      _start 0x1001158..0x1001174: 2-slot frame, argc/argv, call run.
      run 0x1001180: argc < 2 -> a0=2; ret -> exit 2 (0x1001178 li a7,93).
      0x1001190..0x10011a8: run frame (sp = asp-32), s0 = argv[1], call slen.
      slen 0x1001284..0x100129c: a0 = n.
      0x10011ac..0x10011bc: a6 = n; n >> 12 != 0 -> a0=3 -> epilogue exit 3.
      0x10011c0..0x10011d8: mmap args, DIRECT ecall (the tmw branch point).
      Failure: bltz -> a0=4 -> epilogue exit 4.
      Success: branchless uppercase copy loop, '\n' store, one write,
      munmap, epilogue exit 0.

    Conventions: sp-relative addresses/register values are in the
    canonical [Z_to_bv 64 (bv_unsigned asp - k)] form, pc and rodata
    constants in numeral-literal form, loop indices as [nat_to_word];
    all range bookkeeping is in [Z] over [bv_unsigned]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec MmapSim WallSim StepTac StreamExec StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Common Require Import Footprint SymExec SymTac SymSide SymBranch.
From LinuxProcessSemantics.Examples.mmap_upper_ns Require Import mmap_upper_ns_code mmap_upper_ns_defs.
From LinuxProcessSemantics.Examples.mmap_upper_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.mmap_upper_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them.  [fx0] itself is
    the instance, so every state here is [init_mkst]'s [@mkst fx0]. *)
#[local] Existing Instance fx0.

(* ================================================================= *)
(* Store legality (both target segments are read-only)                *)
(* ================================================================= *)

Lemma target_avoids_high : forall a n : Z, (0x1002000 <= a)%Z ->
  range_avoids_ro_segs target_segs a n = true.
Proof.
  intros a n Ha.
  unfold target_segs, TargetMemImage_loaded_segments, range_avoids_ro_segs.
  cbn [forallb].
  change (seg_writable TargetMemImage_segment_000) with false.
  change (seg_writable TargetMemImage_segment_001) with false.
  change (Z.of_N (seg_base TargetMemImage_segment_000)
          + Z.of_N (seg_size TargetMemImage_segment_000))%Z with 0x1001000%Z.
  change (Z.of_N (seg_base TargetMemImage_segment_001)
          + Z.of_N (seg_size TargetMemImage_segment_001))%Z with 0x1002000%Z.
  assert (H0 : Z.ltb a 0x1001000 = false) by (apply Z.ltb_ge; lia).
  assert (H1 : Z.ltb a 0x1002000 = false) by (apply Z.ltb_ge; lia).
  rewrite H0, H1. rewrite !andb_false_r.
  cbn [negb orb andb]. reflexivity.
Qed.

(* ================================================================= *)
(* Grant facts for the target image                                   *)
(* ================================================================= *)

Lemma target_reserved_val :
  segments_reserved target_segs
  = [(Z_to_bv 64 0x1000000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x1001000, Z_to_bv 64 0x1000)].
Proof.
  apply (@bool_decide_eq_true_1 (_ = _) _).
  vm_cast_no_check (eq_refl true).
Qed.

Lemma target_reserved_low : forall a sz, In (a, sz) (segments_reserved target_segs) ->
  (bv_unsigned a + bv_unsigned sz <= Mmap.task_unmapped_base)%Z.
Proof.
  intros a sz Hin. rewrite target_reserved_val in Hin.
  unfold Mmap.task_unmapped_base.
  repeat destruct Hin as [Hin | Hin];
    try (injection Hin as <- <-; rewrite !u_Z2bv by lia; lia).
  destruct Hin.
Qed.

(** The launch model's one-page grant exists
    ([RunSegmentsLift.grant_witness_init]); the model is [Run]'s: [State.with_vdso] of the
    draw's vDSO counter over [State.init_model]. *)
Lemma target_grant_witness : forall inp (hint brk0 mb sp : word) v,
  (sp_window_lo <= bv_unsigned sp)%Z -> (mmap_base_min <= bv_unsigned mb)%Z ->
  exists a, grant_ok hint
    (with_vdso v (init_model (segments_reserved target_segs) brk0 mb sp target_alloc_limit inp))
    a 4096 = true.
Proof.
  intros inp hint brk0 mb sp v Hsp Hmb.
  apply grant_witness_init; [exact target_reserved_low | exact Hsp | exact Hmb |].
  rewrite target_alloc_limit_val. lia.
Qed.

Lemma target_grant_unpack : forall inp (hint brk0 mb sp aG : word) v,
  grant_ok hint (with_vdso v (init_model (segments_reserved target_segs) brk0 mb sp
                                target_alloc_limit inp)) aG 4096 = true ->
  (0 < bv_unsigned aG)%Z /\ (bv_unsigned aG mod page_size = 0)%Z /\
  (bv_unsigned aG + 4096 <= bv_unsigned sp - stack_max_size)%Z /\
  ((bv_unsigned aG + 4096 <= 0x1000000)%Z \/ (0x1001000 <= bv_unsigned aG)%Z) /\
  ((bv_unsigned aG + 4096 <= 0x1001000)%Z \/ (0x1002000 <= bv_unsigned aG)%Z).
Proof.
  intros inp hint brk0 mb sp aG v Hg.
  destruct (grant_ok_unpack _ _ _ _ Hg) as (Hal & Hpos & Hceil & Hfree & _).
  change (alloc_top (m_vmmaps (with_vdso v (init_model (segments_reserved target_segs)
            brk0 mb sp target_alloc_limit inp))))
    with (bv_unsigned sp - stack_max_size)%Z in Hceil.
  change (vm_reserved (m_vmmaps (with_vdso v (init_model (segments_reserved target_segs)
            brk0 mb sp target_alloc_limit inp))))
    with (init_reserved (segments_reserved target_segs) mb sp (in_kernel inp)) in Hfree.
  change (vm_maps (m_vmmaps (with_vdso v (init_model (segments_reserved target_segs)
            brk0 mb sp target_alloc_limit inp))))
    with (@nil (word * word)) in Hfree.
  unfold init_reserved in Hfree.
  rewrite target_reserved_val in Hfree.
  cbn [app] in Hfree.
  apply region_free_cons in Hfree. destruct Hfree as [Hda Hfree].
  apply region_free_cons in Hfree. destruct Hfree as [Hdb _].
  rewrite !u_Z2bv in Hda by lia.
  rewrite !u_Z2bv in Hdb by lia.
  refine (conj Hpos (conj Hal (conj Hceil (conj _ _)))).
  - destruct Hda as [H|H]; [left; lia | right; lia].
  - destruct Hdb as [H|H]; [left; lia | right; lia].
Qed.

Lemma target_grant_avoids : forall aGZ x k : Z,
  (aGZ + 4096 <= 0x1000000 \/ 0x1001000 <= aGZ)%Z ->
  (aGZ + 4096 <= 0x1001000 \/ 0x1002000 <= aGZ)%Z ->
  (aGZ <= x)%Z -> (x + k <= aGZ + 4096)%Z ->
  range_avoids_ro_segs target_segs x k = true.
Proof.
  intros aGZ x k Hda Hdb Hx1 Hx2.
  unfold target_segs, TargetMemImage_loaded_segments, range_avoids_ro_segs.
  cbn [forallb].
  change (seg_writable TargetMemImage_segment_000) with false.
  change (seg_writable TargetMemImage_segment_001) with false.
  change (Z.of_N (seg_base TargetMemImage_segment_000)
          + Z.of_N (seg_size TargetMemImage_segment_000))%Z with 0x1001000%Z.
  change (Z.of_N (seg_base TargetMemImage_segment_000)) with 0x1000000%Z.
  change (Z.of_N (seg_base TargetMemImage_segment_001)
          + Z.of_N (seg_size TargetMemImage_segment_001))%Z with 0x1002000%Z.
  change (Z.of_N (seg_base TargetMemImage_segment_001)) with 0x1001000%Z.
  assert (Hb0 : ((0x1000000 <? x + k) && (x <? 0x1001000))%Z = false).
  { destruct Hda as [H|H].
    - assert (E : (0x1000000 <? x + k)%Z = false) by (apply Z.ltb_ge; lia).
      rewrite E. apply andb_false_l.
    - assert (E : (x <? 0x1001000)%Z = false) by (apply Z.ltb_ge; lia).
      rewrite E. apply andb_false_r. }
  assert (Hb1 : ((0x1001000 <? x + k) && (x <? 0x1002000))%Z = false).
  { destruct Hdb as [H|H].
    - assert (E : (0x1001000 <? x + k)%Z = false) by (apply Z.ltb_ge; lia).
      rewrite E. apply andb_false_l.
    - assert (E : (x <? 0x1002000)%Z = false) by (apply Z.ltb_ge; lia).
      rewrite E. apply andb_false_r. }
  rewrite Hb0, Hb1. reflexivity.
Qed.

(** Zig compiles the [n > 4095] test to a [srli]; the executor denotes
    an immediate shift with the REGISTER shift primitive, and this is
    the bridge back to the immediate spelling the library's [v_srli_div]
    is stated against. *)
Lemma v_srl_12 : forall x : word, v_srl x (Z_to_bv 64 12) = v_srli x 12.
Proof. intro x. unfold v_srl, v_srli. f_equal. Qed.

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x1001158%N.
Proof. vm_compute. reflexivity. Qed.

Section TargetProof.

Variable inp : ProcInput.
Local Abbreviation av := (in_argv inp).
Local Abbreviation ev := (in_envp inp).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.

Variable asp : word.

(** The target run's own AT_RANDOM draw, independent of the source's
    (the [ed_random] half of [Run.ExecEntry]'s [en_draw]; see the source file). *)
Variable arnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned asp)%Z.
Hypothesis Hsp_hi : (bv_unsigned asp <= sp_window_hi)%Z.

(** The quantified initial program break — this example allocates with
    mmap and never calls brk, so the break is read only by the launch
    conjunct. *)
Variable abrk : word.
Variable amb : word.
Hypothesis Hvl : valid_launch inp.

(** The fifth conjunct of [Run.valid_entry_va] for the target's run
    ([create_elf_tables] and [setup_arg_pages], fs/binfmt_elf.c and
    fs/exec.c, Linux v6.18.46). *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry asp abrk amb arnd) inp.

Lemma asp_lo_num : (0x7fff80000000 <= bv_unsigned asp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma asp_hi_num : (bv_unsigned asp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Definition targcN : word := len_word av.
(** The initial overlay, with the entry point [init_mkst] passes to it. *)
Definition awmem : word -> option byte :=
  wrap_mem inp amb target_phdrs (Z_to_bv 64 (Z.of_N 0x1001158)) asp arnd.
(** The run's rom: the image's segments, then the vDSO pair. *)
Definition arom : word -> option byte := seg_rom (run_segments target_segs inp asp amb).

Lemma u_targcN : bv_unsigned targcN = Z.of_nat (length av).
Proof.
  pose proof (valid_argv_len av Hva).
  unfold targcN, len_word. apply u_Z2bv; lia.
Qed.

(** No-overflow bound for the initial stack image, for any entry word
    (the image's length does not read it). *)
Lemma target_bsb_nw : forall entry : word,
  (bv_unsigned asp
   + Z.of_nat (length (entry_stack_image inp amb target_phdrs entry asp arnd)) < 2^64)%Z.
Proof.
  intros entry.
  pose proof (bsb_bound Sv48 inp amb target_phdrs entry asp abrk arnd Hvl Hlau).
  pose proof asp_hi_num. lia.
Qed.

(** Memory after _start's two frame stores. *)
Definition smem : word -> option byte :=
  wbytes (wbytes awmem
    (Z_to_bv 64 (bv_unsigned asp - 0x8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))   (* _start: sd ra,8(sp) *)
    (Z_to_bv 64 (bv_unsigned asp - 0x10)) (word_to_le_bytes 8 (Z_to_bv 64 0)).  (* _start: sd s0,0(sp) *)

(** Memory after run's frame stores (argc >= 2 path). *)
Definition tfmem : word -> option byte :=
  wbytes (wbytes smem
    (Z_to_bv 64 (bv_unsigned asp - 0x18)) (word_to_le_bytes 8 (0x1001178 : word)))  (* run: sd ra,8(sp) *)
    (Z_to_bv 64 (bv_unsigned asp - 0x20)) (word_to_le_bytes 8 asp).                 (* run: sd s0,0(sp) *)

Local Abbreviation s := (nth 1 av []).
Local Abbreviation n := (length s).
Definition tnN : word := nat_to_word n.
Definition tP : word := cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) 1.

Lemma rdn_awmem_stack : forall (a : word) k,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= 2^64)%Z ->
  rdn target_segs awmem a k
  = rdn target_segs
      (stack_to_mem asp (entry_stack_image inp amb target_phdrs
                           (Z_to_bv 64 (Z.of_N 0x1001158)) asp arnd)) a k.
Proof. intros a k Ha Hnw. apply rdn_wrap_stack_above; assumption. Qed.

Lemma rdn_smem_above : forall (a : word) k,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= 2^64)%Z ->
  rdn target_segs smem a k = rdn target_segs awmem a k.
Proof.
  intros a k Ha Hnw. pose proof asp_lo_num. pose proof asp_hi_num. unfold smem.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; u_norm; lia)).
  reflexivity.
Qed.

Lemma rdn_tfmem_above : forall (a : word) k,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= 2^64)%Z ->
  rdn target_segs tfmem a k = rdn target_segs awmem a k.
Proof.
  intros a k Ha Hnw. pose proof asp_lo_num. pose proof asp_hi_num. unfold tfmem.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; u_norm; lia)).
  apply rdn_smem_above; assumption.
Qed.

Lemma target_ptr_bounds : (2 <= length av)%nat ->
  (bv_unsigned asp <= bv_unsigned tP)%Z /\
  (bv_unsigned tP + Z.of_nat n + 1 < 2^64)%Z.
Proof.
  intro H2. unfold tP.
  exact (argv_ptr_bounds Sv48 inp amb asp abrk arnd 1 Hlau ltac:(lia)).
Qed.

Lemma tread_str_byte : forall j, (2 <= length av)%nat -> (j <= n)%nat ->
  rdn target_segs tfmem (tP + nat_to_word j) 1%nat = Some [byte_at s j].
Proof.
  intros j H2 Hj.
  destruct (target_ptr_bounds H2) as [Hge Hup].
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as Hslen.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  rewrite rdn_tfmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_awmem_stack by (rewrite word_add_nat; u_norm; lia).
  apply (read_argv_byte_k Sv48 target_segs inp amb target_phdrs _ asp abrk arnd 1 j Hlau);
    [lia | exact Hj].
Qed.

(* ================================================================= *)
(* Frame-slot read-back on [tfmem]                                    *)
(* ================================================================= *)

Lemma tfread_slot_ra :
  rdn target_segs tfmem (Z_to_bv 64 (bv_unsigned asp - 0x18)) 8%nat
  = Some (word_to_le_bytes 8 (0x1001178 : word)).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. unfold tfmem.
  repeat first
    [ rewrite rdn_wbytes_hit8 by (u_norm; lia)
    | rewrite rdn_wbytes_disjoint by (rewrite ?length_N_to_le_bytes; u_norm; lia)
    | rewrite rdn_wbytes_below by (rewrite ?length_N_to_le_bytes; u_norm; lia) ].
  reflexivity.
Qed.

Lemma tfread_slot_s0 :
  rdn target_segs tfmem (Z_to_bv 64 (bv_unsigned asp - 0x20)) 8%nat
  = Some (word_to_le_bytes 8 asp).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. unfold tfmem.
  repeat first
    [ rewrite rdn_wbytes_hit8 by (u_norm; lia)
    | rewrite rdn_wbytes_disjoint by (rewrite ?length_N_to_le_bytes; u_norm; lia)
    | rewrite rdn_wbytes_below by (rewrite ?length_N_to_le_bytes; u_norm; lia) ].
  reflexivity.
Qed.

(* ================================================================= *)
(* Epilogue: 0x1001274 .. ret .. exit ecall (generic memory)          *)
(* ================================================================= *)

Lemma target_epilogue : forall regs (mem : word -> option byte) code,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 0x20) ->
  reg_get regs 10 = code ->
  rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 0x18)) 8%nat
    = Some (word_to_le_bytes 8 (0x1001178 : word)) ->
  rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 0x20)) 8%nat
    = Some (word_to_le_bytes 8 asp) ->
  exists regs',
    bv_unsigned (getr regs' 17) = 93%Z /\ reg_get regs' 10 = code /\
    msteps target_segs (mkst regs 0x1001274 mem arom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := 0x100117c;
         ms_svc_pending := Some (getr regs' 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := arom |}.
(** SIX instructions in ONE reflective block: the two frame reloads, the
    stack pop, main's [ret] and the crt's [li a7,93] before the [exit]
    [ecall].  The [ra] reload is named in the READ SCRIPT so the [ret]
    two instructions later resolves; the [s0] reload is symbolic ([asp])
    and so goes through [rvals] — note the placeholder for the named
    read, which still consumes a fresh [EVar] index. *)
Proof.
  intros regs mem code H2 H10 Hra Hs0.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  replace (0x1001274 : word) with (Z_to_bv 64 0x1001274) by bveq.
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 0x1001274) mem arom)
    6%nat (@nil bool) [ELit 0x1001178]
    [((2 : reg), EVar 32)] [Z_to_bv 64 (bv_unsigned asp - 0x20)]
    [Z_to_bv 64 0; asp] R HR Hms.
  1: (exists (word_to_le_bytes 8 asp); split;
      [ exact Hs0 | apply bytes_le_to_Z_8 ]).
  1: (exists (word_to_le_bytes 8 (0x1001178 : word)); split;
      [ exact Hra | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  { (* the [sp] pin *) exact H2. }
  exists R. split; [| split].
  - sym_regs HR. vm_compute. reflexivity.
  - sym_regs HR. first [ exact H10 | rewrite <- getr_nz by reg_neq_tac; exact H10 ].
  - eapply msteps_trans; [ exact Hms | ]. norm_pc; sym_pc_lit.
    eapply mst_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_100117c eq_refl) | apply mst_refl ].
Qed.

(* ================================================================= *)
(* argc < 2: straight to exit 2                                       *)
(* ================================================================= *)

Lemma target_wexit_lt2 : (length av < 2)%nat ->
  to_wexit target_segs
    (init_machine_state (run_segments target_segs inp asp amb) 0x1001158 target_phdrs asp amb arnd inp)
    [] (Z_to_bv 64 2).
(** FOURTEEN instructions in ONE reflective block: Zig's [_start] frame,
    its two spills and frame pointer, the [ld] of argc, the
    [auipc]/[jalr] call into [main], main's [argc < 2] test and — through
    the [ret] the call's link register makes literal — the exit tail up
    to the [ecall]. *)
Proof.
  intros Hlt2.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as Hlen.
  pose proof u_targcN as Hu.
  rewrite init_mkst. norm_pc.
  sym_block target_segs 14%nat [false] (@nil expr)
    [((1 : reg), ELit 0); ((8 : reg), ELit 0); ((2 : reg), EVar 32)] [asp]
    [targcN] RA HRA.
  { (* [bltu a2,a0] at 0x1001184 -> not taken, because [argc <= 1] *) sym_br. }
  { (* [ld a0,0(s0)] at 0x1001168 -> argc, out of the initial stack image *)
    replace (Z_to_bv 64 (bv_unsigned asp + 0)) with asp
      by (apply bv_eq; u_norm; lia);
    exists (word_le8 targcN); split;
      [ rewrite rdn_wrap_stack_above by lia;
        apply read_argc; apply target_bsb_nw
      | apply bytes_le_n_to_le_8 ]. }
  1-2: solve_store_ok.
  (* 0x100117c: the exit [ecall] *)
  eapply tw_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_100117c eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRA. vm_compute. reflexivity.
  - sym_regs HRA. reflexivity.
  - u_norm; lia.
Qed.

(* ================================================================= *)
(* Prologue (argc >= 2): init -> slen loop head at 0x1001288          *)
(* ================================================================= *)

Lemma target_prologue : (2 <= length av)%nat ->
  exists regsP,
    (reg_get regsP 2 = Z_to_bv 64 (bv_unsigned asp - 0x20) /\
     reg_get regsP 8 = tP /\ reg_get regsP 10 = tP /\
     reg_get regsP 1 = (0x10011ac : word) /\ reg_get regsP 11 = Z_to_bv 64 0) /\
    msteps target_segs
      (init_machine_state (run_segments target_segs inp asp amb) 0x1001158 target_phdrs asp amb arnd inp)
      (mkst regsP 0x1001288 tfmem arom).
(** EIGHTEEN instructions in ONE reflective block: Zig's [_start] frame
    and call into [main], main's [argc >= 2] test, its own frame with
    the [ra]/[s0] spills, the [ld] of [argv[1]] and the call into
    [slen], stopping at the loop head.  Four stores and two loads; as in
    the source, every obligation is stated against the ORIGINAL memory,
    so nothing peels an overlay.  [sym_block_ex] because the conclusion
    is existential in the exit register file; the exit memory is
    reconciled with [tfmem] by reverting the block's [msteps]. *)
Proof.
  intros H2.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as Hlen.
  pose proof u_targcN as Hu.
  destruct (target_ptr_bounds H2) as [HPge HPlt].
  rewrite init_mkst.
  sym_block_ex target_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 asp)
          (Z_to_bv 64 (Z.of_N 0x1001158))
          (wrap_mem inp amb target_phdrs (Z_to_bv 64 (Z.of_N 0x1001158)) asp arnd)
          (seg_rom (run_segments target_segs inp asp amb)))
    18%nat [true] (@nil expr)
    [((1 : reg), ELit 0); ((8 : reg), ELit 0); ((2 : reg), EVar 32)] [asp]
    [targcN; tP] RA HRA Hms.
  2,3,6,7: solve_store_ok.
  { (* [ld s0,8(a1)] at 0x100119c -> argv[1], out of the stack image *)
    replace (Z_to_bv 64 (bv_unsigned asp + 16)) with (asp + nat_to_word (8 + 8 * 1))
      by (apply bv_eq; rewrite word_add_nat; u_norm; lia);
    exists (word_le8 tP); split;
      [ rewrite rdn_wrap_stack_above by (rewrite word_add_nat; u_norm; lia);
        apply read_argv_ptr_k; [lia | apply target_bsb_nw]
      | apply bytes_le_n_to_le_8 ]. }
  { (* [bltu a2,a0] at 0x1001184 -> taken, because [argc >= 2] *) sym_br. }
  { (* [ld a0,0(s0)] at 0x1001168 -> argc, out of the initial stack image *)
    replace (Z_to_bv 64 (bv_unsigned asp + 0)) with asp
      by (apply bv_eq; u_norm; lia);
    exists (word_le8 targcN); split;
      [ rewrite rdn_wrap_stack_above by lia;
        apply read_argc; apply target_bsb_nw
      | apply bytes_le_n_to_le_8 ]. }
  exists RA. split.
  - repeat split; sym_regs HRA; sym_close.
  - replace (0x1001288 : word) with (Z_to_bv 64 0x1001288) by bveq.
    unfold tfmem, smem, awmem, arom.
    revert Hms. sym_mem_norm. exact (fun x => x).
Qed.

(* ================================================================= *)
(* slen loop: 0x1001288 .. 0x1001294                                  *)
(* ================================================================= *)

Lemma target_slen : (2 <= length av)%nat -> forall f j regs,
  reg_get regs 10 = tP -> reg_get regs 11 = nat_to_word j ->
  (j <= n)%nat -> (n - j <= f)%nat ->
  exists regs',
    (forall r : reg, r <> 11 -> r <> 12 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 11 = nat_to_word (S n) /\
    msteps target_segs (mkst regs 0x1001288 tfmem arom)
                       (mkst regs' 0x1001298 tfmem arom).
Proof.
  intros H2.
  destruct (target_ptr_bounds H2) as [HPge HPlt].
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as Hslen.
  pose proof (valid_argv_str_nz av 1 Hva ltac:(lia)) as Hnz.
  assert (Hbody : forall j regs, reg_get regs 10 = tP ->
    reg_get regs 11 = nat_to_word j -> (j <= n)%nat ->
    exists r3,
      r3 = regupd (regupd (regupd regs 12 (tP + nat_to_word j))
                          12 (Z_to_bv 64 (bv_unsigned (byte_at s j))))
                  11 (nat_to_word (S j)) /\
      msteps target_segs (mkst regs 0x1001288 tfmem arom)
                         (mkst r3 0x1001294 tfmem arom)).
  { intros j regs H10 H11 Hj.
    set (r1 := regupd regs 12 (tP + nat_to_word j)).
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001288 tfmem arom)
                 = MachineOk (mkst r1 0x100128c tfmem arom)).
    { rewrite (step_add target_segs regs 0x1001288 tfmem arom _ 12 10 11
                 TF_1001288 eq_refl TD_1001288).
      reduce_bv_eqb_ifs.
      getr_resolve. rewrite H10, H11. wlits. reflexivity. }
    set (r2 := regupd r1 12 (Z_to_bv 64 (bv_unsigned (byte_at s j)))).
    assert (E2 : RiscvSemantics.step target_segs (mkst r1 0x100128c tfmem arom)
                 = MachineOk (mkst r2 0x1001290 tfmem arom)).
    { rewrite (step_lbu target_segs r1 0x100128c tfmem arom _ 12 12 _ (byte_at s j)
                 TF_100128c eq_refl TD_100128c).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold r1. getr_resolve. rewrite v_addi_0.
        apply tread_str_byte; [exact H2 | exact Hj]. }
    set (r3 := regupd r2 11 (nat_to_word (S j))).
    assert (E3 : RiscvSemantics.step target_segs (mkst r2 0x1001290 tfmem arom)
                 = MachineOk (mkst r3 0x1001294 tfmem arom)).
    { rewrite (step_addi target_segs r2 0x1001290 tfmem arom _ 11 11 _
                 TF_1001290 eq_refl TD_1001290).
      reduce_bv_eqb_ifs.
      unfold r3, r2, r1. getr_resolve. rewrite H11.
      rewrite v_addi_Sj by lia. wlits. reflexivity. }
    exists r3. split; [reflexivity|].
    eapply mst_step; [reflexivity | exact E1 |].
    eapply mst_step; [reflexivity | exact E2 |].
    eapply mst_step; [reflexivity | exact E3 |].
    apply mst_refl. }
  assert (Hexit : forall j regs, reg_get regs 10 = tP ->
    reg_get regs 11 = nat_to_word j -> (j <= n)%nat -> j = n ->
    exists regs',
      (forall r : reg, r <> 11 -> r <> 12 -> reg_get regs' r = reg_get regs r) /\
      reg_get regs' 11 = nat_to_word (S n) /\
      msteps target_segs (mkst regs 0x1001288 tfmem arom)
                         (mkst regs' 0x1001298 tfmem arom)).
  { intros j regs H10 H11 Hj Hjeq.
    destruct (Hbody j regs H10 H11 Hj) as [r3 [Hr3 Hms]].
    assert (Hb0 : byte_at s j = Z_to_bv 8 0) by (rewrite Hjeq; apply byte_at_len).
    exists r3. split; [| split].
    - intros r Hr11 Hr12. rewrite Hr3.
      rewrite !regupd_other by assumption. reflexivity.
    - rewrite Hr3, regupd_same, Hjeq. reflexivity.
    - eapply msteps_trans; [exact Hms|].
      (* 0x1001294: bne a2,x0 -> fall through (NUL byte) *)
      eapply mst_step;
        [ reflexivity
        | eapply step_bne_ft;
          [ exact TF_1001294 | reflexivity | exact TD_1001294
          | rewrite Hr3; getr_resolve; rewrite Hb0; exact c_eq_0_true ]
        | norm_pc; apply mst_refl ]. }
  induction f as [|f IH]; intros j regs H10 H11 Hj Hf.
  - apply (Hexit j regs H10 H11 Hj). lia.
  - destruct (Nat.eq_dec j n) as [Hjeq | Hjne].
    + apply (Hexit j regs H10 H11 Hj). exact Hjeq.
    + (* j < n: byte nonzero, loop *)
      assert (Hjlt : (j < n)%nat) by lia.
      assert (Hbnz : byte_at s j <> Z_to_bv 8 0) by (apply byte_at_nz; assumption).
      destruct (Hbody j regs H10 H11 Hj) as [r3 [Hr3 Hms]].
      assert (H10' : reg_get r3 10 = tP)
        by (rewrite Hr3; rewrite !regupd_other by reg_neq_tac; exact H10).
      assert (H11' : reg_get r3 11 = nat_to_word (S j))
        by (rewrite Hr3; apply regupd_same).
      destruct (IH (S j) r3 H10' H11' ltac:(lia) ltac:(lia))
        as [regs' [Hfr [H11f Hms']]].
      exists regs'. split; [| split].
      * intros r Hr11 Hr12.
        rewrite (Hfr r Hr11 Hr12). rewrite Hr3.
        rewrite !regupd_other by assumption. reflexivity.
      * exact H11f.
      * eapply msteps_trans; [exact Hms|].
        (* 0x1001294: bne a2,x0 -> taken *)
        eapply mst_step;
          [ reflexivity
          | eapply step_bne_tk;
            [ exact TF_1001294 | reflexivity | exact TD_1001294
            | rewrite Hr3; getr_resolve;
              apply c_eq_0_false; rewrite u_zext8;
              apply byte_nz_u; exact Hbnz ]
          | norm_pc; exact Hms' ].
Qed.

(* ================================================================= *)
(* From the slen return to the branch on n                            *)
(* ================================================================= *)

(** After the prologue and slen: at 0x10011ac with a0 = n. *)
Lemma target_after_slen : (2 <= length av)%nat ->
  exists regsA,
    (reg_get regsA 2 = Z_to_bv 64 (bv_unsigned asp - 0x20) /\
     reg_get regsA 8 = tP /\ reg_get regsA 10 = tnN) /\
    msteps target_segs
      (init_machine_state (run_segments target_segs inp asp amb) 0x1001158 target_phdrs asp amb arnd inp)
      (mkst regsA 0x10011ac tfmem arom).
Proof.
  intros H2.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as HnN'.
  destruct (target_prologue H2) as [regsP [[HP2 [HP8 [HP10 [HP1 HP11]]]] HmsP]].
  destruct (target_slen H2 n 0 regsP HP10 ltac:(rewrite HP11; reflexivity)
              ltac:(lia) ltac:(lia)) as [regsL [HfrL [H11L HmsL]]].
  eexists. refine (conj _ _).
  2:{
    eapply msteps_trans; [exact HmsP|].
    eapply msteps_trans; [exact HmsL|].
    (* 0x1001298: addi a0,a1,-1 -> n *)
    stepiv TF_1001298 TD_1001298 tnN
      ltac:(getr_resolve; rewrite H11L; imm_norm; apply v_addi_ntw_pred; lia).
    (* 0x100129c: ret -> 0x10011ac *)
    stepjr TF_100129c TD_100129c (0x10011ac : word) ltac:(getr_resolve; regupd_resolve; rewrite (HfrL 1) by reg_neq_tac; exact HP1).
    apply mst_refl.
  }
  split; [|split].
  - regupd_resolve.
    rewrite (HfrL 2) by reg_neq_tac. exact HP2.
  - regupd_resolve.
    rewrite (HfrL 8) by reg_neq_tac. exact HP8.
  - regupd_resolve. reflexivity.
Qed.

(* ================================================================= *)
(* n > 4095: exit 3                                                   *)
(* ================================================================= *)

Lemma target_wexit_len3 : (2 <= length av)%nat -> (4095 < n)%nat ->
  to_wexit target_segs
    (init_machine_state (run_segments target_segs inp asp amb) 0x1001158 target_phdrs asp amb arnd inp)
    [] (Z_to_bv 64 3).
(** FIVE instructions in ONE reflective block: the [n >> 12] size test
    Zig compiles the [n > 4095] check to, and the jump into the shared
    epilogue with [a0 = 3]. *)
Proof.
  intros H2 Hn.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as HnN'.
  destruct (target_after_slen H2) as [regsA [[HA2 [HA8 HA10]] HmsA]].
  eapply msteps_to_wexit; [exact HmsA|].
  sym_block target_segs 5%nat [false] (@nil expr)
    [((0 : reg), ELit 0); ((10 : reg), EVar 32)] [tnN] (@nil word) RA HRA.
  { (* [beq a0,x0] at 0x10011b4 -> not taken: [n >> 12] is nonzero *)
    rewrite v_srl_12. apply c_eq_0_false.
    rewrite v_srli_div by lia.
    unfold tnN; rewrite u_ntw by lia.
    change (2^12)%Z with 4096%Z.
    assert (Hq : (1 <= Z.of_nat n / 4096)%Z)
      by (apply Z.div_le_lower_bound; lia).
    lia. }
  { (* the [a0] pin: slen's result *)
    rewrite getr_nz by reg_neq_tac. exact HA10. }
  (* epilogue with a0 = 3 *)
  edestruct (target_epilogue RA tfmem (Z_to_bv 64 3))
    as [regsE [HE17 [HE10 HmsE]]].
  - sym_regs HRA. rewrite getr_nz by reg_neq_tac. exact HA2.
  - sym_regs HRA. reflexivity.
  - exact tfread_slot_ra.
  - exact tfread_slot_s0.
  - eapply msteps_to_wexit; [exact HmsE|].
    apply tw_exit_coden; [exact HE17 | exact HE10 | u_norm; lia].
Qed.

(* ================================================================= *)
(* n <= 4095: run to the mmap ecall                                   *)
(* ================================================================= *)

Lemma target_to_mmap : (2 <= length av)%nat -> (n <= 4095)%nat ->
  exists regsE,
    reg_get regsE 2 = Z_to_bv 64 (bv_unsigned asp - 0x20) /\
    reg_get regsE 8 = tP /\ reg_get regsE 16 = tnN /\
    reg_get regsE 11 = Z_to_bv 64 4096 /\
    reg_get regsE 12 = Z_to_bv 64 3 /\
    reg_get regsE 13 = Z_to_bv 64 34 /\
    reg_get regsE 14 = Z_to_bv 64 (2^64 - 1) /\
    reg_get regsE 15 = Z_to_bv 64 0 /\
    reg_get regsE 10 = Z_to_bv 64 0 /\
    bv_unsigned (getr regsE 17) = 222%Z /\
    msteps target_segs
      (init_machine_state (run_segments target_segs inp asp amb) 0x1001158 target_phdrs asp amb arnd inp)
      {| ms_regs := regsE; ms_fregs := fp_regs; ms_pc_val := 0x10011d8;
         ms_svc_pending := Some (getr regsE 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := tfmem; ms_rom := arom |}.
(** NINE instructions in ONE reflective block, with no memory traffic:
    the size test taken the other way and main's six [li]s of the mmap
    arguments, stopping at the [ecall] that is the [tmw] branch point. *)
Proof.
  intros H2 Hn.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as HnN'.
  destruct (target_after_slen H2) as [regsA [[HA2 [HA8 HA10]] HmsA]].
  replace (0x10011ac : word) with (Z_to_bv 64 0x10011ac) in HmsA by bveq.
  sym_block_ex target_segs (mkst regsA (Z_to_bv 64 0x10011ac) tfmem arom)
    9%nat [true] (@nil expr)
    [((0 : reg), ELit 0); ((10 : reg), EVar 32)] [tnN] (@nil word) RA HRA Hms.
  { (* [beq a0,x0] at 0x10011b4 -> taken: [n >> 12] is zero *)
    rewrite v_srl_12. apply c_eq_0_of_u.
    rewrite v_srli_div by lia.
    unfold tnN; rewrite u_ntw by lia.
    change (2^12)%Z with 4096%Z.
    apply Z.div_small; lia. }
  { (* the [a0] pin: slen's result *)
    rewrite getr_nz by reg_neq_tac. exact HA10. }
  exists RA.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ _)))))))))).
  1: (sym_regs HRA; rewrite getr_nz by reg_neq_tac; exact HA2).
  1: (sym_regs HRA; rewrite getr_nz by reg_neq_tac; exact HA8).
  (* a6, a1..a5: no raw [vm_compute] on a bv record (its normal form
     carries the well-formedness proof); [bveq] compares the unsigned
     values of a closed goal *)
  1-6: (sym_regs HRA;
        first [ reflexivity | apply v_lui_4096 | assumption | (f_equal; lia)
              | (apply bv_eq; u_norm; lia) | bveq ]).
  1: (* a0: [n >> 12], zero because [n <= 4095] *)
     (sym_regs HRA; rewrite ?v_srl_12; apply bv_eq;
      rewrite v_srli_div by lia; unfold tnN; rewrite u_ntw by lia;
      change (2^12)%Z with 4096%Z; rewrite Z.div_small by lia; reflexivity).
  1: (sym_regs HRA; first [ reflexivity | (u_norm; lia) ]).
  eapply msteps_trans; [ exact HmsA | ].
  eapply msteps_trans; [ exact Hms | ]. norm_pc; sym_pc_lit.
  eapply mst_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_10011d8 eq_refl) | apply mst_refl ].
Qed.

(* ================================================================= *)
(* Failure continuation: exit 4                                       *)
(* ================================================================= *)

Lemma target_fail_twm : forall model regs e,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 0x20) ->
  twm target_segs (mkst (regupd regs 10 (errno_ret e)) 0x10011dc tfmem arom)
      model [] (Z_to_bv 64 4).
(** THREE instructions in ONE reflective block: the [bltz] the negative
    errno takes, [li a0,4] and the jump into the shared epilogue. *)
Proof.
  intros model regs e He1 He2 Hr2.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (errno_ret_range e He1 He2) as [Her1 Her2].
  sym_block target_segs 3%nat [true] (@nil expr)
    [((0 : reg), ELit 0); ((10 : reg), EVar 32)]
    [errno_ret e] (@nil word) RA HRA.
  { (* [bltz a0] at 0x10011dc -> taken: the mmap failed *)
    apply (c_lts_neg_0 (errno_ret e)); lia. }
  { (* the [a0] pin *) getr_resolve; regupd_resolve; reflexivity. }
  (* epilogue with a0 = 4 *)
  edestruct (target_epilogue RA tfmem (Z_to_bv 64 4))
    as [regsE [HE17 [HE10 HmsE]]].
  - sym_regs HRA. getr_resolve; regupd_resolve; exact Hr2.
  - sym_regs HRA. reflexivity.
  - exact tfread_slot_ra.
  - exact tfread_slot_s0.
  - eapply msteps_twm; [exact HmsE|].
    apply twm_exit_coden; [exact HE17 | exact HE10 | u_norm; lia].
Qed.

(* ================================================================= *)
(* Success continuation                                               *)
(* ================================================================= *)

Section TargetSucc.

Variable aG : word.
Hypothesis HaPos : (0 < bv_unsigned aG)%Z.
Hypothesis HaAl : (bv_unsigned aG mod page_size = 0)%Z.
Hypothesis HaCeil : (bv_unsigned aG + 4096 <= bv_unsigned asp - stack_max_size)%Z.
Hypothesis Hda : (bv_unsigned aG + 4096 <= 0x1000000)%Z \/ (0x1001000 <= bv_unsigned aG)%Z.
Hypothesis Hdb : (bv_unsigned aG + 4096 <= 0x1001000)%Z \/ (0x1002000 <= bv_unsigned aG)%Z.
Hypothesis H2av : (2 <= length av)%nat.
Hypothesis Hnle : (n <= 4095)%nat.

Lemma tnN_le : (Z.of_nat n <= 4095)%Z.
Proof. lia. Qed.

Definition zmemT : word -> option byte := zfill aG (Z_to_bv 64 4096) tfmem.
Definition cmemT (i : nat) : word -> option byte :=
  wbytes zmemT aG (upperv (firstn i s)).

Lemma tcmem_S : forall i, (i < n)%nat ->
  cmemT (S i) = wbytes (cmemT i) (aG + nat_to_word i) [upperb (byte_at s i)].
Proof.
  intros i Hi. unfold cmemT.
  rewrite (upperv_firstn_S s i Hi).
  rewrite wbytes_snoc.
  rewrite length_upperv_firstn by lia.
  reflexivity.
Qed.

Lemma tcread_str_byte : forall i j, (i <= n)%nat -> (j <= n)%nat ->
  rdn target_segs (cmemT i) (tP + nat_to_word j) 1%nat = Some [byte_at s j].
Proof.
  intros i j Hi Hj.
  destruct (target_ptr_bounds H2av) as [Hge Hup].
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tnN_le.
  unfold cmemT.
  rewrite rdn_wbytes_disjoint
    by (rewrite ?length_upperv_firstn by lia;
        rewrite ?word_add_nat; u_norm; lia).
  unfold zmemT.
  rewrite rdn_zfill_out
    by (rewrite ?word_add_nat; u_norm; first [ lia | right; lia ]).
  apply tread_str_byte; assumption.
Qed.

(** The mmap grant is zero-mapped ([zmemT] = [zfill aG 4096 _]), so
    every byte of [aG, aG+4096) is writable whatever sits underneath —
    which is what a machine store into the copied buffer now has to
    show. *)
Lemma tgrant_store_ok : forall (m : word -> option byte) (a : word) (k : nat),
  (bv_unsigned aG <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= bv_unsigned aG + 4096)%Z ->
  store_ok target_segs (zfill aG (Z_to_bv 64 4096) m) a k = true.
Proof.
  intros m a k Hx1 Hx2. pose proof HaCeil. pose proof asp_hi_num. unfold stack_max_size in *. unfold zfill. apply store_ok_zmem.
  - lia.
  - exact Hx1.
  - rewrite u_Z2bv by lia. exact Hx2.
Qed.

(* ----------------------------------------------------------------- *)
(* The branchless copy loop: 0x10011ec .. 0x1001218                   *)
(* ----------------------------------------------------------------- *)

Lemma target_copy : forall f i regs,
  reg_get regs 8 = tP + nat_to_word i ->
  reg_get regs 10 = aG + nat_to_word i ->
  reg_get regs 11 = nat_to_word (n - i) ->
  (i < n)%nat -> (n - i <= f)%nat ->
  exists regs',
    (forall r : reg, r <> 8 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 14 ->
       reg_get regs' r = reg_get regs r) /\
    msteps target_segs (mkst regs 0x10011ec (cmemT i) arom)
                       (mkst regs' 0x100121c (wbytes zmemT aG (upperv s)) arom).
Proof.
  destruct (target_ptr_bounds H2av) as [HPge HPlt].
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. pose proof tnN_le as HnN.
  pose proof (u64_range aG) as HaR.
  assert (EMs : wbytes zmemT aG (upperv s) = cmemT n).
  { unfold cmemT. rewrite firstn_all. reflexivity. }
  induction f as [|f IH]; intros i regs H8 H10 H11 Hi Hf; [lia|].
  set (b := byte_at s i) in *.
  pose proof (u8_range b) as Hb8.
  set (fl := if islower b then Z_to_bv 64 1 else Z_to_bv 64 0).
  set (m1 := if islower b then Z_to_bv 64 (2^64 - 1) else Z_to_bv 64 0).
  set (msk := if islower b then Z_to_bv 64 224 else Z_to_bv 64 0).
  assert (Efl : v_sltiu (usub97 b) 26 = fl).
  { rewrite v_sltiu_26. unfold fl.
    destruct (islower b) eqn:El.
    - pose proof (usub97_le25 b El).
      rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
    - pose proof (usub97_gt25 b El).
      rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
  assert (Em1 : v_subw (Z_to_bv 64 0) fl = m1).
  { unfold fl, m1. destruct (islower b); [apply negw_1 | apply negw_0]. }
  assert (Emsk : v_andi m1 224 = msk).
  { unfold m1, msk. destruct (islower b); [apply andi_m1_224 | apply andi_0_224]. }
  assert (Estore : Z_to_bv 8 (bv_unsigned (v_add (Z_to_bv 64 (bv_unsigned b)) msk))
                   = upperb b).
  { unfold msk. destruct (islower b) eqn:El.
    - apply target_upper_lo. exact El.
    - apply target_upper_hi. exact El. }
  (* 0x10011ec: lbu a2,0(s0) *)
  set (r1 := regupd regs 12 (Z_to_bv 64 (bv_unsigned b))).
  assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x10011ec (cmemT i) arom)
               = MachineOk (mkst r1 0x10011f0 (cmemT i) arom)).
  { rewrite (step_lbu target_segs regs 0x10011ec (cmemT i) arom _ 12 8 _ b
               TF_10011ec eq_refl TD_10011ec).
    - reduce_bv_eqb_ifs. wlits. reflexivity.
    - getr_resolve. rewrite H8. rewrite v_addi_0.
      apply tcread_str_byte; lia. }
  (* 0x10011f0: addi a1,a1,-1 *)
  set (r2 := regupd r1 11 (nat_to_word (n - S i))).
  assert (E2 : RiscvSemantics.step target_segs (mkst r1 0x10011f0 (cmemT i) arom)
               = MachineOk (mkst r2 0x10011f4 (cmemT i) arom)).
  { rewrite (step_addi target_segs r1 0x10011f0 (cmemT i) arom _ 11 11 _
               TF_10011f0 eq_refl TD_10011f0).
    reduce_bv_eqb_ifs.
    unfold r2, r1. getr_resolve. rewrite H11. imm_norm.
    replace (n - i)%nat with (S (n - S i))%nat by lia.
    rewrite v_addi_ntw_pred by lia. wlits. reflexivity. }
  (* 0x10011f4: addi s0,s0,1 *)
  set (r3 := regupd r2 8 (tP + nat_to_word (S i))).
  assert (E3 : RiscvSemantics.step target_segs (mkst r2 0x10011f4 (cmemT i) arom)
               = MachineOk (mkst r3 0x10011f8 (cmemT i) arom)).
  { rewrite (step_addi target_segs r2 0x10011f4 (cmemT i) arom _ 8 8 _
               TF_10011f4 eq_refl TD_10011f4).
    reduce_bv_eqb_ifs.
    unfold r3, r2, r1. getr_resolve. rewrite H8. imm_norm.
    rewrite v_addi_word_Sj. wlits. reflexivity. }
  (* 0x10011f8: addi a4,a2,-97 *)
  set (r4 := regupd r3 14 (Z_to_bv 64 (bv_unsigned b - 97))).
  assert (E4 : RiscvSemantics.step target_segs (mkst r3 0x10011f8 (cmemT i) arom)
               = MachineOk (mkst r4 0x10011fc (cmemT i) arom)).
  { rewrite (step_addi target_segs r3 0x10011f8 (cmemT i) arom _ 14 12 _
               TF_10011f8 eq_refl TD_10011f8).
    reduce_bv_eqb_ifs.
    unfold r4, r3, r2, r1. getr_resolve. imm_norm.
    rewrite (v_addi_byte_m97 b). wlits. reflexivity. }
  (* 0x10011fc: andi a4,a4,255 *)
  set (r5 := regupd r4 14 (usub97 b)).
  assert (E5 : RiscvSemantics.step target_segs (mkst r4 0x10011fc (cmemT i) arom)
               = MachineOk (mkst r5 0x1001200 (cmemT i) arom)).
  { rewrite (step_andi target_segs r4 0x10011fc (cmemT i) arom _ 14 14 _
               TF_10011fc eq_refl TD_10011fc).
    reduce_bv_eqb_ifs.
    unfold r5, r4. getr_resolve. imm_norm.
    rewrite (usub97_andi b). wlits. reflexivity. }
  (* 0x1001200: sltiu a4,a4,26 *)
  set (r6 := regupd r5 14 fl).
  assert (E6 : RiscvSemantics.step target_segs (mkst r5 0x1001200 (cmemT i) arom)
               = MachineOk (mkst r6 0x1001204 (cmemT i) arom)).
  { rewrite (step_sltiu target_segs r5 0x1001200 (cmemT i) arom _ 14 14 _
               TF_1001200 eq_refl TD_1001200).
    reduce_bv_eqb_ifs.
    unfold r6, r5. getr_resolve. imm_norm.
    rewrite Efl. wlits. reflexivity. }
  (* 0x1001204: negw a4,a4 *)
  set (r7 := regupd r6 14 m1).
  assert (E7 : RiscvSemantics.step target_segs (mkst r6 0x1001204 (cmemT i) arom)
               = MachineOk (mkst r7 0x1001208 (cmemT i) arom)).
  { rewrite (step_subw target_segs r6 0x1001204 (cmemT i) arom _ 14 0 14
               TF_1001204 eq_refl TD_1001204).
    reduce_bv_eqb_ifs.
    unfold r7, r6. getr_resolve.
    rewrite Em1. wlits. reflexivity. }
  (* 0x1001208: andi a4,a4,224 *)
  set (r8 := regupd r7 14 msk).
  assert (E8 : RiscvSemantics.step target_segs (mkst r7 0x1001208 (cmemT i) arom)
               = MachineOk (mkst r8 0x100120c (cmemT i) arom)).
  { rewrite (step_andi target_segs r7 0x1001208 (cmemT i) arom _ 14 14 _
               TF_1001208 eq_refl TD_1001208).
    reduce_bv_eqb_ifs.
    unfold r8, r7. getr_resolve. imm_norm.
    rewrite Emsk. wlits. reflexivity. }
  (* 0x100120c: add a2,a2,a4 *)
  set (r9 := regupd r8 12 (v_add (Z_to_bv 64 (bv_unsigned b)) msk)).
  assert (E9 : RiscvSemantics.step target_segs (mkst r8 0x100120c (cmemT i) arom)
               = MachineOk (mkst r9 0x1001210 (cmemT i) arom)).
  { rewrite (step_add target_segs r8 0x100120c (cmemT i) arom _ 12 12 14
               TF_100120c eq_refl TD_100120c).
    reduce_bv_eqb_ifs.
    unfold r9, r8, r7, r6, r5, r4, r3, r2, r1. getr_resolve. wlits. reflexivity. }
  (* 0x1001210: sb a2,0(a0) -> upperb b at aG+i *)
  assert (Hcm : cmemT (S i) = wbytes (cmemT i) (aG + nat_to_word i) [upperb b]).
  { apply tcmem_S. exact Hi. }
  assert (E10 : RiscvSemantics.step target_segs (mkst r9 0x1001210 (cmemT i) arom)
                = MachineOk (mkst r9 0x1001214 (cmemT (S i)) arom)).
  { rewrite Hcm.
    rewrite (step_sb_at target_segs r9 0x1001210 (cmemT i) arom _ 10 12 _
               (aG + nat_to_word i) (v_add (Z_to_bv 64 (bv_unsigned b)) msk) (upperb b)
               TF_1001210 eq_refl TD_1001210).
    - wlits. reflexivity.
    - unfold r9, r8, r7, r6, r5, r4, r3, r2, r1. getr_resolve.
      rewrite H10. apply v_addi_0.
    - unfold r9. getr_resolve. reflexivity.
    - exact Estore.
    - store_ok_peel; apply tgrant_store_ok;
        rewrite ?word_add_nat, ?u_Z2bv by lia; u_norm; lia. }
  (* 0x1001214: addi a0,a0,1 *)
  set (r10 := regupd r9 10 (aG + nat_to_word (S i))).
  assert (E11 : RiscvSemantics.step target_segs (mkst r9 0x1001214 (cmemT (S i)) arom)
                = MachineOk (mkst r10 0x1001218 (cmemT (S i)) arom)).
  { rewrite (step_addi target_segs r9 0x1001214 (cmemT (S i)) arom _ 10 10 _
               TF_1001214 eq_refl TD_1001214).
    reduce_bv_eqb_ifs.
    unfold r10, r9, r8, r7, r6, r5, r4, r3, r2, r1. getr_resolve.
    rewrite H10. imm_norm. rewrite v_addi_word_Sj. wlits. reflexivity. }
  destruct (Nat.eq_dec (S i) n) as [HSeq | HSne].
  - (* last byte copied: fall through to 0x100121c *)
    assert (E12 : RiscvSemantics.step target_segs (mkst r10 0x1001218 (cmemT (S i)) arom)
                  = MachineOk (mkst r10 0x100121c (cmemT (S i)) arom)).
    { rewrite (step_bne_ft target_segs r10 0x1001218 (cmemT (S i)) arom _ 11 0 _
                 TF_1001218 eq_refl TD_1001218).
      - wlits. reflexivity.
      - unfold r10, r9, r8, r7, r6, r5, r4, r3, r2. getr_resolve.
        replace (n - S i)%nat with 0%nat by lia.
        exact c_eq_0_true. }
    exists r10. split.
    + intros r Hr8 Hr10 Hr11 Hr12 Hr14.
      unfold r10, r9, r8, r7, r6, r5, r4, r3, r2, r1.
      rewrite !regupd_other by assumption. reflexivity.
    + rewrite EMs. rewrite <- HSeq.
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      eapply mst_step; [reflexivity | exact E7 |].
      eapply mst_step; [reflexivity | exact E8 |].
      eapply mst_step; [reflexivity | exact E9 |].
      eapply mst_step; [reflexivity | exact E10 |].
      eapply mst_step; [reflexivity | exact E11 |].
      eapply mst_step; [reflexivity | exact E12 |].
      apply mst_refl.
  - (* more bytes: branch back and recurse *)
    assert (HSlt : (S i < n)%nat) by lia.
    assert (E12 : RiscvSemantics.step target_segs (mkst r10 0x1001218 (cmemT (S i)) arom)
                  = MachineOk (mkst r10 0x10011ec (cmemT (S i)) arom)).
    { rewrite (step_bne_tk target_segs r10 0x1001218 (cmemT (S i)) arom _ 11 0 _
                 TF_1001218 eq_refl TD_1001218).
      - wlits. reflexivity.
      - unfold r10, r9, r8, r7, r6, r5, r4, r3, r2. getr_resolve.
        apply c_eq_0_false. rewrite u_ntw by lia. lia. }
    assert (H8' : reg_get r10 8 = tP + nat_to_word (S i)).
    { unfold r10, r9, r8, r7, r6, r5, r4, r3.
      rewrite !regupd_other by reg_neq_tac. apply regupd_same. }
    assert (H10' : reg_get r10 10 = aG + nat_to_word (S i))
      by (unfold r10; apply regupd_same).
    assert (H11' : reg_get r10 11 = nat_to_word (n - S i)).
    { unfold r10, r9, r8, r7, r6, r5, r4, r3, r2.
      rewrite !regupd_other by reg_neq_tac. apply regupd_same. }
    destruct (IH (S i) r10 H8' H10' H11' HSlt ltac:(lia))
      as [regs' [Hfr Hms]].
    exists regs'. split.
    + intros r Hr8 Hr10 Hr11 Hr12 Hr14.
      rewrite (Hfr r Hr8 Hr10 Hr11 Hr12 Hr14).
      unfold r10, r9, r8, r7, r6, r5, r4, r3, r2, r1.
      rewrite !regupd_other by assumption. reflexivity.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      eapply mst_step; [reflexivity | exact E7 |].
      eapply mst_step; [reflexivity | exact E8 |].
      eapply mst_step; [reflexivity | exact E9 |].
      eapply mst_step; [reflexivity | exact E10 |].
      eapply mst_step; [reflexivity | exact E11 |].
      eapply mst_step; [reflexivity | exact E12 |].
      exact Hms.
Qed.

(* ----------------------------------------------------------------- *)
(* From 0x100121c: newline store, the write, munmap, exit 0           *)
(* ----------------------------------------------------------------- *)

(** The tail after the put loop: [munmap] the grant, then exit 0.
    Entered at 0x1001250 with a3 = the grant base; a0/a1/a2 are dead. *)
Lemma target_out_tail : forall model regs,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 0x20) ->
  reg_get regs 13 = aG ->
  map_has (vm_maps (m_vmmaps model)) aG (Z_to_bv 64 4096) = true ->
  twm target_segs (mkst regs 0x1001250 (wbytes zmemT aG (out_buf s)) arom)
      model [] (Z_to_bv 64 0).
Proof.
  intros model regs H2r H13 Hmap.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof tnN_le as HnN.
  pose proof (u64_range aG) as HaR.
  (* ---- 0x1001250 .. 0x1001258: the [munmap] argument setup. *)
  sym_block target_segs 3%nat (@nil bool) (@nil expr)
    [((13 : reg), EVar 32)] [aG] (@nil word) RC HRC.
  { exact H13. }
  (* 0x100125c: ecall -> munmap *)
  chain_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_100125c eq_refl) | ].
  eapply twm_munmap_rec.
  { sym_regs HRC. reflexivity. }
  { sym_regs HRC. reflexivity. }
  { sym_regs HRC. first [ reflexivity | apply v_lui_4096 ]. }
  { exact HaAl. }
  { intro Hc. apply (f_equal bv_unsigned) in Hc.
    change (bv_unsigned (Z_to_bv 64 4096)) with 4096%Z in Hc.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc.
    lia. }
  { change (bv_unsigned (Z_to_bv 64 4096)) with 4096%Z.
    rewrite page_round_up_Z_4096. unfold TASK_SIZE. pose proof HaCeil. pose proof asp_hi_num. unfold stack_max_size in *. lia. }
  { rewrite pru_4096. exact Hmap. }
  { (* munmap refused ([munmap_errnos]): [li a0,0] at 0x1001260 makes
       the exit code 0 whatever munmap answered *)
    intros e _. try norm_pc.
    sym_block target_segs 2%nat (@nil bool) (@nil expr) (@nil (reg * expr))
      (@nil word) (@nil word) RD HRD.
    lazymatch goal with
    | |- twm _ (mkst ?R _ ?M _) _ _ _ =>
      edestruct (target_epilogue R M (Z_to_bv 64 0)) as [regsE [HE17 [HE10 HmsE]]]
    end.
    { sym_regs HRD. sym_regs HRC. exact H2r. }
    { sym_regs HRD. reflexivity. }
    { rewrite rdn_wbytes_disjoint
        by (rewrite ?length_out_buf; u_norm; lia).
      progress unfold zmemT.
      rewrite (rdn_zfill_out target_segs aG (Z_to_bv 64 4096) tfmem
                 (Z_to_bv 64 (bv_unsigned asp - 0x18)) 8%nat)
        by (u_norm; first [ lia | right; lia ]).
      exact tfread_slot_ra. }
    { rewrite rdn_wbytes_disjoint
        by (rewrite ?length_out_buf; u_norm; lia).
      progress unfold zmemT.
      rewrite (rdn_zfill_out target_segs aG (Z_to_bv 64 4096) tfmem
                 (Z_to_bv 64 (bv_unsigned asp - 0x20)) 8%nat)
        by (u_norm; first [ lia | right; lia ]).
      exact tfread_slot_s0. }
    eapply msteps_twm; [exact HmsE|].
    apply twm_exit_coden; [exact HE17 | exact HE10 | u_norm; lia]. }
  rewrite pru_4096.
  (* ---- 0x1001260 .. 0x1001264: main's [li a0,0] and the jump into
     the shared epilogue. *)
  sym_block target_segs 2%nat (@nil bool) (@nil expr) (@nil (reg * expr))
    (@nil word) (@nil word) RD HRD.
  (* epilogue with a0 = 0 *)
  lazymatch goal with
  | |- twm _ (mkst ?R _ ?M _) _ _ _ =>
    edestruct (target_epilogue R M (Z_to_bv 64 0)) as [regsE [HE17 [HE10 HmsE]]]
  end.
  { sym_regs HRD. sym_regs HRC. exact H2r. }
  { sym_regs HRD. reflexivity. }
  { rewrite rdn_unfill_out by (u_norm; first [ lia | right; lia ]).
    rewrite rdn_wbytes_disjoint
      by (rewrite ?length_out_buf; u_norm; lia).
    progress unfold zmemT.
    rewrite (rdn_zfill_out target_segs aG (Z_to_bv 64 4096) tfmem
               (Z_to_bv 64 (bv_unsigned asp - 0x18)) 8%nat)
      by (u_norm; first [ lia | right; lia ]).
    exact tfread_slot_ra. }
  { rewrite rdn_unfill_out by (u_norm; first [ lia | right; lia ]).
    rewrite rdn_wbytes_disjoint
      by (rewrite ?length_out_buf; u_norm; lia).
    progress unfold zmemT.
    rewrite (rdn_zfill_out target_segs aG (Z_to_bv 64 4096) tfmem
               (Z_to_bv 64 (bv_unsigned asp - 0x20)) 8%nat)
      by (u_norm; first [ lia | right; lia ]).
    exact tfread_slot_s0. }
  eapply msteps_twm; [exact HmsE|].
  apply twm_exit_coden; [exact HE17 | exact HE10 | u_norm; lia].
Qed.

(** The put-style write-all retry loop at 0x1001240: register-only, so
    the memory (and every register outside a0/a1/a2) is carried through
    unchanged.  [blez a0]'s error arm is dead because every delivery is
    nonempty. *)
Lemma tgt_put_wall : forall model fuel (rest : list byte) (p : word) k regs,
  (length rest <= fuel)%nat ->
  (1 <= k)%nat -> (k <= length rest)%nat ->
  (Z.of_nat (length rest) <= 4096)%Z ->
  (0 < bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) <= bv_unsigned asp)%Z ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 0x20) ->
  reg_get regs 10 = len_word (firstn k rest) ->
  reg_get regs 11 = p ->
  reg_get regs 12 = len_word rest ->
  reg_get regs 13 = aG ->
  bv_unsigned (reg_get regs 17) = 64%Z ->
  map_has (vm_maps (m_vmmaps model)) aG (Z_to_bv 64 4096) = true ->
  rdn target_segs (wbytes zmemT aG (out_buf s)) p (length rest) = Some rest ->
  twm_tail target_segs (mkst regs 0x1001240 (wbytes zmemT aG (out_buf s)) arom)
    model (skipn k rest) [] (Z_to_bv 64 0).
Proof.
  intros model fuel. induction fuel as [|fuel IH];
    intros rest p k regs Hfuel Hk1 Hk2 Hlen Hplo Hphi
           H2r H10 H11 H12 H13 H17 Hmap Hread.
  { lia. }
  pose proof asp_hi_num as Hahi.
  (* 0x1001240: blez a0 falls through (the delivery is nonempty) *)
  step_intro;
    [ reflexivity
    | eapply step_bge_ft;
      [ exact TF_1001240 | reflexivity | exact TD_1001240
      | getr_resolve; rewrite H10; apply c_lts_0_pos;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x1001244: add a1,a1,a0 *)
  stepiv TF_1001244 TD_1001244 (Z_to_bv 64 (bv_unsigned p + Z.of_nat k))
    ltac:(getr_resolve; rewrite H11, H10; apply v_add_len_firstn_Z; lia).
  (* 0x1001248: sub a2,a2,a0 *)
  stepiv TF_1001248 TD_1001248 (len_word (skipn k rest))
    ltac:(getr_resolve; rewrite H12, H10; apply v_sub_len_firstn; lia).
  destruct (Nat.eq_dec k (length rest)) as [-> | Hne].
  - (* full delivery: bnez not taken, fall into the munmap tail *)
    rewrite skipn_all.
    step_intro;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact TF_100124c | reflexivity | exact TD_100124c
        | getr_resolve; apply c_eq_0_of_u; reflexivity ]
      | norm_pc ].
    apply twmt_done. apply target_out_tail.
    + regupd_resolve; exact H2r.
    + regupd_resolve; exact H13.
    + exact Hmap.
  - (* short delivery: bnez taken, reissue on the remainder *)
    step_intro;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact TF_100124c | reflexivity | exact TD_100124c
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* 0x1001238: li a0,1 *)
    stepiv TF_1001238 TD_1001238 (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* 0x100123c: ecall -- the reissued write *)
    eapply twmt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_100123c eq_refl) |].
    apply twm_tail_write_rec.
    + getr_resolve; exact H17.
    + regupd_resolve; reflexivity.
    + match goal with
      | |- ms_read_bytes _ (reg_get ?R 11) (reg_get ?R 12) = Some _ =>
          replace (reg_get R 11)
            with (Z_to_bv 64 (bv_unsigned p + Z.of_nat k))
            by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word (skipn k rest))
            by (regupd_resolve; reflexivity)
      end.
      rewrite (ms_read_bytes_rdn (run_segments target_segs inp asp amb)) by reflexivity;
      unfold run_segments; apply rdn_lift.
      cbn [ms_mem].
      replace (word_to_nat (len_word (skipn k rest)))
        with (length (skipn k rest))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      pose proof (rdn_skipn target_segs (wbytes zmemT aG (out_buf s))
                    (length rest) p rest k Hread Hk2) as Hsk.
      rewrite word_add_nat_Z in Hsk by lia.
      rewrite length_skipn. exact Hsk.
    + (* [vfs_write]'s [access_ok] on the remaining range *)
      match goal with
      | |- access_okb (reg_get ?R 11) (bv_unsigned (reg_get ?R 12)) = true =>
          replace (reg_get R 11)
            with (Z_to_bv 64 (bv_unsigned p + Z.of_nat k))
            by (regupd_resolve; reflexivity);
          replace (reg_get R 12) with (len_word (skipn k rest))
            by (regupd_resolve; reflexivity)
      end.
      apply Uaccess.access_okb_intro.
      rewrite u_len_word by (rewrite length_skipn; lia).
      rewrite u_Z2bv by lia. rewrite length_skipn. unfold TASK_SIZE. lia.
    + rewrite length_skipn; lia.
    + intros m Hm1 Hm2.
      norm_pc.
      apply (IH (skipn k rest) (Z_to_bv 64 (bv_unsigned p + Z.of_nat k)) m).
      * rewrite length_skipn; lia.
      * exact Hm1.
      * exact Hm2.
      * rewrite length_skipn; lia.
      * rewrite u_Z2bv by lia; lia.
      * rewrite u_Z2bv by lia; rewrite length_skipn; lia.
      * regupd_resolve; exact H2r.
      * regupd_resolve; reflexivity.
      * regupd_resolve; reflexivity.
      * regupd_resolve; reflexivity.
      * regupd_resolve; exact H13.
      * regupd_resolve; exact H17.
      * exact Hmap.
      * pose proof (rdn_skipn target_segs (wbytes zmemT aG (out_buf s))
                      (length rest) p rest k Hread Hk2) as Hsk.
        rewrite word_add_nat_Z in Hsk by lia.
        rewrite length_skipn. exact Hsk.
Qed.

Lemma target_out : forall model regs,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 0x20) ->
  reg_get regs 13 = aG -> reg_get regs 16 = tnN ->
  map_has (vm_maps (m_vmmaps model)) aG (Z_to_bv 64 4096) = true ->
  twm target_segs (mkst regs 0x100121c (wbytes zmemT aG (upperv s)) arom)
      model [out_buf s] (Z_to_bv 64 0).
Proof.
  intros model regs H2r H13 H16 Hmap.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof tnN_le as HnN.
  assert (HuN : bv_unsigned tnN = Z.of_nat n)
    by (unfold tnN; rewrite u_ntw by lia; reflexivity).
  pose proof (u64_range aG) as HaR.
  assert (EMt : wbytes zmemT aG (out_buf s)
                = wbytes (wbytes zmemT aG (upperv s)) (aG + nat_to_word n) [Z_to_bv 8 10]).
  { unfold out_buf. rewrite wbytes_snoc, length_upperv. reflexivity. }
  (* 0x100121c: add a0,a3,a6 -> aG + n *)
  chain_step;
    [ reflexivity
    | eapply step_add_at with (v := aG + nat_to_word n);
      [ exact TF_100121c | reflexivity | exact TD_100121c | reflexivity
      | getr_resolve; rewrite H13, H16; reflexivity ]
    | step_simpl ].
  (* 0x1001220: li a1,10 *)
  stepi_at TF_1001220 TD_1001220 (Z_to_bv 64 10).
  (* 0x1001224: sb a1,0(a0) -> '\n' at aG + n *)
  chain_step;
    [ reflexivity
    | eapply step_sb_at
        with (a := aG + nat_to_word n) (v := Z_to_bv 64 10) (b := Z_to_bv 8 10);
      [ exact TF_1001224 | reflexivity | exact TD_1001224
      | getr_resolve; regupd_resolve; apply v_addi_0
      | getr_resolve; regupd_resolve; reflexivity
      | bveq
      | store_ok_peel; apply tgrant_store_ok;
        rewrite ?word_add_nat, ?u_Z2bv by lia; u_norm; lia ]
    | rewrite <- EMt; step_simpl ].
  (* ---- 0x1001228 .. 0x100123c: FIVE instructions in one block ----
     the byte count, the buffer pointer, the write syscall number and
     the (not taken) zero-length test, stopping at the write [ecall]. *)
  sym_block target_segs 5%nat [false] (@nil expr)
    [((0 : reg), ELit 0); ((16 : reg), EVar 32); ((13 : reg), EVar 33)]
    [tnN; aG] (@nil word) RB HRB.
  { (* [beq a2,x0] at 0x1001234 -> not taken: the buffer is nonempty *)
    apply c_eq_0_false. rewrite u_Z2bv by lia. lia. }
  { (* the [a6] pin *) rewrite getr_nz by reg_neq_tac.
    getr_resolve; regupd_resolve; exact H16. }
  { (* the [a3] pin *) rewrite getr_nz by reg_neq_tac.
    getr_resolve; regupd_resolve; exact H13. }
  (* 0x100123c: ecall -> the write *)
  chain_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_100123c eq_refl) | ].
  eapply twm_write_ret.
  { sym_regs HRB. reflexivity. }
  { sym_regs HRB. reflexivity. }
  { rewrite (ms_read_bytes_rdn (run_segments target_segs inp asp amb)) by reflexivity;
      unfold run_segments; apply rdn_lift.
    cbn [ms_mem ms_regs].
    sym_regs HRB.
    replace (Z_to_bv 64 (bv_unsigned tnN + 1)) with (nat_to_word (S n))
      by (unfold nat_to_word; rewrite HuN; f_equal; lia).
    replace (word_to_nat (nat_to_word (S n))) with (length (out_buf s))
      by (rewrite length_out_buf, word_to_nat_ntw by lia; reflexivity).
    apply rdn_wbytes_hit.
    rewrite length_out_buf. lia. }
  { (* [vfs_write]'s [access_ok] on the whole buffer: a1 = aG and
       a2 = n + 1, read off the block's register file first *)
    assert (Hc11 : reg_get RB 11 = aG)
      by (sym_regs HRB; first [ reflexivity | (apply bv_eq; u_norm; lia) ]).
    assert (Hc12 : reg_get RB 12 = nat_to_word (S n))
      by (sym_regs HRB;
          first [ reflexivity | (apply bv_eq; rewrite ?u_ntw by lia; u_norm; lia) ]).
    rewrite Hc11, Hc12.
    apply Uaccess.access_okb_intro.
    rewrite u_ntw by lia.
    pose proof HaCeil. unfold TASK_SIZE. lia. }
  { rewrite length_out_buf. lia. }
  (* ---- 0x1001240 ..: the put-style retry loop, per delivered length. *)
  intros k Hk1 Hk2.
  norm_pc.
  apply (tgt_put_wall model (length (out_buf s)) (out_buf s) aG k).
  - lia.
  - exact Hk1.
  - exact Hk2.
  - rewrite length_out_buf; lia.
  - exact HaPos.
  - rewrite length_out_buf. pose proof HaCeil. lia.
  - regupd_resolve; sym_regs HRB; rewrite getr_nz by reg_neq_tac;
    regupd_resolve; exact H2r.
  - regupd_resolve; reflexivity.
  - regupd_resolve; sym_regs HRB; sym_close.
  - regupd_resolve; sym_regs HRB.
    match goal with |- ?x = _ => transitivity (Z_to_bv 64 (bv_unsigned tnN + 1)) end;
      [ sym_close
      | apply bv_eq; rewrite u_len_word by (rewrite length_out_buf; lia);
        rewrite length_out_buf, u_Z2bv by lia; lia ].
  - regupd_resolve; sym_regs HRB; sym_close.
  - regupd_resolve; sym_regs HRB; sym_close.
  - exact Hmap.
  - apply rdn_wbytes_hit. rewrite length_out_buf. lia.
Qed.

(* ----------------------------------------------------------------- *)
(* The whole success continuation from the mmap return                *)
(* ----------------------------------------------------------------- *)

Lemma target_succ_twm : forall model regs,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 0x20) ->
  reg_get regs 8 = tP -> reg_get regs 16 = tnN ->
  map_has (vm_maps (m_vmmaps model)) aG (Z_to_bv 64 4096) = true ->
  twm target_segs
      (mkst (regupd regs 10 aG) 0x10011dc (zfill aG (Z_to_bv 64 4096) tfmem) arom)
      model [out_buf s] (Z_to_bv 64 0).
Proof.
  intros model regs H2r H8r H16r Hmap.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof tnN_le as HnN.
  pose proof (u64_range aG) as HaR.
  assert (Hadd0 : forall x : word, x + nat_to_word 0 = x).
  { intro x. rewrite word_add_nat. apply bv_eq.
    rewrite u_Z2bv by (pose proof (u64_range x); lia). lia. }
  (* 0x10011dc: bltz a0 -> fall through *)
  chain_step;
    [ reflexivity
    | eapply step_blt_ft;
      [ exact TF_10011dc | reflexivity | exact TD_10011dc
      | getr_resolve; regupd_resolve; apply c_lts_pos_0; lia ]
    | norm_pc ].
  (* 0x10011e0: mv a3,a0 -> aG *)
  stepiv TF_10011e0 TD_10011e0 aG
    ltac:(getr_resolve; regupd_resolve; apply v_addi_0).
  (* 0x10011e4: mv a1,a6 -> n *)
  stepiv TF_10011e4 TD_10011e4 tnN
    ltac:(getr_resolve; regupd_resolve; rewrite H16r; apply v_addi_0).
  destruct (Nat.eq_dec n 0) as [Hn0 | Hnpos].
  - (* n = 0: skip the copy loop *)
    assert (Hnil : nth 1 av [] = @nil byte) by (apply length_zero_iff_nil; exact Hn0).
    (* 0x10011e8: beq a6,x0 -> taken *)
    chain_step;
      [ reflexivity
      | eapply step_beq_tk;
        [ exact TF_10011e8 | reflexivity | exact TD_10011e8
        | getr_resolve; regupd_resolve; rewrite H16r; unfold tnN;
          apply c_eq_0_of_u; rewrite u_ntw by lia; lia ]
      | norm_pc ].
    assert (Emem0 : wbytes zmemT aG (upperv s) = zfill aG (Z_to_bv 64 4096) tfmem).
    { rewrite Hnil. reflexivity. }
    rewrite <- Emem0.
    apply target_out.
    + regupd_resolve. exact H2r.
    + regupd_resolve. reflexivity.
    + regupd_resolve. exact H16r.
    + exact Hmap.
  - (* n > 0: run the copy loop *)
    (* 0x10011e8: beq a6,x0 -> fall through *)
    chain_step;
      [ reflexivity
      | eapply step_beq_ft;
        [ exact TF_10011e8 | reflexivity | exact TD_10011e8
        | getr_resolve; regupd_resolve; rewrite H16r; unfold tnN;
          apply c_eq_0_false; rewrite u_ntw by lia; lia ]
      | norm_pc ].
    lazymatch goal with
    | |- twm _ (mkst ?R _ _ _) _ _ _ =>
      edestruct (target_copy n 0%nat R) as [regsC [HfrC HmsC]]
    end.
    { regupd_resolve. rewrite H8r, Hadd0. reflexivity. }
    { regupd_resolve. rewrite Hadd0. reflexivity. }
    { regupd_resolve. unfold tnN. f_equal. lia. }
    { lia. }
    { lia. }
    eapply msteps_twm; [exact HmsC |].
    apply target_out.
    + rewrite (HfrC 2) by reg_neq_tac. regupd_resolve. exact H2r.
    + rewrite (HfrC 13) by reg_neq_tac. regupd_resolve. reflexivity.
    + rewrite (HfrC 16) by reg_neq_tac. regupd_resolve. exact H16r.
    + exact Hmap.
Qed.

End TargetSucc.

(* ================================================================= *)
(* The packaged tmw derivation for the target binary                  *)
(* ================================================================= *)

(** The target's whole run, from the launch's state and model ([Run]'s:
    [State.with_vdso] of the draw's vDSO counter over [State.init_model]);
    [Hmb] is [Run.valid_mmap_base]'s floor. *)
Lemma target_tmw : (mmap_base_min <= bv_unsigned amb)%Z ->
  (2 <= length av)%nat -> (n <= 4095)%nat ->
  tmw target_segs
      (init_machine_state (run_segments target_segs inp asp amb) 0x1001158 target_phdrs asp amb arnd inp)
      (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
         (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
      [] (Z_to_bv 64 4) [out_buf s] (Z_to_bv 64 0).
Proof.
  intros Hmb H2 Hn.
  destruct (target_to_mmap H2 Hn)
    as (regsE & HE2 & HE8 & HE16 & HE11 & HE12 & HE13 & HE14 & HE15
        & HE10 & HE17 & Hms).
  eapply msteps_tmw; [exact Hms|].
  apply tmw_mmap_rec.
  - exact HE17.
  - (* len (a1) nonzero *) rewrite HE11. discriminate.
  - exact HE12.
  - exact HE13.
  - rewrite HE14. apply bv_eq. vm_compute. reflexivity.
  - exact HE15.
  - (* a NULL hint is never declined: Linux v6.18.46 mm/mmap.c:754-761
       tries the hint only when it is nonzero, :763-770 search *)
    unfold place_declined_b. rewrite HE10. reflexivity.
  - (* failure family: exit 4, no output *)
    intros e HIn. destruct (mmap_errno_range e HIn) as [He1 He2].
    norm_pc.
    apply target_fail_twm; assumption.
  - (* success family: one write, munmap, exit 0 *)
    intros aa Hg.
    rewrite HE11 in Hg.
    change (bv_unsigned (Z_to_bv 64 4096)) with 4096%Z in Hg.
    rewrite page_round_up_Z_4096 in Hg.
    rewrite HE11, pru_4096.
    destruct (target_grant_unpack inp _ abrk amb asp aa _ Hg)
      as (Hpos & Hal' & Hceil & Hda' & Hdb').
    norm_pc.
    apply (target_succ_twm aa Hpos Hal' Hceil Hda' Hdb' H2 Hn);
      try assumption.
    (* [cbn] alone no longer walks through the model's accessors -- they are
       [simpl never] so a bare [m_vmmaps model] stays put -- so the rewrites
       take it the rest of the way. *)
    unfold mmap_model, map_has. cbn; autorewrite with model; cbn.
    rewrite !bv_eqb_refl. reflexivity.
  - (* at least one admissible grant *)
    rewrite HE11.
    change (bv_unsigned (Z_to_bv 64 4096)) with 4096%Z.
    rewrite page_round_up_Z_4096.
    exact (target_grant_witness inp _ abrk amb asp _ Hsp_lo Hmb).
Qed.

End TargetProof.
