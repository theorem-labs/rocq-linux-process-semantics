(** * arena-tee-ns TARGET binary (Zig): the mirror-image derivation.

    PROOF-SIDE FILE (not part of the trusted specification).

    Machine plan (see the disassembly comments in arena_tee_ns_code.v):

      _start 0x1001158..0x1001164: 2-slot frame, [sd ra,8(sp)] (ra is 0
        at entry), [auipc]/[jalr] into [run] with ra = 0x1001168;
        0x1001168 is [li a7,93] and 0x100116c the exit [ecall].
      run 0x1001170..0x100118c: the six mmap arguments, then a DIRECT
        [ecall] at 0x1001190 — no crt wrapper, no musl.
      0x1001194 [bltz a0] -> 0x1001244 (a0 = 1, [ret]) : mmap failed.
      0x1001198..0x10011ac: a3 = base (the put2 cursor), a1 = 0 (the
        count), a5 = base + 8, a6 = 510, t0 = 4088 = cap, a7 = 63.
      DRAIN LOOP HEAD 0x10011b0: a4 = a1, a0 = a1 >> 3,
        [bltu a6,a0] -> 0x10011d8 once the count reaches 4088 (511 > 510);
        a1 = a5 + a4 (the buffer), a2 = t0 - a4 (= [DrainAlg.dcnt]),
        a0 = 0, [ecall] at 0x10011c8.
        [bltz a0] -> 0x100124c (dead), a1 = a0 + a4, [bnez a0] loops.
        EOF falls through to 0x10011d8 with a4 = the count.
      HEADER 0x10011d8..0x1001210: eight [sb]s of the hex digits of a4
        into the arena, a constant-trip loop over shifts 28, 24, ..., 0.
      PUT2 0x1001214..0x1001238: a2 = a4 + 8, write(2, a3, a2) in a loop
        that a mapped grant makes run exactly once; then a0 = 0 and the
        [ret] into _start's exit tail.

    Unlike the source there is no return path through musl and no frame
    reload: the target performs exactly ONE stack store in its whole
    run, and no load at all.  The loop-head predicate can therefore be
    a single pc (0x10011b0) — the capacity test lives at the head, not
    at the bottom of the body as in the C.

    Conventions: sp-relative values in the canonical
    [Z_to_bv 64 (bv_unsigned asp - k)] form, pc and constants as
    numeral literals, counts as [nat_to_word]; range bookkeeping in [Z]
    over [bv_unsigned]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec AllocSim WallSim MmapSim StepTac StreamExec StreamSim StoreOk.
From LinuxProcessSemantics.Common Require Import Footprint SymExec SymTac SymSide SymBranch.
From LinuxProcessSemantics.Common Require Import ShapeAlg DrainAlg RunSegmentsLift.
From LinuxProcessSemantics.Examples.arena_tee_ns Require Import arena_tee_ns_code arena_tee_ns_defs.
From LinuxProcessSemantics.Examples.arena_tee_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.arena_tee_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them.  [fx0] itself is
    the instance, so every state here is [init_mkst]'s [@mkst fx0]. *)
#[local] Existing Instance fx0.

(* ================================================================= *)
(* Grant facts for the target image (two read-only LOAD segments)     *)
(* ================================================================= *)

Lemma target_reserved_val :
  segments_reserved target_segs
  = [(Z_to_bv 64 0x1000000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x1001000, Z_to_bv 64 0x1000)].
Proof.
  apply (@bool_decide_eq_true_1 (_ = _) _).
  vm_cast_no_check (eq_refl true).
Qed.

(** The run's reservations are the image's: the vDSO pair reserves
    nothing there ([RunSegmentsLift.segments_reserved_vdso]); the image's
    list is concrete, so the split is by computation. *)
Lemma target_reserved_run : forall inp (sp mb : word),
  segments_reserved (run_segments target_segs inp sp mb) = segments_reserved target_segs.
Proof.
  intros inp sp mb.
  replace (segments_reserved (run_segments target_segs inp sp mb))
    with (segments_reserved target_segs
          ++ segments_reserved (vdso_segments (in_kernel inp) sp mb))
    by reflexivity.
  rewrite segments_reserved_vdso, app_nil_r. reflexivity.
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
    ([RunSegmentsLift.grant_witness_init]); the model is [Run]'s:
    [State.with_vdso] of the draw's vDSO counter over [State.init_model]. *)
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

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x1001158%N.
Proof. vm_compute. reflexivity. Qed.

(** Zig's [srli a0,a1,3] — the executor denotes an immediate shift with
    the REGISTER shift primitive, and this is the bridge back to the
    immediate spelling [MmapSim.v_srli_div] is stated against. *)
Lemma v_srl_3 : forall x : word, v_srl x (Z_to_bv 64 3) = v_srli x 3.
Proof. intro x. unfold v_srl, v_srli. f_equal. Qed.

(** Zig's [andi a6,a6,15] — the executor denotes the immediate AND with
    the materialized-literal register [v_and]; bridge back to the
    immediate spelling [dig_val] is stated against. *)
Lemma v_and_15 : forall x : word, v_and x (Z_to_bv 64 15) = v_andi x 15.
Proof. intro x. unfold v_and, v_andi. f_equal. Qed.

(** The byte the digit loop's [sb] stores IS the header digit, on each
    side of the [bltu] split.  Stated in the [Z_to_bv (bv_unsigned _ + c)]
    spelling the symbolic executor's log denotes the ['0'+d] / ['a'+d-10]
    add in. *)
Lemma dig_byte_lo : forall n k', (n <= cap)%nat -> (k' <= 7)%nat ->
  (nib n k' < 10)%nat ->
  word_to_le_bytes 1
    (Z_to_bv 64
       (bv_unsigned
          (v_and (v_srl (nat_to_word n) (Z_to_bv 64 (4 * Z.of_nat k')))
                 (Z_to_bv 64 15)) + 48))
  = [hex_digit (nib n k')].
Proof.
  intros n k' Hn Hk' Hd.
  rewrite v_and_15, (dig_val n k' _ Hn Hk' eq_refl).
  pose proof (nib_lt16 n k').
  change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.of_nat (nib n k'))) + 48))
    with (v_addi (Z_to_bv 64 (Z.of_nat (nib n k'))) 48).
  assert (Hv : v_addi (Z_to_bv 64 (Z.of_nat (nib n k'))) 48
               = Z_to_bv 64 (digZ n k')).
  { unfold v_addi. rewrite u_Z2bv by lia.
    unfold digZ. destruct (Nat.ltb_spec (nib n k') 10); [f_equal; lia | lia]. }
  rewrite Hv, N_to_le_bytes_1_small, digb. reflexivity.
Qed.

Lemma dig_byte_hi : forall n k', (n <= cap)%nat -> (k' <= 7)%nat ->
  (10 <= nib n k')%nat ->
  word_to_le_bytes 1
    (Z_to_bv 64
       (bv_unsigned
          (v_and (v_srl (nat_to_word n) (Z_to_bv 64 (4 * Z.of_nat k')))
                 (Z_to_bv 64 15)) + 87))
  = [hex_digit (nib n k')].
Proof.
  intros n k' Hn Hk' Hd.
  rewrite v_and_15, (dig_val n k' _ Hn Hk' eq_refl).
  pose proof (nib_lt16 n k').
  change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.of_nat (nib n k'))) + 87))
    with (v_addi (Z_to_bv 64 (Z.of_nat (nib n k'))) 87).
  assert (Hv : v_addi (Z_to_bv 64 (Z.of_nat (nib n k'))) 87
               = Z_to_bv 64 (digZ n k')).
  { unfold v_addi. rewrite u_Z2bv by lia.
    unfold digZ. destruct (Nat.ltb_spec (nib n k') 10); [lia | f_equal; lia]. }
  rewrite Hv, N_to_le_bytes_1_small, digb. reflexivity.
Qed.

(* ================================================================= *)
(* Arena addresses (target copies, so the two files stay independent) *)
(* ================================================================= *)

(** [sp] is the run's stack pointer: the grant ends at or below
    [State.alloc_top], a stack's width under it. *)
Definition tgbounds (sp aG : word) : Prop :=
  (0 < bv_unsigned aG)%Z /\
  (bv_unsigned aG mod page_size = 0)%Z /\
  (bv_unsigned aG + 4096 <= bv_unsigned sp - stack_max_size)%Z /\
  ((bv_unsigned aG + 4096 <= 0x1000000)%Z \/ (0x1001000 <= bv_unsigned aG)%Z) /\
  ((bv_unsigned aG + 4096 <= 0x1001000)%Z \/ (0x1002000 <= bv_unsigned aG)%Z).

Definition tbufA (aG : word) (k : nat) : word :=
  Z_to_bv 64 (bv_unsigned aG + 8 + Z.of_nat k).

Lemma tbufA_split : forall sp aG k, tgbounds sp aG -> (k <= cap)%nat ->
  Z_to_bv 64 (bv_unsigned aG + 8) + nat_to_word k = tbufA aG k.
Proof.
  intros sp aG k (_ & _ & Hc & _) Hk. pose proof (u64_range aG).
  pose proof (u64_range sp). unfold stack_max_size in Hc. unfold tbufA.
  rewrite word_add_nat.
  rewrite u_Z2bv by (unfold cap in *; lia).
  f_equal; lia.
Qed.

Lemma tbufA_calc : forall (sp aG : word) k, tgbounds sp aG -> (k <= cap)%nat ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned aG + 8))
              + bv_unsigned (nat_to_word k)) = tbufA aG k.
Proof.
  intros sp aG k (_ & _ & Hc & _) Hk. pose proof (u64_range aG).
  pose proof (u64_range sp). unfold stack_max_size in Hc.
  unfold tbufA.
  rewrite u_Z2bv by (unfold cap in *; lia).
  rewrite u_ntw by (unfold cap in *; lia).
  f_equal; lia.
Qed.

Lemma tdcnt : forall k, (k <= cap)%nat ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 4088) - bv_unsigned (nat_to_word k))
  = Z_to_bv 64 (Z.of_nat (cap - k)).
Proof.
  intros k Hk.
  rewrite u_Z2bv by (unfold cap in *; lia).
  rewrite u_ntw by (unfold cap in *; lia).
  f_equal. unfold cap in *. lia.
Qed.

Lemma tntw_add : forall k (bs : list byte), (k + length bs <= cap)%nat ->
  Z_to_bv 64 (bv_unsigned (len_word bs) + bv_unsigned (nat_to_word k))
  = nat_to_word (k + length bs).
Proof.
  intros k bs H.
  rewrite u_len_word by (unfold cap in *; lia).
  rewrite u_ntw by (unfold cap in *; lia).
  unfold nat_to_word. f_equal. lia.
Qed.

Section TargetProof.

(** No [fs0] abbreviation here, unlike the other sections that need a
    file system: [tgt_LH] and [tgt_TH] below take an arbitrary one as a
    parameter named [fs0], and abbreviating the name would shadow those
    binders. *)
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

Variable abrk : word.
Variable amb : word.
Hypothesis Hvl : valid_launch inp.

(** The fifth conjunct of [Run.valid_entry_va] for the target's run
    ([create_elf_tables] and [setup_arg_pages], fs/binfmt_elf.c and
    fs/exec.c, Linux v6.18.46): it places the stack-store window. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry asp abrk amb arnd) inp.

(** [Run.valid_mmap_base]'s floor: it keeps the vDSO pair above the
    grant's gap. *)
Hypothesis Hmb : (mmap_base_min <= bv_unsigned amb)%Z.

(** The output channel has a reader ([Run.valid_input_channel_reader]). *)
Hypothesis Hrd : in_channel_reader inp = true.

Lemma asp_lo_num : (0x7fff80000000 <= bv_unsigned asp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma asp_hi_num : (bv_unsigned asp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

(** The initial overlay, with the entry point [init_mkst] passes to it. *)
Definition twmem : word -> option byte :=
  wrap_mem inp amb target_phdrs (Z_to_bv 64 (Z.of_N 0x1001158)) asp arnd.
(** The run's rom: the image's segments, then the vDSO pair. *)
Definition trom : word -> option byte := seg_rom (run_segments target_segs inp asp amb).

(** The only store the target performs before the grant: _start's
    [sd ra,8(sp)], with [ra] still 0 at process entry.  It is never
    reloaded — the binary exits through an [ecall], not a frame pop. *)
Definition tfmem : word -> option byte :=
  wbytes twmem (Z_to_bv 64 (bv_unsigned asp - 8))
    (word_to_le_bytes 8 (Z_to_bv 64 0)).

Definition tgmem (aG : word) : word -> option byte :=
  zfill aG (Z_to_bv 64 4096) tfmem.

(** The target has no read-back obligation anywhere, so its memory
    invariant is only "the overlay has grown out of the grant". *)
Definition tmem_ok (aG : word) (mem : word -> option byte) : Prop :=
  mem_grows (tgmem aG) mem.

Lemma tmem_ok_grows_w : forall aG mem, tmem_ok aG mem -> mem_grows twmem mem.
Proof.
  intros aG mem Hg. eapply mem_grows_trans; [| exact Hg].
  unfold tgmem, zfill, tfmem. solve_mem_grows.
Qed.

Local Hint Resolve tmem_ok_grows_w : store_ok_db.

Lemma tgrant_below_stack : forall aG, tgbounds asp aG ->
  (bv_unsigned aG + 4096 <= bv_unsigned asp - 0x800000)%Z.
Proof. intros aG (_ & _ & Hc & _). unfold stack_max_size in Hc. lia. Qed.

Lemma tgrant_store_ok : forall aG mem (a : word) (k : nat),
  tmem_ok aG mem -> tgbounds asp aG ->
  (bv_unsigned aG <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= bv_unsigned aG + 4096)%Z ->
  store_ok target_segs mem a k = true.
Proof.
  intros aG mem a k Hg (_ & _ & Hc & _) Hlo Hhi.
  pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  eapply store_ok_mono; [exact Hg|].
  unfold tgmem, zfill. apply store_ok_zmem;
    [ | exact Hlo | ];
    change (bv_unsigned (Z_to_bv 64 4096)) with 4096%Z; lia.
Qed.

Lemma tmem_ok_grant : forall aG mem (a : word) bs,
  tmem_ok aG mem -> tmem_ok aG (wbytes mem a bs).
Proof. intros aG mem a bs Hg. unfold tmem_ok. solve_mem_grows. Qed.

Lemma tmem_ok_buf : forall aG mem (buf : word) bs,
  tmem_ok aG mem -> tmem_ok aG (write_to_mem mem buf bs).
Proof. intros aG mem buf bs Hg. unfold tmem_ok. solve_mem_grows. Qed.

(* ================================================================= *)
(* The mmap ecall state                                               *)
(* ================================================================= *)

Definition tgt_mmap_ms (regs : bvmap 5 word) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := 0x1001190;
     ms_svc_pending := Some (getr regs 17); ms_resv := None;
     ms_fcsr := fp_csr; ms_mem := tfmem; ms_rom := trom |}.

(** ELEVEN instructions in ONE reflective block: _start's two-slot
    frame and its [auipc]/[jalr] into [run], and [run]'s six mmap
    argument [li]s — the executor stops at the [ecall] at 0x1001190.
    One store, no loads, no branches. *)
Lemma tgt_to_mmap :
  exists regs,
    getr regs 1 = (0x1001168 : word) /\
    getr regs 2 = Z_to_bv 64 (bv_unsigned asp - 0x10) /\
    getr regs 5 = Z_to_bv 64 4096 /\
    getr regs 11 = Z_to_bv 64 4096 /\
    getr regs 12 = Z_to_bv 64 3 /\
    getr regs 13 = Z_to_bv 64 34 /\
    getr regs 14 = Z_to_bv 64 (2^64 - 1) /\
    getr regs 15 = Z_to_bv 64 0 /\
    getr regs 10 = Z_to_bv 64 0 /\
    bv_unsigned (getr regs 17) = 222%Z /\
    msteps target_segs
      (init_machine_state (run_segments target_segs inp asp amb) TargetMemImage_init_pc
         target_phdrs asp amb arnd inp)
      (tgt_mmap_ms regs).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  rewrite target_init_pc_val, init_mkst.
  sym_block_ex target_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 asp)
          (Z_to_bv 64 (Z.of_N 0x1001158))
          (wrap_mem inp amb target_phdrs (Z_to_bv 64 (Z.of_N 0x1001158)) asp arnd)
          (seg_rom (run_segments target_segs inp asp amb)))
    20%nat (@nil bool) (@nil expr)
    [((1 : reg), ELit 0); ((2 : reg), EVar 32)]
    [asp] (@nil word) RA HRA Hms.
  { (* _start's [sd ra,8(sp)] *) solve_store_ok. }
  exists RA.
  split; [sym_regs HRA; sym_close|]. split; [sym_regs HRA; sym_close|].
  split; [sym_regs HRA; sym_close|]. split; [sym_regs HRA; sym_close|].
  split; [sym_regs HRA; sym_close|]. split; [sym_regs HRA; sym_close|].
  split; [sym_regs HRA; sym_close|]. split; [sym_regs HRA; sym_close|].
  split; [sym_regs HRA; sym_close|].
  split; [sym_regs HRA; vm_compute; reflexivity|].
  unfold tgt_mmap_ms.
  eapply msteps_trans;
    [ unfold tfmem, twmem, trom; revert Hms; sym_mem_norm; exact (fun x => x) | ].
  norm_pc; sym_pc_lit.
  eapply mst_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_1001190 eq_refl)
    | apply mst_refl ].
Qed.

(** FOUR instructions in ONE reflective block: the taken [bltz a0], the
    [li a0,1] and [ret] of the failure stub, and _start's [li a7,93]. *)
Lemma tgt_fail_wexit : forall regs e,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  getr regs 1 = (0x1001168 : word) ->
  to_wexit target_segs
    (advance_past_svc (set_gpr0 (tgt_mmap_ms regs) (errno_ret e)))
    [] (Z_to_bv 64 1).
Proof.
  intros regs e He1 He2 Hr1.
  pose proof (errno_ret_range e He1 He2) as [Her1 Her2].
  unfold tgt_mmap_ms. rewrite adv_set. norm_pc.
  sym_block target_segs 4%nat [true] (@nil expr)
    [((1 : reg), ELit 0x1001168); ((10 : reg), EVar 32)]
    [errno_ret e] (@nil word) RA HRA.
  { (* [bltz a0] at 0x1001194 -> taken *)
    apply (c_lts_neg_0 (errno_ret e)); lia. }
  1-2: (getr_resolve; regupd_resolve; rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity | (rewrite Hr1; sym_close) ]).
  eapply tw_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_100116c eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRA. vm_compute. reflexivity.
  - sym_regs HRA. reflexivity.
  - u_norm; lia.
Qed.

(* ================================================================= *)
(* The loop-head and tail-head invariants                             *)
(* ================================================================= *)

(** The drain loop head, 0x10011b0.  Unlike the source the capacity
    test is AT the head, so a full arena is still a loop head and the
    predicate needs no case on the count. *)
Definition tgt_LH (fs0 : Fs.Fs) (acc : list byte) (c : config) : Prop :=
  exists (aG : word) (regs : bvmap 5 word) (mem : word -> option byte),
    tgbounds asp aG /\
    m_halted (cfg_model c) = None /\
    m_vm_lazy (cfg_model c) = [] /\
    m_fs (cfg_model c) = fs0 /\
    fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0)
      = Some (FdChannel (Z_to_bv 64 0)) /\
    fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) (cfg_model c) /\
    msteps target_segs (cfg_ms c) (mkst regs (0x10011b0 : word) mem trom) /\
    getr regs 1 = (0x1001168 : word) /\
    getr regs 5 = Z_to_bv 64 4088 /\
    getr regs 11 = nat_to_word (length acc) /\
    getr regs 13 = aG /\
    getr regs 15 = Z_to_bv 64 (bv_unsigned aG + 8) /\
    getr regs 16 = Z_to_bv 64 510 /\
    getr regs 17 = Z_to_bv 64 63 /\
    (length acc <= cap)%nat /\
    tmem_ok aG mem /\
    rdn target_segs mem (Z_to_bv 64 (bv_unsigned aG + 8)) (length acc)
      = Some acc.

(** The header block, 0x10011d8: [a3] is the arena base and [a4] the
    drained count. *)
Definition tgt_TH (fs0 : Fs.Fs) (acc : list byte) (c : config) : Prop :=
  exists (aG : word) (regs : bvmap 5 word) (mem : word -> option byte),
    tgbounds asp aG /\
    m_halted (cfg_model c) = None /\
    m_vm_lazy (cfg_model c) = [] /\
    m_fs (cfg_model c) = fs0 /\
    fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) (cfg_model c) /\
    msteps target_segs (cfg_ms c) (mkst regs (0x10011d8 : word) mem trom) /\
    getr regs 1 = (0x1001168 : word) /\
    getr regs 13 = aG /\
    getr regs 14 = nat_to_word (length acc) /\
    (length acc <= cap)%nat /\
    tmem_ok aG mem /\
    rdn target_segs mem (Z_to_bv 64 (bv_unsigned aG + 8)) (length acc)
      = Some acc.

Lemma c_eq_sub_self : forall x : word, bv_eqb (v_sub x x) (Z_to_bv 64 0) = true.
Proof.
  intro x. rewrite bv_eqb_Z. apply Z.eqb_eq.
  unfold v_sub. rewrite Z.sub_diag. reflexivity.
Qed.

Lemma word_to_nat_ntw : forall n : nat, (Z.of_nat n < 2^64)%Z ->
  word_to_nat (nat_to_word n) = n.
Proof.
  intros n Hn. unfold word_to_nat. rewrite u_ntw by lia. lia.
Qed.

(** One trip of the eight-iteration digit loop, 0x10011ec..0x1001210:
    [srl a6,a4,a0], [andi a6,a6,15], the DATA-DEPENDENT [bltu a6,a2]
    ('0'+d against 'a'+d-10), the [sb] into the arena, the two index
    [addi]s, and the backward [bne a0,a1] — taken on the first seven
    trips, untaken on the eighth, which falls through to the put2
    block at 0x1001214.  The exit shift [a0] is stated through
    [Z_to_bv]'s wrap so one statement covers the last trip too, and
    the useful [4 * (7 - S k)] form is guarded by [S k < 8]. *)
Lemma tgt_dig_iter : forall (aG : word) (R : bvmap 5 word)
                            (mem : word -> option byte) (n k : nat),
  tgbounds asp aG -> (n <= cap)%nat -> (k < 8)%nat -> tmem_ok aG mem ->
  getr R 1 = (0x1001168 : word) ->
  getr R 10 = Z_to_bv 64 (4 * Z.of_nat (7 - k)) ->
  getr R 11 = Z_to_bv 64 (2^64 - 4) ->
  getr R 12 = Z_to_bv 64 10 ->
  getr R 13 = aG ->
  getr R 14 = nat_to_word n ->
  getr R 15 = aG + nat_to_word k ->
  exists R',
    getr R' 1 = (0x1001168 : word) /\
    ((S k < 8)%nat -> getr R' 10 = Z_to_bv 64 (4 * Z.of_nat (7 - S k))) /\
    getr R' 11 = Z_to_bv 64 (2^64 - 4) /\
    getr R' 12 = Z_to_bv 64 10 /\
    getr R' 13 = aG /\
    getr R' 14 = nat_to_word n /\
    getr R' 15 = aG + nat_to_word (S k) /\
    msteps target_segs (mkst R (Z_to_bv 64 0x10011ec) mem trom)
      (mkst R' (Z_to_bv 64 (if (S k <? 8)%nat then 0x10011ec%Z else 0x1001214%Z))
            (wbytes mem (aG + nat_to_word k) [hex_digit (nib n (7 - k))])
            trom).
Proof.
  intros aG R mem n k Hb Hn Hk Hmok L1 L10 L11 L12 L13 L14 L15.
  pose proof Hb as Hb2. destruct Hb2 as (Hpos & Hal & Hceil & _).
  pose proof asp_hi_num. unfold stack_max_size in Hceil.
  pose proof (u64_range aG) as HaR.
  assert (Hso : store_ok target_segs mem (aG + nat_to_word k) 1%nat = true).
  { eapply tgrant_store_ok; [exact Hmok | exact Hb | |];
    rewrite word_add_nat, u_Z2bv by lia; lia. }
  pose proof (u64_range (aG + nat_to_word k)) as Har.
  destruct (Nat.ltb_spec (S k) 8) as [HSk|HSk].
  - destruct (Nat.ltb_spec (nib n (7 - k)) 10) as [Hd|Hd].
    + (* '0' + d, [bne] taken *)
      sym_block_ex target_segs (mkst R (Z_to_bv 64 0x10011ec) mem trom)
        8%nat [true; true] (@nil expr)
        [((1 : reg), ELit 0x1001168); ((10 : reg), EVar 32);
         ((11 : reg), EVar 33); ((12 : reg), ELit 10); ((13 : reg), EVar 34);
         ((14 : reg), EVar 35); ((15 : reg), EVar 36)]
        [Z_to_bv 64 (4 * Z.of_nat (7 - k)); Z_to_bv 64 (2^64 - 4); aG;
         nat_to_word n; aG + nat_to_word k]
        (@nil word) R' HR' Hms.
      { (* [bne a0,a1] taken: the shift has not reached -4 *)
        rewrite negb_true_iff, bv_eqb_Z. apply Z.eqb_neq.
        rewrite !u_Z2bv by lia. lia. }
      { (* the [sb] store, into the grant *)
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hso. }
      { (* [bltu a6,a2] taken: nibble < 10 *)
        rewrite v_and_15, (dig_val n (7 - k) _ Hn ltac:(lia) eq_refl).
        rewrite bv_ltu_Z. apply Z.ltb_lt.
        rewrite !u_Z2bv by (pose proof (nib_lt16 n (7 - k)); lia). lia. }
      1-7: (rewrite <- ?getr_nz by reg_neq_tac;
            first [ reflexivity | (rewrite L1; bveq) | exact L10 | exact L11
                  | exact L12 | exact L13 | exact L14 | exact L15 ]).
      exists R'.
      split. { sym_regs HR'; first [reflexivity | bveq]. }
      split. { intros _. sym_regs HR'. f_equal. lia. }
      split. { sym_regs HR'; first [reflexivity | bveq]. }
      split. { sym_regs HR'; first [reflexivity | bveq]. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; apply word_add_nat_1. }
      match type of Hms with
      | msteps _ _ (mkst _ _ ?M _) =>
          replace (wbytes mem (aG + nat_to_word k) [hex_digit (nib n (7 - k))])
            with M; [ exact Hms | ]
      end.
      rewrite adenot_var.
      cbn [edenot Eplus Nat.ltb Nat.leb Nat.sub nth app].
      rewrite ?edenot_lit.
      rewrite ?alu_add, ?alu_and, ?alu_srl, ?v_add_lit.
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      f_equal.
      apply (dig_byte_lo n (7 - k) Hn ltac:(lia) Hd).
    + (* 'a' + d - 10, [bne] taken *)
      sym_block_ex target_segs (mkst R (Z_to_bv 64 0x10011ec) mem trom)
        9%nat [false; true] (@nil expr)
        [((1 : reg), ELit 0x1001168); ((10 : reg), EVar 32);
         ((11 : reg), EVar 33); ((12 : reg), ELit 10); ((13 : reg), EVar 34);
         ((14 : reg), EVar 35); ((15 : reg), EVar 36)]
        [Z_to_bv 64 (4 * Z.of_nat (7 - k)); Z_to_bv 64 (2^64 - 4); aG;
         nat_to_word n; aG + nat_to_word k]
        (@nil word) R' HR' Hms.
      { (* [bne a0,a1] taken: the shift has not reached -4 *)
        rewrite negb_true_iff, bv_eqb_Z. apply Z.eqb_neq.
        rewrite !u_Z2bv by lia. lia. }
      { (* the [sb] store, into the grant *)
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hso. }
      { (* [bltu a6,a2] untaken: nibble >= 10 *)
        rewrite v_and_15, (dig_val n (7 - k) _ Hn ltac:(lia) eq_refl).
        rewrite bv_ltu_Z. apply Z.ltb_ge.
        rewrite !u_Z2bv by (pose proof (nib_lt16 n (7 - k)); lia). lia. }
      1-7: (rewrite <- ?getr_nz by reg_neq_tac;
            first [ reflexivity | (rewrite L1; bveq) | exact L10 | exact L11
                  | exact L12 | exact L13 | exact L14 | exact L15 ]).
      exists R'.
      split. { sym_regs HR'; first [reflexivity | bveq]. }
      split. { intros _. sym_regs HR'. f_equal. lia. }
      split. { sym_regs HR'; first [reflexivity | bveq]. }
      split. { sym_regs HR'; first [reflexivity | bveq]. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; apply word_add_nat_1. }
      match type of Hms with
      | msteps _ _ (mkst _ _ ?M _) =>
          replace (wbytes mem (aG + nat_to_word k) [hex_digit (nib n (7 - k))])
            with M; [ exact Hms | ]
      end.
      rewrite adenot_var.
      cbn [edenot Eplus Nat.ltb Nat.leb Nat.sub nth app].
      rewrite ?edenot_lit.
      rewrite ?alu_add, ?alu_and, ?alu_srl, ?v_add_lit.
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      f_equal.
      apply (dig_byte_hi n (7 - k) Hn ltac:(lia) Hd).
  - (* the eighth trip: the untaken [bne] is CLOSED and auto-discharged;
       control falls through to the put2 block at 0x1001214 *)
    assert (Hk7 : k = 7%nat) by lia. subst k.
    destruct (Nat.ltb_spec (nib n 0) 10) as [Hd|Hd].
    + (* '0' + d *)
      sym_block_ex target_segs (mkst R (Z_to_bv 64 0x10011ec) mem trom)
        8%nat [true; false] (@nil expr)
        [((1 : reg), ELit 0x1001168); ((10 : reg), EVar 32);
         ((11 : reg), EVar 33); ((12 : reg), ELit 10); ((13 : reg), EVar 34);
         ((14 : reg), EVar 35); ((15 : reg), EVar 36)]
        [Z_to_bv 64 (4 * Z.of_nat (7 - 7)); Z_to_bv 64 (2^64 - 4); aG;
         nat_to_word n; aG + nat_to_word 7]
        (@nil word) R' HR' Hms.
      { (* the [sb] store, into the grant *)
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hso. }
      { rewrite v_and_15, (dig_val n 0 _ Hn ltac:(lia) eq_refl).
        rewrite bv_ltu_Z. apply Z.ltb_lt.
        rewrite !u_Z2bv by (pose proof (nib_lt16 n 0); lia). lia. }
      1-7: (rewrite <- ?getr_nz by reg_neq_tac;
            first [ reflexivity | (rewrite L1; bveq) | exact L10 | exact L11
                  | exact L12 | exact L13 | exact L14 | exact L15 ]).
      exists R'.
      split. { sym_regs HR'; first [reflexivity | bveq]. }
      split. { intro Hc. exfalso. lia. }
      split. { sym_regs HR'; first [reflexivity | bveq]. }
      split. { sym_regs HR'; first [reflexivity | bveq]. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; apply word_add_nat_1. }
      match type of Hms with
      | msteps _ _ (mkst _ _ ?M _) =>
          replace (wbytes mem (aG + nat_to_word 7) [hex_digit (nib n (7 - 7))])
            with M; [ exact Hms | ]
      end.
      rewrite adenot_var.
      cbn [edenot Eplus Nat.ltb Nat.leb Nat.sub nth app].
      rewrite ?edenot_lit.
      rewrite ?alu_add, ?alu_and, ?alu_srl, ?v_add_lit.
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      f_equal.
      apply (dig_byte_lo n (7 - 7) Hn ltac:(lia) Hd).
    + (* 'a' + d - 10 *)
      sym_block_ex target_segs (mkst R (Z_to_bv 64 0x10011ec) mem trom)
        9%nat [false; false] (@nil expr)
        [((1 : reg), ELit 0x1001168); ((10 : reg), EVar 32);
         ((11 : reg), EVar 33); ((12 : reg), ELit 10); ((13 : reg), EVar 34);
         ((14 : reg), EVar 35); ((15 : reg), EVar 36)]
        [Z_to_bv 64 (4 * Z.of_nat (7 - 7)); Z_to_bv 64 (2^64 - 4); aG;
         nat_to_word n; aG + nat_to_word 7]
        (@nil word) R' HR' Hms.
      { (* the [sb] store, into the grant *)
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hso. }
      { rewrite v_and_15, (dig_val n 0 _ Hn ltac:(lia) eq_refl).
        rewrite bv_ltu_Z. apply Z.ltb_ge.
        rewrite !u_Z2bv by (pose proof (nib_lt16 n 0); lia). lia. }
      1-7: (rewrite <- ?getr_nz by reg_neq_tac;
            first [ reflexivity | (rewrite L1; bveq) | exact L10 | exact L11
                  | exact L12 | exact L13 | exact L14 | exact L15 ]).
      exists R'.
      split. { sym_regs HR'; first [reflexivity | bveq]. }
      split. { intro Hc. exfalso. lia. }
      split. { sym_regs HR'; first [reflexivity | bveq]. }
      split. { sym_regs HR'; first [reflexivity | bveq]. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; apply word_add_nat_1. }
      match type of Hms with
      | msteps _ _ (mkst _ _ ?M _) =>
          replace (wbytes mem (aG + nat_to_word 7) [hex_digit (nib n (7 - 7))])
            with M; [ exact Hms | ]
      end.
      rewrite adenot_var.
      cbn [edenot Eplus Nat.ltb Nat.leb Nat.sub nth app].
      rewrite ?edenot_lit.
      rewrite ?alu_add, ?alu_and, ?alu_srl, ?v_add_lit.
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      f_equal.
      apply (dig_byte_hi n (7 - 7) Hn ltac:(lia) Hd).
Qed.

(** The header block, the single-trip put2 loop, and the exit — carried
    into [realizes] through the fd-2 write machinery:
    [CatSim.to_wexit_ch] at fd 2, [CatSim.msteps_to_wexit_ch] for the
    silent runs, and [ShapeAlg.cat_realizes_ch] to conclude.  The buffer
    read-back is [SeqExec.rdn_wbytes_hit] (the header just stored)
    spliced with [CatExec.rdn_wbytes_out] (the drained prefix) by
    [SeqExec.rdn_app]. *)
(** The whole header block: the four setup instructions, the untaken
    first-entry [beq], and the eight digit-loop trips, with the eight
    byte stores folded into [wbytes mem aG (hdr8 n)]. *)
Lemma tgt_hdr_run : forall (aG : word) (regs : bvmap 5 word) mem (n : nat),
  tgbounds asp aG -> (n <= cap)%nat -> tmem_ok aG mem ->
  getr regs 1 = (0x1001168 : word) ->
  getr regs 13 = aG ->
  getr regs 14 = nat_to_word n ->
  exists R,
    getr R 1 = (0x1001168 : word) /\
    getr R 13 = aG /\
    getr R 14 = nat_to_word n /\
    msteps target_segs (mkst regs (Z_to_bv 64 0x10011d8) mem trom)
      (mkst R (Z_to_bv 64 0x1001214) (wbytes mem aG (hdr8 n)) trom).
Proof.
  intros aG regs mem n Hb Hn Hmok H1 H13 H14.
  pose proof Hb as Hb2. destruct Hb2 as (Hpos & Hal & Hceil & _).
  pose proof asp_hi_num. unfold stack_max_size in Hceil.
  pose proof (u64_range aG) as HaR.
  (* the setup block: a0=28, a1=-4, a2=10, a5=a3, [beq] untaken *)
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 0x10011d8) mem trom)
    5%nat [false] (@nil expr)
    [((1 : reg), ELit 0x1001168); ((13 : reg), EVar 32); ((14 : reg), EVar 33)]
    [aG; nat_to_word n] (@nil word) R0 HR0 Hms0.
  1-3: (rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity | (rewrite H1; bveq) | exact H13 | exact H14 ]).
  assert (L1 : getr R0 1 = (0x1001168 : word)) by (sym_regs HR0; first [reflexivity|bveq]).
  assert (L10 : getr R0 10 = Z_to_bv 64 (4 * Z.of_nat (7 - 0)))
    by (sym_regs HR0; f_equal; lia).
  assert (L11 : getr R0 11 = Z_to_bv 64 (2^64 - 4)) by (sym_regs HR0; bveq).
  assert (L12 : getr R0 12 = Z_to_bv 64 10) by (sym_regs HR0; first [reflexivity|bveq]).
  assert (L13 : getr R0 13 = aG) by (sym_regs HR0; reflexivity).
  assert (L14 : getr R0 14 = nat_to_word n) by (sym_regs HR0; reflexivity).
  assert (L15 : getr R0 15 = aG + nat_to_word 0)
    by (sym_regs HR0; rewrite word_add_nat_0; reflexivity).
  clear HR0.
  (* the eight digit trips *)
  destruct (tgt_dig_iter aG R0 mem n 0 Hb Hn ltac:(lia) Hmok L1 L10 L11 L12 L13 L14 L15)
    as (Ra & A1 & A10 & A11 & A12 & A13 & A14 & A15 & HmsA).
  set (m1 := wbytes mem (aG + nat_to_word 0) [hex_digit (nib n (7 - 0))]) in *.
  assert (Hmok1 : tmem_ok aG m1) by (apply tmem_ok_grant; exact Hmok).
  destruct (tgt_dig_iter aG Ra m1 n 1 Hb Hn ltac:(lia) Hmok1 A1 (A10 ltac:(lia)) A11 A12 A13 A14 A15)
    as (Rb & B1 & B10 & B11 & B12 & B13 & B14 & B15 & HmsB).
  set (m2 := wbytes m1 (aG + nat_to_word 1) [hex_digit (nib n (7 - 1))]) in *.
  assert (Hmok2 : tmem_ok aG m2) by (apply tmem_ok_grant; exact Hmok1).
  destruct (tgt_dig_iter aG Rb m2 n 2 Hb Hn ltac:(lia) Hmok2 B1 (B10 ltac:(lia)) B11 B12 B13 B14 B15)
    as (Rc & C1 & C10 & C11 & C12 & C13 & C14 & C15 & HmsC).
  set (m3 := wbytes m2 (aG + nat_to_word 2) [hex_digit (nib n (7 - 2))]) in *.
  assert (Hmok3 : tmem_ok aG m3) by (apply tmem_ok_grant; exact Hmok2).
  destruct (tgt_dig_iter aG Rc m3 n 3 Hb Hn ltac:(lia) Hmok3 C1 (C10 ltac:(lia)) C11 C12 C13 C14 C15)
    as (Rd & D1 & D10 & D11 & D12 & D13 & D14 & D15 & HmsD).
  set (m4 := wbytes m3 (aG + nat_to_word 3) [hex_digit (nib n (7 - 3))]) in *.
  assert (Hmok4 : tmem_ok aG m4) by (apply tmem_ok_grant; exact Hmok3).
  destruct (tgt_dig_iter aG Rd m4 n 4 Hb Hn ltac:(lia) Hmok4 D1 (D10 ltac:(lia)) D11 D12 D13 D14 D15)
    as (Re & E1 & E10 & E11 & E12 & E13 & E14 & E15 & HmsE).
  set (m5 := wbytes m4 (aG + nat_to_word 4) [hex_digit (nib n (7 - 4))]) in *.
  assert (Hmok5 : tmem_ok aG m5) by (apply tmem_ok_grant; exact Hmok4).
  destruct (tgt_dig_iter aG Re m5 n 5 Hb Hn ltac:(lia) Hmok5 E1 (E10 ltac:(lia)) E11 E12 E13 E14 E15)
    as (Rf & F1 & F10 & F11 & F12 & F13 & F14 & F15 & HmsF).
  set (m6 := wbytes m5 (aG + nat_to_word 5) [hex_digit (nib n (7 - 5))]) in *.
  assert (Hmok6 : tmem_ok aG m6) by (apply tmem_ok_grant; exact Hmok5).
  destruct (tgt_dig_iter aG Rf m6 n 6 Hb Hn ltac:(lia) Hmok6 F1 (F10 ltac:(lia)) F11 F12 F13 F14 F15)
    as (Rg & G1 & G10 & G11 & G12 & G13 & G14 & G15 & HmsG).
  set (m7 := wbytes m6 (aG + nat_to_word 6) [hex_digit (nib n (7 - 6))]) in *.
  assert (Hmok7 : tmem_ok aG m7) by (apply tmem_ok_grant; exact Hmok6).
  destruct (tgt_dig_iter aG Rg m7 n 7 Hb Hn ltac:(lia) Hmok7 G1 (G10 ltac:(lia)) G11 G12 G13 G14 G15)
    as (Rh & I1 & _ & _ & _ & I13 & I14 & _ & HmsH).
  set (m8 := wbytes m7 (aG + nat_to_word 7) [hex_digit (nib n (7 - 7))]) in *.
  assert (Hfold : m8 = wbytes mem aG (hdr8 n)).
  { unfold m8, m7, m6, m5, m4, m3, m2, m1, hdr8.
    change [hex_digit (nib n 7); hex_digit (nib n 6); hex_digit (nib n 5);
            hex_digit (nib n 4); hex_digit (nib n 3); hex_digit (nib n 2);
            hex_digit (nib n 1); hex_digit (nib n 0)]
      with ((((((((@nil byte
             ++ [hex_digit (nib n 7)]) ++ [hex_digit (nib n 6)])
             ++ [hex_digit (nib n 5)]) ++ [hex_digit (nib n 4)])
             ++ [hex_digit (nib n 3)]) ++ [hex_digit (nib n 2)])
             ++ [hex_digit (nib n 1)]) ++ [hex_digit (nib n 0)]).
    rewrite !wbytes_snoc.
    cbn [length app].
    change (wbytes mem aG []) with mem.
    reflexivity. }
  exists Rh.
  split; [exact I1|]. split; [exact I13|]. split; [exact I14|].
  rewrite <- Hfold.
  eapply msteps_trans; [exact Hms0|].
  eapply msteps_trans; [exact HmsA|].
  eapply msteps_trans; [exact HmsB|].
  eapply msteps_trans; [exact HmsC|].
  eapply msteps_trans; [exact HmsD|].
  eapply msteps_trans; [exact HmsE|].
  eapply msteps_trans; [exact HmsF|].
  eapply msteps_trans; [exact HmsG|].
  exact HmsH.
Qed.

(** The put2 emit loop, as a write-all node ([WallSim.to_wall_tail]).

    Entry is 0x100122c, the instruction the write [ecall] returns to,
    with [a0] holding the DELIVERED length — which the environment
    picks, so the loop has to be proven for every nonempty prefix.  The
    [blez a0] error arm (exit 3) is dead for a nonempty delivery and
    resolves uniformly; then [a3 += a0], [a2 -= a0], and the [bnez a2]
    either falls through to the exit line (everything delivered) or
    reissues the write at the bumped pointer on [skipn n rest].
    Induction on [fuel >= length rest]: the remainder shrinks strictly
    because every delivery is nonempty, which is why the whole buffer
    is delivered and the trace contribution is the full [rest]. *)
Lemma tgt_put_wall : forall fuel (rest : list byte) (p : word) n regs mem,
  (length rest <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length rest)%nat ->
  (Z.of_nat (length rest) <= 4096)%Z ->
  (0 < bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) <= bv_unsigned asp)%Z ->
  getr regs 1 = (0x1001168 : word) ->
  getr regs 10 = len_word (firstn n rest) ->
  getr regs 12 = len_word rest ->
  getr regs 13 = p ->
  getr regs 17 = Z_to_bv 64 64 ->
  rdn target_segs mem p (length rest) = Some rest ->
  to_wall_tail target_segs (Z_to_bv 64 2)
    (mkst regs (Z_to_bv 64 0x100122c) mem trom)
    (skipn n rest)
    (fun ms => to_wexit target_segs ms [] (Z_to_bv 64 0)).
Proof.
  induction fuel as [|fuel IH];
    intros rest p n regs mem Hfuel Hn1 Hn2 Hlen Hplo Hphi
           H1 H10 H12 H13 H17 Hread.
  { lia. }
  pose proof asp_hi_num as Hahi.
  destruct (Nat.eq_dec n (length rest)) as [Hfull | Hne].
  - (* full delivery: the [bnez a2] falls through to the exit line *)
    subst n. rewrite skipn_all. rewrite firstn_all in H10.
    apply twt_done. cbv beta.
    sym_block_ex target_segs (mkst regs (Z_to_bv 64 0x100122c) mem trom)
      7%nat [false; false] (@nil expr)
      [((1 : reg), ELit 0x1001168); ((10 : reg), EVar 32);
       ((12 : reg), EVar 32)]
      [len_word rest] (@nil word) R3 HR3 Hms3.
    1-2: first
      [ (* [bnez a2] untaken: the delivery was the whole remainder *)
        (apply negb_false_iff; exact (c_eq_sub_self _))
      | (* [blez a0] untaken: the delivery is nonempty *)
        (apply negb_false_iff;
         rewrite bv_lts_small
           by (rewrite ?u_len_word, ?u_Z2bv by lia; lia);
         apply Z.ltb_lt;
         rewrite u_len_word by lia; rewrite u_Z2bv by lia; lia) ].
    1-3: (rewrite <- ?getr_nz by reg_neq_tac;
          first [ reflexivity | (rewrite H1; bveq) | exact H10 | exact H12 ]).
    eapply msteps_to_wexit; [exact Hms3|].
    assert (M17 : getr R3 17 = Z_to_bv 64 93)
      by (sym_regs HR3; first [reflexivity|bveq]).
    assert (M10 : getr R3 10 = Z_to_bv 64 0)
      by (sym_regs HR3; first [reflexivity|bveq]).
    clear HR3.
    replace (Z_to_bv 64 16781676) with (0x100116c : word) by bveq.
    eapply tw_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_100116c eq_refl) | ].
    match goal with
    | |- to_wexit _ ?ms _ _ =>
        replace (Z_to_bv 64 0) with (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
          by (unfold ms_gpr; cbn [ms_regs]; rewrite arg_reg_0;
              rewrite <- getr_nz by reg_neq_tac; rewrite M10; bveq)
    end.
    eapply tw_exit.
    + cbn [ms_svc_pending]. reflexivity.
    + left. rewrite M17. vm_compute. reflexivity.
  - (* short delivery: the [bnez a2] reissues the write *)
    assert (Hlt : (n < length rest)%nat) by lia.
    sym_block_ex target_segs (mkst regs (Z_to_bv 64 0x100122c) mem trom)
      6%nat [false; true] (@nil expr)
      [((1 : reg), ELit 0x1001168); ((17 : reg), ELit 64);
       ((13 : reg), EVar 32); ((12 : reg), EVar 33); ((10 : reg), EVar 34)]
      [p; len_word rest; len_word (firstn n rest)] (@nil word) R HR Hms.
    1-2: first
      [ (* [bnez a2] taken: the remainder is nonempty *)
        (apply negb_true_iff;
         rewrite v_sub_len_firstn by lia;
         apply c_eq_0_false;
         rewrite u_len_word by (rewrite length_skipn; lia);
         rewrite length_skipn; lia)
      | (* [blez a0] untaken: the delivery is nonempty *)
        (apply negb_false_iff;
         rewrite bv_lts_small
           by (rewrite ?u_len_word_firstn, ?u_Z2bv by lia; lia);
         apply Z.ltb_lt;
         rewrite u_len_word_firstn by lia; rewrite u_Z2bv by lia; lia) ].
    1-5: (rewrite <- ?getr_nz by reg_neq_tac;
          first [ reflexivity | (rewrite H1; bveq) | (rewrite H17; bveq)
                | exact H13 | exact H12 | exact H10 ]).
    assert (N1 : getr R 1 = (0x1001168 : word))
      by (sym_regs HR; first [reflexivity|bveq]).
    assert (N17 : getr R 17 = Z_to_bv 64 64)
      by (sym_regs HR; first [reflexivity|bveq]).
    assert (N10 : getr R 10 = Z_to_bv 64 2)
      by (sym_regs HR; first [reflexivity|bveq]).
    assert (N11 : getr R 11 = p + nat_to_word n)
      by (sym_regs HR; apply v_add_len_firstn; lia).
    assert (N12 : getr R 12 = len_word (skipn n rest))
      by (sym_regs HR; apply v_sub_len_firstn; lia).
    assert (N13 : getr R 13 = p + nat_to_word n)
      by (sym_regs HR; apply v_add_len_firstn; lia).
    clear HR.
    (* the remainder, read back at the bumped pointer *)
    assert (Hsk : rdn target_segs mem (p + nat_to_word n)
                    (length (skipn n rest)) = Some (skipn n rest)).
    { rewrite length_skipn.
      exact (SeqExec.rdn_skipn target_segs mem (length rest) p rest n
               Hread Hn2). }
    assert (HuP : bv_unsigned (p + nat_to_word n)
                  = (bv_unsigned p + Z.of_nat n)%Z).
    { rewrite word_add_nat_Z by lia. apply u_Z2bv; lia. }
    eapply msteps_to_wall_tail; [exact Hms|].
    replace (Z_to_bv 64 16781864) with (0x1001228 : word) by bveq.
    eapply twt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_1001228 eq_refl) | ].
    apply twt_more; [rewrite length_skipn; lia|].
    apply (twl_write_rec target_segs (Z_to_bv 64 2)).
    + rewrite N17. vm_compute. reflexivity.
    + rewrite <- getr_nz by reg_neq_tac; exact N10.
    + rewrite <- ?getr_nz by reg_neq_tac; rewrite N11, N12.
      rewrite (ms_read_bytes_rdn (run_segments target_segs inp asp amb)) by reflexivity;
        unfold run_segments; apply rdn_lift.
      cbn [ms_mem].
      replace (word_to_nat (len_word (skipn n rest)))
        with (length (skipn n rest))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      exact Hsk.
    + (* [vfs_write]'s [access_ok] on the remaining range *)
      rewrite <- ?getr_nz by reg_neq_tac; rewrite N11, N12.
      apply Uaccess.access_okb_intro.
      rewrite u_len_word by (rewrite length_skipn; lia).
      rewrite HuP, length_skipn. unfold TASK_SIZE. lia.
    + rewrite length_skipn; lia.
    + intros m Hm1 Hm2.
      replace (v_addi (0x1001228 : word) 4) with (Z_to_bv 64 0x100122c) by bveq.
      apply (IH (skipn n rest) (p + nat_to_word n) m).
      * rewrite length_skipn; lia.
      * exact Hm1.
      * exact Hm2.
      * rewrite length_skipn; lia.
      * rewrite HuP; lia.
      * rewrite HuP, length_skipn; lia.
      * getr_resolve; exact N1.
      * getr_resolve; reflexivity.
      * getr_resolve; exact N12.
      * getr_resolve; exact N13.
      * getr_resolve; exact N17.
      * exact Hsk.
Qed.

Lemma tgt_tail : forall fs0 acc c,
  tgt_TH fs0 acc c ->
  realizes (run_segments target_segs inp asp amb) c (arena_tail fs0 acc).
Proof.
  intros fs0 acc c HTH.
  destruct HTH as (aG & regs & mem & Hb & Hh & Hlazy & Hfs & Hfd2 & Hms0 &
                   K1 & K13 & K14 & Hle & Hmok & Hrdn).
  destruct c as [ms0 model]. cbn [cfg_ms cfg_model] in *.
  pose proof Hb as Hb2. destruct Hb2 as (Hpos & Hal & Hceil & _).
  pose proof asp_hi_num. unfold stack_max_size in Hceil.
  pose proof (u64_range aG) as HaR.
  unfold arena_tail. rewrite <- Hfs.
  apply (wall_realizes_ch (run_segments target_segs inp asp amb) (Z_to_bv 64 2) ch2 ms0 model
           [arena_out acc] (Z_to_bv 64 0) Hh Hlazy Hfd2 fd32_2);
    [| exact (arena_out_modeled acc Hle)].
  split; [rewrite arena_out_length; lia|].
  (* the write chain is built over the image's segments and lifted whole
     ([RunSegmentsLift.to_wall_lift_mut]; neither vDSO segment executes) *)
  unfold run_segments.
  apply (proj2 (to_wall_lift_mut target_segs _ (Z_to_bv 64 2) (vdso_segments_no_exec _ _ _))
           ms0 (arena_out acc) (fun ms => to_wexit target_segs ms [] (Z_to_bv 64 0)));
    [| intros m Hm; exact (to_wexit_app target_segs _ m [] _ (vdso_segments_no_exec _ _ _) Hm)].
  replace (0x10011d8 : word) with (Z_to_bv 64 0x10011d8) in Hms0 by bveq.
  eapply msteps_to_wall_tail; [exact Hms0|].
  destruct (tgt_hdr_run aG regs mem (length acc) Hb Hle Hmok K1 K13 K14)
    as (R & L1 & L13 & L14 & HmsH).
  eapply msteps_to_wall_tail; [exact HmsH|].
  set (mem8 := wbytes mem aG (hdr8 (length acc))) in *.
  (* put2 setup: a2 = a4 + 8, a7 = 64, the untaken [beq a2,zero],
     a0 = 2, a1 = a3 *)
  sym_block_ex target_segs (mkst R (Z_to_bv 64 0x1001214) mem8 trom)
    5%nat [false] (@nil expr)
    [((1 : reg), ELit 0x1001168); ((13 : reg), EVar 32); ((14 : reg), EVar 33)]
    [aG; nat_to_word (length acc)] (@nil word) R2 HR2 Hms2.
  { (* [beq a2,zero] not taken: the count 8+|acc| is nonzero *)
    rewrite bv_eqb_Z. apply Z.eqb_neq.
    rewrite u_ntw by (unfold cap in *; lia).
    rewrite !u_Z2bv by (unfold cap in *; lia). unfold cap in *. lia. }
  1-3: (rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity | (rewrite L1; bveq) | exact L13 | exact L14 ]).
  eapply msteps_to_wall_tail; [exact Hms2|].
  assert (K1' : getr R2 1 = (0x1001168 : word))
    by (sym_regs HR2; first [reflexivity|bveq]).
  assert (K17' : getr R2 17 = Z_to_bv 64 64)
    by (sym_regs HR2; first [reflexivity|bveq]).
  assert (K10' : getr R2 10 = Z_to_bv 64 2)
    by (sym_regs HR2; first [reflexivity|bveq]).
  assert (K11' : getr R2 11 = aG) by (sym_regs HR2; reflexivity).
  assert (K13' : getr R2 13 = aG) by (sym_regs HR2; reflexivity).
  assert (K12' : getr R2 12 = nat_to_word (8 + length acc))
    by (sym_regs HR2; rewrite u_ntw by (unfold cap in *; lia);
        unfold nat_to_word; f_equal; lia).
  clear HR2.
  (* the whole emitted buffer, read back out of the grant: the eight
     header bytes just stored, spliced with the drained prefix *)
  assert (Hbuf : rdn target_segs mem8 aG (8 + length acc)%nat
                 = Some (arena_out acc)).
  { unfold arena_out, mem8.
    apply rdn_app.
    - replace (8%nat) with (length (hdr8 (length acc))) by apply hdr8_length.
      apply rdn_wbytes_hit. rewrite hdr8_length. lia.
    - rewrite rdn_wbytes_out.
      2: right; rewrite hdr8_length, word_add_nat, u_Z2bv by lia; lia.
      2: rewrite word_add_nat, u_Z2bv by (unfold cap in *; lia);
         unfold cap in *; lia.
      2: rewrite hdr8_length; lia.
      rewrite word_add_nat. exact Hrdn. }
  replace (Z_to_bv 64 16781864) with (0x1001228 : word) by bveq.
  eapply twt_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_1001228 eq_refl) | ].
  apply twt_more; [rewrite arena_out_length; lia|].
  apply (twl_write_rec target_segs (Z_to_bv 64 2)).
  - rewrite K17'. vm_compute. reflexivity.
  - rewrite <- getr_nz by reg_neq_tac; exact K10'.
  - rewrite <- ?getr_nz by reg_neq_tac; rewrite K11', K12'.
    rewrite (ms_read_bytes_rdn (run_segments target_segs inp asp amb)) by reflexivity;
      unfold run_segments; apply rdn_lift.
    cbn [ms_mem].
    rewrite word_to_nat_ntw by (unfold cap in *; lia).
    exact Hbuf.
  - (* [vfs_write]'s [access_ok]: the arena page lies below the stack *)
    rewrite <- ?getr_nz by reg_neq_tac; rewrite K11', K12'.
    apply Uaccess.access_okb_intro.
    rewrite u_ntw by (unfold cap in *; lia).
    unfold TASK_SIZE, cap in *. lia.
  - rewrite arena_out_length; lia.
  - (* every delivered length: the put2 retry loop delivers the rest *)
    intros n Hn1 Hn2.
    replace (v_addi (0x1001228 : word) 4) with (Z_to_bv 64 0x100122c) by bveq.
    apply (tgt_put_wall (length (arena_out acc)) (arena_out acc) aG n).
    + lia.
    + exact Hn1.
    + exact Hn2.
    + rewrite arena_out_length; unfold cap in *; lia.
    + lia.
    + rewrite arena_out_length; unfold cap in *; lia.
    + getr_resolve; exact K1'.
    + getr_resolve; reflexivity.
    + transitivity (nat_to_word (8 + length acc));
        [ getr_resolve; exact K12'
        | unfold len_word, nat_to_word; rewrite arena_out_length;
          reflexivity ].
    + getr_resolve; exact K13'.
    + getr_resolve; exact K17'.
    + rewrite arena_out_length. exact Hbuf.
Qed.


(* ================================================================= *)
(* The obligations                                                    *)
(* ================================================================= *)

Lemma tgt_grant_LH : forall regs (hint : word) a,
  getr regs 1 = (0x1001168 : word) ->
  getr regs 5 = Z_to_bv 64 4096 ->
  getr regs 11 = Z_to_bv 64 4096 ->
  grant_ok hint (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
                  (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)) a
    (page_round_up_Z (bv_unsigned (ms_gpr (tgt_mmap_ms regs) 1))) = true ->
  tgt_LH (in_fs inp) []
    (mkCfg (advance_past_svc
              (apply_effect (tgt_mmap_ms regs)
                 (mkEffect a []
                    [(a, page_round_up (ms_gpr (tgt_mmap_ms regs) 1))])))
           (mmap_model a (page_round_up (ms_gpr (tgt_mmap_ms regs) 1))
              (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
                 (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)))).
(** SEVEN instructions in ONE reflective block: the untaken [bltz a0]
    and the six [li]/[mv]/[addi]s that set up the loop's registers. *)
Proof.
  intros regs hint a Hr1 Hr5 H11 Hg.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  assert (Hga : ms_gpr (tgt_mmap_ms regs) 1 = Z_to_bv 64 4096).
  { unfold ms_gpr, tgt_mmap_ms; cbn [ms_regs]; rewrite arg_reg_1;
    rewrite <- getr_nz by reg_neq_tac; exact H11. }
  rewrite Hga in Hg |- *.
  change (page_round_up_Z (bv_unsigned (Z_to_bv 64 4096))) with 4096%Z in Hg.
  destruct (target_grant_unpack inp _ abrk amb asp a _ Hg)
    as (Hpos & Hal & Hceil & Hda & Hdb).
  assert (Hb : tgbounds asp a) by (repeat split; assumption).
  pose proof (u64_range a) as HaR.
  rewrite pru_4096.
  unfold tgt_mmap_ms. rewrite adv_apply.
  replace (v_addi (0x1001190 : word) 4) with (Z_to_bv 64 0x1001194) by bveq.
  sym_block_ex target_segs
    (mkst (regupd regs 10 a) (Z_to_bv 64 0x1001194)
          (zfill a (Z_to_bv 64 4096) tfmem) trom)
    7%nat [false] (@nil expr)
    [((1 : reg), ELit 0x1001168); ((5 : reg), ELit 4096); ((10 : reg), EVar 32)]
    [a] (@nil word) RA HRA Hms.
  { (* [bltz a0] at 0x1001194 -> not taken: the grant is positive *)
    apply (c_lts_pos_0 a); lia. }
  1-3: (getr_resolve; regupd_resolve; rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity | (rewrite Hr1; sym_close) | (rewrite Hr5; sym_close) ]).
  unfold tgt_LH. exists a, RA, (zfill a (Z_to_bv 64 4096) tfmem).
  cbn [cfg_ms cfg_model].
  split; [exact Hb|]. split; [reflexivity|].
  split; [rewrite mmap_model_lazy; reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [split; [reflexivity | split; [reflexivity | exact Hrd]]|].
  split; [replace (0x10011b0 : word) with (Z_to_bv 64 0x10011b0) by bveq; exact Hms|].
  split; [sym_regs HRA; sym_close|]. split; [sym_regs HRA; sym_close|].
  split; [sym_regs HRA; sym_close|]. split; [sym_regs HRA; sym_close|].
  split; [sym_regs HRA; sym_close|]. split; [sym_regs HRA; sym_close|].
  split; [sym_regs HRA; sym_close|].
  split; [cbn [length]; unfold cap; lia|].
  split; [apply mem_grows_refl|]. reflexivity.
Qed.

(** The loop exit: at [|acc| = cap] the [bltu a6,a0] at 0x10011b8 IS
    taken (511 > 510) and control reaches the header block with
    [a4] = the count. *)
Lemma tgt_Hfull : forall fs0 acc c,
  tgt_LH fs0 acc c -> (cap <= length acc)%nat ->
  realizes (run_segments target_segs inp asp amb) c (arena_tail fs0 acc).
Proof.
  intros fs0 acc c HLH Hfull.
  destruct HLH as (aG & regs & mem & Hb & Hh & Hlazy & Hfs & Hfd0 & Hfd2 & Hms0 &
                   K1 & K5 & K11 & K13 & K15 & K16 & K17 & Hle & Hmok & Hrdn).
  assert (Hn : length acc = cap) by lia.
  assert (Huk : bv_unsigned (nat_to_word (length acc)) = Z.of_nat (length acc))
    by (apply u_ntw; unfold cap in *; lia).
  apply tgt_tail.
  replace (0x10011b0 : word) with (Z_to_bv 64 0x10011b0) in Hms0 by bveq.
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 0x10011b0) mem trom)
    3%nat [true] (@nil expr)
    [((1 : reg), ELit 0x1001168); ((11 : reg), EVar 32); ((13 : reg), EVar 33);
     ((16 : reg), ELit 510)]
    [nat_to_word (length acc); aG] (@nil word) RA HRA Hms.
  { (* [bltu a6,a0] at 0x10011b8 -> taken: 4088 >> 3 = 511 > 510 *)
    rewrite v_srl_3, bv_ltu_Z.
    apply Z.ltb_lt.
    rewrite (v_srli_div (nat_to_word (length acc)) 3) by lia.
    rewrite Huk, u_Z2bv by lia. unfold cap in *. lia. }
  1-4: (rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity | (rewrite K1; sym_close) | (rewrite K11; sym_close)
              | (rewrite K13; sym_close) | (rewrite K16; sym_close) ]).
  unfold tgt_TH. exists aG, RA, mem. cbn [cfg_ms cfg_model].
  split; [exact Hb|]. split; [exact Hh|]. split; [exact Hlazy|].
  split; [exact Hfs|].
  split; [exact Hfd2|].
  split.
  { eapply msteps_trans; [exact Hms0|].
    replace (0x10011d8 : word) with (Z_to_bv 64 0x10011d8) by bveq. exact Hms. }
  split; [sym_regs HRA; sym_close|].
  split; [sym_regs HRA; sym_close|].
  split; [sym_regs HRA; sym_close|].
  split; [exact Hle|]. split; [exact Hmok|]. exact Hrdn.
Qed.

(** FROM the loop head to the read [ecall] at 0x10011c8: six
    instructions, the untaken capacity [bltu], and the two argument
    computations [a1 = a5 + a4] and [a2 = t0 - a4 = cap - |acc|]. *)
Lemma tgt_read_block : forall (aG : word) (regs : bvmap 5 word) mem (k : nat),
  tgbounds asp aG -> (k < cap)%nat ->
  getr regs 1 = (0x1001168 : word) ->
  getr regs 5 = Z_to_bv 64 4088 ->
  getr regs 11 = nat_to_word k ->
  getr regs 13 = aG ->
  getr regs 15 = Z_to_bv 64 (bv_unsigned aG + 8) ->
  getr regs 16 = Z_to_bv 64 510 ->
  getr regs 17 = Z_to_bv 64 63 ->
  exists R1,
    getr R1 1 = (0x1001168 : word) /\
    getr R1 5 = Z_to_bv 64 4088 /\
    getr R1 13 = aG /\
    getr R1 14 = nat_to_word k /\
    getr R1 15 = Z_to_bv 64 (bv_unsigned aG + 8) /\
    getr R1 16 = Z_to_bv 64 510 /\
    getr R1 17 = Z_to_bv 64 63 /\
    getr R1 10 = Z_to_bv 64 0 /\
    getr R1 11 = tbufA aG k /\
    getr R1 12 = Z_to_bv 64 (Z.of_nat (cap - k)) /\
    msteps target_segs (mkst regs (Z_to_bv 64 0x10011b0) mem trom)
                       (mkst R1 (Z_to_bv 64 0x10011c8) mem trom).
Proof.
  intros aG regs mem k Hb Hk H1 H5 H11 H13 H15 H16 H17.
  assert (Huk : bv_unsigned (nat_to_word k) = Z.of_nat k)
    by (apply u_ntw; unfold cap in *; lia).
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 0x10011b0) mem trom)
    6%nat [false] (@nil expr)
    [((1 : reg), ELit 0x1001168); ((5 : reg), ELit 4088); ((11 : reg), EVar 32);
     ((13 : reg), EVar 33); ((15 : reg), EVar 34); ((16 : reg), ELit 510);
     ((17 : reg), ELit 63)]
    [nat_to_word k; aG; Z_to_bv 64 (bv_unsigned aG + 8)]
    (@nil word) R1 HR1 Hms.
  { (* [bltu a6,a0] at 0x10011b8 -> not taken: |acc| >> 3 <= 510 *)
    rewrite v_srl_3, bv_ltu_Z.
    apply Z.ltb_ge.
    rewrite (v_srli_div (nat_to_word k) 3) by lia.
    rewrite Huk, u_Z2bv by lia. unfold cap in *. lia. }
  1-7: (rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity
              | (rewrite H1; sym_close) | (rewrite H5; sym_close)
              | (rewrite H11; sym_close) | (rewrite H13; sym_close)
              | (rewrite H15; sym_close) | (rewrite H16; sym_close)
              | (rewrite H17; sym_close) ]).
  exists R1.
  split; [sym_regs HR1; sym_close|]. split; [sym_regs HR1; sym_close|].
  split; [sym_regs HR1; sym_close|]. split; [sym_regs HR1; sym_close|].
  split; [sym_regs HR1; sym_close|]. split; [sym_regs HR1; sym_close|].
  split; [sym_regs HR1; sym_close|]. split; [sym_regs HR1; sym_close|].
  split; [sym_regs HR1; first [ apply (tbufA_calc asp); [exact Hb | lia] | sym_close ]|].
  split; [sym_regs HR1; first [ apply tdcnt; lia | sym_close ]|].
  exact Hms.
Qed.

(** The state the drain loop's [read] ecall dispatches from. *)
Definition tgt_rd_ms (R1 : bvmap 5 word) (mem : word -> option byte)
  : machine_state :=
  {| ms_regs := R1; ms_fregs := fp_regs; ms_pc_val := 0x10011c8;
     ms_svc_pending := Some (getr R1 17); ms_resv := None;
     ms_fcsr := fp_csr; ms_mem := mem; ms_rom := trom |}.

(** EOF: the [bnez a0] at 0x10011d4 is not taken and control falls into
    the header block with [a4] still the count. *)
Lemma tgt_ret_eof : forall (aG : word) (R1 : bvmap 5 word) mem (k : nat),
  getr R1 1 = (0x1001168 : word) ->
  getr R1 13 = aG -> getr R1 14 = nat_to_word k ->
  exists R2,
    getr R2 1 = (0x1001168 : word) /\
    getr R2 13 = aG /\ getr R2 14 = nat_to_word k /\
    msteps target_segs
      (mkst (regupd R1 10 (Z_to_bv 64 0)) (Z_to_bv 64 0x10011cc) mem trom)
      (mkst R2 (Z_to_bv 64 0x10011d8) mem trom).
Proof.
  intros aG R1 mem k H1 H13 H14.
  sym_block_ex target_segs
    (mkst (regupd R1 10 (Z_to_bv 64 0)) (Z_to_bv 64 0x10011cc) mem trom)
    3%nat [false; false] (@nil expr)
    [((1 : reg), ELit 0x1001168); ((10 : reg), ELit 0); ((13 : reg), EVar 32);
     ((14 : reg), EVar 33)]
    [aG; nat_to_word k] (@nil word) R2 HR2 Hms.
  1-4: (getr_resolve; regupd_resolve; rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity | (rewrite H1; sym_close)
              | (rewrite H13; sym_close) | (rewrite H14; sym_close) ]).
  exists R2.
  split; [sym_regs HR2; sym_close|]. split; [sym_regs HR2; sym_close|].
  split; [sym_regs HR2; sym_close|]. exact Hms.
Qed.

(** A delivered block: [a1 = a0 + a4] and the taken [bnez a0] put the
    machine back on the loop head with the count updated. *)
Lemma tgt_ret_blk : forall (aG : word) (R1 : bvmap 5 word) mem (k : nat)
                           (bs : list byte),
  getr R1 1 = (0x1001168 : word) ->
  getr R1 5 = Z_to_bv 64 4088 ->
  getr R1 13 = aG -> getr R1 14 = nat_to_word k ->
  getr R1 15 = Z_to_bv 64 (bv_unsigned aG + 8) ->
  getr R1 16 = Z_to_bv 64 510 -> getr R1 17 = Z_to_bv 64 63 ->
  (1 <= length bs)%nat -> (k + length bs <= cap)%nat ->
  exists R2,
    getr R2 1 = (0x1001168 : word) /\
    getr R2 5 = Z_to_bv 64 4088 /\
    getr R2 11 = nat_to_word (k + length bs) /\
    getr R2 13 = aG /\
    getr R2 15 = Z_to_bv 64 (bv_unsigned aG + 8) /\
    getr R2 16 = Z_to_bv 64 510 /\
    getr R2 17 = Z_to_bv 64 63 /\
    msteps target_segs
      (mkst (regupd R1 10 (len_word bs)) (Z_to_bv 64 0x10011cc) mem trom)
      (mkst R2 (Z_to_bv 64 0x10011b0) mem trom).
Proof.
  intros aG R1 mem k bs H1 H5 H13 H14 H15 H16 H17 Hlo Hhi.
  assert (Hul : bv_unsigned (len_word bs) = Z.of_nat (length bs))
    by (apply u_len_word; unfold cap in *; lia).
  sym_block_ex target_segs
    (mkst (regupd R1 10 (len_word bs)) (Z_to_bv 64 0x10011cc) mem trom)
    3%nat [false; true] (@nil expr)
    [((1 : reg), ELit 0x1001168); ((5 : reg), ELit 4088); ((10 : reg), EVar 32);
     ((13 : reg), EVar 33); ((14 : reg), EVar 34);
     ((15 : reg), EVar 35); ((16 : reg), ELit 510); ((17 : reg), ELit 63)]
    [len_word bs; aG; nat_to_word k; Z_to_bv 64 (bv_unsigned aG + 8)]
    (@nil word) R2 HR2 Hms.
  (* the [bltz] (a channel read is never negative) and the [bnez] (the
     block is nonempty), in the executor's reverse order *)
  1-2: first
    [ solve [ apply negb_true_iff; rewrite bv_eqb_Z; apply Z.eqb_neq;
              rewrite Hul, u_Z2bv by lia; lia ]
    | solve [ rewrite bv_lts_small
                by (rewrite ?Hul, ?u_Z2bv; unfold cap in *; lia);
              apply Z.ltb_ge; rewrite Hul, u_Z2bv by lia; lia ] ].
  1-8: (getr_resolve; regupd_resolve; rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity
              | (rewrite H1; sym_close) | (rewrite H5; sym_close)
              | (rewrite H13; sym_close) | (rewrite H14; sym_close)
              | (rewrite H15; sym_close) | (rewrite H16; sym_close)
              | (rewrite H17; sym_close) ]).
  exists R2.
  split; [sym_regs HR2; sym_close|]. split; [sym_regs HR2; sym_close|].
  split; [sym_regs HR2; first [ apply tntw_add; lia | sym_close ]|].
  split; [sym_regs HR2; sym_close|]. split; [sym_regs HR2; sym_close|].
  split; [sym_regs HR2; sym_close|]. split; [sym_regs HR2; sym_close|].
  exact Hms.
Qed.

Lemma tgt_Hread : forall fs0 acc c,
  tgt_LH fs0 acc c -> (length acc < cap)%nat ->
  exists ms1 buf x8 w,
    m_halted (cfg_model c) = None /\
    m_vm_lazy (cfg_model c) = [] /\
    fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0)
      = Some (FdChannel (Z_to_bv 64 0)) /\
    msteps (run_segments target_segs inp asp amb) (cfg_ms c) ms1 /\
    ms_svc_pending ms1 = Some x8 /\
    bv_unsigned x8 = 63%Z /\
    ms_gpr ms1 0 = Z_to_bv 64 0 /\
    ms_gpr ms1 1 = buf /\
    ms_gpr ms1 2 = dcnt cap acc /\
    read_bytes_map (ms_writable_byte (run_segments target_segs inp asp amb) ms1) buf (dcnt cap acc)
      = Some w /\
    (* the read range passes [access_ok]: the arena is a grant under this
       run's [alloc_top], itself under [State.TASK_SIZE]; [DrainAlg]'s
       [Hread] asks for it because [vfs_read] tests it before the fd is
       consulted *)
    access_okb buf (bv_unsigned (dcnt cap acc)) = true /\
    realizes (run_segments target_segs inp asp amb) (rd_next ms1 (cfg_model c) buf [])
      (arena_tail fs0 acc) /\
    (forall bs, rd_adm (m_stdin (cfg_model c)) (dcnt cap acc) bs -> bs <> [] ->
       tgt_LH fs0 (acc ++ bs) (rd_next ms1 (cfg_model c) buf bs)).
Proof.
  intros fs0 acc c HLH Hlt.
  destruct HLH as (aG & regs & mem & Hb & Hh & Hlazy & Hfs & Hfd0 & Hfd2 & Hms0 &
                   K1 & K5 & K11 & K13 & K15 & K16 & K17 & Hle & Hmok & Hrdn).
  pose proof Hb as Hb2. destruct Hb2 as (Hpos & Hal & Hceil & _).
  pose proof asp_hi_num. unfold stack_max_size in Hceil.
  pose proof (u64_range aG) as HaR.
  destruct (tgt_read_block aG regs mem (length acc) Hb Hlt K1 K5 K11 K13 K15 K16 K17)
    as (R1 & L1 & L5 & L13 & L14 & L15 & L16 & L17 & L10 & L11 & L12 & Hms1).
  assert (Hwb : exists w,
    read_bytes_map (ms_writable_byte (run_segments target_segs inp asp amb) (tgt_rd_ms R1 mem))
      (tbufA aG (length acc)) (dcnt cap acc) = Some w).
  { eapply (zmem_wbuf (run_segments target_segs inp asp amb) (tgt_rd_ms R1 mem) tfmem aG
              (Z_to_bv 64 4096)).
    - unfold tgt_rd_ms; cbn [ms_mem]. exact Hmok.
    - change (bv_unsigned (Z_to_bv 64 4096)) with 4096%Z. lia.
    - unfold tbufA. rewrite u_Z2bv by (unfold cap in *; lia). lia.
    - unfold tbufA. rewrite u_Z2bv by (unfold cap in *; lia).
      rewrite (dcnt_val cap Hcap_lt (tgt_LH fs0) (arena_tail fs0) acc) by lia.
      change (bv_unsigned (Z_to_bv 64 4096)) with 4096%Z. unfold cap in *. lia. }
  destruct Hwb as (w & Hwb).
  exists (tgt_rd_ms R1 mem), (tbufA aG (length acc)), (getr R1 17), w.
  split; [exact Hh|]. split; [exact Hlazy|]. split; [exact Hfd0|].
  split.
  { apply msteps_run.
    replace (0x10011b0 : word) with (Z_to_bv 64 0x10011b0) in Hms0 by bveq.
    eapply msteps_trans; [exact Hms0|].
    eapply msteps_trans; [exact Hms1|].
    norm_pc. unfold tgt_rd_ms.
    eapply mst_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_10011c8 eq_refl)
      | apply mst_refl ]. }
  split; [reflexivity|].
  split; [rewrite L17; vm_compute; reflexivity|].
  split; [ unfold ms_gpr, tgt_rd_ms; cbn [ms_regs]; rewrite arg_reg_0;
           rewrite <- getr_nz by reg_neq_tac; exact L10 |].
  split; [ unfold ms_gpr, tgt_rd_ms; cbn [ms_regs]; rewrite arg_reg_1;
           rewrite <- getr_nz by reg_neq_tac; exact L11 |].
  split; [ unfold ms_gpr, tgt_rd_ms, dcnt; cbn [ms_regs]; rewrite arg_reg_2;
           rewrite <- getr_nz by reg_neq_tac; exact L12 |].
  split; [exact Hwb|].
  split.
  { (* the range passes [access_ok]: the arena base plus 4096 is under
       this run's [alloc_top], itself far under [State.TASK_SIZE] *)
    apply Uaccess.access_okb_intro.
    unfold tbufA. rewrite u_Z2bv by (unfold cap in *; lia).
    rewrite (dcnt_val cap Hcap_lt (tgt_LH fs0) (arena_tail fs0) acc) by lia.
    unfold TASK_SIZE, cap in *. lia. }
  split.
  { (* EOF: fall through into the header block *)
    cbn [rd_next]. unfold tgt_rd_ms. rewrite adv_set.
    apply tgt_tail.
    destruct (tgt_ret_eof aG R1 mem (length acc) L1 L13 L14)
      as (R2 & M1 & M13 & M14 & Hms2).
    unfold tgt_TH. exists aG, R2, mem. cbn [cfg_ms cfg_model].
    split; [exact Hb|]. split; [exact Hh|]. split; [exact Hlazy|].
    split; [exact Hfs|].
    split; [exact Hfd2|].
    split.
    { replace (v_addi (0x10011c8 : word) 4) with (Z_to_bv 64 0x10011cc) by bveq.
      replace (0x10011d8 : word) with (Z_to_bv 64 0x10011d8) by bveq.
      exact Hms2. }
    split; [exact M1|]. split; [exact M13|]. split; [exact M14|].
    split; [exact Hle|]. split; [exact Hmok|]. exact Hrdn. }
  (* a delivered block: back to the loop head *)
  intros bs Hadm Hne.
  assert (Hbl : (length acc + length bs <= cap)%nat).
  { destruct Hadm as [(-> & _)|(Hlo1 & Hhi1 & _)]; [congruence|].
    rewrite (dcnt_val cap Hcap_lt (tgt_LH fs0) (arena_tail fs0) acc) in Hhi1
      by lia. lia. }
  assert (Hb1 : (1 <= length bs)%nat)
    by (destruct bs; [congruence | cbn [length]; lia]).
  destruct bs as [|b0 bs0]; [congruence|].
  cbn [rd_next]. unfold tgt_rd_ms. rewrite adv_write.
  set (bs := b0 :: bs0) in *.
  set (mem2 := write_to_mem mem (tbufA aG (length acc)) bs) in *.
  assert (Hrdn2 : rdn target_segs mem2 (Z_to_bv 64 (bv_unsigned aG + 8))
                    (length acc + length bs) = Some (acc ++ bs)).
  { apply rdn_app.
    - unfold mem2. rewrite write_to_mem_wbytes.
      rewrite rdn_wbytes_below
        by (unfold tbufA; rewrite ?u_Z2bv by (unfold cap in *; lia);
            unfold cap in *; lia).
      exact Hrdn.
    - rewrite (tbufA_split asp aG (length acc) Hb ltac:(lia)).
      unfold mem2. apply rdn_write_to_mem.
      unfold tbufA. rewrite u_Z2bv by (unfold cap in *; lia).
      unfold cap in *; lia. }
  destruct (tgt_ret_blk aG R1 mem2 (length acc) bs L1 L5 L13 L14 L15 L16 L17
              Hb1 Hbl)
    as (R2 & M1 & M5 & M11 & M13 & M15 & M16 & M17 & Hms2).
  unfold tgt_LH. rewrite length_app.
  exists aG, R2, mem2. cbn [cfg_ms cfg_model].
  split; [exact Hb|].
  split; [rewrite m_halted_with_stdin; exact Hh|].
  split; [rewrite m_vm_lazy_with_stdin; exact Hlazy|].
  split; [rewrite m_fs_with_stdin; exact Hfs|].
  split; [rewrite m_fds_with_stdin; exact Hfd0|].
  split; [unfold fdchan in *; rewrite m_fds_with_stdin; exact Hfd2|].
  split.
  { replace (v_addi (0x10011c8 : word) 4) with (Z_to_bv 64 0x10011cc) by bveq.
    replace (0x10011b0 : word) with (Z_to_bv 64 0x10011b0) by bveq.
    exact Hms2. }
  split; [exact M1|]. split; [exact M5|]. split; [exact M11|].
  split; [exact M13|]. split; [exact M15|]. split; [exact M16|].
  split; [exact M17|]. split; [exact Hbl|].
  split; [unfold mem2; apply tmem_ok_buf; exact Hmok|]. exact Hrdn2.
Qed.

(* ----------------------------------------------------------------- *)
(* The composition                                                    *)
(* ----------------------------------------------------------------- *)

Lemma target_realizes :
  realizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) TargetMemImage_init_pc target_phdrs
       asp abrk amb arnd target_alloc_limit inp)
    (arena_outcomes (in_fs inp) (in_stdin inp)).
Proof.
  destruct tgt_to_mmap
    as (regs & Hra & Hsp & H5 & H11 & H12 & H13 & H14 & H15 & H10 & Hno & Hms).
  unfold init_config, arena_outcomes, arena_fail.
  rewrite target_reserved_run.
  set (fs0 := in_fs inp) in *.
  eapply (rz_mmap_drain (run_segments target_segs inp asp amb) cap Hcap_lt Hcap_mod
            (tgt_LH fs0) (arena_tail fs0) (tgt_Hfull fs0) (tgt_Hread fs0)
            _ (tgt_mmap_ms regs)
            (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
               (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
            (getr regs 17) [] (Z_to_bv 64 1)).
  - reflexivity.
  - reflexivity.
  - (* fd 1 is the stdout channel with a reader ([State.with_vdso] keeps
       the descriptor table) *)
    split; [reflexivity | exact Hrd].
  - exact (msteps_run target_segs inp asp amb _ _ Hms).
  - reflexivity.
  - exact Hno.
  - unfold mmap_args_ok, ms_gpr, tgt_mmap_ms; cbn [ms_regs].
    rewrite arg_reg_1, arg_reg_2.
    assert (E3 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg)) by (apply bv_eq; reflexivity).
    assert (E4 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg)) by (apply bv_eq; reflexivity).
    assert (E5 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg)) by (apply bv_eq; reflexivity).
    rewrite E3, E4, E5.
    rewrite <- !getr_nz by reg_neq_tac.
    refine (conj _ (conj H12 (conj H13 (conj _ H15)))).
    + rewrite H11. discriminate.
    + rewrite H14. apply bv_eq. vm_compute. reflexivity.
  - (* a NULL hint is never declined: Linux v6.18.46 mm/mmap.c:754-761
       tries the hint only when it is nonzero, :763-770 search *)
    assert (Ha0 : ms_gpr (tgt_mmap_ms regs) 0 = Z_to_bv 64 0).
    { unfold ms_gpr, tgt_mmap_ms; cbn [ms_regs]. rewrite arg_reg_0.
      rewrite <- getr_nz by reg_neq_tac. exact H10. }
    rewrite Ha0. reflexivity.
  - intros e He. cbn [mmap_errnos In] in He.
    destruct He as [<- | []].
    cbn [to_wallexit]. apply to_wexit_run.
    apply tgt_fail_wexit;
      [ unfold ENOMEM; lia | unfold ENOMEM; lia | exact Hra ].
  - intros a Ha. eapply tgt_grant_LH; eassumption.
  - assert (Hlen : ms_gpr (tgt_mmap_ms regs) 1 = Z_to_bv 64 4096).
    { unfold ms_gpr, tgt_mmap_ms; cbn [ms_regs]. rewrite arg_reg_1.
      rewrite <- getr_nz by reg_neq_tac. exact H11. }
    rewrite Hlen.
    change (page_round_up_Z (bv_unsigned (Z_to_bv 64 4096))) with 4096%Z.
    exact (target_grant_witness inp _ abrk amb asp _ Hsp_lo Hmb).
  - (* the failure branch writes nothing at all *)
    constructor.
Qed.

End TargetProof.
