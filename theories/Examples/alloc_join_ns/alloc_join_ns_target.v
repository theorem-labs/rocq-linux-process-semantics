(** * alloc-join-ns TARGET binary (Zig): frames, prologue, length loop,
      early exits, the run up to the mmap ecall, and both continuations.

    PROOF-SIDE FILE (not part of the trusted specification).

    Machine plan (see alloc_join_ns_code.v):

      _start 0x1001158..0x1001174: 2-slot frame, argc/argv, call run.
      run 0x1001180: 48-byte frame; argc < 2 -> a1=2 -> 0x10012ac exit 2.
      length loop 0x10011bc..0x10011e0 (slen callee at 0x10012d0):
        s2 = |join1(argv[1..])| = tot - 1.
      cap: (tot-1) >> 16 != 0 -> exit 3.
      mmap args, DIRECT ecall at 0x100120c (the tmw branch point).
      Failure (blt a0,0): exit 4.
      Success: nested copy loops 0x1001228..0x1001268, '\n' store,
      one-write put loop, exit 0.  NO munmap.

    Conventions: sp-relative values are in the canonical
    [Z_to_bv 64 (bv_unsigned asp - k)] form, loop indices in
    [nat_to_word], the total byte count [ttot] is the word
    [nat_to_word ttotn]; all range bookkeeping is [Z] over
    [bv_unsigned].

    The run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  The derivations step over the image's own [target_segs]; the
    proof carries the [tmw] derivation to the run's list
    ([RunSegmentsLift.tmw_app]): no instruction here fetches from the
    pair.  The states carry the run's rom.  The grant address is the one
    Linux's placement rule gives ([target_grant_witness]), and the ledger
    the mmap reads is [State.init_reserved]: the image's reservations,
    then the vDSO pair.  The stack bounds come from the entry predicate's
    launch conjunct [Run.entry_launch_ok_va] and [Run.valid_launch]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import Footprint SymExec SymTac SymSide SymBranch.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec AllocSim WallSim MmapSim AllocSim2 StepTac ListFacts StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Examples.alloc_join_ns Require Import alloc_join_ns_code alloc_join_ns_defs.
From LinuxProcessSemantics.Examples.alloc_join_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.alloc_join_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them.  [fx0] itself is
    the instance, so every state here is [init_mkst]'s [@mkst fx0]. *)
#[local] Existing Instance fx0.

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x1001158%N.
Proof. vm_compute. reflexivity. Qed.

(** Successor step of a byte-walk pointer as a wrapping [bv] add
    (hypothesis-free: both sides wrap identically). *)
Lemma v_addi_ntw_S : forall (p : word) (j : nat),
  v_addi (p + nat_to_word j) 1 = p + nat_to_word (S j).
Proof.
  intros p j. rewrite !word_add_nat. apply bv_eq. unfold v_addi.
  rewrite !Z_to_bv_unsigned. rewrite bv_wrap_add_idemp_l.
  f_equal. lia.
Qed.

(** The register shift the [srli a0,s2,16] compiles to, in the
    immediate-shift spelling the rest of the file uses.  The shift
    amount is a closed literal; only the shifted value is symbolic. *)
Lemma v_srl_16 : forall x : word, v_srl x (Z_to_bv 64 16) = v_srli x 16.
Proof. intro x. unfold v_srl, v_srli. f_equal. Qed.

(* ================================================================= *)
(* Store legality (both target segments are read-only)                *)
(* ================================================================= *)

Lemma target_avoids_high : forall (a : word) (n : Z),
  (0x1002000 <= bv_unsigned a)%Z ->
  range_avoids_ro_segs target_segs (bv_unsigned a) n = true.
Proof.
  intros a n Ha.
  unfold target_segs, TargetMemImage_loaded_segments, range_avoids_ro_segs.
  cbn [forallb].
  change (Z.of_N (seg_base TargetMemImage_segment_000)
          + Z.of_N (seg_size TargetMemImage_segment_000))%Z with 0x1001000%Z.
  change (Z.of_N (seg_base TargetMemImage_segment_001)
          + Z.of_N (seg_size TargetMemImage_segment_001))%Z with 0x1002000%Z.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned a) 0x1001000)) by lia.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned a) 0x1002000)) by lia.
  rewrite !andb_false_r. reflexivity.
Qed.

(* ================================================================= *)
(* Grant facts for the target image                                   *)
(* ================================================================= *)

Lemma target_reserved_val :
  segments_reserved target_segs = [(0x1000000, 0x1000); (0x1001000, 0x1000)].
Proof.
  apply (proj1 (listNN_eqb_eq _ _)). vm_compute. reflexivity.
Qed.

(** The image's reservations end below [Mmap.task_unmapped_base], where
    the grant witness's gap starts. *)
Lemma target_reserved_low : forall a sz, In (a, sz) (segments_reserved target_segs) ->
  (bv_unsigned a + bv_unsigned sz <= Mmap.task_unmapped_base)%Z.
Proof.
  intros a sz Hin. rewrite target_reserved_val in Hin.
  unfold Mmap.task_unmapped_base.
  destruct Hin as [Hin | [Hin | []]]; injection Hin as <- <-;
    apply Z.leb_le; vm_compute; reflexivity.
Qed.

(** The launch model's grant of [g] bytes exists
    ([RunSegmentsLift.grant_witness_init_len]): its address is the one
    Linux's placement gives, not a fixed one (Linux v6.18.46 mm/mmap.c:754-761
    try a nonzero hint first, :763-770 search top-down below the mmap
    base).  The model is [Run]'s: [State.with_vdso] of the draw's vDSO
    counter over [State.init_model]. *)
Lemma target_grant_witness : forall inp (hint brk0 mb sp : word) v (g : Z),
  (sp_window_lo <= bv_unsigned sp)%Z -> (mmap_base_min <= bv_unsigned mb)%Z ->
  (0 < g)%Z -> (g mod page_size = 0)%Z -> (g <= 69632)%Z ->
  exists a, grant_ok hint
    (with_vdso v (init_model (segments_reserved target_segs) brk0 mb sp target_alloc_limit inp))
    a g = true.
Proof.
  intros inp hint brk0 mb sp v g Hsp Hmb Hg0 Hgal Hg.
  apply grant_witness_init_len;
    [exact target_reserved_low | exact Hsp | exact Hmb | exact Hg0 | exact Hgal | lia |].
  change target_alloc_limit with 0x8000000000%Z. lia.
Qed.

Lemma target_grant_unpack : forall inp (hint brk0 mb sp : word) v (aG : word) (g : Z),
  (0 <= g)%Z -> (g < 2^64)%Z ->
  grant_ok hint (with_vdso v (init_model (segments_reserved target_segs) brk0 mb sp
                                target_alloc_limit inp)) aG g
  = true ->
  (0 < bv_unsigned aG)%Z /\ (bv_unsigned aG + g <= bv_unsigned sp - stack_max_size)%Z /\
  ((bv_unsigned aG + g <= 0x1000000)%Z \/ (0x1001000 <= bv_unsigned aG)%Z) /\
  ((bv_unsigned aG + g <= 0x1001000)%Z \/ (0x1002000 <= bv_unsigned aG)%Z).
Proof.
  intros inp hint brk0 mb sp v aG g Hg0 Hg64 Hg.
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
  change (bv_unsigned (0x1000000 : word)) with 0x1000000%Z in Hda.
  change (bv_unsigned (0x1001000 : word)) with 0x1001000%Z in Hdb.
  change (bv_unsigned (0x1000 : word)) with 0x1000%Z in Hda, Hdb.
  rewrite u_Z2bv in Hda, Hdb by lia.
  refine (conj Hpos (conj Hceil (conj _ _))).
  - destruct Hda as [H|H]; [left; lia | right; lia].
  - destruct Hdb as [H|H]; [left; lia | right; lia].
Qed.

Lemma target_grant_avoids : forall (aZ g x k : Z),
  ((aZ + g <= 0x1000000)%Z \/ (0x1001000 <= aZ)%Z) ->
  ((aZ + g <= 0x1001000)%Z \/ (0x1002000 <= aZ)%Z) ->
  (aZ <= x)%Z -> (x + k <= aZ + g)%Z ->
  range_avoids_ro_segs target_segs x k = true.
Proof.
  intros aZ g x k Hda Hdb Hx1 Hx2.
  unfold target_segs, TargetMemImage_loaded_segments, range_avoids_ro_segs.
  cbn [forallb].
  change (Z.of_N (seg_base TargetMemImage_segment_000)
          + Z.of_N (seg_size TargetMemImage_segment_000))%Z with 0x1001000%Z.
  change (Z.of_N (seg_base TargetMemImage_segment_000)) with 0x1000000%Z.
  change (Z.of_N (seg_base TargetMemImage_segment_001)
          + Z.of_N (seg_size TargetMemImage_segment_001))%Z with 0x1002000%Z.
  change (Z.of_N (seg_base TargetMemImage_segment_001)) with 0x1001000%Z.
  assert (Hb0 : ((0x1000000 <? x + k)%Z && (x <? 0x1001000)%Z) = false).
  { destruct Hda as [H|H].
    - rewrite (proj2 (Z.ltb_ge 0x1000000 (x + k))) by lia.
      apply andb_false_l.
    - rewrite (proj2 (Z.ltb_ge x 0x1001000)) by lia.
      apply andb_false_r. }
  assert (Hb1 : ((0x1001000 <? x + k)%Z && (x <? 0x1002000)%Z) = false).
  { destruct Hdb as [H|H].
    - rewrite (proj2 (Z.ltb_ge 0x1001000 (x + k))) by lia.
      apply andb_false_l.
    - rewrite (proj2 (Z.ltb_ge x 0x1002000)) by lia.
      apply andb_false_r. }
  rewrite Hb0, Hb1. reflexivity.
Qed.

(* ================================================================= *)
(* The proof, generic over argv/envp and the stack pointer             *)
(* ================================================================= *)

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

Lemma asp_lo_num : (0x7fff80000000 <= bv_unsigned asp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma asp_hi_num : (bv_unsigned asp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

(** The quantified initial program break — the mmap-allocating target
    never touches it, so the break is read only by the launch conjunct. *)
Variable abrk : word.
Variable amb : word.
Hypothesis Hvl : valid_launch inp.

(** The fifth conjunct of [Run.valid_entry_va] for the target's run
    ([create_elf_tables] and [setup_arg_pages], fs/binfmt_elf.c and
    fs/exec.c, Linux v6.18.46). *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry asp abrk amb arnd) inp.

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

Lemma targcN_le : (bv_unsigned targcN <= 1024)%Z.
Proof. rewrite u_targcN. apply valid_argv_len. exact Hva. Qed.

Lemma targc_le_nat : (length av <= 1024)%nat.
Proof. pose proof (valid_argv_len av Hva). lia. Qed.

Lemma targN_small : forall i, (i <= length av)%nat -> (Z.of_nat i < 2^63)%Z.
Proof. intros i Hi. pose proof targc_le_nat. lia. Qed.

Lemma tiN_le : forall i, (i <= length av)%nat -> (Z.of_nat i <= 1024)%Z.
Proof. intros i Hi. pose proof targc_le_nat. lia. Qed.

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
    (Z_to_bv 64 (bv_unsigned asp - 8))  (word_to_le_bytes 8 (Z_to_bv 64 0)))  (* _start: sd ra,8(sp) *)
    (Z_to_bv 64 (bv_unsigned asp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)). (* _start: sd s0,0(sp) *)

(** Memory after run's frame stores (argc-agnostic: they always run). *)
Definition tfmem : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes smem
    (Z_to_bv 64 (bv_unsigned asp - 24)) (word_to_le_bytes 8 (0x1001178 : word))) (* run: sd ra,40(sp) *)
    (Z_to_bv 64 (bv_unsigned asp - 32)) (word_to_le_bytes 8 asp))                (* run: sd s0,32(sp) *)
    (Z_to_bv 64 (bv_unsigned asp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* run: sd s1,24(sp) *)
    (Z_to_bv 64 (bv_unsigned asp - 48)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* run: sd s2,16(sp) *)
    (Z_to_bv 64 (bv_unsigned asp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* run: sd s3,8(sp)  *)
    (Z_to_bv 64 (bv_unsigned asp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0)).    (* run: sd s4,0(sp)  *)

Lemma rdn_awmem_stack : forall (a : word) k,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= 2^64)%Z ->
  rdn target_segs awmem a k
  = rdn target_segs
      (stack_to_mem asp (entry_stack_image inp amb target_phdrs
                           (Z_to_bv 64 (Z.of_N 0x1001158)) asp arnd)) a k.
Proof. intros a k Ha Hk. apply rdn_wrap_stack_above; assumption. Qed.

Lemma rdn_smem_above : forall (a : word) k,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= 2^64)%Z ->
  rdn target_segs smem a k = rdn target_segs awmem a k.
Proof.
  intros a k Ha Hk. pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. unfold smem.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; u_norm; lia)).
  reflexivity.
Qed.

Lemma rdn_tfmem_above : forall (a : word) k,
  (bv_unsigned asp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= 2^64)%Z ->
  rdn target_segs tfmem a k = rdn target_segs awmem a k.
Proof.
  intros a k Ha Hk. pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. unfold tfmem.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; u_norm; lia)).
  apply rdn_smem_above; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(* Per-argument reads                                                  *)
(* ----------------------------------------------------------------- *)

Definition tsptr (k : nat) : word := cat_argv_ptr (ed_top arnd) av ev (in_execfn inp) k.

Lemma tsptr_bounds : forall k, (k < length av)%nat ->
  (bv_unsigned asp <= bv_unsigned (tsptr k))%Z /\
  (bv_unsigned (tsptr k) + Z.of_nat (length (nth k av [])) + 1 < 2^64)%Z.
Proof.
  intros k Hk. unfold tsptr.
  exact (argv_ptr_bounds Sv48 inp amb asp abrk arnd k Hlau Hk).
Qed.

Lemma tread_arg_ptr : forall k, (k < length av)%nat ->
  rdn target_segs tfmem (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * Z.of_nat k)) 8%nat
  = Some (word_le8 (tsptr k)).
Proof.
  intros k Hk. pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as Hlen.
  assert (HkZ : (Z.of_nat k <= 1024)%Z) by lia.
  replace (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * Z.of_nat k))
    with (asp + nat_to_word (8 + 8 * k)) by (rewrite word_add_nat; f_equal; lia).
  rewrite rdn_tfmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_awmem_stack by (rewrite word_add_nat; u_norm; lia).
  unfold tsptr. apply read_argv_ptr_k; [assumption | apply target_bsb_nw].
Qed.

Lemma tread_arg_byte : forall k j, (k < length av)%nat ->
  (j <= length (nth k av []))%nat ->
  rdn target_segs tfmem (tsptr k + nat_to_word j) 1%nat
  = Some [byte_at (nth k av []) j].
Proof.
  intros k j Hk Hj.
  destruct (tsptr_bounds k Hk) as [Hge Hup].
  pose proof (valid_argv_str_len av k Hva Hk) as Hslen.
  pose proof (u64_range asp). pose proof (u64_range (tsptr k)).
  rewrite rdn_tfmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_awmem_stack by (rewrite word_add_nat; u_norm; lia).
  unfold tsptr, byte_at.
  apply (read_argv_byte_k Sv48 target_segs inp amb target_phdrs _ asp abrk arnd k j Hlau);
    [exact Hk | exact Hj].
Qed.

Lemma targ_bytes_k : forall k, (k < length av)%nat ->
  Forall (fun b : byte => (bv_unsigned b < 256)%Z) (nth k av []).
Proof. intros k Hk. apply valid_argv_str_bytes; assumption. Qed.

Lemma targ_nz_k : forall k, (k < length av)%nat ->
  ~ In (Z_to_bv 8 0) (nth k av []).
Proof. intros k Hk. apply valid_argv_str_nz; assumption. Qed.

(* ----------------------------------------------------------------- *)
(* Frame-slot read-back                                                *)
(* ----------------------------------------------------------------- *)

Lemma tfread_slot_ra :
  rdn target_segs tfmem (Z_to_bv 64 (bv_unsigned asp - 24)) 8%nat
  = Some (word_to_le_bytes 8 (0x1001178 : word)).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. unfold tfmem.
  repeat first
    [ rewrite rdn_wbytes_hit8 by (u_norm; lia)
    | rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; u_norm; lia)
    | rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; u_norm; lia) ].
  reflexivity.
Qed.

Lemma tfread_slot_s0 :
  rdn target_segs tfmem (Z_to_bv 64 (bv_unsigned asp - 32)) 8%nat
  = Some (word_to_le_bytes 8 asp).
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. unfold tfmem.
  repeat first
    [ rewrite rdn_wbytes_hit8 by (u_norm; lia)
    | rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; u_norm; lia)
    | rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; u_norm; lia) ].
  reflexivity.
Qed.

Lemma tfread_slot_0 : forall a : word,
  In a [Z_to_bv 64 (bv_unsigned asp - 40); Z_to_bv 64 (bv_unsigned asp - 48);
        Z_to_bv 64 (bv_unsigned asp - 56); Z_to_bv 64 (bv_unsigned asp - 64)] ->
  rdn target_segs tfmem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros a Ha. pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. unfold tfmem.
  repeat destruct Ha as [<-|Ha];
    try (exfalso; exact Ha);
    repeat first
      [ rewrite rdn_wbytes_hit8 by (u_norm; lia)
      | rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia)
      | rewrite rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes; u_norm; lia) ];
    reflexivity.
Qed.

(* ================================================================= *)
(* Epilogue: 0x10012b0 .. ret .. exit ecall (generic memory)          *)
(* ================================================================= *)

Lemma target_epilogue : forall regs (mem : word -> option byte) (code : word),
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64) ->
  reg_get regs 10 = code ->
  rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 24)) 8%nat
  = Some (word_to_le_bytes 8 (0x1001178 : word)) ->
  rdn target_segs mem (Z_to_bv 64 (bv_unsigned asp - 32)) 8%nat
  = Some (word_to_le_bytes 8 asp) ->
  (forall a : word,
     In a [Z_to_bv 64 (bv_unsigned asp - 40); Z_to_bv 64 (bv_unsigned asp - 48);
           Z_to_bv 64 (bv_unsigned asp - 56); Z_to_bv 64 (bv_unsigned asp - 64)] ->
     rdn target_segs mem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  exists regs',
    bv_unsigned (getr regs' 17) = 93%Z /\ reg_get regs' 10 = code /\
    msteps target_segs (mkst regs 0x10012b0 mem arom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := 0x100117c;
         ms_svc_pending := Some (getr regs' 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := arom |}.
(** NINE instructions in ONE reflective block: the six frame reloads,
    the stack pop, the run function's [ret] — literal because the
    reload of [ra] is NAMED in the read script — and the crt's
    [li a7,93] before the [exit] ecall.  The saved [s0] is a SYMBOLIC
    value, so it is named as [EVar 33] and its denotation is supplied
    in the pin-value list alongside the [sp] pin. *)
Proof.
  intros regs mem code H2 H10 Hra Hs0 Hsl.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  replace (0x10012b0 : word) with (Z_to_bv 64 0x10012b0) by bveq.
  sym_block_ex target_segs (mkst regs (Z_to_bv 64 0x10012b0) mem arom)
    9%nat (@nil bool)
    [ELit 0x1001178; EVar 33; ELit 0; ELit 0; ELit 0; ELit 0]
    [((2 : reg), EVar 32)]
    [Z_to_bv 64 (bv_unsigned asp - 64); asp] (@nil word) R HR Hms.
  1: (exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hsl; right; right; right; left; reflexivity
      | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  1: (exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hsl; right; right; left; reflexivity
      | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  1: (exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hsl; right; left; reflexivity
      | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  1: (exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hsl; left; reflexivity
      | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  1: (exists (word_to_le_bytes 8 asp); split;
      [ exact Hs0 | rewrite bytes_le_to_Z_8; reflexivity ]).
  1: (exists (word_to_le_bytes 8 (0x1001178 : word)); split;
      [ exact Hra | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  { (* the [sp] pin *) exact H2. }
  exists R. refine (conj _ (conj _ _)).
  - sym_regs HR. vm_compute. reflexivity.
  - sym_regs HR. first [ exact H10 | rewrite <- getr_nz by reg_neq_tac; exact H10 ].
  - eapply msteps_trans; [ exact Hms | ]. norm_pc; sym_pc_lit.
    eapply mst_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_100117c eq_refl)
      | apply mst_refl ].
Qed.

(* ================================================================= *)
(* _start + run prologue to the argc dispatch                          *)
(* ================================================================= *)

(** From the entry to the argc branch at 0x10011a4, with the run frame
    stored: sp = asp-64, s0 = asp+8, a0 = argc, a1 = 2. *)
Lemma target_to_dispatch :
  exists regsP,
    reg_get regsP 2 = Z_to_bv 64 (bv_unsigned asp - 64) /\
    reg_get regsP 8 = Z_to_bv 64 (bv_unsigned asp + 8) /\
    reg_get regsP 10 = targcN /\
    reg_get regsP 11 = Z_to_bv 64 2 /\
    msteps target_segs
      (init_machine_state (run_segments target_segs inp asp amb) 0x1001158 target_phdrs asp amb arnd inp)
      (mkst regsP 0x10011a4 tfmem arom).
(** SEVENTEEN instructions in ONE reflective block: [_start]'s frame,
    the [ld] of argc, the [jalr] into [run] and [run]'s own frame push
    with its six spills, down to the argc dispatch.  Eight stores and
    one load; the six callee-saved registers are pinned to [ELit 0] so
    that the spilled values are literals and the exit memory is
    literally [tfmem]. *)
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as HargcLe.
  pose proof u_targcN as Hu.
  rewrite init_mkst.
  sym_block_ex target_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 asp)
          (Z_to_bv 64 (Z.of_N 0x1001158))
          (wrap_mem inp amb target_phdrs (Z_to_bv 64 (Z.of_N 0x1001158)) asp arnd)
          (seg_rom (run_segments target_segs inp asp amb)))
    17%nat (@nil bool) (@nil expr)
    [((2 : reg), EVar 32); ((1 : reg), ELit 0); ((8 : reg), ELit 0);
     ((9 : reg), ELit 0); ((18 : reg), ELit 0); ((19 : reg), ELit 0);
     ((20 : reg), ELit 0)]
    [asp] [targcN] RA HRA Hms.
  1-6: solve_store_ok.
  { (* [ld a0,0(s0)] at 0x1001168 -> argc, out of the initial stack image *)
    replace (Z_to_bv 64 (bv_unsigned asp + 0)) with asp
      by (apply bv_eq; u_norm; lia);
    exists (word_le8 targcN); split;
      [ rewrite rdn_wrap_stack_above by lia;
        apply read_argc; apply target_bsb_nw
      | apply bytes_le_n_to_le_8 ]. }
  1-2: solve_store_ok.
  exists RA. refine (conj _ (conj _ (conj _ (conj _ _)))).
  1-4: (sym_regs HRA; sym_close).
  replace (0x10011a4 : word) with (Z_to_bv 64 16781732) by bveq.
  unfold tfmem, smem, awmem, arom.
  revert Hms. sym_mem_norm. exact (fun x => x).
Qed.

(** argc < 2: no output, exit 2. *)
Lemma target_wexit_lt2 : (length av < 2)%nat ->
  to_wexit target_segs
    (init_machine_state (run_segments target_segs inp asp amb) 0x1001158 target_phdrs asp amb arnd inp)
    [] (Z_to_bv 64 2).
Proof.
  intros Hlt2.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as HA.
  destruct target_to_dispatch as (regsP & P2 & P8 & P10 & P11 & Hms).
  eapply msteps_to_wexit; [exact Hms|].
  (* bltu a0,a1 taken (argc < 2) -> 0x10012ac *)
  eapply tw_step;
    [ reflexivity
    | eapply step_bltu_tk;
      [ exact TF_10011a4 | reflexivity | exact TD_10011a4
      | getr_resolve; rewrite P10, P11;
        rewrite c_ltu_ltb; apply Z.ltb_lt;
        rewrite u_targcN; u_norm; lia ]
    | norm_pc ].
  (* mv a0,a1 -> 2 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 2);
      [ exact TF_10012ac | reflexivity | exact TD_10012ac | reflexivity
      | getr_resolve; rewrite P11; apply v_addi_0 ]
    | step_simpl ].
  (* epilogue with a0 = 2 *)
  lazymatch goal with
  | |- to_wexit _ (mkst ?R _ _ _) _ _ =>
    edestruct (target_epilogue R tfmem (Z_to_bv 64 2)) as [regsE [HE17 [HE10 HmsE]]]
  end.
  - regupd_resolve. exact P2.
  - regupd_resolve. reflexivity.
  - exact tfread_slot_ra.
  - exact tfread_slot_s0.
  - exact tfread_slot_0.
  - eapply msteps_to_wexit; [exact HmsE|].
    apply tw_exit_coden;
      [exact HE17 | exact HE10 | vm_compute; reflexivity].
Qed.

(* ================================================================= *)
(* Join-length theory (target-side duplicates)                        *)
(* ================================================================= *)

Section Ge2T.

Hypothesis Hge2 : (2 <= length av)%nat.

Definition ttotn : nat := total_arg_bytes_nat (tl av).
Definition ttot : word := nat_to_word ttotn.

Lemma ttl_nonnil : tl av <> [].
Proof.
  destruct av as [|a0 [|a1 l]]; cbn [length] in Hge2; try lia.
  cbn [tl]. congruence.
Qed.

Lemma tab_join1_t : forall l,
  total_arg_bytes_nat l
  = (length (join1 l) + (if Nat.eqb (length l) 0 then 0 else 1))%nat.
Proof.
  intro l. destruct l as [|a l'].
  - reflexivity.
  - cbn [length Nat.eqb].
    rewrite <- length_wjoin. rewrite wjoin_join1 by discriminate.
    rewrite length_app. cbn [length]. lia.
Qed.

Lemma ttotn_ge1 : (1 <= ttotn)%nat.
Proof.
  unfold ttotn. rewrite tab_join1_t.
  destruct (Nat.eqb (length (tl av)) 0) eqn:E.
  - apply Nat.eqb_eq in E. apply length_zero_iff_nil in E.
    exfalso. apply ttl_nonnil. exact E.
  - lia.
Qed.

Lemma ttotn_bound : (Z.of_nat ttotn <= 2097152)%Z.
Proof.
  unfold ttotn.
  pose proof (valid_argv_tab av Hva) as Hb.
  apply Nat2Z.inj_le in Hb. rewrite of_nat_2097152 in Hb.
  assert (Htlskip : tl av = skipn 1 av) by (destruct av; reflexivity).
  rewrite Htlskip.
  rewrite <- (firstn_skipn 1 av) in Hb.
  rewrite tab_app in Hb. lia.
Qed.

Lemma u_ttot : bv_unsigned ttot = Z.of_nat ttotn.
Proof.
  unfold ttot. apply u_ntw. pose proof ttotn_bound. lia.
Qed.

Lemma ttot_ge1 : (1 <= bv_unsigned ttot)%Z.
Proof. rewrite u_ttot. pose proof ttotn_ge1. lia. Qed.

Lemma ttot_bound : (bv_unsigned ttot <= 2097152)%Z.
Proof. rewrite u_ttot. exact ttotn_bound. Qed.

Lemma tjoin1_tl_len_nat : length (join1 (tl av)) = (ttotn - 1)%nat.
Proof.
  pose proof (length_join1 (tl av) ttl_nonnil) as H.
  unfold ttotn. lia.
Qed.

Lemma tjout_len_nat : length (jout av) = ttotn.
Proof.
  unfold jout. rewrite length_app. cbn [length].
  pose proof tjoin1_tl_len_nat. pose proof ttotn_ge1. lia.
Qed.

Lemma tjout_len_w : word_to_nat ttot = length (jout av).
Proof.
  rewrite tjout_len_nat. unfold ttot. apply word_to_nat_ntw.
  pose proof ttotn_bound. lia.
Qed.

Lemma tlength_tl_av : length (tl av) = (length av - 1)%nat.
Proof. apply length_tl_list. Qed.

Lemma tjpre_step : forall i, (1 <= i)%nat -> (i <= length (tl av))%nat ->
  length (join1 (firstn i (tl av)))
  = (length (join1 (firstn (i-1) (tl av))) + length (nth i av [])
     + (if Nat.eqb i 1 then 0 else 1))%nat.
Proof.
  intros i H1 Hi.
  replace i with (S (i - 1)) at 1 by lia.
  rewrite (firstn_S_nth _ (tl av) (i-1) []) by lia.
  rewrite join1_snoc. rewrite length_app, length_wjoin.
  rewrite nth_tl. replace (S (i-1)) with i by lia.
  rewrite (tab_join1_t (firstn (i-1) (tl av))).
  rewrite firstn_length_le by lia.
  destruct i as [|i']; [lia|].
  cbn [Nat.sub]. rewrite Nat.sub_0_r.
  destruct i' as [|i'']; cbn [Nat.eqb]; lia.
Qed.

(** Length of the join1 prefix at outer index [i] (args 1..i-1 done). *)
Definition pbJ (i : nat) : nat :=
  length (join1 (firstn (i-1) (tl av))).

Lemma pbJ_1 : pbJ 1 = 0%nat.
Proof. reflexivity. Qed.

Lemma pbJ_le : forall i, (pbJ i <= ttotn - 1)%nat.
Proof.
  intro i. unfold pbJ, ttotn.
  pose proof (tab_join1_t (firstn (i-1) (tl av))) as Hj.
  assert (Hm : (total_arg_bytes_nat (firstn (i-1) (tl av))
                <= total_arg_bytes_nat (tl av))%nat).
  { rewrite <- (firstn_skipn (i-1) (tl av)) at 2. rewrite tab_app. lia. }
  pose proof ttotn_ge1 as Hg1. unfold ttotn in Hg1.
  destruct (length (firstn (i-1) (tl av))) eqn:El.
  - apply length_zero_iff_nil in El. rewrite El. cbn [join1 length]. lia.
  - try rewrite El in Hj. cbn [Nat.eqb] in Hj. lia.
Qed.

Lemma pbJ_last : pbJ (length av) = (ttotn - 1)%nat.
Proof.
  unfold pbJ.
  replace (firstn (length av - 1) (tl av)) with (tl av).
  2:{ rewrite <- tlength_tl_av. symmetry. apply firstn_all. }
  apply tjoin1_tl_len_nat.
Qed.

Lemma pbJ_stepN : forall i, (1 <= i)%nat -> (i < length av)%nat ->
  pbJ (S i) = (pbJ i + length (nth i av [])
               + (if Nat.eqb i 1 then 0 else 1))%nat.
Proof.
  intros i H1 Hi. unfold pbJ.
  replace (S i - 1)%nat with i by lia.
  rewrite (tjpre_step i H1 ltac:(rewrite tlength_tl_av; lia)).
  reflexivity.
Qed.

Lemma tjoin_step : forall i, (2 <= i)%nat -> (i < length av)%nat ->
  join1 (firstn i (tl av))
  = join1 (firstn (i-1) (tl av)) ++ Z_to_bv 8 32 :: nth i av [].
Proof.
  intros i H2 Hi.
  replace i with (S (i - 1)) at 1 by lia.
  rewrite (firstn_S_nth _ (tl av) (i-1) []) by (rewrite tlength_tl_av; lia).
  rewrite join1_snoc.
  rewrite (wjoin_join1 (firstn (i-1) (tl av)))
    by (apply firstn_nonnil; [lia | apply ttl_nonnil]).
  rewrite nth_tl. replace (S (i-1)) with i by lia.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma tjoin_1 : join1 (firstn 1 (tl av)) = nth 1 av [].
Proof.
  destruct av as [|a0 [|a1 l]]; cbn [length] in Hge2; try lia.
  reflexivity.
Qed.

(* ================================================================= *)
(* slen callee: 0x10012d4 loop, exit at 0x10012e4                     *)
(* ================================================================= *)

Lemma target_slen : forall k, (k < length av)%nat ->
  forall d j regs,
  (j + d = length (nth k av []))%nat ->
  reg_get regs 10 = tsptr k ->
  reg_get regs 11 = nat_to_word j ->
  exists regs',
    (forall r : reg, r <> 11 -> r <> 12 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 11 = nat_to_word (length (nth k av [])) + 1 /\
    msteps target_segs (mkst regs 0x10012d4 tfmem arom)
                       (mkst regs' 0x10012e4 tfmem arom).
Proof.
  intros k Hk.
  destruct (tsptr_bounds k Hk) as [Hplo Hphi].
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (targ_nz_k k Hk) as Hnz.
  pose proof (valid_argv_str_len av k Hva Hk) as Hslen.
  set (nk := length (nth k av [])) in *.
  induction d as [|d IH]; intros j regs Hjd Hr10 Hr11.
  - (* j = nk: NUL byte, fall through *)
    assert (Hj : j = nk) by lia.
    set (regs1 := regupd regs 12 (tsptr k + nat_to_word j)).
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x10012d4 tfmem arom)
                 = MachineOk (mkst regs1 0x10012d8 tfmem arom)).
    { eapply eq_trans;
      [ apply (step_add_at target_segs regs 0x10012d4 tfmem arom _ 12 10 11
                 (tsptr k + nat_to_word j) TF_10012d4 eq_refl TD_10012d4 eq_refl);
        getr_resolve; rewrite Hr10, Hr11; rewrite v_add_word; reflexivity
      | wlits; reflexivity ]. }
    set (regs2 := regupd regs1 12 (Z_to_bv 64 0)).
    assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x10012d8 tfmem arom)
                 = MachineOk (mkst regs2 0x10012dc tfmem arom)).
    { rewrite (step_lbu target_segs regs1 0x10012d8 tfmem arom _ 12 12 _ (Z_to_bv 8 0)
                 TF_10012d8 eq_refl TD_10012d8).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite v_addi_0.
        pose proof (tread_arg_byte k j Hk ltac:(unfold nk in *; lia)) as Hrd.
        assert (Hb0 : byte_at (nth k av []) j = Z_to_bv 8 0).
        { unfold nk in Hj. rewrite Hj. apply byte_at_len. }
        rewrite Hb0 in Hrd. exact Hrd. }
    set (regs3 := regupd regs2 11 (nat_to_word (S j))).
    assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x10012dc tfmem arom)
                 = MachineOk (mkst regs3 0x10012e0 tfmem arom)).
    { eapply eq_trans;
      [ apply (step_addi_at target_segs regs2 0x10012dc tfmem arom _ 11 11 _
                 (nat_to_word (S j)) TF_10012dc eq_refl TD_10012dc eq_refl);
        unfold regs2, regs1; getr_resolve; rewrite Hr11;
        apply v_addi_Sj; lia
      | wlits; reflexivity ]. }
    assert (E4 : RiscvSemantics.step target_segs (mkst regs3 0x10012e0 tfmem arom)
                 = MachineOk (mkst regs3 0x10012e4 tfmem arom)).
    { rewrite (step_bne_ft target_segs regs3 0x10012e0 tfmem arom _ 12 0 _
                 TF_10012e0 eq_refl TD_10012e0).
      - wlits. reflexivity.
      - unfold regs3, regs2. getr_resolve. exact c_eq_0_true. }
    exists regs3. split; [|split].
    + intros r H11 H12. unfold regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs3. rewrite regupd_same.
      rewrite Hj. apply ntw_S.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      apply mst_refl.
  - (* j < nk: nonzero byte, loop *)
    assert (Hjlt : (j < nk)%nat) by lia.
    set (b := byte_at (nth k av []) j).
    assert (Hbnz : b <> Z_to_bv 8 0) by (apply byte_at_nz; assumption).
    set (regs1 := regupd regs 12 (tsptr k + nat_to_word j)).
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x10012d4 tfmem arom)
                 = MachineOk (mkst regs1 0x10012d8 tfmem arom)).
    { eapply eq_trans;
      [ apply (step_add_at target_segs regs 0x10012d4 tfmem arom _ 12 10 11
                 (tsptr k + nat_to_word j) TF_10012d4 eq_refl TD_10012d4 eq_refl);
        getr_resolve; rewrite Hr10, Hr11; rewrite v_add_word; reflexivity
      | wlits; reflexivity ]. }
    set (regs2 := regupd regs1 12 (Z_to_bv 64 (bv_unsigned b))).
    assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x10012d8 tfmem arom)
                 = MachineOk (mkst regs2 0x10012dc tfmem arom)).
    { rewrite (step_lbu target_segs regs1 0x10012d8 tfmem arom _ 12 12 _ b
                 TF_10012d8 eq_refl TD_10012d8).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite v_addi_0.
        unfold b. apply tread_arg_byte; [exact Hk | unfold nk in *; lia]. }
    set (regs3 := regupd regs2 11 (nat_to_word (S j))).
    assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x10012dc tfmem arom)
                 = MachineOk (mkst regs3 0x10012e0 tfmem arom)).
    { eapply eq_trans;
      [ apply (step_addi_at target_segs regs2 0x10012dc tfmem arom _ 11 11 _
                 (nat_to_word (S j)) TF_10012dc eq_refl TD_10012dc eq_refl);
        unfold regs2, regs1; getr_resolve; rewrite Hr11;
        apply v_addi_Sj; lia
      | wlits; reflexivity ]. }
    assert (E4 : RiscvSemantics.step target_segs (mkst regs3 0x10012e0 tfmem arom)
                 = MachineOk (mkst regs3 0x10012d4 tfmem arom)).
    { rewrite (step_bne_tk target_segs regs3 0x10012e0 tfmem arom _ 12 0 _
                 TF_10012e0 eq_refl TD_10012e0).
      - wlits. reflexivity.
      - unfold regs3, regs2. getr_resolve.
        apply c_eq_0_false. rewrite u_zext8. apply byte_nz_u. exact Hbnz. }
    assert (Hr10' : reg_get regs3 10 = tsptr k).
    { unfold regs3, regs2, regs1. regupd_resolve. exact Hr10. }
    assert (Hr11' : reg_get regs3 11 = nat_to_word (S j)).
    { unfold regs3. apply regupd_same. }
    destruct (IH (S j) regs3 ltac:(lia) Hr10' Hr11') as [regs' [Hag [H11 Hms]]].
    exists regs'. split; [|split].
    + intros r H11' H12'. rewrite (Hag r H11' H12').
      unfold regs3, regs2, regs1. rewrite !regupd_other by assumption.
      reflexivity.
    + exact H11.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      exact Hms.
Qed.

(* ================================================================= *)
(* Outer length loop: 0x10011bc .. 0x10011e0                          *)
(* ================================================================= *)

Lemma target_length : forall f i regs,
  (1 <= i)%nat -> (i < length av)%nat -> (length av - i <= f)%nat ->
  reg_get regs 9 = targcN ->
  reg_get regs 18 = nat_to_word (pbJ i) ->
  reg_get regs 19 = Z_to_bv 64 (bv_unsigned asp + 8 + 8 * Z.of_nat i) ->
  reg_get regs 20 = nat_to_word i ->
  exists regs',
    (forall r : reg, r <> 1 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 18 ->
       r <> 19 -> r <> 20 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 18 = nat_to_word (ttotn - 1) /\
    msteps target_segs (mkst regs 0x10011bc tfmem arom)
                       (mkst regs' 0x10011e4 tfmem arom).
Proof.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as HargcLe.
  pose proof ttotn_bound as Htb. pose proof ttotn_ge1 as Htg1.
  induction f as [|f IH]; intros i regs H1 Hi Hf H9 H18 H19 H20; [lia|].
  assert (HiZ : (Z.of_nat i <= 1024)%Z) by (apply tiN_le; lia).
  assert (HSiZ : (Z.of_nat (S i) <= 1024)%Z) by (apply tiN_le; lia).
  assert (HniB : (Z.of_nat (length (nth i av [])) <= 131071)%Z)
    by (apply valid_argv_str_len; [exact Hva | lia]).
  assert (HpbLe : (pbJ i <= ttotn - 1)%nat) by apply pbJ_le.
  assert (HpbLeS : (pbJ (S i) <= ttotn - 1)%nat) by apply pbJ_le.
  destruct (tsptr_bounds i ltac:(lia)) as [Hptrlo Hptrhi].
  (* ld a0,0(s3) : a0 = tsptr i *)
  set (regs1 := regupd regs 10 (tsptr i)).
  assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x10011bc tfmem arom)
               = MachineOk (mkst regs1 0x10011c0 tfmem arom)).
  { rewrite (step_ld target_segs regs 0x10011bc tfmem arom _ 10 19 _
               (word_le8 (tsptr i)) (tsptr i) TF_10011bc eq_refl TD_10011bc).
    - reduce_bv_eqb_ifs. wlits. reflexivity.
    - getr_resolve. rewrite H19. rewrite v_addi_0.
      apply tread_arg_ptr. lia.
    - exact (bytes_le_n_to_le_8 _). }
  (* auipc ra,0 : ra = 0x10011c0 *)
  set (regs2 := regupd regs1 1 (0x10011c0 : word)).
  assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x10011c0 tfmem arom)
               = MachineOk (mkst regs2 0x10011c4 tfmem arom)).
  { eapply eq_trans;
    [ apply (step_auipc_at target_segs regs1 0x10011c0 tfmem arom _ 1 _
               (0x10011c0 : word) TF_10011c0 eq_refl TD_10011c0 eq_refl);
      bveq
    | wlits; reflexivity ]. }
  (* jalr ra,272(ra) -> slen (0x10012d0), ra = 0x10011c8 *)
  set (regs3 := regupd regs2 1 (0x10011c8 : word)).
  assert (E3 : RiscvSemantics.step target_segs (mkst regs2 0x10011c4 tfmem arom)
               = MachineOk (mkst regs3 0x10012d0 tfmem arom)).
  { eapply eq_trans;
    [ apply (step_jalr_link target_segs regs2 0x10011c4 tfmem arom _ 1 1 _
               (0x10011c0 : word) TF_10011c4 eq_refl TD_10011c4 eq_refl);
      unfold regs2; getr_resolve; reflexivity
    | wlits; reflexivity ]. }
  (* slen: li a1,0 *)
  set (regs4 := regupd regs3 11 (Z_to_bv 64 0)).
  assert (E4 : RiscvSemantics.step target_segs (mkst regs3 0x10012d0 tfmem arom)
               = MachineOk (mkst regs4 0x10012d4 tfmem arom)).
  { rewrite (step_addi target_segs regs3 0x10012d0 tfmem arom _ 11 0 _
               TF_10012d0 eq_refl TD_10012d0).
    reduce_bv_eqb_ifs. getr_resolve. rewrite v_addi_0. wlits. reflexivity. }
  (* the slen loop *)
  destruct (target_slen i ltac:(lia) (length (nth i av [])) O regs4
              ltac:(lia)
              ltac:(unfold regs4, regs3, regs2; regupd_resolve;
                    unfold regs1; apply regupd_same)
              ltac:(unfold regs4; rewrite regupd_same; reflexivity))
    as (regs5 & Hag5 & H11_5 & Hms5).
  assert (H1_5 : reg_get regs5 1 = (0x10011c8 : word)).
  { rewrite (Hag5 1 ltac:(reg_neq_tac) ltac:(reg_neq_tac)).
    unfold regs4. rewrite regupd_other by reg_neq_tac.
    unfold regs3. apply regupd_same. }
  (* addi a0,a1,-1 : a0 = len *)
  set (regs6 := regupd regs5 10 (nat_to_word (length (nth i av [])))).
  assert (E6 : RiscvSemantics.step target_segs (mkst regs5 0x10012e4 tfmem arom)
               = MachineOk (mkst regs6 0x10012e8 tfmem arom)).
  { eapply eq_trans;
    [ apply (step_addi_at target_segs regs5 0x10012e4 tfmem arom _ 10 11 _
               (nat_to_word (length (nth i av []))) TF_10012e4 eq_refl TD_10012e4 eq_refl);
      getr_resolve; rewrite H11_5; apply v_addi_pred
    | wlits; reflexivity ]. }
  (* ret -> 0x10011c8 *)
  assert (E7 : RiscvSemantics.step target_segs (mkst regs6 0x10012e8 tfmem arom)
               = MachineOk (mkst regs6 0x10011c8 tfmem arom)).
  { eapply eq_trans;
    [ apply (step_jalr_x0 target_segs regs6 0x10012e8 tfmem arom _ 1 _
               (0x10011c8 : word) TF_10012e8 eq_refl TD_10012e8);
      unfold regs6; getr_resolve; exact H1_5
    | wlits; reflexivity ]. }
  assert (H20_6 : reg_get regs6 20 = nat_to_word i).
  { unfold regs6. rewrite regupd_other by reg_neq_tac.
    rewrite (Hag5 20 ltac:(reg_neq_tac) ltac:(reg_neq_tac)).
    unfold regs4, regs3, regs2, regs1.
    rewrite !regupd_other by reg_neq_tac. exact H20. }
  assert (H18_6 : reg_get regs6 18 = nat_to_word (pbJ i)).
  { unfold regs6. rewrite regupd_other by reg_neq_tac.
    rewrite (Hag5 18 ltac:(reg_neq_tac) ltac:(reg_neq_tac)).
    unfold regs4, regs3, regs2, regs1.
    rewrite !regupd_other by reg_neq_tac. exact H18. }
  (* sltiu a1,s4,2 *)
  set (regs7 := regupd regs6 11
        (if (Z.of_nat i <? 2)%Z then Z_to_bv 64 1 else Z_to_bv 64 0)).
  assert (E8 : RiscvSemantics.step target_segs (mkst regs6 0x10011c8 tfmem arom)
               = MachineOk (mkst regs7 0x10011cc tfmem arom)).
  { eapply eq_trans;
    [ apply (step_sltiu_at target_segs regs6 0x10011c8 tfmem arom _ 11 20 _
               (if (Z.of_nat i <? 2)%Z then Z_to_bv 64 1 else Z_to_bv 64 0)
               TF_10011c8 eq_refl TD_10011c8 eq_refl);
      getr_resolve; rewrite H20_6; imm_norm; rewrite v_sltiu_2;
      rewrite u_ntw by lia; reflexivity
    | wlits; reflexivity ]. }
  (* addi s4,s4,1 : i+1 *)
  set (regs8 := regupd regs7 20 (nat_to_word (S i))).
  assert (E9 : RiscvSemantics.step target_segs (mkst regs7 0x10011cc tfmem arom)
               = MachineOk (mkst regs8 0x10011d0 tfmem arom)).
  { eapply eq_trans;
    [ apply (step_addi_at target_segs regs7 0x10011cc tfmem arom _ 20 20 _
               (nat_to_word (S i)) TF_10011cc eq_refl TD_10011cc eq_refl);
      unfold regs7; getr_resolve; rewrite H20_6;
      apply v_addi_Sj; lia
    | wlits; reflexivity ]. }
  (* xori a1,a1,1 : sep *)
  set (sep := if Nat.eqb i 1 then 0%nat else 1%nat).
  set (regs9 := regupd regs8 11 (nat_to_word sep)).
  assert (E10 : RiscvSemantics.step target_segs (mkst regs8 0x10011d0 tfmem arom)
                = MachineOk (mkst regs9 0x10011d4 tfmem arom)).
  { eapply eq_trans;
    [ apply (step_xori_at target_segs regs8 0x10011d0 tfmem arom _ 11 11 _
               (nat_to_word sep) TF_10011d0 eq_refl TD_10011d0 eq_refl);
      unfold regs8, regs7; getr_resolve;
      unfold sep; destruct (Nat.eqb i 1) eqn:Ei;
      [ apply Nat.eqb_eq in Ei;
        replace ((Z.of_nat i <? 2)%Z) with true
          by (symmetry; apply Z.ltb_lt; lia);
        apply v_xori_1_1
      | apply Nat.eqb_neq in Ei;
        replace ((Z.of_nat i <? 2)%Z) with false
          by (symmetry; apply Z.ltb_ge; lia);
        apply v_xori_0_1 ]
    | wlits; reflexivity ]. }
  assert (Hsep1 : (sep <= 1)%nat) by (unfold sep; destruct (Nat.eqb i 1); lia).
  (* add a1,s2,a1 : pbJ i + sep *)
  set (regsA := regupd regs9 11 (nat_to_word (pbJ i + sep))).
  assert (EA : RiscvSemantics.step target_segs (mkst regs9 0x10011d4 tfmem arom)
               = MachineOk (mkst regsA 0x10011d8 tfmem arom)).
  { eapply eq_trans;
    [ apply (step_add_at target_segs regs9 0x10011d4 tfmem arom _ 11 18 11
               (nat_to_word (pbJ i + sep)) TF_10011d4 eq_refl TD_10011d4 eq_refl);
      unfold regs9, regs8, regs7; getr_resolve; rewrite H18_6;
      rewrite v_add_word; apply nat_to_word_merge
    | wlits; reflexivity ]. }
  (* add s2,a1,a0 : pbJ (S i) *)
  set (regsB := regupd regsA 18 (nat_to_word (pbJ (S i)))).
  assert (EB : RiscvSemantics.step target_segs (mkst regsA 0x10011d8 tfmem arom)
               = MachineOk (mkst regsB 0x10011dc tfmem arom)).
  { eapply eq_trans;
    [ apply (step_add_at target_segs regsA 0x10011d8 tfmem arom _ 18 11 10
               (nat_to_word (pbJ (S i))) TF_10011d8 eq_refl TD_10011d8 eq_refl);
      unfold regsA, regs9, regs8, regs7, regs6; getr_resolve;
      rewrite v_add_word; rewrite nat_to_word_merge;
      f_equal; rewrite (pbJ_stepN i H1 Hi); unfold sep;
      destruct (Nat.eqb i 1); lia
    | wlits; reflexivity ]. }
  (* addi s3,s3,8 *)
  set (regsC := regupd regsB 19
        (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * Z.of_nat (S i)))).
  assert (EC : RiscvSemantics.step target_segs (mkst regsB 0x10011dc tfmem arom)
               = MachineOk (mkst regsC 0x10011e0 tfmem arom)).
  { eapply eq_trans;
    [ apply (step_addi_at target_segs regsB 0x10011dc tfmem arom _ 19 19 _
               (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * Z.of_nat (S i)))
               TF_10011dc eq_refl TD_10011dc eq_refl);
      unfold regsB, regsA, regs9, regs8, regs7, regs6; getr_resolve;
      rewrite (Hag5 19 ltac:(reg_neq_tac) ltac:(reg_neq_tac));
      unfold regs4, regs3, regs2, regs1;
      rewrite !regupd_other by reg_neq_tac;
      rewrite H19; sp_norm; f_equal; lia
    | wlits; reflexivity ]. }
  assert (H20C : reg_get regsC 20 = nat_to_word (S i)).
  { unfold regsC, regsB, regsA, regs9.
    rewrite !regupd_other by reg_neq_tac.
    unfold regs8. apply regupd_same. }
  assert (H9C : reg_get regsC 9 = targcN).
  { unfold regsC, regsB, regsA, regs9, regs8, regs7, regs6.
    rewrite !regupd_other by reg_neq_tac.
    rewrite (Hag5 9 ltac:(reg_neq_tac) ltac:(reg_neq_tac)).
    unfold regs4, regs3, regs2, regs1.
    rewrite !regupd_other by reg_neq_tac. exact H9. }
  assert (H18C : reg_get regsC 18 = nat_to_word (pbJ (S i))).
  { unfold regsC. rewrite regupd_other by reg_neq_tac.
    unfold regsB. apply regupd_same. }
  assert (H19C : reg_get regsC 19
                 = Z_to_bv 64 (bv_unsigned asp + 8 + 8 * Z.of_nat (S i)))
    by (unfold regsC; apply regupd_same).
  destruct (lt_dec (S i) (length av)) as [Hlti | Hge].
  - (* bne s1,s4 taken: loop again *)
    assert (ED : RiscvSemantics.step target_segs (mkst regsC 0x10011e0 tfmem arom)
                 = MachineOk (mkst regsC 0x10011bc tfmem arom)).
    { rewrite (step_bne_tk target_segs regsC 0x10011e0 tfmem arom _ 9 20 _
                 TF_10011e0 eq_refl TD_10011e0).
      - wlits. reflexivity.
      - getr_resolve. rewrite H9C, H20C.
        apply c_eq_neq. rewrite u_targcN. rewrite u_ntw by lia. lia. }
    destruct (IH (S i) regsC ltac:(lia) Hlti ltac:(lia) H9C H18C H19C H20C)
      as (regs' & Hag' & H18' & Hms').
    exists regs'. split; [| split].
    + intros r Hx1 Hx10 Hx11 Hx12 Hx18 Hx19 Hx20.
      rewrite (Hag' r Hx1 Hx10 Hx11 Hx12 Hx18 Hx19 Hx20).
      unfold regsC, regsB, regsA, regs9, regs8, regs7, regs6.
      rewrite !regupd_other by assumption.
      rewrite (Hag5 r Hx11 Hx12).
      unfold regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + exact H18'.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply msteps_trans; [exact Hms5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      eapply mst_step; [reflexivity | exact E7 |].
      eapply mst_step; [reflexivity | exact E8 |].
      eapply mst_step; [reflexivity | exact E9 |].
      eapply mst_step; [reflexivity | exact E10 |].
      eapply mst_step; [reflexivity | exact EA |].
      eapply mst_step; [reflexivity | exact EB |].
      eapply mst_step; [reflexivity | exact EC |].
      eapply mst_step; [reflexivity | exact ED |].
      exact Hms'.
  - (* bne fall-through: i+1 = argc, done *)
    assert (HSieq : (S i = length av)%nat) by lia.
    assert (ED : RiscvSemantics.step target_segs (mkst regsC 0x10011e0 tfmem arom)
                 = MachineOk (mkst regsC 0x10011e4 tfmem arom)).
    { rewrite (step_bne_ft target_segs regsC 0x10011e0 tfmem arom _ 9 20 _
                 TF_10011e0 eq_refl TD_10011e0).
      - wlits. reflexivity.
      - getr_resolve. rewrite H9C, H20C.
        unfold targcN, len_word, nat_to_word. rewrite HSieq.
        apply c_eq_refl. }
    exists regsC. split; [| split].
    + intros r Hx1 Hx10 Hx11 Hx12 Hx18 Hx19 Hx20.
      unfold regsC, regsB, regsA, regs9, regs8, regs7, regs6.
      rewrite !regupd_other by assumption.
      rewrite (Hag5 r Hx11 Hx12).
      unfold regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + rewrite H18C. rewrite HSieq. rewrite pbJ_last. reflexivity.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply msteps_trans; [exact Hms5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      eapply mst_step; [reflexivity | exact E7 |].
      eapply mst_step; [reflexivity | exact E8 |].
      eapply mst_step; [reflexivity | exact E9 |].
      eapply mst_step; [reflexivity | exact E10 |].
      eapply mst_step; [reflexivity | exact EA |].
      eapply mst_step; [reflexivity | exact EB |].
      eapply mst_step; [reflexivity | exact EC |].
      eapply mst_step; [reflexivity | exact ED |].
      apply mst_refl.
Qed.

(* ================================================================= *)
(* From entry to 0x10011e4 (post length loop)                         *)
(* ================================================================= *)

Lemma target_after_length :
  exists regsA,
    reg_get regsA 2 = Z_to_bv 64 (bv_unsigned asp - 64) /\
    reg_get regsA 8 = Z_to_bv 64 (bv_unsigned asp + 8) /\
    reg_get regsA 9 = targcN /\
    reg_get regsA 18 = nat_to_word (ttotn - 1) /\
    msteps target_segs
      (init_machine_state (run_segments target_segs inp asp amb) 0x1001158 target_phdrs asp amb arnd inp)
      (mkst regsA 0x10011e4 tfmem arom).
(** SIX instructions in ONE reflective block: the [argc >= 2]
    fall-through and the five register initializations the length loop
    runs on (including the [argc <> 1] test that the dispatch's
    [bltu] has already made dead).  Two branches, no memory. *)
Proof.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as HA.
  pose proof u_targcN as Hu.
  destruct target_to_dispatch as (regsP & P2 & P8 & P10 & P11 & HmsP).
  replace (0x10011a4 : word) with (Z_to_bv 64 0x10011a4) in HmsP by bveq.
  sym_block_ex target_segs (mkst regsP (Z_to_bv 64 0x10011a4) tfmem arom)
    6%nat [false; false] (@nil expr)
    [((10 : reg), EVar 32); ((11 : reg), ELit 2); ((8 : reg), EVar 33)]
    [targcN; Z_to_bv 64 (bv_unsigned asp + 8)] (@nil word) RA HRA Hms.
  { (* [beq a0,s4] at 0x10011b8 -> not taken, because [argc <> 1] *)
    rewrite bv_eqb_Z; apply Z.eqb_neq; u_norm; lia. }
  { (* [bltu a0,a1] at 0x10011a4 -> not taken, because [argc >= 2] *)
    unfold bv_ltu; apply Z.ltb_ge; u_norm; lia. }
  { (* the [a0] pin *) exact P10. }
  { (* the [a1] pin *) exact P11. }
  { (* the [s0] pin *) exact P8. }
  assert (H9_4 : reg_get RA 9 = targcN) by (sym_regs HRA; sym_close).
  assert (H18_4 : reg_get RA 18 = nat_to_word (pbJ 1))
    by (rewrite pbJ_1; sym_regs HRA; sym_close).
  assert (H19_4 : reg_get RA 19
                  = Z_to_bv 64 (bv_unsigned asp + 8 + 8 * Z.of_nat 1))
    by (sym_regs HRA; sym_close).
  assert (H20_4 : reg_get RA 20 = nat_to_word 1) by (sym_regs HRA; sym_close).
  destruct (target_length (length av) 1 RA ltac:(lia) ltac:(lia) ltac:(lia)
              H9_4 H18_4 H19_4 H20_4)
    as (regsL & HagL & H18L & HmsL).
  exists regsL. refine (conj _ (conj _ (conj _ (conj _ _)))).
  - rewrite (HagL 2) by reg_neq_tac. sym_regs HRA. exact P2.
  - rewrite (HagL 8) by reg_neq_tac. sym_regs HRA. sym_close.
  - rewrite (HagL 9) by reg_neq_tac. exact H9_4.
  - exact H18L.
  - eapply msteps_trans; [exact HmsP|].
    eapply msteps_trans; [exact Hms|].
    replace (0x10011bc : word) with (Z_to_bv 64 0x10011bc) in HmsL by bveq.
    exact HmsL.
Qed.

(* ================================================================= *)
(* tot > 65536: no output, exit 3                                     *)
(* ================================================================= *)

Lemma target_wexit_cap : (65536 < bv_unsigned ttot)%Z ->
  to_wexit target_segs
    (init_machine_state (run_segments target_segs inp asp amb) 0x1001158 target_phdrs asp amb arnd inp)
    [] (Z_to_bv 64 3).
(** FIVE instructions in ONE reflective block: the [tot > 65536] test
    and the [j] onto the shared "return this code" tail.  One pinned
    register and one obligation, the [beq]. *)
Proof.
  intros Hcap.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof ttotn_ge1 as Htg1. pose proof ttotn_bound as Htb.
  rewrite u_ttot in Hcap.
  destruct target_after_length as (regsA & A2 & A8 & A9 & A18 & HmsA).
  eapply msteps_to_wexit; [exact HmsA|].
  sym_block target_segs 5%nat [false] (@nil expr)
    [((18 : reg), EVar 32)] [nat_to_word (ttotn - 1)] (@nil word) RA HRA.
  { (* [beq a0,x0] at 0x10011e8 -> not taken, because [tot > 65536] *)
    rewrite v_srl_16, bv_eqb_Z; apply Z.eqb_neq;
    rewrite v_srli_div by lia; rewrite u_ntw by lia; u_norm;
    change (2^16)%Z with 65536%Z;
    assert (Hq : (0 < Z.of_nat (ttotn - 1) / 65536)%Z)
      by (apply Z.div_str_pos; lia);
    lia. }
  { (* the [s2] pin *) exact A18. }
  (* epilogue with a0 = 3 *)
  lazymatch goal with
  | |- to_wexit _ (mkst ?R _ _ _) _ _ =>
    edestruct (target_epilogue R tfmem (Z_to_bv 64 3)) as [regsE [HE17 [HE10 HmsE]]]
  end.
  - sym_regs HRA. exact A2.
  - sym_regs HRA. sym_close.
  - exact tfread_slot_ra.
  - exact tfread_slot_s0.
  - exact tfread_slot_0.
  - eapply msteps_to_wexit; [exact HmsE|].
    apply tw_exit_coden;
      [exact HE17 | exact HE10 | vm_compute; reflexivity].
Qed.

(* ================================================================= *)
(* tot <= 65536: run to the mmap ecall                                *)
(* ================================================================= *)

Lemma target_to_mmap : (bv_unsigned ttot <= 65536)%Z ->
  exists regsE,
    reg_get regsE 2 = Z_to_bv 64 (bv_unsigned asp - 64) /\
    reg_get regsE 8 = Z_to_bv 64 (bv_unsigned asp + 8) /\
    reg_get regsE 9 = targcN /\
    reg_get regsE 11 = ttot /\
    reg_get regsE 12 = Z_to_bv 64 3 /\
    reg_get regsE 13 = Z_to_bv 64 34 /\
    reg_get regsE 14 = Z_to_bv 64 (2^64 - 1) /\
    reg_get regsE 15 = Z_to_bv 64 0 /\
    reg_get regsE 10 = Z_to_bv 64 0 /\
    bv_unsigned (getr regsE 17) = 222%Z /\
    msteps target_segs
      (init_machine_state (run_segments target_segs inp asp amb) 0x1001158 target_phdrs asp amb arnd inp)
      {| ms_regs := regsE; ms_fregs := fp_regs; ms_pc_val := 0x100120c;
         ms_svc_pending := Some (getr regsE 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := tfmem; ms_rom := arom |}.
(** EIGHT instructions in ONE reflective block, with no memory
    traffic: the [tot <= 65536] test (a shift and a [beq]), the
    [+1] that turns the accumulated separator count into [tot], and the
    six mmap arguments, stopping at the [ecall] that is the [tmw]
    branch point.  One pinned register ([s2], the accumulator) and one
    obligation (the [beq]).  The address argument [a0] is the shift's
    result, zero on this path. *)
Proof.
  intros Hcap.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof ttotn_ge1 as Htg1. pose proof ttotn_bound as Htb.
  rewrite u_ttot in Hcap.
  destruct target_after_length as (regsA & A2 & A8 & A9 & A18 & HmsA).
  (* the executor's spelling of [addi a1,s2,1] *)
  assert (Httv : Z_to_bv 64 (bv_unsigned (nat_to_word (ttotn - 1)) + 1) = ttot).
  { change (Z_to_bv 64 (bv_unsigned (nat_to_word (ttotn - 1)) + 1))
      with (v_addi (nat_to_word (ttotn - 1)) 1).
    rewrite v_addi_Sj by lia. unfold ttot. f_equal. lia. }
  replace (0x10011e4 : word) with (Z_to_bv 64 0x10011e4) in HmsA by bveq.
  sym_block_ex target_segs (mkst regsA (Z_to_bv 64 0x10011e4) tfmem arom)
    8%nat [true] (@nil expr)
    [((18 : reg), EVar 32)] [nat_to_word (ttotn - 1)] (@nil word) RA HRA Hms.
  { (* [beq a0,x0] at 0x10011e8 -> taken, because [tot <= 65536] *)
    rewrite v_srl_16, bv_eqb_Z; apply Z.eqb_eq;
    rewrite v_srli_div by lia; rewrite u_ntw by lia; u_norm;
    change (2^16)%Z with 65536%Z; apply Z.div_small; lia. }
  { (* the [s2] pin *) exact A18. }
  exists RA.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ _)))))))))).
  1-10: (sym_regs HRA;
        first [ reflexivity | assumption | exact Httv
              | (f_equal; lia) | (apply bv_eq; u_norm; lia)
              | (* a0: [(tot - 1) >> 16], zero because [tot <= 65536];
                   no raw [vm_compute] on an open bv term *)
                (rewrite ?v_srl_16; apply bv_eq; rewrite v_srli_div by lia;
                 rewrite u_ntw by lia; u_norm; change (2^16)%Z with 65536%Z;
                 apply Z.div_small; lia)
              | bveq ]).
  eapply msteps_trans; [ exact HmsA | ].
  eapply msteps_trans; [ exact Hms | ]. norm_pc; sym_pc_lit.
  eapply mst_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ TF_100120c eq_refl)
    | apply mst_refl ].
Qed.

(* ================================================================= *)
(* Failure continuation: exit 4                                       *)
(* ================================================================= *)

Lemma target_fail_twm : forall model regs (e : Z),
  (1 <= e)%Z -> (e <= 4095)%Z ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64) ->
  twm target_segs (mkst (regupd regs 10 (errno_ret e)) 0x1001210 tfmem arom)
      model [] (Z_to_bv 64 4).
Proof.
  intros model regs e He1 He2 Hr2.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  (* blt a0,x0 taken -> 0x10012a0 *)
  eapply twm_step;
    [ reflexivity
    | eapply step_blt_tk;
      [ exact TF_1001210 | reflexivity | exact TD_1001210
      | getr_resolve; regupd_resolve; apply c_lts_errno; assumption ]
    | norm_pc ].
  (* li a1,4 *)
  eapply twm_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 4);
      [ exact TF_10012a0 | reflexivity | exact TD_10012a0 | reflexivity
      | getr_resolve; bveq ]
    | step_simpl ].
  (* j 0x10012ac *)
  stepj TF_10012a4 TD_10012a4.
  (* mv a0,a1 -> 4 *)
  eapply twm_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 4);
      [ exact TF_10012ac | reflexivity | exact TD_10012ac | reflexivity
      | getr_resolve; regupd_resolve; apply v_addi_0 ]
    | step_simpl ].
  (* epilogue with a0 = 4 *)
  lazymatch goal with
  | |- twm _ (mkst ?R _ _ _) _ _ _ =>
    edestruct (target_epilogue R tfmem (Z_to_bv 64 4)) as [regsE [HE17 [HE10 HmsE]]]
  end.
  - regupd_resolve. exact Hr2.
  - regupd_resolve. reflexivity.
  - exact tfread_slot_ra.
  - exact tfread_slot_s0.
  - exact tfread_slot_0.
  - eapply msteps_twm; [exact HmsE|].
    apply twm_exit_coden;
      [exact HE17 | exact HE10 | vm_compute; reflexivity].
Qed.

(* ================================================================= *)
(* Success continuation                                               *)
(* ================================================================= *)

Section TargetSucc.

Variable aG gz : word.
Hypothesis HaPos : (0 < bv_unsigned aG)%Z.
Hypothesis Hgz_lo : (bv_unsigned ttot <= bv_unsigned gz)%Z.
Hypothesis HaCeil : (bv_unsigned aG + bv_unsigned gz <= bv_unsigned asp - stack_max_size)%Z.
Hypothesis Hda : ((bv_unsigned aG + bv_unsigned gz <= 0x1000000)%Z
                  \/ (0x1001000 <= bv_unsigned aG)%Z).
Hypothesis Hdb : ((bv_unsigned aG + bv_unsigned gz <= 0x1001000)%Z
                  \/ (0x1002000 <= bv_unsigned aG)%Z).

Definition zmemT : word -> option byte := zfill aG gz tfmem.

(** The grant is zero-mapped ([zmemT] = [zfill aG gz _]), so every byte
    of [aG, aG+gz) is writable whatever sits underneath — which is what
    a machine store into the joined buffer now has to show. *)
Lemma tgrant_store_ok : forall (m : word -> option byte) (a : word) (k : nat),
  (bv_unsigned aG <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= bv_unsigned aG + bv_unsigned gz)%Z ->
  store_ok target_segs (zmem m aG gz) a k = true.
Proof.
  intros m a k Hx1 Hx2. apply store_ok_zmem; [|exact Hx1|exact Hx2].
  pose proof HaCeil. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms. lia.
Qed.

(* ----------------------------------------------------------------- *)
(* Inner byte-copy loop: 0x1001248 .. 0x1001260                       *)
(* ----------------------------------------------------------------- *)

Lemma target_copy_inner : forall (p : word) (s pre : list byte),
  ~ In (Z_to_bv 8 0) s ->
  (length pre + length s + 1 <= ttotn)%nat ->
  (bv_unsigned asp <= bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length s) + 1 < 2^64)%Z ->
  (forall j, (j <= length s)%nat ->
     rdn target_segs tfmem (p + nat_to_word j) 1%nat = Some [byte_at s j]) ->
  forall d j regs,
  (j + d = length s)%nat ->
  reg_get regs 11 = aG ->
  reg_get regs 12 = nat_to_word (length pre + j) ->
  reg_get regs 15 = p + nat_to_word j ->
  exists regs',
    (forall r : reg, r <> 12 -> r <> 15 -> r <> 16 -> r <> 17 ->
       reg_get regs' r = reg_get regs r) /\
    reg_get regs' 12 = nat_to_word (length pre + length s) /\
    msteps target_segs
      (mkst regs 0x1001248 (wbytes zmemT aG (pre ++ firstn j s)) arom)
      (mkst regs' 0x1001264 (wbytes zmemT aG (pre ++ s)) arom).
Proof.
  intros p s pre Hnz Hpsb Hp Hpbnd Hrd.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof ttotn_ge1 as Htg1. pose proof ttotn_bound as Htb.
  pose proof (u64_range aG) as HuaG. pose proof (u64_range gz) as Hugz.
  assert (Hgzn : (Z.of_nat ttotn <= bv_unsigned gz)%Z)
    by (rewrite <- u_ttot; exact Hgz_lo).
  set (lp := length pre) in *.
  set (ls := length s) in *.
  induction d as [|d IH]; intros j regs Hjd H11 H12 H15.
  - (* j = length s: NUL byte, exit to 0x1001264 *)
    assert (Hj : j = ls) by lia.
    set (M := wbytes zmemT aG (pre ++ firstn j s)).
    assert (HlenF : (length (pre ++ firstn j s) = lp + j)%nat)
      by (rewrite length_app, firstn_length_le by lia; reflexivity).
    set (regs1 := regupd regs 16 (Z_to_bv 64 0)).
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001248 M arom)
                 = MachineOk (mkst regs1 0x100124c M arom)).
    { rewrite (step_lbu target_segs regs 0x1001248 M arom _ 16 15 _ (Z_to_bv 8 0)
                 TF_1001248 eq_refl TD_1001248).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - getr_resolve. rewrite H15. rewrite v_addi_0.
        unfold M. rewrite rdn_wbytes_disjoint
          by (rewrite ?HlenF, ?word_add_nat; u_norm; lia).
        unfold zmemT. rewrite rdn_zfill_out
          by (rewrite ?word_add_nat; u_norm; try (right); lia).
        pose proof (Hrd j ltac:(lia)) as Hrdj.
        assert (Hb0 : byte_at s j = Z_to_bv 8 0).
        { unfold ls in Hj. rewrite Hj. apply byte_at_len. }
        rewrite Hb0 in Hrdj. exact Hrdj. }
    assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x100124c M arom)
                 = MachineOk (mkst regs1 0x1001264 M arom)).
    { rewrite (step_beq_tk target_segs regs1 0x100124c M arom _ 16 0 _
                 TF_100124c eq_refl TD_100124c).
      - wlits. reflexivity.
      - unfold regs1. getr_resolve. exact c_eq_0_true. }
    exists regs1. split; [|split].
    + intros r Hx12 Hx15 Hx16 Hx17. unfold regs1.
      rewrite regupd_other by assumption. reflexivity.
    + unfold regs1. rewrite regupd_other by reg_neq_tac.
      rewrite H12. unfold ls in Hj. rewrite Hj. reflexivity.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      unfold M.
      replace (firstn j s) with s by (rewrite Hj; symmetry; apply firstn_all).
      apply mst_refl.
  - (* j < length s: store byte, loop *)
    assert (Hjlt : (j < ls)%nat) by lia.
    set (b := byte_at s j).
    assert (Hbnz : b <> Z_to_bv 8 0) by (apply byte_at_nz; assumption).
    set (M := wbytes zmemT aG (pre ++ firstn j s)).
    assert (HlenF : (length (pre ++ firstn j s) = lp + j)%nat)
      by (rewrite length_app, firstn_length_le by lia; reflexivity).
    set (regs1 := regupd regs 16 (Z_to_bv 64 (bv_unsigned b))).
    assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001248 M arom)
                 = MachineOk (mkst regs1 0x100124c M arom)).
    { rewrite (step_lbu target_segs regs 0x1001248 M arom _ 16 15 _ b
                 TF_1001248 eq_refl TD_1001248).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - getr_resolve. rewrite H15. rewrite v_addi_0.
        unfold M. rewrite rdn_wbytes_disjoint
          by (rewrite ?HlenF, ?word_add_nat; u_norm; lia).
        unfold zmemT. rewrite rdn_zfill_out
          by (rewrite ?word_add_nat; u_norm; try (right); lia).
        unfold b. apply Hrd. lia. }
    assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x100124c M arom)
                 = MachineOk (mkst regs1 0x1001250 M arom)).
    { rewrite (step_beq_ft target_segs regs1 0x100124c M arom _ 16 0 _
                 TF_100124c eq_refl TD_100124c).
      - wlits. reflexivity.
      - unfold regs1. getr_resolve.
        apply c_eq_0_false. rewrite u_zext8. apply byte_nz_u. exact Hbnz. }
    (* add a7,a1,a2 : dest = aG + lp + j *)
    set (regs2 := regupd regs1 17 (aG + nat_to_word (lp + j))).
    assert (E3 : RiscvSemantics.step target_segs (mkst regs1 0x1001250 M arom)
                 = MachineOk (mkst regs2 0x1001254 M arom)).
    { eapply eq_trans;
      [ apply (step_add_at target_segs regs1 0x1001250 M arom _ 17 11 12
                 (aG + nat_to_word (lp + j)) TF_1001250 eq_refl TD_1001250 eq_refl);
        unfold regs1; getr_resolve; rewrite H11, H12;
        rewrite v_add_word; reflexivity
      | wlits; reflexivity ]. }
    (* addi a2,a2,1 *)
    set (regs3 := regupd regs2 12 (nat_to_word (lp + S j))).
    assert (E4 : RiscvSemantics.step target_segs (mkst regs2 0x1001254 M arom)
                 = MachineOk (mkst regs3 0x1001258 M arom)).
    { eapply eq_trans;
      [ apply (step_addi_at target_segs regs2 0x1001254 M arom _ 12 12 _
                 (nat_to_word (lp + S j)) TF_1001254 eq_refl TD_1001254 eq_refl);
        unfold regs2, regs1; getr_resolve; rewrite H12;
        rewrite v_addi_Sj by lia; f_equal; lia
      | wlits; reflexivity ]. }
    (* sb a6,0(a7) : store the byte *)
    set (Mnext := wbytes zmemT aG (pre ++ firstn (S j) s)).
    assert (E5 : RiscvSemantics.step target_segs (mkst regs3 0x1001258 M arom)
                 = MachineOk (mkst regs3 0x100125c Mnext arom)).
    { eapply eq_trans;
      [ apply (step_sb_atv target_segs regs3 0x1001258 M arom _ 17 16 _
                 (aG + nat_to_word (length (pre ++ firstn j s))) b
                 TF_1001258 eq_refl TD_1001258);
        [ unfold regs3, regs2; getr_resolve; rewrite v_addi_0;
          rewrite HlenF; reflexivity
        | unfold regs3, regs2, regs1; getr_resolve; reflexivity
        | store_ok_peel; apply tgrant_store_ok;
          rewrite ?HlenF, ?word_add_nat; u_norm; lia ]
      | wlits;
        unfold Mnext, M;
        replace (pre ++ firstn (S j) s)
          with ((pre ++ firstn j s) ++ [b])
          by (rewrite (firstn_S_nth _ s j (Z_to_bv 8 0)) by lia;
              rewrite app_assoc; unfold b;
              rewrite (nth_lt_byte_at s j Hjlt); reflexivity);
        rewrite wbytes_snoc; reflexivity ]. }
    (* addi a5,a5,1 *)
    set (regs4 := regupd regs3 15 (p + nat_to_word (S j))).
    assert (E6 : RiscvSemantics.step target_segs (mkst regs3 0x100125c Mnext arom)
                 = MachineOk (mkst regs4 0x1001260 Mnext arom)).
    { eapply eq_trans;
      [ apply (step_addi_at target_segs regs3 0x100125c Mnext arom _ 15 15 _
                 (p + nat_to_word (S j)) TF_100125c eq_refl TD_100125c eq_refl);
        unfold regs3, regs2, regs1; getr_resolve; rewrite H15;
        apply v_addi_ntw_S
      | wlits; reflexivity ]. }
    (* j 0x1001248 *)
    assert (E7 : RiscvSemantics.step target_segs (mkst regs4 0x1001260 Mnext arom)
                 = MachineOk (mkst regs4 0x1001248 Mnext arom)).
    { rewrite (step_jal_x0 target_segs regs4 0x1001260 Mnext arom _ _
                 TF_1001260 eq_refl TD_1001260).
      wlits. reflexivity. }
    assert (H11' : reg_get regs4 11 = aG).
    { unfold regs4, regs3, regs2, regs1. regupd_resolve. exact H11. }
    assert (H12' : reg_get regs4 12 = nat_to_word (lp + S j)).
    { unfold regs4. rewrite regupd_other by reg_neq_tac.
      unfold regs3. apply regupd_same. }
    assert (H15' : reg_get regs4 15 = p + nat_to_word (S j)).
    { unfold regs4. apply regupd_same. }
    destruct (IH (S j) regs4 ltac:(lia) H11' H12' H15')
      as (regs' & Hag' & H12f & Hms').
    exists regs'. split; [|split].
    + intros r Hx12 Hx15 Hx16 Hx17. rewrite (Hag' r Hx12 Hx15 Hx16 Hx17).
      unfold regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + exact H12f.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      eapply mst_step; [reflexivity | exact E7 |].
      unfold Mnext in Hms'. exact Hms'.
Qed.

(* ----------------------------------------------------------------- *)
(* Outer copy loop: 0x1001228 .. exit at 0x100126c                    *)
(* ----------------------------------------------------------------- *)

Lemma target_copy_outer : forall f i regs,
  (1 <= i)%nat -> (i < length av)%nat -> (length av - i <= f)%nat ->
  reg_get regs 8 = Z_to_bv 64 (bv_unsigned asp + 8) ->
  reg_get regs 9 = targcN ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  reg_get regs 11 = aG ->
  reg_get regs 12 = nat_to_word (pbJ i) ->
  reg_get regs 13 = Z_to_bv 64 32 ->
  reg_get regs 14 = nat_to_word i ->
  exists regs',
    (forall r : reg, r <> 12 -> r <> 14 -> r <> 15 -> r <> 16 -> r <> 17 ->
       reg_get regs' r = reg_get regs r) /\
    reg_get regs' 12 = nat_to_word (ttotn - 1) /\
    reg_get regs' 15 = aG + nat_to_word (ttotn - 1) /\
    msteps target_segs
      (mkst regs 0x1001228 (wbytes zmemT aG (join1 (firstn (i-1) (tl av)))) arom)
      (mkst regs' 0x100126c (wbytes zmemT aG (join1 (tl av))) arom).
Proof.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi. pose proof stack_max_size_val as Hsms.
  pose proof ttotn_ge1 as Htg1. pose proof ttotn_bound as Htb.
  pose proof (valid_argv_len av Hva) as HargcLe.
  pose proof (u64_range aG) as HuaG. pose proof (u64_range gz) as Hugz.
  assert (Hgzn : (Z.of_nat ttotn <= bv_unsigned gz)%Z)
    by (rewrite <- u_ttot; exact Hgz_lo).
  induction f as [|f IH]; intros i regs H1 Hi Hf H8 H9 H10 H11 H12 H13 H14; [lia|].
  assert (HiZ : (Z.of_nat i <= 1024)%Z) by (apply tiN_le; lia).
  assert (HSiZ : (Z.of_nat (S i) <= 1024)%Z) by (apply tiN_le; lia).
  assert (HniB : (Z.of_nat (length (nth i av [])) <= 131071)%Z)
    by (apply valid_argv_str_len; [exact Hva | lia]).
  assert (HpbLe : (pbJ i <= ttotn - 1)%nat) by apply pbJ_le.
  assert (HpbLeS : (pbJ (S i) <= ttotn - 1)%nat) by apply pbJ_le.
  destruct (tsptr_bounds i ltac:(lia)) as [Hptrlo Hptrhi].
  set (M0 := wbytes zmemT aG (join1 (firstn (i-1) (tl av)))).
  assert (HlenM0 : length (join1 (firstn (i-1) (tl av))) = pbJ i)
    by reflexivity.
  (* add a5,a1,a2 : a5 = aG + pbJ i *)
  set (regs1 := regupd regs 15 (aG + nat_to_word (pbJ i))).
  assert (E1 : RiscvSemantics.step target_segs (mkst regs 0x1001228 M0 arom)
               = MachineOk (mkst regs1 0x100122c M0 arom)).
  { eapply eq_trans;
    [ apply (step_add_at target_segs regs 0x1001228 M0 arom _ 15 11 12
               (aG + nat_to_word (pbJ i)) TF_1001228 eq_refl TD_1001228 eq_refl);
      getr_resolve; rewrite H11, H12; rewrite v_add_word; reflexivity
    | wlits; reflexivity ]. }
  (* beq a4,s1 fall-through (i <> argc) *)
  assert (E2 : RiscvSemantics.step target_segs (mkst regs1 0x100122c M0 arom)
               = MachineOk (mkst regs1 0x1001230 M0 arom)).
  { rewrite (step_beq_ft target_segs regs1 0x100122c M0 arom _ 14 9 _
               TF_100122c eq_refl TD_100122c).
    - wlits. reflexivity.
    - unfold regs1. getr_resolve. rewrite H14, H9.
      apply c_eq_neq. rewrite u_ntw by lia. rewrite u_targcN. lia. }
  (* separator branch: reach 0x100123c with a2 = pbJ i + sep and the
     prefix extended by the separator byte *)
  set (sep := if Nat.eqb i 1 then 0%nat else 1%nat).
  set (preI := if Nat.eqb i 1 then join1 (firstn (i-1) (tl av))
               else join1 (firstn (i-1) (tl av)) ++ [Z_to_bv 8 32]).
  assert (HlenPre : length preI = (pbJ i + sep)%nat).
  { unfold preI, sep. destruct (Nat.eqb i 1).
    - rewrite HlenM0. lia.
    - rewrite length_app. cbn [length]. rewrite HlenM0. lia. }
  assert (Hsep1 : (sep <= 1)%nat) by (unfold sep; destruct (Nat.eqb i 1); lia).
  assert (HB : exists regsB,
     (forall r : reg, r <> 12 -> reg_get regsB r = reg_get regs1 r) /\
     reg_get regsB 12 = nat_to_word (pbJ i + sep) /\
     msteps target_segs (mkst regs1 0x1001230 M0 arom)
                        (mkst regsB 0x100123c (wbytes zmemT aG preI) arom)).
  { destruct (Nat.eq_dec i 1) as [Hi1 | Hine].
    - (* i = 1: bgeu taken, no separator *)
      exists regs1. split; [intros; reflexivity | split].
      + unfold sep. replace (Nat.eqb i 1) with true
          by (symmetry; apply Nat.eqb_eq; exact Hi1).
        unfold regs1. rewrite regupd_other by reg_neq_tac.
        rewrite H12. f_equal. lia.
      + eapply mst_step;
          [ reflexivity
          | eapply step_bgeu_tk;
            [ exact TF_1001230 | reflexivity | exact TD_1001230
            | unfold regs1; getr_resolve; rewrite H10, H14, Hi1;
              rewrite c_ltu_ltb; apply Z.ltb_ge;
              rewrite u_ntw by lia; u_norm; lia ]
          | ].
        norm_pc.
        unfold preI. replace (Nat.eqb i 1) with true
          by (symmetry; apply Nat.eqb_eq; exact Hi1).
        apply mst_refl.
    - (* i >= 2: bgeu fall-through, store the separator *)
      set (regs2 := regupd regs1 12 (nat_to_word (pbJ i + 1))).
      assert (F1 : RiscvSemantics.step target_segs (mkst regs1 0x1001230 M0 arom)
                   = MachineOk (mkst regs1 0x1001234 M0 arom)).
      { rewrite (step_bgeu_ft target_segs regs1 0x1001230 M0 arom _ 10 14 _
                   TF_1001230 eq_refl TD_1001230).
        - wlits. reflexivity.
        - unfold regs1. getr_resolve. rewrite H10, H14.
          rewrite c_ltu_ltb. apply Z.ltb_lt.
          rewrite u_ntw by lia. u_norm. lia. }
      assert (F2 : RiscvSemantics.step target_segs (mkst regs1 0x1001234 M0 arom)
                   = MachineOk (mkst regs2 0x1001238 M0 arom)).
      { eapply eq_trans;
        [ apply (step_addi_at target_segs regs1 0x1001234 M0 arom _ 12 12 _
                   (nat_to_word (pbJ i + 1)) TF_1001234 eq_refl TD_1001234 eq_refl);
          unfold regs1; getr_resolve; rewrite H12;
          rewrite v_addi_Sj by lia; f_equal; lia
        | wlits; reflexivity ]. }
      assert (F3 : RiscvSemantics.step target_segs (mkst regs2 0x1001238 M0 arom)
                   = MachineOk (mkst regs2 0x100123c (wbytes zmemT aG preI) arom)).
      { eapply eq_trans;
        [ apply (step_sb_atv target_segs regs2 0x1001238 M0 arom _ 15 13 _
                   (aG + nat_to_word (pbJ i)) (Z_to_bv 8 32)
                   TF_1001238 eq_refl TD_1001238);
          [ unfold regs2, regs1; getr_resolve; rewrite v_addi_0; reflexivity
          | unfold regs2, regs1; getr_resolve; rewrite H13; bveq
          | store_ok_peel; apply tgrant_store_ok;
            rewrite ?word_add_nat; u_norm; lia ]
        | wlits;
          unfold preI; replace (Nat.eqb i 1) with false
            by (symmetry; apply Nat.eqb_neq; exact Hine);
          unfold M0; rewrite wbytes_snoc; rewrite HlenM0; reflexivity ]. }
      exists regs2. split; [| split].
      + intros r Hx12. unfold regs2. rewrite regupd_other by assumption.
        reflexivity.
      + unfold regs2. rewrite regupd_same. unfold sep.
        replace (Nat.eqb i 1) with false
          by (symmetry; apply Nat.eqb_neq; exact Hine).
        f_equal; lia.
      + eapply mst_step; [reflexivity | exact F1 |].
        eapply mst_step; [reflexivity | exact F2 |].
        eapply mst_step; [reflexivity | exact F3 |].
        apply mst_refl. }
  destruct HB as (regsB & HagB & H12B & HmsB).
  assert (H8B : reg_get regsB 8 = Z_to_bv 64 (bv_unsigned asp + 8)).
  { rewrite (HagB 8 ltac:(reg_neq_tac)). unfold regs1.
    rewrite regupd_other by reg_neq_tac. exact H8. }
  assert (H11B : reg_get regsB 11 = aG).
  { rewrite (HagB 11 ltac:(reg_neq_tac)). unfold regs1.
    rewrite regupd_other by reg_neq_tac. exact H11. }
  assert (H14B : reg_get regsB 14 = nat_to_word i).
  { rewrite (HagB 14 ltac:(reg_neq_tac)). unfold regs1.
    rewrite regupd_other by reg_neq_tac. exact H14. }
  (* slli a5,a4,3 ; add a5,s0,a5 ; ld a5,0(a5) : a5 = tsptr i *)
  set (regsC := regupd regsB 15 (Z_to_bv 64 (8 * Z.of_nat i))).
  assert (EC : RiscvSemantics.step target_segs
                 (mkst regsB 0x100123c (wbytes zmemT aG preI) arom)
               = MachineOk (mkst regsC 0x1001240 (wbytes zmemT aG preI) arom)).
  { rewrite (step_slli target_segs regsB 0x100123c _ arom _ 15 14 _
               TF_100123c eq_refl TD_100123c).
    reduce_bv_eqb_ifs. getr_resolve. rewrite H14B.
    imm_norm. rewrite v_slli3_nat by lia. wlits. reflexivity. }
  set (regsD := regupd regsC 15
        (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * Z.of_nat i))).
  assert (ED : RiscvSemantics.step target_segs
                 (mkst regsC 0x1001240 (wbytes zmemT aG preI) arom)
               = MachineOk (mkst regsD 0x1001244 (wbytes zmemT aG preI) arom)).
  { eapply eq_trans;
    [ apply (step_add_at target_segs regsC 0x1001240 _ arom _ 15 8 15
               (Z_to_bv 64 (bv_unsigned asp + 8 + 8 * Z.of_nat i))
               TF_1001240 eq_refl TD_1001240 eq_refl);
      unfold regsC; getr_resolve; rewrite H8B;
      unfold v_add; u_norm; f_equal; lia
    | wlits; reflexivity ]. }
  set (regsE := regupd regsD 15 (tsptr i)).
  assert (EE : RiscvSemantics.step target_segs
                 (mkst regsD 0x1001244 (wbytes zmemT aG preI) arom)
               = MachineOk (mkst regsE 0x1001248 (wbytes zmemT aG preI) arom)).
  { rewrite (step_ld target_segs regsD 0x1001244 _ arom _ 15 15 _
               (word_le8 (tsptr i)) (tsptr i) TF_1001244 eq_refl TD_1001244).
    - reduce_bv_eqb_ifs. wlits. reflexivity.
    - unfold regsD. getr_resolve. rewrite v_addi_0.
      rewrite rdn_wbytes_disjoint
        by (rewrite ?HlenPre; u_norm; lia).
      unfold zmemT. rewrite rdn_zfill_out by (u_norm; try (right); lia).
      apply tread_arg_ptr. lia.
    - exact (bytes_le_n_to_le_8 _). }
  (* the inner byte copy *)
  destruct (target_copy_inner (tsptr i) (nth i av []) preI
              ltac:(apply targ_nz_k; lia)
              ltac:(rewrite HlenPre;
                    rewrite (pbJ_stepN i H1 Hi) in HpbLeS;
                    unfold sep; destruct (Nat.eqb i 1); lia)
              ltac:(lia) ltac:(lia)
              (fun j Hj => tread_arg_byte i j ltac:(lia) Hj)
              (length (nth i av [])) O regsE
              ltac:(lia)
              ltac:(unfold regsE, regsD, regsC;
                    rewrite !regupd_other by reg_neq_tac; exact H11B)
              ltac:(unfold regsE, regsD, regsC;
                    rewrite !regupd_other by reg_neq_tac;
                    rewrite H12B; f_equal; rewrite HlenPre; lia)
              ltac:(unfold regsE; rewrite regupd_same;
                    rewrite word_add_0; reflexivity))
    as (regsI & HagI & H12I & HmsI).
  assert (HmemI : wbytes zmemT aG (preI ++ firstn 0 (nth i av []))
                  = wbytes zmemT aG preI).
  { cbn [firstn]. rewrite app_nil_r. reflexivity. }
  rewrite HmemI in HmsI.
  assert (HpreApp : preI ++ nth i av [] = join1 (firstn i (tl av))).
  { unfold preI. destruct (Nat.eqb i 1) eqn:Ei.
    - apply Nat.eqb_eq in Ei. subst i.
      rewrite tjoin_1. reflexivity.
    - apply Nat.eqb_neq in Ei.
      rewrite (tjoin_step i ltac:(lia) Hi).
      rewrite <- app_assoc. reflexivity. }
  assert (H12I' : reg_get regsI 12 = nat_to_word (pbJ (S i))).
  { rewrite H12I. f_equal. rewrite HlenPre.
    rewrite (pbJ_stepN i H1 Hi). unfold sep.
    destruct (Nat.eqb i 1); lia. }
  (* addi a4,a4,1 ; j 0x1001228 *)
  set (regsF := regupd regsI 14 (nat_to_word (S i))).
  assert (EF : RiscvSemantics.step target_segs
                 (mkst regsI 0x1001264 (wbytes zmemT aG (preI ++ nth i av [])) arom)
               = MachineOk (mkst regsF 0x1001268
                              (wbytes zmemT aG (preI ++ nth i av [])) arom)).
  { eapply eq_trans;
    [ apply (step_addi_at target_segs regsI 0x1001264 _ arom _ 14 14 _
               (nat_to_word (S i)) TF_1001264 eq_refl TD_1001264 eq_refl);
      rewrite getr_nz by reg_neq_tac;
      rewrite (HagI 14 ltac:(reg_neq_tac) ltac:(reg_neq_tac)
                 ltac:(reg_neq_tac) ltac:(reg_neq_tac));
      unfold regsE, regsD, regsC;
      rewrite !regupd_other by reg_neq_tac;
      rewrite H14B;
      apply v_addi_Sj; lia
    | wlits; reflexivity ]. }
  assert (EG : RiscvSemantics.step target_segs
                 (mkst regsF 0x1001268 (wbytes zmemT aG (preI ++ nth i av [])) arom)
               = MachineOk (mkst regsF 0x1001228
                              (wbytes zmemT aG (preI ++ nth i av [])) arom)).
  { rewrite (step_jal_x0 target_segs regsF 0x1001268 _ arom _ _
               TF_1001268 eq_refl TD_1001268).
    wlits. reflexivity. }
  assert (HagF : forall r : reg, r <> 12 -> r <> 14 -> r <> 15 -> r <> 16 ->
                 r <> 17 -> reg_get regsF r = reg_get regs r).
  { intros r Hx12 Hx14 Hx15 Hx16 Hx17.
    unfold regsF. rewrite regupd_other by assumption.
    rewrite (HagI r Hx12 Hx15 Hx16 Hx17).
    unfold regsE, regsD, regsC. rewrite !regupd_other by assumption.
    rewrite (HagB r Hx12). unfold regs1.
    rewrite regupd_other by assumption. reflexivity. }
  assert (H8F : reg_get regsF 8 = Z_to_bv 64 (bv_unsigned asp + 8))
    by (rewrite HagF by reg_neq_tac; exact H8).
  assert (H9F : reg_get regsF 9 = targcN)
    by (rewrite HagF by reg_neq_tac; exact H9).
  assert (H10F : reg_get regsF 10 = Z_to_bv 64 1)
    by (rewrite HagF by reg_neq_tac; exact H10).
  assert (H11F : reg_get regsF 11 = aG)
    by (rewrite HagF by reg_neq_tac; exact H11).
  assert (H13F : reg_get regsF 13 = Z_to_bv 64 32)
    by (rewrite HagF by reg_neq_tac; exact H13).
  assert (H12F : reg_get regsF 12 = nat_to_word (pbJ (S i))).
  { unfold regsF. rewrite regupd_other by reg_neq_tac. exact H12I'. }
  assert (H14F : reg_get regsF 14 = nat_to_word (S i)).
  { unfold regsF. apply regupd_same. }
  destruct (lt_dec (S i) (length av)) as [Hlti | Hge].
  - (* another argument follows *)
    destruct (IH (S i) regsF ltac:(lia) Hlti ltac:(lia)
                H8F H9F H10F H11F H12F H13F H14F)
      as (regs' & Hag' & H12' & H15' & Hms').
    exists regs'. split; [| split; [| split]].
    + intros r Hx12 Hx14 Hx15 Hx16 Hx17.
      rewrite (Hag' r Hx12 Hx14 Hx15 Hx16 Hx17).
      apply HagF; assumption.
    + exact H12'.
    + exact H15'.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply msteps_trans; [exact HmsB |].
      eapply mst_step; [reflexivity | exact EC |].
      eapply mst_step; [reflexivity | exact ED |].
      eapply mst_step; [reflexivity | exact EE |].
      eapply msteps_trans; [exact HmsI |].
      eapply mst_step; [reflexivity | exact EF |].
      eapply mst_step; [reflexivity | exact EG |].
      replace (preI ++ nth i av [])
        with (join1 (firstn (S i - 1) (tl av)));
        [ exact Hms'
        | rewrite HpreApp; f_equal; f_equal; lia ].
  - (* i+1 = argc: one more head pass, then exit to 0x100126c *)
    assert (HSieq : (S i = length av)%nat) by lia.
    assert (HpreAll : preI ++ nth i av [] = join1 (tl av)).
    { rewrite HpreApp.
      replace (firstn i (tl av)) with (tl av); [reflexivity|].
      replace i with (length (tl av)) by (rewrite tlength_tl_av; lia).
      symmetry. apply firstn_all. }
    assert (HpbSi : pbJ (S i) = (ttotn - 1)%nat).
    { rewrite HSieq. apply pbJ_last. }
    (* add a5,a1,a2 : a5 = aG + (ttot-1) *)
    set (regsH := regupd regsF 15 (aG + nat_to_word (ttotn - 1))).
    assert (EH : RiscvSemantics.step target_segs
                   (mkst regsF 0x1001228 (wbytes zmemT aG (preI ++ nth i av [])) arom)
                 = MachineOk (mkst regsH 0x100122c
                                (wbytes zmemT aG (preI ++ nth i av [])) arom)).
    { eapply eq_trans;
      [ apply (step_add_at target_segs regsF 0x1001228 _ arom _ 15 11 12
                 (aG + nat_to_word (ttotn - 1)) TF_1001228 eq_refl TD_1001228 eq_refl);
        getr_resolve; rewrite H11F, H12F, HpbSi;
        rewrite v_add_word; reflexivity
      | wlits; reflexivity ]. }
    (* beq a4,s1 taken -> 0x100126c *)
    assert (EI : RiscvSemantics.step target_segs
                   (mkst regsH 0x100122c (wbytes zmemT aG (preI ++ nth i av [])) arom)
                 = MachineOk (mkst regsH 0x100126c
                                (wbytes zmemT aG (preI ++ nth i av [])) arom)).
    { rewrite (step_beq_tk target_segs regsH 0x100122c _ arom _ 14 9 _
                 TF_100122c eq_refl TD_100122c).
      - wlits. reflexivity.
      - unfold regsH. getr_resolve. rewrite H14F, H9F.
        unfold targcN, len_word, nat_to_word. rewrite HSieq.
        apply c_eq_refl. }
    exists regsH. split; [| split; [| split]].
    + intros r Hx12 Hx14 Hx15 Hx16 Hx17.
      unfold regsH. rewrite regupd_other by assumption.
      apply HagF; assumption.
    + unfold regsH. rewrite regupd_other by reg_neq_tac.
      rewrite H12F. f_equal. exact HpbSi.
    + unfold regsH. apply regupd_same.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply msteps_trans; [exact HmsB |].
      eapply mst_step; [reflexivity | exact EC |].
      eapply mst_step; [reflexivity | exact ED |].
      eapply mst_step; [reflexivity | exact EE |].
      eapply msteps_trans; [exact HmsI |].
      eapply mst_step; [reflexivity | exact EF |].
      eapply mst_step; [reflexivity | exact EG |].
      eapply mst_step; [reflexivity | exact EH |].
      eapply mst_step; [reflexivity | exact EI |].
      rewrite HpreAll.
      apply mst_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* From the newline store to the write and exit 0                     *)
(* ----------------------------------------------------------------- *)

(** The tail after the put loop: exit code 0.  Entered at 0x1001298
    with the frame still in place. *)
Lemma target_out_tail : forall model regs,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64) ->
  twm target_segs (mkst regs 0x1001298 (wbytes zmemT aG (jout av)) arom)
      model [] (Z_to_bv 64 0).
Proof.
  intros model regs H2r.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof ttotn_ge1 as Htg1. pose proof ttotn_bound as Htb.
  pose proof (u64_range aG) as HuaG. pose proof (u64_range gz) as Hugz.
  assert (Hgzn : (Z.of_nat ttotn <= bv_unsigned gz)%Z)
    by (rewrite <- u_ttot; exact Hgz_lo).
  set (memJ := wbytes zmemT aG (jout av)) in *.
  (* THREE instructions: the exit code, the jump onto the shared tail
     and its [mv a0,a1]. *)
  sym_block target_segs 3%nat (@nil bool) (@nil expr)
    [((2 : reg), EVar 32)] [Z_to_bv 64 (bv_unsigned asp - 64)]
    (@nil word) RB HRB.
  { exact H2r. }
  (* epilogue with a0 = 0 *)
  lazymatch goal with
  | |- twm _ (mkst ?R _ ?M _) _ _ _ =>
    edestruct (target_epilogue R M (Z_to_bv 64 0)) as [regsE [HE17 [HE10 HmsE]]]
  end.
  { sym_regs HRB. sym_close. }
  { sym_regs HRB. sym_close. }
  { unfold memJ.
    rewrite rdn_wbytes_disjoint
      by (rewrite ?tjout_len_nat; u_norm; lia).
    unfold zmemT.
    rewrite rdn_zfill_out by (u_norm; try (right); lia).
    exact tfread_slot_ra. }
  { unfold memJ.
    rewrite rdn_wbytes_disjoint
      by (rewrite ?tjout_len_nat; u_norm; lia).
    unfold zmemT.
    rewrite rdn_zfill_out by (u_norm; try (right); lia).
    exact tfread_slot_s0. }
  { intros a Ha.
    assert (Hab : (bv_unsigned asp - 64 <= bv_unsigned a
                   /\ bv_unsigned a <= bv_unsigned asp - 40)%Z).
    { repeat destruct Ha as [<-|Ha]; try (exfalso; exact Ha); u_norm; lia. }
    destruct Hab as [Hab1 Hab2].
    unfold memJ.
    rewrite rdn_wbytes_disjoint
      by (rewrite ?tjout_len_nat; lia).
    unfold zmemT.
    rewrite rdn_zfill_out by (try (right); lia).
    apply tfread_slot_0. exact Ha. }
  eapply msteps_twm; [exact HmsE|].
  apply twm_exit_coden;
    [exact HE17 | exact HE10 | vm_compute; reflexivity].
Qed.

(** The put-style write-all retry loop at 0x1001288: register-only, so
    the memory and every register outside a0/a1/a2 carry through
    unchanged. *)
Lemma tgt_put_wall : forall model fuel (rest : list byte) (p : word) k regs,
  (length rest <= fuel)%nat ->
  (1 <= k)%nat -> (k <= length rest)%nat ->
  (Z.of_nat (length rest) <= 2097152)%Z ->
  (0 < bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) <= bv_unsigned asp)%Z ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64) ->
  reg_get regs 10 = len_word (firstn k rest) ->
  reg_get regs 11 = p ->
  reg_get regs 12 = len_word rest ->
  bv_unsigned (reg_get regs 17) = 64%Z ->
  rdn target_segs (wbytes zmemT aG (jout av)) p (length rest) = Some rest ->
  twm_tail target_segs (mkst regs 0x1001288 (wbytes zmemT aG (jout av)) arom)
    model (skipn k rest) [] (Z_to_bv 64 0).
Proof.
  intros model fuel. induction fuel as [|fuel IH];
    intros rest p k regs Hfuel Hk1 Hk2 Hlen Hplo Hphi
           H2r H10 H11 H12 H17 Hread.
  { lia. }
  pose proof asp_hi_num as Hahi.
  (* 0x1001288: blez a0 falls through (the delivery is nonempty) *)
  step_intro;
    [ reflexivity
    | eapply step_bge_ft;
      [ exact TF_1001288 | reflexivity | exact TD_1001288
      | getr_resolve; rewrite H10; apply c_lts_0_pos;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x100128c: add a1,a1,a0 *)
  stepiv TF_100128c TD_100128c (Z_to_bv 64 (bv_unsigned p + Z.of_nat k))
    ltac:(getr_resolve; rewrite H11, H10; apply v_add_len_firstn_Z; lia).
  (* 0x1001290: sub a2,a2,a0 *)
  stepiv TF_1001290 TD_1001290 (len_word (skipn k rest))
    ltac:(getr_resolve; rewrite H12, H10; apply v_sub_len_firstn; lia).
  destruct (Nat.eq_dec k (length rest)) as [-> | Hne].
  - (* full delivery: bnez not taken, fall into the exit-0 tail *)
    rewrite skipn_all.
    step_intro;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact TF_1001294 | reflexivity | exact TD_1001294
        | getr_resolve; apply c_eq_0_of_u; reflexivity ]
      | norm_pc ].
    apply twmt_done. apply target_out_tail.
    regupd_resolve; exact H2r.
  - (* short delivery: bnez taken, reissue on the remainder *)
    step_intro;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact TF_1001294 | reflexivity | exact TD_1001294
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* 0x1001280: li a0,1 *)
    stepiv TF_1001280 TD_1001280 (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* 0x1001284: ecall -- the reissued write *)
    eapply twmt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ TF_1001284 eq_refl) |].
    apply twm_tail_write_rec.
    + getr_resolve; first [ exact H17 | vm_compute; reflexivity ].
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
      pose proof (rdn_skipn target_segs (wbytes zmemT aG (jout av))
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
      * regupd_resolve; first [ exact H17 | vm_compute; reflexivity ].
      * pose proof (rdn_skipn target_segs (wbytes zmemT aG (jout av))
                      (length rest) p rest k Hread Hk2) as Hsk.
        rewrite word_add_nat_Z in Hsk by lia.
        rewrite length_skipn. exact Hsk.
Qed.

Lemma target_out : forall model regs,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64) ->
  reg_get regs 11 = aG ->
  reg_get regs 12 = nat_to_word (ttotn - 1) ->
  reg_get regs 15 = aG + nat_to_word (ttotn - 1) ->
  twm target_segs (mkst regs 0x100126c (wbytes zmemT aG (join1 (tl av))) arom)
      model [jout av] (Z_to_bv 64 0).
Proof.
  intros model regs H2r H11 H12 H15.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof ttotn_ge1 as Htg1. pose proof ttotn_bound as Htb.
  pose proof (u64_range aG) as HuaG. pose proof (u64_range gz) as Hugz.
  assert (Hgzn : (Z.of_nat ttotn <= bv_unsigned gz)%Z)
    by (rewrite <- u_ttot; exact Hgz_lo).
  pose proof (u64_range (aG + nat_to_word (ttotn - 1))) as HuaGn.
  (* the executor's spellings: the [sb]'s address carries an explicit
     [+0], and [addi a2,a2,1] is [Z_to_bv 64 (… + 1)]. *)
  assert (Hsba : Z_to_bv 64 (bv_unsigned (aG + nat_to_word (ttotn - 1)) + 0)
                 = aG + nat_to_word (ttotn - 1))
    by (apply bv_eq; rewrite u_Z2bv by lia; lia).
  assert (Httv : Z_to_bv 64 (bv_unsigned (nat_to_word (ttotn - 1)) + 1) = ttot).
  { change (Z_to_bv 64 (bv_unsigned (nat_to_word (ttotn - 1)) + 1))
      with (v_addi (nat_to_word (ttotn - 1)) 1).
    rewrite v_addi_Sj by lia. unfold ttot. f_equal. lia. }
  set (memJ := wbytes zmemT aG (jout av)).
  (* SIX instructions in ONE reflective block: the trailing newline
     store, the [+1] that makes the count [tot], the write's [fd]/[n]
     arguments and the [n = 0] test, stopping at the write [ecall]. *)
  sym_block target_segs 6%nat [false] (@nil expr)
    [((11 : reg), EVar 32); ((12 : reg), EVar 33); ((15 : reg), EVar 34)]
    [aG; nat_to_word (ttotn - 1); aG + nat_to_word (ttotn - 1)]
    (@nil word) RA HRA.
  { (* [beq a2,x0] at 0x100127c -> not taken, because [tot <> 0] *)
    rewrite Httv, bv_eqb_Z; apply Z.eqb_neq; rewrite u_ttot; u_norm; lia. }
  { (* [sb a0,0(a5)] at 0x1001270 -> the newline at [aG + ttotn - 1] *)
    rewrite Hsba; store_ok_peel; apply tgrant_store_ok;
    rewrite ?word_add_nat; u_norm; lia. }
  { (* the [a1] pin *) exact H11. }
  { (* the [a2] pin *) exact H12. }
  { (* the [a5] pin *) exact H15. }
  rewrite Hsba.
  match goal with
  |- twm _ (mkst _ _ ?M _) _ _ _ =>
      replace M with memJ
        by (unfold memJ, jout;
            rewrite wbytes_snoc, tjoin1_tl_len_nat; reflexivity)
  end.
  (* 0x1001284: the write [ecall] *)
  eapply twm_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ TF_1001284 eq_refl) | ].
  eapply twm_write_ret with (buf := jout av).
  { sym_regs HRA. vm_compute. reflexivity. }
  { sym_regs HRA. sym_close. }
  { rewrite (ms_read_bytes_rdn (run_segments target_segs inp asp amb)) by reflexivity;
      unfold run_segments; apply rdn_lift.
    cbn [ms_mem ms_regs].
    sym_regs HRA.
    rewrite ?Httv, tjout_len_w.
    unfold memJ.
    apply rdn_wbytes_hit.
    rewrite tjout_len_nat. lia. }
  { (* [vfs_write]'s [access_ok] on the whole joined buffer: the lemma
       first, so [sym_regs]' unsigned normalisation cannot hide the
       count's [bv_unsigned] from it *)
    apply Uaccess.access_okb_intro.
    cbn [ms_regs]. sym_regs HRA.
    rewrite ?Httv, ?u_ttot. rewrite ?u_ntw by lia. unfold TASK_SIZE. lia. }
  { rewrite tjout_len_nat; lia. }
  (* 0x1001288 ..: the put-style retry loop, per delivered length. *)
  intros k Hk1 Hk2.
  norm_pc.
  apply (tgt_put_wall model (length (jout av)) (jout av) aG k).
  - lia.
  - exact Hk1.
  - exact Hk2.
  - rewrite tjout_len_nat; lia.
  - exact HaPos.
  - rewrite tjout_len_nat. lia.
  - regupd_resolve; sym_regs HRA; first [ exact H2r | sym_close ].
  - regupd_resolve; reflexivity.
  - regupd_resolve; sym_regs HRA; first [ exact H11 | sym_close ].
  - regupd_resolve; sym_regs HRA.
    match goal with |- ?x = _ => transitivity ttot end;
      [ first [ exact Httv | (symmetry; exact Httv) | sym_close ]
      | unfold ttot, nat_to_word, len_word; rewrite tjout_len_nat; reflexivity ].
  - regupd_resolve; sym_regs HRA; vm_compute; reflexivity.
  - unfold memJ. apply rdn_wbytes_hit. rewrite tjout_len_nat. lia.
Qed.

(* ----------------------------------------------------------------- *)
(* The whole success continuation from the mmap return                *)
(* ----------------------------------------------------------------- *)

Lemma target_succ_twm : forall model regs,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned asp - 64) ->
  reg_get regs 8 = Z_to_bv 64 (bv_unsigned asp + 8) ->
  reg_get regs 9 = targcN ->
  twm target_segs (mkst (regupd regs 10 aG) 0x1001210 (zfill aG gz tfmem) arom)
      model [jout av] (Z_to_bv 64 0).
Proof.
  intros model regs H2r H8r H9r.
  pose proof asp_lo_num. pose proof asp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof ttotn_ge1 as Htg1. pose proof ttotn_bound as Htb.
  pose proof (u64_range gz) as Hugz.
  assert (Hagl : (bv_unsigned aG < 2^63)%Z) by lia.
  (* SIX instructions in ONE reflective block: the "mmap did not fail"
     test and the five constants the copy loop runs on.  No memory
     traffic; one branch, one pinned register (the grant base). *)
  sym_block target_segs 6%nat [false] (@nil expr)
    [((10 : reg), EVar 32)] [aG] (@nil word) RA HRA.
  { (* [blt a0,x0] at 0x1001210 -> not taken: the grant is not an errno *)
    rewrite bv_lts_small by (u_norm; lia); apply Z.ltb_ge; u_norm; lia. }
  { (* the [a0] pin *) getr_resolve; regupd_resolve; reflexivity. }
  (* the nested copy loops *)
  lazymatch goal with
  | |- twm _ (mkst ?R _ _ _) _ _ _ =>
    edestruct (target_copy_outer (length av) 1%nat R)
      as (regsC & HagC & H12C & H15C & HmsC)
  end.
  { lia. } { lia. } { lia. }
  1-7: (sym_regs HRA;
        first [ reflexivity | assumption
              | (getr_resolve; regupd_resolve; assumption)
              | (rewrite pbJ_1; reflexivity)
              | (f_equal; lia) | (apply bv_eq; u_norm; lia) | bveq ]).
  eapply msteps_twm; [exact HmsC |].
  apply target_out.
  - rewrite (HagC 2) by reg_neq_tac. sym_regs HRA.
    getr_resolve; regupd_resolve; exact H2r.
  - rewrite (HagC 11) by reg_neq_tac. sym_regs HRA. sym_close.
  - exact H12C.
  - exact H15C.
Qed.

End TargetSucc.

(* ================================================================= *)
(* The packaged tmw derivation for the target binary                  *)
(* ================================================================= *)

(** The target's whole run, from the launch's state and model ([Run]'s:
    [State.with_vdso] of the draw's vDSO counter over [State.init_model]);
    [Hmb] is [Run.valid_mmap_base]'s floor. *)
Lemma target_tmw : (mmap_base_min <= bv_unsigned amb)%Z ->
  (bv_unsigned ttot <= 65536)%Z ->
  tmw target_segs
      (init_machine_state (run_segments target_segs inp asp amb) 0x1001158 target_phdrs asp amb arnd inp)
      (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
         (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
      [] (Z_to_bv 64 4) [jout av] (Z_to_bv 64 0).
Proof.
  intros Hmb Hcap.
  pose proof ttotn_ge1 as Htg1. pose proof ttotn_bound as Htb.
  pose proof u_ttot as Hut.
  destruct (target_to_mmap Hcap)
    as (regsE & HE2 & HE8 & HE9 & HE11 & HE12 & HE13 & HE14 & HE15
        & HE10 & HE17 & Hms).
  eapply msteps_tmw; [exact Hms|].
  apply tmw_mmap_rec.
  - exact HE17.
  - (* len (a1) nonzero *) rewrite HE11.
    intro Heq. apply bv_eq in Heq. rewrite u_ttot in Heq.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Heq. lia.
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
    apply target_fail_twm; [exact He1 | exact He2 | exact HE2].
  - (* success family: one write, exit 0 *)
    intros aa Hg.
    rewrite HE11 in Hg |- *. norm_pc.
    destruct (pru_Z_bounds (bv_unsigned ttot) ltac:(lia)) as [Hg1 Hg2].
    assert (Hpruu : bv_unsigned (page_round_up ttot)
                    = page_round_up_Z (bv_unsigned ttot))
      by (apply pru_u; lia).
    destruct (target_grant_unpack inp _ abrk amb asp _ aa
                (page_round_up_Z (bv_unsigned ttot))
                ltac:(apply page_round_up_Z_nonneg; lia)
                ltac:(lia) Hg)
      as (Hpos & Hceil & Hda' & Hdb').
    eapply (target_succ_twm aa (page_round_up ttot));
      first [ exact Hpos
            | (rewrite Hpruu;
               first [ exact Hg1 | exact Hceil | exact Hda' | exact Hdb' ])
            | exact HE2 | exact HE8 | exact HE9 ].
  - (* at least one admissible grant: the address Linux's placement gives *)
    rewrite HE11.
    destruct (pru_Z_bounds (bv_unsigned ttot) ltac:(lia)) as [Hg1 Hg2].
    apply (target_grant_witness inp _ abrk amb asp _ _ Hsp_lo Hmb).
    + lia.
    + unfold page_round_up_Z. apply Z.mod_mul. unfold page_size. lia.
    + lia.
Qed.

End Ge2T.

End TargetProof.
