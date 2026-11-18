(** * oob-read-bug-ns source binary: per-binary derivations.

    PROOF-SIDE FILE (not part of the trusted specification).

    Deliverables (Section [SourceProof], generic over av/ev and the
    ASLR window sp):
    - [source_wexit_lt2]  : argc < 2             -> to_wexit [] 2
    - [source_wexit_cap]  : argc >= 2, n > 65536 -> to_wexit [] 3
    - [source_outcomes]   : argc >= 2, n <= 65536 ->
        to_outcomes (the run's list) (init) (the run's initial model)
          (oobU (outbufs argv[1]))
    - [source_outcomes_mix]/[source_escape]: compatibility spellings of
        the same complete outcome theorem for non-multiples of eight.
        RETAINED BUT NO LONGER CALLED.  Page-rounded [brk] grants made the
        [n mod 8 <> 0] overread defined, so [Proof.v] now drives every
        [n <= 65536] case through [source_outcomes] and these two have no
        call site anywhere in [theories/].  They are kept because a proof
        is not deleted once written, and each still re-derives
        [source_outcomes], so they cannot rot silently — but a reader
        looking for what the file contributes to the build should read
        [source_outcomes] and stop.  [oob_read_bug_ns_target.v]'s
        [target_continues_mod] is uncalled for the same reason.
        Two helpers one level below them go the same way:
        [source_to_fault] and [source_fault_step] are still compiled and
        still proved, but nothing in [theories/] calls them.  Their last
        callers were the byte-granular predecessor proofs of the two
        above, which this file no longer carries: they had been left
        commented out for comparison after the port to page-granular
        grants, and Rocq never read them.  [git log -p] on this file
        holds them.

    The C source computes [strlen] with a hand-written byte loop; under
    [-fno-builtin] gcc keeps it as an inline byte-at-a-time scan
    ([source_slen_loop] below) instead of calling musl's word-at-a-time
    [strlen].  The scan reads exactly the bytes of argv[1] up to and
    including the NUL.  The byte-sum loop still rounds the length up to a
    multiple of eight, but page-rounded [brk] grants make those logical
    overreads defined: the trailing physical bytes read as zero.
    The stack read-back below is still stated for [nn + 8] bytes: above
    argv[1]'s NUL the initial stack image holds the later strings, the
    exec name with its NUL and the eight-byte slot below the stack's top
    (Linux v6.18.46 fs/exec.c:1831-1840, mm/vma_exec.c:150), so at least
    eight bytes follow the NUL ([source_ptr_room]); the scan only consumes
    the first [nn + 1].

    The run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  The derivations step over the image's own [source_segs] and are
    carried to the run's list whole in [source_outcomes]
    ([RunSegmentsLift.msteps_run], [to_wallexit_run]): no instruction here
    fetches from the pair.  The states carry the run's rom.  The brk
    ledger of the run's initial model is [State.init_reserved]: the
    image's reservations, then the vDSO pair, which lies far above the
    heap ([run_ledger_free]).  The stack bounds come from the entry
    predicate's launch conjunct [Run.entry_launch_ok_va] and
    [Run.valid_launch]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec AllocSim WallSim NumPrint StepTac MuslStrlen StreamSim StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Common Require Import Footprint SymExec SymTac SymBranch SymSide.
From LinuxProcessSemantics.Examples.oob_read_bug_ns Require Import oob_read_bug_ns_code oob_read_bug_ns_defs.
From LinuxProcessSemantics.Examples.oob_read_bug_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.oob_read_bug_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them.  [fx0] itself is
    the instance, so every state here is [init_mkst]'s [@mkst fx0]. *)
#[local] Existing Instance fx0.

Local Ltac bveq := apply bv_eq; vm_compute; reflexivity.

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x111c8%N.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Local helpers (copied from grep_args_ns/brk_rev_ns ports)          *)
(* ================================================================= *)


Lemma sumb_nonneg : forall s, (0 <= sumb s)%Z.
Proof.
  induction s as [|b s IH]; [cbn; lia|].
  unfold sumb in *. cbn [fold_right]. pose proof (u8_range b). lia.
Qed.

Lemma word_add_nat_split : forall (r : word) (m j : nat),
  (bv_unsigned r + Z.of_nat m + Z.of_nat j < 2 ^ 64)%Z ->
  v_add (r + nat_to_word m) (nat_to_word j) = r + nat_to_word (m + j).
Proof.
  intros r m j Hnw. pose proof (u64_range r) as Hr0.
  apply bv_eq. unfold v_add.
  rewrite Z_to_bv_unsigned.
  rewrite (u_add_small r (nat_to_word m)) by (rewrite u_ntw by lia; lia).
  rewrite (u_ntw m) by lia. rewrite (u_ntw j) by lia.
  rewrite word_add_nat, Z_to_bv_unsigned, Nat2Z.inj_add. f_equal. lia.
Qed.

Lemma v_addi_nat_add : forall (k n : nat),
  (Z.of_nat k + Z.of_nat n < 2 ^ 64)%Z ->
  v_addi (nat_to_word k) (Z.of_nat n) = nat_to_word (k + n).
Proof.
  intros k n Hnw. apply bv_eq. unfold v_addi, nat_to_word.
  rewrite !Z_to_bv_unsigned. rewrite bv_wrap_add_idemp_l.
  rewrite Nat2Z.inj_add. reflexivity.
Qed.

Lemma v_addi_off_nat_add : forall (r : word) (k n : nat),
  (bv_unsigned r + Z.of_nat k + Z.of_nat n < 2 ^ 64)%Z ->
  v_addi (r + nat_to_word k) (Z.of_nat n) = r + nat_to_word (k + n).
Proof.
  intros r k n Hnw. pose proof (u64_range r) as Hr0.
  apply bv_eq. unfold v_addi.
  rewrite (u_add_small r (nat_to_word k)) by (rewrite u_ntw by lia; lia).
  rewrite (u_ntw k) by lia.
  rewrite word_add_nat. rewrite !Z_to_bv_unsigned.
  rewrite Nat2Z.inj_add. f_equal. lia.
Qed.


(* ================================================================= *)
(* Reserved list and store legality                                   *)
(* ================================================================= *)

Lemma source_reserved_val :
  segments_reserved source_segs = [(0x10000, 0x1000); (0x11000, 0x1000); (0x12000, 0x1000); (0x13000, 0x1000)].
Proof. vm_refl. Qed.

(** Stores at/above the end of the (page-rounded) read-only part of the
    image are legal.  Under [-z separate-code] that part is THREE
    segments — [0x10000, 0x11000) headers, [0x11000, 0x12000) .text, and
    [0x12000, 0x13000) .rodata + .eh_frame — with the writable data
    segment starting at 0x13000. *)
Lemma source_avoids_stack : forall (a : word) (n : Z),
  (0x13000 <= bv_unsigned a)%Z ->
  range_avoids_ro_segs source_segs (bv_unsigned a) n = true.
Proof.
  intros a n Ha.
  apply range_avoids_ro_above with (data_base := 0x13000%Z);
    [vm_compute; reflexivity | exact Ha].
Qed.

(** The source image's WRITABLE window: the rw- segment covers
    [0x13000, 0x14000) and the snapshot carries a byte for every
    address in it (.bss is zero-filled in the .hex), so [wview] is
    defined there whatever the overlay holds — a store into .data/.bss
    needs no prior write.  That is the [store_ok] side condition
    machine stores now carry; stack targets go through the RLIMIT_STACK
    window ([solve_store_ok]) and heap targets through the grant's
    zero-fill ([store_ok_zmem]). *)
Lemma source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma source_store_ok : forall (m : word -> option byte) (a : word) (n : nat),
  (0x13000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x14000)%Z ->
  store_ok source_segs m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply store_ok_window with (base := 0x13000%Z) (hi := 0x14000%Z);
    [ | | | exact source_data_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.

(** A region [b, b+l) free against the page-rounded reservations is
    entirely below 0x10000 or entirely at/above 0x14000.  There are FOUR
    reserved pages under [-z separate-code] (headers, .text, .rodata,
    data), so the region cannot start inside the image at all. *)
Lemma source_free_cases : forall (b l : word),
  region_free (segments_reserved source_segs) b l = true ->
  (0 < bv_unsigned l)%Z ->
  (bv_unsigned b + bv_unsigned l <= 0x10000)%Z \/ (0x14000 <= bv_unsigned b)%Z.
Proof.
  intros b l Hfree Hl.
  rewrite source_reserved_val in Hfree.
  cbn [region_free] in Hfree.
  apply andb_true_iff in Hfree as [H0 Hfree].
  apply andb_true_iff in Hfree as [H1 Hfree].
  apply andb_true_iff in Hfree as [H2 Hfree].
  apply andb_true_iff in Hfree as [H3 _].
  apply negb_true_iff in H0. apply negb_true_iff in H1.
  apply negb_true_iff in H2. apply negb_true_iff in H3.
  unfold iv_overlap in H0, H1, H2, H3.
  change (bv_unsigned (0x10000 : word)) with 0x10000%Z in H0.
  change (bv_unsigned (0x11000 : word)) with 0x11000%Z in H1.
  change (bv_unsigned (0x12000 : word)) with 0x12000%Z in H2.
  change (bv_unsigned (0x13000 : word)) with 0x13000%Z in H3.
  change (bv_unsigned (0x1000 : word)) with 0x1000%Z in H0, H1, H2, H3.
  apply andb_false_iff in H0. apply andb_false_iff in H1.
  apply andb_false_iff in H2. apply andb_false_iff in H3.
  destruct H0 as [H0|H0]; destruct H1 as [H1|H1];
    destruct H2 as [H2|H2]; destruct H3 as [H3|H3];
    apply Z.ltb_ge in H0; apply Z.ltb_ge in H1;
    apply Z.ltb_ge in H2; apply Z.ltb_ge in H3; lia.
Qed.

(** A region free against the reservations avoids the read-only segment
    everywhere inside it. *)
Lemma source_free_avoids : forall (b l : word),
  region_free (segments_reserved source_segs) b l = true ->
  (0 < bv_unsigned l)%Z ->
  forall (a k : Z), (bv_unsigned b <= a)%Z ->
  (a + k <= bv_unsigned b + bv_unsigned l)%Z ->
  range_avoids_ro_segs source_segs a k = true.
Proof.
  intros b l Hfree Hl a k Hlo Hhi.
  unfold range_avoids_ro_segs, source_segs, SourceMemImage_loaded_segments.
  cbn [forallb].
  assert (W0 : seg_writable SourceMemImage_segment_000 = false) by (vm_compute; reflexivity).
  assert (W1 : seg_writable SourceMemImage_segment_001 = false) by (vm_compute; reflexivity).
  assert (W2 : seg_writable SourceMemImage_segment_002 = false) by (vm_compute; reflexivity).
  assert (W3 : seg_writable SourceMemImage_segment_003 = true) by (vm_compute; reflexivity).
  rewrite W0, W1, W2, W3. cbn [orb].
  change (Z.of_N (seg_base SourceMemImage_segment_000)
          + Z.of_N (seg_size SourceMemImage_segment_000))%Z with 0x11000%Z.
  change (Z.of_N (seg_base SourceMemImage_segment_000))%Z with 0x10000%Z.
  change (Z.of_N (seg_base SourceMemImage_segment_001)
          + Z.of_N (seg_size SourceMemImage_segment_001))%Z with 0x12000%Z.
  change (Z.of_N (seg_base SourceMemImage_segment_001))%Z with 0x11000%Z.
  change (Z.of_N (seg_base SourceMemImage_segment_002)
          + Z.of_N (seg_size SourceMemImage_segment_002))%Z with 0x13000%Z.
  change (Z.of_N (seg_base SourceMemImage_segment_002))%Z with 0x12000%Z.
  destruct (source_free_cases b l Hfree Hl) as [Hc | Hc].
  - rewrite (proj2 (Z.ltb_ge 0x10000 (a + k))) by lia.
    rewrite (proj2 (Z.ltb_ge 0x11000 (a + k))) by lia.
    rewrite (proj2 (Z.ltb_ge 0x12000 (a + k))) by lia.
    reflexivity.
  - rewrite (proj2 (Z.ltb_ge a 0x11000)) by lia.
    rewrite (proj2 (Z.ltb_ge a 0x12000)) by lia.
    rewrite (proj2 (Z.ltb_ge a 0x13000)) by lia.
    rewrite !andb_false_r. reflexivity.
Qed.

(** Above every loaded segment (>= 0x14000): the ROM misses.  The image
    has four page-rounded segments under [-z separate-code]. *)
Lemma srom_none_hi : forall a : word, (0x14000 <= bv_unsigned a)%Z ->
  seg_rom source_segs a = None.
Proof.
  intros a Ha. pose proof (u64_range a).
  unfold seg_rom, memory_read.
  assert (Hfs : find_segment source_segs (bv_unsigned a) (Z.of_N 1) = None).
  { unfold source_segs, SourceMemImage_loaded_segments. cbn [find_segment].
    assert (T0 : (Z.of_N (seg_base SourceMemImage_segment_000)
                  + Z.of_N (seg_size SourceMemImage_segment_000))%Z = 0x11000%Z)
      by (vm_compute; reflexivity).
    assert (T1 : (Z.of_N (seg_base SourceMemImage_segment_001)
                  + Z.of_N (seg_size SourceMemImage_segment_001))%Z = 0x12000%Z)
      by (vm_compute; reflexivity).
    assert (T2 : (Z.of_N (seg_base SourceMemImage_segment_002)
                  + Z.of_N (seg_size SourceMemImage_segment_002))%Z = 0x13000%Z)
      by (vm_compute; reflexivity).
    assert (T3 : (Z.of_N (seg_base SourceMemImage_segment_003)
                  + Z.of_N (seg_size SourceMemImage_segment_003))%Z = 0x14000%Z)
      by (vm_compute; reflexivity).
    rewrite T0, T1, T2, T3.
    rewrite (proj2 (Z.leb_gt (bv_unsigned a + Z.of_N 1) 0x11000)) by lia.
    rewrite (proj2 (Z.leb_gt (bv_unsigned a + Z.of_N 1) 0x12000)) by lia.
    rewrite (proj2 (Z.leb_gt (bv_unsigned a + Z.of_N 1) 0x13000)) by lia.
    rewrite (proj2 (Z.leb_gt (bv_unsigned a + Z.of_N 1) 0x14000)) by lia.
    rewrite !andb_false_r. reflexivity. }
  rewrite Hfs. reflexivity.
Qed.

(* ================================================================= *)
(* Generic rdn helpers                                                *)
(* ================================================================= *)

(* The suffix step is [SeqExec.rdn_skipn] (imported above), not a local
   copy: this file used to carry one of its own, stating the same fact
   under a different binder order, so a bare [rdn_skipn] here and a bare
   [rdn_skipn] in any other example named different lemmas. *)

Lemma rdn_window : forall segs mem (a : word) n bs j k,
  rdn segs mem a n = Some bs -> (j + k <= n)%nat ->
  rdn segs mem (a + nat_to_word j) k = Some (firstn k (skipn j bs)).
Proof.
  intros segs mem a n bs j k H Hjk.
  pose proof (SeqExec.rdn_skipn segs mem n a bs j H ltac:(lia)) as Hs.
  apply (rdn_firstn segs mem (n - j) (a + nat_to_word j) (skipn j bs) k Hs).
  lia.
Qed.

Lemma zmem0 : forall mem (b : word), zmem mem b (Z_to_bv 64 0) = mem.
Proof.
  intros mem b. apply FunctionalExtensionality.functional_extensionality.
  intro a. apply zmem_out.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
Qed.


(* ================================================================= *)
(* The proof, generic over argv/envp and the stack pointer             *)
(* ================================================================= *)

Section SourceProof.

Variable inp : ProcInput.
Local Abbreviation av := (in_argv inp).
Local Abbreviation ev := (in_envp inp).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.

Variable rsp : word.

(** The entry stack draw this run was started with
    ([Run.ExecEntry]'s [en_draw]): the 16 AT_RANDOM bytes the kernel
    picks afresh at every [execve], and the bytes of the entry stack's
    last page above the block.  This proof may assume NOTHING about
    either, exactly as it may assume nothing about where the stack
    landed.  Quantified per binary, so the target's draw below is a
    different variable. *)
Variable rrnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned rsp)%Z.
Hypothesis Hsp_hi : (bv_unsigned rsp <= sp_window_hi)%Z.

Lemma rsp_lo_num : (0x7fff80000000 <= bv_unsigned rsp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma rsp_hi_num : (bv_unsigned rsp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

(** The quantified initial program break ([Run.valid_brk] window, like the
    SP above; alignment is not needed by this proof). *)
Variable rbrk : word.
Variable rmb : word.
Hypothesis Hvl : valid_launch inp.

(** The fifth conjunct of [Run.valid_entry_va]: this placement is one a
    Linux launch can give ([create_elf_tables] and [setup_arg_pages],
    fs/binfmt_elf.c and fs/exec.c, Linux v6.18.46).  With [Hvl] it bounds
    the entry block, places the argv strings below [ed_top] and the
    stack-store window. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry rsp rbrk rmb rrnd) inp.

(** The run's rom: the image's segments, then the vDSO pair. *)
Definition rrom : word -> option byte := seg_rom (run_segments source_segs inp rsp rmb).
Hypothesis Hbrk_lo :
  (reserved_top (segments_reserved source_segs) <= bv_unsigned rbrk)%Z.
Hypothesis Hbrk_hi :
  (bv_unsigned rbrk
   <= reserved_top (segments_reserved source_segs) + brk_aslr_max)%Z.

Lemma rtop_src_val : reserved_top (segments_reserved source_segs) = 0x14000%Z.
Proof. rewrite source_reserved_val. reflexivity. Qed.
Lemma rbrk_lo_num : (0x14000 <= bv_unsigned rbrk)%Z.
Proof. rewrite <- rtop_src_val. exact Hbrk_lo. Qed.
Lemma rbrk_hi_num : (bv_unsigned rbrk <= 0x14000 + 1073741824)%Z.
Proof. rewrite <- rtop_src_val, <- brk_aslr_max_val. exact Hbrk_hi. Qed.
Lemma rbrk_lt64 : (bv_unsigned rbrk < 2^64)%Z.
Proof. pose proof (u64_range rbrk). lia. Qed.

Definition argcN : word := len_word av.
(** The initial overlay, with the entry point [init_mkst] passes to it. *)
Definition wmem : word -> option byte :=
  wrap_mem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x111c8)) rsp rrnd.

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
Proof.
  pose proof (valid_argv_len av Hva).
  unfold argcN, len_word. apply u_Z2bv; lia.
Qed.

Lemma argcN_le : (bv_unsigned argcN <= 1024)%Z.
Proof. rewrite u_argcN. apply valid_argv_len. exact Hva. Qed.

(** No-overflow bound for the initial stack image, for any entry word. *)
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
  pose proof rsp_hi_num. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as Hlen.
  apply bv_eq. unfold envp_val, v_addi.
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
  wbytes wmem 0x13000 (word_to_le_bytes 8 envp_val).

(** main()'s 80-byte frame (stores in execution order; sp = rsp - 80).
    gcc 15 with [-fno-builtin] saves s0/ra/s1/s2 in that order — no call
    before the scan loop, so the four sd's run back to back before the
    argv[1] load. *)
Definition fmem : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes emem
    (Z_to_bv 64 (bv_unsigned rsp - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* sd s0, 64(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 8))  (word_to_le_bytes 8 (0x111f4 : word)))  (* sd ra, 72(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* sd s1, 56(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)).    (* sd s2, 48(sp) *)

Lemma rdn_emem_above : forall (a : word) n,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn source_segs emem a n = rdn source_segs wmem a n.
Proof.
  intros a n Ha Hn. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. unfold emem.
  rewrite rdn_wbytes_disjoint
    by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia).
  reflexivity.
Qed.

Lemma rdn_fmem_above : forall (a : word) n,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn source_segs fmem a n = rdn source_segs wmem a n.
Proof.
  intros a n Ha Hn. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. unfold fmem.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; u_norm; lia)).
  apply rdn_emem_above; assumption.
Qed.

Lemma rdn_wmem_stack : forall (a : word) n,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn source_segs wmem a n
  = rdn source_segs
      (stack_to_mem rsp (entry_stack_image inp rmb source_phdrs
                           (Z_to_bv 64 (Z.of_N 0x111c8)) rsp rrnd)) a n.
Proof. intros a n Ha Hn. apply rdn_wrap_stack_above; assumption. Qed.

(** argc at rsp. *)
Lemma read_argc_w :
  rdn source_segs wmem rsp 8%nat = Some (word_le8 argcN).
Proof.
  pose proof rsp_hi_num. rewrite rdn_wmem_stack by lia.
  apply read_argc. apply source_bsb_nw.
Qed.

(* ----------------------------------------------------------------- *)
(* argv[1] and its bytes                                              *)
(* ----------------------------------------------------------------- *)

Definition arg1 : list byte := nth 1 av [].
Definition nn : nat := length arg1.
Definition nN : word := nat_to_word nn.
Definition ptr : word := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1.

(** Room for a whole word past any byte of argv string [k], its NUL
    included: the later strings, the exec name and its NUL and the 8-byte
    slot lie above it, so at least 9 bytes from the NUL on (Linux v6.18.46
    fs/exec.c:1831-1840, mm/vma_exec.c:150; instance of MuslStrlen's
    [argv_ptr_room]). *)
Lemma source_ptr_room : forall k, (k < length av)%nat ->
  (bv_unsigned (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)
     + Z.of_nat (length (nth k av [])) + 9
   <= bv_unsigned rsp
      + Z.of_nat (length (entry_stack_image inp rmb source_phdrs
                            (Z_to_bv 64 (Z.of_N 0x111c8)) rsp rrnd)))%Z.
Proof. intros k Hk. eapply argv_ptr_room; eassumption. Qed.

(** argv[k]'s bytes, its NUL and the next seven bytes, read back from the
    initial stack image ([source_ptr_room]: at least eight bytes follow
    the NUL). *)
Lemma read_argv_str_tail : forall k, (k < length av)%nat ->
  exists tl, length tl = 7%nat /\
  rdn source_segs
      (stack_to_mem rsp (entry_stack_image inp rmb source_phdrs
                           (Z_to_bv 64 (Z.of_N 0x111c8)) rsp rrnd))
      (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)
      (length (nth k av []) + 8)
  = Some (nth k av [] ++ [Z_to_bv 8 0] ++ tl).
Proof.
  intros k Hk.
  pose proof (source_bsb_nw (Z_to_bv 64 (Z.of_N 0x111c8))) as Hnw.
  pose proof (source_ptr_room k Hk) as Hroom.
  destruct (bsb_byte_k inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x111c8)) rsp rrnd k Hk)
    as [pre [post [E Hlen]]].
  assert (Hptr : cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k
                 = rsp + nat_to_word (length pre)).
  { rewrite Hlen, (cat_argv_ptr_offset _ _ _ _ k Hk),
      (cat_string_base_offset Sv48 inp rmb rsp rbrk rrnd Hlau),
      nat_to_word_add_merge.
    reflexivity. }
  assert (HlenE : length (entry_stack_image inp rmb source_phdrs
                            (Z_to_bv 64 (Z.of_N 0x111c8)) rsp rrnd)
                  = (length pre + (length (nth k av []) + 1) + length post)%nat)
    by (rewrite E, !length_app; cbn [length]; lia).
  pose proof (u64_range rsp) as Hsp0.
  assert (Hntw : bv_unsigned (nat_to_word (length pre)) = Z.of_nat (length pre))
    by (apply u_ntw; lia).
  assert (Hu : bv_unsigned (rsp + nat_to_word (length pre))
               = (bv_unsigned rsp + Z.of_nat (length pre))%Z)
    by (rewrite u_add_small; rewrite Hntw; lia).
  rewrite Hptr, Hu, HlenE in Hroom.
  assert (Hpost : (7 <= length post)%nat) by lia.
  exists (firstn 7 post). split; [apply firstn_length_le; exact Hpost|].
  rewrite Hptr.
  apply (read_at_offset_image source_segs inp rmb source_phdrs
           (Z_to_bv 64 (Z.of_N 0x111c8)) rsp rrnd pre
           (nth k av [] ++ [Z_to_bv 8 0] ++ firstn 7 post) (skipn 7 post)).
  - rewrite E. rewrite <- !app_assoc. rewrite (firstn_skipn 7 post). reflexivity.
  - rewrite !length_app, length_firstn. cbn [length]. lia.
  - exact Hnw.
Qed.

Section Ge2.

Hypothesis Hge2 : (2 <= length av)%nat.

Lemma nN_le : (Z.of_nat nn <= 131071)%Z.
Proof. unfold nn, arg1. apply valid_argv_str_len; [exact Hva | lia]. Qed.

Lemma u_nN : bv_unsigned nN = Z.of_nat nn.
Proof. pose proof nN_le. unfold nN. apply u_ntw. lia. Qed.

Lemma arg1_nz : ~ In (Z_to_bv 8 0) arg1.
Proof. unfold arg1. apply valid_argv_str_nz; [exact Hva | lia]. Qed.

Lemma arg1_bytes : Forall (fun b : byte => (bv_unsigned b < 256)%Z) arg1.
Proof. unfold arg1. apply valid_argv_str_bytes; [exact Hva | lia]. Qed.

Lemma ptr_bounds :
  (bv_unsigned rsp <= bv_unsigned ptr)%Z /\
  (bv_unsigned ptr + Z.of_nat nn + 1 < 2^64)%Z.
Proof.
  unfold ptr, nn, arg1.
  exact (argv_ptr_bounds Sv48 inp rmb rsp rbrk rrnd 1 Hlau ltac:(lia)).
Qed.

Lemma ptr_lo : (bv_unsigned rsp <= bv_unsigned ptr)%Z.
Proof. exact (proj1 ptr_bounds). Qed.
Lemma ptr_hi : (bv_unsigned ptr + Z.of_nat nn + 1 < 2^64)%Z.
Proof. exact (proj2 ptr_bounds). Qed.

(** The uniform [nn + 8]-byte read-back needs the string, its NUL and
    seven further bytes to fit below 2^64 ([source_ptr_room]). *)
Lemma ptr_hi8 : (bv_unsigned ptr + Z.of_nat nn + 8 < 2^64)%Z.
Proof.
  pose proof (source_bsb_nw (Z_to_bv 64 (Z.of_N 0x111c8))) as Hbsb.
  pose proof (source_ptr_room 1 ltac:(lia)) as Hroom.
  fold arg1 in Hroom. fold nn in Hroom. fold ptr in Hroom. lia.
Qed.

Lemma read_str_f :
  rdn source_segs fmem ptr (S nn) = Some (arg1 ++ [Z_to_bv 8 0]).
Proof.
  destruct ptr_bounds as [Hlo Hhi].
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  rewrite rdn_fmem_above by lia.
  rewrite rdn_wmem_stack by lia.
  replace (S nn) with (nn + 1)%nat by lia.
  apply rdn_app.
  - unfold ptr, arg1, nn.
    apply (read_argv_str_k Sv48 source_segs inp rmb source_phdrs _ rsp rbrk rrnd 1 Hlau).
    lia.
  - pose proof (read_argv_byte_k Sv48 source_segs inp rmb source_phdrs
                  (Z_to_bv 64 (Z.of_N 0x111c8)) rsp rbrk rrnd 1 nn Hlau
                  ltac:(lia) ltac:(unfold nn, arg1; lia)) as Hbk.
    assert (Hb0 : nth nn (nth 1 av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)
                  = Z_to_bv 8 0).
    { change (nth nn (nth 1 av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))
        with (byte_at (nth 1 av []) nn).
      apply byte_at_len. }
    rewrite Hb0 in Hbk. exact Hbk.
Qed.

(** The same read-back extended by seven (unconstrained) spare bytes
    past the NUL. *)
Lemma read_str_f8 : exists tl, length tl = 7%nat /\
  rdn source_segs fmem ptr (nn + 8) = Some (arg1 ++ [Z_to_bv 8 0] ++ tl).
Proof.
  destruct ptr_bounds as [Hlo Hhi].
  pose proof ptr_hi8 as Hhi8.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  destruct (read_argv_str_tail 1 ltac:(lia)) as (tl & Htl & Hread).
  rewrite rdn_fmem_above by lia.
  rewrite rdn_wmem_stack by lia.
  exists tl. split; [exact Htl | exact Hread].
Qed.

End Ge2.

(* ----------------------------------------------------------------- *)
(* Frame-slot read-back                                               *)
(* ----------------------------------------------------------------- *)

Lemma read_slot_ra :
  rdn source_segs fmem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
  = Some (word_to_le_bytes 8 (0x111f4 : word)).
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. unfold fmem.
  repeat first
    [ rewrite rdn_wbytes_hit8 by (u_norm; lia)
    | rewrite rdn_wbytes_disjoint
        by (rewrite ?length_N_to_le_bytes; u_norm; lia)
    | rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; u_norm; lia) ].
  reflexivity.
Qed.

Lemma read_slot_0 : forall a : word,
  In a [Z_to_bv 64 (bv_unsigned rsp - 16); Z_to_bv 64 (bv_unsigned rsp - 24);
        Z_to_bv 64 (bv_unsigned rsp - 32)] ->
  rdn source_segs fmem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros a Ha. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. unfold fmem.
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
(* Epilogue: 0x11068 .. ret .. exit ecall                             *)
(* ================================================================= *)

Lemma source_epilogue : forall regs mem (code : word),
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
  reg_get regs 10 = code -> (bv_unsigned code < 256)%Z ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
  = Some (word_to_le_bytes 8 (0x111f4 : word)) ->
  (forall a : word,
     In a [Z_to_bv 64 (bv_unsigned rsp - 16); Z_to_bv 64 (bv_unsigned rsp - 24);
           Z_to_bv 64 (bv_unsigned rsp - 32)] ->
     rdn source_segs mem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  to_wexit source_segs (mkst regs 0x11068 mem rrom) [] code.
Proof.
  intros regs mem code H2 H10 Hc Hra Hsl.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  (* SEVEN instructions in one reflective block: the four callee-save
     reloads, the stack pop, the [ret] and crt's [li a7,93], stopping at
     the [exit] ecall.  The [ra] reload is NAMED in the read script,
     which is what lets the [ret] resolve to a literal pc. *)
  sym_block source_segs 12%nat (@nil bool) [ELit 0x111f4]
    [((2 : reg), EVar 32)] [Z_to_bv 64 (bv_unsigned rsp - 80)]
    (* the named read still consumes a variable slot, so the first entry
       is a placeholder and s0/s1/s2's zeros follow *)
    [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0] RA HRA.
  { (* [ld s2,48(sp)] *)
    exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hsl; right; right; left; reflexivity | apply bytes_le_to_Z_8 ]. }
  { (* [ld s1,56(sp)] *)
    exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hsl; right; left; reflexivity | apply bytes_le_to_Z_8 ]. }
  { (* [ld s0,64(sp)] *)
    exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hsl; left; reflexivity | apply bytes_le_to_Z_8 ]. }
  { (* [ld ra,72(sp)] -> main's return address *)
    exists (word_to_le_bytes 8 (0x111f4 : word)); split;
      [ exact Hra | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]. }
  { (* the [sp] pin *) exact H2. }
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_111f8 eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRA; sym_close.
  - sym_regs HRA; exact H10.
  - exact Hc.
Qed.

(* ================================================================= *)
(* _start and main's prologue                                         *)
(* ================================================================= *)

(** argc < 2: no output, exit 2. *)
Lemma source_wexit_lt2 : (length av < 2)%nat ->
  to_wexit source_segs
    (init_machine_state (run_segments source_segs inp rsp rmb) 0x111c8 source_phdrs rsp rmb rrnd inp)
    [] (Z_to_bv 64 2).
Proof.
  intros Hlt2.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as HargcLe.
  rewrite init_mkst. norm_pc.
  (* SIXTEEN instructions in one block: crt [_start] (gp setup, the argc
     load, the envp-pointer arithmetic and its store into musl's
     [__environ] slot, the [jal] into main), main's [bge] taken, the exit
     code and the [ret], and crt's exit tail, stopping at the [ecall]. *)
  sym_block source_segs 20%nat [true] (@nil expr)
    [((2 : reg), EVar 32)] [rsp] [argcN] RA HRA.
  { (* [bge a5,a0] taken: 1 >= argc *)
    rewrite negb_true_iff;
    rewrite bv_lts_small by (u_norm; rewrite ?u_argcN; lia);
    apply Z.ltb_ge; u_norm; rewrite u_argcN; lia. }
  { (* [sd a2,0(t1)] -> musl's [__environ] slot at 0x13000 *)
    apply source_store_ok; u_norm; lia. }
  { (* [ld a0,0(sp)] -> argc, out of the initial stack image *)
    replace (Z_to_bv 64 (bv_unsigned rsp + 0)) with rsp by (apply bv_eq; u_norm; lia);
    exists (word_le8 argcN); split;
      [ fold wmem; apply read_argc_w | apply bytes_le_n_to_le_8 ]. }
  eapply tw_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_111f8 eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRA; sym_close.
  - sym_regs HRA; sym_close.
  - vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* argc >= 2: main's prologue, then the inline byte-scan loop         *)
(* ================================================================= *)

Section Ge2Main.

Hypothesis Hge2 : (2 <= length av)%nat.

Lemma nN_le' : (Z.of_nat nn <= 131071)%Z.
Proof. apply nN_le. exact Hge2. Qed.
Lemma u_nN' : bv_unsigned nN = Z.of_nat nn.
Proof. apply u_nN. exact Hge2. Qed.
Lemma ptr_lo' : (bv_unsigned rsp <= bv_unsigned ptr)%Z.
Proof. apply ptr_lo. exact Hge2. Qed.
Lemma ptr_hi' : (bv_unsigned ptr + Z.of_nat nn + 1 < 2^64)%Z.
Proof. apply ptr_hi. exact Hge2. Qed.
Lemma ptr_hi8' : (bv_unsigned ptr + Z.of_nat nn + 8 < 2^64)%Z.
Proof. apply ptr_hi8. exact Hge2. Qed.

(** The address of the byte [j] into argv[1], with its unsigned value
    (the whole scanned window stays below 2^64 by [ptr_hi8']). *)
Lemma u_ptr_off : forall j, (j <= nn + 8)%nat ->
  bv_unsigned (ptr + nat_to_word j) = (bv_unsigned ptr + Z.of_nat j)%Z.
Proof.
  intros j Hj. pose proof ptr_hi8' as H8. pose proof (u64_range ptr).
  rewrite u_add_small; rewrite u_ntw by lia; lia.
Qed.

(* ----------------------------------------------------------------- *)
(* The inline byte-scan loop (gcc's -fno-builtin rendering of slen)   *)
(* ----------------------------------------------------------------- *)

(* --- the byte list the whole scan sees ---------------------------- *)

Lemma nth_full_lt : forall (tl : list byte) j, (j < nn)%nat ->
  nth j (arg1 ++ [Z_to_bv 8 0] ++ tl) (Z_to_bv 8 0) = nth j arg1 (Z_to_bv 8 0).
Proof. intros tl j Hj. apply app_nth1. unfold nn in Hj. exact Hj. Qed.

Lemma nth_full_nn : forall (tl : list byte),
  nth nn (arg1 ++ [Z_to_bv 8 0] ++ tl) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  intro tl. rewrite app_nth2 by (unfold nn; lia).
  unfold nn. rewrite Nat.sub_diag. reflexivity.
Qed.

(* --- reading bytes out of the stack image -------------------------- *)

Lemma sl_byte : forall mem (tl : list byte),
  rdn source_segs mem ptr (nn + 8) = Some (arg1 ++ [Z_to_bv 8 0] ++ tl) ->
  forall j, (j <= nn)%nat ->
  rdn source_segs mem (ptr + nat_to_word j) 1%nat
  = Some [nth j (arg1 ++ [Z_to_bv 8 0] ++ tl) (Z_to_bv 8 0)].
Proof.
  intros mem tl Hread j Hj.
  exact (rdn_nth source_segs mem (nn + 8) ptr _ j Hread ltac:(lia)).
Qed.

Lemma nth_arg1_nz : forall j, (j < nn)%nat ->
  nth j arg1 (Z_to_bv 8 0) <> Z_to_bv 8 0.
Proof.
  intros j Hj.
  rewrite <- (nth_lt_byte_at arg1 j) by (unfold nn in Hj; lia).
  apply byte_at_nz; [apply (arg1_nz Hge2) | unfold nn in Hj; lia].
Qed.

(** The inline byte-scan loop, from its head at 0x11024:
    [add a5,s2,s0 ; lbu a5,0(a5) ; bnez a5,0x11080] with the backedge
    [0x11080: addi s0,s0,1 ; j 0x11024].  With [-fno-builtin] gcc keeps
    the C source's hand-written loop: it reads exactly the bytes of
    argv[1] up to and including the NUL — no overread here (the
    fixture's deliberate out-of-bounds read lives in the byte-sum loop
    over the brk grant, below).  Advances [s0] from [j] to [nn] and
    falls through to 0x11030 on the NUL, clobbering only s0 and a5. *)
Lemma source_slen_loop : forall mem (tl : list byte),
  rdn source_segs mem ptr (nn + 8) = Some (arg1 ++ [Z_to_bv 8 0] ++ tl) ->
  forall d j regs, (j + d = nn)%nat ->
  reg_get regs 18 = ptr ->
  reg_get regs 8 = nat_to_word j ->
  exists regs',
    (forall r : reg, r <> 8 -> r <> 15 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 8 = nN /\
    msteps source_segs (mkst regs 0x11024 mem rrom) (mkst regs' 0x11030 mem rrom).
Proof.
  intros mem tl Hread.
  pose proof nN_le' as HnnLe. pose proof ptr_hi8' as H8.
  pose proof (u64_range ptr) as Hup.
  induction d as [|d IH]; intros j regs Hjd Hr18 Hr8.
  - (* j = nn: the NUL, fall through to 0x11030 *)
    assert (Hj : j = nn) by lia.
    (* 0x11024 add a5,s2,s0 : a5 = ptr + nn *)
    set (regs1 := regupd regs 15 (ptr + nat_to_word j)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11024 mem rrom)
                 = MachineOk (mkst regs1 0x11028 mem rrom)).
    { rewrite (step_add_at source_segs regs 0x11024 mem rrom _ 15 18 8
                 (ptr + nat_to_word j) SF_11024 eq_refl SD_11024 eq_refl).
      - wlits. reflexivity.
      - getr_resolve. rewrite Hr18, Hr8. reflexivity. }
    (* 0x11028 lbu a5,0(a5) : the NUL *)
    set (regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0)))).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x11028 mem rrom)
                 = MachineOk (mkst regs2 0x1102c mem rrom)).
    { rewrite (step_lbu source_segs regs1 0x11028 mem rrom _ 15 15 _ (Z_to_bv 8 0)
                 SF_11028 eq_refl SD_11028).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite v_addi_0.
        rewrite (sl_byte mem tl Hread j ltac:(lia)).
        rewrite Hj, nth_full_nn. reflexivity. }
    (* 0x1102c bnez a5 : not taken, exit the loop *)
    assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x1102c mem rrom)
                 = MachineOk (mkst regs2 0x11030 mem rrom)).
    { rewrite (step_bne_ft source_segs regs2 0x1102c mem rrom _ 15 0 _
                 SF_1102c eq_refl SD_1102c).
      - wlits. reflexivity.
      - unfold regs2. getr_resolve. exact c_eq_0_true. }
    exists regs2. split; [|split].
    + intros r Hra Hrb. unfold regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs2, regs1. rewrite !regupd_other by reg_neq_tac.
      rewrite Hr8, Hj. reflexivity.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      apply mst_refl.
  - (* j < nn: a nonzero byte, take the backedge *)
    assert (Hjn : (j < nn)%nat) by lia.
    set (b := nth j arg1 (Z_to_bv 8 0)).
    assert (Hbnz : b <> Z_to_bv 8 0) by (unfold b; apply nth_arg1_nz; lia).
    (* 0x11024 add a5,s2,s0 : a5 = ptr + j *)
    set (regs1 := regupd regs 15 (ptr + nat_to_word j)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11024 mem rrom)
                 = MachineOk (mkst regs1 0x11028 mem rrom)).
    { rewrite (step_add_at source_segs regs 0x11024 mem rrom _ 15 18 8
                 (ptr + nat_to_word j) SF_11024 eq_refl SD_11024 eq_refl).
      - wlits. reflexivity.
      - getr_resolve. rewrite Hr18, Hr8. reflexivity. }
    (* 0x11028 lbu a5,0(a5) : the (nonzero) byte *)
    set (regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned b))).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x11028 mem rrom)
                 = MachineOk (mkst regs2 0x1102c mem rrom)).
    { rewrite (step_lbu source_segs regs1 0x11028 mem rrom _ 15 15 _ b
                 SF_11028 eq_refl SD_11028).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite v_addi_0.
        rewrite (sl_byte mem tl Hread j ltac:(lia)).
        rewrite nth_full_lt by lia. reflexivity. }
    (* 0x1102c bnez a5 : taken -> 0x11080 *)
    assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x1102c mem rrom)
                 = MachineOk (mkst regs2 0x11080 mem rrom)).
    { rewrite (step_bne_tk source_segs regs2 0x1102c mem rrom _ 15 0 _
                 SF_1102c eq_refl SD_1102c).
      - wlits. reflexivity.
      - unfold regs2. getr_resolve. apply c_eq_0_false.
        rewrite u_zext8. apply byte_nz_u. exact Hbnz. }
    (* 0x11080 addi s0,s0,1 *)
    set (regs3 := regupd regs2 8 (nat_to_word (S j))).
    assert (E4 : RiscvSemantics.step source_segs (mkst regs2 0x11080 mem rrom)
                 = MachineOk (mkst regs3 0x11084 mem rrom)).
    { rewrite (step_addi_at source_segs regs2 0x11080 mem rrom _ 8 8 _
                 (nat_to_word (S j)) SF_11080 eq_refl SD_11080 eq_refl).
      - wlits. reflexivity.
      - unfold regs2, regs1. getr_resolve. rewrite Hr8.
        rewrite v_addi_Sj by lia. reflexivity. }
    (* 0x11084 j 0x11024 : the backedge *)
    assert (E5 : RiscvSemantics.step source_segs (mkst regs3 0x11084 mem rrom)
                 = MachineOk (mkst regs3 0x11024 mem rrom)).
    { rewrite (step_jal_x0 source_segs regs3 0x11084 mem rrom _ _
                 SF_11084 eq_refl SD_11084). wlits. reflexivity. }
    assert (Hr18' : reg_get regs3 18 = ptr).
    { unfold regs3, regs2, regs1. rewrite !regupd_other by reg_neq_tac.
      exact Hr18. }
    assert (Hr8' : reg_get regs3 8 = nat_to_word (S j))
      by (unfold regs3; apply regupd_same).
    destruct (IH (S j) regs3 ltac:(lia) Hr18' Hr8') as (regs' & Hag & H8' & Hms).
    exists regs'. split; [|split].
    + intros r Hra Hrb. rewrite (Hag r Hra Hrb).
      unfold regs3, regs2, regs1. rewrite !regupd_other by assumption. reflexivity.
    + exact H8'.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      exact Hms.
Qed.

(* ================================================================= *)
(* Entry -> the scan loop -> back at 0x11030 with s0 = n              *)
(* ================================================================= *)

(** From the entry point to the head of the byte-scan loop at 0x11024,
    with main's frame pushed, [s2] = argv[1] and [s0] = 0. *)
Lemma source_to_loop :
  exists regs1,
    reg_get regs1 2 = Z_to_bv 64 (bv_unsigned rsp - 80) /\
    reg_get regs1 8 = nat_to_word 0 /\
    reg_get regs1 18 = ptr /\
    msteps source_segs
      (init_machine_state (run_segments source_segs inp rsp rmb) 0x111c8 source_phdrs rsp rmb rrnd inp)
      (mkst regs1 0x11024 fmem rrom).
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as HargcLe.
  pose proof ptr_lo' as Hplo. pose proof ptr_hi' as Hphi. pose proof nN_le' as HnnLe.
  eexists. repeat split.
  4: {
  rewrite init_mkst. norm_pc.
  stepi SF_111c8 SD_111c8.
  stepi SF_111cc SD_111cc.
  eapply mst_step;
    [ reflexivity
    | eapply step_ld with (bs := word_le8 argcN) (v := argcN);
      [ exact SF_111d0 | reflexivity | exact SD_111d0
      | match goal with |- rdn _ _ ?a _ = _ =>
          replace a with rsp
            by (getr_resolve; regupd_resolve; cbv beta; reduce_bv_eqb_ifs;
                rewrite v_addi_0; reflexivity) end;
        fold wmem; apply read_argc_w
      | exact (bytes_le_n_to_le_8 _) ]
    | step_simpl ].
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 (bv_unsigned rsp + 8));
      [ exact SF_111d4 | reflexivity | exact SD_111d4 | reflexivity
      | getr_resolve; regupd_resolve; cbv beta; reduce_bv_eqb_ifs; sp_norm; f_equal; lia ]
    | norm_pc ].
  stepi SF_111d8 SD_111d8.
  eapply mst_step;
    [ reflexivity
    | eapply step_add_at with (v := v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (v_slli argcN 3));
      [ exact SF_111dc | reflexivity | exact SD_111dc | reflexivity
      | getr_resolve; regupd_resolve; reflexivity ]
    | norm_pc ].
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := envp_val);
      [ exact SF_111e0 | reflexivity | exact SD_111e0 | reflexivity
      | getr_resolve; regupd_resolve; exact envp_val_eq ]
    | norm_pc ].
  stepi SF_111e4 SD_111e4.
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := (0x13000 : word));
      [ exact SF_111e8 | reflexivity | exact SD_111e8 | reflexivity
      | getr_resolve; regupd_resolve; bveq ]
    | norm_pc ].
  eapply mst_step;
    [ reflexivity
    | eapply step_sd_at with (a := (0x13000 : word)) (v := envp_val);
      [ exact SF_111ec | reflexivity | exact SD_111ec
      | getr_resolve; regupd_resolve; rewrite v_addi_0; reflexivity
      | getr_resolve; regupd_resolve; reflexivity
      | apply source_store_ok; imm_norm; lia ]
    | step_simpl ].
  eapply mst_step;
    [ reflexivity
    | eapply step_jal_link;
      [ exact SF_111f0 | reflexivity | exact SD_111f0 ]
    | step_simpl ].
  (* main: li a5,1 ; bge fall-through (argc >= 2) *)
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 1);
      [ exact SF_11000 | reflexivity | exact SD_11000 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  eapply mst_step;
    [ reflexivity
    | eapply step_bge_ft;
      [ exact SF_11004 | reflexivity | exact SD_11004
      | getr_resolve; regupd_resolve;
        rewrite c_lts_small by (u_norm; rewrite ?u_argcN; lia);
        apply Z.ltb_lt; u_norm; rewrite u_argcN; lia ]
    | norm_pc ].
  (* addi sp, sp, -80 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 (bv_unsigned rsp - 80));
      [ exact SF_11008 | reflexivity | exact SD_11008 | reflexivity
      | getr_resolve; regupd_resolve; cbv beta; reduce_bv_eqb_ifs; sp_norm; f_equal; lia ]
    | norm_pc ].
  (* sd s0, 64(sp) -> rsp-16 : 0 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned rsp - 16)) (v := Z_to_bv 64 0);
      [ exact SF_1100c | reflexivity | exact SD_1100c
      | getr_resolve; regupd_resolve; sp_norm; f_equal; lia
      | getr_resolve; regupd_resolve; cbv beta; reduce_bv_eqb_ifs; reflexivity
      | solve_store_ok_inv ]
    | step_simpl ].
  (* sd ra, 72(sp) -> rsp-8 : 0x111f4 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned rsp - 8)) (v := (0x111f4 : word));
      [ exact SF_11010 | reflexivity | exact SD_11010
      | getr_resolve; regupd_resolve; sp_norm; f_equal; lia
      | getr_resolve; regupd_resolve; bveq
      | solve_store_ok_inv ]
    | step_simpl ].
  (* sd s1, 56(sp) -> rsp-24 : 0 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned rsp - 24)) (v := Z_to_bv 64 0);
      [ exact SF_11014 | reflexivity | exact SD_11014
      | getr_resolve; regupd_resolve; sp_norm; f_equal; lia
      | getr_resolve; regupd_resolve; cbv beta; reduce_bv_eqb_ifs; reflexivity
      | solve_store_ok_inv ]
    | step_simpl ].
  (* sd s2, 48(sp) -> rsp-32 : 0 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned rsp - 32)) (v := Z_to_bv 64 0);
      [ exact SF_11018 | reflexivity | exact SD_11018
      | getr_resolve; regupd_resolve; sp_norm; f_equal; lia
      | getr_resolve; regupd_resolve; cbv beta; reduce_bv_eqb_ifs; reflexivity
      | solve_store_ok_inv ]
    | step_simpl ].
  (* ld s2, 8(a1) -- argv[1] pointer *)
  eapply mst_step;
    [ reflexivity
    | eapply step_ld with (bs := word_le8 ptr) (v := ptr);
      [ exact SF_1101c | reflexivity | exact SD_1101c
      | match goal with |- rdn _ _ ?a _ = _ =>
          replace a with (rsp + nat_to_word (8 + 8 * 1))
            by (getr_resolve; regupd_resolve; rewrite word_add_nat; sp_norm; f_equal; lia) end;
        rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes, ?word_add_nat; imm_norm; u_norm; lia);
        rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes, ?word_add_nat; imm_norm; u_norm; lia);
        rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes, ?word_add_nat; imm_norm; u_norm; lia);
        rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes, ?word_add_nat; imm_norm; u_norm; lia);
        rewrite rdn_emem_above by (rewrite ?word_add_nat; u_norm; lia);
        rewrite rdn_wmem_stack by (rewrite ?word_add_nat; u_norm; lia);
        unfold ptr; apply read_argv_ptr_k; [lia | apply source_bsb_nw]
      | exact (bytes_le_n_to_le_8 _) ]
    | step_simpl ].
  (* li s0, 0 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11020 | reflexivity | exact SD_11020 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  fold wmem. fold emem.
  match goal with
  |- msteps _ (mkst _ _ ?m _) (mkst _ _ ?m' _) =>
      replace m' with m by reflexivity
  end.
  apply mst_refl. }
  all: getr_resolve; regupd_resolve; first [ reflexivity | bveq ].
Qed.

(** After the scan loop exits: [s0] = n, [s2] = argv[1]. *)
Lemma source_after_strlen :
  exists regs2,
    reg_get regs2 2 = Z_to_bv 64 (bv_unsigned rsp - 80) /\
    reg_get regs2 8 = nN /\
    reg_get regs2 18 = ptr /\
    msteps source_segs
      (init_machine_state (run_segments source_segs inp rsp rmb) 0x111c8 source_phdrs rsp rmb rrnd inp)
      (mkst regs2 0x11030 fmem rrom).
Proof.
  destruct source_to_loop as (regs1 & H2 & H8 & H18 & Hms1).
  destruct (read_str_f8 Hge2) as (tl & Htl & Hread).
  destruct (source_slen_loop fmem tl Hread nn 0%nat regs1 ltac:(lia) H18 H8)
    as (regsS & HagS & HS8 & HmsS).
  exists regsS. split; [|split; [|split]].
  - rewrite (HagS 2) by reg_neq_tac. exact H2.
  - exact HS8.
  - rewrite (HagS 18) by reg_neq_tac. exact H18.
  - eapply msteps_trans; [exact Hms1 | exact HmsS].
Qed.

(** n > 65536: no output, exit 3. *)
Lemma source_wexit_cap : (65536 < Z.of_nat nn)%Z ->
  to_wexit source_segs
    (init_machine_state (run_segments source_segs inp rsp rmb) 0x111c8 source_phdrs rsp rmb rrnd inp)
    [] (Z_to_bv 64 3).
Proof.
  intros Hcap.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le' as HnnLe.
  destruct source_after_strlen as (regs2 & H2 & H8 & H18 & Hms).
  eapply msteps_to_wexit; [exact Hms|].
  (* lui a5, 0x10 -> 65536 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_lui_at with (v := Z_to_bv 64 0x10000);
      [ exact SF_11030 | reflexivity | exact SD_11030 | reflexivity | bveq ]
    | norm_pc ].
  (* li a0, 3 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 3);
      [ exact SF_11034 | reflexivity | exact SD_11034 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* bltu a5, s0 taken (65536 < n) -> 0x11068 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_bltu_tk;
      [ exact SF_11038 | reflexivity | exact SD_11038
      | getr_resolve; regupd_resolve; rewrite H8;
        rewrite c_ltu_ltb; apply Z.ltb_lt; u_norm; rewrite ?u_nN'; lia ]
    | norm_pc ].
  apply source_epilogue.
  - regupd_resolve. exact H2.
  - regupd_resolve. reflexivity.
  - vm_compute. reflexivity.
  - apply read_slot_ra.
  - apply read_slot_0.
Qed.

(* ================================================================= *)
(* Exit-4 leaf: 0x11064                                               *)
(* ================================================================= *)

Lemma source_exit4 : forall regs mem,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
  = Some (word_to_le_bytes 8 (0x111f4 : word)) ->
  (forall a : word,
     In a [Z_to_bv 64 (bv_unsigned rsp - 16); Z_to_bv 64 (bv_unsigned rsp - 24);
           Z_to_bv 64 (bv_unsigned rsp - 32)] ->
     rdn source_segs mem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  to_wexit source_segs (mkst regs 0x11064 mem rrom) [] (Z_to_bv 64 4).
Proof.
  intros regs mem H2 Hra Hsl.
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 4);
      [ exact SF_11064 | reflexivity | exact SD_11064 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  apply source_epilogue.
  - regupd_resolve. exact H2.
  - regupd_resolve. reflexivity.
  - vm_compute. reflexivity.
  - exact Hra.
  - exact Hsl.
Qed.

(* ================================================================= *)
(* Entry to the first brk ecall                                       *)
(* ================================================================= *)

Lemma source_to_brk1 : (Z.of_nat nn <= 65536)%Z ->
  exists regs3,
    reg_get regs3 1 = (0x1105c : word) /\
    reg_get regs3 2 = Z_to_bv 64 (bv_unsigned rsp - 80) /\
    reg_get regs3 8 = nN /\
    reg_get regs3 10 = Z_to_bv 64 0 /\
    reg_get regs3 17 = Z_to_bv 64 214 /\
    reg_get regs3 18 = ptr /\
    msteps source_segs
      (init_machine_state (run_segments source_segs inp rsp rmb) 0x111c8 source_phdrs rsp rmb rrnd inp)
      {| ms_regs := regs3; ms_fregs := fp_regs; ms_pc_val := (0x11218 : word);
         ms_svc_pending := Some (Z_to_bv 64 214); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := fmem; ms_rom := rrom |}.
Proof.
  intros Hncap.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le' as HnnLe.
  destruct source_after_strlen as (regs2 & H2 & H8 & H18 & Hms).
  eexists. repeat split.
  7: {
  eapply msteps_trans; [exact Hms|].
  (* lui a5, 0x10 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_lui_at with (v := Z_to_bv 64 0x10000);
      [ exact SF_11030 | reflexivity | exact SD_11030 | reflexivity | bveq ]
    | norm_pc ].
  (* li a0, 3 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 3);
      [ exact SF_11034 | reflexivity | exact SD_11034 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* bltu a5, s0 fall-through (n <= 65536) *)
  eapply mst_step;
    [ reflexivity
    | eapply step_bltu_ft;
      [ exact SF_11038 | reflexivity | exact SD_11038
      | getr_resolve; regupd_resolve; rewrite H8;
        rewrite c_ltu_ltb; apply Z.ltb_ge; u_norm; rewrite ?u_nN'; lia ]
    | norm_pc ].
  (* li a6..a1 := 0 ; li a0 := 214 *)
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_1103c | reflexivity | exact SD_1103c | reflexivity | getr_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11040 | reflexivity | exact SD_11040 | reflexivity | getr_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11044 | reflexivity | exact SD_11044 | reflexivity | getr_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11048 | reflexivity | exact SD_11048 | reflexivity | getr_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_1104c | reflexivity | exact SD_1104c | reflexivity | getr_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11050 | reflexivity | exact SD_11050 | reflexivity | getr_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 214);
      [ exact SF_11054 | reflexivity | exact SD_11054 | reflexivity | getr_resolve; bveq ] | norm_pc ].
  (* jal ra, raw_syscall *)
  eapply mst_step;
    [ reflexivity | eapply step_jal_link; [ exact SF_11058 | reflexivity | exact SD_11058 ] | step_simpl ].
  (* raw_syscall: the seven moves *)
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 214);
      [ exact SF_111fc | reflexivity | exact SD_111fc | reflexivity | getr_resolve; regupd_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11200 | reflexivity | exact SD_11200 | reflexivity | getr_resolve; regupd_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11204 | reflexivity | exact SD_11204 | reflexivity | getr_resolve; regupd_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11208 | reflexivity | exact SD_11208 | reflexivity | getr_resolve; regupd_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_1120c | reflexivity | exact SD_1120c | reflexivity | getr_resolve; regupd_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11210 | reflexivity | exact SD_11210 | reflexivity | getr_resolve; regupd_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11214 | reflexivity | exact SD_11214 | reflexivity | getr_resolve; regupd_resolve; apply v_addi_0 ] | norm_pc ].
  (* ecall *)
  eapply mst_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_11218 eq_refl) | ].
  match goal with
  | |- msteps _ {| ms_regs := ?R; ms_fregs := _; ms_pc_val := _; ms_svc_pending := _;
                   ms_resv := _; ms_fcsr := _; ms_mem := _; ms_rom := _ |} _ =>
      replace (getr R 17) with (Z_to_bv 64 214)
        by (getr_resolve; regupd_resolve; bveq)
  end.
  apply mst_refl. }
  - regupd_resolve. bveq.
  - regupd_resolve. exact H2.
  - regupd_resolve. exact H8.
  - regupd_resolve. reflexivity.
  - regupd_resolve. bveq.
  - regupd_resolve. exact H18.
Qed.

(* ================================================================= *)
(* From the return of the first brk to the second brk ecall            *)
(* ================================================================= *)

(** gcc 15 keeps the requested break in a stack slot ([8(sp)]) across
    the second [brk] instead of a callee-saved register, so the frame
    gains an eighth live byte range at [rsp-72]. *)
Definition fmem2 (r : word) : word -> option byte :=
  wbytes fmem (Z_to_bv 64 (bv_unsigned rsp - 72)) (word_to_le_bytes 8 (r + nN)).

Lemma fmem2_above : forall r (x : word), (bv_unsigned rsp - 64 <= bv_unsigned x)%Z ->
  fmem2 r x = fmem x.
Proof.
  intros r x Hx. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  unfold fmem2. apply wbytes_above.
  rewrite length_N_to_le_bytes. u_norm. lia.
Qed.

Lemma fmem2_below : forall r (x : word), (bv_unsigned x < bv_unsigned rsp - 72)%Z ->
  fmem2 r x = fmem x.
Proof.
  intros r x Hx. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  unfold fmem2. apply wbytes_below.
  - rewrite length_N_to_le_bytes. u_norm. lia.
  - u_norm. lia.
Qed.

Lemma read_slot_ra2 : forall r,
  rdn source_segs (fmem2 r) (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
  = Some (word_to_le_bytes 8 (0x111f4 : word)).
Proof.
  intro r. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  erewrite rdn_ext; [ exact read_slot_ra | u_norm; lia | ].
  intros x Hx. apply fmem2_above. revert Hx. u_norm. lia.
Qed.

Lemma read_slot_02 : forall r (a : word),
  In a [Z_to_bv 64 (bv_unsigned rsp - 16); Z_to_bv 64 (bv_unsigned rsp - 24);
        Z_to_bv 64 (bv_unsigned rsp - 32)] ->
  rdn source_segs (fmem2 r) a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros r a Ha. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  assert (Hab : (bv_unsigned rsp - 32 <= bv_unsigned a <= bv_unsigned rsp - 16)%Z)
    by (repeat destruct Ha as [<-|Ha]; try (exfalso; exact Ha); u_norm; lia).
  erewrite rdn_ext; [ apply read_slot_0; exact Ha | u_norm; lia | ].
  intros x Hx. apply fmem2_above. lia.
Qed.

Lemma read_str_f8_2 : forall r, exists tl, length tl = 7%nat /\
  rdn source_segs (fmem2 r) ptr (nn + 8) = Some (arg1 ++ [Z_to_bv 8 0] ++ tl).
Proof.
  intro r. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof ptr_lo' as Hplo. pose proof ptr_hi8' as Hphi.
  destruct (read_str_f8 Hge2) as (tl & Htl & Hread).
  exists tl. split; [exact Htl|].
  erewrite rdn_ext; [ exact Hread | lia | ].
  intros x Hx. apply fmem2_above. lia.
Qed.

Lemma source_to_brk2 : forall regs3 (r : word),
  reg_get regs3 1 = (0x1105c : word) ->
  reg_get regs3 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
  reg_get regs3 8 = nN ->
  reg_get regs3 18 = ptr ->
  r <> Z_to_bv 64 0 ->
  (bv_unsigned r + Z.of_nat nn < 2^64)%Z ->
  exists regs5,
    reg_get regs5 1 = (0x110b0 : word) /\
    reg_get regs5 2 = Z_to_bv 64 (bv_unsigned rsp - 80) /\
    reg_get regs5 8 = nN /\
    reg_get regs5 9 = r /\
    reg_get regs5 10 = r + nN /\
    reg_get regs5 17 = Z_to_bv 64 214 /\
    reg_get regs5 18 = ptr /\
    msteps source_segs (mkst (regupd regs3 10 r) 0x1121c fmem rrom)
      {| ms_regs := regs5; ms_fregs := fp_regs; ms_pc_val := (0x11218 : word);
         ms_svc_pending := Some (Z_to_bv 64 214); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := fmem2 r; ms_rom := rrom |}.
Proof.
  intros regs3 r H1 H2 H8 H18 Hrnz Hw.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le' as HnnLe.
  pose proof (u64_range r) as Hur.
  pose proof (word_neq0_unsigned r Hrnz) as Hur0.
  assert (Hurn : bv_unsigned (r + nN) = (bv_unsigned r + Z.of_nat nn)%Z).
  { rewrite u_add_small; rewrite u_nN'; lia. }
  eexists. repeat split.
  8: {
  (* ret -> 0x1105c *)
  eapply mst_step;
    [ reflexivity
    | eapply step_jalr_x0 with (tgt := (0x1105c : word));
      [ exact SF_1121c | reflexivity | exact SD_1121c | getr_resolve; regupd_resolve; exact H1 ]
    | norm_pc ].
  (* mv s1, a0 : s1 = r *)
  eapply mst_step;
    [ reflexivity
    | eapply step_addi_at with (v := r);
      [ exact SF_1105c | reflexivity | exact SD_1105c | reflexivity
      | getr_resolve; regupd_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* bnez a0 taken -> 0x11088 *)
  eapply mst_step;
    [ reflexivity
    | eapply step_bne_tk;
      [ exact SF_11060 | reflexivity | exact SD_11060
      | getr_resolve; regupd_resolve; apply c_eq_0_false; exact Hur0 ]
    | norm_pc ].
  (* add a1, a0, s0 : a1 = r + n *)
  eapply mst_step;
    [ reflexivity
    | eapply step_add_at with (v := r + nN);
      [ exact SF_11088 | reflexivity | exact SD_11088 | reflexivity
      | getr_resolve; regupd_resolve; rewrite H8; reflexivity ]
    | norm_pc ].
  (* bltu a1, a0 fall-through (r <= r + n) *)
  eapply mst_step;
    [ reflexivity
    | eapply step_bltu_ft;
      [ exact SF_1108c | reflexivity | exact SD_1108c
      | getr_resolve; regupd_resolve;
        rewrite c_ltu_ltb, Hurn; apply Z.ltb_ge; lia ]
    | norm_pc ].
  (* li a5,a6,a4,a3,a2 := 0 ; li a0 := 214 *)
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11090 | reflexivity | exact SD_11090 | reflexivity | getr_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11094 | reflexivity | exact SD_11094 | reflexivity | getr_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11098 | reflexivity | exact SD_11098 | reflexivity | getr_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_1109c | reflexivity | exact SD_1109c | reflexivity | getr_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_110a0 | reflexivity | exact SD_110a0 | reflexivity | getr_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 214);
      [ exact SF_110a4 | reflexivity | exact SD_110a4 | reflexivity | getr_resolve; bveq ] | norm_pc ].
  (* sd a1, 8(sp) : the requested break, spilled *)
  eapply mst_step;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned rsp - 72)) (v := r + nN);
      [ exact SF_110a8 | reflexivity | exact SD_110a8
      | getr_resolve; regupd_resolve; rewrite H2; sp_norm; f_equal; lia
      | getr_resolve; regupd_resolve; reflexivity
      | solve_store_ok_inv ]
    | step_simpl ].
  fold (fmem2 r).
  (* jal ra, raw_syscall *)
  eapply mst_step;
    [ reflexivity | eapply step_jal_link; [ exact SF_110ac | reflexivity | exact SD_110ac ] | step_simpl ].
  (* raw_syscall: the seven moves *)
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 214);
      [ exact SF_111fc | reflexivity | exact SD_111fc | reflexivity | getr_resolve; regupd_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := r + nN);
      [ exact SF_11200 | reflexivity | exact SD_11200 | reflexivity | getr_resolve; regupd_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11204 | reflexivity | exact SD_11204 | reflexivity | getr_resolve; regupd_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11208 | reflexivity | exact SD_11208 | reflexivity | getr_resolve; regupd_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_1120c | reflexivity | exact SD_1120c | reflexivity | getr_resolve; regupd_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11210 | reflexivity | exact SD_11210 | reflexivity | getr_resolve; regupd_resolve; apply v_addi_0 ] | norm_pc ].
  eapply mst_step; [ reflexivity | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11214 | reflexivity | exact SD_11214 | reflexivity | getr_resolve; regupd_resolve; apply v_addi_0 ] | norm_pc ].
  (* ecall *)
  eapply mst_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_11218 eq_refl) | ].
  match goal with
  | |- msteps _ {| ms_regs := ?R; ms_fregs := _; ms_pc_val := _; ms_svc_pending := _;
                   ms_resv := _; ms_fcsr := _; ms_mem := _; ms_rom := _ |} _ =>
      replace (getr R 17) with (Z_to_bv 64 214)
        by (getr_resolve; regupd_resolve; bveq)
  end.
  apply mst_refl. }
  - regupd_resolve. bveq.
  - regupd_resolve. exact H2.
  - regupd_resolve. exact H8.
  - regupd_resolve. reflexivity.
  - regupd_resolve. reflexivity.
  - regupd_resolve. bveq.
  - regupd_resolve. exact H18.
Qed.

(* ================================================================= *)
(* Reading the '\n' constant from rodata (0x12000)                    *)
(* ================================================================= *)

Lemma wmem_nl_none : wmem (0x12000 : word) = None.
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  unfold wmem.
  apply (wrap_mem_below Sv48 inp rmb source_phdrs _ rsp rbrk rrnd _ Hlau).
  change (bv_unsigned (0x12000 : word)) with 0x12000%Z. lia.
Qed.

Lemma read_newline : forall (mem : word -> option byte),
  mem (0x12000 : word) = None ->
  rdn source_segs mem (0x12000 : word) 1%nat = Some [Z_to_bv 8 10].
Proof.
  intros mem Hn. cbn [rdn]. rewrite Hn.
  replace (seg_rom source_segs (0x12000 : word)) with (Some (Z_to_bv 8 10)).
  - reflexivity.
  - symmetry.
    apply (@bool_decide_eq_true_1 (seg_rom source_segs (0x12000 : word) = Some (Z_to_bv 8 10)) _).
    vm_cast_no_check (@eq_refl bool true).
Qed.

Lemma fmem_none : forall a : word,
  (bv_unsigned a < bv_unsigned rsp - stack_max_size)%Z ->
  (bv_unsigned a < 0x13000 \/ 0x13008 <= bv_unsigned a)%Z ->
  fmem a = None.
Proof.
  intros a Hlo Hgap.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. rewrite stack_max_size_val in Hlo.
  unfold fmem.
  rewrite !(wbytes_below (word_to_le_bytes 8 _)) by (rewrite ?length_N_to_le_bytes; u_norm; lia).
  unfold emem.
  assert (He : wbytes wmem (0x13000 : word) (word_to_le_bytes 8 envp_val) a = wmem a).
  { destruct Hgap as [Hg | Hg].
    - apply wbytes_below.
      + rewrite length_N_to_le_bytes.
        change (bv_unsigned (0x13000 : word)) with 0x13000%Z. lia.
      + change (bv_unsigned (0x13000 : word)) with 0x13000%Z. lia.
    - apply wbytes_above. rewrite length_N_to_le_bytes.
      change (bv_unsigned (0x13000 : word)) with 0x13000%Z. lia. }
  rewrite He.
  unfold wmem.
  apply (wrap_mem_below Sv48 inp rmb source_phdrs _ rsp rbrk rrnd _ Hlau).
  rewrite stack_max_size_val. lia.
Qed.

Lemma fmem2_none : forall r (a : word),
  (bv_unsigned a < bv_unsigned rsp - stack_max_size)%Z ->
  (bv_unsigned a < 0x13000 \/ 0x13008 <= bv_unsigned a)%Z ->
  fmem2 r a = None.
Proof.
  intros r a Hlo Hgap. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  rewrite stack_max_size_val in Hlo.
  rewrite fmem2_below by lia.
  apply fmem_none; [rewrite stack_max_size_val; lia | exact Hgap].
Qed.

(* ================================================================= *)
(* The forward copy loop (0x110bc)                                    *)
(* ================================================================= *)

(* [store_grant_ok]: the loop's [sb]s are machine stores into the brk
   grant, and [mem0] is abstract here, so the grant's writability has to
   come in as a hypothesis. *)
Lemma source_copy : forall (r : word) mem0,
  store_grant_ok source_segs mem0 r nN ->
  rdn source_segs mem0 ptr (S nn) = Some (arg1 ++ [Z_to_bv 8 0]) ->
  region_free (segments_reserved source_segs) r nN = true ->
  (0 < bv_unsigned r)%Z -> (bv_unsigned r + Z.of_nat nn <= bv_unsigned rsp - stack_max_size)%Z ->
  forall d regs, (d <= nn)%nat ->
  reg_get regs 18 = ptr -> reg_get regs 9 = r -> reg_get regs 8 = nN ->
  reg_get regs 15 = nat_to_word (nn - d) ->
  exists regs',
    (forall x : reg, x <> 13 -> x <> 14 -> x <> 15 -> reg_get regs' x = reg_get regs x) /\
    reg_get regs' 15 = nN /\ reg_get regs' 9 = r /\ reg_get regs' 8 = nN /\ reg_get regs' 18 = ptr /\
    msteps source_segs
      (mkst regs 0x110bc (wbytes mem0 r (firstn (nn - d) arg1)) rrom)
      (mkst regs' 0x110c0 (wbytes mem0 r arg1) rrom).
Proof.
  intros r mem0 Hgok Hstr Hfree Hr0 Hceil.
  pose proof ptr_lo' as Hplo. pose proof ptr_hi' as Hphi.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le' as HnnLe.
  pose proof (u64_range r) as Hur.
  assert (Hnn : nn = length arg1) by reflexivity.
  assert (Hrp : (bv_unsigned r + Z.of_nat nn <= bv_unsigned ptr)%Z) by lia.
  induction d as [|d IH]; intros regs Hd Hr18 Hr9 Hr8 Hr15.
  - exists regs. split; [|split; [|split; [|split; [|split]]]].
    + intros x _ _ _. reflexivity.
    + rewrite Hr15, Nat.sub_0_r. reflexivity.
    + exact Hr9.
    + exact Hr8.
    + exact Hr18.
    + replace (firstn (nn - 0) arg1) with arg1
        by (rewrite Nat.sub_0_r, Hnn; symmetry; apply firstn_all).
      eapply mst_step;
        [ reflexivity
        | eapply step_bne_ft;
          [ exact SF_110bc | reflexivity | exact SD_110bc
          | getr_resolve; rewrite Hr15, Hr8, Nat.sub_0_r;
            unfold nN; apply c_eq_refl ]
        | norm_pc ].
      apply mst_refl.
  - assert (Hilt : (nn - S d < nn)%nat) by lia.
    set (i := (nn - S d)%nat).
    set (memI := wbytes mem0 r (firstn i arg1)).
    set (b := nth i arg1 (Z_to_bv 8 0)).
    assert (HlenF : length (firstn i arg1) = i)
      by (apply firstn_length_le; rewrite <- Hnn; lia).
    assert (Hui : bv_unsigned (ptr + nat_to_word i) = (bv_unsigned ptr + Z.of_nat i)%Z)
      by (rewrite u_add_small; rewrite u_ntw by lia; lia).
    assert (Hri : bv_unsigned (r + nat_to_word i) = (bv_unsigned r + Z.of_nat i)%Z)
      by (rewrite u_add_small; rewrite u_ntw by lia; lia).
    (* 0x110bc bne a5,s0 taken -> 0x11144 *)
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x110bc memI rrom)
                 = MachineOk (mkst regs 0x11144 memI rrom)).
    { rewrite (step_bne_tk source_segs regs 0x110bc memI rrom _ 15 8 _
                 SF_110bc eq_refl SD_110bc).
      - wlits. reflexivity.
      - getr_resolve. rewrite Hr15, Hr8. apply c_eq_neq.
        rewrite u_ntw by lia. rewrite u_nN'. unfold i; lia. }
    (* 0x11144 add a4,s2,a5 : a4 = ptr + i *)
    set (regs1 := regupd regs 14 (ptr + nat_to_word i)).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs 0x11144 memI rrom)
                 = MachineOk (mkst regs1 0x11148 memI rrom)).
    { rewrite (step_add_at source_segs regs 0x11144 memI rrom _ 14 18 15
                 (ptr + nat_to_word i) SF_11144 eq_refl SD_11144 eq_refl).
      - wlits. reflexivity.
      - getr_resolve. rewrite Hr18, Hr15. reflexivity. }
    (* 0x11148 lbu a3,0(a4) : a3 = arg1[i] *)
    set (regs2 := regupd regs1 13 (Z_to_bv 64 (bv_unsigned b))).
    assert (E3 : RiscvSemantics.step source_segs (mkst regs1 0x11148 memI rrom)
                 = MachineOk (mkst regs2 0x1114c memI rrom)).
    { rewrite (step_lbu source_segs regs1 0x11148 memI rrom _ 13 14 _ b
                 SF_11148 eq_refl SD_11148).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite v_addi_0. unfold memI.
        rewrite rdn_wbytes_disjoint by (rewrite ?HlenF; rewrite ?Hui; lia).
        pose proof (rdn_nth source_segs mem0 (S nn) ptr (arg1 ++ [Z_to_bv 8 0]) i
                      Hstr ltac:(lia)) as Hb'.
        replace (nth i (arg1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) with b in Hb'
          by (unfold b; symmetry; apply app_nth1; rewrite <- Hnn; lia).
        exact Hb'. }
    (* 0x1114c add a4,a5,s1 : a4 = r + i *)
    set (regs3 := regupd regs2 14 (r + nat_to_word i)).
    assert (E4 : RiscvSemantics.step source_segs (mkst regs2 0x1114c memI rrom)
                 = MachineOk (mkst regs3 0x11150 memI rrom)).
    { rewrite (step_add_at source_segs regs2 0x1114c memI rrom _ 14 15 9
                 (r + nat_to_word i) SF_1114c eq_refl SD_1114c eq_refl).
      - wlits. reflexivity.
      - unfold regs2, regs1. getr_resolve. rewrite Hr15, Hr9.
        apply bv_eq. unfold v_add.
        rewrite bv_add_unsigned, Z_to_bv_unsigned. f_equal. unfold i. lia. }
    (* 0x11150 addi a5,a5,1 : i++ *)
    set (regs4 := regupd regs3 15 (nat_to_word (S i))).
    assert (E5 : RiscvSemantics.step source_segs (mkst regs3 0x11150 memI rrom)
                 = MachineOk (mkst regs4 0x11154 memI rrom)).
    { rewrite (step_addi_at source_segs regs3 0x11150 memI rrom _ 15 15 _
                 (nat_to_word (S i)) SF_11150 eq_refl SD_11150 eq_refl).
      - wlits. reflexivity.
      - unfold regs3, regs2, regs1. getr_resolve. rewrite Hr15.
        rewrite v_addi_Sj by lia. reflexivity. }
    (* 0x11154 sb a3,0(a4) : store byte at r+i *)
    set (memI' := wbytes mem0 r (firstn (S i) arg1)).
    assert (E6 : RiscvSemantics.step source_segs (mkst regs4 0x11154 memI rrom)
                 = MachineOk (mkst regs4 0x11158 memI' rrom)).
    { rewrite (step_sb_at source_segs regs4 0x11154 memI rrom _ 14 13 _
                 (r + nat_to_word i) b SF_11154 eq_refl SD_11154).
      - wlits. replace (wbytes memI (r + nat_to_word i) [b]) with memI'; [reflexivity|].
        unfold memI', memI.
        rewrite (firstn_snoc arg1 i) by (rewrite <- Hnn; lia).
        rewrite wbytes_app, HlenF. reflexivity.
      - unfold regs4, regs3. getr_resolve. rewrite v_addi_0. reflexivity.
      - unfold regs4, regs3, regs2. getr_resolve. apply zext8_byte.
      - store_ok_peel; apply Hgok;
          [ rewrite Hri; lia | rewrite Hri, u_nN'; unfold i; lia ]. }
    (* 0x11158 j 0x110bc *)
    assert (E7 : RiscvSemantics.step source_segs (mkst regs4 0x11158 memI' rrom)
                 = MachineOk (mkst regs4 0x110bc memI' rrom)).
    { rewrite (step_jal_x0 source_segs regs4 0x11158 memI' rrom _ _
                 SF_11158 eq_refl SD_11158).
      wlits. reflexivity. }
    assert (Hr18' : reg_get regs4 18 = ptr).
    { unfold regs4, regs3, regs2, regs1. rewrite !regupd_other by reg_neq_tac.
      exact Hr18. }
    assert (Hr9' : reg_get regs4 9 = r).
    { unfold regs4, regs3, regs2, regs1. rewrite !regupd_other by reg_neq_tac.
      exact Hr9. }
    assert (Hr8' : reg_get regs4 8 = nN).
    { unfold regs4, regs3, regs2, regs1. rewrite !regupd_other by reg_neq_tac.
      exact Hr8. }
    assert (Hr15' : reg_get regs4 15 = nat_to_word (nn - d)).
    { unfold regs4. rewrite regupd_same. unfold i.
      replace (S (nn - S d)) with (nn - d)%nat by lia. reflexivity. }
    destruct (IH regs4 ltac:(lia) Hr18' Hr9' Hr8' Hr15')
      as (regs' & Hag & H15 & H9 & H8 & H18 & Hms).
    exists regs'. split; [|split; [|split; [|split; [|split]]]].
    + intros x Hx13 Hx14 Hx15. rewrite (Hag x Hx13 Hx14 Hx15).
      unfold regs4, regs3, regs2, regs1. rewrite !regupd_other by assumption.
      reflexivity.
    + exact H15.
    + exact H9.
    + exact H8.
    + exact H18.
    + fold i memI.
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      eapply mst_step; [reflexivity | exact E7 |].
      unfold memI'. replace (S i) with (nn - d)%nat by (unfold i; lia).
      exact Hms.
Qed.

(* ================================================================= *)
(* The byte-sum loops                                                 *)
(* ================================================================= *)

Lemma sum_firstn_bound : forall k, (sumb (firstn k arg1) <= 255 * Z.of_nat nn)%Z.
Proof.
  intro k.
  assert (Hle : (sumb (firstn k arg1) <= sumb arg1)%Z).
  { rewrite <- (firstn_skipn k arg1) at 2. rewrite sumb_app.
    pose proof (sumb_nonneg (skipn k arg1)). lia. }
  pose proof (sumb_le arg1 (arg1_bytes Hge2)) as Hb. unfold nn. lia.
Qed.

(** The inner 8-byte chunk loop (0x11164).  [a0] holds [buf + i] — gcc 15
    recomputes it per chunk instead of bumping a callee-saved pointer. *)
Lemma source_sum_inner : forall (r : word) (M : word -> option byte) total m,
  (forall i, (i < total)%nat ->
     rdn source_segs M (r + nat_to_word i) 1 =
       Some [nth i arg1 (Z_to_bv 8 0)]) ->
  (8 * m + 8 <= total)%nat ->
  (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + Z.of_nat total <= bv_unsigned rsp - stack_max_size)%Z ->
  forall c regs, (1 <= c <= 8)%nat ->
  reg_get regs 10 = r + nat_to_word (8 * m) ->
  reg_get regs 12 = Z_to_bv 64 8 ->
  reg_get regs 13 = nat_to_word (8 - c) ->
  reg_get regs 15 = Z_to_bv 64 (sumb (firstn (8 * m + (8 - c)) arg1)) ->
  exists regs',
    (forall x : reg, x <> 13 -> x <> 11 -> x <> 15 -> reg_get regs' x = reg_get regs x) /\
    reg_get regs' 15 = Z_to_bv 64 (sumb (firstn (8 * m + 8) arg1)) /\
    msteps source_segs (mkst regs 0x11164 M rrom) (mkst regs' 0x11178 M rrom).
Proof.
  intros r M total m Hbyte Hmn Hr0 Hceil.
  pose proof nN_le' as HnnLe. pose proof (arg1_bytes Hge2) as Hbytes.
  pose proof (u64_range r) as Hur.
  pose proof stack_max_size_val as Hsms. pose proof rsp_hi_num as Hsphi.
  assert (Hnn : nn = length arg1) by reflexivity.
  induction c as [|c' IH]; intros regs Hc H10 H12 H13 H15; [lia|].
  set (j := (8 - S c')%nat).
  assert (Hjlt : (j < 8)%nat) by (unfold j; lia).
  assert (Hidx : (8 * m + j < total)%nat) by (unfold j; lia).
  set (b := nth (8 * m + j) arg1 (Z_to_bv 8 0)).
  pose proof (u8_range b) as Hb8.
  pose proof (sum_firstn_bound (8 * m + j)) as Hsb1.
  pose proof (sumb_nonneg (firstn (8 * m + j) arg1)) as Hsb0.
  pose proof (sum_firstn_bound (S (8 * m + j))) as HsbS1.
  pose proof (sumb_nonneg (firstn (S (8 * m + j)) arg1)) as HsbS0.
  (* 0x11164 add a1,a0,a3 : a1 = r + 8m + j *)
  set (regsA := regupd regs 11 (r + nat_to_word (8 * m + j))).
  assert (EA : RiscvSemantics.step source_segs (mkst regs 0x11164 M rrom)
               = MachineOk (mkst regsA 0x11168 M rrom)).
  { rewrite (step_add_at source_segs regs 0x11164 M rrom _ 11 10 13
               (r + nat_to_word (8 * m + j)) SF_11164 eq_refl SD_11164 eq_refl).
    - wlits. reflexivity.
    - getr_resolve. rewrite H10, H13. rewrite word_add_nat_split by lia. reflexivity. }
  (* 0x11168 lbu a1,0(a1): bytes beyond the logical string come from
     the zero-filled tail of the page-rounded physical brk grant. *)
  set (regsB := regupd regsA 11 (Z_to_bv 64 (bv_unsigned b))).
  assert (EB : RiscvSemantics.step source_segs (mkst regsA 0x11168 M rrom)
               = MachineOk (mkst regsB 0x1116c M rrom)).
  { rewrite (step_lbu source_segs regsA 0x11168 M rrom _ 11 11 _ b
               SF_11168 eq_refl SD_11168).
    - reduce_bv_eqb_ifs. wlits. reflexivity.
    - unfold regsA. getr_resolve. rewrite v_addi_0.
      apply Hbyte. exact Hidx. }
  (* 0x1116c addi a3,a3,1 : j++ *)
  set (regsC := regupd regsB 13 (nat_to_word (S j))).
  assert (EC : RiscvSemantics.step source_segs (mkst regsB 0x1116c M rrom)
               = MachineOk (mkst regsC 0x11170 M rrom)).
  { rewrite (step_addi_at source_segs regsB 0x1116c M rrom _ 13 13 _
               (nat_to_word (S j)) SF_1116c eq_refl SD_1116c eq_refl).
    - wlits. reflexivity.
    - unfold regsB, regsA. getr_resolve. rewrite H13.
      rewrite v_addi_Sj by lia. reflexivity. }
  (* 0x11170 add a5,a5,a1 : sum += b *)
  set (regsD := regupd regsC 15 (Z_to_bv 64 (sumb (firstn (S (8 * m + j)) arg1)))).
  assert (ED : RiscvSemantics.step source_segs (mkst regsC 0x11170 M rrom)
               = MachineOk (mkst regsD 0x11174 M rrom)).
  { rewrite (step_add_at source_segs regsC 0x11170 M rrom _ 15 15 11
               (Z_to_bv 64 (sumb (firstn (S (8 * m + j)) arg1)))
               SF_11170 eq_refl SD_11170 eq_refl).
    - wlits. reflexivity.
    - unfold regsC, regsB, regsA. getr_resolve. rewrite H15.
      apply bv_eq. rewrite v_add_small.
      + rewrite !u_Z2bv by (unfold j in *; lia).
        rewrite (sumb_firstn_S_default arg1 (8 * m + j)).
        fold b. reflexivity.
      + rewrite !u_Z2bv by (unfold j in *; lia). unfold j in *; lia. }
  assert (HDother : forall x : reg, x <> 13 -> x <> 11 -> x <> 15 ->
                    reg_get regsD x = reg_get regs x).
  { intros x Ha Hb' Hc'. unfold regsD, regsC, regsB, regsA.
    rewrite !regupd_other by assumption. reflexivity. }
  assert (HD13 : reg_get regsD 13 = nat_to_word (S j)).
  { unfold regsD, regsC. rewrite regupd_other by reg_neq_tac. apply regupd_same. }
  assert (HD12 : reg_get regsD 12 = Z_to_bv 64 8).
  { unfold regsD, regsC, regsB, regsA. rewrite !regupd_other by reg_neq_tac. exact H12. }
  assert (HD10 : reg_get regsD 10 = r + nat_to_word (8 * m)).
  { unfold regsD, regsC, regsB, regsA. rewrite !regupd_other by reg_neq_tac. exact H10. }
  assert (HD15 : reg_get regsD 15 = Z_to_bv 64 (sumb (firstn (S (8 * m + j)) arg1)))
    by (unfold regsD; apply regupd_same).
  destruct (Nat.eqb_spec c' 0) as [-> | Hc'n].
  - (* last iteration: j = 7, bne falls through to 0x11178 *)
    exists regsD. split; [|split].
    + exact HDother.
    + rewrite HD15.
      replace (S (8 * m + j))%nat with (8 * m + 8)%nat by (unfold j; lia). reflexivity.
    + eapply mst_step; [reflexivity | exact EA |].
      eapply mst_step; [reflexivity | exact EB |].
      eapply mst_step; [reflexivity | exact EC |].
      eapply mst_step; [reflexivity | exact ED |].
      eapply mst_step;
        [ reflexivity
        | eapply step_bne_ft;
          [ exact SF_11174 | reflexivity | exact SD_11174
          | getr_resolve; rewrite HD13, HD12;
            replace (nat_to_word (S j)) with (Z_to_bv 64 8)
              by (apply bv_eq; rewrite u_ntw by (unfold j; lia);
                  rewrite u_Z2bv by lia; unfold j; lia);
            apply c_eq_refl ]
        | norm_pc ].
      apply mst_refl.
  - (* not last: bne taken -> 0x11164, recurse with c' *)
    assert (HcS : (1 <= c' <= 8)%nat) by lia.
    destruct (IH regsD HcS HD10 HD12
                ltac:(rewrite HD13; f_equal; unfold j; lia)
                ltac:(rewrite HD15;
                      replace (S (8 * m + j))%nat with (8 * m + (8 - c'))%nat
                        by (unfold j; lia); reflexivity))
      as (regs' & Hag & H15' & Hms).
    exists regs'. split; [|split].
    + intros x Hx13 Hx11 Hx15. rewrite (Hag x Hx13 Hx11 Hx15).
      apply HDother; assumption.
    + exact H15'.
    + eapply mst_step; [reflexivity | exact EA |].
      eapply mst_step; [reflexivity | exact EB |].
      eapply mst_step; [reflexivity | exact EC |].
      eapply mst_step; [reflexivity | exact ED |].
      eapply mst_step;
        [ reflexivity
        | eapply step_bne_tk;
          [ exact SF_11174 | reflexivity | exact SD_11174
          | getr_resolve; rewrite HD13, HD12; apply c_eq_neq;
            rewrite u_ntw by (unfold j; lia); rewrite u_Z2bv by lia; unfold j; lia ]
        | norm_pc ].
      exact Hms.
Qed.

Lemma source_sum_chunk : forall (r : word) (M : word -> option byte) total m,
  (forall i, (i < total)%nat ->
     rdn source_segs M (r + nat_to_word i) 1 =
       Some [nth i arg1 (Z_to_bv 8 0)]) ->
  (8 * m < nn)%nat ->
  (8 * m + 8 <= total)%nat ->
  (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + Z.of_nat total <= bv_unsigned rsp - stack_max_size)%Z ->
  forall regs,
  reg_get regs 14 = nat_to_word (8 * m) ->
  reg_get regs 9 = r ->
  reg_get regs 15 = Z_to_bv 64 (sumb (firstn (8 * m) arg1)) ->
  reg_get regs 12 = Z_to_bv 64 8 -> reg_get regs 8 = nN ->
  exists regs',
    (forall x : reg, x <> 14 -> x <> 10 -> x <> 15 -> x <> 13 -> x <> 11 -> reg_get regs' x = reg_get regs x) /\
    reg_get regs' 14 = nat_to_word (8 * S m) /\
    reg_get regs' 9 = r /\
    reg_get regs' 15 = Z_to_bv 64 (sumb (firstn (8 * S m) arg1)) /\
    reg_get regs' 12 = Z_to_bv 64 8 /\ reg_get regs' 8 = nN /\
    msteps source_segs (mkst regs 0x110cc M rrom) (mkst regs' 0x110cc M rrom).
Proof.
  intros r M total m Hbyte Hrun Hmn Hr0 Hceil regs H14 H9 H15 H12 H8.
  pose proof nN_le' as HnnLe. pose proof (u64_range r) as Hur.
  pose proof stack_max_size_val as Hsms. pose proof rsp_hi_num as Hsphi.
  (* 0x110cc bltu a4,s0 taken (8m < n) -> 0x1115c *)
  assert (E0 : RiscvSemantics.step source_segs (mkst regs 0x110cc M rrom)
               = MachineOk (mkst regs 0x1115c M rrom)).
  { rewrite (step_bltu_tk source_segs regs 0x110cc M rrom _ 14 8 _
               SF_110cc eq_refl SD_110cc).
    - wlits. reflexivity.
    - getr_resolve. rewrite H14, H8. rewrite c_ltu_ltb. apply Z.ltb_lt.
      rewrite u_ntw by lia. rewrite u_nN'. lia. }
  (* 0x1115c li a3,0 : j = 0 *)
  set (regs0 := regupd regs 13 (Z_to_bv 64 0)).
  assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x1115c M rrom)
               = MachineOk (mkst regs0 0x11160 M rrom)).
  { rewrite (step_addi_at source_segs regs 0x1115c M rrom _ 13 0 _
               (Z_to_bv 64 0) SF_1115c eq_refl SD_1115c eq_refl).
    - wlits. reflexivity.
    - getr_resolve. apply v_addi_0. }
  (* 0x11160 add a0,a4,s1 : a0 = r + 8m *)
  set (regs0' := regupd regs0 10 (r + nat_to_word (8 * m))).
  assert (E1' : RiscvSemantics.step source_segs (mkst regs0 0x11160 M rrom)
                = MachineOk (mkst regs0' 0x11164 M rrom)).
  { rewrite (step_add_at source_segs regs0 0x11160 M rrom _ 10 14 9
               (r + nat_to_word (8 * m)) SF_11160 eq_refl SD_11160 eq_refl).
    - wlits. reflexivity.
    - unfold regs0. getr_resolve. rewrite H14, H9. rewrite v_add_comm. reflexivity. }
  assert (H0_10 : reg_get regs0' 10 = r + nat_to_word (8 * m))
    by (unfold regs0'; apply regupd_same).
  assert (H0_12 : reg_get regs0' 12 = Z_to_bv 64 8).
  { unfold regs0', regs0. rewrite !regupd_other by reg_neq_tac. exact H12. }
  assert (H0_13 : reg_get regs0' 13 = nat_to_word (8 - 8)).
  { unfold regs0'. rewrite regupd_other by reg_neq_tac.
    unfold regs0. rewrite regupd_same. reflexivity. }
  assert (H0_15 : reg_get regs0' 15 = Z_to_bv 64 (sumb (firstn (8 * m + (8 - 8)) arg1))).
  { unfold regs0', regs0. rewrite !regupd_other by reg_neq_tac. rewrite H15.
    replace (8 * m + (8 - 8))%nat with (8 * m)%nat by lia. reflexivity. }
  destruct (source_sum_inner r M total m Hbyte Hmn Hr0
              Hceil 8 regs0'
              ltac:(lia) H0_10 H0_12 H0_13 H0_15)
    as (regs1 & Hag1 & H1_15 & Hms1).
  assert (H1_14 : reg_get regs1 14 = nat_to_word (8 * m)).
  { rewrite (Hag1 14) by reg_neq_tac.
    unfold regs0', regs0. rewrite !regupd_other by reg_neq_tac. exact H14. }
  assert (H1_9 : reg_get regs1 9 = r).
  { rewrite (Hag1 9) by reg_neq_tac.
    unfold regs0', regs0. rewrite !regupd_other by reg_neq_tac. exact H9. }
  assert (H1_8 : reg_get regs1 8 = nN).
  { rewrite (Hag1 8) by reg_neq_tac.
    unfold regs0', regs0. rewrite !regupd_other by reg_neq_tac. exact H8. }
  assert (H1_12 : reg_get regs1 12 = Z_to_bv 64 8).
  { rewrite (Hag1 12) by reg_neq_tac. exact H0_12. }
  (* 0x11178 addi a4,a4,8 : i += 8 *)
  set (regs2 := regupd regs1 14 (nat_to_word (8 * S m))).
  assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x11178 M rrom)
               = MachineOk (mkst regs2 0x1117c M rrom)).
  { rewrite (step_addi_at source_segs regs1 0x11178 M rrom _ 14 14 _
               (nat_to_word (8 * S m)) SF_11178 eq_refl SD_11178 eq_refl).
    - wlits. reflexivity.
    - getr_resolve. rewrite H1_14. apply bv_eq.
      rewrite v_addi_nneg by (imm_norm; rewrite ?u_ntw by lia; lia).
      imm_norm. rewrite (u_ntw (8 * m)) by lia. rewrite (u_ntw (8 * S m)) by lia. lia. }
  (* 0x1117c j 0x110cc *)
  assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x1117c M rrom)
               = MachineOk (mkst regs2 0x110cc M rrom)).
  { rewrite (step_jal_x0 source_segs regs2 0x1117c M rrom _ _
               SF_1117c eq_refl SD_1117c).
    wlits. reflexivity. }
  exists regs2. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - intros x Hx14 Hx10 Hx15 Hx13 Hx11.
    unfold regs2. rewrite regupd_other by assumption.
    rewrite (Hag1 x Hx13 Hx11 Hx15).
    unfold regs0', regs0. rewrite !regupd_other by assumption. reflexivity.
  - unfold regs2. apply regupd_same.
  - unfold regs2. rewrite regupd_other by reg_neq_tac. exact H1_9.
  - unfold regs2. rewrite regupd_other by reg_neq_tac.
    rewrite H1_15. replace (8 * S m)%nat with (8 * m + 8)%nat by lia. reflexivity.
  - unfold regs2. rewrite regupd_other by reg_neq_tac. exact H1_12.
  - unfold regs2. rewrite regupd_other by reg_neq_tac. exact H1_8.
  - eapply mst_step; [reflexivity | exact E0 |].
    eapply mst_step; [reflexivity | exact E1 |].
    eapply mst_step; [reflexivity | exact E1' |].
    eapply msteps_trans; [exact Hms1 |].
    eapply mst_step; [reflexivity | exact E2 |].
    eapply mst_step; [reflexivity | exact E3 |].
    apply mst_refl.
Qed.

Lemma source_sum : forall (r : word) (M : word -> option byte) total,
  (forall i, (i < total)%nat ->
     rdn source_segs M (r + nat_to_word i) 1 =
       Some [nth i arg1 (Z_to_bv 8 0)]) ->
  (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + Z.of_nat total <= bv_unsigned rsp - stack_max_size)%Z ->
  forall c m0 regs,
  (8 * (m0 + c - 1) < nn)%nat ->
  (8 * (m0 + c) = total)%nat ->
  reg_get regs 14 = nat_to_word (8 * m0) ->
  reg_get regs 9 = r ->
  reg_get regs 15 = Z_to_bv 64 (sumb (firstn (8 * m0) arg1)) ->
  reg_get regs 12 = Z_to_bv 64 8 -> reg_get regs 8 = nN ->
  exists regs',
    (forall x : reg, x <> 14 -> x <> 10 -> x <> 15 -> x <> 13 -> x <> 11 -> reg_get regs' x = reg_get regs x) /\
    reg_get regs' 14 = nat_to_word (8 * (m0 + c)) /\
    reg_get regs' 9 = r /\
    reg_get regs' 15 = Z_to_bv 64 (sumb (firstn (8 * (m0 + c)) arg1)) /\
    reg_get regs' 12 = Z_to_bv 64 8 /\ reg_get regs' 8 = nN /\
    msteps source_segs (mkst regs 0x110cc M rrom) (mkst regs' 0x110cc M rrom).
Proof.
  intros r M total Hbyte Hr0 Hceil c.
  induction c as [|c IH]; intros m0 regs Hrun Htotal H14 H9 H15 H12 H8.
  - rewrite Nat.add_0_r.
    exists regs. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros x _ _ _ _ _. reflexivity.
    + exact H14.
    + exact H9.
    + exact H15.
    + exact H12.
    + exact H8.
    + apply mst_refl.
  - destruct (source_sum_chunk r M total m0 Hbyte ltac:(lia) ltac:(lia)
                Hr0 Hceil regs
                H14 H9 H15 H12 H8)
      as (regs1 & Hag1 & H1_14 & H1_9 & H1_15 & H1_12 & H1_8 & Hms1).
    destruct (IH (S m0) regs1 ltac:(lia) ltac:(lia)
                H1_14 H1_9 H1_15 H1_12 H1_8)
      as (regs' & Hag' & H'_14 & H'_9 & H'_15 & H'_12 & H'_8 & Hms').
    exists regs'.
    replace (m0 + S c)%nat with (S m0 + c)%nat by lia.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros x Ha Hb Hc' Hd He. rewrite (Hag' x Ha Hb Hc' Hd He).
      apply Hag1; assumption.
    + exact H'_14.
    + exact H'_9.
    + exact H'_15.
    + exact H'_12.
    + exact H'_8.
    + eapply msteps_trans; [exact Hms1 | exact Hms'].
Qed.

(** The same inner loop, run for [q] valid iterations only — used by the
    may-error argument, where the [q+1]-st load is the out-of-bounds one. *)
Lemma source_inner_valid : forall (r : word) (M : word -> option byte) m,
  rdn source_segs M r nn = Some arg1 ->
  (0 < bv_unsigned r)%Z -> (bv_unsigned r + Z.of_nat nn <= bv_unsigned rsp - stack_max_size)%Z ->
  forall d j regs, (8 * m + j + d <= nn)%nat -> (j + d <= 7)%nat ->
  reg_get regs 10 = r + nat_to_word (8 * m) -> reg_get regs 12 = Z_to_bv 64 8 ->
  reg_get regs 13 = nat_to_word j ->
  exists regs',
    reg_get regs' 10 = r + nat_to_word (8 * m) /\ reg_get regs' 12 = Z_to_bv 64 8 /\
    reg_get regs' 13 = nat_to_word (j + d) /\
    msteps source_segs (mkst regs 0x11164 M rrom) (mkst regs' 0x11164 M rrom).
Proof.
  intros r M m Hbuf Hr0 Hceil.
  pose proof nN_le' as HnnLe. pose proof (arg1_bytes Hge2) as Hbytes.
  pose proof (u64_range r) as Hur.
  pose proof stack_max_size_val as Hsms. pose proof rsp_hi_num as Hsphi.
  assert (Hnn : nn = length arg1) by reflexivity.
  induction d as [|d IH]; intros j regs Hbnd Hj7 H10 H12 H13.
  - exists regs. rewrite Nat.add_0_r. split; [|split; [|split]].
    + exact H10.
    + exact H12.
    + exact H13.
    + apply mst_refl.
  - assert (Hidx : (8 * m + j < nn)%nat) by lia.
    set (b := nth (8 * m + j) arg1 (Z_to_bv 8 0)).
    pose proof (u8_range b) as Hb8.
    (* 0x11164 add a1,a0,a3 : a1 = r + 8m + j *)
    set (regsA := regupd regs 11 (r + nat_to_word (8 * m + j))).
    assert (EA : RiscvSemantics.step source_segs (mkst regs 0x11164 M rrom)
                 = MachineOk (mkst regsA 0x11168 M rrom)).
    { rewrite (step_add_at source_segs regs 0x11164 M rrom _ 11 10 13
                 (r + nat_to_word (8 * m + j)) SF_11164 eq_refl SD_11164 eq_refl).
      - wlits. reflexivity.
      - getr_resolve. rewrite H10, H13. rewrite word_add_nat_split by lia. reflexivity. }
    (* 0x11168 lbu a1,0(a1) : a1 = b *)
    set (regsB := regupd regsA 11 (Z_to_bv 64 (bv_unsigned b))).
    assert (EB : RiscvSemantics.step source_segs (mkst regsA 0x11168 M rrom)
                 = MachineOk (mkst regsB 0x1116c M rrom)).
    { rewrite (step_lbu source_segs regsA 0x11168 M rrom _ 11 11 _ b
                 SF_11168 eq_refl SD_11168).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regsA. getr_resolve. rewrite v_addi_0.
        pose proof (rdn_nth source_segs M nn r arg1 (8 * m + j) Hbuf Hidx) as Hb'.
        fold b in Hb'. exact Hb'. }
    (* 0x1116c addi a3,a3,1 : j++ *)
    set (regsC := regupd regsB 13 (nat_to_word (S j))).
    assert (EC : RiscvSemantics.step source_segs (mkst regsB 0x1116c M rrom)
                 = MachineOk (mkst regsC 0x11170 M rrom)).
    { rewrite (step_addi_at source_segs regsB 0x1116c M rrom _ 13 13 _
                 (nat_to_word (S j)) SF_1116c eq_refl SD_1116c eq_refl).
      - wlits. reflexivity.
      - unfold regsB, regsA. getr_resolve. rewrite H13.
        rewrite v_addi_Sj by lia. reflexivity. }
    (* 0x11170 add a5,a5,a1 : sum += b (value irrelevant) *)
    set (regsD := regupd regsC 15 (v_add (getr regsC 15) (getr regsC 11))).
    assert (ED : RiscvSemantics.step source_segs (mkst regsC 0x11170 M rrom)
                 = MachineOk (mkst regsD 0x11174 M rrom)).
    { rewrite (step_add source_segs regsC 0x11170 M rrom _ 15 15 11
                 SF_11170 eq_refl SD_11170).
      reduce_bv_eqb_ifs. wlits. reflexivity. }
    assert (HD10 : reg_get regsD 10 = r + nat_to_word (8 * m)).
    { unfold regsD, regsC, regsB, regsA. rewrite !regupd_other by reg_neq_tac. exact H10. }
    assert (HD12 : reg_get regsD 12 = Z_to_bv 64 8).
    { unfold regsD, regsC, regsB, regsA. rewrite !regupd_other by reg_neq_tac. exact H12. }
    assert (HD13 : reg_get regsD 13 = nat_to_word (S j)).
    { unfold regsD, regsC. rewrite regupd_other by reg_neq_tac. apply regupd_same. }
    (* 0x11174 bne a3,a2 taken (j+1 <> 8) -> 0x11164 *)
    assert (EE : RiscvSemantics.step source_segs (mkst regsD 0x11174 M rrom)
                 = MachineOk (mkst regsD 0x11164 M rrom)).
    { rewrite (step_bne_tk source_segs regsD 0x11174 M rrom _ 13 12 _
                 SF_11174 eq_refl SD_11174).
      - wlits. reflexivity.
      - getr_resolve. rewrite HD13, HD12. apply c_eq_neq.
        rewrite u_ntw by lia. rewrite u_Z2bv by lia. lia. }
    destruct (IH (S j) regsD ltac:(lia) ltac:(lia) HD10 HD12 HD13)
      as (regs' & H10' & H12' & H13' & Hms').
    exists regs'. split; [|split; [|split]].
    + exact H10'.
    + exact H12'.
    + rewrite H13'. f_equal. lia.
    + eapply mst_step; [reflexivity | exact EA |].
      eapply mst_step; [reflexivity | exact EB |].
      eapply mst_step; [reflexivity | exact EC |].
      eapply mst_step; [reflexivity | exact ED |].
      eapply mst_step; [reflexivity | exact EE |].
      exact Hms'.
Qed.

(* ================================================================= *)
(* put(): musl write() + the (now frameless) __syscall_ret            *)
(* ================================================================= *)

(** gcc 15 builds [__syscall_ret]'s success path without a frame — [lui
    a5,0xfffff; bltu a5,a0,err; ret] — so the walk no longer spills and
    reloads s0, and the callee-saved registers survive untouched. *)
Lemma source_put : forall (K : machine_state -> Prop)
    regs mem buf (pbuf len RA : word),
  reg_get regs 1 = RA ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  reg_get regs 11 = pbuf ->
  reg_get regs 12 = len ->
  (0 < bv_unsigned len)%Z -> (bv_unsigned len < 2^31)%Z ->
  (* [vfs_write]'s [access_ok] on the buffer *)
  (bv_unsigned pbuf + bv_unsigned len <= TASK_SIZE)%Z ->
  v_jalr RA 0 = RA ->
  rdn source_segs (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 88)) (word_to_le_bytes 8 RA))
      pbuf (word_to_nat len) = Some buf ->
  (* the wrapper saves ra below the frame: a machine store, so [mem] has
     to be writable there.  The continuation gets the fact back, since
     it is what its own stores will need. *)
  mem_grows wmem mem ->
  (forall regs' mem' n, (1 <= n)%nat -> (n <= length buf)%nat ->
     reg_get regs' 1 = RA -> reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
     reg_get regs' 8 = reg_get regs 8 ->
     reg_get regs' 10 = len_word (firstn n buf) ->
     reg_get regs' 9 = reg_get regs 9 -> reg_get regs' 18 = reg_get regs 18 ->
     mem_grows wmem mem' ->
     (forall x : word,
        (bv_unsigned x < bv_unsigned rsp - 88)%Z \/ (bv_unsigned rsp - 80 <= bv_unsigned x)%Z ->
        mem' x = mem x) ->
     to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs' RA mem' rrom)
       (skipn n buf) K) ->
  to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs 0x11220 mem rrom) buf K.
Proof.
  intros K regs mem buf pbuf len RA
    H1 H2 H10 H11 H12 Hlen0 Hlen31 Hacc HRAj Hread Hgrow Hcont.
  pose proof (rdn_length _ _ _ _ _ Hread) as Hbl.
  pose proof (u64_range len) as Hul.
  assert (HbufL : Z.of_nat (length buf) = bv_unsigned len)
    by (rewrite Hbl; unfold word_to_nat; rewrite Z2Nat.id by lia; reflexivity).
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  set (mem1 := wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 88)) (word_to_le_bytes 8 RA)).
  (* addi sp,sp,-16 : sp = rsp-96 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 (bv_unsigned rsp - 96));
      [ exact SF_11220 | reflexivity | exact SD_11220 | reflexivity
      | getr_resolve; rewrite H2; sp_norm; f_equal; lia ]
    | norm_pc ].
  (* mv a3,a2 : a3 = len *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := len);
      [ exact SF_11224 | reflexivity | exact SD_11224 | reflexivity
      | getr_resolve; regupd_resolve; rewrite H12; apply v_addi_0 ]
    | norm_pc ].
  (* li a6,0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11228 | reflexivity | exact SD_11228 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* mv a2,a1 : a2 = pbuf *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := pbuf);
      [ exact SF_1122c | reflexivity | exact SD_1122c | reflexivity
      | getr_resolve; regupd_resolve; rewrite H11; apply v_addi_0 ]
    | norm_pc ].
  (* li a5,0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11230 | reflexivity | exact SD_11230 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* mv a1,a0 : a1 = 1 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 1);
      [ exact SF_11234 | reflexivity | exact SD_11234 | reflexivity
      | getr_resolve; regupd_resolve; rewrite H10; apply v_addi_0 ]
    | norm_pc ].
  (* li a4,0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11238 | reflexivity | exact SD_11238 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* li a0,64 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 64);
      [ exact SF_1123c | reflexivity | exact SD_1123c | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* sd ra,8(sp) : RA at rsp-88 *)
  chain_step;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned rsp - 88)) (v := RA);
      [ exact SF_11240 | reflexivity | exact SD_11240
      | getr_resolve; regupd_resolve; sp_norm; f_equal; lia
      | getr_resolve; regupd_resolve; exact H1
      | solve_store_ok_inv ]
    | step_simpl ].
  fold mem1.
  (* jal ra,0x112b0 *)
  chain_step;
    [ reflexivity
    | eapply step_jal_link; [ exact SF_11244 | reflexivity | exact SD_11244 ]
    | step_simpl ].
  (* j 0x1128c *)
  chain_step;
    [ reflexivity
    | eapply step_jal_x0; [ exact SF_112b0 | reflexivity | exact SD_112b0 ]
    | norm_pc ].
  (* mv a7,a0 : a7 = 64 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 64);
      [ exact SF_1128c | reflexivity | exact SD_1128c | reflexivity
      | getr_resolve; regupd_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* mv a0,a1 : a0 = 1 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 1);
      [ exact SF_11290 | reflexivity | exact SD_11290 | reflexivity
      | getr_resolve; regupd_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* mv a1,a2 : a1 = pbuf *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := pbuf);
      [ exact SF_11294 | reflexivity | exact SD_11294 | reflexivity
      | getr_resolve; regupd_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* mv a2,a3 : a2 = len *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := len);
      [ exact SF_11298 | reflexivity | exact SD_11298 | reflexivity
      | getr_resolve; regupd_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* mv a3,a4 : a3 = 0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_1129c | reflexivity | exact SD_1129c | reflexivity
      | getr_resolve; regupd_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* mv a4,a5 : a4 = 0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_112a0 | reflexivity | exact SD_112a0 | reflexivity
      | getr_resolve; regupd_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* mv a5,a6 : a5 = 0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_112a4 | reflexivity | exact SD_112a4 | reflexivity
      | getr_resolve; regupd_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* ecall : write(1, pbuf, len) *)
  chain_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_112a8 eq_refl) | ].
  apply twt_more; [lia|].
  apply (twl_write_rec source_segs (Z_to_bv 64 1)).
  - getr_resolve. regupd_resolve. vm_compute. reflexivity.
  - regupd_resolve. reflexivity.
  - rewrite (ms_read_bytes_rdn (run_segments source_segs inp rsp rmb)) by reflexivity;
      unfold run_segments; apply rdn_lift.
    cbn [ms_mem ms_regs]. regupd_resolve. exact Hread.
  - (* [vfs_write]'s [access_ok] on the buffer *)
    cbn [ms_regs]. regupd_resolve. rewrite ?H11, ?H12.
    apply Uaccess.access_okb_intro. exact Hacc.
  - lia.
  - (* per delivered length: the wrapper's return path *)
    intros n Hn1 Hn2.
    norm_pc.
    (* ret -> 0x11248 *)
    chain_step;
      [ reflexivity
      | eapply step_jalr_x0 with (tgt := (0x11248 : word));
        [ exact SF_112ac | reflexivity | exact SD_112ac
        | getr_resolve; regupd_resolve; bveq ]
      | norm_pc ].
    (* ld ra,8(sp) : RA from rsp-88 *)
    chain_step;
      [ reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 RA) (v := RA);
        [ exact SF_11248 | reflexivity | exact SD_11248
        | match goal with |- rdn _ _ ?a _ = _ =>
            replace a with (Z_to_bv 64 (bv_unsigned rsp - 88))
              by (getr_resolve; regupd_resolve; sp_norm; f_equal; lia) end;
          unfold mem1; apply rdn_wbytes_hit8; u_norm; lia
        | exact (bytes_le_to_Z_8 _) ]
      | step_simpl ].
    (* addi sp,sp,16 : sp = rsp-80 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 (bv_unsigned rsp - 80));
        [ exact SF_1124c | reflexivity | exact SD_1124c | reflexivity
        | getr_resolve; regupd_resolve; sp_norm; f_equal; lia ]
      | norm_pc ].
    (* j 0x11254 *)
    chain_step;
      [ reflexivity
      | eapply step_jal_x0; [ exact SF_11250 | reflexivity | exact SD_11250 ]
      | norm_pc ].
    (* lui a5,-4096 *)
    chain_step;
      [ reflexivity
      | eapply step_lui_at with (v := Z_to_bv 64 18446744073709547520);
        [ exact SF_11254 | reflexivity | exact SD_11254 | reflexivity | bveq ]
      | norm_pc ].
    (* bltu a5,a0 fall-through *)
    chain_step;
      [ reflexivity
      | eapply step_bltu_ft;
        [ exact SF_11258 | reflexivity | exact SD_11258
        | getr_resolve; regupd_resolve; rewrite c_ltu_ltb; apply Z.ltb_ge;
          rewrite u_len_word_firstn by lia; u_norm; lia ]
      | norm_pc ].
    (* ret -> RA *)
    chain_step;
      [ reflexivity
      | eapply step_jalr_x0 with (tgt := RA);
        [ exact SF_1125c | reflexivity | exact SD_1125c
        | getr_resolve; regupd_resolve; reflexivity ]
      | idtac ].
    imm_norm. rewrite HRAj.
    apply (Hcont _ _ n Hn1 Hn2).
    + regupd_resolve. reflexivity.
    + regupd_resolve. reflexivity.
    + regupd_resolve. reflexivity.
    + regupd_resolve. reflexivity.
    + regupd_resolve. reflexivity.
    + regupd_resolve. reflexivity.
    + unfold mem1. solve_mem_grows.
    + intros x Hx. unfold mem1.
      destruct Hx as [Hx | Hx].
      * rewrite (wbytes_below (word_to_le_bytes 8 _))
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        reflexivity.
      * rewrite (wbytes_above (word_to_le_bytes 8 _))
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        reflexivity.
Qed.

(* ================================================================= *)
(* The decimal-rendering loop (0x1118c)                               *)
(* ================================================================= *)

(** The digit buffer now lives at [24(sp) .. 47(sp)], i.e. [rsp-56 ..
    rsp-33], and its base stays in [a1] across the loop. *)
Definition dbuf : word := Z_to_bv 64 (bv_unsigned rsp - 56).

Lemma source_udec_loop : forall f (m : word -> option byte) (v k : word) regs,
  (1 <= bv_unsigned v)%Z -> (bv_unsigned v < 10 ^ Z.of_nat f)%Z ->
  (Z.of_nat (length (udec (bv_unsigned v))) + 1 <= bv_unsigned k)%Z ->
  (bv_unsigned k <= 23)%Z ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
  reg_get regs 10 = Z_to_bv 64 9 -> reg_get regs 12 = Z_to_bv 64 10 ->
  reg_get regs 11 = dbuf ->
  reg_get regs 13 = k -> reg_get regs 15 = v ->
  (* the digit buffer is a stack slot: the [sb] below is a machine store *)
  mem_grows wmem m ->
  exists regs',
    (forall x : reg, x <> 13 -> x <> 14 -> x <> 15 -> x <> 16 ->
       reg_get regs' x = reg_get regs x) /\
    reg_get regs' 14 = Z_to_bv 64 (bv_unsigned k + 1 - Z.of_nat (length (udec (bv_unsigned v)))) /\
    msteps source_segs (mkst regs 0x1118c m rrom)
      (mkst regs' 0x111b0
        (wbytes m (Z_to_bv 64 (bv_unsigned rsp - 56 + (bv_unsigned k + 1 - Z.of_nat (length (udec (bv_unsigned v))))))
                (udec (bv_unsigned v))) rrom).
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  induction f as [|f IH];
    intros m v k regs Hv1 Hvf HLk Hk H2 H10 H12 H11 H13 H15 Hgrow.
  { change (10 ^ Z.of_nat 0)%Z with 1%Z in Hvf. lia. }
  pose proof (u64_range v) as Huv. pose proof (u64_range k) as Huk.
  pose proof (udec_len_pos (bv_unsigned v)) as Hlp.
  set (dgz := (bv_unsigned v mod 10)%Z).
  assert (Hdg : (0 <= dgz < 10)%Z) by (unfold dgz; apply Z.mod_pos_bound; lia).
  set (a6a := Z_to_bv 64 (bv_unsigned rsp - 56 + bv_unsigned k)).
  (* 0x1118c remu a4,a5,a2 : a4 = v mod 10 *)
  set (regs1 := regupd regs 14 (Z_to_bv 64 dgz)).
  assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x1118c m rrom)
               = MachineOk (mkst regs1 0x11190 m rrom)).
  { rewrite (step_remu source_segs regs 0x1118c m rrom _ 14 15 12
               SF_1118c eq_refl SD_1118c).
    - reduce_bv_eqb_ifs.
      replace (v_remu (getr regs 15) (getr regs 12)) with (Z_to_bv 64 dgz).
      + wlits. reflexivity.
      + getr_resolve. rewrite H15, H12.
        unfold v_remu, dgz. rewrite u_Z2bv by lia. reflexivity.
    - getr_resolve. rewrite H12. rewrite u_Z2bv by lia. lia. }
  (* 0x11190 add a6,a1,a3 : a6 = dbuf + k *)
  set (regs2 := regupd regs1 16 a6a).
  assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x11190 m rrom)
               = MachineOk (mkst regs2 0x11194 m rrom)).
  { rewrite (step_add_at source_segs regs1 0x11190 m rrom _ 16 11 13
               a6a SF_11190 eq_refl SD_11190 eq_refl).
    - wlits. reflexivity.
    - unfold regs1. getr_resolve. rewrite H11, H13. unfold a6a, dbuf.
      apply bv_eq. rewrite v_add_small.
      + u_norm. reflexivity.
      + u_norm. lia. }
  (* 0x11194 addiw a4,a4,48 : a4 = dg + 48 *)
  set (regs3 := regupd regs2 14 (Z_to_bv 64 (48 + dgz))).
  assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x11194 m rrom)
               = MachineOk (mkst regs3 0x11198 m rrom)).
  { rewrite (step_addiw source_segs regs2 0x11194 m rrom _ 14 14 _
               SF_11194 eq_refl SD_11194).
    reduce_bv_eqb_ifs.
    replace (v_addiw (getr regs2 14) (bv_signed 48)) with (Z_to_bv 64 (48 + dgz)).
    - wlits. reflexivity.
    - unfold regs2, regs1. getr_resolve. imm_norm. apply bv_eq.
      rewrite v_addiw_d48 by (rewrite u_Z2bv by lia; lia).
      rewrite !u_Z2bv by lia. lia. }
  (* 0x11198 sb a4,0(a6) : store the digit char *)
  set (m1 := wbytes m a6a [Z_to_bv 8 (48 + dgz)]).
  assert (E4 : RiscvSemantics.step source_segs (mkst regs3 0x11198 m rrom)
               = MachineOk (mkst regs3 0x1119c m1 rrom)).
  { rewrite (step_sb_at source_segs regs3 0x11198 m rrom _ 16 14 _
               a6a (Z_to_bv 8 (48 + dgz)) SF_11198 eq_refl SD_11198).
    - wlits. reflexivity.
    - unfold regs3, regs2, regs1. getr_resolve.
      rewrite v_addi_0. reflexivity.
    - unfold regs3. getr_resolve. rewrite u_Z2bv by lia. reflexivity.
    - eapply store_ok_mono; [exact Hgrow|].
      apply (store_ok_wrap_window_valid source_segs inp rmb source_phdrs _ rsp rbrk _ 1 rrnd
               Hvl Hlau);
        unfold stack_window_reach, stack_max_size, a6a; u_norm; lia. }
  (* 0x1119c mv a6,a5 : a6 = v (old) *)
  set (regs4 := regupd regs3 16 v).
  assert (E5 : RiscvSemantics.step source_segs (mkst regs3 0x1119c m1 rrom)
               = MachineOk (mkst regs4 0x111a0 m1 rrom)).
  { rewrite (step_addi_at source_segs regs3 0x1119c m1 rrom _ 16 15 _
               v SF_1119c eq_refl SD_1119c eq_refl).
    - wlits. reflexivity.
    - unfold regs3, regs2, regs1. getr_resolve. rewrite H15. apply v_addi_0. }
  (* 0x111a0 mv a4,a3 : a4 = k *)
  set (regs5 := regupd regs4 14 k).
  assert (E6 : RiscvSemantics.step source_segs (mkst regs4 0x111a0 m1 rrom)
               = MachineOk (mkst regs5 0x111a4 m1 rrom)).
  { rewrite (step_addi_at source_segs regs4 0x111a0 m1 rrom _ 14 13 _
               k SF_111a0 eq_refl SD_111a0 eq_refl).
    - wlits. reflexivity.
    - unfold regs4, regs3, regs2, regs1. getr_resolve. rewrite H13. apply v_addi_0. }
  (* 0x111a4 divu a5,a5,a2 : a5 = v/10 *)
  set (regs6 := regupd regs5 15 (Z_to_bv 64 (bv_unsigned v / 10))).
  assert (E7 : RiscvSemantics.step source_segs (mkst regs5 0x111a4 m1 rrom)
               = MachineOk (mkst regs6 0x111a8 m1 rrom)).
  { rewrite (step_divu source_segs regs5 0x111a4 m1 rrom _ 15 15 12
               SF_111a4 eq_refl SD_111a4).
    - reduce_bv_eqb_ifs.
      replace (v_divu (getr regs5 15) (getr regs5 12)) with (Z_to_bv 64 (bv_unsigned v / 10)).
      + wlits. reflexivity.
      + unfold regs5, regs4, regs3, regs2, regs1. getr_resolve.
        rewrite H15, H12. unfold v_divu. rewrite u_Z2bv by lia. reflexivity.
    - unfold regs5, regs4, regs3, regs2, regs1. getr_resolve.
      rewrite H12. rewrite u_Z2bv by lia. lia. }
  (* 0x111a8 addi a3,a3,-1 : k-- *)
  set (regs7 := regupd regs6 13 (Z_to_bv 64 (bv_unsigned k - 1))).
  assert (E8 : RiscvSemantics.step source_segs (mkst regs6 0x111a8 m1 rrom)
               = MachineOk (mkst regs7 0x111ac m1 rrom)).
  { rewrite (step_addi_at source_segs regs6 0x111a8 m1 rrom _ 13 13 _
               (Z_to_bv 64 (bv_unsigned k - 1)) SF_111a8 eq_refl SD_111a8 eq_refl).
    - wlits. reflexivity.
    - unfold regs6, regs5, regs4, regs3, regs2, regs1. getr_resolve. rewrite H13.
      imm_norm. rewrite v_addi_m1 by lia. reflexivity. }
  assert (Hr7_2 : reg_get regs7 2 = Z_to_bv 64 (bv_unsigned rsp - 80)).
  { unfold regs7, regs6, regs5, regs4, regs3, regs2, regs1.
    rewrite !regupd_other by reg_neq_tac. exact H2. }
  destruct (Z.le_gt_cases (bv_unsigned v) 9) as [Hle9 | Hgt9].
  - (* single digit: exit the loop, one store *)
    assert (Hudec1 : udec (bv_unsigned v) = [Z_to_bv 8 (48 + bv_unsigned v)]).
    { rewrite udec_single by lia. reflexivity. }
    assert (E9 : RiscvSemantics.step source_segs (mkst regs7 0x111ac m1 rrom)
                 = MachineOk (mkst regs7 0x111b0 m1 rrom)).
    { rewrite (step_bltu_ft source_segs regs7 0x111ac m1 rrom _ 10 16 _
                 SF_111ac eq_refl SD_111ac).
      - wlits. reflexivity.
      - unfold regs7, regs6, regs5, regs4, regs3, regs2, regs1. getr_resolve.
        regupd_resolve. rewrite H10.
        rewrite c_ltu_ltb. apply Z.ltb_ge. rewrite u_Z2bv by lia. lia. }
    exists regs7. split; [|split].
    + intros x Hx13 Hx14 Hx15 Hx16.
      unfold regs7, regs6, regs5, regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs7, regs6. rewrite !regupd_other by reg_neq_tac.
      unfold regs5. rewrite regupd_same. rewrite Hudec1. cbn [length].
      apply bv_eq. rewrite u_Z2bv by lia. lia.
    + assert (Hm1 : m1 = wbytes m
        (Z_to_bv 64 (bv_unsigned rsp - 56 + (bv_unsigned k + 1
           - Z.of_nat (length (udec (bv_unsigned v)))))) (udec (bv_unsigned v))).
      { unfold m1, a6a. rewrite Hudec1. cbn [length].
        replace dgz with (bv_unsigned v) by (unfold dgz; rewrite Z.mod_small by lia; reflexivity).
        f_equal. f_equal. lia. }
      rewrite <- Hm1.
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      eapply mst_step; [reflexivity | exact E7 |].
      eapply mst_step; [reflexivity | exact E8 |].
      eapply mst_step; [reflexivity | exact E9 |].
      apply mst_refl.
  - (* multi-digit: loop back to 0x1118c with v/10, k-1 *)
    assert (Hudec : udec (bv_unsigned v)
                    = udec (bv_unsigned v / 10) ++ [Z_to_bv 8 (48 + dgz)]).
    { unfold dgz. apply udec_step; lia. }
    assert (HLv : Z.of_nat (length (udec (bv_unsigned v)))
                  = (Z.of_nat (length (udec (bv_unsigned v / 10))) + 1)%Z).
    { rewrite Hudec. rewrite length_app. cbn [length]. lia. }
    assert (Hv10_1 : (1 <= bv_unsigned v / 10)%Z)
      by (apply Z.div_le_lower_bound; lia).
    assert (Hv10_64 : (bv_unsigned v / 10 < 2 ^ 64)%Z)
      by (pose proof (Z.div_le_upper_bound (bv_unsigned v) 10 (bv_unsigned v)
             ltac:(lia) ltac:(lia)); lia).
    assert (Hv10_f : (bv_unsigned v / 10 < 10 ^ Z.of_nat f)%Z).
    { apply Z.div_lt_upper_bound; [lia|].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hvf by lia. lia. }
    assert (Huv10 : bv_unsigned (Z_to_bv 64 (bv_unsigned v / 10)) = (bv_unsigned v / 10)%Z)
      by (rewrite u_Z2bv by lia; reflexivity).
    assert (Huk1 : bv_unsigned (Z_to_bv 64 (bv_unsigned k - 1)) = (bv_unsigned k - 1)%Z)
      by (rewrite u_Z2bv by lia; reflexivity).
    assert (Hr7_10 : reg_get regs7 10 = Z_to_bv 64 9).
    { unfold regs7, regs6, regs5, regs4, regs3, regs2, regs1.
      rewrite !regupd_other by reg_neq_tac. exact H10. }
    assert (Hr7_12 : reg_get regs7 12 = Z_to_bv 64 10).
    { unfold regs7, regs6, regs5, regs4, regs3, regs2, regs1.
      rewrite !regupd_other by reg_neq_tac. exact H12. }
    assert (Hr7_11 : reg_get regs7 11 = dbuf).
    { unfold regs7, regs6, regs5, regs4, regs3, regs2, regs1.
      rewrite !regupd_other by reg_neq_tac. exact H11. }
    assert (Hr7_13 : reg_get regs7 13 = Z_to_bv 64 (bv_unsigned k - 1))
      by (unfold regs7; apply regupd_same).
    assert (Hr7_15 : reg_get regs7 15 = Z_to_bv 64 (bv_unsigned v / 10)).
    { unfold regs7. rewrite regupd_other by reg_neq_tac.
      unfold regs6. apply regupd_same. }
    assert (E9 : RiscvSemantics.step source_segs (mkst regs7 0x111ac m1 rrom)
                 = MachineOk (mkst regs7 0x1118c m1 rrom)).
    { rewrite (step_bltu_tk source_segs regs7 0x111ac m1 rrom _ 10 16 _
                 SF_111ac eq_refl SD_111ac).
      - wlits. reflexivity.
      - unfold regs7, regs6, regs5, regs4, regs3, regs2, regs1. getr_resolve.
        regupd_resolve. rewrite H10.
        rewrite c_ltu_ltb. apply Z.ltb_lt. rewrite u_Z2bv by lia. lia. }
    destruct (IH m1 (Z_to_bv 64 (bv_unsigned v / 10)) (Z_to_bv 64 (bv_unsigned k - 1)) regs7
                ltac:(rewrite Huv10; exact Hv10_1)
                ltac:(rewrite Huv10; exact Hv10_f)
                ltac:(rewrite Huv10, Huk1; rewrite HLv in HLk; lia)
                ltac:(rewrite Huk1; lia)
                Hr7_2 Hr7_10 Hr7_12 Hr7_11 Hr7_13 Hr7_15
                ltac:(unfold m1; solve_mem_grows))
      as (regs' & Hag' & H14' & Hms').
    exists regs'. split; [|split].
    + intros x Hx13 Hx14 Hx15 Hx16.
      rewrite (Hag' x Hx13 Hx14 Hx15 Hx16).
      unfold regs7, regs6, regs5, regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + rewrite H14'. rewrite Huv10, Huk1. rewrite HLv.
      apply bv_eq. rewrite !u_Z2bv by (rewrite ?Huv10; lia). lia.
    + (* memory reconciliation *)
      set (L' := Z.of_nat (length (udec (bv_unsigned v / 10)))) in *.
      rewrite Huv10 in Hms'. rewrite Huk1 in Hms'.
      fold L' in Hms'.
      replace (wbytes m
        (Z_to_bv 64 (bv_unsigned rsp - 56 + (bv_unsigned k + 1
           - Z.of_nat (length (udec (bv_unsigned v)))))) (udec (bv_unsigned v)))
        with (wbytes m1
          (Z_to_bv 64 (bv_unsigned rsp - 56 + (bv_unsigned k - 1 + 1 - L')))
          (udec (bv_unsigned v / 10))).
      2:{ unfold m1, a6a. rewrite HLv. rewrite Hudec.
          fold L'.
          replace (bv_unsigned k + 1 - (L' + 1))%Z with (bv_unsigned k - 1 + 1 - L')%Z by lia.
          rewrite wbytes_app.
          replace (Z_to_bv 64 (bv_unsigned rsp - 56 + (bv_unsigned k - 1 + 1 - L'))
                   + nat_to_word (length (udec (bv_unsigned v / 10))))
            with (Z_to_bv 64 (bv_unsigned rsp - 56 + bv_unsigned k)).
          2:{ rewrite word_add_nat. apply bv_eq.
              rewrite (u_Z2bv (bv_unsigned rsp - 56 + (bv_unsigned k - 1 + 1 - L'))
                         ltac:(unfold L'; lia) ltac:(unfold L'; lia)).
              rewrite !u_Z2bv by (unfold L'; lia).
              unfold L'. lia. }
          symmetry. apply wbytes_disjoint_comm.
          - rewrite !u_Z2bv by (unfold L'; lia). unfold L'. lia.
          - cbn [length]. rewrite u_Z2bv by (unfold L'; lia). lia. }
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      eapply mst_step; [reflexivity | exact E7 |].
      eapply mst_step; [reflexivity | exact E8 |].
      eapply mst_step; [reflexivity | exact E9 |].
      exact Hms'.
Qed.

(* ================================================================= *)
(* Printing the digits and the newline (0x110e4)                      *)
(* ================================================================= *)

(* ================================================================= *)
(* The two put-style write-all retry loops in main                    *)
(* ================================================================= *)

(** [rdn] over the wrapper's own [ra] spill slot, for a buffer that
    avoids it. *)
Lemma read_over_spill : forall (mem : word -> option byte) (p RA : word) k,
  (bv_unsigned p + Z.of_nat k <= bv_unsigned rsp - 88)%Z
  \/ (bv_unsigned rsp - 80 <= bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat k <= 2^64)%Z ->
  rdn source_segs (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 88))
                     (word_to_le_bytes 8 RA)) p k
  = rdn source_segs mem p k.
Proof.
  intros mem p RA k Hd Hnw. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  destruct Hd as [Hd | Hd].
  - apply rdn_wbytes_below; rewrite ?length_N_to_le_bytes; u_norm; lia.
  - apply rdn_wbytes_disjoint; rewrite ?length_N_to_le_bytes; u_norm; lia.
Qed.

(** The FIRST loop (the digit string): the running count is s0 and the
    running pointer s1; entry is 0x11100, the [blez] right after the
    call, and full delivery falls through to 0x11110. *)
Lemma src_put_loop1 : forall (K : machine_state -> Prop) fuel
    (rest : list byte) (p : word) n regs mem,
  (length rest <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length rest)%nat ->
  (Z.of_nat (length rest) < 2^31)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) <= bv_unsigned rsp - 88)%Z
  \/ (bv_unsigned rsp - 80 <= bv_unsigned p
      /\ bv_unsigned p + Z.of_nat (length rest) <= bv_unsigned rsp)%Z ->
  reg_get regs 1 = (0x11100 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
  reg_get regs 8 = len_word rest ->
  reg_get regs 9 = p ->
  reg_get regs 10 = len_word (firstn n rest) ->
  mem_grows wmem mem ->
  rdn source_segs mem p (length rest) = Some rest ->
  (forall regs' mem',
     reg_get regs' 1 = (0x11100 : word) ->
     reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
     reg_get regs' 18 = reg_get regs 18 ->
     mem_grows wmem mem' ->
     (forall x : word,
        (bv_unsigned x < bv_unsigned rsp - 88)%Z
        \/ (bv_unsigned rsp - 80 <= bv_unsigned x)%Z ->
        mem' x = mem x) ->
     K (mkst regs' (0x11110 : word) mem' rrom)) ->
  to_wall_tail source_segs (Z_to_bv 64 1)
    (mkst regs (0x11100 : word) mem rrom) (skipn n rest) K.
Proof.
  intros K fuel. induction fuel as [|fuel IH];
    intros rest p n regs mem Hfuel Hn1 Hn2 Hlen Hp
           H1 H2 H8 H9 H10 Hgrow Hread Hcont.
  { lia. }
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi. pose proof stack_max_size_val as Hsms.
  pose proof (u64_range p) as Hup.
  assert (Hupn : bv_unsigned (p + nat_to_word n)
                 = (bv_unsigned p + Z.of_nat n)%Z).
  { assert (Hb : (0 <= bv_unsigned p + Z.of_nat n < 2^64)%Z)
      by (destruct Hp as [Hp'|[Hpa Hpb]]; lia).
    rewrite word_add_nat_Z by lia. apply u_Z2bv; lia. }
  (* 0x11100: blez a0 falls through (the delivery is nonempty) *)
  chain_step;
    [ reflexivity
    | eapply step_bge_ft;
      [ exact SF_11100 | reflexivity | exact SD_11100
      | getr_resolve; rewrite H10; apply c_lts_0_pos;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x11104: sub s0,s0,a0 *)
  stepiv SF_11104 SD_11104 (len_word (skipn n rest))
    ltac:(getr_resolve; rewrite H8, H10; apply v_sub_len_firstn; lia).
  (* 0x11108: add s1,s1,a0 *)
  stepiv SF_11108 SD_11108 (p + nat_to_word n)
    ltac:(getr_resolve; rewrite H9, H10; apply v_add_len_firstn; lia).
  destruct (Nat.eq_dec n (length rest)) as [-> | Hne].
  - (* full delivery: bnez s0 not taken *)
    rewrite skipn_all.
    chain_step;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact SF_1110c | reflexivity | exact SD_1110c
        | getr_resolve; apply c_eq_0_of_u; reflexivity ]
      | norm_pc ].
    apply twt_done. apply Hcont.
    + regupd_resolve; exact H1.
    + regupd_resolve; exact H2.
    + regupd_resolve; reflexivity.
    + exact Hgrow.
    + intros x Hx; reflexivity.
  - (* short delivery: bnez s0 taken, reissue *)
    chain_step;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact SF_1110c | reflexivity | exact SD_1110c
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* 0x110f0: mv a2,s0 *)
    stepiv SF_110f0 SD_110f0 (len_word (skipn n rest))
      ltac:(getr_resolve; apply v_addi_0).
    (* 0x110f4: mv a1,s1 *)
    stepiv SF_110f4 SD_110f4 (p + nat_to_word n)
      ltac:(getr_resolve; apply v_addi_0).
    (* 0x110f8: li a0,1 *)
    stepiv SF_110f8 SD_110f8 (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* 0x110fc: jal ra,put *)
    chain_step;
      [ reflexivity
      | eapply step_jal_link; [ exact SF_110fc | reflexivity | exact SD_110fc ]
      | step_simpl ].
    assert (Hsk : rdn source_segs mem (p + nat_to_word n)
                    (length (skipn n rest)) = Some (skipn n rest)).
    { pose proof (SeqExec.rdn_skipn source_segs mem (length rest) p rest n Hread Hn2)
        as H. rewrite length_skipn. exact H. }
    eapply source_put with (K := K) (buf := skipn n rest)
      (pbuf := p + nat_to_word n) (len := len_word (skipn n rest))
      (RA := (0x11100 : word)).
    + regupd_resolve; bveq.
    + regupd_resolve; exact H2.
    + regupd_resolve; reflexivity.
    + regupd_resolve; reflexivity.
    + regupd_resolve; reflexivity.
    + rewrite u_len_word by (rewrite length_skipn; lia);
      rewrite length_skipn; lia.
    + rewrite u_len_word by (rewrite length_skipn; lia);
      rewrite length_skipn; lia.
    + rewrite u_len_word by (rewrite length_skipn; lia).
      rewrite Hupn, length_skipn. unfold TASK_SIZE.
      destruct Hp as [Hp'|[Hpa Hpb]]; lia.
    + bveq.
    + replace (word_to_nat (len_word (skipn n rest)))
        with (length (skipn n rest))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      assert (HdA : (bv_unsigned (p + nat_to_word n)
                     + Z.of_nat (length (skipn n rest))
                     <= bv_unsigned rsp - 88)%Z
                    \/ (bv_unsigned rsp - 80
                        <= bv_unsigned (p + nat_to_word n))%Z).
      { rewrite Hupn, length_skipn.
        destruct Hp as [Hp|[Hpa Hpb]].
        - left. lia.
        - right. lia. }
      assert (HnwA : (bv_unsigned (p + nat_to_word n)
                      + Z.of_nat (length (skipn n rest)) <= 2^64)%Z).
      { rewrite Hupn, length_skipn.
        destruct Hp as [Hp|[Hpa Hpb]]; lia. }
      rewrite read_over_spill; [ exact Hsk | exact HdA | exact HnwA ].
    + exact Hgrow.
    + intros regs' mem' m Hm1 Hm2 R1 R2 R8 R10 R9 R18 Hgrow' Hmem'.
      apply (IH (skipn n rest) (p + nat_to_word n) m).
      * rewrite length_skipn; lia.
      * exact Hm1.
      * exact Hm2.
      * rewrite length_skipn; lia.
      * rewrite Hupn, length_skipn.
        destruct Hp as [Hp'|[Hpa Hpb]].
        { left. lia. }
        { right. split; lia. }
      * exact R1.
      * exact R2.
      * rewrite R8. regupd_resolve. reflexivity.
      * rewrite R9. regupd_resolve. reflexivity.
      * exact R10.
      * exact Hgrow'.
      * rewrite (rdn_ext source_segs (length (skipn n rest)) mem' mem);
          [ exact Hsk
          | rewrite length_skipn; lia
          | intros x Hx; apply Hmem'; rewrite length_skipn in Hx; lia ].
      * intros regs'' mem'' R1' R2' R18' Hgrow'' Hmem''.
        apply Hcont; try assumption.
        { rewrite R18'. rewrite R18. regupd_resolve. reflexivity. }
        { intros x Hx. rewrite Hmem'' by exact Hx. apply Hmem'. exact Hx. }
Qed.

Lemma source_print_tail : forall regs (M : word -> option byte) (sum : Z),
  (0 <= sum)%Z -> (sum < 2^64)%Z ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
  reg_get regs 11 = dbuf ->
  reg_get regs 15 = Z_to_bv 64 (24 - Z.of_nat (length (udec sum))) ->
  M (0x12000 : word) = None ->
  rdn source_segs M (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat = Some (word_to_le_bytes 8 (0x111f4 : word)) ->
  (forall a : word,
     In a [Z_to_bv 64 (bv_unsigned rsp - 16); Z_to_bv 64 (bv_unsigned rsp - 24);
           Z_to_bv 64 (bv_unsigned rsp - 32)] ->
     rdn source_segs M a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  (* the scratch stores below are machine stores into the stack frame *)
  mem_grows wmem M ->
  to_wallexit source_segs (Z_to_bv 64 1)
    [udec sum; [Z_to_bv 8 10]] (Z_to_bv 64 0)
    (mkst regs 0x110e4
      (wbytes M (Z_to_bv 64 (bv_unsigned rsp - 56 + (24 - Z.of_nat (length (udec sum))))) (udec sum)) rrom)
    .
Proof.
  intros regs M sum Hsum0 Hsum H2 H11 H15 Hnl Hra Hsl Hgrow.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  set (Lv := Z.of_nat (length (udec sum))).
  assert (HLv1 : (1 <= Lv)%Z)
    by (unfold Lv; pose proof (udec_len_pos sum); lia).
  assert (HLv20 : (Lv <= 20)%Z)
    by (unfold Lv; pose proof (udec_len_le sum Hsum0 Hsum); lia).
  set (base := Z_to_bv 64 (bv_unsigned rsp - 56 + (24 - Lv))).
  set (Md := wbytes M base (udec sum)).
  split; [unfold Lv in HLv1; lia|].
  (* 0x110e4 li s0,24 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 24);
      [ exact SF_110e4 | reflexivity | exact SD_110e4 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* 0x110e8 add s1,a1,a5 : s1 = base *)
  chain_step;
    [ reflexivity
    | eapply step_add_at with (v := base);
      [ exact SF_110e8 | reflexivity | exact SD_110e8 | reflexivity
      | getr_resolve; regupd_resolve; rewrite H11, H15; unfold base, dbuf; apply bv_eq;
        rewrite v_add_small by (u_norm; lia); u_norm; lia ]
    | norm_pc ].
  (* 0x110ec sub s0,s0,a5 : s0 = Lv *)
  chain_step;
    [ reflexivity
    | eapply step_sub_at with (v := Z_to_bv 64 Lv);
      [ exact SF_110ec | reflexivity | exact SD_110ec | reflexivity
      | getr_resolve; regupd_resolve; rewrite H15; apply bv_eq;
        rewrite v_sub_small by (u_norm; lia); u_norm; lia ]
    | norm_pc ].
  (* 0x110f0 mv a2,s0 : a2 = Lv *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 Lv);
      [ exact SF_110f0 | reflexivity | exact SD_110f0 | reflexivity
      | getr_resolve; regupd_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* 0x110f4 mv a1,s1 : a1 = base *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := base);
      [ exact SF_110f4 | reflexivity | exact SD_110f4 | reflexivity
      | getr_resolve; regupd_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* 0x110f8 li a0,1 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 1);
      [ exact SF_110f8 | reflexivity | exact SD_110f8 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* 0x110fc jal ra,put : ra = 0x11100 *)
  chain_step;
    [ reflexivity
    | eapply step_jal_link; [ exact SF_110fc | reflexivity | exact SD_110fc ]
    | step_simpl ].
  (* put(1, base, Lv) : writes udec sum *)
  eapply source_put with (K := to_wallexit source_segs (Z_to_bv 64 1)
                                  [[Z_to_bv 8 10]] (Z_to_bv 64 0))
    (buf := udec sum) (pbuf := base) (len := Z_to_bv 64 Lv)
    (RA := (0x11100 : word)).
  - regupd_resolve. bveq.
  - regupd_resolve. exact H2.
  - regupd_resolve. reflexivity.
  - regupd_resolve. reflexivity.
  - regupd_resolve. reflexivity.
  - rewrite u_Z2bv by lia. lia.
  - rewrite u_Z2bv by lia. unfold Lv. lia.
  - rewrite u_Z2bv by lia. unfold base, TASK_SIZE. u_norm. fold Lv. lia.
  - bveq.
  - rewrite rdn_wbytes_disjoint
      by (rewrite ?length_N_to_le_bytes; unfold word_to_nat; unfold base; u_norm; lia).
    unfold Md.
    replace (word_to_nat (Z_to_bv 64 Lv)) with (length (udec sum))
      by (unfold word_to_nat; rewrite u_Z2bv by lia; unfold Lv; rewrite Nat2Z.id; reflexivity).
    apply rdn_wbytes_hit. unfold base. u_norm. lia.
  - (* the frame is writable: [Md] only adds to the given overlay *)
    unfold Md. solve_mem_grows.
  - (* continuation after the first write *)
    intros regs1 mem1 nA HnA1 HnA2 H1_1 H1_2 H1_8 H1_10 H1_9 H1_18 Hgrow1 Hmem1.
    assert (Hmd_eq : forall x : word, (bv_unsigned rsp - 32 <= bv_unsigned x)%Z -> mem1 x = M x).
    { intros x Hx. rewrite Hmem1 by (right; lia). unfold Md.
      apply wbytes_above. unfold base. u_norm. fold Lv. lia. }
    assert (Hnl1 : mem1 (0x12000 : word) = None).
    { rewrite Hmem1 by (left; change (bv_unsigned (0x12000:word)) with 0x12000%Z; lia).
      unfold Md. rewrite wbytes_below.
      - exact Hnl.
      - unfold base. u_norm. fold Lv. lia.
      - unfold base. change (bv_unsigned (0x12000:word)) with 0x12000%Z. u_norm. lia. }
    apply (src_put_loop1 _ (length (udec sum)) (udec sum) base nA regs1 mem1).
    + lia.
    + exact HnA1.
    + exact HnA2.
    + unfold Lv in HLv20; lia.
    + right. split; unfold base; u_norm; fold Lv; lia.
    + exact H1_1.
    + exact H1_2.
    + rewrite H1_8. regupd_resolve.
      unfold len_word. fold Lv. reflexivity.
    + rewrite H1_9. regupd_resolve. reflexivity.
    + exact H1_10.
    + exact Hgrow1.
    + erewrite rdn_ext;
        [ | unfold base; u_norm; fold Lv; lia
        | intros x Hx; apply Hmem1; unfold base in Hx; revert Hx; u_norm;
          fold Lv; intro Hx; right; lia ].
      unfold Md. apply rdn_wbytes_hit. unfold base. u_norm. fold Lv. lia.
    + { intros regsB memB HB_1 HB_2 HB_18 HgrowB HmemB.
      assert (HnlB : memB (0x12000 : word) = None).
      { rewrite HmemB
          by (left; change (bv_unsigned (0x12000:word)) with 0x12000%Z; lia).
        exact Hnl1. }
      assert (Hmd_eqB : forall x : word,
                 (bv_unsigned rsp - 32 <= bv_unsigned x)%Z -> memB x = M x).
      { intros x Hx. rewrite HmemB by (right; lia). apply Hmd_eq. lia. }
      clear HmemB HB_18 Hnl1 Hmd_eq Hmem1 Hgrow1 H1_1 H1_10 H1_8 H1_9 H1_18 H1_2
            HnA1 HnA2.
      clear regs1 mem1 nA.
      rename regsB into regs1. rename memB into mem1.
      rename HB_1 into H1_1. rename HB_2 into H1_2.
      rename HgrowB into Hgrow1. rename HnlB into Hnl1.
      rename Hmd_eqB into Hmd_eq.
    (* 0x11110 lui s0,0x12 -> 0x12000 *)
    chain_step;
      [ reflexivity
      | eapply step_lui_at with (v := (0x12000 : word));
        [ exact SF_11110 | reflexivity | exact SD_11110 | reflexivity | bveq ]
      | norm_pc ].
    (* 0x11114 li s1,1 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 1);
        [ exact SF_11114 | reflexivity | exact SD_11114 | reflexivity
        | getr_resolve; bveq ]
      | norm_pc ].
    (* 0x11118 mv s0,s0 : s0 = 0x12000 (self-move) *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := (0x12000 : word));
        [ exact SF_11118 | reflexivity | exact SD_11118 | reflexivity
        | getr_resolve; regupd_resolve; apply v_addi_0 ]
      | norm_pc ].
    (* 0x1111c mv a2,s1 : a2 = 1 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 1);
        [ exact SF_1111c | reflexivity | exact SD_1111c | reflexivity
        | getr_resolve; regupd_resolve; apply v_addi_0 ]
      | norm_pc ].
    (* 0x11120 mv a1,s0 : a1 = 0x12000 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := (0x12000 : word));
        [ exact SF_11120 | reflexivity | exact SD_11120 | reflexivity
        | getr_resolve; regupd_resolve; apply v_addi_0 ]
      | norm_pc ].
    (* 0x11124 li a0,1 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 1);
        [ exact SF_11124 | reflexivity | exact SD_11124 | reflexivity
        | getr_resolve; bveq ]
      | norm_pc ].
    (* 0x11128 jal ra,put : ra = 0x1112c *)
    chain_step;
      [ reflexivity
      | eapply step_jal_link; [ exact SF_11128 | reflexivity | exact SD_11128 ]
      | step_simpl ].
    (* put(1, 0x12000, 1) : writes the newline *)
    split; [cbn [length]; lia|].
    eapply source_put with (K := to_wallexit source_segs (Z_to_bv 64 1)
                                    [] (Z_to_bv 64 0))
      (buf := [Z_to_bv 8 10]) (pbuf := (0x12000 : word)) (len := Z_to_bv 64 1)
      (RA := (0x1112c : word)).
    + regupd_resolve. bveq.
    + regupd_resolve. exact H1_2.
    + regupd_resolve. reflexivity.
    + regupd_resolve. reflexivity.
    + regupd_resolve. reflexivity.
    + rewrite u_Z2bv by lia. lia.
    + rewrite u_Z2bv by lia. lia.
    + change (bv_unsigned (0x12000 : word)) with 0x12000%Z.
      rewrite u_Z2bv by lia. unfold TASK_SIZE. lia.
    + bveq.
    + replace (word_to_nat (Z_to_bv 64 1)) with 1%nat
        by (unfold word_to_nat; rewrite u_Z2bv by lia; reflexivity).
      rewrite rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes; cbn [length];
            change (bv_unsigned (0x12000:word)) with 0x12000%Z; u_norm; lia).
      apply read_newline. exact Hnl1.
    + exact Hgrow1.
    + (* continuation after the second write : exit 0 *)
      intros regs2 mem2 nB HnB1 HnB2 H2_1 H2_2 H2_8 H2_10 H2_9 H2_18 Hgrow2 Hmem2.
      assert (HnB : nB = 1%nat) by (cbn [length] in HnB2; lia). subst nB.
      cbn [firstn skipn] in H2_10 |- *.
      replace (len_word [Z_to_bv 8 10]) with (Z_to_bv 64 1) in H2_10
        by reflexivity.
      assert (Hmd_eq2 : forall x : word, (bv_unsigned rsp - 32 <= bv_unsigned x)%Z -> mem2 x = M x).
      { intros x Hx. rewrite Hmem2 by (right; lia). apply Hmd_eq. lia. }
      (* 0x1112c bge x0,a0 fall-through *)
      chain_step;
        [ reflexivity
        | eapply step_bge_ft;
          [ exact SF_1112c | reflexivity | exact SD_1112c
          | getr_resolve; rewrite H2_10;
            rewrite c_lts_small by (u_norm; lia); apply Z.ltb_lt; u_norm; lia ]
        | norm_pc ].
      (* 0x11130 sub s1,s1,a0 : s1 = 0 *)
      chain_step;
        [ reflexivity
        | eapply step_sub_at with (v := Z_to_bv 64 0);
          [ exact SF_11130 | reflexivity | exact SD_11130 | reflexivity
          | getr_resolve; rewrite H2_9, H2_10; regupd_resolve; apply bv_eq;
            rewrite v_sub_small by (u_norm; lia); u_norm; lia ]
        | norm_pc ].
      (* 0x11134 add s0,s0,a0 (dead) *)
      chain_step;
        [ reflexivity
        | eapply step_add_at with (v := v_add (reg_get regs2 8) (reg_get regs2 10));
          [ exact SF_11134 | reflexivity | exact SD_11134 | reflexivity
          | getr_resolve; reflexivity ]
        | norm_pc ].
      (* 0x11138 bne s1,x0 fall-through (s1 = 0) *)
      chain_step;
        [ reflexivity
        | eapply step_bne_ft;
          [ exact SF_11138 | reflexivity | exact SD_11138
          | getr_resolve; regupd_resolve; exact c_eq_0_true ]
        | norm_pc ].
      apply twt_done. cbn [to_wallexit].
      (* 0x1113c li a0,0 *)
      chain_step;
        [ reflexivity
        | eapply step_addi_at with (v := Z_to_bv 64 0);
          [ exact SF_1113c | reflexivity | exact SD_1113c | reflexivity
          | getr_resolve; apply v_addi_0 ]
        | norm_pc ].
      (* 0x11140 j 0x11068 (epilogue) *)
      chain_step;
        [ reflexivity
        | eapply step_jal_x0; [ exact SF_11140 | reflexivity | exact SD_11140 ]
        | norm_pc ].
      (* epilogue: exit 0 *)
      apply source_epilogue.
      * regupd_resolve. rewrite H2_2. reflexivity.
      * regupd_resolve. reflexivity.
      * vm_compute. reflexivity.
      * erewrite rdn_ext; [ exact Hra | u_norm; lia | ].
        intros x Hx. apply Hmd_eq2. revert Hx. u_norm. lia.
      * intros a Ha.
        erewrite rdn_ext; [ apply Hsl; exact Ha | | ].
        -- assert (Hab : (bv_unsigned rsp - 32 <= bv_unsigned a
                          <= bv_unsigned rsp - 16)%Z)
             by (repeat destruct Ha as [<-|Ha]; try (exfalso; exact Ha); u_norm; lia).
           u_norm; lia.
        -- intros x Hx.
           assert (Hab : (bv_unsigned rsp - 32 <= bv_unsigned a)%Z)
             by (repeat destruct Ha as [<-|Ha]; try (exfalso; exact Ha); u_norm; lia).
           apply Hmd_eq2. revert Hx. u_norm. lia. }
Qed.

Lemma source_success : forall regs (M : word -> option byte),
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
  reg_get regs 15 = Z_to_bv 64 (sumb arg1) ->
  M (0x12000 : word) = None ->
  rdn source_segs M (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat = Some (word_to_le_bytes 8 (0x111f4 : word)) ->
  (forall a : word,
     In a [Z_to_bv 64 (bv_unsigned rsp - 16); Z_to_bv 64 (bv_unsigned rsp - 24);
           Z_to_bv 64 (bv_unsigned rsp - 32)] ->
     rdn source_segs M a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  (* the scratch stores below are machine stores into the stack frame *)
  mem_grows wmem M ->
  to_wallexit source_segs (Z_to_bv 64 1) (outbufs arg1) (Z_to_bv 64 0)
    (mkst regs 0x110d0 M rrom).
Proof.
  intros regs M H2 H15 Hnl Hra Hsl Hgrow.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le' as HnnLe.
  pose proof (arg1_bytes Hge2) as Hbytes.
  pose proof (sumb_nonneg arg1) as Hsum0.
  assert (Hsum64 : (sumb arg1 < 2 ^ 64)%Z).
  { pose proof (sumb_le arg1 Hbytes) as Hle. unfold nn in *. lia. }
  unfold outbufs.
  (* 0x110d0 addi a1,sp,24 : a1 = the digit buffer *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := dbuf);
      [ exact SF_110d0 | reflexivity | exact SD_110d0 | reflexivity
      | getr_resolve; rewrite H2; unfold dbuf; sp_norm; f_equal; lia ]
    | norm_pc ].
  destruct (Z.eq_dec (sumb arg1) 0) as [Hsz | Hnz].
  - (* sum = 0 : the '0' path *)
    assert (Hudec0 : udec (sumb arg1) = [Z_to_bv 8 48]) by (rewrite Hsz; reflexivity).
    (* 0x110d4 bne a5,x0 fall-through (a5 = 0) *)
    chain_step;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact SF_110d4 | reflexivity | exact SD_110d4
        | getr_resolve; regupd_resolve; rewrite H15, Hsz; exact c_eq_0_true ]
      | norm_pc ].
    (* 0x110d8 li a5,48 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 48);
        [ exact SF_110d8 | reflexivity | exact SD_110d8 | reflexivity
        | getr_resolve; bveq ]
      | norm_pc ].
    (* 0x110dc sb a5,47(sp) : store '0' at rsp-33 *)
    chain_step;
      [ reflexivity
      | eapply step_sb_at with (a := Z_to_bv 64 (bv_unsigned rsp - 33)) (b := Z_to_bv 8 48);
        [ exact SF_110dc | reflexivity | exact SD_110dc
        | getr_resolve; regupd_resolve; rewrite H2; sp_norm; f_equal; lia
        | getr_resolve; regupd_resolve; bveq
        | solve_store_ok_inv ]
      | step_simpl ].
    (* 0x110e0 li a5,23 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 23);
        [ exact SF_110e0 | reflexivity | exact SD_110e0 | reflexivity
        | getr_resolve; bveq ]
      | norm_pc ].
    match goal with
    |- to_wallexit _ _ _ _ (mkst ?R _ ?Mem _) =>
        replace Mem with
          (wbytes M (Z_to_bv 64 (bv_unsigned rsp - 56 + (24 - Z.of_nat (length (udec (sumb arg1)))))) (udec (sumb arg1)))
    end.
    2:{ rewrite Hudec0. cbn [length].
        replace (bv_unsigned rsp - 56 + (24 - Z.of_nat 1))%Z with (bv_unsigned rsp - 33)%Z by lia.
        reflexivity. }
    apply source_print_tail.
    + exact Hsum0.
    + exact Hsum64.
    + regupd_resolve. exact H2.
    + regupd_resolve. reflexivity.
    + regupd_resolve. rewrite Hudec0. cbn [length]. f_equal.
    + exact Hnl.
    + exact Hra.
    + exact Hsl.
    + solve_mem_grows.
  - (* sum > 0 : the udec loop path *)
    assert (Hsum1 : (1 <= sumb arg1)%Z) by lia.
    (* 0x110d4 bne a5,x0 taken (a5 <> 0) -> 0x11180 *)
    chain_step;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact SF_110d4 | reflexivity | exact SD_110d4
        | getr_resolve; regupd_resolve; rewrite H15; apply c_eq_0_false;
          rewrite u_Z2bv by lia; lia ]
      | norm_pc ].
    (* 0x11180 li a3,23 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 23);
        [ exact SF_11180 | reflexivity | exact SD_11180 | reflexivity
        | getr_resolve; bveq ]
      | norm_pc ].
    (* 0x11184 li a2,10 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 10);
        [ exact SF_11184 | reflexivity | exact SD_11184 | reflexivity
        | getr_resolve; bveq ]
      | norm_pc ].
    (* 0x11188 li a0,9 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 9);
        [ exact SF_11188 | reflexivity | exact SD_11188 | reflexivity
        | getr_resolve; bveq ]
      | norm_pc ].
    (* the decimal loop *)
    match goal with
    |- to_wallexit _ _ _ _ (mkst ?R 0x1118c _ _) =>
        destruct (source_udec_loop 25 M (Z_to_bv 64 (sumb arg1)) (Z_to_bv 64 23) R
                    ltac:(rewrite u_Z2bv by lia; lia)
                    ltac:(rewrite u_Z2bv by lia;
                          change (10 ^ Z.of_nat 25)%Z with 10000000000000000000000000%Z; lia)
                    ltac:(rewrite !u_Z2bv by lia;
                          pose proof (udec_len_le (sumb arg1) Hsum0 Hsum64); lia)
                    ltac:(rewrite u_Z2bv by lia; lia)
                    ltac:(regupd_resolve; exact H2)
                    ltac:(regupd_resolve; reflexivity)
                    ltac:(regupd_resolve; reflexivity)
                    ltac:(regupd_resolve; reflexivity)
                    ltac:(regupd_resolve; reflexivity)
                    ltac:(regupd_resolve; exact H15)
                    ltac:(solve_mem_grows))
          as (regsU & HagU & H14U & HmsU)
    end.
    rewrite !u_Z2bv in H14U, HmsU by lia.
    change (23 + 1)%Z with 24%Z in H14U, HmsU.
    eapply msteps_to_wallexit; [exact HmsU|].
    pose proof (udec_len_pos (sumb arg1)) as HLp.
    pose proof (udec_len_le (sumb arg1) Hsum0 Hsum64) as HLe.
    (* 0x111b0 sext.w a5,a4 : a5 = 24 - L *)
    chain_step;
      [ reflexivity
      | eapply step_addiw_at with (v := Z_to_bv 64 (24 - Z.of_nat (length (udec (sumb arg1)))));
        [ exact SF_111b0 | reflexivity | exact SD_111b0 | reflexivity
        | getr_resolve; rewrite H14U; imm_norm; apply v_addiw_id;
          rewrite u_Z2bv by lia; lia ]
      | norm_pc ].
    (* 0x111b4 j 0x110e4 *)
    chain_step;
      [ reflexivity
      | eapply step_jal_x0; [ exact SF_111b4 | reflexivity | exact SD_111b4 ]
      | norm_pc ].
    apply source_print_tail.
    + exact Hsum0.
    + exact Hsum64.
    + regupd_resolve. rewrite (HagU 2) by reg_neq_tac. regupd_resolve. exact H2.
    + regupd_resolve. rewrite (HagU 11) by reg_neq_tac. regupd_resolve. reflexivity.
    + regupd_resolve. reflexivity.
    + exact Hnl.
    + exact Hra.
    + exact Hsl.
    + solve_mem_grows.
Qed.

(* ================================================================= *)
(* After the second brk: reload the spilled break, copy, sum, print    *)
(* ================================================================= *)

Lemma read_spill : forall r,
  rdn source_segs (fmem2 r) (Z_to_bv 64 (bv_unsigned rsp - 72)) 8%nat
  = Some (word_to_le_bytes 8 (r + nN)).
Proof.
  intro r. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  unfold fmem2. apply rdn_wbytes_hit8. u_norm. lia.
Qed.

Lemma source_run_empty : (nn = 0)%nat -> forall regs5 (r : word),
  (bv_unsigned r + Z.of_nat nn < 2^64)%Z ->
  reg_get regs5 1 = (0x110b0 : word) -> reg_get regs5 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
  reg_get regs5 8 = nN -> reg_get regs5 18 = ptr ->
  to_wallexit source_segs (Z_to_bv 64 1) (outbufs arg1) (Z_to_bv 64 0)
    (mkst (regupd regs5 10 (r + nN)) 0x1121c (fmem2 r) rrom).
Proof.
  intros Hnn0 regs5 r Hrw H1 H2 H8 H18.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  assert (Harg : arg1 = []) by (apply length_zero_iff_nil; exact Hnn0).
  assert (HnN0 : nN = Z_to_bv 64 0) by (unfold nN; rewrite Hnn0; reflexivity).
  (* ret 0x1121c -> 0x110b0 *)
  chain_step;
    [ reflexivity
    | eapply step_jalr_x0 with (tgt := (0x110b0 : word));
      [ exact SF_1121c | reflexivity | exact SD_1121c
      | getr_resolve; regupd_resolve; exact H1 ]
    | norm_pc ].
  (* 0x110b0 ld a1,8(sp) : reload the requested break *)
  chain_step;
    [ reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 (r + nN)) (v := r + nN);
      [ exact SF_110b0 | reflexivity | exact SD_110b0
      | match goal with |- rdn _ _ ?a _ = _ =>
          replace a with (Z_to_bv 64 (bv_unsigned rsp - 72))
            by (getr_resolve; regupd_resolve; rewrite H2; sp_norm; f_equal; lia) end;
        apply read_spill
      | exact (bytes_le_to_Z_8 _) ]
    | step_simpl ].
  (* 0x110b4 li a5,0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_110b4 | reflexivity | exact SD_110b4 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* 0x110b8 bne a1,a0 fall-through *)
  chain_step;
    [ reflexivity
    | eapply step_bne_ft;
      [ exact SF_110b8 | reflexivity | exact SD_110b8
      | getr_resolve; regupd_resolve; apply c_eq_refl ]
    | norm_pc ].
  (* 0x110bc bne a5,s0 fall-through (0 = n = 0) *)
  chain_step;
    [ reflexivity
    | eapply step_bne_ft;
      [ exact SF_110bc | reflexivity | exact SD_110bc
      | getr_resolve; regupd_resolve; rewrite H8, HnN0; exact c_eq_0_true ]
    | norm_pc ].
  (* 0x110c0 li a4,0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_110c0 | reflexivity | exact SD_110c0 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* 0x110c4 li a5,0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_110c4 | reflexivity | exact SD_110c4 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* 0x110c8 li a2,8 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 8);
      [ exact SF_110c8 | reflexivity | exact SD_110c8 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* 0x110cc bltu a4,s0 fall-through (0 < 0 false) *)
  chain_step;
    [ reflexivity
    | eapply step_bltu_ft;
      [ exact SF_110cc | reflexivity | exact SD_110cc
      | getr_resolve; regupd_resolve; rewrite H8, HnN0;
        rewrite c_ltu_ltb; apply Z.ltb_ge; u_norm; lia ]
    | norm_pc ].
  (* print (sum = 0) *)
  apply source_success.
  - regupd_resolve. exact H2.
  - regupd_resolve. rewrite Harg. reflexivity.
  - apply (fmem2_none r (0x12000 : word));
      [ change (bv_unsigned (0x12000:word)) with 0x12000%Z; rewrite stack_max_size_val; lia
      | left; change (bv_unsigned (0x12000:word)) with 0x12000%Z; lia ].
  - apply read_slot_ra2.
  - apply read_slot_02.
  - unfold fmem2. solve_mem_grows.
Qed.

Lemma source_run_success : forall regs5 (r grant : word),
  (bv_unsigned nN <= bv_unsigned grant)%Z ->
  (Z.of_nat (8 * ((nn + 7) / 8)) <= bv_unsigned grant)%Z ->
  (bv_unsigned r + bv_unsigned grant <= bv_unsigned rsp - stack_max_size)%Z ->
  region_free (segments_reserved source_segs) r grant = true ->
  (0 < bv_unsigned r)%Z -> (nn <> 0)%nat ->
  reg_get regs5 1 = (0x110b0 : word) -> reg_get regs5 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
  reg_get regs5 8 = nN -> reg_get regs5 9 = r -> reg_get regs5 18 = ptr ->
  to_wallexit source_segs (Z_to_bv 64 1) (outbufs arg1) (Z_to_bv 64 0)
    (mkst (regupd regs5 10 (r + nN)) 0x1121c (zmem (fmem2 r) r grant) rrom).
Proof.
  intros regs5 r grant Hgrant Hpad Hphysceil Hphysfree Hr0 Hnnz H1 H2 H8 H9 H18.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le' as HnnLe.
  pose proof ptr_lo' as Hplo. pose proof ptr_hi' as Hphi.
  set (chunks := ((nn + 7) / 8)%nat).
  set (total := (8 * chunks)%nat).
  change (Z.of_nat total <= bv_unsigned grant)%Z in Hpad.
  pose proof (Nat.div_mod (nn + 7) 8 ltac:(lia)) as Hdiv.
  pose proof (Nat.mod_upper_bound (nn + 7) 8 ltac:(lia)) as Hrem.
  assert (Hchunks : (1 <= chunks)%nat) by (unfold chunks; lia).
  assert (Hstop : (8 * (chunks - 1) < nn <= 8 * chunks)%nat)
    by (unfold chunks in *; lia).
  assert (Hlast : (8 * (chunks - 1) < nn)%nat) by exact (proj1 Hstop).
  assert (Hntotal : (nn <= total)%nat) by (unfold total; lia).
  assert (Hceil : (bv_unsigned r + Z.of_nat nn <= bv_unsigned rsp - stack_max_size)%Z).
  { rewrite <- u_nN'. lia. }
  assert (Htotalceil : (bv_unsigned r + Z.of_nat total
                        <= bv_unsigned rsp - stack_max_size)%Z)
    by lia.
  assert (Hfree : region_free (segments_reserved source_segs) r nN = true).
  { eapply region_free_prefix; [exact Hgrant|exact Hphysfree]. }
  assert (Hceil' : (bv_unsigned r + Z.of_nat nn <= bv_unsigned rsp - 8388608)%Z)
    by exact Hceil.
  assert (Hphysceil' :
      (bv_unsigned r + bv_unsigned grant <= bv_unsigned rsp - 8388608)%Z)
    by exact Hphysceil.
  assert (Hrw : (bv_unsigned r + Z.of_nat total < 2 ^ 64)%Z) by lia.
  set (mem0 := zmem (fmem2 r) r grant).
  set (M := wbytes mem0 r arg1).
  assert (Hstr0 : rdn source_segs mem0 ptr (S nn) = Some (arg1 ++ [Z_to_bv 8 0])).
  { unfold mem0. rewrite rdn_zmem_out.
    - destruct (read_str_f8_2 r) as (tl & Htl & Hread8).
      apply (rdn_firstn source_segs (fmem2 r) (nn + 8) ptr _ (S nn)) in Hread8; [|lia].
      rewrite Hread8. f_equal.
      rewrite firstn_app.
      rewrite firstn_all2 by (unfold nn; lia).
      replace (S nn - length arg1)%nat with 1%nat by (unfold nn; lia).
      cbn [firstn app]. reflexivity.
    - rewrite Nat2Z.inj_succ. lia.
    - right. lia. }
  assert (Hbuf : rdn source_segs M r nn = Some arg1).
  { unfold M. replace nn with (length arg1) by reflexivity. apply rdn_wbytes_hit.
    change (Z.of_nat (length arg1)) with (Z.of_nat nn). lia. }
  assert (Hbyte : forall i, (i < total)%nat ->
      rdn source_segs M (r + nat_to_word i) 1 =
        Some [nth i arg1 (Z_to_bv 8 0)]).
  { intros i Hi. destruct (lt_dec i nn) as [Hin|Hout].
    - exact (rdn_nth source_segs M nn r arg1 i Hbuf Hin).
    - unfold M. rewrite rdn_wbytes_disjoint.
      + unfold mem0. rewrite nth_overflow by (unfold nn in Hout; lia).
        apply rdn_zmem_in1. rewrite word_add_nat by lia.
        rewrite u_Z2bv by lia. lia.
      + change (Z.of_nat (length arg1)) with (Z.of_nat nn).
        rewrite word_add_nat by lia. rewrite u_Z2bv by lia. lia.
      + rewrite word_add_nat by lia. rewrite u_Z2bv by lia. lia. }
  assert (Hspill : rdn source_segs mem0 (Z_to_bv 64 (bv_unsigned rsp - 72)) 8%nat
                   = Some (word_to_le_bytes 8 (r + nN))).
  { unfold mem0. rewrite rdn_zmem_out.
    - apply read_spill.
    - u_norm. lia.
    - right. u_norm. lia. }
  (* ret 0x1121c -> 0x110b0 ; reload the break ; li a5,0 ; bne fall-through *)
  chain_step;
    [ reflexivity
    | eapply step_jalr_x0 with (tgt := (0x110b0 : word));
      [ exact SF_1121c | reflexivity | exact SD_1121c
      | getr_resolve; regupd_resolve; exact H1 ]
    | norm_pc ].
  chain_step;
    [ reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 (r + nN)) (v := r + nN);
      [ exact SF_110b0 | reflexivity | exact SD_110b0
      | match goal with |- rdn _ _ ?a _ = _ =>
          replace a with (Z_to_bv 64 (bv_unsigned rsp - 72))
            by (getr_resolve; regupd_resolve; rewrite H2; sp_norm; f_equal; lia) end;
        exact Hspill
      | exact (bytes_le_to_Z_8 _) ]
    | step_simpl ].
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_110b4 | reflexivity | exact SD_110b4 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  chain_step;
    [ reflexivity
    | eapply step_bne_ft;
      [ exact SF_110b8 | reflexivity | exact SD_110b8
      | getr_resolve; regupd_resolve; apply c_eq_refl ]
    | norm_pc ].
  (* the forward copy loop, d = nn *)
  match goal with
  |- to_wallexit _ _ _ _ (mkst ?R 0x110bc _ _) =>
      destruct (source_copy r mem0
                  ltac:(unfold mem0; apply store_grant_zmem_prefix;
                        [ exact Hgrant | lia ])
                  Hstr0 Hfree Hr0 Hceil nn R
                  (Nat.le_refl nn)
                  ltac:(regupd_resolve; exact H18)
                  ltac:(regupd_resolve; exact H9)
                  ltac:(regupd_resolve; exact H8)
                  ltac:(regupd_resolve; rewrite Nat.sub_diag; reflexivity))
        as (regsC & HagC & H15C & H9C & H8C & H18C & HmsC)
  end.
  replace (wbytes mem0 r (firstn (nn - nn) arg1)) with mem0 in HmsC
    by (rewrite Nat.sub_diag; cbn [firstn wbytes]; reflexivity).
  eapply msteps_to_wallexit; [exact HmsC|].
  fold M.
  (* 0x110c0 li a4,0 ; 0x110c4 li a5,0 ; 0x110c8 li a2,8 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_110c0 | reflexivity | exact SD_110c0 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_110c4 | reflexivity | exact SD_110c4 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 8);
      [ exact SF_110c8 | reflexivity | exact SD_110c8 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* The chunk loop rounds the logical length up to eight bytes.  Its
     padding reads are zeroes supplied by the physical page grant. *)
  match goal with
  |- to_wallexit _ _ _ _ (mkst ?R 0x110cc _ _) =>
      destruct (source_sum r M total Hbyte Hr0 Htotalceil chunks 0%nat R
                  ltac:(rewrite Nat.add_0_l; exact Hlast)
                  ltac:(rewrite Nat.add_0_l; unfold total; reflexivity)
                  ltac:(regupd_resolve; rewrite Nat.mul_0_r; reflexivity)
                  ltac:(regupd_resolve; exact H9C)
                  ltac:(regupd_resolve; rewrite Nat.mul_0_r; reflexivity)
                  ltac:(regupd_resolve; reflexivity)
                  ltac:(regupd_resolve; exact H8C))
        as (regsS & HagS & H14S & H9S & H15S & H12S & H8S & HmsS)
  end.
  eapply msteps_to_wallexit; [exact HmsS|].
  rewrite Nat.add_0_l in H14S, H15S.
  (* 0x110cc bltu a4,s0 falls through: total = round8(n) >= n. *)
  chain_step;
    [ reflexivity
    | eapply step_bltu_ft;
      [ exact SF_110cc | reflexivity | exact SD_110cc
      | getr_resolve; rewrite H14S, H8S;
        rewrite c_ltu_ltb; apply Z.ltb_ge;
        rewrite u_ntw by (unfold total; pose proof nN_le'; lia);
        rewrite u_nN'; lia ]
    | norm_pc ].
  (* print *)
  apply source_success.
  - rewrite (HagS 2) by reg_neq_tac. regupd_resolve.
    rewrite (HagC 2) by reg_neq_tac. regupd_resolve. exact H2.
  - fold total in H15S. rewrite H15S. rewrite firstn_all2.
    + reflexivity.
    + change (nn <= total)%nat. exact Hntotal.
  - (* M 0x12000 = None *)
    assert (Hdisj :
        (0x12000 + 1 <= bv_unsigned r \/
         bv_unsigned r + bv_unsigned grant <= 0x12000)%Z).
    { destruct (source_free_cases r grant Hphysfree
                  ltac:(rewrite u_nN' in Hgrant; lia)) as [Hc|Hc];
        [right|left]; lia. }
    assert (HMfmem : M (0x12000 : word) = fmem2 r (0x12000 : word)).
    { unfold M, mem0. destruct Hdisj as [Hd|Hd].
      - rewrite wbytes_below.
        + apply zmem_out. left. change (bv_unsigned (0x12000:word)) with 0x12000%Z. lia.
        + change (Z.of_nat (length arg1)) with (Z.of_nat nn). lia.
        + change (bv_unsigned (0x12000:word)) with 0x12000%Z. lia.
      - rewrite wbytes_above.
        + apply zmem_out. right. change (bv_unsigned (0x12000:word)) with 0x12000%Z.
          lia.
        + change (Z.of_nat (length arg1)) with (Z.of_nat nn).
          change (bv_unsigned (0x12000:word)) with 0x12000%Z. lia. }
    rewrite HMfmem. apply (fmem2_none r (0x12000 : word));
      [ change (bv_unsigned (0x12000:word)) with 0x12000%Z; rewrite stack_max_size_val; lia
      | left; change (bv_unsigned (0x12000:word)) with 0x12000%Z; lia ].
  - (* frame ra slot *)
    erewrite rdn_ext; [ apply (read_slot_ra2 r) | u_norm; lia | ].
    intros x Hx. unfold M.
    rewrite wbytes_above by (change (Z.of_nat (length arg1)) with (Z.of_nat nn);
                             revert Hx; u_norm; rewrite ?u_nN'; lia).
    unfold mem0. rewrite zmem_out; [reflexivity| right; revert Hx; u_norm; lia].
  - (* frame zero slots *)
    intros a Ha.
    erewrite rdn_ext; [ apply (read_slot_02 r); exact Ha | | ].
    + assert (Hxlo : (bv_unsigned rsp - 32 <= bv_unsigned a
                      <= bv_unsigned rsp - 16)%Z)
        by (repeat destruct Ha as [<-|Ha]; try (exfalso; exact Ha); u_norm; lia).
      u_norm; lia.
    + intros x Hx.
      assert (Hxlo : (bv_unsigned rsp - 32 <= bv_unsigned a)%Z)
        by (repeat destruct Ha as [<-|Ha]; try (exfalso; exact Ha); u_norm; lia).
      unfold M.
      rewrite wbytes_above by (change (Z.of_nat (length arg1)) with (Z.of_nat nn);
                               revert Hx; u_norm; rewrite ?u_nN'; lia).
      unfold mem0. rewrite zmem_out; [reflexivity| right; revert Hx; u_norm; lia].
  - unfold M, mem0, fmem2. solve_mem_grows.
Qed.

(** The string and the spilled break, read back through the zeroed brk
    grant (the grant lies far below the stack frame). *)
Lemma str_from_mem0 : forall r, (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + Z.of_nat nn <= bv_unsigned rsp - stack_max_size)%Z ->
  rdn source_segs (zmem (fmem2 r) r nN) ptr (S nn) = Some (arg1 ++ [Z_to_bv 8 0]).
Proof.
  intros r Hr0 Hceil.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le' as HnnLe.
  pose proof ptr_lo' as Hplo. pose proof ptr_hi' as Hphi.
  rewrite rdn_zmem_out.
  - destruct (read_str_f8_2 r) as (tl & Htl & Hread8).
    apply (rdn_firstn source_segs (fmem2 r) (nn + 8) ptr _ (S nn)) in Hread8; [|lia].
    rewrite Hread8. f_equal.
    rewrite firstn_app.
    rewrite firstn_all2 by (unfold nn; lia).
    replace (S nn - length arg1)%nat with 1%nat by (unfold nn; lia).
    cbn [firstn app]. reflexivity.
  - rewrite Nat2Z.inj_succ. lia.
  - right. rewrite u_nN'. lia.
Qed.

Lemma spill_from_mem0 : forall r, (0 < bv_unsigned r)%Z ->
  (bv_unsigned r + Z.of_nat nn <= bv_unsigned rsp - stack_max_size)%Z ->
  rdn source_segs (zmem (fmem2 r) r nN) (Z_to_bv 64 (bv_unsigned rsp - 72)) 8%nat
  = Some (word_to_le_bytes 8 (r + nN)).
Proof.
  intros r Hr0 Hceil.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le' as HnnLe.
  rewrite rdn_zmem_out.
  - apply read_spill.
  - u_norm. lia.
  - right. u_norm. rewrite u_nN'. lia.
Qed.

(* ================================================================= *)
(* The former fault path, now a zero-padded successful run             *)
(* ================================================================= *)

(** Historical name retained: the path that formerly ran to a fault now
    completes successfully because the enclosing physical page supplies
    zero bytes after the logical [n]-byte prefix. *)
Lemma source_to_fault : forall regs5 (r grant : word),
  (bv_unsigned nN <= bv_unsigned grant)%Z ->
  (Z.of_nat (8 * ((nn + 7) / 8)) <= bv_unsigned grant)%Z ->
  (bv_unsigned r + bv_unsigned grant <= bv_unsigned rsp - stack_max_size)%Z ->
  region_free (segments_reserved source_segs) r grant = true ->
  (0 < bv_unsigned r)%Z ->
  (nn mod 8 <> 0)%nat ->
  reg_get regs5 1 = (0x110b0 : word) -> reg_get regs5 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
  reg_get regs5 8 = nN -> reg_get regs5 9 = r -> reg_get regs5 18 = ptr ->
  to_wallexit source_segs (Z_to_bv 64 1) (outbufs arg1) (Z_to_bv 64 0)
    (mkst (regupd regs5 10 (r + nN)) 0x1121c (zmem (fmem2 r) r grant) rrom).
Proof.
  intros regs5 r grant Hgrant Htotal Hceil Hfree Hr0 Hmod
    H1 H2 H8 H9 H18.
  apply (source_run_success regs5 r grant); try assumption.
  intro Hnn0. apply Hmod. rewrite Hnn0. reflexivity.
Qed.

(** The old faulting address now reads the first zero padding byte. *)
Lemma source_fault_step : forall (r grant : word),
  (bv_unsigned nN < bv_unsigned grant)%Z ->
  (bv_unsigned r + bv_unsigned grant < 2 ^ 64)%Z ->
  rdn source_segs (wbytes (zmem (fmem2 r) r grant) r arg1)
    (r + nN) 1 = Some [Z_to_bv 8 0].
Proof.
  intros r grant Hinside Hnw.
  rewrite u_nN' in Hinside.
  assert (Hrawnw : (bv_unsigned r + bv_unsigned nN < 2 ^ 64)%Z).
  { rewrite u_nN'. lia. }
  rewrite rdn_wbytes_disjoint.
  - apply rdn_zmem_in1. rewrite u_add_small by exact Hrawnw.
    rewrite u_nN'. lia.
  - change (Z.of_nat (length arg1)) with (Z.of_nat nn).
    rewrite u_add_small by exact Hrawnw. rewrite u_nN'. lia.
  - rewrite u_add_small by exact Hrawnw. rewrite u_nN'. lia.
Qed.

(** A failing second brk (the kernel keeps the break): the reloaded
    request differs from the returned break, so main exits 4 silently. *)
Lemma source_fail4 : forall regs5 (r : word),
  reg_get regs5 1 = (0x110b0 : word) ->
  reg_get regs5 2 = Z_to_bv 64 (bv_unsigned rsp - 80) ->
  bv_unsigned r <> bv_unsigned (r + nN) ->
  to_wexit source_segs (mkst (regupd regs5 10 r) 0x1121c (fmem2 r) rrom) [] (Z_to_bv 64 4).
Proof.
  intros regs5 r H1 H2 Hne.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  chain_step;
    [ reflexivity
    | eapply step_jalr_x0 with (tgt := (0x110b0 : word));
      [ exact SF_1121c | reflexivity | exact SD_1121c
      | getr_resolve; regupd_resolve; exact H1 ]
    | norm_pc ].
  chain_step;
    [ reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 (r + nN)) (v := r + nN);
      [ exact SF_110b0 | reflexivity | exact SD_110b0
      | match goal with |- rdn _ _ ?a _ = _ =>
          replace a with (Z_to_bv 64 (bv_unsigned rsp - 72))
            by (getr_resolve; regupd_resolve; rewrite H2; sp_norm; f_equal; lia) end;
        apply read_spill
      | exact (bytes_le_to_Z_8 _) ]
    | step_simpl ].
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_110b4 | reflexivity | exact SD_110b4 | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  chain_step;
    [ reflexivity
    | eapply step_bne_tk;
      [ exact SF_110b8 | reflexivity | exact SD_110b8
      | getr_resolve; regupd_resolve; apply c_eq_neq; auto ]
    | norm_pc ].
  apply source_exit4.
  - regupd_resolve. exact H2.
  - apply read_slot_ra2.
  - apply read_slot_02.
Qed.

(* ================================================================= *)
(* The three top-level source facts                                   *)
(* ================================================================= *)

Hypothesis Hbrk_mod : (bv_unsigned rbrk mod page_size = 0)%Z.

Local Abbreviation RS := (run_segments source_segs inp rsp rmb).

(** The run's outcome set, over the run's segment list and initial model
    (the vDSO counter, and the vDSO pair in the brk ledger
    [State.init_reserved]).  [Hmb] is [Run.valid_mmap_base]'s floor, which
    keeps the vDSO pair far above the heap ([run_ledger_free]); [Hrd] is
    the stdout reader [Run.valid_input] pins, which the write nodes need. *)
Lemma source_outcomes :
  (mmap_base_min <= bv_unsigned rmb)%Z ->
  in_channel_reader inp = true ->
  (Z.of_nat nn <= 65536)%Z ->
  to_outcomes RS
    (init_machine_state RS 0x111c8 source_phdrs rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
       (init_model (segments_reserved RS) rbrk rmb rsp source_alloc_limit inp))
    (oobU nN (outbufs arg1)).
Proof.
  intros Hmb Hrd Hncap.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le' as HnnLe.
  pose proof rbrk_lo_num as Hblo. pose proof rbrk_hi_num as Hbhi.
  assert (E10i : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  (* the image's list is concrete, so the run's reservations split by
     computation; the vDSO pair reserves nothing *)
  assert (HresRS : segments_reserved RS = segments_reserved source_segs).
  { replace (segments_reserved RS)
      with (segments_reserved source_segs
            ++ segments_reserved (vdso_segments (in_kernel inp) rsp rmb))
      by reflexivity.
    rewrite segments_reserved_vdso, app_nil_r. reflexivity. }
  rewrite HresRS.
  (* fd 1 is the stdout channel and has a reader in the run's initial
     model ([with_vdso] keeps the descriptor table and the reader flag) *)
  assert (Hfd0 : fd1chan (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
                   (init_model (segments_reserved source_segs) rbrk rmb rsp
                      source_alloc_limit inp)))
    by exact (init_model_fd1chan (segments_reserved source_segs) rbrk rmb rsp
                source_alloc_limit inp Hrd).
  destruct (source_to_brk1 Hncap)
    as (regs3 & E1 & E2 & E8 & E10 & E17 & E18 & Hms).
  eapply tou_msteps; [exact (msteps_run source_segs inp rsp rmb _ _ Hms)|].
  apply (tou_brk_r RS _ _ (Z_to_bv 64 214)
           (T1 (init_reserved (segments_reserved source_segs) rmb rsp (in_kernel inp))
              source_alloc_limit (bv_unsigned rsp - stack_max_size) nN (outbufs arg1)));
    [reflexivity | vm_compute; reflexivity | | ].
  { (* per-resolution continuation at the first brk *)
    intros r Hok.
    unfold ms_gpr in Hok |- *; cbn [ms_regs] in Hok |- *.
    rewrite E10i, E10 in Hok |- *.
    change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved source_segs) rmb rsp
                                      (in_kernel inp))
                        [] [] rbrk rbrk source_alloc_limit rmb rsp)
              (Z_to_bv 64 0) r) in Hok.
    apply brk_r_ok_query_iff in Hok. cbn [vm_brk] in Hok.
    rewrite m_vmmaps_with_vdso, m_vmmaps_init_model. cbn [vm_brk].
    assert (Hurb : bv_unsigned r = bv_unsigned rbrk)
      by (rewrite Hok; reflexivity).
    assert (Hrmod : (bv_unsigned r mod page_size = 0)%Z).
    { rewrite Hurb. exact Hbrk_mod. }
    assert (Hrnz : r <> Z_to_bv 64 0).
    { intro He. apply (f_equal bv_unsigned) in He.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in He. lia. }
    assert (Hnw : (bv_unsigned r + Z.of_nat nn < 2^64)%Z) by lia.
    assert (Hurn : bv_unsigned (r + nN) = (bv_unsigned r + Z.of_nat nn)%Z)
      by (rewrite u_add_small; rewrite u_nN'; lia).
    assert (Hwant0 : r + nN <> Z_to_bv 64 0).
    { intro He. apply (f_equal bv_unsigned) in He. rewrite Hurn in He.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in He. lia. }
    assert (Hne2 : r <> r + nN \/ (nn = 0)%nat).
    { destruct (Nat.eq_dec nn 0) as [->|Hp]; [right; reflexivity|].
      left. intro He. apply (f_equal bv_unsigned) in He. rewrite Hurn in He. lia. }
    rewrite brk_zeros_query.
    rewrite (brk_unmaps_grow r rbrk) by lia.
    rewrite adv_brk, apply_zeros_nil. wlits.
    rewrite brk_model_query by exact Hok.
    rewrite m_vmmaps_with_vdso, m_vmmaps_init_model.
    cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_limit vm_mmap_base vm_init_sp].
    destruct (source_to_brk2 regs3 r E1 E2 E8 E18 Hrnz Hnw)
          as (regs5 & F1 & F2 & F8 & F9 & F10 & F17 & F18 & Hms2).
        eapply tou_msteps; [exact (msteps_run source_segs inp rsp rmb _ _ Hms2)|].
        apply (tou_brk_r RS _ _ (Z_to_bv 64 214) (T2 (r + nN) (outbufs arg1)));
          [reflexivity | vm_compute; reflexivity | | ].
        * (* per-resolution continuation at the second brk *)
          intros r2 Hok2.
          unfold ms_gpr in Hok2 |- *; cbn [ms_regs] in Hok2 |- *.
          rewrite E10i, F10 in Hok2 |- *.
          change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved source_segs) rmb rsp
                                            (in_kernel inp))
                              [] [] rbrk r source_alloc_limit rmb rsp)
                    (r + nN) r2) in Hok2.
          rewrite m_vmmaps_with_vmmaps. cbn [vm_brk].
          apply brk_r_ok_grow_iff in Hok2;
            [ | rewrite ?Hurn; lia | rewrite ?Hurn; lia | rewrite ?Hurn; lia ].
          destruct (decide (r2 = r + nN)) as [-> | Hne].
          { (* success resolution *)
            destruct (Nat.eq_dec nn 0) as [Hnn0 | Hnnpos].
            - (* n = 0: keep *)
              assert (HnN0 : nN = Z_to_bv 64 0) by (unfold nN; rewrite Hnn0; reflexivity).
              assert (Hz : brk_zeros (r + nN) (r + nN) r = [])
                by (rewrite HnN0, word_add_0_r; apply brk_zeros_keep).
              rewrite Hz.
              rewrite brk_unmaps_grow by lia.
              rewrite adv_brk, apply_zeros_nil. wlits.
              eapply tou_equiv;
                [ | intro o; apply (T2_succ_iff (r + nN) (outbufs arg1)) ].
              apply tou_wexit_eq.
              + apply fd1chan_brk_model. apply fd1chan_with_vmmaps. exact Hfd0.
              + apply to_wallexit_run.
                apply (source_run_empty Hnn0 regs5 r); try assumption.
              + apply outbufs_modeled.
            - (* n > 0: grow *)
              destruct Hok2 as [_ Hgrow2].
              rewrite brk_grow_ok_aligned_grow in Hgrow2;
                [ cbn [vm_brk vm_reserved vm_maps] in Hgrow2;
                  rewrite app_nil_r in Hgrow2
                | exact Hwant0
                | cbn [vm_brk]; lia
                | cbn [vm_brk]; rewrite Hurn; lia
                | cbn [vm_brk]; exact Hrmod ].
              apply andb_true_iff in Hgrow2;
              destruct Hgrow2 as [Hgrow2 Hbud].
              apply andb_true_iff in Hgrow2;
              destruct Hgrow2 as [Hle Hfree].
              apply Z.leb_le in Hle.
              set (grant := Z_to_bv 64
                (page_round_up_Z (bv_unsigned (r + nN)) - bv_unsigned r)).
              destruct (brk_aligned_grant_ok _ r nN grant _ _
                          ltac:(rewrite u_nN'; exact Hurn) Hurn eq_refl
                          (alloc_top_page_lt _) Hle Hfree)
                as (HgrantU & Hgrant & Hphysceil & _ & _ & Hgrantfree).
              assert (Htotalgrant :
                (Z.of_nat (8 * ((nn + 7) / 8)) <= bv_unsigned grant)%Z).
              { rewrite HgrantU, Hurn.
                rewrite Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add by lia.
                cbn [Z.of_nat].
                rewrite Z.mul_comm.
                apply round8_le_page_grant; [lia|lia|exact Hrmod]. }
              rewrite brk_zeros_aligned_grow;
                [ | exact Hwant0 | lia | rewrite Hurn; lia | exact Hrmod ].
              fold grant.
              rewrite brk_unmaps_grow by lia.
              rewrite adv_brk, apply_zeros_one. wlits.
              eapply tou_equiv;
                [ | intro o; apply (T2_succ_iff (r + nN) (outbufs arg1)) ].
              apply tou_wexit_eq.
              + apply fd1chan_brk_model. apply fd1chan_with_vmmaps. exact Hfd0.
              + apply to_wallexit_run.
                apply (source_run_success regs5 r grant).
                * exact Hgrant.
                * exact Htotalgrant.
                * exact Hphysceil.
                * (* the image's part of the run's ledger *)
                  exact (region_free_init_reserved_img _ rmb rsp (in_kernel inp) r grant
                           Hgrantfree).
                * lia.
                * exact Hnnpos.
                * exact F1.
                * exact F2.
                * exact F8.
                * exact F9.
                * exact F18.
              + apply outbufs_modeled. }
          { (* failure resolution: r2 = r, exit 4 *)
            destruct Hok2 as [Hcase _].
            destruct Hcase as [Hc | Hc]; [exact (False_ind _ (Hne Hc)) |].
            subst r2.
            rewrite brk_zeros_keep.
            rewrite brk_unmaps_grow by lia.
            rewrite adv_brk, apply_zeros_nil. wlits.
            assert (Hnepos : r <> r + nN).
            { destruct Hne2 as [Hh|Hh]; [exact Hh|].
              exfalso. apply Hne. unfold nN. rewrite Hh.
              change (nat_to_word 0) with (Z_to_bv 64 0). rewrite word_add_0_r. reflexivity. }
            eapply tou_equiv;
              [ | intro o; apply (T2_fail_iff (r + nN) (outbufs arg1) r Hnepos) ].
            apply tou_wexit_eq.
            - apply fd1chan_brk_model. apply fd1chan_with_vmmaps. exact Hfd0.
            - apply to_wallexit_run.
              apply (source_fail4 regs5 r F1 F2).
              rewrite Hurn.
              assert (Hnnz : (nn <> 0)%nat)
                by (intro Hz; apply Hnepos; unfold nN; rewrite Hz;
                    change (nat_to_word 0) with (Z_to_bv 64 0);
                    rewrite word_add_0_r; reflexivity).
              lia.
            - apply Forall_nil. }
        * (* set identity at the second node *)
          intro o.
          unfold ms_gpr; cbn [ms_regs].
          rewrite E10i, F10.
          change (T1 (init_reserved (segments_reserved source_segs) rmb rsp (in_kernel inp))
                     source_alloc_limit (bv_unsigned rsp - stack_max_size) nN
                     (outbufs arg1) r o <->
                  (exists r2,
                     brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved source_segs)
                                               rmb rsp (in_kernel inp))
                                 [] [] rbrk r source_alloc_limit rmb rsp)
                       (r + nN) r2
                     /\ T2 (r + nN) (outbufs arg1) r2 o)).
          apply (T1_iff_T2 (init_reserved (segments_reserved source_segs) rmb rsp (in_kernel inp))
                   source_alloc_limit rbrk rmb rsp nN (outbufs arg1) r);
            [exact Hrnz | lia | rewrite u_nN'; lia]. }
  { (* set identity at the first node: the query resolves to rbrk only *)
    intro o.
    unfold ms_gpr; cbn [ms_regs].
    rewrite E10i, E10.
    apply (oobU_iff_T1 (init_reserved (segments_reserved source_segs) rmb rsp (in_kernel inp))
             source_alloc_limit (bv_unsigned rsp - stack_max_size) nN (outbufs arg1) rbrk).
    - intro r0.
      change (brk_r_ok (mkVmMapsFull (init_reserved (segments_reserved source_segs) rmb rsp
                                        (in_kernel inp))
                          [] [] rbrk rbrk source_alloc_limit rmb rsp)
                (Z_to_bv 64 0) r0 <-> r0 = rbrk).
      apply brk_r_ok_query_iff.
    - (* growable at the quantified base, over the run's ledger *)
      destruct (Nat.eq_dec nn 0) as [Hnn0|Hnnpos].
      + split; [| split].
        * intro He. apply (f_equal bv_unsigned) in He.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in He. lia.
        * rewrite u_nN'. lia.
        * left. unfold nN. rewrite Hnn0. reflexivity.
      + apply growable_ledger.
        * exact Hmb.
        * exact Hsp_lo.
        * exact Hbrk_mod.
        * lia.
        * exact Hbrk_lo.
        * rewrite u_nN'. lia.
        * rewrite u_nN'. unfold page_size. lia.
        * rewrite u_nN'. unfold page_size. change source_alloc_limit with 0x400000000%Z. lia.
        * rewrite u_nN'. unfold page_size. lia. }
Qed.

(* ================================================================= *)
(* source_outcomes_mix (n mod 8 <> 0): compatibility theorem.  The    *)
(* byte-sum loop reads past the logical n-byte prefix but stays inside *)
(* the page-rounded zero grant, so it has the ordinary oobU outcomes. *)
(* ================================================================= *)

Lemma source_outcomes_mix :
  (mmap_base_min <= bv_unsigned rmb)%Z ->
  in_channel_reader inp = true ->
  (Z.of_nat nn <= 65536)%Z ->
  (nn mod 8 <> 0)%nat ->
  to_outcomes RS
    (init_machine_state RS 0x111c8 source_phdrs rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
       (init_model (segments_reserved RS) rbrk rmb rsp source_alloc_limit inp))
    (oobU nN (outbufs arg1)).
Proof.
  intros Hmb Hrd Hncap _. apply source_outcomes; assumption.
Qed.

Lemma source_escape :
  (mmap_base_min <= bv_unsigned rmb)%Z ->
  in_channel_reader inp = true ->
  (Z.of_nat nn <= 65536)%Z ->
  (nn mod 8 <> 0)%nat ->
  to_outcomes RS
    (init_machine_state RS 0x111c8 source_phdrs rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
       (init_model (segments_reserved RS) rbrk rmb rsp source_alloc_limit inp))
    (oobU nN (outbufs arg1)).
Proof.
  intros Hmb Hrd Hncap _. apply source_outcomes; assumption.
Qed.

End Ge2Main.

End SourceProof.
