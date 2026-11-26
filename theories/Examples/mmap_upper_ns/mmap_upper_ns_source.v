(** * mmap-upper-ns SOURCE binary: frames, prologue, strlen, early exits,
      and the run up to the mmap ecall.

    PROOF-SIDE FILE (not part of the trusted specification).

    Machine plan (musl-gcc 15 -Os -fno-builtin, see the disassembly
    comments in mmap_upper_ns_code.v):

      _start 0x11128..0x11150: gp setup, argc/argv, environ store to
        0x13000, jal main (ra = 0x11154; 0x11154 = li a7,93; ecall).
      main 0x11000: argc < 2 -> a0=2; ret -> exit 2.
      prologue 0x11008..0x11020: frame (sp = rsp-48, FOUR sd's: s0, ra,
        s1, s2), s2 = argv[1], s0 = 0.
      slen loop 0x11024..0x1102c (back-edge 0x110d4/0x110d8): the
        source's own byte loop, inline under -fno-builtin; s0 = n.
      0x11030..0x11038: n >= 4096 -> a0=3 -> epilogue -> exit 3.
      0x1103c..0x11054: mmap args, jal raw_syscall -> ecall at 0x11178
        with a7=222, a1=4096 (the tmw branch point).

    Sp-relative addresses/register values are in the canonical
    [Z_to_bv 64 (bv_unsigned rsp - k)] form, pc and rodata constants in
    numeral-literal form, loop indices as [nat_to_word]; all range
    bookkeeping is in [Z] over [bv_unsigned]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec MmapSim WallSim StepTac StreamSim StoreOk RunSegmentsLift.
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
    below are [fx0]'s; no instruction here touches them. *)
#[local] Instance mmap_upper_ns_source_fx : FPState := fx0.

(* ================================================================= *)
(* Store legality: everything at/above the data segment base          *)
(* ================================================================= *)

(** Under [-z separate-code] with gcc 15 the image has FOUR LOAD
    segments — 000 ([0x10000,0x11000), headers), 001 ([0x11000,0x12000),
    .text), 002 ([0x12000,0x13000), .rodata/.eh_frame) and the writable
    003 ([0x13000,0x14000)).  [range_avoids_ro_above] is stated for any
    segment count, so this is one bound rather than a per-segment
    enumeration. *)
Lemma source_avoids_data : forall a n : Z, (0x13000 <= a)%Z ->
  range_avoids_ro_segs source_segs a n = true.
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
    window ([solve_store_ok]) and mmap targets through the grant's
    zero-fill ([grant_store_ok]). *)
Lemma source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma source_store_ok : forall (m : word -> option byte) (a : word) (k : nat),
  (0x13000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= 0x14000)%Z ->
  store_ok source_segs m a k = true.
Proof.
  intros m a k Hlo Hhi.
  eapply store_ok_window with (base := 0x13000%Z) (hi := 0x14000%Z);
    [ | | | exact source_data_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.

(* ================================================================= *)
(* Grant facts for the source image                                   *)
(* ================================================================= *)

Lemma source_reserved_val :
  segments_reserved source_segs
  = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x11000, Z_to_bv 64 0x1000);
     (Z_to_bv 64 0x12000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x13000, Z_to_bv 64 0x1000)].
Proof.
  apply (@bool_decide_eq_true_1 (_ = _) _).
  vm_cast_no_check (eq_refl true).
Qed.

Lemma source_reserved_low : forall a sz, In (a, sz) (segments_reserved source_segs) ->
  (bv_unsigned a + bv_unsigned sz <= Mmap.task_unmapped_base)%Z.
Proof.
  intros a sz Hin. rewrite source_reserved_val in Hin.
  unfold Mmap.task_unmapped_base.
  repeat destruct Hin as [Hin | Hin];
    try (injection Hin as <- <-; rewrite !u_Z2bv by lia; lia).
  destruct Hin.
Qed.

(** The launch model's one-page grant exists
    ([RunSegmentsLift.grant_witness_init]); the model is [Run]'s: [State.with_vdso] of the
    draw's vDSO counter over [State.init_model]. *)
Lemma source_grant_witness : forall inp (hint brk0 mb sp : word) v,
  (sp_window_lo <= bv_unsigned sp)%Z -> (mmap_base_min <= bv_unsigned mb)%Z ->
  exists a, grant_ok hint
    (with_vdso v (init_model (segments_reserved source_segs) brk0 mb sp source_alloc_limit inp))
    a 4096 = true.
Proof.
  intros inp hint brk0 mb sp v Hsp Hmb.
  apply grant_witness_init; [exact source_reserved_low | exact Hsp | exact Hmb |].
  rewrite source_alloc_limit_val. lia.
Qed.

Lemma source_grant_unpack : forall inp (hint brk0 mb sp aG : word) v,
  grant_ok hint (with_vdso v (init_model (segments_reserved source_segs) brk0 mb sp
                                source_alloc_limit inp)) aG 4096 = true ->
  (0 < bv_unsigned aG)%Z /\ (bv_unsigned aG mod page_size = 0)%Z /\
  (bv_unsigned aG + 4096 <= bv_unsigned sp - stack_max_size)%Z /\
  ((bv_unsigned aG + 4096 <= 0x10000)%Z \/ (0x11000 <= bv_unsigned aG)%Z) /\
  ((bv_unsigned aG + 4096 <= 0x11000)%Z \/ (0x12000 <= bv_unsigned aG)%Z) /\
  ((bv_unsigned aG + 4096 <= 0x12000)%Z \/ (0x13000 <= bv_unsigned aG)%Z).
Proof.
  intros inp hint brk0 mb sp aG v Hg.
  destruct (grant_ok_unpack _ _ _ _ Hg) as (Hal & Hpos & Hceil & Hfree & _).
  change (alloc_top (m_vmmaps (with_vdso v (init_model (segments_reserved source_segs)
            brk0 mb sp source_alloc_limit inp))))
    with (bv_unsigned sp - stack_max_size)%Z in Hceil.
  change (vm_reserved (m_vmmaps (with_vdso v (init_model (segments_reserved source_segs)
            brk0 mb sp source_alloc_limit inp))))
    with (init_reserved (segments_reserved source_segs) mb sp (in_kernel inp)) in Hfree.
  change (vm_maps (m_vmmaps (with_vdso v (init_model (segments_reserved source_segs)
            brk0 mb sp source_alloc_limit inp))))
    with (@nil (word * word)) in Hfree.
  unfold init_reserved in Hfree.
  rewrite source_reserved_val in Hfree.
  cbn [app] in Hfree.
  apply region_free_cons in Hfree. destruct Hfree as [Hda Hfree].
  apply region_free_cons in Hfree. destruct Hfree as [Hdb Hfree].
  apply region_free_cons in Hfree. destruct Hfree as [Hdc _].
  rewrite !u_Z2bv in Hda by lia.
  rewrite !u_Z2bv in Hdb by lia.
  rewrite !u_Z2bv in Hdc by lia.
  refine (conj Hpos (conj Hal (conj Hceil (conj _ (conj _ _))))).
  - destruct Hda as [H|H]; [left; lia | right; lia].
  - destruct Hdb as [H|H]; [left; lia | right; lia].
  - destruct Hdc as [H|H]; [left; lia | right; lia].
Qed.

(** A grant-backed range avoids the read-only segments.  With THREE
    read-only segments the three pairwise disjointness facts collapse to
    a single split: a page-sized grant cannot start inside the image, so
    it lies wholly below 0x10000 or at/above 0x13000. *)
Lemma source_grant_avoids : forall aGZ x k : Z,
  (aGZ + 4096 <= 0x10000 \/ 0x11000 <= aGZ)%Z ->
  (aGZ + 4096 <= 0x11000 \/ 0x12000 <= aGZ)%Z ->
  (aGZ + 4096 <= 0x12000 \/ 0x13000 <= aGZ)%Z ->
  (aGZ <= x)%Z -> (x + k <= aGZ + 4096)%Z ->
  range_avoids_ro_segs source_segs x k = true.
Proof.
  intros aGZ x k Hd1 Hd2 Hd3 Hx1 Hx2.
  assert (Hcase : (x + k <= 0x10000)%Z \/ (0x13000 <= x)%Z).
  { destruct Hd1 as [H1|H1]; [left; lia|].
    destruct Hd2 as [H2|H2]; [left; lia|].
    destruct Hd3 as [H3|H3]; [left; lia| right; lia]. }
  destruct Hcase as [Hbelow | Habove];
    [| apply range_avoids_ro_above with (data_base := 0x13000%Z);
       [vm_compute; reflexivity | lia]].
  unfold source_segs, SourceMemImage_loaded_segments, range_avoids_ro_segs.
  cbn [forallb].
  change (seg_writable SourceMemImage_segment_000) with false.
  change (seg_writable SourceMemImage_segment_001) with false.
  change (seg_writable SourceMemImage_segment_002) with false.
  change (seg_writable SourceMemImage_segment_003) with true.
  change (Z.of_N (seg_base SourceMemImage_segment_000)) with 0x10000%Z.
  change (Z.of_N (seg_base SourceMemImage_segment_001)) with 0x11000%Z.
  change (Z.of_N (seg_base SourceMemImage_segment_002)) with 0x12000%Z.
  assert (Hb0 : (0x10000 <? x + k)%Z = false) by (apply Z.ltb_ge; lia).
  assert (Hb1 : (0x11000 <? x + k)%Z = false) by (apply Z.ltb_ge; lia).
  assert (Hb2 : (0x12000 <? x + k)%Z = false) by (apply Z.ltb_ge; lia).
  rewrite Hb0, Hb1, Hb2. cbn [andb negb orb]. reflexivity.
Qed.

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x11128%N.
Proof. vm_compute. reflexivity. Qed.

Section SourceProof.

Variable inp : ProcInput.
Local Abbreviation av := (in_argv inp).
Local Abbreviation ev := (in_envp inp).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.

(** The initial stack pointer, program break and mmap base are QUANTIFIED
    (ASLR).  This example allocates with mmap and never calls brk, so the
    break is read only by the launch conjunct. *)
Variable rsp rbrk rmb : word.

(** The entry stack draw this run was started with
    ([Run.ExecEntry]'s [en_draw]): the 16 AT_RANDOM bytes the kernel
    picks afresh at every [execve], and the stack VMA's end
    [StackLayout.ed_top].  This proof may assume NOTHING about either
    beyond the launch conjunct below.  Quantified per binary, so the
    target's draw is a different variable. *)
Variable rrnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned rsp)%Z.
Hypothesis Hsp_hi : (bv_unsigned rsp <= sp_window_hi)%Z.
Hypothesis Hvl : valid_launch inp.

(** The fifth conjunct of [Run.valid_entry_va]: this placement is one a
    Linux launch can give ([create_elf_tables] and [setup_arg_pages],
    fs/binfmt_elf.c and fs/exec.c, Linux v6.18.46, commit
    1f99e9ab748f).  With [Hvl] it bounds the entry block, places the
    argv strings below [ed_top] and the stack-store window. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry rsp rbrk rmb rrnd) inp.

Lemma rsp_lo_num : (0x7fff80000000 <= bv_unsigned rsp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma rsp_hi_num : (bv_unsigned rsp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Definition argcN : word := len_word av.
(** The initial overlay, with the entry point [init_mkst] passes to it. *)
Definition rwmem : word -> option byte :=
  wrap_mem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x11128)) rsp rrnd.
(** The run's rom: the image's segments, then the vDSO pair. *)
Definition rrom : word -> option byte := seg_rom (run_segments source_segs inp rsp rmb).

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
Proof.
  pose proof (valid_argv_len av Hva).
  unfold argcN, len_word. apply u_Z2bv; lia.
Qed.

(** No-overflow bound for the initial stack image, for any entry word
    (the image's length does not read it; the entry reaches proofs in
    both its [Z_to_bv] and its literal spelling). *)
Lemma source_bsb_nw : forall entry : word,
  (bv_unsigned rsp
   + Z.of_nat (length (entry_stack_image inp rmb source_phdrs entry rsp rrnd)) < 2^64)%Z.
Proof.
  intros entry.
  pose proof (bsb_bound Sv48 inp rmb source_phdrs entry rsp rbrk rrnd Hvl Hlau).
  pose proof rsp_hi_num. lia.
Qed.

(** The register shift the crt's [slli a2,a0,3] compiles to, in the
    immediate-shift spelling the rest of the file uses.  The shift
    amount is a closed literal; only the shifted value is symbolic. *)
Lemma v_sll_3 : forall x : word, v_sll x (Z_to_bv 64 3) = v_slli x 3.
Proof.
  intro x. unfold v_sll, v_slli. f_equal.
Qed.

(** environ value stored by _start. *)
Definition envval : word :=
  Z_to_bv 64 (bv_unsigned rsp + 16 + 8 * Z.of_nat (length av)).

Lemma envval_eq : v_addi (v_add (v_addi rsp 8) (v_slli argcN 3)) 8 = envval.
Proof.
  pose proof rsp_hi_num. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as Hlen.
  apply bv_eq. unfold envval, v_addi.
  rewrite !Z_to_bv_unsigned.
  rewrite v_add_small
    by (rewrite u_Z2bv by lia; rewrite v_slli_3 by (rewrite u_argcN; lia);
        rewrite u_argcN; lia).
  rewrite u_Z2bv by lia.
  rewrite v_slli_3 by (rewrite u_argcN; lia).
  rewrite u_argcN.
  f_equal; lia.
Qed.

(** The same equation in the spelling a REFLECTIVE block leaves behind:
    the executor denotes the crt's four-instruction envp computation as
    an [alu64]/[v_sll] tree, and this is where it becomes [envval].
    Without it the exit memory is only CONVERTIBLE to [fmem], and making
    the unifier find that conversion costs minutes. *)
Lemma envval_sym :
  Z_to_bv 64 (bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
                                         (v_sll argcN (Z_to_bv 64 3))) + 8)
  = envval.
Proof. rewrite alu_add, v_sll_3. exact envval_eq. Qed.

(** Memory after _start's environ store (the data segment now sits at
    0x13000). *)
Definition emem : word -> option byte :=
  wbytes rwmem 0x13000 (word_to_le_bytes 8 envval).

(** Memory after main's prologue.  gcc 15 saves only FOUR registers
    (s0, ra, s1, s2); 0(sp) and 8(sp) are left alone by the prologue and
    reused later as spill slots for the write loop's pointer/count. *)
Definition fmem : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes
    emem
    (Z_to_bv 64 (bv_unsigned rsp - 0x10)) (word_to_le_bytes 8 (Z_to_bv 64 0)))      (* sd s0,32(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 0x8))  (word_to_le_bytes 8 (0x11154 : word)))    (* sd ra,40(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 0x18)) (word_to_le_bytes 8 (Z_to_bv 64 0)))      (* sd s1,24(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 0x20)) (word_to_le_bytes 8 (Z_to_bv 64 0)).      (* sd s2,16(sp) *)

Local Abbreviation s := (nth 1 av []).
Local Abbreviation n := (length s).
Definition nN : word := nat_to_word n.
Definition P : word := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1.

Lemma rdn_rwmem_stack : forall (a : word) k,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= 2^64)%Z ->
  rdn source_segs rwmem a k
  = rdn source_segs
      (stack_to_mem rsp (entry_stack_image inp rmb source_phdrs
                           (Z_to_bv 64 (Z.of_N 0x11128)) rsp rrnd)) a k.
Proof. intros a k Ha Hnw. apply rdn_wrap_stack_above; assumption. Qed.

Lemma rdn_emem_above : forall (a : word) k,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= 2^64)%Z ->
  rdn source_segs emem a k = rdn source_segs rwmem a k.
Proof.
  intros a k Ha Hnw. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. unfold emem.
  rewrite rdn_wbytes_disjoint
    by (rewrite ?length_N_to_le_bytes; imm_norm; lia).
  reflexivity.
Qed.

Lemma rdn_fmem_above : forall (a : word) k,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= 2^64)%Z ->
  rdn source_segs fmem a k = rdn source_segs rwmem a k.
Proof.
  intros a k Ha Hnw. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  unfold fmem.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; u_norm; lia)).
  apply rdn_emem_above; assumption.
Qed.

Lemma source_ptr_bounds : (2 <= length av)%nat ->
  (bv_unsigned rsp <= bv_unsigned P)%Z /\
  (bv_unsigned P + Z.of_nat n + 1 < 2^64)%Z.
Proof.
  intro H2. unfold P.
  exact (argv_ptr_bounds Sv48 inp rmb rsp rbrk rrnd 1 Hlau ltac:(lia)).
Qed.

Lemma fread_str_byte : forall j, (2 <= length av)%nat -> (j <= n)%nat ->
  rdn source_segs fmem (P + nat_to_word j) 1%nat = Some [byte_at s j].
Proof.
  intros j H2 Hj.
  destruct (source_ptr_bounds H2) as [Hge Hup].
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as Hslen.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  rewrite rdn_fmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_rwmem_stack by (rewrite word_add_nat; u_norm; lia).
  apply (read_argv_byte_k Sv48 source_segs inp rmb source_phdrs _ rsp rbrk rrnd 1 j Hlau);
    [lia | exact Hj].
Qed.

(* ================================================================= *)
(* Frame-slot read-back on [fmem]                                     *)
(* ================================================================= *)

Lemma fread_slot_ra :
  rdn source_segs fmem (Z_to_bv 64 (bv_unsigned rsp - 0x8)) 8%nat
  = Some (word_to_le_bytes 8 (0x11154 : word)).
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. unfold fmem.
  repeat first
    [ rewrite rdn_wbytes_hit8 by (u_norm; lia)
    | rewrite rdn_wbytes_disjoint by (rewrite ?length_N_to_le_bytes; u_norm; lia)
    | rewrite rdn_wbytes_below by (rewrite ?length_N_to_le_bytes; u_norm; lia) ].
  reflexivity.
Qed.

Lemma fread_slot_0 : forall a,
  In a [Z_to_bv 64 (bv_unsigned rsp - 0x20); Z_to_bv 64 (bv_unsigned rsp - 0x18);
        Z_to_bv 64 (bv_unsigned rsp - 0x10)] ->
  rdn source_segs fmem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros a Ha. pose proof rsp_lo_num. pose proof rsp_hi_num. unfold fmem.
  repeat destruct Ha as [<-|Ha];
    try (exfalso; exact Ha);
    repeat first
      [ rewrite rdn_wbytes_hit8 by (u_norm; lia)
      | rewrite rdn_wbytes_disjoint by (rewrite ?length_N_to_le_bytes; u_norm; lia)
      | rewrite rdn_wbytes_below by (rewrite ?length_N_to_le_bytes; u_norm; lia) ];
    reflexivity.
Qed.

(* ================================================================= *)
(* Epilogue: 0x11110 .. ret .. exit ecall (generic memory)            *)
(* ================================================================= *)

(** From the main epilogue at 0x11110, with sp = rsp-48 and the frame
    slots readable in [mem], reach the exit ecall's pending record.
    gcc 15's frame saves only ra/s0/s1/s2, so this restores FOUR
    registers rather than six. *)
Lemma source_epilogue : forall regs (mem : word -> option byte) code,
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ->
  reg_get regs 10 = code ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x8)) 8%nat
    = Some (word_to_le_bytes 8 (0x11154 : word)) ->
  (forall a, In a [Z_to_bv 64 (bv_unsigned rsp - 0x20); Z_to_bv 64 (bv_unsigned rsp - 0x18);
                   Z_to_bv 64 (bv_unsigned rsp - 0x10)] ->
     rdn source_segs mem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  exists regs',
    bv_unsigned (getr regs' 17) = 93%Z /\ reg_get regs' 10 = code /\
    msteps source_segs (mkst regs 0x11110 mem rrom)
      {| ms_regs := regs'; ms_fregs := fp_regs; ms_pc_val := 0x11158;
         ms_svc_pending := Some (getr regs' 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rrom |}.
(** EIGHT instructions in ONE reflective block: the four frame reloads,
    the stack pop, main's [ret], and the crt's [li a7,93] before the
    [exit] ecall.  The block's only pinned register is [sp]; the four
    reloads are named in the READ SCRIPT ([ELit 0x11154] for _start's
    return address, [ELit 0] for the three callee-saved slots), which is
    what lets the [ret] two instructions later resolve to a literal pc
    and the block run all the way into the crt tail.  What is left below
    is exactly the four [rdn] facts the caller supplies. *)
Proof.
  intros regs mem code H2 H10 Hra Hz.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  replace (0x11110 : word) with (Z_to_bv 64 0x11110) by bveq.
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 0x11110) mem rrom)
    8%nat (@nil bool) [ELit 0x11154; ELit 0; ELit 0; ELit 0]
    [((2 : reg), EVar 32)] [Z_to_bv 64 (bv_unsigned rsp - 0x30)] (@nil word)
    R HR Hms.
  (* the four frame reloads, in the executor's (reverse) order *)
  1: (exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hz; left; reflexivity
      | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  1: (exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hz; right; left; reflexivity
      | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  1: (exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
      [ apply Hz; right; right; left; reflexivity
      | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  1: (exists (word_to_le_bytes 8 (0x11154 : word)); split;
      [ exact Hra | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  { (* the [sp] pin *) exact H2. }
  exists R. split; [| split].
  - sym_regs HR. vm_compute. reflexivity.
  - sym_regs HR. first [ exact H10 | rewrite <- getr_nz by reg_neq_tac; exact H10 ].
  - eapply msteps_trans; [ exact Hms | ]. norm_pc; sym_pc_lit.
    eapply mst_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ SF_11158 eq_refl) | apply mst_refl ].
Qed.

(* ================================================================= *)
(* argc < 2: straight to exit 2                                       *)
(* ================================================================= *)

Lemma source_wexit_lt2 : (length av < 2)%nat ->
  to_wexit source_segs
    (init_machine_state (run_segments source_segs inp rsp rmb) 0x11128 source_phdrs rsp rmb rrnd inp)
    [] (Z_to_bv 64 2).
(** SIXTEEN instructions in ONE reflective block: the whole crt entry
    sequence (gp setup, the [ld] of argc, the envp pointer arithmetic
    and its store into musl's [__environ] slot, the [jal] into main),
    main's [argc < 2] test, and — through the [ret] that the [jal]'s
    link register makes literal — the crt exit tail up to the [ecall].
    One branch, so one [SCBr]; one load and one store, so two image
    facts.  Everything else the executor computed. *)
Proof.
  intros Hlt2.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as Hlen.
  pose proof u_argcN as Hu.
  rewrite init_mkst. norm_pc.
  sym_block source_segs 16%nat [true] (@nil expr)
    [((2 : reg), EVar 32)] [rsp] [argcN] RA HRA.
  { (* [bge a5,a0] at 0x11004 -> taken, because [argc <= 1] *) sym_br. }
  { (* [sd a2,0(t1)] at 0x1114c -> musl's [__environ] slot at 0x13000 *)
    apply source_store_ok; u_norm; lia. }
  { (* [ld a0,0(sp)] at 0x11130 -> argc, out of the initial stack image *)
    replace (Z_to_bv 64 (bv_unsigned rsp + 0)) with rsp
      by (apply bv_eq; u_norm; lia);
    exists (word_le8 argcN); split;
      [ rewrite rdn_wrap_stack_above by lia;
        apply read_argc; apply source_bsb_nw
      | apply bytes_le_n_to_le_8 ]. }
  (* 0x11158: the exit [ecall] *)
  eapply tw_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ SF_11158 eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRA. vm_compute. reflexivity.
  - sym_regs HRA. reflexivity.
  - u_norm; lia.
Qed.



(* ================================================================= *)
(* Prologue (argc >= 2): init -> the slen loop head at 0x11024        *)
(* ================================================================= *)

Lemma source_prologue : (2 <= length av)%nat ->
  exists regsP,
    (reg_get regsP 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) /\
     reg_get regsP 18 = P /\
     reg_get regsP 8 = nat_to_word 0 /\ reg_get regsP 9 = Z_to_bv 64 0) /\
    msteps source_segs
      (init_machine_state (run_segments source_segs inp rsp rmb) 0x11128 source_phdrs rsp rmb rrnd inp)
      (mkst regsP 0x11024 fmem rrom).
(** TWENTY instructions in ONE reflective block: the crt entry
    sequence again, main's [argc >= 2] fall-through, the frame push with
    its FOUR spills, the [ld] of [argv[1]] into [s2] and the [li s0,0]
    that seeds the scan index.  Five stores and two loads, so seven
    memory obligations — and, because the executor states every one of
    them against the ORIGINAL memory, none of them peels an overlay:
    the four stack spills are one [solve_store_ok] each and the
    [argv[1]] read goes straight to the stack image.  The three
    callee-saved registers are PINNED to [ELit 0] so that their spilled
    values are literals, which is what makes the exit memory literally
    [fmem].

    This is [sym_block_ex] rather than [sym_block] because the
    conclusion is existential in the exit register file — the exact
    situation its docstring names.  The exit memory is then reconciled
    with [fmem] by REVERTING the block's [msteps] and running the same
    [sym_mem_norm] on it that [sym_block] runs on a goal. *)
Proof.
  intros H2.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as Hlen.
  pose proof u_argcN as Hu.
  destruct (source_ptr_bounds H2) as [HPge HPlt].
  rewrite init_mkst.
  sym_block_ex source_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
          (Z_to_bv 64 (Z.of_N 0x11128))
          (wrap_mem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x11128)) rsp rrnd)
          (seg_rom (run_segments source_segs inp rsp rmb)))
    20%nat [false] (@nil expr)
    [((2 : reg), EVar 32); ((9 : reg), ELit 0); ((18 : reg), ELit 0);
     ((8 : reg), ELit 0)] [rsp] [argcN; P] RA HRA Hms.
  (* the four frame spills (goals 2-5, reverse execution order) *)
  2-5: solve_store_ok.
  (* [sd a2,0(t1)] at 0x1114c -> musl's [__environ] slot at 0x13000 *)
  3: (apply source_store_ok; u_norm; lia).
  { (* [ld s2,8(a1)] at 0x1101c -> argv[1], out of the stack image *)
    replace (Z_to_bv 64 (bv_unsigned rsp + 16)) with (rsp + nat_to_word (8 + 8 * 1))
      by (apply bv_eq; rewrite word_add_nat; u_norm; lia);
    exists (word_le8 P); split;
      [ rewrite rdn_wrap_stack_above by (rewrite word_add_nat; u_norm; lia);
        apply read_argv_ptr_k; [lia | apply source_bsb_nw]
      | apply bytes_le_n_to_le_8 ]. }
  { (* [bge a5,a0] at 0x11004 -> not taken, because [argc >= 2] *) sym_br. }
  { (* [ld a0,0(sp)] at 0x11130 -> argc, out of the initial stack image *)
    replace (Z_to_bv 64 (bv_unsigned rsp + 0)) with rsp
      by (apply bv_eq; u_norm; lia);
    exists (word_le8 argcN); split;
      [ rewrite rdn_wrap_stack_above by lia;
        apply read_argc; apply source_bsb_nw
      | apply bytes_le_n_to_le_8 ]. }
  exists RA. split.
  - repeat split; sym_regs HRA; sym_close.
  - replace (0x11024 : word) with (Z_to_bv 64 0x11024) by bveq.
    unfold fmem, emem, rwmem, rrom.
    revert Hms. sym_mem_norm. rewrite envval_sym. exact (fun x => x).
Qed.





(* ================================================================= *)
(* The inline [slen] scan loop: 0x11024 .. 0x1102c / 0x110d4          *)
(* ================================================================= *)

Section Strlen.

Hypothesis H2 : (2 <= length av)%nat.

(** The scan loop gcc emits for the source's own [slen] under
    [-fno-builtin]:

      0x11024  add  a5,s2,s0     a5 := P + i
      0x11028  lbu  a5,0(a5)
      0x1102c  bnez a5,0x110d4   -> 0x110d4 addi s0,s0,1 ; 0x110d8 j 0x11024

    i lives in s0 and the string base in s2, so on the way out s0 = n.
    (With builtins enabled gcc used to call musl's word-at-a-time
    [strlen] instead; alloc_join_ns keeps that image, and its walk is
    where that variant stays proved.) *)
Lemma source_slen : forall d i regs,
  (i + d = n)%nat ->
  reg_get regs 8 = nat_to_word i ->
  reg_get regs 18 = P ->
  exists regs',
    (forall r : reg, r <> 8 -> r <> 15 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 8 = nN /\
    reg_get regs' 18 = P /\
    msteps source_segs (mkst regs 0x11024 fmem rrom) (mkst regs' 0x11030 fmem rrom).
Proof.
  pose proof (valid_argv_str_nz av 1 Hva ltac:(lia)) as Hnz.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as Hslen.
  destruct (source_ptr_bounds H2) as [HPge HPlt].
  induction d as [|d IH]; intros i regs Hid H8 H18.
  - (* the NUL: the branch falls through to 0x11030 *)
    assert (Hi : i = n) by lia.
    assert (Hb0 : byte_at s i = Z_to_bv 8 0) by (rewrite Hi; apply byte_at_len).
    set (q := regupd regs 15 (P + nat_to_word i)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11024 fmem rrom)
                 = MachineOk (mkst q 0x11028 fmem rrom)).
    { rewrite (step_add source_segs regs 0x11024 fmem rrom _ 15 18 8
                 SF_11024 eq_refl SD_11024).
      reduce_bv_eqb_ifs.
      unfold q. getr_resolve. rewrite H8, H18. wlits. reflexivity. }
    set (q1 := regupd q 15 (Z_to_bv 64 0)).
    assert (E2 : RiscvSemantics.step source_segs (mkst q 0x11028 fmem rrom)
                 = MachineOk (mkst q1 0x1102c fmem rrom)).
    { rewrite (step_lbu source_segs q 0x11028 fmem rrom _ 15 15 _ (Z_to_bv 8 0)
                 SF_11028 eq_refl SD_11028).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold q. getr_resolve. rewrite v_addi_0.
        pose proof (fread_str_byte i H2 ltac:(lia)) as Hrd.
        rewrite Hb0 in Hrd. exact Hrd. }
    assert (E3 : RiscvSemantics.step source_segs (mkst q1 0x1102c fmem rrom)
                 = MachineOk (mkst q1 0x11030 fmem rrom)).
    { rewrite (step_bne_ft source_segs q1 0x1102c fmem rrom _ 15 0 _
                 SF_1102c eq_refl SD_1102c).
      - wlits. reflexivity.
      - unfold q1. getr_resolve. exact c_eq_0_true. }
    exists q1. split; [|split; [|split]].
    + intros r Hr8 Hr15. unfold q1, q. rewrite !regupd_other by assumption.
      reflexivity.
    + unfold q1, q. rewrite !regupd_other by reg_neq_tac.
      rewrite H8, Hi. reflexivity.
    + unfold q1, q. rewrite !regupd_other by reg_neq_tac. exact H18.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      apply mst_refl.
  - (* a nonzero byte: take the branch, bump s0, and come back *)
    assert (Hilt : (i < n)%nat) by lia.
    set (b := byte_at s i).
    assert (Hbnz : b <> Z_to_bv 8 0) by (apply byte_at_nz; [exact Hnz | exact Hilt]).
    set (q := regupd regs 15 (P + nat_to_word i)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11024 fmem rrom)
                 = MachineOk (mkst q 0x11028 fmem rrom)).
    { rewrite (step_add source_segs regs 0x11024 fmem rrom _ 15 18 8
                 SF_11024 eq_refl SD_11024).
      reduce_bv_eqb_ifs.
      unfold q. getr_resolve. rewrite H8, H18. wlits. reflexivity. }
    set (q1 := regupd q 15 (Z_to_bv 64 (bv_unsigned b))).
    assert (E2 : RiscvSemantics.step source_segs (mkst q 0x11028 fmem rrom)
                 = MachineOk (mkst q1 0x1102c fmem rrom)).
    { rewrite (step_lbu source_segs q 0x11028 fmem rrom _ 15 15 _ b
                 SF_11028 eq_refl SD_11028).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold q. getr_resolve. rewrite v_addi_0.
        apply fread_str_byte; [exact H2 | lia]. }
    assert (E3 : RiscvSemantics.step source_segs (mkst q1 0x1102c fmem rrom)
                 = MachineOk (mkst q1 0x110d4 fmem rrom)).
    { rewrite (step_bne_tk source_segs q1 0x1102c fmem rrom _ 15 0 _
                 SF_1102c eq_refl SD_1102c).
      - wlits. reflexivity.
      - unfold q1. getr_resolve.
        apply c_eq_0_false. rewrite u_zext8. apply byte_nz_u. exact Hbnz. }
    set (q2 := regupd q1 8 (nat_to_word (S i))).
    assert (E4 : RiscvSemantics.step source_segs (mkst q1 0x110d4 fmem rrom)
                 = MachineOk (mkst q2 0x110d8 fmem rrom)).
    { rewrite (step_addi source_segs q1 0x110d4 fmem rrom _ 8 8 _
                 SF_110d4 eq_refl SD_110d4).
      reduce_bv_eqb_ifs.
      unfold q2, q1, q. getr_resolve. rewrite H8.
      rewrite v_addi_Sj by lia. wlits. reflexivity. }
    assert (E5 : RiscvSemantics.step source_segs (mkst q2 0x110d8 fmem rrom)
                 = MachineOk (mkst q2 0x11024 fmem rrom)).
    { rewrite (step_jal_x0 source_segs q2 0x110d8 fmem rrom _ _
                 SF_110d8 eq_refl SD_110d8).
      wlits. reflexivity. }
    assert (H8' : reg_get q2 8 = nat_to_word (S i))
      by (unfold q2; apply regupd_same).
    assert (H18' : reg_get q2 18 = P).
    { unfold q2, q1, q. rewrite !regupd_other by reg_neq_tac. exact H18. }
    destruct (IH (S i) q2 ltac:(lia) H8' H18') as [regs' [Hag [H8f [H18f Hms]]]].
    exists regs'. split; [|split; [|split]].
    + intros r Hr8 Hr15. rewrite (Hag r Hr8 Hr15).
      unfold q2, q1, q. rewrite !regupd_other by assumption. reflexivity.
    + exact H8f.
    + exact H18f.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      exact Hms.
Qed.

End Strlen.

(* ================================================================= *)
(* n > 4095: exit 3 through the epilogue                              *)
(* ================================================================= *)

Lemma source_wexit_len3 : (2 <= length av)%nat -> (4095 < n)%nat ->
  to_wexit source_segs
    (init_machine_state (run_segments source_segs inp rsp rmb) 0x11128 source_phdrs rsp rmb rrnd inp)
    [] (Z_to_bv 64 3).
Proof.
  intros H2 Hn.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as HnN'.
  assert (HuN : bv_unsigned nN = Z.of_nat n)
    by (unfold nN; rewrite u_ntw by lia; reflexivity).
  destruct (source_prologue H2) as [regsP [[HP2 [HP18 [HP8 HP9]]] HmsP]].
  eapply msteps_to_wexit; [exact HmsP |].
  destruct (source_slen H2 n 0%nat regsP ltac:(lia) HP8 HP18)
    as [regsL [HfrL [H8L [H18L HmsL]]]].
  eapply msteps_to_wexit; [exact HmsL |].
  (* 0x11030 .. 0x11038: the length test, taken into the epilogue *)
  sym_block source_segs 3%nat [true] (@nil expr)
    [((8 : reg), EVar 32)] [nN] (@nil word) RA HRA.
  { (* [bgeu s0,a2] at 0x11038 -> taken, because [n > 4095] *) sym_br. }
  { (* the [s0] pin: [s0] is the scan loop's result *)
    rewrite getr_nz by reg_neq_tac. exact H8L. }
  (* epilogue at 0x11110 with a0 = 3 *)
  edestruct (source_epilogue RA fmem (Z_to_bv 64 3))
    as [regsE [HE17 [HE10 HmsE]]].
  - sym_regs HRA. rewrite getr_nz by reg_neq_tac.
    rewrite (HfrL 2) by reg_neq_tac. exact HP2.
  - sym_regs HRA. reflexivity.
  - exact fread_slot_ra.
  - exact fread_slot_0.
  - eapply msteps_to_wexit; [exact HmsE |].
    apply tw_exit_coden; [exact HE17 | exact HE10 | u_norm; lia].
Qed.

(* ================================================================= *)
(* n <= 4095: run to the mmap ecall                                   *)
(* ================================================================= *)

Lemma source_to_mmap : (2 <= length av)%nat -> (n <= 4095)%nat ->
  exists regsE,
    reg_get regsE 1 = (0x11058 : word) /\
    reg_get regsE 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) /\
    reg_get regsE 8 = nN /\
    reg_get regsE 18 = P /\
    reg_get regsE 11 = Z_to_bv 64 4096 /\
    reg_get regsE 12 = Z_to_bv 64 3 /\
    reg_get regsE 13 = Z_to_bv 64 34 /\
    reg_get regsE 14 = Z_to_bv 64 (2^64 - 1) /\
    reg_get regsE 15 = Z_to_bv 64 0 /\
    reg_get regsE 10 = Z_to_bv 64 0 /\
    bv_unsigned (getr regsE 17) = 222%Z /\
    msteps source_segs
      (init_machine_state (run_segments source_segs inp rsp rmb) 0x11128 source_phdrs rsp rmb rrnd inp)
      {| ms_regs := regsE; ms_fregs := fp_regs; ms_pc_val := 0x11178;
         ms_svc_pending := Some (getr regsE 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := fmem; ms_rom := rrom |}.
(** SEVENTEEN instructions in ONE reflective block, with no memory
    traffic at all: the [n <= 4095] test, main's six mmap-argument
    [li]s, the [jal] into the crt's [raw_syscall] and its seven register
    moves, stopping at the [ecall] that is the [tmw] branch point.  The
    only obligation is the [bgeu], because the block reads and writes no
    memory; the ten register facts the caller needs are read straight
    out of the exit register file by [sym_regs]. *)
Proof.
  intros H2 Hn.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as HnN'.
  assert (HuN : bv_unsigned nN = Z.of_nat n)
    by (unfold nN; rewrite u_ntw by lia; reflexivity).
  destruct (source_prologue H2) as [regsP [[HP2 [HP18 [HP8 HP9]]] HmsP]].
  destruct (source_slen H2 n 0%nat regsP ltac:(lia) HP8 HP18)
    as [regsL [HfrL [H8L [H18L HmsL]]]].
  assert (HL2 : getr regsL 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30))
    by (rewrite getr_nz by reg_neq_tac; rewrite (HfrL 2) by reg_neq_tac; exact HP2).
  assert (HL18 : getr regsL 18 = P)
    by (rewrite getr_nz by reg_neq_tac; exact H18L).
  replace (0x11030 : word) with (Z_to_bv 64 0x11030) in HmsL by bveq.
  sym_block_ex source_segs (mkst regsL (Z_to_bv 64 0x11030) fmem rrom)
    17%nat [false] (@nil expr)
    [((0 : reg), ELit 0); ((8 : reg), EVar 32)] [nN] (@nil word) RA HRA Hms.
  { (* [bgeu s0,a2] at 0x11038 -> not taken, because [n <= 4095] *) sym_br. }
  { (* the [s0] pin: [s0] is the scan loop's result *)
    rewrite getr_nz by reg_neq_tac. exact H8L. }
  exists RA.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ _))))))))))).
  1-11: (sym_regs HRA;
         first [ reflexivity
               | assumption
               | (f_equal; lia)
               | (apply bv_eq; u_norm; lia)
               | bveq ]).
  eapply msteps_trans; [ exact HmsP | ].
  eapply msteps_trans; [ exact HmsL | ].
  eapply msteps_trans; [ exact Hms | ]. norm_pc; sym_pc_lit.
  eapply mst_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ SF_11178 eq_refl) | apply mst_refl ].
Qed.

(* ================================================================= *)
(* Failure continuation: exit 4                                       *)
(* ================================================================= *)

Lemma source_fail_twm : forall model regs e,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  reg_get regs 1 = (0x11058 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ->
  twm source_segs (mkst (regupd regs 10 (errno_ret e)) 0x1117c fmem rrom)
      model [] (Z_to_bv 64 4).
(** FOUR instructions in ONE reflective block — the crt wrapper's [ret],
    the [mv s1,a0] of the raw return value, [li a0,4] and the [bltz]
    that the negative errno takes — and then the shared epilogue.  [a0]
    is pinned to the errno word so the branch obligation is a statement
    about it and nothing else. *)
Proof.
  intros model regs e He1 He2 Hr1 Hr2.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (errno_ret_range e He1 He2) as [Her1 Her2].
  sym_block source_segs 4%nat [true] (@nil expr)
    [((0 : reg), ELit 0); ((1 : reg), ELit 0x11058); ((10 : reg), EVar 32)]
    [errno_ret e] (@nil word) RA HRA.
  { (* [bltz s1] at 0x11060 -> taken: the raw syscall returned [-e] *)
    apply (c_lts_neg_0 (errno_ret e)); lia. }
  { (* the [ra] pin: the crt wrapper's return address *)
    getr_resolve; regupd_resolve; rewrite Hr1; bveq. }
  { (* the [a0] pin *) getr_resolve; regupd_resolve; reflexivity. }
  (* epilogue at 0x11110 with a0 = 4 *)
  edestruct (source_epilogue RA fmem (Z_to_bv 64 4))
    as [regsE [HE17 [HE10 HmsE]]].
  - sym_regs HRA. getr_resolve; regupd_resolve; exact Hr2.
  - sym_regs HRA. reflexivity.
  - exact fread_slot_ra.
  - exact fread_slot_0.
  - eapply msteps_twm; [exact HmsE|].
    apply twm_exit_coden; [exact HE17 | exact HE10 | u_norm; lia].
Qed.

(* ================================================================= *)
(* Success continuation                                               *)
(* ================================================================= *)

Section SourceSucc.

Variable aG : word.
Hypothesis HaPos : (0 < bv_unsigned aG)%Z.
Hypothesis HaAl : (bv_unsigned aG mod page_size = 0)%Z.
Hypothesis HaCeil : (bv_unsigned aG + 4096 <= bv_unsigned rsp - stack_max_size)%Z.
Hypothesis Hda : (bv_unsigned aG + 4096 <= 0x10000)%Z \/ (0x11000 <= bv_unsigned aG)%Z.
Hypothesis Hdb : (bv_unsigned aG + 4096 <= 0x11000)%Z \/ (0x12000 <= bv_unsigned aG)%Z.
Hypothesis Hdc : (bv_unsigned aG + 4096 <= 0x12000)%Z \/ (0x13000 <= bv_unsigned aG)%Z.
Hypothesis H2av : (2 <= length av)%nat.
Hypothesis Hnle : (n <= 4095)%nat.

Lemma nN_le : (Z.of_nat n <= 4095)%Z.
Proof. lia. Qed.

Definition zmem : word -> option byte := zfill aG (Z_to_bv 64 4096) fmem.
Definition cmem (i : nat) : word -> option byte :=
  wbytes zmem aG (upperv (firstn i s)).

Lemma grows_zmem : mem_grows rwmem zmem.
Proof.
  unfold zmem, zfill, fmem, emem.
  eapply mem_grows_trans; [ | apply zmem_grows ].
  repeat (eapply mem_grows_trans; [ | apply wbytes_grows ]).
  apply mem_grows_refl.
Qed.

Lemma cmem_S : forall i, (i < n)%nat ->
  cmem (S i) = wbytes (cmem i) (aG + nat_to_word i) [upperb (byte_at s i)].
Proof.
  intros i Hi. unfold cmem.
  rewrite (upperv_firstn_S s i Hi).
  rewrite wbytes_snoc.
  rewrite length_upperv_firstn by lia.
  reflexivity.
Qed.

Lemma cread_str_byte : forall i j, (i <= n)%nat -> (j <= n)%nat ->
  rdn source_segs (cmem i) (P + nat_to_word j) 1%nat = Some [byte_at s j].
Proof.
  intros i j Hi Hj.
  destruct (source_ptr_bounds H2av) as [Hge Hup].
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le.
  unfold cmem.
  rewrite rdn_wbytes_disjoint
    by (rewrite ?length_upperv_firstn by lia;
        rewrite ?word_add_nat; u_norm; lia).
  unfold zmem.
  rewrite rdn_zfill_out
    by (rewrite ?word_add_nat; u_norm; first [ lia | right; lia ]).
  apply fread_str_byte; assumption.
Qed.

(** The mmap grant is zero-mapped ([zmem] = [zfill aG 4096 _]), so
    every byte of [aG, aG+4096) is writable whatever sits underneath —
    which is what a machine store into the copied buffer now has to
    show. *)
Lemma grant_store_ok : forall (m : word -> option byte) (a : word) (k : nat),
  (bv_unsigned aG <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= bv_unsigned aG + 4096)%Z ->
  store_ok source_segs (zfill aG (Z_to_bv 64 4096) m) a k = true.
Proof.
  intros m a k Hx1 Hx2. pose proof HaCeil. pose proof rsp_hi_num. unfold stack_max_size in *. unfold zfill. apply store_ok_zmem.
  - lia.
  - exact Hx1.
  - rewrite u_Z2bv by lia. exact Hx2.
Qed.

(* ----------------------------------------------------------------- *)
(* The copy loop: 0x11070 .. 0x11084                                  *)
(* ----------------------------------------------------------------- *)

Lemma source_copy : forall f i regs,
  reg_get regs 18 = P -> reg_get regs 8 = nN -> reg_get regs 9 = aG ->
  reg_get regs 10 = Z_to_bv 64 25 ->
  reg_get regs 15 = nat_to_word i -> (i <= n)%nat -> (n - i <= f)%nat ->
  exists regs',
    (forall r : reg, r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 ->
       reg_get regs' r = reg_get regs r) /\
    reg_get regs' 12 = nat_to_word (S n) /\
    msteps source_segs (mkst regs 0x11070 (cmem i) rrom)
                       (mkst regs' 0x11084 (wbytes zmem aG (out_buf s)) rrom).
Proof.
  destruct (source_ptr_bounds H2av) as [HPge HPlt].
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms. pose proof nN_le as HnN.
  pose proof (u64_range aG) as HaR.
  assert (EM : wbytes zmem aG (out_buf s)
               = wbytes (cmem n) (aG + nat_to_word n) [Z_to_bv 8 10]).
  { unfold cmem. rewrite firstn_all. unfold out_buf.
    rewrite wbytes_snoc, length_upperv. reflexivity. }
  assert (Hexit : forall i regs, reg_get regs 8 = nN -> reg_get regs 9 = aG ->
    reg_get regs 15 = nat_to_word i -> i = n ->
    exists regs',
      (forall r : reg, r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 ->
         reg_get regs' r = reg_get regs r) /\
      reg_get regs' 12 = nat_to_word (S n) /\
      msteps source_segs (mkst regs 0x11070 (cmem i) rrom)
                         (mkst regs' 0x11084 (wbytes zmem aG (out_buf s)) rrom)).
  { intros i regs H8 H9 H15 Hieq. subst i.
    set (r1 := regupd regs 13 (aG + nat_to_word n)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11070 (cmem n) rrom)
                 = MachineOk (mkst r1 0x11074 (cmem n) rrom)).
    { rewrite (step_add source_segs regs 0x11070 (cmem n) rrom _ 13 9 15
                 SF_11070 eq_refl SD_11070).
      reduce_bv_eqb_ifs.
      getr_resolve. rewrite H9, H15. wlits. reflexivity. }
    set (r2 := regupd r1 12 (nat_to_word (S n))).
    assert (E2 : RiscvSemantics.step source_segs (mkst r1 0x11074 (cmem n) rrom)
                 = MachineOk (mkst r2 0x11078 (cmem n) rrom)).
    { rewrite (step_addi source_segs r1 0x11074 (cmem n) rrom _ 12 15 _
                 SF_11074 eq_refl SD_11074).
      reduce_bv_eqb_ifs.
      unfold r2, r1. getr_resolve. rewrite H15.
      rewrite v_addi_Sj by lia. wlits. reflexivity. }
    assert (E3 : RiscvSemantics.step source_segs (mkst r2 0x11078 (cmem n) rrom)
                 = MachineOk (mkst r2 0x1107c (cmem n) rrom)).
    { rewrite (step_bne_ft source_segs r2 0x11078 (cmem n) rrom _ 15 8 _
                 SF_11078 eq_refl SD_11078).
      - wlits. reflexivity.
      - unfold r2, r1. getr_resolve. rewrite H15, H8.
        unfold nN. apply c_eq_refl. }
    set (r3 := regupd r2 15 (10 : word)).
    assert (E4 : RiscvSemantics.step source_segs (mkst r2 0x1107c (cmem n) rrom)
                 = MachineOk (mkst r3 0x11080 (cmem n) rrom)).
    { rewrite (step_addi source_segs r2 0x1107c (cmem n) rrom _ 15 0 _
                 SF_1107c eq_refl SD_1107c).
      reduce_bv_eqb_ifs.
      unfold r3. getr_resolve. wlits. reflexivity. }
    assert (E5 : RiscvSemantics.step source_segs (mkst r3 0x11080 (cmem n) rrom)
                 = MachineOk (mkst r3 0x11084 (wbytes zmem aG (out_buf s)) rrom)).
    { rewrite EM.
      rewrite (step_sb_at source_segs r3 0x11080 (cmem n) rrom _ 13 15 _
                 (aG + nat_to_word n) (10 : word) (Z_to_bv 8 10)
                 SF_11080 eq_refl SD_11080).
      - wlits. reflexivity.
      - unfold r3, r2, r1. getr_resolve. apply v_addi_0.
      - unfold r3. getr_resolve. reflexivity.
      - bveq.
      - store_ok_peel; apply grant_store_ok;
          rewrite ?word_add_nat, ?u_Z2bv by lia; u_norm; lia. }
    exists r3. split; [| split].
    - intros r Hr12 Hr13 Hr14 Hr15. unfold r3, r2, r1.
      rewrite !regupd_other by assumption. reflexivity.
    - unfold r3, r2. rewrite regupd_other by reg_neq_tac.
      apply regupd_same.
    - eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      apply mst_refl. }
  induction f as [|f IH]; intros i regs H18 H8 H9 H10 H15 Hi Hf.
  - apply (Hexit i regs H8 H9 H15). lia.
  - destruct (Nat.eq_dec i n) as [Hieq | Hine].
    + apply (Hexit i regs H8 H9 H15). exact Hieq.
    + assert (Hilt : (i < n)%nat) by lia.
      set (b := byte_at s i) in *.
      pose proof (u8_range b) as Hb8.
      set (r1 := regupd regs 13 (aG + nat_to_word i)).
      assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11070 (cmem i) rrom)
                   = MachineOk (mkst r1 0x11074 (cmem i) rrom)).
      { rewrite (step_add source_segs regs 0x11070 (cmem i) rrom _ 13 9 15
                   SF_11070 eq_refl SD_11070).
        reduce_bv_eqb_ifs.
        getr_resolve. rewrite H9, H15. wlits. reflexivity. }
      set (r2 := regupd r1 12 (nat_to_word (S i))).
      assert (E2 : RiscvSemantics.step source_segs (mkst r1 0x11074 (cmem i) rrom)
                   = MachineOk (mkst r2 0x11078 (cmem i) rrom)).
      { rewrite (step_addi source_segs r1 0x11074 (cmem i) rrom _ 12 15 _
                   SF_11074 eq_refl SD_11074).
        reduce_bv_eqb_ifs.
        unfold r2, r1. getr_resolve. rewrite H15.
        rewrite v_addi_Sj by lia. wlits. reflexivity. }
      assert (E3 : RiscvSemantics.step source_segs (mkst r2 0x11078 (cmem i) rrom)
                   = MachineOk (mkst r2 0x110dc (cmem i) rrom)).
      { rewrite (step_bne_tk source_segs r2 0x11078 (cmem i) rrom _ 15 8 _
                   SF_11078 eq_refl SD_11078).
        - wlits. reflexivity.
        - unfold r2, r1. getr_resolve. rewrite H15, H8. unfold nN.
          apply c_eq_neq. rewrite !u_ntw by lia. lia. }
      set (r3 := regupd r2 15 (P + nat_to_word i)).
      assert (E4 : RiscvSemantics.step source_segs (mkst r2 0x110dc (cmem i) rrom)
                   = MachineOk (mkst r3 0x110e0 (cmem i) rrom)).
      { rewrite (step_add source_segs r2 0x110dc (cmem i) rrom _ 15 18 15
                   SF_110dc eq_refl SD_110dc).
        reduce_bv_eqb_ifs.
        unfold r3, r2, r1. getr_resolve. rewrite H18, H15.
        wlits. reflexivity. }
      set (r4 := regupd r3 15 (Z_to_bv 64 (bv_unsigned b))).
      assert (E5 : RiscvSemantics.step source_segs (mkst r3 0x110e0 (cmem i) rrom)
                   = MachineOk (mkst r4 0x110e4 (cmem i) rrom)).
      { rewrite (step_lbu source_segs r3 0x110e0 (cmem i) rrom _ 15 15 _ b
                   SF_110e0 eq_refl SD_110e0).
        - reduce_bv_eqb_ifs. wlits. reflexivity.
        - unfold r3. getr_resolve. rewrite v_addi_0.
          apply cread_str_byte; lia. }
      set (r5 := regupd r4 14 (v_addiw (Z_to_bv 64 (bv_unsigned b)) (-97))).
      assert (E6 : RiscvSemantics.step source_segs (mkst r4 0x110e4 (cmem i) rrom)
                   = MachineOk (mkst r5 0x110e8 (cmem i) rrom)).
      { rewrite (step_addiw source_segs r4 0x110e4 (cmem i) rrom _ 14 15 _
                   SF_110e4 eq_refl SD_110e4).
        reduce_bv_eqb_ifs.
        unfold r5, r4. getr_resolve. imm_norm. wlits. reflexivity. }
      set (r6 := regupd r5 14 (usub97 b)).
      assert (E7 : RiscvSemantics.step source_segs (mkst r5 0x110e8 (cmem i) rrom)
                   = MachineOk (mkst r6 0x110ec (cmem i) rrom)).
      { rewrite (step_andi source_segs r5 0x110e8 (cmem i) rrom _ 14 14 _
                   SF_110e8 eq_refl SD_110e8).
        reduce_bv_eqb_ifs.
        unfold r6, r5. getr_resolve. imm_norm.
        rewrite (usub97_addiw b). wlits. reflexivity. }
      assert (Hcm : cmem (S i) = wbytes (cmem i) (aG + nat_to_word i) [upperb b]).
      { apply cmem_S. exact Hilt. }
      destruct (islower b) eqn:El.
      * (* lowercase: fall through, uppercase, store *)
        assert (E8 : RiscvSemantics.step source_segs (mkst r6 0x110ec (cmem i) rrom)
                     = MachineOk (mkst r6 0x110f0 (cmem i) rrom)).
        { rewrite (step_bltu_ft source_segs r6 0x110ec (cmem i) rrom _ 10 14 _
                     SF_110ec eq_refl SD_110ec).
          - wlits. reflexivity.
          - unfold r6, r5, r4, r3, r2, r1. getr_resolve. rewrite H10.
            rewrite c_ltu_ltb. apply Z.ltb_ge.
            change (bv_unsigned (Z_to_bv 64 25)) with 25%Z.
            pose proof (usub97_le25 b El). lia. }
        set (r7 := regupd r6 15 (v_addiw (Z_to_bv 64 (bv_unsigned b)) (-32))).
        assert (E9 : RiscvSemantics.step source_segs (mkst r6 0x110f0 (cmem i) rrom)
                     = MachineOk (mkst r7 0x110f4 (cmem i) rrom)).
        { rewrite (step_addiw source_segs r6 0x110f0 (cmem i) rrom _ 15 15 _
                     SF_110f0 eq_refl SD_110f0).
          reduce_bv_eqb_ifs.
          unfold r7, r6, r5, r4. getr_resolve. imm_norm. wlits. reflexivity. }
        set (r8 := regupd r7 15 (Z_to_bv 64 (bv_unsigned b - 32))).
        assert (E10 : RiscvSemantics.step source_segs (mkst r7 0x110f4 (cmem i) rrom)
                      = MachineOk (mkst r8 0x110f8 (cmem i) rrom)).
        { rewrite (step_andi source_segs r7 0x110f4 (cmem i) rrom _ 15 15 _
                     SF_110f4 eq_refl SD_110f4).
          reduce_bv_eqb_ifs.
          unfold r8, r7. getr_resolve. imm_norm.
          rewrite (upper_addiw b El). wlits. reflexivity. }
        assert (E11 : RiscvSemantics.step source_segs (mkst r8 0x110f8 (cmem i) rrom)
                      = MachineOk (mkst r8 0x110fc (cmem (S i)) rrom)).
        { rewrite Hcm.
          rewrite (step_sb_at source_segs r8 0x110f8 (cmem i) rrom _ 13 15 _
                     (aG + nat_to_word i) (Z_to_bv 64 (bv_unsigned b - 32)) (upperb b)
                     SF_110f8 eq_refl SD_110f8).
          - wlits. reflexivity.
          - unfold r8, r7, r6, r5, r4, r3, r2, r1. getr_resolve. apply v_addi_0.
          - unfold r8. getr_resolve. reflexivity.
          - apply sb_upper_lo. exact El.
          - store_ok_peel; apply grant_store_ok;
          rewrite ?word_add_nat, ?u_Z2bv by lia; u_norm; lia. }
        set (r9 := regupd r8 15 (nat_to_word (S i))).
        assert (E12 : RiscvSemantics.step source_segs (mkst r8 0x110fc (cmem (S i)) rrom)
                      = MachineOk (mkst r9 0x11100 (cmem (S i)) rrom)).
        { rewrite (step_addi source_segs r8 0x110fc (cmem (S i)) rrom _ 15 12 _
                     SF_110fc eq_refl SD_110fc).
          reduce_bv_eqb_ifs.
          unfold r9, r8, r7, r6, r5, r4, r3, r2. getr_resolve.
          rewrite v_addi_0. wlits. reflexivity. }
        assert (E13 : RiscvSemantics.step source_segs (mkst r9 0x11100 (cmem (S i)) rrom)
                      = MachineOk (mkst r9 0x11070 (cmem (S i)) rrom)).
        { rewrite (step_jal_x0 source_segs r9 0x11100 (cmem (S i)) rrom _ _
                     SF_11100 eq_refl SD_11100).
          wlits. reflexivity. }
        assert (H18' : reg_get r9 18 = P)
          by (unfold r9, r8, r7, r6, r5, r4, r3, r2, r1;
              regupd_resolve; exact H18).
        assert (H8' : reg_get r9 8 = nN)
          by (unfold r9, r8, r7, r6, r5, r4, r3, r2, r1;
              regupd_resolve; exact H8).
        assert (H9' : reg_get r9 9 = aG)
          by (unfold r9, r8, r7, r6, r5, r4, r3, r2, r1;
              regupd_resolve; exact H9).
        assert (H10' : reg_get r9 10 = Z_to_bv 64 25)
          by (unfold r9, r8, r7, r6, r5, r4, r3, r2, r1;
              regupd_resolve; exact H10).
        assert (H15' : reg_get r9 15 = nat_to_word (S i))
          by (unfold r9; apply regupd_same).
        destruct (IH (S i) r9 H18' H8' H9' H10' H15' ltac:(lia) ltac:(lia))
          as [regs' [Hfr [H12f Hms]]].
        exists regs'. split; [| split].
        { intros r Hr12 Hr13 Hr14 Hr15.
          rewrite (Hfr r Hr12 Hr13 Hr14 Hr15).
          unfold r9, r8, r7, r6, r5, r4, r3, r2, r1.
          rewrite !regupd_other by assumption. reflexivity. }
        { exact H12f. }
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
        eapply mst_step; [reflexivity | exact E13 |].
        exact Hms.
      * (* not lowercase: branch taken, store the byte unchanged *)
        assert (E8 : RiscvSemantics.step source_segs (mkst r6 0x110ec (cmem i) rrom)
                     = MachineOk (mkst r6 0x110f8 (cmem i) rrom)).
        { rewrite (step_bltu_tk source_segs r6 0x110ec (cmem i) rrom _ 10 14 _
                     SF_110ec eq_refl SD_110ec).
          - wlits. reflexivity.
          - unfold r6, r5, r4, r3, r2, r1. getr_resolve. rewrite H10.
            rewrite c_ltu_ltb. apply Z.ltb_lt.
            change (bv_unsigned (Z_to_bv 64 25)) with 25%Z.
            pose proof (usub97_gt25 b El). lia. }
        assert (E9 : RiscvSemantics.step source_segs (mkst r6 0x110f8 (cmem i) rrom)
                     = MachineOk (mkst r6 0x110fc (cmem (S i)) rrom)).
        { rewrite Hcm.
          rewrite (step_sb_at source_segs r6 0x110f8 (cmem i) rrom _ 13 15 _
                     (aG + nat_to_word i) (Z_to_bv 64 (bv_unsigned b)) (upperb b)
                     SF_110f8 eq_refl SD_110f8).
          - wlits. reflexivity.
          - unfold r6, r5, r4, r3, r2, r1. getr_resolve. apply v_addi_0.
          - unfold r6, r5, r4. getr_resolve. reflexivity.
          - apply sb_upper_hi. exact El.
          - store_ok_peel; apply grant_store_ok;
          rewrite ?word_add_nat, ?u_Z2bv by lia; u_norm; lia. }
        set (r9 := regupd r6 15 (nat_to_word (S i))).
        assert (E12 : RiscvSemantics.step source_segs (mkst r6 0x110fc (cmem (S i)) rrom)
                      = MachineOk (mkst r9 0x11100 (cmem (S i)) rrom)).
        { rewrite (step_addi source_segs r6 0x110fc (cmem (S i)) rrom _ 15 12 _
                     SF_110fc eq_refl SD_110fc).
          reduce_bv_eqb_ifs.
          unfold r9, r6, r5, r4, r3, r2. getr_resolve.
          rewrite v_addi_0. wlits. reflexivity. }
        assert (E13 : RiscvSemantics.step source_segs (mkst r9 0x11100 (cmem (S i)) rrom)
                      = MachineOk (mkst r9 0x11070 (cmem (S i)) rrom)).
        { rewrite (step_jal_x0 source_segs r9 0x11100 (cmem (S i)) rrom _ _
                     SF_11100 eq_refl SD_11100).
          wlits. reflexivity. }
        assert (H18' : reg_get r9 18 = P)
          by (unfold r9, r6, r5, r4, r3, r2, r1; regupd_resolve; exact H18).
        assert (H8' : reg_get r9 8 = nN)
          by (unfold r9, r6, r5, r4, r3, r2, r1; regupd_resolve; exact H8).
        assert (H9' : reg_get r9 9 = aG)
          by (unfold r9, r6, r5, r4, r3, r2, r1; regupd_resolve; exact H9).
        assert (H10' : reg_get r9 10 = Z_to_bv 64 25)
          by (unfold r9, r6, r5, r4, r3, r2, r1; regupd_resolve; exact H10).
        assert (H15' : reg_get r9 15 = nat_to_word (S i))
          by (unfold r9; apply regupd_same).
        destruct (IH (S i) r9 H18' H8' H9' H10' H15' ltac:(lia) ltac:(lia))
          as [regs' [Hfr [H12f Hms]]].
        exists regs'. split; [| split].
        { intros r Hr12 Hr13 Hr14 Hr15.
          rewrite (Hfr r Hr12 Hr13 Hr14 Hr15).
          unfold r9, r6, r5, r4, r3, r2, r1.
          rewrite !regupd_other by assumption. reflexivity. }
        { exact H12f. }
        eapply mst_step; [reflexivity | exact E1 |].
        eapply mst_step; [reflexivity | exact E2 |].
        eapply mst_step; [reflexivity | exact E3 |].
        eapply mst_step; [reflexivity | exact E4 |].
        eapply mst_step; [reflexivity | exact E5 |].
        eapply mst_step; [reflexivity | exact E6 |].
        eapply mst_step; [reflexivity | exact E7 |].
        eapply mst_step; [reflexivity | exact E8 |].
        eapply mst_step; [reflexivity | exact E9 |].
        eapply mst_step; [reflexivity | exact E12 |].
        eapply mst_step; [reflexivity | exact E13 |].
        exact Hms.
Qed.

(* ----------------------------------------------------------------- *)
(* The write / munmap / exit-0 continuation                            *)
(* ----------------------------------------------------------------- *)

(* ----------------------------------------------------------------- *)
(* The put-style write-all retry loop                                 *)
(* ----------------------------------------------------------------- *)

(** Every store the write loop makes lands in main's frame or in musl's
    16-byte frame just below it, both inside the RLIMIT_STACK window. *)
Lemma mu_sok8 : forall (mem : word -> option byte) (a : word),
  mem_grows rwmem mem ->
  (bv_unsigned rsp - 0x50 <= bv_unsigned a)%Z ->
  (bv_unsigned a + 8 <= bv_unsigned rsp)%Z ->
  RiscvSemantics.store_ok source_segs mem a 8%nat = true.
Proof.
  intros mem a Hg Hlo Hhi.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  eapply store_ok_mono; [exact Hg|].
  unfold rwmem.
  apply (store_ok_wrap_window_valid source_segs inp rmb source_phdrs _ rsp rbrk a 8 rrnd
           Hvl Hlau);
    unfold stack_window_reach, stack_max_size; lia.
Qed.

Local Ltac mu_grows := solve_mem_grows.

Local Ltac mu_sok := apply mu_sok8; [ mu_grows | u_norm; lia | u_norm; lia ].

Local Ltac mu_ssd F D aexp vexp vtac := stepsd F D aexp vexp vtac ltac:(mu_sok).

Local Ltac mu_sld F D aexp vexp readtac := stepld F D aexp vexp readtac.

(** The tail after the put loop: [munmap] the grant through the crt
    wrapper, then exit 0.  Entered at 0x110ac with s1 = the grant base;
    a0..a6 are all reloaded here. *)
Lemma source_out_tail : forall model regs (mem : word -> option byte),
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ->
  reg_get regs 9 = aG ->
  map_has (vm_maps (m_vmmaps model)) aG (Z_to_bv 64 4096) = true ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x8)) 8%nat
    = Some (word_to_le_bytes 8 (0x11154 : word)) ->
  (forall a, In a [Z_to_bv 64 (bv_unsigned rsp - 0x20); Z_to_bv 64 (bv_unsigned rsp - 0x18);
                   Z_to_bv 64 (bv_unsigned rsp - 0x10)] ->
     rdn source_segs mem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  twm source_segs (mkst regs 0x110ac mem rrom) model [] (Z_to_bv 64 0).
Proof.
  intros model regs mem Hr2 Hr9 Hmap Hra Hsl.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof nN_le as HnN.
  pose proof (u64_range aG) as HaR.
  (* ---- 0x110ac .. 0x11174: the [munmap] argument setup, the [jal]
     into the crt wrapper and its seven register moves, stopping at the
     [munmap] [ecall].  No loads, no stores, no branches. *)
  sym_block source_segs 15%nat (@nil bool) (@nil expr)
    [((0 : reg), ELit 0); ((2 : reg), EVar 32); ((9 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x30); aG] (@nil word) RC HRC.
  { exact Hr2. }
  { exact Hr9. }
  (* 0x11178: ecall -> munmap *)
  chain_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ SF_11178 eq_refl) | ].
  eapply twm_munmap_rec.
  { sym_regs HRC. reflexivity. }
  { sym_regs HRC. reflexivity. }
  { sym_regs HRC. reflexivity. }
  { exact HaAl. }
  { intro Hc. apply (f_equal bv_unsigned) in Hc.
    change (bv_unsigned (Z_to_bv 64 4096)) with 4096%Z in Hc.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc.
    lia. }
  { change (bv_unsigned (Z_to_bv 64 4096)) with 4096%Z.
    rewrite page_round_up_Z_4096. unfold TASK_SIZE. pose proof HaCeil. pose proof rsp_hi_num. unfold stack_max_size in *. lia. }
  { rewrite pru_4096. exact Hmap. }
  { (* munmap refused ([munmap_errnos]): the program ignores a0 and
       exits 0 through the same three instructions and the epilogue *)
    intros e _. try norm_pc.
    sym_block source_segs 3%nat (@nil bool) (@nil expr)
      [((1 : reg), ELit 0x110cc); ((2 : reg), EVar 32)]
      [Z_to_bv 64 (bv_unsigned rsp - 0x30)] (@nil word) RD HRD.
    lazymatch goal with
    | |- twm _ (mkst ?R _ ?M _) _ _ _ =>
      edestruct (source_epilogue R M (Z_to_bv 64 0)) as [regsE [HE17 [HE10 HmsE]]]
    end.
    { sym_regs HRD. sym_close. }
    { sym_regs HRD. reflexivity. }
    { exact Hra. }
    { exact Hsl. }
    eapply msteps_twm; [exact HmsE|].
    apply twm_exit_coden; [exact HE17 | exact HE10 | u_norm; lia]. }
  rewrite pru_4096.
  (* ---- 0x1117c .. 0x110d0: THREE instructions in one block ----
     the crt wrapper's [ret], main's [li a0,0] and the jump into the
     shared epilogue. *)
  sym_block source_segs 3%nat (@nil bool) (@nil expr)
    [((1 : reg), ELit 0x110cc); ((2 : reg), EVar 32)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x30)] (@nil word) RD HRD.
  (* epilogue with a0 = 0 *)
  lazymatch goal with
  | |- twm _ (mkst ?R _ ?M _) _ _ _ =>
    edestruct (source_epilogue R M (Z_to_bv 64 0)) as [regsE [HE17 [HE10 HmsE]]]
  end.
  { sym_regs HRD. sym_close. }
  { sym_regs HRD. reflexivity. }
  { rewrite rdn_unfill_out by (u_norm; first [ lia | right; lia ]).
    exact Hra. }
  { intros aa Haa.
    assert (Hab : (bv_unsigned rsp - 0x20 <= bv_unsigned aa
                   /\ bv_unsigned aa + 8 <= bv_unsigned rsp - 0x8)%Z).
    { repeat destruct Haa as [<-|Haa]; try (exfalso; exact Haa); u_norm; lia. }
    rewrite rdn_unfill_out by (u_norm; first [ lia | right; lia ]).
    apply Hsl. exact Haa. }
  eapply msteps_twm; [exact HmsE|].
  apply twm_exit_coden; [exact HE17 | exact HE10 | u_norm; lia].
Qed.

(** After a (possibly short) delivery of [k] bytes the machine sits at
    0x1120c ([__syscall_cp_c]'s post-ecall [ret]) with
    a0 = [len_word (firstn k rest)].  It returns through musl's [write]
    wrapper and [__syscall_ret], reloads the pointer/count spills at
    sp+0 / sp+8, updates them and either falls into the munmap tail
    (full delivery) or respills and reissues.  Induction on
    [fuel >= length rest]. *)
Lemma src_put_wall : forall model fuel (rest : list byte) (p : word) k regs mem,
  (length rest <= fuel)%nat ->
  (1 <= k)%nat -> (k <= length rest)%nat ->
  (Z.of_nat (length rest) <= 4096)%Z ->
  (0 < bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) <= bv_unsigned rsp - 0x50)%Z ->
  reg_get regs 1 = (0x111a8 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ->
  reg_get regs 9 = aG ->
  reg_get regs 10 = len_word (firstn k rest) ->
  bv_unsigned (reg_get regs 17) = 64%Z ->
  map_has (vm_maps (m_vmmaps model)) aG (Z_to_bv 64 4096) = true ->
  mem_grows rwmem mem ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8%nat
    = Some (word_to_le_bytes 8 (0x11094 : word)) ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x28)) 8%nat
    = Some (word_to_le_bytes 8 (len_word rest)) ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x30)) 8%nat
    = Some (word_to_le_bytes 8 p) ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x8)) 8%nat
    = Some (word_to_le_bytes 8 (0x11154 : word)) ->
  (forall a, In a [Z_to_bv 64 (bv_unsigned rsp - 0x20); Z_to_bv 64 (bv_unsigned rsp - 0x18);
                   Z_to_bv 64 (bv_unsigned rsp - 0x10)] ->
     rdn source_segs mem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  rdn source_segs mem p (length rest) = Some rest ->
  twm_tail source_segs (mkst regs (0x1120c : word) mem rrom)
    model (skipn k rest) [] (Z_to_bv 64 0).
Proof.
  intros model fuel. induction fuel as [|fuel IH];
    intros rest p k regs mem Hfuel Hk1 Hk2 Hlen Hplo Hphi
           H1 H2 H9 H10 H17 Hmap Hgrow Hra40 Hcnt Hptr Hslra Hsl Hread.
  { lia. }
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  (* 0x1120c: ret out of __syscall_cp_c, back into the write wrapper *)
  stepjr SF_1120c SD_1120c (0x111a8 : word) ltac:(getr_resolve; exact H1).
  (* 0x111a8: ld ra,8(sp) -- the wrapper's saved ra (0x11094) *)
  mu_sld SF_111a8 SD_111a8 (Z_to_bv 64 (bv_unsigned rsp - 0x38))
    (0x11094 : word) ltac:(exact Hra40).
  (* 0x111ac: addi sp,sp,16 -- pop the wrapper frame *)
  stepiv SF_111ac SD_111ac (Z_to_bv 64 (bv_unsigned rsp - 0x30))
    ltac:(getr_resolve; rewrite H2; sp_norm; f_equal; lia).
  (* 0x111b0: j __syscall_ret *)
  stepj SF_111b0 SD_111b0.
  (* 0x111b4: lui a5,0xfffff *)
  stepi SF_111b4 SD_111b4.
  (* 0x111b8: bltu a5,a0 falls through (the delivery is no error) *)
  step_intro;
    [ reflexivity
    | eapply step_bltu_ft;
      [ exact SF_111b8 | reflexivity | exact SD_111b8
      | getr_resolve; rewrite H10;
        rewrite c_ltu_ltb; apply Z.ltb_ge;
        match goal with |- context [bv_unsigned (v_lui ?z)] =>
          replace (bv_unsigned (v_lui z)) with 18446744073709547520%Z
            by (vm_compute; reflexivity)
        end;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x111bc: ret -- back into main's put loop at 0x11094 *)
  stepjr SF_111bc SD_111bc (0x11094 : word) ltac:(getr_resolve; reflexivity).
  (* 0x11094: blez a0 falls through (the delivery is nonempty) *)
  step_intro;
    [ reflexivity
    | eapply step_bge_ft;
      [ exact SF_11094 | reflexivity | exact SD_11094
      | getr_resolve; rewrite H10; apply c_lts_0_pos;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x11098: ld a2,8(sp) -- the count spill *)
  mu_sld SF_11098 SD_11098 (Z_to_bv 64 (bv_unsigned rsp - 0x28))
    (len_word rest) ltac:(exact Hcnt).
  (* 0x1109c: ld a1,0(sp) -- the pointer spill *)
  mu_sld SF_1109c SD_1109c (Z_to_bv 64 (bv_unsigned rsp - 0x30)) p
    ltac:(exact Hptr).
  (* 0x110a0: sub a2,a2,a0 *)
  stepiv SF_110a0 SD_110a0 (len_word (skipn k rest))
    ltac:(getr_resolve; rewrite H10; apply v_sub_len_firstn; lia).
  (* 0x110a4: add a1,a1,a0 *)
  stepiv SF_110a4 SD_110a4 (Z_to_bv 64 (bv_unsigned p + Z.of_nat k))
    ltac:(getr_resolve; rewrite H10; apply v_add_len_firstn_Z; lia).
  destruct (Nat.eq_dec k (length rest)) as [-> | Hne].
  - (* full delivery: bnez not taken, fall into the munmap tail *)
    rewrite skipn_all.
    step_intro;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact SF_110a8 | reflexivity | exact SD_110a8
        | getr_resolve; apply c_eq_0_of_u; reflexivity ]
      | norm_pc ].
    apply twmt_done. apply source_out_tail.
    + regupd_resolve; reflexivity.
    + regupd_resolve; exact H9.
    + exact Hmap.
    + exact Hslra.
    + exact Hsl.
  - (* short delivery: bnez taken, respill and reissue *)
    step_intro;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact SF_110a8 | reflexivity | exact SD_110a8
        | getr_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* 0x11084: li a0,1 *)
    stepiv SF_11084 SD_11084 (Z_to_bv 64 1) ltac:(getr_resolve; bveq).
    (* 0x11088: sd a2,8(sp) -- respill the count *)
    mu_ssd SF_11088 SD_11088 (Z_to_bv 64 (bv_unsigned rsp - 0x28))
      (len_word (skipn k rest)) ltac:(getr_resolve; reflexivity).
    (* 0x1108c: sd a1,0(sp) -- respill the pointer *)
    mu_ssd SF_1108c SD_1108c (Z_to_bv 64 (bv_unsigned rsp - 0x30))
      (Z_to_bv 64 (bv_unsigned p + Z.of_nat k))
      ltac:(getr_resolve; reflexivity).
    (* 0x11090: jal write() *)
    stepj SF_11090 SD_11090.
    (* the wrapper: frame, arg shuffle, ra spill, __syscall_cp *)
    stepiv SF_11180 SD_11180 (Z_to_bv 64 (bv_unsigned rsp - 0x40))
      ltac:(getr_resolve; sp_norm; f_equal; lia).
    stepiv SF_11184 SD_11184 (len_word (skipn k rest))
      ltac:(getr_resolve; apply v_addi_0).
    stepi SF_11188 SD_11188.
    stepiv SF_1118c SD_1118c (Z_to_bv 64 (bv_unsigned p + Z.of_nat k))
      ltac:(getr_resolve; apply v_addi_0).
    stepi SF_11190 SD_11190.
    stepiv SF_11194 SD_11194 (Z_to_bv 64 1)
      ltac:(getr_resolve; apply v_addi_0).
    stepi SF_11198 SD_11198.
    stepiv SF_1119c SD_1119c (Z_to_bv 64 64) ltac:(getr_resolve; bveq).
    mu_ssd SF_111a0 SD_111a0 (Z_to_bv 64 (bv_unsigned rsp - 0x38))
      (0x11094 : word) ltac:(getr_resolve; bveq).
    stepj SF_111a4 SD_111a4.
    (* 0x11210: __syscall_cp's trampoline into __syscall_cp_c *)
    stepj SF_11210 SD_11210.
    (* __syscall_cp_c's seven shuffles *)
    stepiv SF_111ec SD_111ec (Z_to_bv 64 64) ltac:(getr_resolve; apply v_addi_0).
    stepiv SF_111f0 SD_111f0 (Z_to_bv 64 1) ltac:(getr_resolve; apply v_addi_0).
    stepiv SF_111f4 SD_111f4 (Z_to_bv 64 (bv_unsigned p + Z.of_nat k))
      ltac:(getr_resolve; apply v_addi_0).
    stepiv SF_111f8 SD_111f8 (len_word (skipn k rest))
      ltac:(getr_resolve; apply v_addi_0).
    stepi SF_111fc SD_111fc.
    stepi SF_11200 SD_11200.
    stepi SF_11204 SD_11204.
    (* 0x11208: ecall -- the reissued write *)
    eapply twmt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ SF_11208 eq_refl) |].
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
      rewrite (ms_read_bytes_rdn (run_segments source_segs inp rsp rmb)) by reflexivity;
      unfold run_segments; apply rdn_lift.
      cbn [ms_mem].
      replace (word_to_nat (len_word (skipn k rest)))
        with (length (skipn k rest))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      rewrite !rdn_wbytes_below
        by (rewrite ?length_N_to_le_bytes, ?length_skipn; u_norm; lia).
      pose proof (rdn_skipn source_segs mem (length rest) p rest k Hread Hk2)
        as Hsk.
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
      * regupd_resolve; bveq.
      * regupd_resolve; reflexivity.
      * regupd_resolve; exact H9.
      * regupd_resolve; reflexivity.
      * regupd_resolve; first [ exact H17 | vm_compute; reflexivity ].
      * exact Hmap.
      * mu_grows.
      * apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite !rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite !rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        exact Hslra.
      * intros a Ha.
        assert (Hab : (bv_unsigned rsp - 0x20 <= bv_unsigned a
                       /\ bv_unsigned a + 8 <= bv_unsigned rsp - 0x8)%Z).
        { repeat destruct Ha as [<-|Ha]; try (exfalso; exact Ha); u_norm; lia. }
        rewrite !rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        apply Hsl. exact Ha.
      * rewrite !rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes, ?length_skipn; u_norm; lia).
        pose proof (rdn_skipn source_segs mem (length rest) p rest k Hread Hk2)
          as Hsk.
        rewrite word_add_nat_Z in Hsk by lia.
        rewrite length_skipn. exact Hsk.
Qed.

Lemma source_succ_twm : forall model regs,
  reg_get regs 1 = (0x11058 : word) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ->
  reg_get regs 8 = nN -> reg_get regs 18 = P ->
  map_has (vm_maps (m_vmmaps model)) aG (Z_to_bv 64 4096) = true ->
  twm source_segs
      (mkst (regupd regs 10 aG) 0x1117c (zfill aG (Z_to_bv 64 4096) fmem) rrom)
      model [out_buf s] (Z_to_bv 64 0).
Proof.
  intros model regs Hr1 Hr2 Hr8 Hr18 Hmap.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof nN_le as HnN.
  pose proof (u64_range aG) as HaR.
  (* ---- 0x1117c .. 0x11070: SEVEN instructions in one block ----
     the crt wrapper's [ret], the [mv s1,a0] of the grant address, the
     [bltz] that a valid grant does NOT take, and the three-register
     setup of the copy loop. *)
  sym_block source_segs 7%nat [false] (@nil expr)
    [((0 : reg), ELit 0); ((1 : reg), ELit 0x11058); ((10 : reg), EVar 32)]
    [aG] (@nil word) RA HRA.
  { (* [bltz s1] at 0x11060 -> not taken: the grant address is positive *)
    apply (c_lts_pos_0 aG); lia. }
  { (* the [ra] pin *) getr_resolve; regupd_resolve; rewrite Hr1; bveq. }
  { (* the [a0] pin *) getr_resolve; regupd_resolve; reflexivity. }
  (* copy loop *)
  edestruct (source_copy n 0%nat RA) as [regsC [HfrC [H12C HmsC]]].
  { sym_regs HRA; getr_resolve; regupd_resolve; exact Hr18. }
  { sym_regs HRA; getr_resolve; regupd_resolve; exact Hr8. }
  { sym_regs HRA; reflexivity. }
  { sym_regs HRA; reflexivity. }
  { sym_regs HRA; reflexivity. }
  { lia. }
  { lia. }
  eapply msteps_twm; [exact HmsC |].
  assert (HC2 : reg_get regsC 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30)).
  { rewrite (HfrC 2) by reg_neq_tac. sym_regs HRA.
    getr_resolve; regupd_resolve. exact Hr2. }
  assert (HC9 : reg_get regsC 9 = aG).
  { rewrite (HfrC 9) by reg_neq_tac. sym_regs HRA. reflexivity. }
  assert (HC11 : reg_get regsC 11 = aG).
  { rewrite (HfrC 11) by reg_neq_tac. sym_regs HRA. reflexivity. }
  (* ---- 0x11084 .. 0x11208: TWENTY-TWO instructions in one block ----
     the two argument spills, the [jal] into the crt's [write], its own
     frame push, the seven-register shuffle, the [ra] spill, the [jal]
     into [__syscall_cp] and its seven moves, stopping at the write
     [ecall].  Three stores, no loads, no branches: three [store_ok]
     obligations and nothing else. *)
  sym_block source_segs 22%nat (@nil bool) (@nil expr)
    [((2 : reg), EVar 32); ((12 : reg), EVar 33); ((11 : reg), EVar 34)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x30); nat_to_word (S n); aG]
    (@nil word) RB HRB.
  1-3: solve_store_ok_inv.
  { (* the [sp] pin *) rewrite getr_nz by reg_neq_tac. exact HC2. }
  { (* the [a2] pin: the copy loop's byte count *)
    rewrite getr_nz by reg_neq_tac. exact H12C. }
  { (* the [a1] pin: the grant address *)
    rewrite getr_nz by reg_neq_tac. exact HC11. }
  (* 0x11208: ecall -> the write *)
  chain_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ SF_11208 eq_refl) | ].
  eapply twm_write_ret.
  { sym_regs HRB. reflexivity. }
  { sym_regs HRB. reflexivity. }
  { rewrite (ms_read_bytes_rdn (run_segments source_segs inp rsp rmb)) by reflexivity;
      unfold run_segments; apply rdn_lift.
    cbn [ms_mem ms_regs].
    sym_regs HRB.
    replace (word_to_nat (nat_to_word (S n))) with (length (out_buf s))
      by (rewrite length_out_buf, word_to_nat_ntw by lia; reflexivity).
    repeat (rewrite rdn_wbytes_below
      by (rewrite ?length_N_to_le_bytes, ?length_out_buf; u_norm; lia)).
    apply rdn_wbytes_hit.
    rewrite length_out_buf. lia. }
  { (* [vfs_write]'s [access_ok] on the whole buffer *)
    sym_regs HRB.
    apply Uaccess.access_okb_intro.
    rewrite ?v_addi_0. rewrite u_ntw by lia.
    unfold TASK_SIZE. lia. }
  { rewrite length_out_buf. lia. }
  (* ---- 0x1120c ..: the put-style retry loop, per delivered length. *)
  intros k Hk1 Hk2.
  norm_pc.
  assert (Eln : len_word (out_buf s) = nat_to_word (S n))
    by (unfold len_word, nat_to_word; rewrite length_out_buf; reflexivity).
  apply (src_put_wall model (length (out_buf s)) (out_buf s) aG k).
  - lia.
  - exact Hk1.
  - exact Hk2.
  - rewrite length_out_buf; lia.
  - exact HaPos.
  - rewrite length_out_buf. lia.
  - regupd_resolve; sym_regs HRB; sym_close.
  - regupd_resolve; sym_regs HRB; sym_close.
  - regupd_resolve; sym_regs HRB; rewrite getr_nz by reg_neq_tac; exact HC9.
  - regupd_resolve; reflexivity.
  - regupd_resolve; sym_regs HRB; reflexivity.
  - exact Hmap.
  - (* the loop's memory grows out of the initial stack image *)
    repeat (eapply mem_grows_trans; [ | apply wbytes_grows ]).
    exact grows_zmem.
  - repeat (rewrite rdn_wbytes_disjoint
              by (rewrite ?length_N_to_le_bytes; u_norm; lia));
    apply rdn_wbytes_hit8; u_norm; lia.
  - rewrite Eln.
    repeat (rewrite rdn_wbytes_disjoint
              by (rewrite ?length_N_to_le_bytes; u_norm; lia));
    apply rdn_wbytes_hit8; u_norm; lia.
  - repeat (rewrite rdn_wbytes_disjoint
              by (rewrite ?length_N_to_le_bytes; u_norm; lia));
    apply rdn_wbytes_hit8; u_norm; lia.
  - repeat (rewrite rdn_wbytes_disjoint
              by (rewrite ?length_N_to_le_bytes, ?length_out_buf; u_norm; lia)).
    unfold zmem.
    rewrite rdn_zfill_out by (u_norm; first [ lia | right; lia ]).
    exact fread_slot_ra.
  - intros aa Haa.
    assert (Hab : (bv_unsigned rsp - 0x20 <= bv_unsigned aa
                   /\ bv_unsigned aa + 8 <= bv_unsigned rsp - 0x8)%Z).
    { repeat destruct Haa as [<-|Haa]; try (exfalso; exact Haa); u_norm; lia. }
    repeat (rewrite rdn_wbytes_disjoint
              by (rewrite ?length_N_to_le_bytes, ?length_out_buf; u_norm; lia)).
    unfold zmem.
    rewrite rdn_zfill_out by (u_norm; first [ lia | right; lia ]).
    apply fread_slot_0. exact Haa.
  - repeat (rewrite rdn_wbytes_below
              by (rewrite ?length_N_to_le_bytes, ?length_out_buf; u_norm; lia)).
    apply rdn_wbytes_hit. rewrite length_out_buf. lia.
Qed.

End SourceSucc.

(* ================================================================= *)
(* The packaged tmw derivation for the source binary                  *)
(* ================================================================= *)

(** The source's whole run, from the launch's state and model.  The model
    is [Run.init_config]'s: [State.with_vdso] of the draw's vDSO counter
    over [State.init_model]; [Hmb] is [Run.valid_mmap_base]'s floor, which
    keeps the vDSO pair above the grant's gap. *)
Lemma source_tmw : (mmap_base_min <= bv_unsigned rmb)%Z ->
  (2 <= length av)%nat -> (n <= 4095)%nat ->
  tmw source_segs
      (init_machine_state (run_segments source_segs inp rsp rmb) 0x11128 source_phdrs rsp rmb rrnd inp)
      (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
         (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
      [] (Z_to_bv 64 4) [out_buf s] (Z_to_bv 64 0).
Proof.
  intros Hmb H2 Hn.
  destruct (source_to_mmap H2 Hn)
    as (regsE & HE1 & HE2 & HE8 & HE18 & HE11 & HE12 & HE13 & HE14 & HE15
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
    apply source_fail_twm; assumption.
  - (* success family: one write, munmap, exit 0 *)
    intros aa Hg.
    rewrite HE11 in Hg.
    change (bv_unsigned (Z_to_bv 64 4096)) with 4096%Z in Hg.
    rewrite page_round_up_Z_4096 in Hg.
    rewrite HE11, pru_4096.
    destruct (source_grant_unpack inp _ rbrk rmb rsp aa _ Hg)
      as (Hpos & Hal' & Hceil & Hda' & Hdb' & Hdc').
    norm_pc.
    apply (source_succ_twm aa Hpos Hal' Hceil Hda' Hdb' Hdc' H2 Hn);
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
    exact (source_grant_witness inp _ rbrk rmb rsp _ Hsp_lo Hmb).
Qed.

End SourceProof.
