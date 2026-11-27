(** * grep-args-ns SOURCE binary (musl-gcc -Os).

    PROOF-SIDE FILE (not part of the trusted specification).  Symbolic
    execution of the source image from its entry point to the exit
    [ecall], concluding the two [to_wexit] derivations [Proof.v] glues
    (one per input branch: [argc >= 2] and [argc < 2]).  See [Proof.v]'s
    header for the program and the proof shape.

    The run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  The derivations step over the image's own [source_segs] and are
    carried to the run's list whole ([RunSegmentsLift.to_wallexit_run]):
    no instruction here fetches from the pair and no write node reads the
    buffer through the list.  The states carry the run's rom.  The stack
    bounds come from the entry predicate's launch conjunct
    [Run.entry_launch_ok_va] and [Run.valid_launch]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec WallSim StepTac MuslStrlen StreamSim StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Common Require Import Footprint SymExec SymBranch SymSide SymTac.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import grep_args_ns_code.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import grep_args_ns_defs.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them. *)
#[local] Instance grep_args_ns_source_fx : FPState := fx0.

(* ######################################################################### *)
(* SOURCE binary                                                          *)
(* ######################################################################### *)

Section SourceProof.

Variable inp : ProcInput.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.

(** The argv and envp lists of the launch. *)
Local Abbreviation av := (in_argv inp).
Local Abbreviation ev := (in_envp inp).

(** The initial stack pointer, the program break and the mmap base are
    QUANTIFIED (ASLR): the whole section is generic over them. *)
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
    ([StepTac.bsb_bound]), places the argv strings below [ed_top] and
    the stack-store window. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry rsp rbrk rmb rrnd) inp.

Lemma rsp_lo_num : (0x7fff80000000 <= bv_unsigned rsp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma rsp_hi_num : (bv_unsigned rsp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x11174%N.
Proof. vm_compute. reflexivity. Qed.

Definition argcN : word := len_word av.
(** The initial overlay, with the entry point [init_mkst] passes to it. *)
Definition wmem : word -> option byte :=
  wrap_mem inp rmb source_phdrs (0x11174 : word) rsp rrnd.
(** The run's rom: the image's segments, then the vDSO pair. *)
Definition rrom : word -> option byte := seg_rom (run_segments source_segs inp rsp rmb).

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
Proof.
  pose proof (valid_argv_len av Hva).
  unfold argcN, len_word. apply u_Z2bv; lia.
Qed.

(** No-overflow bound for the initial stack image (feeds the stack-read
    lemmas' side conditions). *)
Lemma source_bsb_nw :
  (bv_unsigned rsp
   + Z.of_nat (length (entry_stack_image inp rmb source_phdrs (0x11174 : word) rsp rrnd))
   < 2^64)%Z.
Proof.
  pose proof (bsb_bound Sv48 inp rmb source_phdrs (0x11174 : word) rsp rbrk rrnd Hvl Hlau).
  pose proof rsp_hi_num. lia.
Qed.

(** The pointer _start stores into musl's [environ] slot at 0x13000. *)
Definition envp_ptr : word :=
  Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat (length av) + 8).

(** The value _start computes in a2 equals [envp_ptr]. *)
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

(** Memory after _start's environ store and main()'s prologue: the
    environ slot, then six 8-byte callee-save slots below the initial
    sp, in execution order (innermost = first store).  Every value is a
    known constant of the initial state (s* = 0, ra = 0x111a0).  The
    two lowest slots of the frame, 0(sp) and 8(sp) = [rsp-0x40,
    rsp-0x30), are NOT initialized here: -fno-builtin main uses them as
    spill scratch around its write() calls. *)
Definition fmem : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes wmem
    0x13000 (word_to_le_bytes 8 envp_ptr))        (* sd a2, 0(t1)  [environ] *)
    (Z_to_bv 64 (bv_unsigned rsp - 0x10)) (word_to_le_bytes 8 (Z_to_bv 64 0)))  (* sd s0, 48(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 0x18)) (word_to_le_bytes 8 (Z_to_bv 64 0)))  (* sd s1, 40(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 0x20)) (word_to_le_bytes 8 (Z_to_bv 64 0)))  (* sd s2, 32(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 0x30)) (word_to_le_bytes 8 (Z_to_bv 64 0)))  (* sd s4, 16(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 8)) (word_to_le_bytes 8 (0x111a0 : word)))   (* sd ra, 56(sp) *)
    (Z_to_bv 64 (bv_unsigned rsp - 0x28)) (word_to_le_bytes 8 (Z_to_bv 64 0)).  (* sd s3, 24(sp) *)

(** Reads at or above the initial sp see through the frame stores.
    (New no-overflow hypothesis, mirroring [rdn_wbytes_disjoint].) *)
Lemma rdn_fmem_above : forall (a : word) n,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn source_segs fmem a n = rdn source_segs wmem a n.
Proof.
  intros a n Ha Hn. pose proof rsp_lo_num. pose proof rsp_hi_num. unfold fmem.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia)).
  reflexivity.
Qed.

(** Reads over [wmem] at/above sp defer to the raw stack bytes. *)
Lemma rdn_wmem_stack : forall (a : word) n,
  (bv_unsigned rsp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn source_segs wmem a n
  = rdn source_segs
      (stack_to_mem rsp (entry_stack_image inp rmb source_phdrs (0x11174 : word) rsp rrnd)) a n.
Proof. intros a n Ha Hn. apply rdn_wrap_stack_above; assumption. Qed.

(** argc at [rsp]. *)
Lemma read_argc_f :
  rdn source_segs fmem rsp 8%nat = Some (word_le8 argcN).
Proof.
  pose proof rsp_hi_num.
  rewrite rdn_fmem_above by lia. rewrite rdn_wmem_stack by lia.
  apply read_argc. exact source_bsb_nw.
Qed.

(** argv pointer k at [rsp + 8 + 8k]. *)
Lemma read_ptr_f : forall k, (k < length av)%nat ->
  rdn source_segs fmem (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat k)) 8%nat
  = Some (word_le8 (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)).
Proof.
  intros k Hk.
  pose proof rsp_hi_num. pose proof rsp_lo_num.
  pose proof (valid_argv_len av Hva) as Hlen.
  assert (HkZ : (Z.of_nat k <= 1024)%Z) by lia.
  replace (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat k))
    with (rsp + nat_to_word (8 + 8 * k)) by (rewrite word_add_nat; f_equal; lia).
  rewrite rdn_fmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
  apply read_argv_ptr_k; [assumption | exact source_bsb_nw].
Qed.

Lemma source_ptr_bounds : forall k, (k < length av)%nat ->
  (bv_unsigned rsp <= bv_unsigned (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k))%Z /\
  (bv_unsigned (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)
   + Z.of_nat (length (nth k av [])) + 1 < 2^64)%Z.
Proof. intros k Hk. exact (argv_ptr_bounds Sv48 inp rmb rsp rbrk rrnd k Hlau Hk). Qed.

(** String byte j (including the NUL sentinel at j = len). *)
Lemma read_str_byte_f : forall k j, (k < length av)%nat ->
  (j <= length (nth k av []))%nat ->
  rdn source_segs fmem (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word j) 1%nat
  = Some [byte_at (nth k av []) j].
Proof.
  intros k j Hk Hj.
  destruct (source_ptr_bounds k Hk) as [Hge Hup].
  pose proof (valid_argv_str_len av k Hva Hk) as Hslen.
  pose proof (u64_range rsp). pose proof (u64_range (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)).
  rewrite rdn_fmem_above by (rewrite word_add_nat; u_norm; lia).
  rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
  eapply read_argv_byte_k; eassumption.
Qed.

(** Whole string k. *)
Lemma read_str_f : forall k, (k < length av)%nat ->
  rdn source_segs fmem (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k) (length (nth k av []))
  = Some (nth k av []).
Proof.
  intros k Hk.
  destruct (source_ptr_bounds k Hk) as [Hge Hup].
  rewrite rdn_fmem_above by lia.
  rewrite rdn_wmem_stack by lia.
  eapply read_argv_str_k; eassumption.
Qed.

(** Room for a whole word past any offset inside argv string [k]: the
    envp strings, the exec file name, its NUL and the eight-byte slot
    [create_init_stack_vma] leaves at the top lie above the last argv
    string's NUL.  (Instance of MuslStrlen's [argv_ptr_room].) *)
Lemma source_ptr_room : forall k, (k < length av)%nat ->
  (bv_unsigned (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)
     + Z.of_nat (length (nth k av [])) + 9
   <= bv_unsigned rsp
      + Z.of_nat (length (entry_stack_image inp rmb source_phdrs (0x11174 : word) rsp rrnd)))%Z.
Proof. intros k Hk. eapply argv_ptr_room; eassumption. Qed.

(** The '\n' byte in the source image at 0x12000. *)
Lemma seg_rom_newline : seg_rom source_segs 0x12000 = Some (Z_to_bv 8 10).
Proof. vm_refl. Qed.

Lemma read_newline_f : rdn source_segs fmem 0x12000 1%nat = Some [Z_to_bv 8 10].
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. unfold fmem.
  repeat (rewrite rdn_wbytes_below
            by (rewrite ?length_N_to_le_bytes; imm_norm; u_norm; lia)).
  cbn [rdn].
  unfold wmem.
  rewrite (wrap_mem_below Sv48 inp rmb source_phdrs (0x11174 : word) rsp rbrk rrnd 0x12000 Hlau)
    by (rewrite stack_max_size_val; imm_norm; lia).
  rewrite seg_rom_newline. reflexivity.
Qed.

(** Frame-slot read-back for the epilogue. *)
Lemma read_slot_ra :
  rdn source_segs fmem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
  = Some (word_to_le_bytes 8 (0x111a0 : word)).
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. unfold fmem.
  rewrite rdn_wbytes_disjoint
    by (rewrite ?length_N_to_le_bytes; u_norm; lia).
  apply rdn_wbytes_hit8. u_norm; lia.
Qed.

Lemma read_slot_0 : forall a : word,
  In a [Z_to_bv 64 (bv_unsigned rsp - 0x30); Z_to_bv 64 (bv_unsigned rsp - 0x28);
        Z_to_bv 64 (bv_unsigned rsp - 0x20); Z_to_bv 64 (bv_unsigned rsp - 0x18);
        Z_to_bv 64 (bv_unsigned rsp - 0x10)] ->
  rdn source_segs fmem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros a Ha. pose proof rsp_lo_num. pose proof rsp_hi_num. unfold fmem.
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
(* The mem_ok abstraction: memories that agree with [fmem] outside    *)
(* the scratch window [rsp-0x50, rsp-0x30) — the write() wrapper's    *)
(* own 16-byte frame [rsp-0x50, rsp-0x40) plus main's two spill slots *)
(* 0(sp)/8(sp) = [rsp-0x40, rsp-0x30).                                *)
(* ================================================================= *)

(** …and, second clause, [mem] is still writable wherever the initial
    overlay [wmem] was.  The wrapper's scratch stores are machine
    stores, which now carry a [store_ok] bound, and [mem] is abstract
    here — so the bound has to travel with it.  [mem_grows] is the
    weakest thing that carries it: the overlay only ever gains
    addresses.

    The two clauses sit under ONE [forall], and [mem_ok] is SEALED
    ([Opaque], just below the preservation lemma).  Both are needed to
    keep [repeat split] — which the scripts below use on goals that
    have [mem_ok] as a conjunct — from taking it apart into halves that
    none of the lemmas here match. *)
Definition mem_ok (mem : word -> option byte) : Prop :=
  forall (a : word) (n : nat),
    ((bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
     ((bv_unsigned rsp - 0x30 <= bv_unsigned a)%Z \/
      (bv_unsigned a + Z.of_nat n <= bv_unsigned rsp - 0x50)%Z) ->
     rdn source_segs mem a n = rdn source_segs fmem a n)
    /\ (wmem a <> None -> mem a <> None).

(** The two projections; [mem_ok_grows] is what the shared store-bound
    dispatcher reaches for (via [store_ok_db]), and both are the only
    way past the seal below. *)
Lemma mem_ok_agree : forall mem, mem_ok mem ->
  forall (a : word) (n : nat),
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    ((bv_unsigned rsp - 0x30 <= bv_unsigned a)%Z \/
     (bv_unsigned a + Z.of_nat n <= bv_unsigned rsp - 0x50)%Z) ->
    rdn source_segs mem a n = rdn source_segs fmem a n.
Proof. intros mem H a n. apply (H a n). Qed.

Lemma mem_ok_grows : forall mem, mem_ok mem -> mem_grows wmem mem.
Proof. intros mem H x. apply (H x 0%nat). Qed.

Local Hint Resolve mem_ok_grows : store_ok_db.

Lemma fmem_ok : mem_ok fmem.
Proof.
  assert (Hg : mem_grows wmem fmem) by (unfold fmem; solve_mem_grows).
  intros a n. split; [reflexivity | apply Hg].
Qed.

(** An 8-byte store inside the scratch window preserves [mem_ok]. *)
Lemma mem_ok_scratch8 : forall mem (a : word) v,
  mem_ok mem ->
  (bv_unsigned rsp - 0x50 <= bv_unsigned a)%Z ->
  (bv_unsigned a + 8 <= bv_unsigned rsp - 0x30)%Z ->
  mem_ok (wbytes mem a (word_to_le_bytes 8 v)).
Proof.
  intros mem a v Hm Hlo Hhi.
  pose proof (mem_ok_grows _ Hm) as Hg.
  assert (Hg' : mem_grows wmem (wbytes mem a (word_to_le_bytes 8 v)))
    by solve_mem_grows.
  intros a' n. split; [|apply Hg']. intros Hnw Hd.
  destruct Hd as [Hd | Hd].
  - rewrite rdn_wbytes_disjoint
      by (rewrite ?length_N_to_le_bytes; lia).
    apply (mem_ok_agree _ Hm); [exact Hnw | left; exact Hd].
  - rewrite rdn_wbytes_below
      by (rewrite ?length_N_to_le_bytes; pose proof rsp_hi_num; lia).
    apply (mem_ok_agree _ Hm); [exact Hnw | right; exact Hd].
Qed.

(* Everything below reaches [mem_ok] only through the lemmas above; seal
   it so [repeat split] leaves it alone (see the note at the
   definition). *)
Opaque mem_ok.

(* mem_ok-relative read lemmas *)

Lemma read_ptr_m : forall mem, mem_ok mem -> forall k, (k < length av)%nat ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat k)) 8%nat
  = Some (word_le8 (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)).
Proof.
  intros mem Hm k Hk. pose proof rsp_lo_num. pose proof rsp_hi_num.
  pose proof (valid_argv_len av Hva).
  rewrite (mem_ok_agree _ Hm) by (u_norm; lia). apply read_ptr_f. exact Hk.
Qed.

Lemma read_str_byte_m : forall mem, mem_ok mem -> forall k j,
  (k < length av)%nat -> (j <= length (nth k av []))%nat ->
  rdn source_segs mem (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word j) 1%nat
  = Some [byte_at (nth k av []) j].
Proof.
  intros mem Hm k j Hk Hj. pose proof rsp_lo_num.
  destruct (source_ptr_bounds k Hk) as [Hge Hup].
  pose proof (valid_argv_str_len av k Hva Hk) as Hslen.
  rewrite (mem_ok_agree _ Hm) by (rewrite word_add_nat; u_norm; lia).
  apply read_str_byte_f; assumption.
Qed.

Lemma read_str_m : forall mem, mem_ok mem -> forall k, (k < length av)%nat ->
  rdn source_segs mem (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k) (length (nth k av []))
  = Some (nth k av []).
Proof.
  intros mem Hm k Hk. pose proof rsp_lo_num.
  destruct (source_ptr_bounds k Hk) as [Hge Hup].
  rewrite (mem_ok_agree _ Hm) by lia. apply read_str_f. exact Hk.
Qed.

Lemma read_newline_m : forall mem, mem_ok mem ->
  rdn source_segs mem 0x12000 1%nat = Some [Z_to_bv 8 10].
Proof.
  intros mem Hm. pose proof rsp_lo_num.
  rewrite (mem_ok_agree _ Hm) by (imm_norm; lia).
  exact read_newline_f.
Qed.

Lemma read_slot_ra_m : forall mem, mem_ok mem ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 8)) 8%nat
  = Some (word_to_le_bytes 8 (0x111a0 : word)).
Proof.
  intros mem Hm. pose proof rsp_lo_num. pose proof rsp_hi_num.
  rewrite (mem_ok_agree _ Hm) by (u_norm; lia). exact read_slot_ra.
Qed.

Lemma read_slot_0_m : forall mem, mem_ok mem -> forall a : word,
  In a [Z_to_bv 64 (bv_unsigned rsp - 0x30); Z_to_bv 64 (bv_unsigned rsp - 0x28);
        Z_to_bv 64 (bv_unsigned rsp - 0x20); Z_to_bv 64 (bv_unsigned rsp - 0x18);
        Z_to_bv 64 (bv_unsigned rsp - 0x10)] ->
  rdn source_segs mem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros mem Hm a Ha. pose proof rsp_lo_num. pose proof rsp_hi_num.
  rewrite (mem_ok_agree _ Hm)
    by (repeat destruct Ha as [<-|Ha]; try (exfalso; exact Ha); u_norm; lia).
  apply read_slot_0. exact Ha.
Qed.

(** An 8-byte load at offset [m] inside argv string [k] never faults:
    peel this binary's frame overlay off down to [wmem = wrap_mem ...],
    then hand off to MuslStrlen's [argv_word_readable] (which is where
    the argument about the strings above the last argv NUL lives). *)
Lemma read_word_m : forall mem, mem_ok mem -> forall k m,
  (k < length av)%nat -> (m <= length (nth k av []))%nat ->
  exists bs, length bs = 8%nat /\
    rdn source_segs mem (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word m) 8%nat
    = Some bs.
Proof.
  intros mem Hmk k m Hk Hm.
  pose proof rsp_lo_num. pose proof rsp_hi_num.
  destruct (source_ptr_bounds k Hk) as [Hge Hup].
  pose proof (source_ptr_room k Hk) as Hroom.
  pose proof source_bsb_nw as Hnw.
  pose proof (u64_range (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)).
  assert (Hu : bv_unsigned (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word m)
               = (bv_unsigned (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k) + Z.of_nat m)%Z)
    by (rewrite word_add_nat; apply u_Z2bv; lia).
  destruct (argv_word_readable source_segs Sv48 inp rmb source_phdrs (0x11174 : word)
              rsp rbrk rrnd Hvl Hlau Hsp_lo Hsp_hi k m Hk Hm) as [bs [Hl Hr]].
  exists bs. split; [exact Hl|].
  rewrite (mem_ok_agree _ Hmk) by (rewrite Hu; solve [lia | left; lia]).
  rewrite rdn_fmem_above by (rewrite Hu; lia).
  exact Hr.
Qed.

(** Its bytes, as far as the NUL (MuslStrlen's [word_bytes_nth] fed with
    this binary's overlay-relative byte-read lemma). *)
Lemma read_word_nth : forall mem, mem_ok mem -> forall k m bs j,
  (k < length av)%nat ->
  rdn source_segs mem (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word m) 8%nat = Some bs ->
  (j < 8)%nat -> (m + j <= length (nth k av []))%nat ->
  nth j bs (Z_to_bv 8 0) = byte_at (nth k av []) (m + j).
Proof.
  intros mem Hmk k m bs j Hk Hr Hj Hmj.
  apply (word_bytes_nth source_segs mem (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k)
           (nth k av []) m bs j Hr);
    [ intros i Hi; apply read_str_byte_m; assumption
    | exact Hj | exact Hmj ].
Qed.

(* ================================================================= *)
(* Epilogue: 0x11140 (reload callee-saves) .. ret .. exit ecall       *)
(* ================================================================= *)

(** The frame-slot reads the epilogue's six [ld]s fall through to.
    All six arrive as [SCReadBase] obligations in one batch (in reverse
    execution order), and every one of them is one of the [read_slot_*_m]
    facts above, so a single dispatcher closes the batch. *)
(** The frame-slot reads the epilogue's six [ld]s fall through to.
    Every [SCReadBase] the block emits is one of the [read_slot_*] facts
    above, so one dispatcher closes the whole batch; the [lazymatch] is
    load-bearing, since letting [exact] try the wrong slot lemma makes
    unification unfold [rdn] over the segment image. *)
Ltac s_slot_rd :=
  eexists; split;
  [ lazymatch goal with
    | H : mem_ok ?m |- rdn _ _ (Z_to_bv 64 (_ - 8)) _ = _ =>
        exact (read_slot_ra_m m H)
    | H : mem_ok ?m |- _ =>
        apply (read_slot_0_m m H); cbn [In];
        first [ left; reflexivity | right; left; reflexivity
              | do 2 right; left; reflexivity | do 3 right; left; reflexivity
              | do 4 right; left; reflexivity | do 5 right; left; reflexivity
              | do 6 right; left; reflexivity ]
    end
  | vm_closed ].

Lemma source_epilogue : forall regs mem code,
  mem_ok mem ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ->
  reg_get regs 10 = code -> (bv_unsigned code < 256)%Z ->
  wexit1 source_segs (mkst regs 0x11140 mem rrom) [] code.
Proof.
  intros regs mem code Hmem H2 H10 Hc.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  sym_block source_segs 14%nat (@nil bool)
    [ELit 0x111a0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0]
    [((2 : reg), EVar 32)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x40)] (@nil word) RE HRE.
  1-6: s_slot_rd.
  { exact H2. }
  chain_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_111a4 eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRE. vm_closed.
  - sym_regs HRE. exact H10.
  - exact Hc.
Qed.

(* ================================================================= *)
(* musl write(): 0x111cc (wrapper) .. __syscall shuffle .. ecall ..   *)
(* __syscall_ret .. return to RA                                      *)
(* ================================================================= *)

(** Calling write(1, buf, len) from the wrapper entry: emits a nonempty
    prefix of the buffer, stores/reloads one scratch slot in
    [rsp-0x50, rsp-0x40), and returns to [RA] with a0 = the length
    actually delivered.  The environment chooses how much lands, so the
    continuation is quantified over that delivery [k], [1 <= k <= length
    buf]: it gets a0 = [len_word (firstn k buf)] and carries on down
    [to_wall_tail] with the undelivered [skipn k buf].  Every delivery
    is nonempty, so the return stays positive and musl's -errno branch
    in __syscall_ret is still dead.  Otherwise the continuation is
    quantified over the resulting register file and memory as before:
    only a0/a3..a7 change, and the memory stays [mem_ok]. *)
Lemma source_write_fn : forall (K : machine_state -> Prop) regs mem buf RA,
  mem_ok mem ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  reg_get regs 1 = RA ->
  v_jalr RA 0 = RA ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ->
  (1 <= bv_unsigned (reg_get regs 12%bv))%Z ->
  (bv_unsigned (reg_get regs 12%bv) <= 131072)%Z ->
  (bv_unsigned (reg_get regs 11%bv) + bv_unsigned (reg_get regs 12%bv) <= 2^64)%Z ->
  (* the range [vfs_write]'s [access_ok] accepts ([WallSim.to_wall]'s write node) *)
  (bv_unsigned (reg_get regs 11%bv) + bv_unsigned (reg_get regs 12%bv) <= TASK_SIZE)%Z ->
  ((bv_unsigned rsp - 0x30 <= bv_unsigned (reg_get regs 11%bv))%Z \/
   (bv_unsigned (reg_get regs 11%bv) + bv_unsigned (reg_get regs 12%bv) <= bv_unsigned rsp - 0x50)%Z) ->
  rdn source_segs fmem (reg_get regs 11) (word_to_nat (reg_get regs 12)) = Some buf ->
  (forall regs' mem' k, (1 <= k)%nat -> (k <= length buf)%nat ->
     mem_ok mem' ->
     (forall (a : word) (n : nat),
        (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
        ((bv_unsigned rsp - 0x40 <= bv_unsigned a)%Z \/
         (bv_unsigned a + Z.of_nat n <= bv_unsigned rsp - 0x50)%Z) ->
        rdn source_segs mem' a n = rdn source_segs mem a n) ->
     (forall r : reg, r <> 10 -> r <> 13 -> r <> 14 -> r <> 15 -> r <> 16 ->
        r <> 17 -> reg_get regs' r = reg_get regs r) ->
     reg_get regs' 10 = len_word (firstn k buf) ->
     to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs' RA mem' rrom)
       (skipn k buf) K) ->
  to_wall_tail source_segs (Z_to_bv 64 1) (mkst regs 0x111cc mem rrom) buf K.
Proof.
  intros K regs mem buf RA Hmem H10 H1 Hvj H2 H12lo H12 Hnov Htask Hdisj Hbuf Hcont.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  pose proof (rdn_length _ _ _ _ _ Hbuf) as Hbl.
  pose proof (u64_range (reg_get regs 12)) as H12r.
  assert (HbufL : Z.of_nat (length buf) = bv_unsigned (reg_get regs 12))
    by (rewrite Hbl; unfold word_to_nat; rewrite Z2Nat.id by lia; reflexivity).
  (* 0x111cc: sp -= 16 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 (bv_unsigned rsp - 0x50));
      [ exact SF_111cc | reflexivity | exact SD_111cc | reflexivity
      | getr_resolve; rewrite H2; sp_norm; f_equal; lia ]
    | norm_pc ].
  (* 0x111d0: a3 := a2 (= len) *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := reg_get regs 12);
      [ exact SF_111d0 | reflexivity | exact SD_111d0 | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* 0x111d4: a6 := 0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_111d4 | reflexivity | exact SD_111d4 | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* 0x111d8: a2 := a1 (= buf) *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := reg_get regs 11);
      [ exact SF_111d8 | reflexivity | exact SD_111d8 | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* 0x111dc: a5 := 0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_111dc | reflexivity | exact SD_111dc | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* 0x111e0: a1 := a0 (= 1) *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 1);
      [ exact SF_111e0 | reflexivity | exact SD_111e0 | reflexivity
      | getr_resolve; rewrite H10; apply v_addi_0 ]
    | norm_pc ].
  (* 0x111e4: a4 := 0 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_111e4 | reflexivity | exact SD_111e4 | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* 0x111e8: a0 := 64 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 64);
      [ exact SF_111e8 | reflexivity | exact SD_111e8 | reflexivity
      | getr_resolve; exact v_addi_0_64 ]
    | norm_pc ].
  (* 0x111ec: sd ra, 8(sp) *)
  chain_step;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned rsp - 0x48)) (v := RA);
      [ exact SF_111ec | reflexivity | exact SD_111ec
      | getr_resolve; sp_norm; f_equal; lia
      | getr_resolve; exact H1
      | solve_store_ok_inv ]
    | step_simpl ].
  (* 0x111f0: jal 0x1125c *)
  chain_step;
    [ reflexivity
    | eapply step_jal_link;
      [ exact SF_111f0 | reflexivity | exact SD_111f0 ]
    | step_simpl ].
  (* 0x1125c: j 0x11238 *)
  stepj SF_1125c SD_1125c.
  (* 0x11238..0x11250: shuffle args into the syscall registers *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 64);
      [ exact SF_11238 | reflexivity | exact SD_11238 | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | norm_pc ].
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 1);
      [ exact SF_1123c | reflexivity | exact SD_1123c | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | norm_pc ].
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := reg_get regs 11);
      [ exact SF_11240 | reflexivity | exact SD_11240 | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | norm_pc ].
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := reg_get regs 12);
      [ exact SF_11244 | reflexivity | exact SD_11244 | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | norm_pc ].
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11248 | reflexivity | exact SD_11248 | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | norm_pc ].
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_1124c | reflexivity | exact SD_1124c | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | norm_pc ].
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 0);
      [ exact SF_11250 | reflexivity | exact SD_11250 | reflexivity
      | getr_resolve; apply v_addi_0 ]
    | norm_pc ].
  (* 0x11254: ecall — the write syscall *)
  chain_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_11254 eq_refl) | ].
  apply twt_more; [lia|].
  apply (twl_write_rec source_segs (Z_to_bv 64 1)).
  - getr_resolve. vm_compute. reflexivity.
  - regupd_resolve. reflexivity.
  - (* the state's rom is the run's; the buffer read is the image's *)
    rewrite (ms_read_bytes_rdn (run_segments source_segs inp rsp rmb)) by reflexivity.
    unfold run_segments. apply rdn_lift.
    cbn [ms_mem ms_regs]. regupd_resolve.
    assert (Hm1 : mem_ok (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 0x48))
                            (word_to_le_bytes 8 RA)))
      by (apply mem_ok_scratch8; [exact Hmem | u_norm; lia | u_norm; lia]).
    rewrite (mem_ok_agree _ Hm1) by (rewrite ?of_nat_word_to_nat; lia).
    exact Hbuf.
  - regupd_resolve. apply Uaccess.access_okb_intro. exact Htask.
  - lia.
  - (* per delivered length: the wrapper's return path *)
    intros k Hk1 Hk2.
    norm_pc.
    chain_step;
      [ reflexivity
      | eapply step_jalr_x0 with (tgt := (0x111f4 : word));
        [ exact SF_11258 | reflexivity | exact SD_11258
        | getr_resolve; regupd_resolve; bveq ]
      | norm_pc ].
    (* 0x111f4: ld ra, 8(sp) *)
    chain_step;
      [ reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 RA) (v := RA);
        [ exact SF_111f4 | reflexivity | exact SD_111f4
        | match goal with |- rdn _ _ ?a _ = _ =>
            replace a with (Z_to_bv 64 (bv_unsigned rsp - 0x48))
              by (getr_resolve; regupd_resolve; sp_norm; f_equal; lia) end;
          apply rdn_wbytes_hit8; u_norm; lia
        | exact (bytes_le_to_Z_8 _) ]
      | step_simpl ].
    (* 0x111f8: sp += 16 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 (bv_unsigned rsp - 0x40));
        [ exact SF_111f8 | reflexivity | exact SD_111f8 | reflexivity
        | getr_resolve; regupd_resolve; sp_norm; f_equal; lia ]
      | norm_pc ].
    (* 0x111fc: j 0x11200 (__syscall_ret) *)
    stepj SF_111fc SD_111fc.
    (* 0x11200: lui a5, 0xfffff  (__syscall_ret; gcc 15 has a frameless
       success path -- the errno fixup lives in a cold tail) *)
    stepi SF_11200 SD_11200.
    (* 0x11204: bltu a5, a0 falls through (len << 2^64 - 4096) *)
    chain_step;
      [ reflexivity
      | eapply step_bltu_ft;
        [ exact SF_11204 | reflexivity | exact SD_11204
        | getr_resolve; regupd_resolve;
          rewrite c_ltu_ltb; apply Z.ltb_ge;
          match goal with |- context [bv_unsigned (v_lui ?z)] =>
            assert (Hlui : bv_unsigned (v_lui z) = 18446744073709547520%Z)
              by (vm_compute; reflexivity)
          end;
          rewrite Hlui; rewrite u_len_word_firstn by lia; lia ]
      | norm_pc ].
    (* 0x11208: ret to RA *)
    chain_step;
      [ reflexivity
      | eapply step_jalr_x0 with (tgt := RA);
        [ exact SF_11208 | reflexivity | exact SD_11208
        | getr_resolve; reflexivity ]
      | ].
    imm_norm. rewrite Hvj.
    apply (Hcont _ _ k Hk1 Hk2).
    + apply mem_ok_scratch8; [exact Hmem | u_norm; lia | u_norm; lia].
    + intros a n Hn Hd. destruct Hd as [Hd | Hd].
      * rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia). reflexivity.
      * rewrite rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes; u_norm; lia). reflexivity.
    + intros r Hx10 Hx13 Hx14 Hx15 Hx16 Hx17.
      destruct (decide (r = 1)) as [->|Hx1];
        [regupd_resolve; symmetry; exact H1|].
      destruct (decide (r = 2)) as [->|Hx2];
        [regupd_resolve; symmetry; exact H2|].
      destruct (decide (r = 11)) as [->|Hx11];
        [regupd_resolve; reflexivity|].
      destruct (decide (r = 12)) as [->|Hx12];
        [regupd_resolve; reflexivity|].
      repeat (rewrite regupd_other by assumption). reflexivity.
    + regupd_resolve. reflexivity.
Qed.

(* ================================================================= *)
(* The inline byte-scan loops                                        *)
(*                                                                    *)
(* -fno-builtin keeps gcc from turning the source's [slen] loops into  *)
(* calls to musl's word-at-a-time strlen, so strlen is gone from the   *)
(* image and main scans bytes directly.  It carries three copies of    *)
(* the loop:                                                          *)
(*                                                                    *)
(*   0x11058  a4 := strlen(argv[i])   (a1 = &argv[i], scratch a5)      *)
(*   0x11068  a2 := strlen(argv[1])   (s3 = &argv[1], scratch a5)      *)
(*   0x110dc  a2 := strlen(argv[i])   (recomputed as the write length  *)
(*            of a matched argument; a2 enters 0 from both the match   *)
(*            and the empty-pattern path)                              *)
(* ================================================================= *)

(** The hay scan 0x11058 (a4 := strlen(argv[k])), from offset [j]. *)
Lemma source_slen_hay : forall k, (k < length av)%nat ->
  forall mem, mem_ok mem ->
  forall d j regs,
  (j + d = length (nth k av []))%nat ->
  reg_get regs 11 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k ->
  reg_get regs 14 = nat_to_word j ->
  exists regs',
    (forall r : reg, r <> 14 -> r <> 15 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 14 = nat_to_word (length (nth k av [])) /\
    msteps source_segs (mkst regs 0x11058 mem rrom) (mkst regs' 0x11064 mem rrom).
Proof.
  intros k Hk mem Hmem.
  pose proof (source_ptr_bounds k Hk) as [Hge Hup].
  pose proof (valid_argv_str_len av k Hva Hk) as Hslen.
  pose proof (valid_argv_str_nz av k Hva Hk) as Hsnz.
  set (ptr := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k) in *.
  set (s := nth k av []) in *.
  induction d as [|d IH]; intros j regs Hjd Hr11 Hr14.
  - (* j = length s: the byte is the NUL, fall through to 0x11064 *)
    assert (Hj : j = length s) by lia.
    set (regs1 := regupd regs 15 (ptr + nat_to_word j)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11058 mem rrom)
                 = MachineOk (mkst regs1 0x1105c mem rrom)).
    { rewrite (step_add source_segs regs 0x11058 mem rrom _ 15 11 14
                 SF_11058 eq_refl SD_11058).
      reduce_bv_eqb_ifs. unfold regs1. getr_resolve. rewrite Hr11, Hr14.
      wlits. reflexivity. }
    set (regs2 := regupd regs1 15 (Z_to_bv 64 0)).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x1105c mem rrom)
                 = MachineOk (mkst regs2 0x11060 mem rrom)).
    { rewrite (step_lbu source_segs regs1 0x1105c mem rrom _ 15 15 _ (Z_to_bv 8 0)
                 SF_1105c eq_refl SD_1105c).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite ?regupd_same, v_addi_0.
        pose proof (read_str_byte_m mem Hmem k j Hk ltac:(unfold s in Hjd; lia)) as Hrd.
        assert (Hb0 : byte_at (nth k av []) j = Z_to_bv 8 0)
          by (unfold s in Hj; rewrite Hj; apply byte_at_len).
        rewrite Hb0 in Hrd. exact Hrd. }
    assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x11060 mem rrom)
                 = MachineOk (mkst regs2 0x11064 mem rrom)).
    { rewrite (step_bne_ft source_segs regs2 0x11060 mem rrom _ 15 0 _
                 SF_11060 eq_refl SD_11060).
      - wlits. reflexivity.
      - unfold regs2. getr_resolve. exact c_eq_0_true. }
    exists regs2. split; [|split].
    + intros r Hx14 Hx15. unfold regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs2, regs1. regupd_resolve. rewrite Hr14.
      unfold s in Hj. rewrite Hj. reflexivity.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      apply mst_refl.
  - (* j < length s: the byte is nonzero, bump a4 and loop *)
    assert (Hjlt : (j < length s)%nat) by lia.
    set (b := byte_at s j).
    assert (Hbnz : b <> Z_to_bv 8 0)
      by (apply byte_at_nz; [exact Hsnz | exact Hjlt]).
    set (regs1 := regupd regs 15 (ptr + nat_to_word j)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11058 mem rrom)
                 = MachineOk (mkst regs1 0x1105c mem rrom)).
    { rewrite (step_add source_segs regs 0x11058 mem rrom _ 15 11 14
                 SF_11058 eq_refl SD_11058).
      reduce_bv_eqb_ifs. unfold regs1. getr_resolve. rewrite Hr11, Hr14.
      wlits. reflexivity. }
    set (regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned b))).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x1105c mem rrom)
                 = MachineOk (mkst regs2 0x11060 mem rrom)).
    { rewrite (step_lbu source_segs regs1 0x1105c mem rrom _ 15 15 _ b
                 SF_1105c eq_refl SD_1105c).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite ?regupd_same, v_addi_0.
        unfold b, ptr, s. apply (read_str_byte_m mem Hmem);
          [exact Hk | unfold s in Hjlt; lia]. }
    assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x11060 mem rrom)
                 = MachineOk (mkst regs2 0x11088 mem rrom)).
    { rewrite (step_bne_tk source_segs regs2 0x11060 mem rrom _ 15 0 _
                 SF_11060 eq_refl SD_11060).
      - wlits. reflexivity.
      - unfold regs2. getr_resolve.
        apply c_eq_0_false. rewrite u_zext8. apply byte_nz_u. exact Hbnz. }
    set (regs3 := regupd regs2 14 (nat_to_word (S j))).
    assert (E4 : RiscvSemantics.step source_segs (mkst regs2 0x11088 mem rrom)
                 = MachineOk (mkst regs3 0x1108c mem rrom)).
    { rewrite (step_addi source_segs regs2 0x11088 mem rrom _ 14 14 _
                 SF_11088 eq_refl SD_11088).
      reduce_bv_eqb_ifs.
      unfold regs3, regs2, regs1. getr_resolve. rewrite Hr14.
      rewrite v_addi_Sj by lia. wlits. reflexivity. }
    assert (E5 : RiscvSemantics.step source_segs (mkst regs3 0x1108c mem rrom)
                 = MachineOk (mkst regs3 0x11058 mem rrom)).
    { rewrite (step_jal_x0 source_segs regs3 0x1108c mem rrom _ _
                 SF_1108c eq_refl SD_1108c).
      wlits. reflexivity. }
    assert (Hr11' : reg_get regs3 11 = ptr)
      by (unfold regs3, regs2, regs1; regupd_resolve; exact Hr11).
    assert (Hr14' : reg_get regs3 14 = nat_to_word (S j))
      by (unfold regs3; apply regupd_same).
    destruct (IH (S j) regs3 ltac:(lia) Hr11' Hr14') as [regs' [Hag [H14 Hms]]].
    exists regs'. split; [|split].
    + intros r Hx14 Hx15. rewrite (Hag r Hx14 Hx15).
      unfold regs3, regs2, regs1. rewrite !regupd_other by assumption.
      reflexivity.
    + exact H14.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      exact Hms.
Qed.

(** The pattern scan 0x11068 (a2 := strlen(argv[1])), from offset [j]. *)
Lemma source_slen_pat : (2 <= length av)%nat ->
  forall mem, mem_ok mem ->
  forall d j regs,
  (j + d = length (nth 1 av []))%nat ->
  reg_get regs 19 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1 ->
  reg_get regs 12 = nat_to_word j ->
  exists regs',
    (forall r : reg, r <> 12 -> r <> 15 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 12 = nat_to_word (length (nth 1 av [])) /\
    msteps source_segs (mkst regs 0x11068 mem rrom) (mkst regs' 0x11074 mem rrom).
Proof.
  intros H2le mem Hmem.
  pose proof (source_ptr_bounds 1 ltac:(lia)) as [Hge Hup].
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as Hslen.
  pose proof (valid_argv_str_nz av 1 Hva ltac:(lia)) as Hsnz.
  set (ptr := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1) in *.
  set (s := nth 1 av []) in *.
  induction d as [|d IH]; intros j regs Hjd Hr19 Hr12.
  - (* j = length s: the byte is the NUL, fall through to 0x11074 *)
    assert (Hj : j = length s) by lia.
    set (regs1 := regupd regs 15 (ptr + nat_to_word j)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11068 mem rrom)
                 = MachineOk (mkst regs1 0x1106c mem rrom)).
    { rewrite (step_add source_segs regs 0x11068 mem rrom _ 15 19 12
                 SF_11068 eq_refl SD_11068).
      reduce_bv_eqb_ifs. unfold regs1. getr_resolve. rewrite Hr19, Hr12.
      wlits. reflexivity. }
    set (regs2 := regupd regs1 15 (Z_to_bv 64 0)).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x1106c mem rrom)
                 = MachineOk (mkst regs2 0x11070 mem rrom)).
    { rewrite (step_lbu source_segs regs1 0x1106c mem rrom _ 15 15 _ (Z_to_bv 8 0)
                 SF_1106c eq_refl SD_1106c).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite ?regupd_same, v_addi_0.
        pose proof (read_str_byte_m mem Hmem 1 j ltac:(lia)
                      ltac:(unfold s in Hjd; lia)) as Hrd.
        assert (Hb0 : byte_at (nth 1 av []) j = Z_to_bv 8 0)
          by (unfold s in Hj; rewrite Hj; apply byte_at_len).
        rewrite Hb0 in Hrd. exact Hrd. }
    assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x11070 mem rrom)
                 = MachineOk (mkst regs2 0x11074 mem rrom)).
    { rewrite (step_bne_ft source_segs regs2 0x11070 mem rrom _ 15 0 _
                 SF_11070 eq_refl SD_11070).
      - wlits. reflexivity.
      - unfold regs2. getr_resolve. exact c_eq_0_true. }
    exists regs2. split; [|split].
    + intros r Hx12 Hx15. unfold regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs2, regs1. regupd_resolve. rewrite Hr12.
      unfold s in Hj. rewrite Hj. reflexivity.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      apply mst_refl.
  - (* j < length s: the byte is nonzero, bump a2 and loop *)
    assert (Hjlt : (j < length s)%nat) by lia.
    set (b := byte_at s j).
    assert (Hbnz : b <> Z_to_bv 8 0)
      by (apply byte_at_nz; [exact Hsnz | exact Hjlt]).
    set (regs1 := regupd regs 15 (ptr + nat_to_word j)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11068 mem rrom)
                 = MachineOk (mkst regs1 0x1106c mem rrom)).
    { rewrite (step_add source_segs regs 0x11068 mem rrom _ 15 19 12
                 SF_11068 eq_refl SD_11068).
      reduce_bv_eqb_ifs. unfold regs1. getr_resolve. rewrite Hr19, Hr12.
      wlits. reflexivity. }
    set (regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned b))).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x1106c mem rrom)
                 = MachineOk (mkst regs2 0x11070 mem rrom)).
    { rewrite (step_lbu source_segs regs1 0x1106c mem rrom _ 15 15 _ b
                 SF_1106c eq_refl SD_1106c).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite ?regupd_same, v_addi_0.
        unfold b, ptr, s. apply (read_str_byte_m mem Hmem);
          [lia | unfold s in Hjlt; lia]. }
    assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x11070 mem rrom)
                 = MachineOk (mkst regs2 0x11090 mem rrom)).
    { rewrite (step_bne_tk source_segs regs2 0x11070 mem rrom _ 15 0 _
                 SF_11070 eq_refl SD_11070).
      - wlits. reflexivity.
      - unfold regs2. getr_resolve.
        apply c_eq_0_false. rewrite u_zext8. apply byte_nz_u. exact Hbnz. }
    set (regs3 := regupd regs2 12 (nat_to_word (S j))).
    assert (E4 : RiscvSemantics.step source_segs (mkst regs2 0x11090 mem rrom)
                 = MachineOk (mkst regs3 0x11094 mem rrom)).
    { rewrite (step_addi source_segs regs2 0x11090 mem rrom _ 12 12 _
                 SF_11090 eq_refl SD_11090).
      reduce_bv_eqb_ifs.
      unfold regs3, regs2, regs1. getr_resolve. rewrite Hr12.
      rewrite v_addi_Sj by lia. wlits. reflexivity. }
    assert (E5 : RiscvSemantics.step source_segs (mkst regs3 0x11094 mem rrom)
                 = MachineOk (mkst regs3 0x11068 mem rrom)).
    { rewrite (step_jal_x0 source_segs regs3 0x11094 mem rrom _ _
                 SF_11094 eq_refl SD_11094).
      wlits. reflexivity. }
    assert (Hr19' : reg_get regs3 19 = ptr)
      by (unfold regs3, regs2, regs1; regupd_resolve; exact Hr19).
    assert (Hr12' : reg_get regs3 12 = nat_to_word (S j))
      by (unfold regs3; apply regupd_same).
    destruct (IH (S j) regs3 ltac:(lia) Hr19' Hr12') as [regs' [Hag [H12 Hms]]].
    exists regs'. split; [|split].
    + intros r Hx12 Hx15. rewrite (Hag r Hx12 Hx15).
      unfold regs3, regs2, regs1. rewrite !regupd_other by assumption.
      reflexivity.
    + exact H12.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      exact Hms.
Qed.

(** The write-length recompute 0x110dc (a2 := strlen(argv[k])), from
    offset [j].  Same loop, laid out backwards: the increment at 0x110d8
    sits BEFORE the loop head, and the [bne] jumps back up to it. *)
Lemma source_slen_out : forall k, (k < length av)%nat ->
  forall mem, mem_ok mem ->
  forall d j regs,
  (j + d = length (nth k av []))%nat ->
  reg_get regs 11 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k ->
  reg_get regs 12 = nat_to_word j ->
  exists regs',
    (forall r : reg, r <> 12 -> r <> 15 -> reg_get regs' r = reg_get regs r) /\
    reg_get regs' 12 = nat_to_word (length (nth k av [])) /\
    msteps source_segs (mkst regs 0x110dc mem rrom) (mkst regs' 0x110e8 mem rrom).
Proof.
  intros k Hk mem Hmem.
  pose proof (source_ptr_bounds k Hk) as [Hge Hup].
  pose proof (valid_argv_str_len av k Hva Hk) as Hslen.
  pose proof (valid_argv_str_nz av k Hva Hk) as Hsnz.
  set (ptr := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k) in *.
  set (s := nth k av []) in *.
  induction d as [|d IH]; intros j regs Hjd Hr11 Hr12.
  - (* j = length s: the byte is the NUL, fall through to 0x110e8 *)
    assert (Hj : j = length s) by lia.
    set (regs1 := regupd regs 15 (ptr + nat_to_word j)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x110dc mem rrom)
                 = MachineOk (mkst regs1 0x110e0 mem rrom)).
    { rewrite (step_add source_segs regs 0x110dc mem rrom _ 15 11 12
                 SF_110dc eq_refl SD_110dc).
      reduce_bv_eqb_ifs. unfold regs1. getr_resolve. rewrite Hr11, Hr12.
      wlits. reflexivity. }
    set (regs2 := regupd regs1 15 (Z_to_bv 64 0)).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x110e0 mem rrom)
                 = MachineOk (mkst regs2 0x110e4 mem rrom)).
    { rewrite (step_lbu source_segs regs1 0x110e0 mem rrom _ 15 15 _ (Z_to_bv 8 0)
                 SF_110e0 eq_refl SD_110e0).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite ?regupd_same, v_addi_0.
        pose proof (read_str_byte_m mem Hmem k j Hk ltac:(unfold s in Hjd; lia)) as Hrd.
        assert (Hb0 : byte_at (nth k av []) j = Z_to_bv 8 0)
          by (unfold s in Hj; rewrite Hj; apply byte_at_len).
        rewrite Hb0 in Hrd. exact Hrd. }
    assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x110e4 mem rrom)
                 = MachineOk (mkst regs2 0x110e8 mem rrom)).
    { rewrite (step_bne_ft source_segs regs2 0x110e4 mem rrom _ 15 0 _
                 SF_110e4 eq_refl SD_110e4).
      - wlits. reflexivity.
      - unfold regs2. getr_resolve. exact c_eq_0_true. }
    exists regs2. split; [|split].
    + intros r Hx12 Hx15. unfold regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + unfold regs2, regs1. regupd_resolve. rewrite Hr12.
      unfold s in Hj. rewrite Hj. reflexivity.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      apply mst_refl.
  - (* j < length s: the byte is nonzero, bump a2 and loop *)
    assert (Hjlt : (j < length s)%nat) by lia.
    set (b := byte_at s j).
    assert (Hbnz : b <> Z_to_bv 8 0)
      by (apply byte_at_nz; [exact Hsnz | exact Hjlt]).
    set (regs1 := regupd regs 15 (ptr + nat_to_word j)).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x110dc mem rrom)
                 = MachineOk (mkst regs1 0x110e0 mem rrom)).
    { rewrite (step_add source_segs regs 0x110dc mem rrom _ 15 11 12
                 SF_110dc eq_refl SD_110dc).
      reduce_bv_eqb_ifs. unfold regs1. getr_resolve. rewrite Hr11, Hr12.
      wlits. reflexivity. }
    set (regs2 := regupd regs1 15 (Z_to_bv 64 (bv_unsigned b))).
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x110e0 mem rrom)
                 = MachineOk (mkst regs2 0x110e4 mem rrom)).
    { rewrite (step_lbu source_segs regs1 0x110e0 mem rrom _ 15 15 _ b
                 SF_110e0 eq_refl SD_110e0).
      - reduce_bv_eqb_ifs. wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite ?regupd_same, v_addi_0.
        unfold b, ptr, s. apply (read_str_byte_m mem Hmem);
          [exact Hk | unfold s in Hjlt; lia]. }
    assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x110e4 mem rrom)
                 = MachineOk (mkst regs2 0x110d8 mem rrom)).
    { rewrite (step_bne_tk source_segs regs2 0x110e4 mem rrom _ 15 0 _
                 SF_110e4 eq_refl SD_110e4).
      - wlits. reflexivity.
      - unfold regs2. getr_resolve.
        apply c_eq_0_false. rewrite u_zext8. apply byte_nz_u. exact Hbnz. }
    set (regs3 := regupd regs2 12 (nat_to_word (S j))).
    assert (E4 : RiscvSemantics.step source_segs (mkst regs2 0x110d8 mem rrom)
                 = MachineOk (mkst regs3 0x110dc mem rrom)).
    { rewrite (step_addi source_segs regs2 0x110d8 mem rrom _ 12 12 _
                 SF_110d8 eq_refl SD_110d8).
      reduce_bv_eqb_ifs.
      unfold regs3, regs2, regs1. getr_resolve. rewrite Hr12.
      rewrite v_addi_Sj by lia. wlits. reflexivity. }
    assert (Hr11' : reg_get regs3 11 = ptr)
      by (unfold regs3, regs2, regs1; regupd_resolve; exact Hr11).
    assert (Hr12' : reg_get regs3 12 = nat_to_word (S j))
      by (unfold regs3; apply regupd_same).
    destruct (IH (S j) regs3 ltac:(lia) Hr11' Hr12') as [regs' [Hag [H12 Hms]]].
    exists regs'. split; [|split].
    + intros r Hx12 Hx15. rewrite (Hag r Hx12 Hx15).
      unfold regs3, regs2, regs1. rewrite !regupd_other by assumption.
      reflexivity.
    + exact H12.
    + eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      exact Hms.
Qed.

(* ================================================================= *)
(* Inner byte-compare loop vs [prefix_eqb]                            *)
(* ================================================================= *)

(** From the compare head 0x110b0 with a5 = j, a7 = &hay[i], s3 = &pat,
    a2 = nn, the loop compares pat[j..) against hay[i+j..).  If the
    whole remaining pattern matches it exits to 0x110dc with a2 := 0
    (through the [li a2,0; j 110dc] pair at 0x110a0); at the first
    mismatch it exits to 0x110c8 (bump the scan index) with a2 kept.
    Clobbers a0, a2, a5, a6. *)
Lemma source_cmp : forall k, (k < length av)%nat -> (2 <= length av)%nat ->
  forall mem, mem_ok mem ->
  forall i d j regs,
  (j + d = length (nth 1 av []))%nat -> (1 <= d)%nat ->
  (i + length (nth 1 av []) <= length (nth k av []))%nat ->
  reg_get regs 15 = nat_to_word j ->
  reg_get regs 17 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word i ->
  reg_get regs 19 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1 ->
  reg_get regs 12 = nat_to_word (length (nth 1 av [])) ->
  exists regs',
    (forall r : reg, r <> 10 -> r <> 12 -> r <> 15 -> r <> 16 ->
       reg_get regs' r = reg_get regs r) /\
    reg_get regs' 12 = (if prefix_eqb (skipn j (nth 1 av [])) (nth k av []) (i + j)
                        then nat_to_word 0
                        else nat_to_word (length (nth 1 av []))) /\
    msteps source_segs (mkst regs 0x110b0 mem rrom)
      (mkst regs'
        (if prefix_eqb (skipn j (nth 1 av [])) (nth k av []) (i + j)
         then 0x110dc else 0x110c8)
        mem rrom).
Proof.
  intros k Hk H2le mem Hmem.
  pose proof (source_ptr_bounds k Hk) as [Hgeh Hlth].
  pose proof (source_ptr_bounds 1 ltac:(lia)) as [Hgep Hltp].
  pose proof (valid_argv_str_len av k Hva Hk) as Hhlen.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as Hplen.
  set (hay := nth k av []) in *.
  set (pat := nth 1 av []) in *.
  set (hp := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k) in *.
  set (pp := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1) in *.
  intros i d. revert i.
  induction d as [|d IH]; intros i j regs Hjd Hd Hin Hr15 Hr17 Hr19 Hr12;
    [lia|].
  assert (Hjlt : (j < length pat)%nat) by lia.
  assert (HijN : (i + j < length hay)%nat) by lia.
  set (bh := byte_at hay (i + j)).
  set (bp := byte_at pat j).
  (* a6 := a7 + a5 = &hay[i+j] *)
  set (regs1 := regupd regs 16 (hp + nat_to_word (i + j))).
  assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x110b0 mem rrom)
               = MachineOk (mkst regs1 0x110b4 mem rrom)).
  { rewrite (step_add source_segs regs 0x110b0 mem rrom _ 16 17 15
               SF_110b0 eq_refl SD_110b0).
    reduce_bv_eqb_ifs.
    getr_resolve. rewrite Hr17, Hr15.
    rewrite v_add_ntw_merge. wlits. reflexivity. }
  (* a0 := s3 + a5 = &pat[j] *)
  set (regs2 := regupd regs1 10 (pp + nat_to_word j)).
  assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x110b4 mem rrom)
               = MachineOk (mkst regs2 0x110b8 mem rrom)).
  { rewrite (step_add source_segs regs1 0x110b4 mem rrom _ 10 19 15
               SF_110b4 eq_refl SD_110b4).
    reduce_bv_eqb_ifs.
    unfold regs2, regs1. getr_resolve. rewrite Hr19, Hr15.
    wlits. reflexivity. }
  (* a6 := hay[i+j] *)
  set (regs3 := regupd regs2 16 (Z_to_bv 64 (bv_unsigned bh))).
  assert (E3 : RiscvSemantics.step source_segs (mkst regs2 0x110b8 mem rrom)
               = MachineOk (mkst regs3 0x110bc mem rrom)).
  { rewrite (step_lbu source_segs regs2 0x110b8 mem rrom _ 16 16 _ bh
               SF_110b8 eq_refl SD_110b8).
    - reduce_bv_eqb_ifs. wlits. reflexivity.
    - unfold regs2, regs1. getr_resolve.
      rewrite v_addi_0.
      unfold bh, hay, hp. apply (read_str_byte_m mem Hmem);
        [exact Hk | unfold hay in HijN; lia]. }
  (* a0 := pat[j] *)
  set (regs4 := regupd regs3 10 (Z_to_bv 64 (bv_unsigned bp))).
  assert (E4 : RiscvSemantics.step source_segs (mkst regs3 0x110bc mem rrom)
               = MachineOk (mkst regs4 0x110c0 mem rrom)).
  { rewrite (step_lbu source_segs regs3 0x110bc mem rrom _ 10 10 _ bp
               SF_110bc eq_refl SD_110bc).
    - reduce_bv_eqb_ifs. wlits. reflexivity.
    - unfold regs3, regs2. getr_resolve.
      rewrite v_addi_0.
      unfold bp, pat, pp. apply (read_str_byte_m mem Hmem);
        [lia | unfold pat in Hjlt; lia]. }
  assert (Hspec : prefix_eqb (skipn j pat) hay (i + j)
                  = (bv_eqb bh bp && prefix_eqb (skipn (S j) pat) hay (S (i + j)))%bool).
  { rewrite (skipn_nth pat j (Z_to_bv 8 0) Hjlt). cbn [prefix_eqb].
    rewrite <- (nth_lt_byte_at pat j Hjlt).
    reflexivity. }
  destruct (bv_eqb bh bp) eqn:Heqb.
  - (* bytes equal: branch to 0x11098, a5 += 1, test j+1 = nn *)
    assert (E5 : RiscvSemantics.step source_segs (mkst regs4 0x110c0 mem rrom)
                 = MachineOk (mkst regs4 0x11098 mem rrom)).
    { rewrite (step_beq_tk source_segs regs4 0x110c0 mem rrom _ 16 10 _
                 SF_110c0 eq_refl SD_110c0).
      - wlits. reflexivity.
      - unfold regs4, regs3. getr_resolve.
        rewrite c_eq_small, bv_eqb_zext. exact Heqb. }
    set (regs5 := regupd regs4 15 (nat_to_word (S j))).
    assert (E6 : RiscvSemantics.step source_segs (mkst regs4 0x11098 mem rrom)
                 = MachineOk (mkst regs5 0x1109c mem rrom)).
    { rewrite (step_addi source_segs regs4 0x11098 mem rrom _ 15 15 _
                 SF_11098 eq_refl SD_11098).
      reduce_bv_eqb_ifs.
      unfold regs5, regs4, regs3, regs2, regs1.
      getr_resolve. rewrite Hr15.
      rewrite v_addi_Sj by lia. wlits. reflexivity. }
    destruct (Nat.eq_dec (S j) (length pat)) as [HSj | HSj].
    + (* whole pattern compared: bne falls through -> a2 := 0 -> 0x110dc *)
      assert (E7 : RiscvSemantics.step source_segs (mkst regs5 0x1109c mem rrom)
                   = MachineOk (mkst regs5 0x110a0 mem rrom)).
      { rewrite (step_bne_ft source_segs regs5 0x1109c mem rrom _ 15 12 _
                   SF_1109c eq_refl SD_1109c).
        - wlits. reflexivity.
        - unfold regs5, regs4, regs3, regs2, regs1.
          getr_resolve. rewrite Hr12, HSj.
          rewrite c_eq_small. apply bv_eqb_refl. }
      set (regs6 := regupd regs5 12 (nat_to_word 0)).
      assert (E8 : RiscvSemantics.step source_segs (mkst regs5 0x110a0 mem rrom)
                   = MachineOk (mkst regs6 0x110a4 mem rrom)).
      { rewrite (step_addi source_segs regs5 0x110a0 mem rrom _ 12 0 _
                   SF_110a0 eq_refl SD_110a0).
        reduce_bv_eqb_ifs. getr_resolve.
        replace (v_addi (Z_to_bv 64 0) (bv_signed (0%bv : bv 12)))
          with (nat_to_word 0) by bveq.
        wlits. reflexivity. }
      assert (E9 : RiscvSemantics.step source_segs (mkst regs6 0x110a4 mem rrom)
                   = MachineOk (mkst regs6 0x110dc mem rrom)).
      { rewrite (step_jal_x0 source_segs regs6 0x110a4 mem rrom _ _
                   SF_110a4 eq_refl SD_110a4).
        wlits. reflexivity. }
      exists regs6. split; [|split].
      * intros r H10 H12 H15 H16.
        unfold regs6, regs5, regs4, regs3, regs2, regs1.
        rewrite !regupd_other by assumption. reflexivity.
      * rewrite Hspec, ?Heqb.
        replace (skipn (S j) pat) with (@nil byte)
          by (symmetry; apply skipn_all2; lia).
        cbn [prefix_eqb andb].
        unfold regs6. apply regupd_same.
      * rewrite Hspec, ?Heqb.
        replace (skipn (S j) pat) with (@nil byte)
          by (symmetry; apply skipn_all2; lia).
        cbn [prefix_eqb andb].
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
    + (* more pattern bytes remain: bne taken, loop *)
      assert (E7 : RiscvSemantics.step source_segs (mkst regs5 0x1109c mem rrom)
                   = MachineOk (mkst regs5 0x110b0 mem rrom)).
      { rewrite (step_bne_tk source_segs regs5 0x1109c mem rrom _ 15 12 _
                   SF_1109c eq_refl SD_1109c).
        - wlits. reflexivity.
        - unfold regs5, regs4, regs3, regs2, regs1.
          getr_resolve. rewrite Hr12.
          rewrite c_eq_small. unfold bv_eqb. apply Z.eqb_neq.
          rewrite !u_ntw by lia. lia. }
      assert (Hr15' : reg_get regs5 15 = nat_to_word (S j)) by apply regupd_same.
      assert (Hr17' : reg_get regs5 17 = hp + nat_to_word i).
      { unfold regs5, regs4, regs3, regs2, regs1.
        regupd_resolve. exact Hr17. }
      assert (Hr19' : reg_get regs5 19 = pp).
      { unfold regs5, regs4, regs3, regs2, regs1.
        regupd_resolve. exact Hr19. }
      assert (Hr12' : reg_get regs5 12 = nat_to_word (length pat)).
      { unfold regs5, regs4, regs3, regs2, regs1.
        regupd_resolve. exact Hr12. }
      destruct (IH i (S j) regs5 ltac:(lia) ltac:(lia) ltac:(lia)
                  Hr15' Hr17' Hr19' Hr12') as [regs' [Hag [H12 Hms]]].
      exists regs'. split; [|split].
      * intros r H10 H12x H15 H16. rewrite (Hag r H10 H12x H15 H16).
        unfold regs5, regs4, regs3, regs2, regs1.
        rewrite !regupd_other by assumption. reflexivity.
      * rewrite Hspec, ?Heqb. cbn [andb].
        rewrite <- plus_n_Sm in H12. exact H12.
      * rewrite Hspec, ?Heqb. cbn [andb].
        rewrite <- plus_n_Sm in Hms.
        eapply mst_step; [reflexivity | exact E1 |].
        eapply mst_step; [reflexivity | exact E2 |].
        eapply mst_step; [reflexivity | exact E3 |].
        eapply mst_step; [reflexivity | exact E4 |].
        eapply mst_step; [reflexivity | exact E5 |].
        eapply mst_step; [reflexivity | exact E6 |].
        eapply mst_step; [reflexivity | exact E7 |].
        exact Hms.
  - (* bytes differ: beq falls through; the j = nn test at 0x110c4 fails *)
    assert (E5 : RiscvSemantics.step source_segs (mkst regs4 0x110c0 mem rrom)
                 = MachineOk (mkst regs4 0x110c4 mem rrom)).
    { rewrite (step_beq_ft source_segs regs4 0x110c0 mem rrom _ 16 10 _
                 SF_110c0 eq_refl SD_110c0).
      - wlits. reflexivity.
      - unfold regs4, regs3. getr_resolve.
        rewrite c_eq_small, bv_eqb_zext. exact Heqb. }
    assert (E6 : RiscvSemantics.step source_segs (mkst regs4 0x110c4 mem rrom)
                 = MachineOk (mkst regs4 0x110c8 mem rrom)).
    { rewrite (step_beq_ft source_segs regs4 0x110c4 mem rrom _ 15 12 _
                 SF_110c4 eq_refl SD_110c4).
      - wlits. reflexivity.
      - unfold regs4, regs3, regs2, regs1.
        getr_resolve. rewrite Hr15, Hr12.
        rewrite c_eq_small. unfold bv_eqb. apply Z.eqb_neq.
        rewrite !u_ntw by lia. lia. }
    exists regs4. split; [|split].
    + intros r H10 H12 H15 H16.
      unfold regs4, regs3, regs2, regs1.
      rewrite !regupd_other by assumption. reflexivity.
    + rewrite Hspec, ?Heqb. cbn [andb].
      unfold regs4, regs3, regs2, regs1.
      regupd_resolve. exact Hr12.
    + rewrite Hspec, ?Heqb. cbn [andb].
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      eapply mst_step; [reflexivity | exact E4 |].
      eapply mst_step; [reflexivity | exact E5 |].
      eapply mst_step; [reflexivity | exact E6 |].
      apply mst_refl.
Qed.

(* ================================================================= *)
(* Scan loop vs [scan_from]                                          *)
(* ================================================================= *)

(** From the scan guard 0x110cc with a3 = i, a4 = hn, a2 = nn >= 1,
    a1 = &hay, s3 = &pat and nn <= hn: exits to 0x110dc (with a2 := 0)
    iff the pattern occurs at some position >= i (within fuel f), else
    to 0x11080 (next argument).  Clobbers a0, a2, a3, a5, a6, a7. *)
Lemma source_scan : forall k, (k < length av)%nat -> (2 <= length av)%nat ->
  forall mem, mem_ok mem ->
  forall f i regs,
  (1 <= length (nth 1 av []))%nat ->
  (length (nth 1 av []) <= length (nth k av []))%nat ->
  (i + f = S (length (nth k av []) - length (nth 1 av [])))%nat ->
  reg_get regs 13 = nat_to_word i ->
  reg_get regs 14 = nat_to_word (length (nth k av [])) ->
  reg_get regs 12 = nat_to_word (length (nth 1 av [])) ->
  reg_get regs 11 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k ->
  reg_get regs 19 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1 ->
  exists regs',
    (forall r : reg, r <> 10 -> r <> 12 -> r <> 13 -> r <> 15 -> r <> 16 ->
       r <> 17 -> reg_get regs' r = reg_get regs r) /\
    (if scan_from (nth k av []) (nth 1 av []) i f
     then reg_get regs' 12 = nat_to_word 0 else True) /\
    msteps source_segs (mkst regs 0x110cc mem rrom)
      (mkst regs'
        (if scan_from (nth k av []) (nth 1 av []) i f
         then 0x110dc else 0x11080) mem rrom).
Proof.
  intros k Hk H2le mem Hmem.
  pose proof (source_ptr_bounds k Hk) as [Hgeh Hlth].
  pose proof (valid_argv_str_len av k Hva Hk) as Hhlen.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as Hplen.
  induction f as [|f IH];
    intros i regs Hnn1 Hnnhn Hif Hr13 Hr14 Hr12 Hr11 Hr19.
  - (* fuel exhausted: the guard must fail *)
    set (regs1 := regupd regs 15 (nat_to_word (i + length (nth 1 av [])))).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x110cc mem rrom)
                 = MachineOk (mkst regs1 0x110d0 mem rrom)).
    { rewrite (step_add source_segs regs 0x110cc mem rrom _ 15 13 12
                 SF_110cc eq_refl SD_110cc).
      reduce_bv_eqb_ifs.
      unfold regs1. getr_resolve. rewrite Hr13, Hr12.
      rewrite v_add_ntw. wlits. reflexivity. }
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x110d0 mem rrom)
                 = MachineOk (mkst regs1 0x110d4 mem rrom)).
    { rewrite (step_bgeu_ft source_segs regs1 0x110d0 mem rrom _ 14 15 _
                 SF_110d0 eq_refl SD_110d0).
      - wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite Hr14.
        rewrite c_ltu_ltb. apply Z.ltb_lt.
        rewrite !u_ntw by lia. lia. }
    assert (E3 : RiscvSemantics.step source_segs (mkst regs1 0x110d4 mem rrom)
                 = MachineOk (mkst regs1 0x11080 mem rrom)).
    { rewrite (step_jal_x0 source_segs regs1 0x110d4 mem rrom _ _
                 SF_110d4 eq_refl SD_110d4).
      wlits. reflexivity. }
    exists regs1. split; [|split].
    + intros r H10 H12 H13 H15 H16 H17. unfold regs1.
      rewrite regupd_other by assumption. reflexivity.
    + cbn [scan_from]. exact I.
    + cbn [scan_from].
      eapply mst_step; [reflexivity | exact E1 |].
      eapply mst_step; [reflexivity | exact E2 |].
      eapply mst_step; [reflexivity | exact E3 |].
      apply mst_refl.
  - (* fuel left: the guard holds, run one compare at position i *)
    assert (Hin : (i + length (nth 1 av []) <= length (nth k av []))%nat) by lia.
    set (regs1 := regupd regs 15 (nat_to_word (i + length (nth 1 av [])))).
    assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x110cc mem rrom)
                 = MachineOk (mkst regs1 0x110d0 mem rrom)).
    { rewrite (step_add source_segs regs 0x110cc mem rrom _ 15 13 12
                 SF_110cc eq_refl SD_110cc).
      reduce_bv_eqb_ifs.
      unfold regs1. getr_resolve. rewrite Hr13, Hr12.
      rewrite v_add_ntw. wlits. reflexivity. }
    assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x110d0 mem rrom)
                 = MachineOk (mkst regs1 0x110a8 mem rrom)).
    { rewrite (step_bgeu_tk source_segs regs1 0x110d0 mem rrom _ 14 15 _
                 SF_110d0 eq_refl SD_110d0).
      - wlits. reflexivity.
      - unfold regs1. getr_resolve. rewrite Hr14.
        rewrite c_ltu_ltb. apply Z.ltb_ge.
        rewrite !u_ntw by lia. lia. }
    (* 0x110a8: a5 := 0 *)
    set (regs2 := regupd regs1 15 (nat_to_word 0)).
    assert (E3 : RiscvSemantics.step source_segs (mkst regs1 0x110a8 mem rrom)
                 = MachineOk (mkst regs2 0x110ac mem rrom)).
    { rewrite (step_addi source_segs regs1 0x110a8 mem rrom _ 15 0 _
                 SF_110a8 eq_refl SD_110a8).
      reduce_bv_eqb_ifs. getr_resolve.
      replace (v_addi (Z_to_bv 64 0) (bv_signed (0%bv : bv 12)))
        with (nat_to_word 0) by bveq.
      wlits. reflexivity. }
    (* 0x110ac: a7 := a1 + a3 = &hay[i] *)
    set (regs3 := regupd regs2 17 (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word i)).
    assert (E4 : RiscvSemantics.step source_segs (mkst regs2 0x110ac mem rrom)
                 = MachineOk (mkst regs3 0x110b0 mem rrom)).
    { rewrite (step_add source_segs regs2 0x110ac mem rrom _ 17 11 13
                 SF_110ac eq_refl SD_110ac).
      reduce_bv_eqb_ifs.
      unfold regs3, regs2, regs1. getr_resolve. rewrite Hr11, Hr13.
      wlits. reflexivity. }
    assert (Hr15C : reg_get regs3 15 = nat_to_word 0).
    { unfold regs3, regs2. regupd_resolve. reflexivity. }
    assert (Hr17C : reg_get regs3 17
                    = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k + nat_to_word i)
      by (unfold regs3; apply regupd_same).
    assert (Hr19C : reg_get regs3 19 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1).
    { unfold regs3, regs2, regs1. regupd_resolve. exact Hr19. }
    assert (Hr12C : reg_get regs3 12 = nat_to_word (length (nth 1 av []))).
    { unfold regs3, regs2, regs1. regupd_resolve. exact Hr12. }
    destruct (source_cmp k Hk H2le mem Hmem i (length (nth 1 av [])) 0 regs3
                ltac:(lia) ltac:(lia) Hin Hr15C Hr17C Hr19C Hr12C)
      as [regsC [HagC [H12C HmsC]]].
    rewrite skipn_O, Nat.add_0_r in H12C, HmsC.
    assert (HagE : forall r : reg, r <> 10 -> r <> 12 -> r <> 13 -> r <> 15 ->
                     r <> 16 -> r <> 17 -> reg_get regsC r = reg_get regs r).
    { intros r H10 H12 H13 H15 H16 H17. rewrite (HagC r H10 H12 H15 H16).
      unfold regs3, regs2, regs1. rewrite !regupd_other by assumption.
      reflexivity. }
    cbn [scan_from].
    destruct (prefix_eqb (nth 1 av []) (nth k av []) i) eqn:Epre.
    + (* match found at i *)
      exists regsC. split; [|split].
      * exact HagE.
      * cbn [orb]. exact H12C.
      * cbn [orb].
        eapply mst_step; [reflexivity | exact E1 |].
        eapply mst_step; [reflexivity | exact E2 |].
        eapply mst_step; [reflexivity | exact E3 |].
        eapply mst_step; [reflexivity | exact E4 |].
        exact HmsC.
    + (* no match at i: a3 += 1 and retest the guard *)
      cbn [orb].
      set (regsD := regupd regsC 13 (nat_to_word (S i))).
      assert (E5 : RiscvSemantics.step source_segs (mkst regsC 0x110c8 mem rrom)
                   = MachineOk (mkst regsD 0x110cc mem rrom)).
      { rewrite (step_addi source_segs regsC 0x110c8 mem rrom _ 13 13 _
                   SF_110c8 eq_refl SD_110c8).
        reduce_bv_eqb_ifs.
        unfold regsD. getr_resolve.
        rewrite (HagC 13) by reg_neq_tac.
        unfold regs3, regs2, regs1. regupd_resolve. rewrite Hr13.
        rewrite v_addi_Sj by lia. wlits. reflexivity. }
      assert (Hr13D : reg_get regsD 13 = nat_to_word (S i))
        by (unfold regsD; apply regupd_same).
      assert (Hr14D : reg_get regsD 14 = nat_to_word (length (nth k av []))).
      { unfold regsD. rewrite regupd_other by reg_neq_tac.
        rewrite HagE by reg_neq_tac. exact Hr14. }
      assert (Hr12D : reg_get regsD 12 = nat_to_word (length (nth 1 av []))).
      { unfold regsD. rewrite regupd_other by reg_neq_tac. exact H12C. }
      assert (Hr11D : reg_get regsD 11 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) k).
      { unfold regsD. rewrite regupd_other by reg_neq_tac.
        rewrite HagE by reg_neq_tac. exact Hr11. }
      assert (Hr19D : reg_get regsD 19 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1).
      { unfold regsD. rewrite regupd_other by reg_neq_tac.
        rewrite HagE by reg_neq_tac. exact Hr19. }
      destruct (IH (S i) regsD Hnn1 Hnnhn ltac:(lia)
                  Hr13D Hr14D Hr12D Hr11D Hr19D) as [regs' [Hag' [H12' Hms']]].
      exists regs'. split; [|split].
      * intros r H10 H12 H13 H15 H16 H17.
        rewrite (Hag' r H10 H12 H13 H15 H16 H17).
        unfold regsD. rewrite regupd_other by assumption.
        apply HagE; assumption.
      * exact H12'.
      * eapply mst_step; [reflexivity | exact E1 |].
        eapply mst_step; [reflexivity | exact E2 |].
        eapply mst_step; [reflexivity | exact E3 |].
        eapply mst_step; [reflexivity | exact E4 |].
        eapply msteps_trans; [exact HmsC |].
        eapply mst_step; [reflexivity | exact E5 |].
        exact Hms'.
Qed.

(* ================================================================= *)
(* Output phase: 0x110dc (write a matched argument) .. 0x11080        *)
(* ================================================================= *)

(** The newline write from 0x110ec: a2 := 1; a1 := 0x12000; the write
    loop spills a2/a1 to 8(sp)/0(sp), calls write(1, "\n", 1) and
    (since the model pins the return to the full length) reloads, sees
    a2 - a0 = 0 and rejoins the next-arg path at 0x11080.  Preserves
    sp and every callee-saved register; the memory stays [mem_ok]. *)
Lemma source_nl_write : forall regs mem bufs code,
  mem_ok mem ->
  reg_get regs 20 = Z_to_bv 64 73728 ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ->
  (forall regs' mem', mem_ok mem' ->
     (forall r : reg, r <> 1 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 ->
        r <> 14 -> r <> 15 -> r <> 16 -> r <> 17 ->
        reg_get regs' r = reg_get regs r) ->
     wexit1 source_segs (mkst regs' 0x11080 mem' rrom) bufs code) ->
  wexit1 source_segs (mkst regs 0x110ec mem rrom) ([Z_to_bv 8 10] :: bufs) code.
Proof.
  intros regs mem bufs code Hmem Hr20 Hr2 Hcont.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  split; [cbn [length]; lia|].
  (* 0x110ec: a2 := 1 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 1);
      [ exact SF_110ec | reflexivity | exact SD_110ec | reflexivity
      | getr_resolve; bveq ]
    | norm_pc ].
  (* 0x110f0: a1 := s4 = 0x12000 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := (0x12000 : word));
      [ exact SF_110f0 | reflexivity | exact SD_110f0 | reflexivity
      | getr_resolve; regupd_resolve; rewrite Hr20; bveq ]
    | norm_pc ].
  (* 0x110f4: a0 := 1 *)
  chain_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 1);
      [ exact SF_110f4 | reflexivity | exact SD_110f4 | reflexivity
      | getr_resolve; exact v_addi_0_1 ]
    | norm_pc ].
  (* 0x110f8: sd a2, 8(sp) — spill the length *)
  chain_step;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned rsp - 0x38))
                             (v := Z_to_bv 64 1);
      [ exact SF_110f8 | reflexivity | exact SD_110f8
      | getr_resolve; regupd_resolve; rewrite Hr2; sp_norm; f_equal; lia
      | getr_resolve; regupd_resolve; reflexivity
      | solve_store_ok_inv ]
    | step_simpl ].
  (* 0x110fc: sd a1, 0(sp) — spill the pointer *)
  chain_step;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned rsp - 0x40))
                             (v := (0x12000 : word));
      [ exact SF_110fc | reflexivity | exact SD_110fc
      | getr_resolve; regupd_resolve; rewrite Hr2; sp_norm; f_equal; lia
      | getr_resolve; regupd_resolve; reflexivity
      | solve_store_ok_inv ]
    | step_simpl ].
  (* 0x11100: call write *)
  chain_step;
    [ reflexivity
    | eapply step_jal_link;
      [ exact SF_11100 | reflexivity | exact SD_11100 ]
    | step_simpl ].
  eapply source_write_fn with (buf := [Z_to_bv 8 10]) (RA := (0x11104 : word))
    (K := to_wallexit source_segs (Z_to_bv 64 1) bufs code).
  + apply mem_ok_scratch8;
      [ apply mem_ok_scratch8; [exact Hmem | u_norm; lia | u_norm; lia]
      | u_norm; lia | u_norm; lia ].
  + regupd_resolve. reflexivity.
  + regupd_resolve. bveq.
  + bveq.
  + regupd_resolve. exact Hr2.
  + regupd_resolve. u_norm; lia.
  + regupd_resolve. u_norm; lia.
  + regupd_resolve. imm_norm; u_norm; lia.
  + regupd_resolve. imm_norm; u_norm. unfold TASK_SIZE. lia.
  + regupd_resolve. right. imm_norm; u_norm; lia.
  + regupd_resolve. exact read_newline_f.
  + intros regsB memB kB HkB1 HkB2 HmB HagrB HagB H10B.
    assert (HkB : kB = 1%nat) by (cbn [length] in HkB2; lia). subst kB.
    cbn [firstn skipn] in H10B |- *.
    replace (len_word [Z_to_bv 8 10]) with (Z_to_bv 64 1) in H10B
      by reflexivity.
    (* 0x11104: blez a0 falls through (a0 = 1) *)
    chain_step;
      [ reflexivity
      | eapply step_bge_ft;
        [ exact SF_11104 | reflexivity | exact SD_11104
        | getr_resolve; rewrite H10B; regupd_resolve;
          vm_compute; reflexivity ]
      | norm_pc ].
    (* 0x11108: ld a2, 8(sp) — the spilled length *)
    chain_step;
      [ reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 1))
                            (v := Z_to_bv 64 1);
        [ exact SF_11108 | reflexivity | exact SD_11108
        | match goal with |- rdn _ _ ?a _ = _ =>
            replace a with (Z_to_bv 64 (bv_unsigned rsp - 0x38))
              by (getr_resolve; rewrite (HagB 2) by reg_neq_tac;
                  regupd_resolve; rewrite Hr2; sp_norm; f_equal; lia) end;
          rewrite HagrB by (u_norm; lia);
          rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; u_norm; lia);
          apply rdn_wbytes_hit8; u_norm; lia
        | exact (bytes_le_to_Z_8 _) ]
      | step_simpl ].
    (* 0x1110c: ld a1, 0(sp) — the spilled pointer *)
    chain_step;
      [ reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 (0x12000 : word))
                            (v := (0x12000 : word));
        [ exact SF_1110c | reflexivity | exact SD_1110c
        | match goal with |- rdn _ _ ?a _ = _ =>
            replace a with (Z_to_bv 64 (bv_unsigned rsp - 0x40))
              by (getr_resolve; regupd_resolve;
                  rewrite (HagB 2) by reg_neq_tac;
                  regupd_resolve; rewrite Hr2; sp_norm; f_equal; lia) end;
          rewrite HagrB by (u_norm; lia);
          apply rdn_wbytes_hit8; u_norm; lia
        | exact (bytes_le_to_Z_8 _) ]
      | step_simpl ].
    (* 0x11110: a2 -= a0 (= 0); 0x11114: a1 += a0 *)
    stepi SF_11110 SD_11110.
    stepi SF_11114 SD_11114.
    (* 0x11118: bnez a2 falls through (a2 = 1 - 1 = 0) *)
    chain_step;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact SF_11118 | reflexivity | exact SD_11118
        | getr_resolve; regupd_resolve; rewrite H10B; regupd_resolve;
          vm_compute; reflexivity ]
      | norm_pc ].
    (* 0x1111c: j 0x11080 *)
    stepj SF_1111c SD_1111c.
    apply twt_done.
    apply Hcont.
    * exact HmB.
    * intros r Hx1 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17.
      rewrite !regupd_other by assumption.
      rewrite (HagB r) by assumption.
      rewrite !regupd_other by assumption.
      reflexivity.
Qed.

(** The argument-write retry loop at 0x11130.  Entry is the
    [ld a1,0(sp)] right after a [write] delivery: [p] and [rest] are
    the pointer and the byte count spilled to 0(sp)/8(sp) before that
    call, and [n] is the length that delivery handed back in a0.  The
    loop reloads the spilled pair, bumps it by [n], and either falls
    into the newline write at 0x110ec (everything delivered) or
    reissues [write] on the remainder.  The [bgtz] error arm is dead:
    every delivery is nonempty.  The buffer read is stated over [fmem]
    (it is what [source_write_fn] asks for); the two spill slots sit
    inside the window [mem_ok] excludes, so they travel as their own
    [rdn] facts. *)
Lemma source_out_wall : forall (K : machine_state -> Prop) fuel
    (rest : list byte) (p : word) n regs mem,
  (length rest <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length rest)%nat ->
  (Z.of_nat (length rest) <= 131071)%Z ->
  (bv_unsigned rsp - 0x30 <= bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) < 2^64)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) <= TASK_SIZE)%Z ->
  mem_ok mem ->
  reg_get regs 10 = len_word (firstn n rest) ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x40)) 8%nat
    = Some (word_to_le_bytes 8 p) ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8%nat
    = Some (word_to_le_bytes 8 (len_word rest)) ->
  rdn source_segs fmem p (length rest) = Some rest ->
  (forall regs' mem', mem_ok mem' ->
     (forall r : reg, r <> 1 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 ->
        r <> 14 -> r <> 15 -> r <> 16 -> r <> 17 ->
        reg_get regs' r = reg_get regs r) ->
     K (mkst regs' 0x110ec mem' rrom)) ->
  to_wall_tail source_segs (Z_to_bv 64 1)
    (mkst regs 0x11130 mem rrom) (skipn n rest) K.
Proof.
  intros K fuel. induction fuel as [|fuel IH];
    intros rest p n regs mem Hfuel Hn1 Hn2 Hlen Hplo Hphi Hptask Hmem H10 H2
           Hs0 Hs8 Hbuf Hcont.
  { lia. }
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  pose proof (u64_range p) as Hup.
  assert (Hsk : rdn source_segs fmem (p + nat_to_word n)
                  (length (skipn n rest)) = Some (skipn n rest)).
  { pose proof (SeqExec.rdn_skipn source_segs fmem (length rest) p rest n
                  Hbuf Hn2) as H.
    rewrite length_skipn. exact H. }
  (* 0x11130: ld a1, 0(sp) — reload the spilled pointer *)
  chain_step;
    [ reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 p) (v := p);
      [ exact SF_11130 | reflexivity | exact SD_11130
      | match goal with |- rdn _ _ ?a _ = _ =>
          replace a with (Z_to_bv 64 (bv_unsigned rsp - 0x40))
            by (getr_resolve; rewrite H2; sp_norm; f_equal; lia) end;
        exact Hs0
      | exact (bytes_le_to_Z_8 _) ]
    | step_simpl ].
  (* 0x11134: ld a2, 8(sp) — reload the spilled count *)
  chain_step;
    [ reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 (len_word rest))
                          (v := len_word rest);
      [ exact SF_11134 | reflexivity | exact SD_11134
      | match goal with |- rdn _ _ ?a _ = _ =>
          replace a with (Z_to_bv 64 (bv_unsigned rsp - 0x38))
            by (getr_resolve; regupd_resolve; rewrite H2; sp_norm;
                f_equal; lia) end;
        exact Hs8
      | exact (bytes_le_to_Z_8 _) ]
    | step_simpl ].
  (* 0x11138: bgtz a0 taken (the delivery is nonempty) -> 0x11160 *)
  chain_step;
    [ reflexivity
    | eapply step_blt_tk;
      [ exact SF_11138 | reflexivity | exact SD_11138
      | getr_resolve; regupd_resolve; rewrite H10; apply c_lts_0_pos;
        rewrite u_len_word_firstn by lia; lia ]
    | norm_pc ].
  (* 0x11160: add a1,a1,a0 *)
  stepiv SF_11160 SD_11160 (p + nat_to_word n)
    ltac:(getr_resolve; regupd_resolve; rewrite H10;
          apply v_add_len_firstn; lia).
  (* 0x11164: sub a2,a2,a0 *)
  stepiv SF_11164 SD_11164 (len_word (skipn n rest))
    ltac:(getr_resolve; regupd_resolve; rewrite H10;
          apply v_sub_len_firstn; lia).
  (* 0x11168: j 0x110e8 *)
  stepj SF_11168 SD_11168.
  destruct (Nat.eq_dec n (length rest)) as [-> | Hne].
  - (* everything delivered: bnez a2 falls through into the newline *)
    rewrite skipn_all.
    chain_step;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact SF_110e8 | reflexivity | exact SD_110e8
        | getr_resolve; regupd_resolve; apply c_eq_0_of_u; reflexivity ]
      | norm_pc ].
    apply twt_done. apply Hcont; [exact Hmem|].
    intros r Hx1 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17.
    rewrite !regupd_other by assumption. reflexivity.
  - (* a short delivery: bnez a2 taken -> reissue at 0x11120 *)
    assert (Hupn : bv_unsigned (p + nat_to_word n)
                   = (bv_unsigned p + Z.of_nat n)%Z).
    { rewrite word_add_nat_Z by lia. apply u_Z2bv; lia. }
    chain_step;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact SF_110e8 | reflexivity | exact SD_110e8
        | getr_resolve; regupd_resolve; apply c_eq_0_false;
          rewrite u_len_word by (rewrite length_skipn; lia);
          rewrite length_skipn; lia ]
      | norm_pc ].
    (* 0x11120: a0 := 1 *)
    stepiv SF_11120 SD_11120 (Z_to_bv 64 1)
      ltac:(getr_resolve; exact v_addi_0_1).
    (* 0x11124: sd a2, 8(sp) — respill the remaining count *)
    chain_step;
      [ reflexivity
      | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned rsp - 0x38))
                               (v := len_word (skipn n rest));
        [ exact SF_11124 | reflexivity | exact SD_11124
        | getr_resolve; regupd_resolve; rewrite H2; sp_norm; f_equal; lia
        | getr_resolve; regupd_resolve; reflexivity
        | solve_store_ok_inv ]
      | step_simpl ].
    (* 0x11128: sd a1, 0(sp) — respill the bumped pointer *)
    chain_step;
      [ reflexivity
      | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned rsp - 0x40))
                               (v := p + nat_to_word n);
        [ exact SF_11128 | reflexivity | exact SD_11128
        | getr_resolve; regupd_resolve; rewrite H2; sp_norm; f_equal; lia
        | getr_resolve; regupd_resolve; reflexivity
        | solve_store_ok_inv ]
      | step_simpl ].
    (* 0x1112c: call write *)
    chain_step;
      [ reflexivity
      | eapply step_jal_link;
        [ exact SF_1112c | reflexivity | exact SD_1112c ]
      | step_simpl ].
    eapply source_write_fn with (buf := skipn n rest) (RA := (0x11130 : word)).
    + apply mem_ok_scratch8;
        [ apply mem_ok_scratch8; [exact Hmem | u_norm; lia | u_norm; lia]
        | u_norm; lia | u_norm; lia ].
    + regupd_resolve. reflexivity.
    + regupd_resolve. bveq.
    + bveq.
    + regupd_resolve. exact H2.
    + regupd_resolve.
      rewrite u_len_word by (rewrite length_skipn; lia).
      rewrite length_skipn; lia.
    + regupd_resolve.
      rewrite u_len_word by (rewrite length_skipn; lia).
      rewrite length_skipn; lia.
    + regupd_resolve.
      rewrite u_len_word by (rewrite length_skipn; lia).
      rewrite length_skipn, Hupn; lia.
    + regupd_resolve.
      rewrite u_len_word by (rewrite length_skipn; lia).
      rewrite length_skipn, Hupn; lia.
    + regupd_resolve. left. rewrite Hupn. lia.
    + regupd_resolve.
      replace (word_to_nat (len_word (skipn n rest)))
        with (length (skipn n rest))
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; lia);
            rewrite Nat2Z.id; reflexivity).
      exact Hsk.
    + intros regsB memB m Hm1 Hm2 HmB HagrB HagB H10B.
      apply (IH (skipn n rest) (p + nat_to_word n) m regsB memB).
      * rewrite length_skipn; lia.
      * exact Hm1.
      * exact Hm2.
      * rewrite length_skipn; lia.
      * rewrite Hupn; lia.
      * rewrite Hupn, length_skipn; lia.
      * rewrite Hupn, length_skipn; lia.
      * exact HmB.
      * exact H10B.
      * rewrite HagB by reg_neq_tac. regupd_resolve. exact H2.
      * rewrite HagrB by (u_norm; lia).
        apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite HagrB by (u_norm; lia).
        rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        apply rdn_wbytes_hit8; u_norm; lia.
      * exact Hsk.
      * intros regsC memC HmC HagC.
        apply Hcont; [exact HmC|].
        intros r Hx1 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17.
        rewrite (HagC r) by assumption.
        rewrite (HagB r) by assumption.
        rewrite !regupd_other by assumption.
        reflexivity.
Qed.

(** From 0x110dc with a1 = &argv[i] and a2 = 0 (a matched argument):
    recomputes the length, writes the argument (skipped when empty) and
    a newline, and rejoins the next-arg path at 0x11080.  Preserves
    sp, s0..s4; the memory stays [mem_ok]. *)
Lemma source_output : forall i regs mem bufs code,
  mem_ok mem ->
  (i < length av)%nat ->
  reg_get regs 11 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) i ->
  reg_get regs 12 = nat_to_word 0 ->
  reg_get regs 20 = Z_to_bv 64 73728 ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ->
  (forall regs' mem', mem_ok mem' ->
     (forall r : reg, r <> 1 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 ->
        r <> 14 -> r <> 15 -> r <> 16 -> r <> 17 ->
        reg_get regs' r = reg_get regs r) ->
     wexit1 source_segs (mkst regs' 0x11080 mem' rrom) bufs code) ->
  wexit1 source_segs (mkst regs 0x110dc mem rrom)
    ((match nth i av [] with
      | [] => [[Z_to_bv 8 10]] | _ :: _ => [nth i av []; [Z_to_bv 8 10]] end) ++ bufs) code.
Proof.
  intros i regs mem bufs code Hmem Hi Hr11 Hr12 Hr20 Hr2 Hcont.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  pose proof (source_ptr_bounds i Hi) as [Hge Hlt].
  pose proof (valid_argv_str_len av i Hva Hi) as Hslen.
  (* a2 := strlen(argv[i]) *)
  destruct (source_slen_out i Hi mem Hmem (length (nth i av [])) 0%nat regs
              ltac:(lia) Hr11 Hr12) as [regsL [HagL [Hr12L HmsL]]].
  eapply msteps_to_wallexit; [exact HmsL |].
  destruct (nth i av []) as [|b0 srest] eqn:Ea.
  - (* empty argument: newline only *)
    cbn [app]. cbn [length] in Hr12L.
    (* 0x110e8: bnez a2 falls through (a2 = 0) *)
    chain_step;
      [ reflexivity
      | eapply step_bne_ft;
        [ exact SF_110e8 | reflexivity | exact SD_110e8
        | getr_resolve; rewrite Hr12L; apply c_eq_0_of_u;
          rewrite u_ntw by lia; lia ]
      | norm_pc ].
    apply source_nl_write.
    + exact Hmem.
    + rewrite HagL by reg_neq_tac. exact Hr20.
    + rewrite HagL by reg_neq_tac. exact Hr2.
    + intros regsF memF HmF HagF. apply Hcont; [exact HmF|].
      intros r Hx1 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17.
      rewrite (HagF r) by assumption. apply HagL; assumption.
  - (* nonempty argument: write it, then the newline *)
    rewrite <- Ea in *.
    assert (Hnn : (1 <= length (nth i av []))%nat) by (rewrite Ea; cbn; lia).
    cbn [app].
    (* 0x110e8: bnez a2 taken (a2 = hn >= 1) -> 0x11120 *)
    chain_step;
      [ reflexivity
      | eapply step_bne_tk;
        [ exact SF_110e8 | reflexivity | exact SD_110e8
        | getr_resolve; rewrite Hr12L; apply c_eq_0_false;
          rewrite u_ntw by lia; lia ]
      | norm_pc ].
    (* 0x11120: a0 := 1 *)
    chain_step;
      [ reflexivity
      | eapply step_addi_at with (v := Z_to_bv 64 1);
        [ exact SF_11120 | reflexivity | exact SD_11120 | reflexivity
        | getr_resolve; exact v_addi_0_1 ]
      | norm_pc ].
    (* 0x11124: sd a2, 8(sp) — spill the length *)
    chain_step;
      [ reflexivity
      | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned rsp - 0x38))
                               (v := nat_to_word (length (nth i av [])));
        [ exact SF_11124 | reflexivity | exact SD_11124
        | getr_resolve; regupd_resolve; rewrite (HagL 2) by reg_neq_tac;
          rewrite Hr2; sp_norm; f_equal; lia
        | getr_resolve; regupd_resolve; exact Hr12L
        | solve_store_ok_inv ]
      | step_simpl ].
    (* 0x11128: sd a1, 0(sp) — spill the pointer *)
    chain_step;
      [ reflexivity
      | eapply step_sd_at with (a := Z_to_bv 64 (bv_unsigned rsp - 0x40))
                               (v := cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) i);
        [ exact SF_11128 | reflexivity | exact SD_11128
        | getr_resolve; regupd_resolve; rewrite (HagL 2) by reg_neq_tac;
          rewrite Hr2; sp_norm; f_equal; lia
        | getr_resolve; regupd_resolve; rewrite (HagL 11) by reg_neq_tac;
          exact Hr11
        | solve_store_ok_inv ]
      | step_simpl ].
    (* 0x1112c: call write *)
    chain_step;
      [ reflexivity
      | eapply step_jal_link;
        [ exact SF_1112c | reflexivity | exact SD_1112c ]
      | step_simpl ].
    split; [exact Hnn|].
    eapply source_write_fn with (buf := nth i av []) (RA := (0x11130 : word)).
    + apply mem_ok_scratch8;
        [ apply mem_ok_scratch8; [exact Hmem | u_norm; lia | u_norm; lia]
        | u_norm; lia | u_norm; lia ].
    + regupd_resolve. reflexivity.
    + regupd_resolve. bveq.
    + bveq.
    + regupd_resolve. rewrite (HagL 2) by reg_neq_tac. exact Hr2.
    + regupd_resolve. rewrite Hr12L. rewrite u_ntw by lia. lia.
    + regupd_resolve. rewrite Hr12L. rewrite u_ntw by lia. lia.
    + regupd_resolve. rewrite (HagL 11) by reg_neq_tac.
      rewrite Hr11, Hr12L. rewrite u_ntw by lia. lia.
    + regupd_resolve. rewrite (HagL 11) by reg_neq_tac.
      rewrite Hr11, Hr12L. rewrite u_ntw by lia.
      exact (argv_str_task inp rmb rsp rbrk rrnd Hlau i Hi).
    + regupd_resolve. left. rewrite (HagL 11) by reg_neq_tac.
      rewrite Hr11. lia.
    + regupd_resolve. rewrite (HagL 11) by reg_neq_tac.
      rewrite Hr11, Hr12L. rewrite word_to_nat_ntw by lia.
      apply read_str_f. exact Hi.
    + intros regsA memA kA HkA1 HkA2 HmA HagrA HagA H10A.
      apply (source_out_wall _ (length (nth i av [])) (nth i av [])
               (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) i) kA regsA memA).
      * lia.
      * exact HkA1.
      * exact HkA2.
      * lia.
      * lia.
      * lia.
      * exact (argv_str_task inp rmb rsp rbrk rrnd Hlau i Hi).
      * exact HmA.
      * exact H10A.
      * rewrite (HagA 2) by reg_neq_tac. regupd_resolve.
        rewrite (HagL 2) by reg_neq_tac. exact Hr2.
      * rewrite HagrA by (u_norm; lia).
        apply rdn_wbytes_hit8; u_norm; lia.
      * rewrite HagrA by (u_norm; lia).
        rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia).
        apply rdn_wbytes_hit8; u_norm; lia.
      * apply read_str_f. exact Hi.
      * intros regsF memF HmF HagF.
        apply source_nl_write.
        -- exact HmF.
        -- rewrite (HagF 20) by reg_neq_tac.
           rewrite (HagA 20) by reg_neq_tac. regupd_resolve.
           rewrite (HagL 20) by reg_neq_tac. exact Hr20.
        -- rewrite (HagF 2) by reg_neq_tac.
           rewrite (HagA 2) by reg_neq_tac. regupd_resolve.
           rewrite (HagL 2) by reg_neq_tac. exact Hr2.
        -- intros regsG memG HmG HagG. apply Hcont; [exact HmG|].
           intros r Hx1 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17.
           rewrite (HagG r) by assumption.
           rewrite (HagF r) by assumption.
           rewrite (HagA r) by assumption.
           rewrite !regupd_other by assumption.
           apply HagL; assumption.
Qed.

(* ================================================================= *)
(* One argument: loop head 0x11038 -> (writes) -> loop head           *)
(* ================================================================= *)

Lemma source_arg : forall i regs mem bufs code,
  mem_ok mem ->
  (2 <= length av)%nat -> (2 <= i)%nat -> (i < length av)%nat ->
  reg_get regs 8 = argcN ->
  reg_get regs 9 = nat_to_word i ->
  reg_get regs 18 = Z_to_bv 64 (bv_unsigned rsp + 8) ->
  reg_get regs 19 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1 ->
  reg_get regs 20 = Z_to_bv 64 73728 ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ->
  (forall regs' mem', mem_ok mem' ->
     reg_get regs' 8 = argcN -> reg_get regs' 9 = nat_to_word (S i) ->
     reg_get regs' 18 = Z_to_bv 64 (bv_unsigned rsp + 8) ->
     reg_get regs' 19 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1 ->
     reg_get regs' 20 = Z_to_bv 64 73728 ->
     reg_get regs' 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ->
     wexit1 source_segs (mkst regs' 0x11038 mem' rrom) bufs code) ->
  wexit1 source_segs (mkst regs 0x11038 mem rrom)
    (arg_bufs (nth 1 av []) (nth i av []) ++ bufs) code.
Proof.
  intros i regs mem bufs code Hmem H2le H2i Hi Hr8 Hr9 Hr18 Hr19 Hr20 Hr2
    Hcont.
  pose proof (valid_argv_len av Hva) as Hargc.
  pose proof (source_ptr_bounds i Hi) as [Hgeh Hlth].
  pose proof (source_ptr_bounds 1 ltac:(lia)) as [Hgep Hltp].
  pose proof (valid_argv_str_len av i Hva Hi) as Hhlen.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as Hplen.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  assert (HiN' : (Z.of_nat i <= 1024)%Z) by lia.
  (* --- the next-arg tail: 0x11080 (s1 += 1; j loop head) --- *)
  assert (Htail : forall regsT memT,
    reg_get regsT 9%bv = nat_to_word i ->
    msteps source_segs (mkst regsT 0x11080 memT rrom)
           (mkst (regupd regsT 9 (nat_to_word (S i))) 0x11038 memT rrom)).
  { intros regsT memT HrT.
    eapply mst_step;
      [ reflexivity
      | rewrite (step_addi source_segs regsT 0x11080 memT rrom _ 9 9 _
                   SF_11080 eq_refl SD_11080);
        reduce_bv_eqb_ifs;
        getr_resolve; rewrite HrT;
        rewrite v_addi_Sj by lia; wlits; reflexivity
      |].
    eapply mst_step;
      [ reflexivity
      | rewrite (step_jal_x0 source_segs _ 0x11084 memT rrom _ _
                   SF_11084 eq_refl SD_11084);
        wlits; reflexivity
      |].
    apply mst_refl. }
  (* --- 0x11038..0x11050: loop test, index the argv table, load argv[i] --- *)
  set (regs1 := regupd regs 15 (nat_to_word i)).
  assert (E1 : RiscvSemantics.step source_segs (mkst regs 0x11038 mem rrom)
               = MachineOk (mkst regs1 0x1103c mem rrom)).
  { rewrite (step_addiw source_segs regs 0x11038 mem rrom _ 15 9 _
               SF_11038 eq_refl SD_11038).
    reduce_bv_eqb_ifs. getr_resolve.
    rewrite Hr9. rewrite v_addiw_id by (rewrite u_ntw by lia; lia).
    wlits. reflexivity. }
  assert (E2 : RiscvSemantics.step source_segs (mkst regs1 0x1103c mem rrom)
               = MachineOk (mkst regs1 0x11048 mem rrom)).
  { rewrite (step_blt_tk source_segs regs1 0x1103c mem rrom _ 15 8 _
               SF_1103c eq_refl SD_1103c).
    - wlits. reflexivity.
    - unfold regs1. getr_resolve. rewrite Hr8.
      rewrite c_lts_small
        by (rewrite ?u_ntw by lia; rewrite ?u_argcN; lia).
      apply Z.ltb_lt. rewrite u_ntw by lia. rewrite u_argcN. lia. }
  set (regs2 := regupd regs1 15 (Z_to_bv 64 (8 * Z.of_nat i))).
  assert (E3 : RiscvSemantics.step source_segs (mkst regs1 0x11048 mem rrom)
               = MachineOk (mkst regs2 0x1104c mem rrom)).
  { rewrite (step_slli source_segs regs1 0x11048 mem rrom _ 15 9 _
               SF_11048 eq_refl SD_11048).
    reduce_bv_eqb_ifs.
    unfold regs2, regs1. getr_resolve. rewrite Hr9.
    rewrite v_slli3_nat by lia. wlits. reflexivity. }
  set (regs3 := regupd regs2 15 (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat i))).
  assert (E4 : RiscvSemantics.step source_segs (mkst regs2 0x1104c mem rrom)
               = MachineOk (mkst regs3 0x11050 mem rrom)).
  { rewrite (step_add source_segs regs2 0x1104c mem rrom _ 15 18 15
               SF_1104c eq_refl SD_1104c).
    reduce_bv_eqb_ifs.
    unfold regs3, regs2, regs1. getr_resolve. rewrite Hr18.
    replace (v_add (Z_to_bv 64 (bv_unsigned rsp + 8)) (Z_to_bv 64 (8 * Z.of_nat i)))
      with (Z_to_bv 64 (bv_unsigned rsp + 8 + 8 * Z.of_nat i))
      by (apply bv_eq; rewrite v_add_small by (u_norm; lia); u_norm; lia).
    wlits. reflexivity. }
  set (regs4 := regupd regs3 11 (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) i)).
  assert (E5 : RiscvSemantics.step source_segs (mkst regs3 0x11050 mem rrom)
               = MachineOk (mkst regs4 0x11054 mem rrom)).
  { rewrite (step_ld source_segs regs3 0x11050 mem rrom _ 11 15 _
               (word_le8 (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) i)) (cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) i)
               SF_11050 eq_refl SD_11050).
    - reduce_bv_eqb_ifs. wlits. reflexivity.
    - unfold regs3. getr_resolve.
      rewrite v_addi_0.
      apply (read_ptr_m mem Hmem). exact Hi.
    - exact (bytes_le_n_to_le_8 _). }
  (* 0x11054: a4 := 0 *)
  set (regs5 := regupd regs4 14 (nat_to_word 0)).
  assert (E6 : RiscvSemantics.step source_segs (mkst regs4 0x11054 mem rrom)
               = MachineOk (mkst regs5 0x11058 mem rrom)).
  { rewrite (step_addi source_segs regs4 0x11054 mem rrom _ 14 0 _
               SF_11054 eq_refl SD_11054).
    reduce_bv_eqb_ifs. getr_resolve.
    replace (v_addi (Z_to_bv 64 0) (bv_signed (0%bv : bv 12)))
      with (nat_to_word 0) by bveq.
    wlits. reflexivity. }
  (* --- a4 := strlen(argv[i]) --- *)
  assert (Hr11_5 : reg_get regs5 11%bv = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) i).
  { unfold regs5, regs4. regupd_resolve. reflexivity. }
  assert (Hr14_5 : reg_get regs5 14%bv = nat_to_word 0)
    by (unfold regs5; apply regupd_same).
  destruct (source_slen_hay i Hi mem Hmem (length (nth i av [])) 0%nat regs5
              ltac:(lia) Hr11_5 Hr14_5) as [regsH [HagH [Hr14H HmsH]]].
  assert (HrH : forall r : reg, r <> 11 -> r <> 14 -> r <> 15 ->
                  reg_get regsH r = reg_get regs r).
  { intros r Hx11 Hx14 Hx15.
    rewrite (HagH r Hx14 Hx15).
    unfold regs5, regs4, regs3, regs2, regs1.
    rewrite !regupd_other by assumption. reflexivity. }
  assert (Hr11H : reg_get regsH 11%bv = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) i)
    by (rewrite (HagH 11) by reg_neq_tac; exact Hr11_5).
  (* --- 0x11064: a2 := 0; a2 := strlen(argv[1]) --- *)
  set (regs6 := regupd regsH 12 (nat_to_word 0)).
  assert (E7 : RiscvSemantics.step source_segs (mkst regsH 0x11064 mem rrom)
               = MachineOk (mkst regs6 0x11068 mem rrom)).
  { rewrite (step_addi source_segs regsH 0x11064 mem rrom _ 12 0 _
               SF_11064 eq_refl SD_11064).
    reduce_bv_eqb_ifs. getr_resolve.
    replace (v_addi (Z_to_bv 64 0) (bv_signed (0%bv : bv 12)))
      with (nat_to_word 0) by bveq.
    wlits. reflexivity. }
  assert (Hr19_6 : reg_get regs6 19%bv = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1).
  { unfold regs6. regupd_resolve. rewrite HrH by reg_neq_tac. exact Hr19. }
  assert (Hr12_6 : reg_get regs6 12%bv = nat_to_word 0)
    by (unfold regs6; apply regupd_same).
  destruct (source_slen_pat H2le mem Hmem (length (nth 1 av [])) 0%nat regs6
              ltac:(lia) Hr19_6 Hr12_6) as [regsP [HagP [Hr12P HmsP]]].
  assert (HrP : forall r : reg, r <> 11 -> r <> 12 -> r <> 14 -> r <> 15 ->
                  reg_get regsP r = reg_get regs r).
  { intros r Hx11 Hx12 Hx14 Hx15.
    rewrite (HagP r Hx12 Hx15).
    unfold regs6. rewrite regupd_other by assumption.
    apply HrH; assumption. }
  assert (Hr11P : reg_get regsP 11%bv = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) i).
  { rewrite (HagP 11) by reg_neq_tac. unfold regs6.
    rewrite regupd_other by reg_neq_tac. exact Hr11H. }
  assert (Hr14P : reg_get regsP 14%bv = nat_to_word (length (nth i av []))).
  { rewrite (HagP 14) by reg_neq_tac. unfold regs6.
    rewrite regupd_other by reg_neq_tac. exact Hr14H. }
  assert (Hr19P : reg_get regsP 19%bv = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1)
    by (rewrite HrP by reg_neq_tac; exact Hr19).
  assert (Hr8P : reg_get regsP 8%bv = argcN)
    by (rewrite HrP by reg_neq_tac; exact Hr8).
  assert (Hr9P : reg_get regsP 9%bv = nat_to_word i)
    by (rewrite HrP by reg_neq_tac; exact Hr9).
  assert (Hr18P : reg_get regsP 18%bv = Z_to_bv 64 (bv_unsigned rsp + 8))
    by (rewrite HrP by reg_neq_tac; exact Hr18).
  assert (Hr20P : reg_get regsP 20%bv = Z_to_bv 64 73728)
    by (rewrite HrP by reg_neq_tac; exact Hr20).
  assert (Hr2P : reg_get regsP 2%bv = Z_to_bv 64 (bv_unsigned rsp - 0x40))
    by (rewrite HrP by reg_neq_tac; exact Hr2).
  (* the common prefix of machine steps: loop head .. 0x11074 *)
  assert (HmsPre : msteps source_segs (mkst regs 0x11038 mem rrom)
                          (mkst regsP 0x11074 mem rrom)).
  { eapply mst_step; [reflexivity | exact E1 |].
    eapply mst_step; [reflexivity | exact E2 |].
    eapply mst_step; [reflexivity | exact E3 |].
    eapply mst_step; [reflexivity | exact E4 |].
    eapply mst_step; [reflexivity | exact E5 |].
    eapply mst_step; [reflexivity | exact E6 |].
    eapply msteps_trans; [exact HmsH |].
    eapply mst_step; [reflexivity | exact E7 |].
    exact HmsP. }
  (* --- the shared next-arg continuation at 0x11080 --- *)
  assert (Hout : forall regsO memO,
      mem_ok memO ->
      (forall r : reg, r <> 1 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 ->
         r <> 14 -> r <> 15 -> r <> 16 -> r <> 17 ->
         reg_get regsO r = reg_get regs r) ->
      wexit1 source_segs (mkst regsO 0x11080 memO rrom) bufs code).
  { intros regsO memO HmO HagO.
    eapply msteps_to_wallexit;
      [ apply Htail; rewrite HagO by reg_neq_tac; exact Hr9 | ].
    apply Hcont.
    - exact HmO.
    - regupd_resolve. rewrite HagO by reg_neq_tac. exact Hr8.
    - apply regupd_same.
    - regupd_resolve. rewrite HagO by reg_neq_tac. exact Hr18.
    - regupd_resolve. rewrite HagO by reg_neq_tac. exact Hr19.
    - regupd_resolve. rewrite HagO by reg_neq_tac. exact Hr20.
    - regupd_resolve. rewrite HagO by reg_neq_tac. exact Hr2. }
  (* --- case analysis on the pattern/containment --- *)
  destruct (Nat.eq_dec (length (nth 1 av [])) 0) as [Hnn0 | Hnn].
  - (* empty pattern: always a match *)
    assert (Hcont_b : contains_b (nth i av []) (nth 1 av []) = true).
    { unfold contains_b. rewrite Hnn0. reflexivity. }
    (* 0x11074: beqz a2 taken -> 0x110dc *)
    assert (E8 : RiscvSemantics.step source_segs (mkst regsP 0x11074 mem rrom)
                 = MachineOk (mkst regsP 0x110dc mem rrom)).
    { rewrite (step_beq_tk source_segs regsP 0x11074 mem rrom _ 12 0 _
                 SF_11074 eq_refl SD_11074).
      - wlits. reflexivity.
      - getr_resolve. rewrite Hr12P, Hnn0. apply c_eq_0_of_u.
        rewrite u_ntw by lia. lia. }
    assert (Hr12P0 : reg_get regsP 12%bv = nat_to_word 0)
      by (rewrite Hr12P, Hnn0; reflexivity).
    unfold arg_bufs. rewrite Hcont_b.
    eapply msteps_to_wallexit; [exact HmsPre |].
    chain_step; [reflexivity | exact E8 |].
    apply (source_output i regsP mem bufs code Hmem Hi Hr11P Hr12P0 Hr20P Hr2P).
    intros regsF memF HmF HagF.
    apply (Hout regsF memF HmF).
    intros r Hx1 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17.
    rewrite (HagF r) by assumption. apply HrP; assumption.
  - (* nonempty pattern *)
    assert (Hnn1 : (1 <= length (nth 1 av []))%nat) by lia.
    (* 0x11074: beqz a2 falls through *)
    assert (E8 : RiscvSemantics.step source_segs (mkst regsP 0x11074 mem rrom)
                 = MachineOk (mkst regsP 0x11078 mem rrom)).
    { rewrite (step_beq_ft source_segs regsP 0x11074 mem rrom _ 12 0 _
                 SF_11074 eq_refl SD_11074).
      - wlits. reflexivity.
      - getr_resolve. rewrite Hr12P. apply c_eq_0_false.
        rewrite u_ntw by lia. lia. }
    (* 0x11078: a3 := 0 *)
    set (regsA := regupd regsP 13 (nat_to_word 0)).
    assert (E9 : RiscvSemantics.step source_segs (mkst regsP 0x11078 mem rrom)
                 = MachineOk (mkst regsA 0x1107c mem rrom)).
    { rewrite (step_addi source_segs regsP 0x11078 mem rrom _ 13 0 _
                 SF_11078 eq_refl SD_11078).
      reduce_bv_eqb_ifs. getr_resolve.
      replace (v_addi (Z_to_bv 64 0) (bv_signed (0%bv : bv 12)))
        with (nat_to_word 0) by bveq.
      wlits. reflexivity. }
    destruct (le_lt_dec (length (nth 1 av [])) (length (nth i av [])))
      as [Hle | Hgt].
    + (* nn <= hn: enter the scan loop *)
      assert (Hcont_b : contains_b (nth i av []) (nth 1 av [])
              = scan_from (nth i av []) (nth 1 av []) 0
                  (S (length (nth i av []) - length (nth 1 av [])))).
      { unfold contains_b.
        rewrite (proj2 (Nat.eqb_neq _ 0) Hnn).
        rewrite (proj2 (Nat.ltb_ge _ _) Hle). reflexivity. }
      (* 0x1107c: bgeu a4,a2 taken (hn >= nn) -> the guard at 0x110cc *)
      assert (E10 : RiscvSemantics.step source_segs (mkst regsA 0x1107c mem rrom)
                    = MachineOk (mkst regsA 0x110cc mem rrom)).
      { rewrite (step_bgeu_tk source_segs regsA 0x1107c mem rrom _ 14 12 _
                   SF_1107c eq_refl SD_1107c).
        - wlits. reflexivity.
        - unfold regsA. getr_resolve. rewrite Hr14P, Hr12P.
          rewrite c_ltu_ltb. apply Z.ltb_ge. rewrite !u_ntw by lia. lia. }
      assert (Hr13A : reg_get regsA 13%bv = nat_to_word 0)
        by (unfold regsA; apply regupd_same).
      assert (Hr14A : reg_get regsA 14%bv = nat_to_word (length (nth i av [])))
        by (unfold regsA; rewrite regupd_other by reg_neq_tac; exact Hr14P).
      assert (Hr12A : reg_get regsA 12%bv = nat_to_word (length (nth 1 av [])))
        by (unfold regsA; rewrite regupd_other by reg_neq_tac; exact Hr12P).
      assert (Hr11A : reg_get regsA 11%bv = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) i)
        by (unfold regsA; rewrite regupd_other by reg_neq_tac; exact Hr11P).
      assert (Hr19A : reg_get regsA 19%bv = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1)
        by (unfold regsA; rewrite regupd_other by reg_neq_tac; exact Hr19P).
      destruct (source_scan i Hi H2le mem Hmem
                  (S (length (nth i av []) - length (nth 1 av []))) 0 regsA
                  Hnn1 Hle ltac:(lia)
                  Hr13A Hr14A Hr12A Hr11A Hr19A)
        as [regsS [HagS [H12S HmsS]]].
      assert (HrS : forall r : reg, r <> 1 -> r <> 10 -> r <> 11 -> r <> 12 ->
                      r <> 13 -> r <> 14 -> r <> 15 -> r <> 16 -> r <> 17 ->
                      reg_get regsS r = reg_get regs r).
      { intros r Hx1 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17.
        rewrite (HagS r Hx10 Hx12 Hx13 Hx15 Hx16 Hx17).
        unfold regsA. rewrite regupd_other by assumption.
        apply HrP; assumption. }
      unfold arg_bufs. rewrite Hcont_b.
      destruct (scan_from (nth i av []) (nth 1 av []) 0
                  (S (length (nth i av []) - length (nth 1 av [])))) eqn:Esc.
      * (* match found: the scan lands on the output path *)
        assert (Hr11S : reg_get regsS 11%bv = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) i)
          by (rewrite (HagS 11) by reg_neq_tac; exact Hr11A).
        assert (Hr20S : reg_get regsS 20%bv = Z_to_bv 64 73728)
          by (rewrite HrS by reg_neq_tac; exact Hr20).
        assert (Hr2S : reg_get regsS 2%bv = Z_to_bv 64 (bv_unsigned rsp - 0x40))
          by (rewrite HrS by reg_neq_tac; exact Hr2).
        eapply msteps_to_wallexit; [exact HmsPre |].
        chain_step; [reflexivity | exact E8 |].
        chain_step; [reflexivity | exact E9 |].
        chain_step; [reflexivity | exact E10 |].
        eapply msteps_to_wallexit; [exact HmsS |].
        apply (source_output i regsS mem bufs code Hmem Hi Hr11S H12S Hr20S Hr2S).
        intros regsF memF HmF HagF.
        apply (Hout regsF memF HmF).
        intros r Hx1 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17.
        rewrite (HagF r) by assumption. apply HrS; assumption.
      * (* no match: the scan lands on the next-arg path *)
        cbn [app].
        eapply msteps_to_wallexit; [exact HmsPre |].
        chain_step; [reflexivity | exact E8 |].
        chain_step; [reflexivity | exact E9 |].
        chain_step; [reflexivity | exact E10 |].
        eapply msteps_to_wallexit; [exact HmsS |].
        apply (Hout regsS mem Hmem).
        intros r Hx1 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17.
        apply HrS; assumption.
    + (* hn < nn: no match without scanning *)
      assert (Hcont_b : contains_b (nth i av []) (nth 1 av []) = false).
      { unfold contains_b.
        rewrite (proj2 (Nat.eqb_neq _ 0) Hnn).
        rewrite (proj2 (Nat.ltb_lt _ _) Hgt). reflexivity. }
      (* 0x1107c: bgeu a4,a2 falls through (hn < nn) -> 0x11080 *)
      assert (E10 : RiscvSemantics.step source_segs (mkst regsA 0x1107c mem rrom)
                    = MachineOk (mkst regsA 0x11080 mem rrom)).
      { rewrite (step_bgeu_ft source_segs regsA 0x1107c mem rrom _ 14 12 _
                   SF_1107c eq_refl SD_1107c).
        - wlits. reflexivity.
        - unfold regsA. getr_resolve. rewrite Hr14P, Hr12P.
          rewrite c_ltu_ltb. apply Z.ltb_lt. rewrite !u_ntw by lia. lia. }
      unfold arg_bufs. rewrite Hcont_b. cbn [app].
      eapply msteps_to_wallexit; [exact HmsPre |].
      chain_step; [reflexivity | exact E8 |].
      chain_step; [reflexivity | exact E9 |].
      chain_step; [reflexivity | exact E10 |].
      apply (Hout regsA mem Hmem).
      intros r Hx1 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17.
      unfold regsA. rewrite regupd_other by assumption.
      apply HrP; assumption.
Qed.

(* ================================================================= *)
(* Outer loop and program entry                                       *)
(* ================================================================= *)

(** [sext.w] of a small non-negative index is the identity.  The
    reflective block leaves the loop counter under [v_lw] (that is what
    [sext.w a5,s3] denotes), and no library lemma is stated against that
    spelling. *)
Lemma v_lw_ntw : forall n : nat, (Z.of_nat n < 2 ^ 31)%Z ->
  v_lw (nat_to_word n) = nat_to_word n.
Proof.
  intros n Hn. pose proof (Nat2Z.is_nonneg n).
  unfold v_lw, nat_to_word. rewrite u_Z2bv by lia.
  rewrite bv_swrap_small
    by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia).
  reflexivity.
Qed.

Lemma source_loop : forall m i regs mem,
  mem_ok mem ->
  (2 <= length av)%nat -> (2 <= i)%nat -> (i + m = length av)%nat ->
  reg_get regs 8 = argcN ->
  reg_get regs 9 = nat_to_word i ->
  reg_get regs 18 = Z_to_bv 64 (bv_unsigned rsp + 8) ->
  reg_get regs 19 = cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1 ->
  reg_get regs 20 = Z_to_bv 64 73728 ->
  reg_get regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ->
  wexit1 source_segs (mkst regs 0x11038 mem rrom)
    (grep_bufs (nth 1 av []) (skipn i av)) (Z_to_bv 64 0).
Proof.
  intros m. induction m as [|m IH];
    intros i regs mem Hmem H2le H2i Him Hr8 Hr9 Hr18 Hr19 Hr20 Hr2.
  - (* i = argc: exit the loop, return 0 *)
    assert (Hi : i = length av) by lia.
    rewrite (skipn_all2 av) by lia.
    cbn [grep_bufs flat_map].
    pose proof (valid_argv_len av Hva) as Hargc.
    pose proof u_argcN as HuA.
    pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
    (* 0x11038 .. 0x11044: the loop test fails (i = argc), so main sets
       its exit code to 0 and jumps to the epilogue at 0x11140. *)
    sym_block source_segs 4%nat [false] (@nil expr)
      [((9 : reg), EVar 32); ((8 : reg), EVar 33)]
      [nat_to_word i; argcN] (@nil word) RE HRE.
    { (* blt a5,s0 falls through: i >= argc *)
      rewrite v_lw_ntw by lia.
      rewrite bv_lts_small by (rewrite ?u_ntw by lia; rewrite ?HuA; lia).
      apply Z.ltb_ge. rewrite u_ntw by lia. rewrite HuA. lia. }
    { exact Hr9. }
    { exact Hr8. }
    apply (source_epilogue RE mem (Z_to_bv 64 0) Hmem).
    + sym_regs HRE. exact Hr2.
    + sym_regs HRE. reflexivity.
    + u_norm; lia.
  - (* process argv[i], recurse *)
    assert (Hi : (i < length av)%nat) by lia.
    rewrite (skipn_nth av i [] Hi).
    cbn [grep_bufs flat_map].
    change (flat_map (arg_bufs (nth 1 av [])) (skipn (S i) av))
      with (grep_bufs (nth 1 av []) (skipn (S i) av)).
    apply (source_arg i regs mem _ (Z_to_bv 64 0) Hmem H2le H2i Hi
             Hr8 Hr9 Hr18 Hr19 Hr20 Hr2).
    intros regs' mem' Hm' H8' H9' H18' H19' H20' H2'.
    apply IH; try assumption; lia.
Qed.

(** Program entry, argc >= 2. *)
(** The [SCReadBase] the [ld a0,0(sp)] at 0x1117c raises: argc, out of
    the initial stack image. *)
Ltac s_read_argc :=
  eexists; split;
  [ match goal with |- rdn _ _ ?a _ = _ =>
      replace a with rsp by (apply bv_eq; u_norm; lia) end;
    rewrite rdn_wrap_stack_above by lia;
    apply read_argc; exact source_bsb_nw
  | apply bytes_le_n_to_le_8 ].

(** The [envp] pointer as the reflective block computes it.  The
    executor leaves [addi a2,a2,8] over an [add]/[slli] pair in the
    [alu64]/[v_sll] spelling, which no library lemma is stated against;
    one rewrite puts it back into [envp_ptr] so the block's exit memory
    is literally [fmem]. *)
Lemma envp_ptr_alu :
  Z_to_bv 64 (bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
                             (v_sll argcN (Z_to_bv 64 3))) + 8) = envp_ptr.
Proof. rewrite alu_add. exact envp_ptr_eq. Qed.

(** Program entry, argc >= 2.  The run's segment list is the image's
    followed by the vDSO pair; the derivation below is the image's own,
    carried over whole. *)
Lemma source_wexit_ge2 : (2 <= length av)%nat ->
  wexit1 (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) 0x11174 source_phdrs
       rsp rmb rrnd inp)
    (grep_bufs (nth 1 av []) (skipn 2 av)) (Z_to_bv 64 0).
Proof.
  intros H2le. apply to_wallexit_run.
  pose proof (valid_argv_len av Hva) as Hargc.
  pose proof u_argcN as HuA.
  pose proof (source_ptr_bounds 1 ltac:(lia)) as [Hgep Hltp].
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  rewrite init_mkst. norm_pc.
  (* 0x11174 .. 0x11034: _start (argc, environ, call main) and main's
     prologue (frame, six callee-save stores, the [pat] pointer), in
     ONE block ending at the outer loop head 0x11038.  The five
     callee-saved registers that get stored are pinned to 0 so the
     frame stores land in [fmem]'s spelling. *)
  sym_block source_segs 25%nat [false] [EVar 33; EVar 34]
    [((2 : reg), EVar 32); ((8 : reg), ELit 0); ((9 : reg), ELit 0);
     ((18 : reg), ELit 0); ((19 : reg), ELit 0); ((20 : reg), ELit 0)]
    [rsp] [argcN; cat_argv_ptr (ed_top rrnd) av ev (in_execfn inp) 1] RE HRE.
  all: try solve [ solve_store_ok ].
  { (* ld s3,8(a1): the [pat] pointer argv[1] *)
    eexists; split;
    [ match goal with |- rdn _ _ ?a _ = _ =>
        replace a with (rsp + nat_to_word (8 + 8 * 1))
          by (rewrite word_add_nat; apply bv_eq; u_norm; lia) end;
      rewrite rdn_wrap_stack_above by (rewrite word_add_nat; u_norm; lia);
      apply read_argv_ptr_k; [lia | exact source_bsb_nw]
    | apply bytes_le_n_to_le_8 ]. }
  { (* bge a5,a0 falls through: argc >= 2 *) sym_br. }
  { (* sd a2,0(t1): the [environ] slot is writable *)
    apply source_store_ok; u_norm; lia. }
  { (* ld a0,0(sp): argc *) s_read_argc. }
  (* the block's exit memory IS [fmem] *)
  match goal with
  | |- to_wexit _ (mkst _ _ ?m _) _ _ =>
    replace m with fmem
      by (unfold fmem, wmem; rewrite envp_ptr_alu; reflexivity)
  | |- wexit1 _ (mkst _ _ ?m _) _ _ =>
    replace m with fmem
      by (unfold fmem, wmem; rewrite envp_ptr_alu; reflexivity) end.
  apply (source_loop (length av - 2) 2); try assumption; try lia.
  - exact fmem_ok.
  - sym_regs HRE. reflexivity.
  - sym_regs HRE. bveq.
  - sym_regs HRE. reflexivity.
  - sym_regs HRE. reflexivity.
  - sym_regs HRE. bveq.
  - sym_regs HRE. reflexivity.
Qed.

(** Program entry, argc < 2: exit 2, no output. *)
Lemma source_wexit_lt2 : (length av < 2)%nat ->
  wexit1 (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) 0x11174 source_phdrs
       rsp rmb rrnd inp)
    [] (Z_to_bv 64 2).
Proof.
  intros Hlt2. apply to_wallexit_run.
  pose proof (valid_argv_len av Hva) as Hargc.
  pose proof u_argcN as HuA.
  pose proof rsp_lo_num as Hlo. pose proof rsp_hi_num as Hhi.
  rewrite init_mkst. norm_pc.
  (* 0x11174 .. 0x111a4: the whole run.  _start reads argc, publishes
     [environ] and calls main; main's [bge a5,a0] is TAKEN (argc <= 1),
     so it returns 2 immediately and the block stops at the exit
     [ecall]. *)
  sym_block source_segs 18%nat [true] [EVar 33]
    [((2 : reg), EVar 32)]
    [rsp] [argcN] RE HRE.
  { (* bge a5,a0 taken: 1 >= argc *) sym_br. }
  { (* sd a2,0(t1): the [environ] slot is writable *)
    apply source_store_ok; u_norm; lia. }
  { (* ld a0,0(sp): argc *) s_read_argc. }
  (* 0x111a4: ecall -- exit(2) *)
  chain_step;
    [ reflexivity | apply (step_ecall _ _ _ _ _ _ SF_111a4 eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRE. vm_closed.
  - sym_regs HRE. reflexivity.
  - u_norm; lia.
Qed.

End SourceProof.
