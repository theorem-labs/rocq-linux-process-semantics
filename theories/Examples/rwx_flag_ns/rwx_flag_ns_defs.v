(** * rwx-flag-ns: shared definitions and image facts.

    PROOF-SIDE FILE (not part of the trusted specification).

    Both binaries store 5 into a writable global byte, load it back, and
    exit with it: no output, exit code 5, on every input.

    What the example is FOR is the source binary's layout: it is linked
    (source/rwx.lds, via source/ldflags.txt) into a SINGLE RWX LOAD
    segment holding the ELF headers, .text, and the writable data — the
    merged layout GNU ld's default [-z noseparate-code] produces — so
    every instruction fetch goes through the model's overlay-aware w+x
    fetch ([RiscvSemantics.code_read_ov]), and both of its
    stores (musl's [__environ] slot in .bss, and [flag]) land in the
    same segment the code executes from.  The proof carries
    [WxExec.mem_clear] — "the overlay misses the .text range
    [0x10078, 0x100e4)" — as the frame invariant that lets the
    generated static [fetch_word_wx] facts close each step's fetch.
    The target is an ordinary lld-linked binary (immutable r-x code),
    so its side of the proof is the standard static-fetch machinery. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import rwx_flag_ns_code.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(* ######################################################################### *)
(* Entry points                                                              *)
(* ######################################################################### *)

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x10078%N.
Proof. vm_compute. reflexivity. Qed.

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x1001190%N.
Proof. vm_compute. reflexivity. Qed.

(* ######################################################################### *)
(* The source image is ALL w+x: the static fetch declines everywhere         *)
(* ######################################################################### *)

Lemma source_no_ro_exec : no_ro_exec source_segs = true.
Proof. vm_compute. reflexivity. Qed.

(** The source's .text range: the [mem_clear] frame invariant is stated
    over it, and every fetched pc lies inside it. *)
Definition stext_lo : Z := 0x10078%Z.
Definition stext_hi : Z := 0x100e4%Z.

(* ######################################################################### *)
(* Store legality                                                            *)
(* ######################################################################### *)

(** The source's one RWX segment covers [0x10000, 0x11000) (page-rounded)
    and is writable with a snapshot byte for every address, so [wview]
    is defined on all of it — both stores ([__environ] at 0x100e8,
    [flag] at 0x100e4) are legal. *)
Lemma source_wseg : wseg_ok source_segs (0x10000 : word) 4096 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma source_store_ok : forall (m : word -> option byte) (a : word) (n : nat),
  (0x10000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x11000)%Z ->
  store_ok source_segs m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply store_ok_window with (base := 0x10000%Z) (hi := 0x11000%Z);
    [ | | | exact source_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.

(** The target's rw- data segment covers [0x1002000, 0x1003000). *)
Lemma target_wseg : wseg_ok target_segs (0x1002000 : word) 4096 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma target_store_ok : forall (m : word -> option byte) (a : word) (n : nat),
  (0x1002000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x1003000)%Z ->
  store_ok target_segs m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply store_ok_window with (base := 0x1002000%Z) (hi := 0x1003000%Z);
    [ | | | exact target_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.

(* ######################################################################### *)
(* The run's segment list: the image's own, then the vDSO pair               *)
(* ######################################################################### *)

(** A run reads [Run.run_segments]: the image's LOAD segments followed by
    the vDSO pair.  The generated fetch facts and the store lemmas above
    are stated over the image's own list, and they carry over to the
    run's list unchanged because every reader they go through —
    [find_segment] under [code_read], [code_read_wx] and [wview] — scans
    head first, so a hit among the image's segments is the same hit in
    any longer list. *)
Lemma find_segment_app : forall segs vt a n seg,
  find_segment segs a n = Some seg -> find_segment (segs ++ vt) a n = Some seg.
Proof.
  induction segs as [|s rest IH]; intros vt a n seg H; [discriminate|].
  cbn [find_segment app] in *.
  match goal with |- (if ?c then _ else _) = _ => destruct c end;
    [exact H | exact (IH vt a n seg H)].
Qed.

Lemma code_read_app : forall segs vt (a : word) n bs,
  code_read segs a n = Some bs -> code_read (segs ++ vt) a n = Some bs.
Proof.
  intros segs vt a n bs H. unfold code_read in *.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf;
    [|discriminate].
  rewrite (find_segment_app segs vt _ _ seg Hf). exact H.
Qed.

Lemma code_read_wx_app : forall segs vt (a : word) n bs,
  code_read_wx segs a n = Some bs -> code_read_wx (segs ++ vt) a n = Some bs.
Proof.
  intros segs vt a n bs H. unfold code_read_wx in *.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf;
    [|discriminate].
  rewrite (find_segment_app segs vt _ _ seg Hf). exact H.
Qed.

Lemma fetch_word_app : forall segs vt (pc : word) w,
  fetch_word segs pc = Some w -> fetch_word (segs ++ vt) pc = Some w.
Proof.
  intros segs vt pc w H. unfold fetch_word in *.
  destruct (negb (Z.eqb (bv_unsigned pc mod 2) 0)%Z); [discriminate|].
  destruct (code_read segs pc 4) as [bs|] eqn:Hc; [|discriminate].
  rewrite (code_read_app segs vt pc 4 bs Hc). exact H.
Qed.

Lemma fetch_word_wx_app : forall segs vt (pc : word) w,
  fetch_word_wx segs pc = Some w -> fetch_word_wx (segs ++ vt) pc = Some w.
Proof.
  intros segs vt pc w H. unfold fetch_word_wx in *.
  destruct (negb (Z.eqb (bv_unsigned pc mod 2) 0)%Z); [discriminate|].
  destruct (code_read_wx segs pc 4) as [bs|] eqn:Hc; [|discriminate].
  rewrite (code_read_wx_app segs vt pc 4 bs Hc). exact H.
Qed.

Lemma wview_app : forall segs vt m (a : word) b,
  wview segs m a = Some b -> wview (segs ++ vt) m a = Some b.
Proof.
  intros segs vt m a b H. unfold wview in *.
  destruct (m a) as [b'|]; [exact H|].
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hf; [|discriminate].
  rewrite (find_segment_app segs vt _ _ seg Hf). exact H.
Qed.

Lemma store_ok_app : forall segs vt m n (a : word),
  store_ok segs m a n = true -> store_ok (segs ++ vt) m a n = true.
Proof.
  intros segs vt m n. induction n as [|n IH]; intros a H; [reflexivity|].
  cbn [store_ok] in *.
  destruct (wview segs m a) as [b|] eqn:Hw; [|discriminate].
  rewrite (wview_app segs vt m a b Hw). exact (IH _ H).
Qed.

(** The source's all-w+x fact at the run's list: neither vDSO segment is
    executable (the model does not run the vDSO's bytes; see
    [Run.vdso_segments]), so the static fetch still declines
    everywhere. *)
Lemma no_ro_exec_app : forall segs vt,
  no_ro_exec segs = true -> no_ro_exec vt = true -> no_ro_exec (segs ++ vt) = true.
Proof.
  intros segs vt H1 H2. unfold no_ro_exec in *. rewrite forallb_app, H1, H2. reflexivity.
Qed.

Local Transparent vdso_segments.
Lemma no_ro_exec_vdso : forall kb sp mbase, no_ro_exec (vdso_segments kb sp mbase) = true.
Proof.
  intros kb sp mbase. unfold vdso_segments. cbv zeta.
  match goal with |- no_ro_exec (if ?c then _ else _) = _ => destruct c end;
    reflexivity.
Qed.
Local Opaque vdso_segments.

Lemma source_run_no_ro_exec : forall inp sp mbase,
  no_ro_exec (run_segments source_segs inp sp mbase) = true.
Proof.
  intros inp sp mbase. unfold run_segments.
  apply no_ro_exec_app; [exact source_no_ro_exec | apply no_ro_exec_vdso].
Qed.
