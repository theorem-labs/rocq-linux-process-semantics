(** * modprint-ns: shared spec, pure lemmas and image probes.

    PROOF-SIDE FILE (not part of the trusted specification).

    Both binaries have exactly ONE observable behavior, for every input:
    write(1, [digit; '\n'], 2) where digit = '0' + (argc mod 7), then
    exit 0.  There is no input-dependent control flow, so unlike every
    other example in the tree there is no case split at all — [Proof.v]
    is a single application of [cat_strong_equiv_te].

    The modulus is not a literal in either binary: both load a 32-bit
    all-zero word from .bss (a volatile read, so neither compiler folds
    it away) and add 7.  That load is the reason this example exists —
    it is the tree's only use of [SeqExec.step_lw_zero], and the
    [remu] it feeds is the only use of [SeqExec.v_remu_small].

    Conventions follow the other examples: bytes are [byte = bv 8],
    machine values [word = bv 64], unbounded address bookkeeping in [Z]
    over [bv_unsigned]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec NumPrint StepTac StreamSim StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Examples.modprint_ns Require Import modprint_ns_code.
From LinuxProcessSemantics.Examples.modprint_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.modprint_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(* ######################################################################### *)
(* The shared observable-behavior spec                                       *)
(* ######################################################################### *)

(** The newline the digit is followed by. *)
Definition nl : byte := Z_to_bv 8 10.

(** The single buffer both binaries write: the decimal rendering of
    [argc mod 7], then a newline.  Phrased over [NumPrint.udec] rather
    than the one byte it always reduces to, so the spec says what the
    program means ("print this number in decimal") rather than what the
    compiler happened to emit. *)
Definition mod_buf (argc : Z) : list byte := udec (argc mod 7) ++ [nl].

Definition mod_bufs (argc : Z) : list (list byte) := [mod_buf argc].

(* ######################################################################### *)
(* Pure lemmas about the spec                                                *)
(* ######################################################################### *)

(** A value below 10 renders as its single ASCII digit.  [udec_single]
    covers 1..9; 0 is [udec]'s own base case. *)
Lemma udec_digit : forall r, (0 <= r < 10)%Z -> udec r = [Z_to_bv 8 (48 + r)].
Proof.
  intros r Hr.
  destruct (Z.eq_dec r 0) as [->|Hnz].
  - unfold udec. cbn. reflexivity.
  - apply udec_single. lia.
Qed.

(** [argc mod 7] is always a single digit, so the spec buffer is always
    the two bytes the binaries actually store and emit. *)
Lemma mod_buf_bytes : forall argc, (0 <= argc)%Z ->
  mod_buf argc = [Z_to_bv 8 (48 + argc mod 7); nl].
Proof.
  intros argc Hargc.
  unfold mod_buf. rewrite udec_digit by (pose proof (Z.mod_pos_bound argc 7); lia).
  reflexivity.
Qed.

(** The one range fact both per-binary proofs need about the remainder,
    stated once here: [modprint_ns_source.v] and [modprint_ns_target.v]
    both open with [pose proof (mod_rem_range ...)] rather than each
    re-deriving it from [Z.mod_pos_bound]. *)
Lemma mod_rem_range : forall argc, (0 <= argc)%Z -> (0 <= argc mod 7 < 7)%Z.
Proof. intros argc H. apply Z.mod_pos_bound. lia. Qed.

(* ######################################################################### *)
(* Value lemmas for the two arithmetic instructions                          *)
(* ######################################################################### *)

(** [addiw a5,a5,7] on the all-zero loaded word: the divisor is 7. *)
Lemma v_addiw_zero_7 : v_addiw (Z_to_bv 64 0) 7 = Z_to_bv 64 7.
Proof. bveq. Qed.

(** [remu a0,a0,a5] with the divisor 7: THE use of [v_remu_small].
    Stated over an arbitrary in-range dividend, which is [argc]. *)
Lemma v_remu_7 : forall n : Z, (0 <= n)%Z -> (n < 2^64)%Z ->
  v_remu (Z_to_bv 64 n) (Z_to_bv 64 7) = Z_to_bv 64 (n mod 7).
Proof.
  intros n Hlo Hhi.
  pose proof (Z.mod_pos_bound n 7 ltac:(lia)).
  apply bv_eq.
  rewrite v_remu_small by (rewrite u_Z2bv by lia; lia).
  rewrite !u_Z2bv by lia. reflexivity.
Qed.

(** [addiw a0,a0,48]: turn the remainder into its ASCII digit. *)
Lemma v_addiw_digit : forall r : Z, (0 <= r < 7)%Z ->
  v_addiw (Z_to_bv 64 r) 48 = Z_to_bv 64 (48 + r).
Proof.
  intros r Hr. apply bv_eq. unfold v_addiw.
  rewrite (u_Z2bv r) by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  rewrite !u_Z2bv by lia. lia.
Qed.

(** The target reaches the same digit with a 64-bit [addi] instead of
    the source's [addiw]. *)
Lemma v_addi_digit : forall r : Z, (0 <= r < 7)%Z ->
  v_addi (Z_to_bv 64 r) 48 = Z_to_bv 64 (48 + r).
Proof.
  intros r Hr. apply bv_eq. unfold v_addi.
  rewrite (u_Z2bv r) by lia.
  rewrite !u_Z2bv by lia. lia.
Qed.

(** The byte the [sb] stores is exactly the spec's digit byte. *)
Lemma stored_digit : forall r : Z, (0 <= r < 7)%Z ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (48 + r))) = Z_to_bv 8 (48 + r).
Proof. intros r Hr. rewrite u_Z2bv by lia. reflexivity. Qed.

(* ######################################################################### *)
(* Store legality                                                            *)
(* ######################################################################### *)

(** Source: under [-z separate-code] the read-only part of the image is
    THREE segments — segment 000 ([0x10000, 0x11000), r--, the ELF headers
    and .riscv.attributes), segment 001 ([0x11000, 0x12000), r-x, .text)
    and segment 002 ([0x12000, 0x13000), r--, .eh_frame) — and segment
    003 (0x13000, .sdata/.sbss) is the rw- one.  A store at/above 0x13000
    avoids all three read-only segments. *)
Lemma source_avoids_ro : forall (a : word) (n : Z), (0x13000 <= bv_unsigned a)%Z ->
  range_avoids_ro_segs source_segs (bv_unsigned a) n = true.
Proof.
  intros a n Ha.
  apply range_avoids_ro_above with (data_base := 0x13000%Z);
    [vm_compute; reflexivity | exact Ha].
Qed.

(** The source image's WRITABLE window: the rw- segment covers
    [0x13000, 0x14000) and the snapshot carries a byte for every address in
    it (.bss is zero-filled in the .hex), so [wview] is defined there
    whatever the overlay holds — a store into .data/.bss needs no
    prior write.  That is the [store_ok] side condition machine stores
    now carry; stack targets go through the RLIMIT_STACK window
    ([solve_store_ok]) instead.

    A run reads [Run.run_segments]: the image's segments followed by
    the vDSO pair.  The store bounds and the image read-backs below are
    stated over [source_segs ++ vt] for any appended [vt]
    ([RunSegmentsLift]): every reader scans the image's segments first. *)
Lemma source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma source_store_ok : forall vt (m : word -> option byte) (a : word) (n : nat),
  (0x13000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x14000)%Z ->
  store_ok (source_segs ++ vt) m a n = true.
Proof.
  intros vt m a n Hlo Hhi. apply store_ok_app.
  eapply store_ok_window with (base := 0x13000%Z) (hi := 0x14000%Z);
    [ | | | exact source_data_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.

(** Target: segments 000 (0x1000000, r--) and 001 (0x1001000, r-x) are
    read-only, segment 002 (0x1002000) is rw-.  A store at/above
    0x1002000 avoids both read-only segments. *)
Lemma target_avoids_ro : forall (a : word) (n : Z), (0x1002000 <= bv_unsigned a)%Z ->
  range_avoids_ro_segs target_segs (bv_unsigned a) n = true.
Proof.
  intros a n Ha.
  unfold target_segs, TargetMemImage_loaded_segments, range_avoids_ro_segs.
  cbn [forallb].
  change (seg_writable TargetMemImage_segment_000) with false.
  change (seg_writable TargetMemImage_segment_001) with false.
  change (seg_writable TargetMemImage_segment_002) with true.
  change (Z.of_N (seg_base TargetMemImage_segment_000)
          + Z.of_N (seg_size TargetMemImage_segment_000))%Z with 0x1001000%Z.
  change (Z.of_N (seg_base TargetMemImage_segment_001)
          + Z.of_N (seg_size TargetMemImage_segment_001))%Z with 0x1002000%Z.
  assert (H0 : Z.ltb (bv_unsigned a) 0x1001000 = false) by (apply Z.ltb_ge; lia).
  assert (H1 : Z.ltb (bv_unsigned a) 0x1002000 = false) by (apply Z.ltb_ge; lia).
  rewrite H0, H1. rewrite !andb_false_r.
  cbn [negb orb andb]. reflexivity.
Qed.

(** The target image's WRITABLE window: the rw- segment covers
    [0x1002000, 0x1003000) and the snapshot carries a byte for every address in
    it (.bss is zero-filled in the .hex), so [wview] is defined there
    whatever the overlay holds — a store into .data/.bss needs no
    prior write.  That is the [store_ok] side condition machine stores
    now carry; stack targets go through the RLIMIT_STACK window
    ([solve_store_ok]) instead. *)
Lemma target_data_wseg : wseg_ok target_segs (0x1002000 : word) 4096 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma target_store_ok : forall vt (m : word -> option byte) (a : word) (n : nat),
  (0x1002000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x1003000)%Z ->
  store_ok (target_segs ++ vt) m a n = true.
Proof.
  intros vt m a n Hlo Hhi. apply store_ok_app.
  eapply store_ok_window with (base := 0x1002000%Z) (hi := 0x1003000%Z);
    [ | | | exact target_data_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.

(* ######################################################################### *)
(* Image probes                                                              *)
(* ######################################################################### *)

(** Source: [modulus_base] in .sbss at 0x13008 — four zero bytes.  This
    is what makes [step_lw_zero] applicable. *)
Lemma srom_zero4 : forall vt, rdn (source_segs ++ vt) (fun _ => None) 0x13008 4%nat
  = Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof. intros vt. apply rdn_lift. vm_refl. Qed.

(** Source: the newline byte of [out] in .sdata at 0x13001.  (Byte
    0x13000 is overwritten by the [sb] before the write, so only this
    one is read out of the image.) *)
Lemma srom_nl : forall vt, rdn (source_segs ++ vt) (fun _ => None) 0x13001 1%nat = Some [nl].
Proof. intros vt. apply rdn_lift. vm_refl. Qed.

(** Target: [modulus_base] in .bss at 0x10021f0 — four zero bytes. *)
Lemma arom_zero4 : forall vt, rdn (target_segs ++ vt) (fun _ => None) 0x10021f0 4%nat
  = Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof. intros vt. apply rdn_lift. vm_refl. Qed.

(** Target: the newline byte of [out] in .data at 0x10021ed. *)
Lemma arom_nl : forall vt, rdn (target_segs ++ vt) (fun _ => None) 0x10021ed 1%nat = Some [nl].
Proof. intros vt. apply rdn_lift. vm_refl. Qed.

(* ######################################################################### *)
(* Entry points                                                              *)
(* ######################################################################### *)

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x11044%N.
Proof. vm_compute. reflexivity. Qed.

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x1001190%N.
Proof. vm_compute. reflexivity. Qed.
