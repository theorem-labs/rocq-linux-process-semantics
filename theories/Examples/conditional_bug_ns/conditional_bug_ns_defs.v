(** * conditional-bug-ns: shared definitions, tactics and small facts.

    PROOF-SIDE FILE (not part of the trusted specification).

    Both binaries dispatch on the FIRST byte of argv[1]:
      argc < 2        -> exit 2, no output
      first byte 'n'  -> exit 0, no output
      first byte 'h'  -> write "hello\n", exit 0
      first byte 'o'  -> volatile load from unmapped address 64
                         (all source executions error; target is freed)
      anything else   -> exit 3, no output.

    Conventions: bytes are [byte = bv 8],
    machine values [word = bv 64]; unbounded address bookkeeping is in [Z]
    over [bv_unsigned]; computed stack addresses use the canonical
    [Z_to_bv 64 (...)] form, pc values the numeral-literal form.

    A run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  The store bound and the image read-backs below are stated
    over [segs ++ vt] for any appended [vt] ([RunSegmentsLift]); the
    source's fault at address 64 stays a fault there because the pair
    sits at or above [page_size] ([RunSegmentsLift.vdso_find_low]). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec ErrEscape StepTac StreamSim StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Examples.conditional_bug_ns Require Import conditional_bug_ns_code.
From LinuxProcessSemantics.Examples.conditional_bug_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.conditional_bug_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(* ######################################################################### *)
(* The shared observable-behavior spec                                       *)
(* ######################################################################### *)

(* [byte_at] (byte [k] of string [s] as laid out in memory, [s] then a
   NUL) now lives in CatExec. *)

(** "hello\n" *)
Definition hello : list byte :=
  [Z_to_bv 8 104; Z_to_bv 8 101; Z_to_bv 8 108;
   Z_to_bv 8 108; Z_to_bv 8 111; Z_to_bv 8 10].

(** The only thing either binary ever writes is that fixed six-byte
    string, so every buffer this example emits is well inside the
    transfer size the model judges ([Uaccess.rw_bytes_max]). *)
Lemma hello_modeled : buf_modeled hello.
Proof. unfold buf_modeled, hello, rw_bytes_max. cbn [length]. lia. Qed.

Lemma hello_bufs_modeled : bufs_modeled [hello].
Proof.
  apply bufs_modeled_single, hello_modeled.
Qed.

Lemma nil_bufs_modeled : bufs_modeled [].
Proof. unfold bufs_modeled. apply Forall_nil. Qed.

(* ######################################################################### *)
(* Shared small facts                                                        *)
(* ######################################################################### *)

(* valid_argv_len, valid_argv_str_bytes, byte_at_bound now live in CatExec. *)

(** Close a CLOSED word/byte equation by unsigned comparison. *)

(** The wrapping word/nat offset add in the canonical [Z_to_bv] form
    (hypothesis-free: both sides wrap identically).  Same bridge as in
    grep_args_ns — lift to Common if a third example needs it. *)

(** [bv_unsigned] of a byte zero-extended into a word. *)

(** A byte-literal disequality transfers to the [Z] level. *)

(** The dispatch compares the zero-extended loaded byte against a
    zero-extended literal: reflect a byte-literal disequality. *)

(** Sealed [Z.of_nat] equation for [valid_envp]'s large literal
    (companion of CatExec's [of_nat_131071]/[of_nat_2097152]). *)

(* ######################################################################### *)
(* Step-chaining tactics (as in grep_args_ns)                               *)
(* ######################################################################### *)

(* [norm_pc]/[stepi]/[stepj]/[sp_norm]/[stepi_at] now live in
   Common/StepTac.v (imported above). *)

(* ######################################################################### *)
(* Store legality                                                            *)
(* ######################################################################### *)

(** Source: a store target at/above the end of the read-only segments
    passes the read-only-avoidance check (the rw data segment is exempt).
    After the [-z separate-code] relink there are THREE of them — r--
    headers [0x10000, 0x11000), r-x text [0x11000, 0x12000) and r--
    .rodata + .eh_frame [0x12000, 0x13000) — so the rw- data segment,
    and the first writable address, start at 0x13000.  Discharged by
    [StepTac.range_avoids_ro_above], which is generic in the segment
    list, so a change in the number of read-only segments only moves
    the [vm_compute] check. *)
Lemma source_avoids_ro : forall (a : word) (n : Z), (0x13000 <= bv_unsigned a)%Z ->
  range_avoids_ro_segs source_segs (bv_unsigned a) n = true.
Proof.
  intros a n Ha.
  apply range_avoids_ro_above with (data_base := 0x13000%Z);
    [vm_compute; reflexivity | exact Ha].
Qed.


(** Target: both segments are read-only; a store target at/above the end
    of the last segment avoids both. *)
Lemma target_avoids_ro : forall (a : word) (n : Z), (0x1002000 <= bv_unsigned a)%Z ->
  range_avoids_ro_segs target_segs (bv_unsigned a) n = true.
Proof.
  intros a n Ha.
  unfold target_segs, TargetMemImage_loaded_segments.
  apply range_avoids_two; apply Z.ltb_ge.
  - change (Z.of_N (seg_base TargetMemImage_segment_000)
            + Z.of_N (seg_size TargetMemImage_segment_000))%Z with 0x1001000%Z.
    lia.
  - change (Z.of_N (seg_base TargetMemImage_segment_001)
            + Z.of_N (seg_size TargetMemImage_segment_001))%Z with 0x1002000%Z.
    lia.
Qed.

(** The source image's WRITABLE window: the rw- data segment covers
    [0x13000, 0x14000) and the snapshot carries a byte for every
    address in it (.bss is zero-filled in the .hex), so [wview] is
    defined there for EVERY overlay — the segment fallback needs no
    prior write.  That is exactly what a store into .data/.bss has to
    show now that [store_ok] bounds machine stores; stack targets are
    covered by the RLIMIT_STACK window instead ([solve_store_ok]).
    The target image has no writable segment at all, so all of its
    stores are stack stores. *)
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

(* ######################################################################### *)
(* ROM facts                                                                 *)
(* ######################################################################### *)

(** "hello\n" in the source image at 0x12000. *)
Lemma srom_hello : forall vt, rdn (source_segs ++ vt) (fun _ => None) 0x12000 6%nat = Some hello.
Proof. intros vt. apply rdn_lift. vm_refl. Qed.

(** "hello\n" in the target image at 0x1000158. *)
Lemma arom_hello : forall vt, rdn (target_segs ++ vt) (fun _ => None) 0x1000158 6%nat = Some hello.
Proof. intros vt. apply rdn_lift. vm_refl. Qed.

(** Address 64 is below every loaded segment of the source image and
    below the vDSO pair of every run: unmapped, the buggy load faults.
    (Stated at the [Z_to_bv] form the faulting-address computation
    produces.) *)
Lemma srom_64_find_run : forall kb sp mb,
  find_segment (source_segs ++ vdso_segments kb sp mb) (bv_unsigned (Z_to_bv 64 64)) 1
  = None.
Proof.
  intros kb sp mb. rewrite find_segment_append.
  replace (find_segment source_segs (bv_unsigned (Z_to_bv 64 64)) 1) with (@None Segment)
    by (vm_compute; reflexivity).
  cbn beta iota. apply vdso_find_low. vm_compute. reflexivity.
Qed.

Lemma srom_64_none_run : forall kb sp mb,
  rdn (source_segs ++ vdso_segments kb sp mb) (fun _ => None) (Z_to_bv 64 64) 1%nat = None.
Proof.
  intros kb sp mb. cbn [rdn]. unfold seg_rom, memory_read.
  change (Z.of_N 1) with 1%Z. rewrite srom_64_find_run. reflexivity.
Qed.

(** ... and no byte of it is a vvar byte, so the load is a fault, not
    the model's decline. *)
Lemma vvar_64_run : forall kb sp mb,
  range_meets_vvar (source_segs ++ vdso_segments kb sp mb) (Z_to_bv 64 64) 1%nat = false.
Proof.
  intros kb sp mb. cbn [range_meets_vvar]. unfold vvar_byte_at.
  rewrite srom_64_find_run. reflexivity.
Qed.

(* ######################################################################### *)
(* Entry points                                                              *)
(* ######################################################################### *)

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x110a4%N.
Proof. vm_compute. reflexivity. Qed.

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x1001160%N.
Proof. vm_compute. reflexivity. Qed.
