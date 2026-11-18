(** * Examples.measure_lib_demo.FileGeometricPrefix — the header-conditioned
      file family, worked

    DEMO FILE (not part of the trusted specification, and not installed).
    [MeasureLib.file_geometric] varies the CONTENTS OF ONE FILE over a
    fixed environment, every byte uniform.  [MeasureLib.file_geometric_prefix]
    fixes the first bytes of that file to a HEADER the task names and
    spreads the geometric source over what follows.  This file
    instantiates it at a seven-byte header and carries it through to a
    [Measure.weight_bound_T], beside the whole-file family's own demo.

    ** Why a task reaches for this one rather than the whole-file one

    A driver that parses a header before it hands the rest of the file
    to the library under test rejects almost every file the whole-file
    family weighs: the header's bytes are uniform there too, so only the
    sliver of files whose random header happens to parse reaches the
    library, and a bound over the whole-file family prices the driver's
    reject path.  [file_demo_prefix_header_dilution] below is that
    statement as arithmetic: the very same core — the header followed by
    nothing — weighs the stop weight under this family and the stop
    weight times a seventh power of a tiny number under the whole-file
    family.

    ** The header, and what is fixed

    The header is the shape a length-prefixed driver reads: a two-byte
    little-endian length word saying "one", the one configuration byte
    it announces, and a four-byte all-zero flags word.  Nothing here
    depends on that reading; it is seven bytes the family holds fixed.

    ** The argv/path coupling, discharged by construction

    As for the whole-file family, the path is passed ONCE through
    [MeasureLib.file_geometric_prefix_argv1], and
    [file_demo_prefix_argv_names_path] is the receipt.

    ** The empty header

    [file_demo_prefix_nil_collapse] checks, by computation at a concrete
    core, that the family at the EMPTY header is the whole-file family:
    the general lemma is [MeasureLib.file_geometric_prefix_nil_pointwise],
    and the numeric check is here so that a reader sees a number and not
    only a [Qeq].

    Nothing exhibited here is claimed VALID and nothing is claimed
    rejected by any classifier. *)

From Stdlib Require Import ZArith NArith List QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  FinInput Measure MeasureLib.
From LinuxProcessSemantics.EquivalenceDefinition Require Classifier.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The task's fixed data: a program, the path it is given, the base, and
   the header
   ========================================================================= *)

(** The program's own name and the path it is invoked on: ["wc"] and
    ["/in"], as in the whole-file demo. *)
Definition file_demo_prefix_prog : list byte := [Z_to_bv 8 119; Z_to_bv 8 99].
Definition file_demo_prefix_path : Fs.path :=
  [Z_to_bv 8 47; Z_to_bv 8 105; Z_to_bv 8 110].

Definition file_demo_prefix_envp : list (list byte) := [].
Definition file_demo_prefix_fs0 : Fs.Fs := Fs.fs_empty.
Definition file_demo_prefix_stdin : list byte := [].

(** THE HEADER: seven bytes.  [01 00] is a little-endian length word of
    one, [2a] the one configuration byte, [00 00 00 00] the flags. *)
Definition file_demo_hdr : list byte :=
  [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 42;
   Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].

Lemma file_demo_hdr_length : length file_demo_hdr = 7%nat.
Proof. reflexivity. Qed.

(** The stop weight: one in two hundred fifty-seven, chosen so that
    [1 - p] is [256 / 257] and the per-byte factor [(1 - p) / 256] is
    exactly [1 / 257] — every number below is a power of [257]. *)
Definition file_demo_prefix_p : Q := (1 # 257)%Q.

Lemma file_demo_prefix_p_nonneg : (0 <= file_demo_prefix_p)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma file_demo_prefix_p_le_1 : (file_demo_prefix_p <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

(** THE DISTRIBUTION, through the coupled constructor. *)
Definition file_demo_prefix_cd : CoreDistribution :=
  file_geometric_prefix_argv1 file_demo_hdr file_demo_prefix_p
    file_demo_prefix_prog file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin
    file_demo_prefix_p_nonneg file_demo_prefix_p_le_1.

Definition file_demo_prefix_argv : list (list byte) :=
  path_argv file_demo_prefix_prog file_demo_prefix_path.

Lemma file_demo_prefix_mass_is_one : cd_mass file_demo_prefix_cd = 1%Q.
Proof. reflexivity. Qed.

Lemma file_demo_prefix_argv_names_path :
  argv_names_path file_demo_prefix_argv file_demo_prefix_path
  /\ file_demo_prefix_cd
     = file_geometric_prefix file_demo_hdr file_demo_prefix_p
         file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
         file_demo_prefix_path file_demo_prefix_stdin
         file_demo_prefix_p_nonneg file_demo_prefix_p_le_1.
Proof.
  exact (file_geometric_prefix_argv1_names_path file_demo_hdr
           file_demo_prefix_p file_demo_prefix_prog file_demo_prefix_envp
           file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
           file_demo_prefix_p_nonneg file_demo_prefix_p_le_1).
Qed.

(* =========================================================================
   The fire set: after the header, the payload begins with a NUL byte
   ========================================================================= *)

Definition file_demo_prefix_nul : byte := Z_to_bv 8 0.
Definition file_demo_prefix_a : byte := Z_to_bv 8 65.

(** The PAYLOAD prefix the fire set is charged against: one NUL byte
    right after the header. *)
Definition file_demo_prefix_bs : list byte := [file_demo_prefix_nul].

(** THE CEILING: the mass of the payload cylinder over that one byte.
    It is [(1 - p) / 256] at this stop weight, which is one in two
    hundred fifty-seven — and it does NOT pay for the header. *)
Lemma file_demo_prefix_fire_ceiling :
  (file_geometric_prefix_cylinder_mass file_demo_prefix_p file_demo_prefix_bs
     == 1 # 257)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma file_demo_prefix_fire_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
       file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
       file_demo_prefix_stdin file_demo_prefix_bs (fin_core f)) ->
  (core_sum (cd_weight file_demo_prefix_cd) l <= 1 # 257)%Q.
Proof.
  intros l Hnd Hcyl.
  rewrite <- file_demo_prefix_fire_ceiling.
  unfold file_demo_prefix_cd, file_geometric_prefix_argv1.
  apply (file_geometric_prefix_bound file_demo_hdr file_demo_prefix_p
           file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
           file_demo_prefix_path file_demo_prefix_stdin
           file_demo_prefix_p_nonneg file_demo_prefix_p_le_1
           file_demo_prefix_bs l Hnd Hcyl).
Qed.

(** The payload-length slice at [n = 1]: [p (1 - p)], with the 256
    alternatives per payload byte charged nothing and the header charged
    nothing. *)
Lemma file_demo_prefix_slice_bound_at_one : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     exists t, fin_core f = file_prefix_core file_demo_hdr file_demo_prefix_argv
                              file_demo_prefix_envp file_demo_prefix_fs0
                              file_demo_prefix_path file_demo_prefix_stdin t
               /\ length t = 1%nat) ->
  (core_sum (cd_weight file_demo_prefix_cd) l <= 256 # 66049)%Q.
Proof.
  intros l Hnd Hslice.
  eapply Qle_trans.
  - unfold file_demo_prefix_cd, file_geometric_prefix_argv1.
    apply (file_geometric_prefix_slice_bound file_demo_hdr file_demo_prefix_p
             file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
             file_demo_prefix_path file_demo_prefix_stdin
             file_demo_prefix_p_nonneg file_demo_prefix_p_le_1 1%nat l Hnd
             Hslice).
  - apply Qle_of_Qeq. vm_compute. reflexivity.
Qed.

(* =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= *)

Module FilePrefix_D <: DISTRIBUTION.
  Definition w : FinProcInput -> Q := cd_lift file_demo_prefix_cd.
  Definition M : Q := cd_mass file_demo_prefix_cd.
  Definition w_nonneg : forall f, (0 <= w f)%Q :=
    cd_lift_nonneg file_demo_prefix_cd.
  Lemma M_nonneg : (0 <= M)%Q.
  Proof. unfold M. rewrite file_demo_prefix_mass_is_one. exact Qle_0_1. Qed.
  Definition w_core_blind :
    forall f g, fin_core f = fin_core g -> (w f == w g)%Q :=
    cd_lift_core_blind file_demo_prefix_cd.
End FilePrefix_D.

Lemma file_demo_prefix_weight_bound_T_of : forall C b,
  (forall f, Classifier.rejects C f ->
     in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
       file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
       file_demo_prefix_stdin file_demo_prefix_bs (fin_core f)) ->
  (1 # 257 <= b)%Q ->
  weight_bound_T C FilePrefix_D.w FilePrefix_D.M b.
Proof.
  intros C b Hfire Hb l Hnd Hrej.
  unfold FilePrefix_D.w. rewrite <- core_sum_cd_lift.
  apply (Qle_trans _ (1 # 257)%Q).
  - apply file_demo_prefix_fire_bound;
      [exact Hnd | intros f Hf; apply Hfire, Hrej, Hf].
  - unfold FilePrefix_D.M. rewrite file_demo_prefix_mass_is_one.
    apply (Qle_trans _ b); [exact Hb | apply Qle_of_Qeq; ring].
Qed.

(** At a round multiplier a task would declare: a classifier that fires
    only on payloads beginning with a NUL byte carries at most a
    hundredth of the mass. *)
Lemma file_demo_prefix_weight_bound_T_hundredth : forall C,
  (forall f, Classifier.rejects C f ->
     in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
       file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
       file_demo_prefix_stdin file_demo_prefix_bs (fin_core f)) ->
  weight_bound_T C FilePrefix_D.w FilePrefix_D.M (1 # 100).
Proof.
  intros C Hfire. apply file_demo_prefix_weight_bound_T_of; [exact Hfire |].
  apply (proj1 (Qle_bool_iff _ _)). vm_compute. reflexivity.
Qed.

(* =========================================================================
   Non-vacuity: inside the cylinder, and the mass is a supremum
   ========================================================================= *)

(** Two cores of the cylinder: the payload that stops at the NUL byte,
    and the payload that carries one byte more. *)
Definition file_demo_prefix_core_stop : FinCore :=
  file_prefix_core file_demo_hdr file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    [file_demo_prefix_nul].
Definition file_demo_prefix_core_ext : FinCore :=
  file_prefix_core file_demo_hdr file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    [file_demo_prefix_nul; file_demo_prefix_a].

Definition file_demo_prefix_fire_list : list FinProcInput :=
  List.map core_input [file_demo_prefix_core_stop; file_demo_prefix_core_ext].

(** HOW MUCH OF THE CEILING IS REAL: both cores are in the cylinder, the
    list is admissible — [MeasureLib.file_prefix_core_inj] is what makes
    two payloads two cores — and the sum is strictly under the ceiling. *)
Lemma file_demo_prefix_fire_slack :
  in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
    file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
    file_demo_prefix_stdin file_demo_prefix_bs file_demo_prefix_core_stop
  /\ in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
       file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
       file_demo_prefix_stdin file_demo_prefix_bs file_demo_prefix_core_ext
  /\ List.NoDup (List.map fin_core file_demo_prefix_fire_list)
  /\ ~ (1 # 257 <= core_sum (cd_weight file_demo_prefix_cd)
                     file_demo_prefix_fire_list)%Q.
Proof.
  split; [| split; [| split]].
  - exists []. reflexivity.
  - exists [file_demo_prefix_a]. reflexivity.
  - unfold file_demo_prefix_fire_list. rewrite map_fin_core_core_input.
    apply List.NoDup_cons.
    + intros [Heq | []].
      unfold file_demo_prefix_core_stop, file_demo_prefix_core_ext in Heq.
      apply file_prefix_core_inj in Heq.
      apply (f_equal (@length byte)) in Heq. cbn [length] in Heq.
      discriminate Heq.
    + apply List.NoDup_cons; [intros [] | apply List.NoDup_nil].
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate.
Qed.

(** THE LOWER HALF of the certificate pair, at a concrete margin. *)
Lemma file_demo_prefix_mass_lower_at_a_thousandth :
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (1 - (1 # 1000) <= core_sum (cd_weight file_demo_prefix_cd) l)%Q.
Proof.
  unfold file_demo_prefix_cd, file_geometric_prefix_argv1.
  apply (file_geometric_prefix_mass_lower_certificate file_demo_hdr
           file_demo_prefix_p file_demo_prefix_argv file_demo_prefix_envp
           file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
           file_demo_prefix_p_nonneg file_demo_prefix_p_le_1 (1 # 1000)%Q);
    reflexivity.
Qed.

(** ... and it is a SUPREMUM and not a maximum. *)
Lemma file_demo_prefix_mass_not_attained : forall l : list FinProcInput,
  List.NoDup (List.map fin_core l) ->
  ~ (core_sum (cd_weight file_demo_prefix_cd) l == 1)%Q.
Proof.
  unfold file_demo_prefix_cd, file_geometric_prefix_argv1.
  apply (file_geometric_prefix_mass_supremum_not_maximum file_demo_hdr
           file_demo_prefix_p file_demo_prefix_argv file_demo_prefix_envp
           file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
           file_demo_prefix_p_nonneg file_demo_prefix_p_le_1).
  reflexivity.
Qed.

(** The whole-space upper certificate for the same distribution. *)
Lemma file_demo_prefix_whole_space_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight file_demo_prefix_cd) l <= 1)%Q.
Proof.
  intros l Hnd. unfold file_demo_prefix_cd, file_geometric_prefix_argv1.
  apply (file_geometric_prefix_mass_upper file_demo_hdr file_demo_prefix_p
           file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
           file_demo_prefix_path file_demo_prefix_stdin
           file_demo_prefix_p_nonneg file_demo_prefix_p_le_1 l Hnd).
Qed.

(* =========================================================================
   The header bites, numerically
   ========================================================================= *)

(** The core whose file is EXACTLY the header (empty payload), the core
    whose file is the header with its first byte changed, and the
    whole-file family at the same parameters, for comparison. *)
Definition file_demo_prefix_core_hdr : FinCore :=
  file_prefix_core file_demo_hdr file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin [].

(** The corrupted header is DERIVED from the header — its first byte
    replaced, the rest taken from [file_demo_hdr] by [List.tl] — so that
    editing the header cannot leave the pin below green while it stops
    meaning "the header with its first byte changed".
    [file_demo_badhdr_is_the_header_with_its_first_byte_changed] is the
    receipt: same tail, different list. *)
Definition file_demo_badhdr : list byte :=
  Z_to_bv 8 2 :: List.tl file_demo_hdr.

Lemma file_demo_badhdr_is_the_header_with_its_first_byte_changed :
  List.tl file_demo_badhdr = List.tl file_demo_hdr
  /\ Fs.path_eqb file_demo_badhdr file_demo_hdr = false.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Definition file_demo_prefix_core_badhdr : FinCore :=
  file_core file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin file_demo_badhdr.

Definition file_demo_wholefile_cd : CoreDistribution :=
  file_geometric file_demo_prefix_p file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    file_demo_prefix_p_nonneg file_demo_prefix_p_le_1.

(** THE HEADER BITES: the exact-header core weighs the stop weight, the
    corrupted-header core weighs zero, and the declared mass is [1].
    All three are closed computations. *)
Lemma file_demo_prefix_header_bites :
  (cd_weight file_demo_prefix_cd file_demo_prefix_core_hdr == 1 # 257)%Q
  /\ (cd_weight file_demo_prefix_cd file_demo_prefix_core_badhdr == 0)%Q
  /\ cd_mass file_demo_prefix_cd = 1%Q.
Proof.
  split; [| split]; [vm_compute; reflexivity | vm_compute; reflexivity |
                     reflexivity].
Qed.

(** THE HEADER DILUTION, as arithmetic: the same exact-header core weighs
    [p] here and [p * ((1 - p) / 256) ^ 7] under the whole-file family —
    a seventh power of one in two hundred fifty-seven smaller.  That
    factor is what a bound over the whole-file family would have to pay
    for the header before it says anything about the payload. *)
Lemma file_demo_prefix_header_dilution :
  (cd_weight file_demo_wholefile_cd file_demo_prefix_core_hdr
     == (1 # 257) * Qpow (1 # 257) 7)%Q
  /\ (cd_weight file_demo_prefix_cd file_demo_prefix_core_hdr == 1 # 257)%Q.
Proof.
  split; vm_compute; reflexivity.
Qed.

(* =========================================================================
   The empty header, numerically
   ========================================================================= *)

Definition file_demo_nilhdr_cd : CoreDistribution :=
  file_geometric_prefix [] file_demo_prefix_p file_demo_prefix_argv
    file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
    file_demo_prefix_stdin file_demo_prefix_p_nonneg file_demo_prefix_p_le_1.

Definition file_demo_prefix_core_one : FinCore :=
  file_core file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin [file_demo_prefix_nul].

(** THE [k = 0] COLLAPSE, at two concrete cores and as a number: the
    empty-header family and the whole-file family agree at the one-byte
    file, where both weigh [p (1 - p) / 256], and at the seven-byte
    header file.  The general statement is
    [MeasureLib.file_geometric_prefix_nil_pointwise], instantiated in
    the last conjunct. *)
Lemma file_demo_prefix_nil_collapse :
  (cd_weight file_demo_nilhdr_cd file_demo_prefix_core_one == 1 # 66049)%Q
  /\ (cd_weight file_demo_wholefile_cd file_demo_prefix_core_one == 1 # 66049)%Q
  /\ (cd_weight file_demo_nilhdr_cd file_demo_prefix_core_hdr
        == cd_weight file_demo_wholefile_cd file_demo_prefix_core_hdr)%Q
  /\ (forall c, (cd_weight file_demo_nilhdr_cd c
                   == cd_weight file_demo_wholefile_cd c)%Q).
Proof.
  split; [| split; [| split]].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros c. apply file_geometric_prefix_nil_pointwise.
Qed.

(** THE MISCONFIGURATION, at this file's stop weight: the library's pin
    that an instance whose argv does not name the path is invisible to
    the program it is built for, for this family. *)
Lemma file_demo_prefix_misconfiguration_is_invisible :
  ~ argv_names_path file_misconfigured_argv file_example_path
  /\ (0 < cd_weight (file_geometric_prefix file_example_hdr file_demo_prefix_p
                       file_misconfigured_argv [] Fs.fs_empty file_example_path []
                       file_demo_prefix_p_nonneg file_demo_prefix_p_le_1)
            (file_prefix_core file_example_hdr file_misconfigured_argv [] Fs.fs_empty
               file_example_path [] []))%Q
  /\ (0 < cd_weight (file_geometric_prefix file_example_hdr file_demo_prefix_p
                       file_misconfigured_argv [] Fs.fs_empty file_example_path []
                       file_demo_prefix_p_nonneg file_demo_prefix_p_le_1)
            (file_prefix_core file_example_hdr file_misconfigured_argv [] Fs.fs_empty
               file_example_path [] [Z_to_bv 8 65]))%Q
  /\ fs_file file_other_path
       (core_fs (file_prefix_core file_example_hdr file_misconfigured_argv [] Fs.fs_empty
                   file_example_path [] []))
     = fs_file file_other_path
         (core_fs (file_prefix_core file_example_hdr file_misconfigured_argv
                     [] Fs.fs_empty file_example_path [] [Z_to_bv 8 65])).
Proof.
  exact (file_geometric_prefix_needs_argv_to_name_the_path file_demo_prefix_p
           file_demo_prefix_p_nonneg file_demo_prefix_p_le_1 eq_refl eq_refl).
Qed.
