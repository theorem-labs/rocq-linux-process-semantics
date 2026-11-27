(** * Examples.measure_lib_demo.FileGeometricPrefixOver — the
      header-conditioned file family over PRINTABLE ASCII, worked

    DEMO FILE (not part of the trusted specification, and not installed).
    [MeasureLib.file_geometric_prefix] fixes the first bytes of the input
    file to a header and spreads the geometric source over what follows,
    every payload byte uniform over all the bytes.
    [MeasureLib.file_geometric_prefix_over] spreads the payload's bytes
    over a fixed ALPHABET instead.  This file instantiates it at the
    printable ASCII bytes, behind the same seven-byte header the
    all-bytes demo uses, and carries it through to a
    [Measure.weight_bound_T].

    ** Why a task reaches for this one rather than the all-bytes one

    A text-consuming program parses printable input.  Under the all-bytes
    law almost every payload of any length holds a control byte, so a
    fire set described by printable text sits under every threshold for
    a reason that has nothing to do with the library: it is a small
    fraction of a space the program mostly rejects.  Over the printable
    alphabet the payload space IS the text the program reads.

    ** The alphabet, and what is derived from what

    [printable_ascii] is the bytes from the space to the tilde, built as
    [Z_to_bv] over [List.seq] from a lower bound and a count, so that
    its size, duplicate-freedom and non-emptiness are arguments about
    [List.seq] and not a literal.  The stop weight, the fire set's
    first byte, the in-alphabet and off-alphabet payloads below are all
    derived from those two numbers or reused from the all-bytes demo;
    nothing here is a literal copy of something defined elsewhere.

    ** The full alphabet

    [file_demo_over_all_bytes_collapse] checks, by computation at a
    concrete core, that the family at [all_bytes] is the all-bytes header
    family: the general lemma is
    [MeasureLib.file_geometric_prefix_over_all_bytes_pointwise].

    Nothing exhibited here is claimed VALID and nothing is claimed
    rejected by any classifier. *)

From Stdlib Require Import ZArith NArith List QArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  FinInput Measure MeasureLib.
From LinuxProcessSemantics.EquivalenceDefinition Require Classifier.
From LinuxProcessSemantics.Examples.measure_lib_demo Require Import
  FileGeometricPrefix.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The alphabet: printable ASCII
   ========================================================================= *)

(** The space is the first printable byte and there are ninety-five of
    them, up to the tilde.  Everything below is built from these. *)
Definition printable_lo : nat := 32.
Definition printable_count : nat := 95.

Definition printable_ascii : list byte :=
  List.map (fun n => Z_to_bv 8 (Z.of_nat n))
    (List.seq printable_lo printable_count).

Lemma printable_ascii_length : length printable_ascii = printable_count.
Proof.
  unfold printable_ascii. rewrite List.length_map, List.length_seq. reflexivity.
Qed.

(** THE RECEIPT for "space to tilde": the alphabet's first byte is the
    space (hex 20) and its last is the tilde (hex 7e).  Both closed
    computations, so that the lower bound and the count above are pinned
    to the range the prose names rather than trusted. *)
Lemma printable_ascii_runs_from_space_to_tilde :
  List.hd (Z_to_bv 8 0) printable_ascii = Z_to_bv 8 32
  /\ List.last printable_ascii (Z_to_bv 8 0) = Z_to_bv 8 126.
Proof. split; vm_compute; reflexivity. Qed.

(** Duplicate-free, by the argument [MeasureLib.all_bytes_nodup] makes
    for the whole range: below the modulus the round trip through
    [bv_unsigned] is the identity, so the map is injective on the
    sequence. *)
Lemma printable_ascii_nodup : List.NoDup printable_ascii.
Proof.
  unfold printable_ascii. apply NoDup_map_inj; [| apply List.seq_NoDup].
  intros x y Hx Hy Heq.
  apply List.in_seq in Hx. apply List.in_seq in Hy.
  unfold printable_lo, printable_count in Hx, Hy.
  apply (f_equal (@bv_unsigned 8)) in Heq.
  rewrite !Z_to_bv_small in Heq.
  - apply Nat2Z.inj. exact Heq.
  - change (bv_modulus 8) with 256%Z. lia.
  - change (bv_modulus 8) with 256%Z. lia.
Qed.

Lemma printable_ascii_ne : printable_ascii <> [].
Proof.
  intros H. apply (f_equal (@length byte)) in H.
  rewrite printable_ascii_length in H. discriminate H.
Qed.

(** The stop weight: one over one more than the alphabet's size, so that
    [1 - p] is the alphabet's size over that, and the per-byte factor
    [(1 - p) * alpha_ratio] is again one over one more than the size —
    every number below is a power of that one denominator. *)
Definition file_demo_over_p : Q := (/ Qnat (S printable_count))%Q.

Lemma file_demo_over_p_nonneg : (0 <= file_demo_over_p)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma file_demo_over_p_le_1 : (file_demo_over_p <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

(** The space byte and the letter [A], derived from the lower bound. *)
Definition file_demo_over_space : byte := Z_to_bv 8 (Z.of_nat printable_lo).
Definition file_demo_over_a : byte := Z_to_bv 8 (Z.of_nat (printable_lo + 33)).

Lemma file_demo_over_space_in_alpha :
  alpha_memb printable_ascii file_demo_over_space = true.
Proof. vm_compute. reflexivity. Qed.

(** ... and the NUL byte the all-bytes demo fires on is a CONTROL byte,
    outside the alphabet. *)
Lemma file_demo_prefix_nul_off_alpha :
  alpha_memb printable_ascii file_demo_prefix_nul = false.
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   The distribution: the same header, program, path and base as the
   all-bytes demo
   ========================================================================= *)

Definition file_demo_over_cd : CoreDistribution :=
  file_geometric_prefix_over_argv1 printable_ascii printable_ascii_nodup
    printable_ascii_ne file_demo_hdr file_demo_over_p
    file_demo_prefix_prog file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin
    file_demo_over_p_nonneg file_demo_over_p_le_1.

Lemma file_demo_over_mass_is_one : cd_mass file_demo_over_cd = 1%Q.
Proof. reflexivity. Qed.

Lemma file_demo_over_argv_names_path :
  argv_names_path file_demo_prefix_argv file_demo_prefix_path
  /\ file_demo_over_cd
     = file_geometric_prefix_over printable_ascii printable_ascii_nodup
         printable_ascii_ne file_demo_hdr file_demo_over_p
         file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
         file_demo_prefix_path file_demo_prefix_stdin
         file_demo_over_p_nonneg file_demo_over_p_le_1.
Proof.
  exact (file_geometric_prefix_over_argv1_names_path printable_ascii
           printable_ascii_nodup printable_ascii_ne file_demo_hdr
           file_demo_over_p file_demo_prefix_prog file_demo_prefix_envp
           file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
           file_demo_over_p_nonneg file_demo_over_p_le_1).
Qed.

(* =========================================================================
   The fire set: after the header, the payload begins with a space
   ========================================================================= *)

Definition file_demo_over_bs : list byte := [file_demo_over_space].

(** THE CEILING: [(1 - p) * alpha_ratio] at one payload byte, which is
    one ninety-sixth at this stop weight. *)
Lemma file_demo_over_fire_ceiling :
  (file_geometric_prefix_over_cylinder_mass printable_ascii file_demo_over_p
     file_demo_over_bs == 1 # 96)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma file_demo_over_fire_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
       file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
       file_demo_prefix_stdin file_demo_over_bs (fin_core f)) ->
  (core_sum (cd_weight file_demo_over_cd) l <= 1 # 96)%Q.
Proof.
  intros l Hnd Hcyl.
  rewrite <- file_demo_over_fire_ceiling.
  unfold file_demo_over_cd, file_geometric_prefix_over_argv1.
  apply (file_geometric_prefix_over_bound printable_ascii printable_ascii_nodup
           printable_ascii_ne file_demo_hdr file_demo_over_p
           file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
           file_demo_prefix_path file_demo_prefix_stdin
           file_demo_over_p_nonneg file_demo_over_p_le_1
           file_demo_over_bs l Hnd Hcyl).
Qed.

(** The payload-length slice at [n = 1]: [p (1 - p)], with the
    ninety-five alternatives per payload byte charged nothing. *)
Lemma file_demo_over_slice_bound_at_one : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     exists t, fin_core f = file_prefix_core file_demo_hdr file_demo_prefix_argv
                              file_demo_prefix_envp file_demo_prefix_fs0
                              file_demo_prefix_path file_demo_prefix_stdin t
               /\ length t = 1%nat) ->
  (core_sum (cd_weight file_demo_over_cd) l <= 95 # 9216)%Q.
Proof.
  intros l Hnd Hslice.
  eapply Qle_trans.
  - unfold file_demo_over_cd, file_geometric_prefix_over_argv1.
    apply (file_geometric_prefix_over_slice_bound printable_ascii
             printable_ascii_nodup printable_ascii_ne file_demo_hdr
             file_demo_over_p file_demo_prefix_argv file_demo_prefix_envp
             file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
             file_demo_over_p_nonneg file_demo_over_p_le_1 1%nat l Hnd Hslice).
  - apply Qle_of_Qeq. vm_compute. reflexivity.
Qed.

(** The same slice in the file-length shape, with no premise on the
    header or the alphabet. *)
Lemma file_demo_over_slice_bound_by_file_length_at_one : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_core f = file_core file_demo_prefix_argv file_demo_prefix_envp
                    file_demo_prefix_fs0 file_demo_prefix_path
                    file_demo_prefix_stdin (fs_file file_demo_prefix_path (fin_image_fs f))
     /\ length (fs_file file_demo_prefix_path (fin_image_fs f))
        = (length file_demo_hdr + 1)%nat) ->
  (core_sum (cd_weight file_demo_over_cd) l <= 95 # 9216)%Q.
Proof.
  intros l Hnd Hslice.
  eapply Qle_trans.
  - unfold file_demo_over_cd, file_geometric_prefix_over_argv1.
    apply (file_geometric_prefix_over_slice_bound_by_file_length printable_ascii
             printable_ascii_nodup printable_ascii_ne file_demo_hdr
             file_demo_over_p file_demo_prefix_argv file_demo_prefix_envp
             file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
             file_demo_over_p_nonneg file_demo_over_p_le_1 1%nat l Hnd Hslice).
  - apply Qle_of_Qeq. vm_compute. reflexivity.
Qed.

(* =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= *)

Module FilePrefixOver_D <: DISTRIBUTION.
  Definition w : FinProcInput -> Q := cd_lift file_demo_over_cd.
  Definition M : Q := cd_mass file_demo_over_cd.
  Definition w_nonneg : forall f, (0 <= w f)%Q :=
    cd_lift_nonneg file_demo_over_cd.
  Lemma M_nonneg : (0 <= M)%Q.
  Proof. unfold M. rewrite file_demo_over_mass_is_one. exact Qle_0_1. Qed.
  Definition w_core_blind :
    forall f g, fin_core f = fin_core g -> (w f == w g)%Q :=
    cd_lift_core_blind file_demo_over_cd.
End FilePrefixOver_D.

Lemma file_demo_over_weight_bound_T_of : forall C b,
  (forall f, Classifier.rejects C f ->
     in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
       file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
       file_demo_prefix_stdin file_demo_over_bs (fin_core f)) ->
  (1 # 96 <= b)%Q ->
  weight_bound_T C FilePrefixOver_D.w FilePrefixOver_D.M b.
Proof.
  intros C b Hfire Hb l Hnd Hrej.
  unfold FilePrefixOver_D.w. rewrite <- core_sum_cd_lift.
  apply (Qle_trans _ (1 # 96)%Q).
  - apply file_demo_over_fire_bound;
      [exact Hnd | intros f Hf; apply Hfire, Hrej, Hf].
  - unfold FilePrefixOver_D.M. rewrite file_demo_over_mass_is_one.
    apply (Qle_trans _ b); [exact Hb | apply Qle_of_Qeq; ring].
Qed.

(** At a round multiplier a task would declare: a classifier that fires
    only on payloads beginning with a space carries at most a fiftieth
    of the mass. *)
Lemma file_demo_over_weight_bound_T_fiftieth : forall C,
  (forall f, Classifier.rejects C f ->
     in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
       file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
       file_demo_prefix_stdin file_demo_over_bs (fin_core f)) ->
  weight_bound_T C FilePrefixOver_D.w FilePrefixOver_D.M (1 # 50).
Proof.
  intros C Hfire. apply file_demo_over_weight_bound_T_of; [exact Hfire |].
  apply (proj1 (Qle_bool_iff _ _)). vm_compute. reflexivity.
Qed.

(* =========================================================================
   Non-vacuity: inside the cylinder, and the mass is a supremum
   ========================================================================= *)

Definition file_demo_over_core_stop : FinCore :=
  file_prefix_core file_demo_hdr file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    [file_demo_over_space].
Definition file_demo_over_core_ext : FinCore :=
  file_prefix_core file_demo_hdr file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    [file_demo_over_space; file_demo_over_a].

Definition file_demo_over_fire_list : list FinProcInput :=
  List.map core_input [file_demo_over_core_stop; file_demo_over_core_ext].

Lemma file_demo_over_fire_slack :
  in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
    file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
    file_demo_prefix_stdin file_demo_over_bs file_demo_over_core_stop
  /\ in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
       file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
       file_demo_prefix_stdin file_demo_over_bs file_demo_over_core_ext
  /\ List.NoDup (List.map fin_core file_demo_over_fire_list)
  /\ ~ (1 # 96 <= core_sum (cd_weight file_demo_over_cd)
                    file_demo_over_fire_list)%Q.
Proof.
  split; [| split; [| split]].
  - exists []. reflexivity.
  - exists [file_demo_over_a]. reflexivity.
  - unfold file_demo_over_fire_list. rewrite map_fin_core_core_input.
    apply List.NoDup_cons.
    + intros [Heq | []].
      unfold file_demo_over_core_stop, file_demo_over_core_ext in Heq.
      apply file_prefix_core_inj in Heq.
      apply (f_equal (@length byte)) in Heq. cbn [length] in Heq.
      discriminate Heq.
    + apply List.NoDup_cons; [intros [] | apply List.NoDup_nil].
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate.
Qed.

Lemma file_demo_over_mass_lower_at_a_thousandth :
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (1 - (1 # 1000) <= core_sum (cd_weight file_demo_over_cd) l)%Q.
Proof.
  unfold file_demo_over_cd, file_geometric_prefix_over_argv1.
  apply (file_geometric_prefix_over_mass_lower_certificate printable_ascii
           printable_ascii_nodup printable_ascii_ne file_demo_hdr
           file_demo_over_p file_demo_prefix_argv file_demo_prefix_envp
           file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
           file_demo_over_p_nonneg file_demo_over_p_le_1 (1 # 1000)%Q);
    reflexivity.
Qed.

Lemma file_demo_over_mass_not_attained : forall l : list FinProcInput,
  List.NoDup (List.map fin_core l) ->
  ~ (core_sum (cd_weight file_demo_over_cd) l == 1)%Q.
Proof.
  unfold file_demo_over_cd, file_geometric_prefix_over_argv1.
  apply (file_geometric_prefix_over_mass_supremum_not_maximum printable_ascii
           printable_ascii_nodup printable_ascii_ne file_demo_hdr
           file_demo_over_p file_demo_prefix_argv file_demo_prefix_envp
           file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
           file_demo_over_p_nonneg file_demo_over_p_le_1).
  reflexivity.
Qed.

Lemma file_demo_over_whole_space_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight file_demo_over_cd) l <= 1)%Q.
Proof.
  intros l Hnd. unfold file_demo_over_cd, file_geometric_prefix_over_argv1.
  apply (file_geometric_prefix_over_mass_upper printable_ascii
           printable_ascii_nodup printable_ascii_ne file_demo_hdr
           file_demo_over_p file_demo_prefix_argv file_demo_prefix_envp
           file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
           file_demo_over_p_nonneg file_demo_over_p_le_1 l Hnd).
Qed.

(* =========================================================================
   The alphabet bites, numerically
   ========================================================================= *)

(** A one-byte printable payload, and a one-byte CONTROL payload — the
    NUL byte the all-bytes demo fires on. *)
Definition file_demo_over_core_printable : FinCore := file_demo_over_core_stop.

Definition file_demo_over_core_control : FinCore :=
  file_prefix_core file_demo_hdr file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    [file_demo_prefix_nul].

(** The all-bytes header family at this file's stop weight, for
    comparison. *)
Definition file_demo_over_allbytes_ref_cd : CoreDistribution :=
  file_geometric_prefix file_demo_hdr file_demo_over_p file_demo_prefix_argv
    file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
    file_demo_prefix_stdin file_demo_over_p_nonneg file_demo_over_p_le_1.

(** THE ALPHABET BITES: the printable payload weighs [p * (1 - p) / 95],
    which is one over the square of ninety-six; the control payload
    weighs zero here and positively under the all-bytes header family;
    the mass is [1]. *)
Lemma file_demo_over_alphabet_bites :
  (cd_weight file_demo_over_cd file_demo_over_core_printable == 1 # 9216)%Q
  /\ (cd_weight file_demo_over_cd file_demo_over_core_control == 0)%Q
  /\ cd_mass file_demo_over_cd = 1%Q
  /\ (0 < cd_weight file_demo_over_allbytes_ref_cd file_demo_over_core_control)%Q.
Proof.
  split; [| split; [| split]].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - apply (proj2 (Qlt_alt _ _)). vm_compute. reflexivity.
Qed.

(* =========================================================================
   The full alphabet, numerically
   ========================================================================= *)

Definition file_demo_over_allbytes_cd : CoreDistribution :=
  file_geometric_prefix_over all_bytes all_bytes_nodup all_bytes_ne
    file_demo_hdr file_demo_over_p file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    file_demo_over_p_nonneg file_demo_over_p_le_1.

(** THE [alpha = all_bytes] COLLAPSE, at a concrete core and in general:
    the family over the full alphabet agrees with the all-bytes header
    family at the control payload, as a number, and at every core. *)
Lemma file_demo_over_all_bytes_collapse :
  (cd_weight file_demo_over_allbytes_cd file_demo_over_core_control
     == cd_weight file_demo_over_allbytes_ref_cd file_demo_over_core_control)%Q
  /\ (forall c, (cd_weight file_demo_over_allbytes_cd c
                   == cd_weight file_demo_over_allbytes_ref_cd c)%Q).
Proof.
  split.
  - vm_compute. reflexivity.
  - intros c. apply file_geometric_prefix_over_all_bytes_pointwise.
Qed.

(** THE MISCONFIGURATION, at this file's stop weight, for this family. *)
Lemma file_demo_over_misconfiguration_is_invisible :
  ~ argv_names_path file_misconfigured_argv file_example_path
  /\ (0 < cd_weight (file_geometric_prefix_over file_example_alpha
                       file_example_alpha_nodup file_example_alpha_ne
                       file_example_hdr file_demo_over_p file_misconfigured_argv
                       [] Fs.fs_empty file_example_path []
                       file_demo_over_p_nonneg file_demo_over_p_le_1)
            (file_prefix_core file_example_hdr file_misconfigured_argv [] Fs.fs_empty
               file_example_path [] []))%Q
  /\ (0 < cd_weight (file_geometric_prefix_over file_example_alpha
                       file_example_alpha_nodup file_example_alpha_ne
                       file_example_hdr file_demo_over_p file_misconfigured_argv
                       [] Fs.fs_empty file_example_path []
                       file_demo_over_p_nonneg file_demo_over_p_le_1)
            (file_prefix_core file_example_hdr file_misconfigured_argv [] Fs.fs_empty
               file_example_path [] [Z_to_bv 8 65]))%Q
  /\ fs_file file_other_path
       (core_fs (file_prefix_core file_example_hdr file_misconfigured_argv [] Fs.fs_empty
                   file_example_path [] []))
     = fs_file file_other_path
         (core_fs (file_prefix_core file_example_hdr file_misconfigured_argv
                     [] Fs.fs_empty file_example_path [] [Z_to_bv 8 65])).
Proof.
  exact (file_geometric_prefix_over_needs_argv_to_name_the_path file_demo_over_p
           file_demo_over_p_nonneg file_demo_over_p_le_1 eq_refl eq_refl).
Qed.
