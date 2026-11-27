(** * Examples.measure_lib_demo.FileGeometric — the file-varying
      geometric family, worked

    DEMO FILE (not part of the trusted specification, and not installed).
    [MeasureLib.stdin_geometric] varies STANDARD INPUT over a fixed
    launch-time environment.  [MeasureLib.file_geometric] varies the
    CONTENTS OF ONE FILE instead, at a path the task names, over a fixed
    argv, environment, standard input and base file system.  This file
    instantiates it and carries it through to a
    [Measure.weight_bound_T].

    ** Why a task reaches for this one rather than the standard-input one

    A program that takes its input as a path argument reads nothing from
    standard input, so a distribution that varies standard input puts all
    its mass on a coordinate the program never looks at, and every
    classifier either rejects all of it or none of it.  The file family
    varies the coordinate the program actually reads.  What it costs is
    one obligation that has no counterpart in the standard-input family,
    and this file pays it the way the library recommends.

    ** The argv/path coupling, discharged by construction

    [MeasureLib.file_geometric] takes argv and the path as INDEPENDENT
    parameters, and passing two different paths yields a distribution
    that is healthy by every certificate and varies a file the program
    never opens.  [MeasureLib.file_geometric_argv1] is the derived
    constructor for the shape a driver actually has — a program name and
    the input path at argv[1] — and it takes the path ONCE, so the
    mismatch is not expressible.  This file uses it, and
    [file_demo_argv_names_path] is the receipt.

    [file_demo_misconfiguration_is_invisible] is the other half: the
    library's pin of what a mismatched instance looks like, instantiated
    at this file's stop weight.  A reader can see there that the
    misconfigured instance passes both certificates and still collapses.

    ** The file system, and what [MeasureLib.fs_file] reads

    A core carries a whole [Fs.Fs], and the family varies one path of it
    over a fixed base: [MeasureLib.file_core] is
    [Fs.fs_set] of the contents into the base, and
    [MeasureLib.fs_file] is the readback, total by returning [[]] at an
    absent path.  [MeasureLib.file_core_inj] — the injectivity of that
    embedding — is what the duplicate-freedom argument below spends, and
    it is the reason two cores differing only in the file's contents are
    distinct cores rather than the same one.

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
   The task's fixed data: a program, the path it is given, and the base
   ========================================================================= *)

(** The program's own name, and the path it is invoked on: ["wc"] and
    ["/in"].  Both are byte lists because argv entries and
    [Fs.path] are the same type here. *)
Definition file_demo_prog : list byte := [Z_to_bv 8 119; Z_to_bv 8 99].
Definition file_demo_path : Fs.path :=
  [Z_to_bv 8 47; Z_to_bv 8 105; Z_to_bv 8 110].

(** Everything the family holds fixed: no environment, an empty base file
    system, and an empty standard input.  The standard input being empty
    is the point rather than a default — this family's programs read
    their input from the path, so leaving standard input with any
    content at all would put weight on a coordinate nothing reads. *)
Definition file_demo_envp : list (list byte) := [].
Definition file_demo_fs0 : Fs.Fs := Fs.fs_empty.
Definition file_demo_stdin : list byte := [].

Definition file_demo_p : Q := (1 # 8)%Q.

Lemma file_demo_p_nonneg : (0 <= file_demo_p)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma file_demo_p_le_1 : (file_demo_p <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

(** THE DISTRIBUTION, through the coupled constructor.  [file_demo_path]
    appears once in this term and reaches both the argv it is built into
    and the path whose contents are varied. *)
Definition file_demo_cd : CoreDistribution :=
  file_geometric_argv1 file_demo_p file_demo_prog file_demo_envp
    file_demo_fs0 file_demo_path file_demo_stdin
    file_demo_p_nonneg file_demo_p_le_1.

Definition file_demo_argv : list (list byte) :=
  path_argv file_demo_prog file_demo_path.

Lemma file_demo_mass_is_one : cd_mass file_demo_cd = 1%Q.
Proof. reflexivity. Qed.

(** THE RECEIPT for the coupling: the argv this distribution was built
    with really does name the path whose contents it varies, and the
    coupled constructor really is the general one at that argv.  Both
    conjuncts come from the library; neither is argued here. *)
Lemma file_demo_argv_names_path :
  argv_names_path file_demo_argv file_demo_path
  /\ file_demo_cd
     = file_geometric file_demo_p file_demo_argv file_demo_envp
         file_demo_fs0 file_demo_path file_demo_stdin
         file_demo_p_nonneg file_demo_p_le_1.
Proof.
  exact (file_geometric_argv1_names_path file_demo_p file_demo_prog
           file_demo_envp file_demo_fs0 file_demo_path file_demo_stdin
           file_demo_p_nonneg file_demo_p_le_1).
Qed.

(* =========================================================================
   The fire set: the input file begins with a NUL byte
   ========================================================================= *)

Definition file_demo_nul : byte := Z_to_bv 8 0.
Definition file_demo_a : byte := Z_to_bv 8 65.

(** The prefix the fire set is charged against: one NUL byte at the head
    of the input file.  A task whose program fails on binary input
    describes its fire set exactly this way. *)
Definition file_demo_bs : list byte := [file_demo_nul].

(** THE CEILING: the mass of the cylinder over that one byte.  It is the
    same [MeasureLib.geo_mass] the standard-input family charges, at the
    same stop weight — the two coordinates are weighted identically, and
    only the coordinate differs. *)
Lemma file_demo_fire_ceiling :
  (file_geometric_cylinder_mass file_demo_p file_demo_bs == 7 # 2048)%Q.
Proof. vm_compute. reflexivity. Qed.

(** THE BOUND: every admissible list drawn from the cylinder weighs at
    most the ceiling.  One [MeasureLib.file_geometric_bound]; the
    existential the cylinder asks for is discharged by the caller, at
    the fire set it actually has. *)
Lemma file_demo_fire_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_file_cylinder file_demo_argv file_demo_envp file_demo_fs0
       file_demo_path file_demo_stdin file_demo_bs (fin_core f)) ->
  (core_sum (cd_weight file_demo_cd) l <= 7 # 2048)%Q.
Proof.
  intros l Hnd Hcyl.
  rewrite <- file_demo_fire_ceiling.
  unfold file_demo_cd, file_geometric_argv1.
  apply (file_geometric_bound file_demo_p file_demo_argv file_demo_envp
           file_demo_fs0 file_demo_path file_demo_stdin
           file_demo_p_nonneg file_demo_p_le_1 file_demo_bs l Hnd Hcyl).
Qed.

(** The length slice, which is the other bound the family exports: every
    admissible list whose members' input files all have the SAME length
    weighs at most [p (1 - p)^n], with the 256 alternatives per byte
    charged nothing.  Instantiated at [n = 1]. *)
Lemma file_demo_slice_bound_at_one : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_core f = file_core file_demo_argv file_demo_envp file_demo_fs0
                    file_demo_path file_demo_stdin
                    (fs_file file_demo_path (fin_image_fs f))
     /\ length (fs_file file_demo_path (fin_image_fs f)) = 1%nat) ->
  (core_sum (cd_weight file_demo_cd) l <= 7 # 64)%Q.
Proof.
  intros l Hnd Hslice.
  eapply Qle_trans.
  - unfold file_demo_cd, file_geometric_argv1.
    apply (file_geometric_slice_bound file_demo_p file_demo_argv
             file_demo_envp file_demo_fs0 file_demo_path file_demo_stdin
             file_demo_p_nonneg file_demo_p_le_1 1%nat l Hnd Hslice).
  - apply Qle_of_Qeq. vm_compute. reflexivity.
Qed.

(* =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= *)

Module File_D <: DISTRIBUTION.
  Definition w : FinProcInput -> Q := cd_lift file_demo_cd.
  Definition M : Q := cd_mass file_demo_cd.
  Definition w_nonneg : forall f, (0 <= w f)%Q := cd_lift_nonneg file_demo_cd.
  Lemma M_nonneg : (0 <= M)%Q.
  Proof. unfold M. rewrite file_demo_mass_is_one. exact Qle_0_1. Qed.
  Definition w_core_blind :
    forall f g, fin_core f = fin_core g -> (w f == w g)%Q :=
    cd_lift_core_blind file_demo_cd.
End File_D.

Lemma file_demo_weight_bound_T_of : forall C b,
  (forall f, Classifier.rejects C f ->
     in_file_cylinder file_demo_argv file_demo_envp file_demo_fs0
       file_demo_path file_demo_stdin file_demo_bs (fin_core f)) ->
  (7 # 2048 <= b)%Q ->
  weight_bound_T C File_D.w File_D.M b.
Proof.
  intros C b Hfire Hb l Hnd Hrej.
  unfold File_D.w. rewrite <- core_sum_cd_lift.
  apply (Qle_trans _ (7 # 2048)%Q).
  - apply file_demo_fire_bound;
      [exact Hnd | intros f Hf; apply Hfire, Hrej, Hf].
  - unfold File_D.M. rewrite file_demo_mass_is_one.
    apply (Qle_trans _ b); [exact Hb | apply Qle_of_Qeq; ring].
Qed.

(** At a round multiplier a task would declare: a classifier that fires
    only on binary input files carries at most a hundredth of the mass. *)
Lemma file_demo_weight_bound_T_hundredth : forall C,
  (forall f, Classifier.rejects C f ->
     in_file_cylinder file_demo_argv file_demo_envp file_demo_fs0
       file_demo_path file_demo_stdin file_demo_bs (fin_core f)) ->
  weight_bound_T C File_D.w File_D.M (1 # 100).
Proof.
  intros C Hfire. apply file_demo_weight_bound_T_of; [exact Hfire |].
  apply (proj1 (Qle_bool_iff _ _)). vm_compute. reflexivity.
Qed.

(* =========================================================================
   Non-vacuity: inside the cylinder, and the mass is a supremum
   ========================================================================= *)

(** Two cores of the cylinder: the file that stops at the NUL byte, and
    the file that carries one byte more. *)
Definition file_demo_core_stop : FinCore :=
  file_core file_demo_argv file_demo_envp file_demo_fs0 file_demo_path
    file_demo_stdin [file_demo_nul].
Definition file_demo_core_ext : FinCore :=
  file_core file_demo_argv file_demo_envp file_demo_fs0 file_demo_path
    file_demo_stdin [file_demo_nul; file_demo_a].

Definition file_demo_fire_list : list FinProcInput :=
  List.map core_input [file_demo_core_stop; file_demo_core_ext].

(** HOW MUCH OF THE CEILING IS REAL.  The two cores are in the cylinder,
    the list is admissible — and duplicate-freedom is where
    [MeasureLib.file_core_inj] is spent: two cores differing only in the
    varied file's contents are distinct because the embedding into the
    file system is injective, which is a lemma and not an observation.
    The last conjunct is the strictness. *)
Lemma file_demo_fire_slack :
  in_file_cylinder file_demo_argv file_demo_envp file_demo_fs0
    file_demo_path file_demo_stdin file_demo_bs file_demo_core_stop
  /\ in_file_cylinder file_demo_argv file_demo_envp file_demo_fs0
       file_demo_path file_demo_stdin file_demo_bs file_demo_core_ext
  /\ List.NoDup (List.map fin_core file_demo_fire_list)
  /\ ~ (7 # 2048 <= core_sum (cd_weight file_demo_cd) file_demo_fire_list)%Q.
Proof.
  split; [| split; [| split]].
  - exists []. reflexivity.
  - exists [file_demo_a]. reflexivity.
  - unfold file_demo_fire_list. rewrite map_fin_core_core_input.
    apply List.NoDup_cons.
    + intros [Heq | []].
      unfold file_demo_core_stop, file_demo_core_ext in Heq.
      apply file_core_inj in Heq.
      apply (f_equal (@length byte)) in Heq. cbn [length] in Heq.
      discriminate Heq.
    + apply List.NoDup_cons; [intros [] | apply List.NoDup_nil].
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate.
Qed.

(** THE LOWER HALF of the certificate pair, at a concrete margin: some
    admissible list weighs within a thousandth of the declared mass.  A
    task prints this beside the upper bound to show that the [1] it
    declared is not an overstatement of what the weight actually
    carries. *)
Lemma file_demo_mass_lower_at_a_thousandth :
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (1 - (1 # 1000) <= core_sum (cd_weight file_demo_cd) l)%Q.
Proof.
  unfold file_demo_cd, file_geometric_argv1.
  apply (file_geometric_mass_lower_certificate file_demo_p file_demo_argv
           file_demo_envp file_demo_fs0 file_demo_path file_demo_stdin
           file_demo_p_nonneg file_demo_p_le_1 (1 # 1000)%Q);
    reflexivity.
Qed.

(** ... and it is a SUPREMUM and not a maximum: no admissible list
    whatever attains the declared mass, at this stop weight.  The two
    together are the honest reading of a declared [1] — approached, never
    reached. *)
Lemma file_demo_mass_not_attained : forall l : list FinProcInput,
  List.NoDup (List.map fin_core l) ->
  ~ (core_sum (cd_weight file_demo_cd) l == 1)%Q.
Proof.
  unfold file_demo_cd, file_geometric_argv1.
  apply (file_geometric_mass_supremum_not_maximum file_demo_p file_demo_argv
           file_demo_envp file_demo_fs0 file_demo_path file_demo_stdin
           file_demo_p_nonneg file_demo_p_le_1).
  reflexivity.
Qed.

(** THE MISCONFIGURATION, at this file's stop weight: the library's pin
    that an instance whose argv does not name the path is invisible to
    the program it is built for.  It declares mass [1], puts positive
    weight on two distinct file contents, and those two cores hold the
    SAME bytes at the path argv actually names.  This is what
    [file_demo_argv_names_path] buys, made concrete. *)
Lemma file_demo_misconfiguration_is_invisible :
  ~ argv_names_path file_misconfigured_argv file_example_path
  /\ (0 < cd_weight (file_geometric file_demo_p file_misconfigured_argv [] Fs.fs_empty
                       file_example_path []
                       file_demo_p_nonneg file_demo_p_le_1)
            (file_core file_misconfigured_argv [] Fs.fs_empty file_example_path [] []))%Q
  /\ (0 < cd_weight (file_geometric file_demo_p file_misconfigured_argv [] Fs.fs_empty
                       file_example_path []
                       file_demo_p_nonneg file_demo_p_le_1)
            (file_core file_misconfigured_argv [] Fs.fs_empty file_example_path []
               [Z_to_bv 8 65]))%Q
  /\ fs_file file_other_path
       (core_fs (file_core file_misconfigured_argv [] Fs.fs_empty file_example_path []
                   []))
     = fs_file file_other_path
         (core_fs (file_core file_misconfigured_argv [] Fs.fs_empty file_example_path []
                     [Z_to_bv 8 65])).
Proof.
  exact (file_geometric_needs_argv_to_name_the_path file_demo_p
           file_demo_p_nonneg file_demo_p_le_1 eq_refl eq_refl).
Qed.

(** The whole-space upper certificate for the same distribution: the
    bound a task gets with no description of its fire set at all. *)
Lemma file_demo_whole_space_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight file_demo_cd) l <= 1)%Q.
Proof.
  intros l Hnd. unfold file_demo_cd, file_geometric_argv1.
  apply (file_geometric_mass_upper file_demo_p file_demo_argv file_demo_envp
           file_demo_fs0 file_demo_path file_demo_stdin
           file_demo_p_nonneg file_demo_p_le_1 l Hnd).
Qed.
