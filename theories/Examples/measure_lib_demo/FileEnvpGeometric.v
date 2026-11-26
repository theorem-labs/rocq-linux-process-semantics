(** * Examples.measure_lib_demo.FileEnvpGeometric — the file-and-
      environment family, worked

    DEMO FILE (not part of the trusted specification, and not installed).
    The fourth base family: [MeasureLib.file_envp_geometric] varies the
    contents of one named file AND the launch-time environment together,
    over a fixed argv, base file system and standard input.  It is to
    [MeasureLib.file_geometric] what
    [MeasureLib.stdin_envp_geometric] is to
    [MeasureLib.stdin_geometric], and it is the family a task reaches for
    when its program both reads a path argument and consults the
    environment.

    ** The two coordinates multiply, and the cylinder has two prefixes

    A core is in the cylinder over [(es, bs)] when its environment
    extends [es] and the varied file's contents extend [bs].  The mass is
    the product of what the two coordinates contribute —
    [MeasureLib.envp_factor] on one, [MeasureLib.geo_mass] on the other —
    so it is the same number [Examples.measure_lib_demo.EnvpGeometric]
    reaches at the same three parameters and the same two prefixes.
    That is not a coincidence worth hiding: the two families differ in
    WHICH coordinate carries the byte geometry, and in nothing else, so
    a task that knows the ceiling for one knows it for the other.

    ** The argv/path coupling, again by construction

    [MeasureLib.file_envp_geometric_argv1] takes the path once, so the
    mismatch this family shares with [MeasureLib.file_geometric] is not
    expressible through it.  [file_envp_demo_argv_names_path] is the
    receipt, and [file_envp_demo_misconfiguration_is_invisible] is the
    library's pin of what the mismatched instance looks like, at this
    file's three parameters.

    Nothing exhibited here is claimed VALID and nothing is claimed
    rejected by any classifier.

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith NArith List QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  FinInput Measure MeasureLib.
From LinuxProcessSemantics.EquivalenceDefinition Require Classifier.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The task's fixed data, and the three parameters
   ========================================================================= *)

Definition file_envp_demo_prog : list byte := [Z_to_bv 8 119; Z_to_bv 8 99].
Definition file_envp_demo_path : Fs.path :=
  [Z_to_bv 8 47; Z_to_bv 8 105; Z_to_bv 8 110].
Definition file_envp_demo_fs0 : Fs.Fs := Fs.fs_empty.
Definition file_envp_demo_stdin : list byte := [].

Definition file_envp_demo_p : Q := (1 # 8)%Q.
Definition file_envp_demo_r : Q := (1 # 4)%Q.
Definition file_envp_demo_q : Q := (1 # 16)%Q.

Lemma file_envp_demo_p_nonneg : (0 <= file_envp_demo_p)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma file_envp_demo_p_le_1 : (file_envp_demo_p <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma file_envp_demo_r_nonneg : (0 <= file_envp_demo_r)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma file_envp_demo_r_le_1 : (file_envp_demo_r <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma file_envp_demo_q_nonneg : (0 <= file_envp_demo_q)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma file_envp_demo_q_le_1 : (file_envp_demo_q <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Definition file_envp_demo_argv : list (list byte) :=
  path_argv file_envp_demo_prog file_envp_demo_path.

(** THE DISTRIBUTION, through the coupled constructor. *)
Definition file_envp_demo_cd : CoreDistribution :=
  file_envp_geometric_argv1 file_envp_demo_p file_envp_demo_r
    file_envp_demo_q file_envp_demo_prog file_envp_demo_fs0
    file_envp_demo_path file_envp_demo_stdin
    file_envp_demo_p_nonneg file_envp_demo_p_le_1
    file_envp_demo_r_nonneg file_envp_demo_r_le_1
    file_envp_demo_q_nonneg file_envp_demo_q_le_1.

Lemma file_envp_demo_mass_is_one : cd_mass file_envp_demo_cd = 1%Q.
Proof. reflexivity. Qed.

Lemma file_envp_demo_argv_names_path :
  argv_names_path file_envp_demo_argv file_envp_demo_path
  /\ file_envp_demo_cd
     = file_envp_geometric file_envp_demo_p file_envp_demo_r
         file_envp_demo_q file_envp_demo_argv file_envp_demo_fs0
         file_envp_demo_path file_envp_demo_stdin
         file_envp_demo_p_nonneg file_envp_demo_p_le_1
         file_envp_demo_r_nonneg file_envp_demo_r_le_1
         file_envp_demo_q_nonneg file_envp_demo_q_le_1.
Proof.
  exact (file_envp_geometric_argv1_names_path file_envp_demo_p
           file_envp_demo_r file_envp_demo_q file_envp_demo_prog
           file_envp_demo_fs0 file_envp_demo_path file_envp_demo_stdin
           file_envp_demo_p_nonneg file_envp_demo_p_le_1
           file_envp_demo_r_nonneg file_envp_demo_r_le_1
           file_envp_demo_q_nonneg file_envp_demo_q_le_1).
Qed.

(* =========================================================================
   The fire set: one environment prefix, one file prefix
   ========================================================================= *)

Definition file_envp_demo_v : byte := Z_to_bv 8 86.
Definition file_envp_demo_w : byte := Z_to_bv 8 87.
Definition file_envp_demo_nul : byte := Z_to_bv 8 0.
Definition file_envp_demo_a : byte := Z_to_bv 8 65.

Definition file_envp_demo_es : list (list byte) := [[file_envp_demo_v]].
Definition file_envp_demo_bs : list byte := [file_envp_demo_nul].

(** THE CEILING, exactly as in the standard-input twin and for the same
    four factors: [1 - r] for continuing past no entry, the one-byte
    entry's own weight, and the byte-geometric factor on the varied
    coordinate. *)
Lemma file_envp_demo_fire_ceiling :
  (file_envp_geometric_cylinder_mass file_envp_demo_p file_envp_demo_r
     file_envp_demo_q file_envp_demo_es file_envp_demo_bs
     == 315 # 536870912)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma file_envp_demo_fire_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_file_envp_cylinder file_envp_demo_argv file_envp_demo_fs0
       file_envp_demo_path file_envp_demo_stdin file_envp_demo_es
       file_envp_demo_bs (fin_core f)) ->
  (core_sum (cd_weight file_envp_demo_cd) l <= 315 # 536870912)%Q.
Proof.
  intros l Hnd Hcyl.
  rewrite <- file_envp_demo_fire_ceiling.
  unfold file_envp_demo_cd, file_envp_geometric_argv1.
  apply (file_envp_geometric_bound file_envp_demo_p file_envp_demo_r
           file_envp_demo_q file_envp_demo_argv file_envp_demo_fs0
           file_envp_demo_path file_envp_demo_stdin
           file_envp_demo_p_nonneg file_envp_demo_p_le_1
           file_envp_demo_r_nonneg file_envp_demo_r_le_1
           file_envp_demo_q_nonneg file_envp_demo_q_le_1
           file_envp_demo_es file_envp_demo_bs l Hnd Hcyl).
Qed.

(** The length slice, charging the environment nothing, at [n = 2]. *)
Lemma file_envp_demo_slice_bound_at_two : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_core f = file_envp_core file_envp_demo_argv file_envp_demo_fs0
                    file_envp_demo_path file_envp_demo_stdin (fin_envp f)
                    (fs_file file_envp_demo_path (fin_image_fs f))
     /\ length (fs_file file_envp_demo_path (fin_image_fs f)) = 2%nat) ->
  (core_sum (cd_weight file_envp_demo_cd) l <= 49 # 512)%Q.
Proof.
  intros l Hnd Hslice.
  eapply Qle_trans.
  - unfold file_envp_demo_cd, file_envp_geometric_argv1.
    apply (file_envp_geometric_slice_bound file_envp_demo_p file_envp_demo_r
             file_envp_demo_q file_envp_demo_argv file_envp_demo_fs0
             file_envp_demo_path file_envp_demo_stdin
             file_envp_demo_p_nonneg file_envp_demo_p_le_1
             file_envp_demo_r_nonneg file_envp_demo_r_le_1
             file_envp_demo_q_nonneg file_envp_demo_q_le_1
             2%nat l Hnd Hslice).
  - apply Qle_of_Qeq. vm_compute. reflexivity.
Qed.

(* =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= *)

Module FileEnvp_D <: DISTRIBUTION.
  Definition w : FinProcInput -> Q := cd_lift file_envp_demo_cd.
  Definition M : Q := cd_mass file_envp_demo_cd.
  Definition w_nonneg : forall f, (0 <= w f)%Q :=
    cd_lift_nonneg file_envp_demo_cd.
  Lemma M_nonneg : (0 <= M)%Q.
  Proof. unfold M. rewrite file_envp_demo_mass_is_one. exact Qle_0_1. Qed.
  Definition w_core_blind :
    forall f g, fin_core f = fin_core g -> (w f == w g)%Q :=
    cd_lift_core_blind file_envp_demo_cd.
End FileEnvp_D.

Lemma file_envp_demo_weight_bound_T_of : forall C b,
  (forall f, Classifier.rejects C f ->
     in_file_envp_cylinder file_envp_demo_argv file_envp_demo_fs0
       file_envp_demo_path file_envp_demo_stdin file_envp_demo_es
       file_envp_demo_bs (fin_core f)) ->
  (315 # 536870912 <= b)%Q ->
  weight_bound_T C FileEnvp_D.w FileEnvp_D.M b.
Proof.
  intros C b Hfire Hb l Hnd Hrej.
  unfold FileEnvp_D.w. rewrite <- core_sum_cd_lift.
  apply (Qle_trans _ (315 # 536870912)%Q).
  - apply file_envp_demo_fire_bound;
      [exact Hnd | intros f Hf; apply Hfire, Hrej, Hf].
  - unfold FileEnvp_D.M. rewrite file_envp_demo_mass_is_one.
    apply (Qle_trans _ b); [exact Hb | apply Qle_of_Qeq; ring].
Qed.

Lemma file_envp_demo_weight_bound_T_thousandth : forall C,
  (forall f, Classifier.rejects C f ->
     in_file_envp_cylinder file_envp_demo_argv file_envp_demo_fs0
       file_envp_demo_path file_envp_demo_stdin file_envp_demo_es
       file_envp_demo_bs (fin_core f)) ->
  weight_bound_T C FileEnvp_D.w FileEnvp_D.M (1 # 1000).
Proof.
  intros C Hfire. apply file_envp_demo_weight_bound_T_of; [exact Hfire |].
  apply (proj1 (Qle_bool_iff _ _)). vm_compute. reflexivity.
Qed.

(* =========================================================================
   Non-vacuity
   ========================================================================= *)

(** Two cores of the cylinder, extending it in BOTH coordinates at once:
    the one that stops at both prefixes, and the one carrying a second
    environment entry and a second file byte. *)
Definition file_envp_demo_core_stop : FinCore :=
  file_envp_core file_envp_demo_argv file_envp_demo_fs0 file_envp_demo_path
    file_envp_demo_stdin [[file_envp_demo_v]] [file_envp_demo_nul].
Definition file_envp_demo_core_ext : FinCore :=
  file_envp_core file_envp_demo_argv file_envp_demo_fs0 file_envp_demo_path
    file_envp_demo_stdin [[file_envp_demo_v]; [file_envp_demo_w]]
    [file_envp_demo_nul; file_envp_demo_a].

Definition file_envp_demo_fire_list : list FinProcInput :=
  List.map core_input
    [file_envp_demo_core_stop; file_envp_demo_core_ext].

Lemma file_envp_demo_fire_slack :
  in_file_envp_cylinder file_envp_demo_argv file_envp_demo_fs0
    file_envp_demo_path file_envp_demo_stdin file_envp_demo_es
    file_envp_demo_bs file_envp_demo_core_stop
  /\ in_file_envp_cylinder file_envp_demo_argv file_envp_demo_fs0
       file_envp_demo_path file_envp_demo_stdin file_envp_demo_es
       file_envp_demo_bs file_envp_demo_core_ext
  /\ List.NoDup (List.map fin_core file_envp_demo_fire_list)
  /\ ~ (315 # 536870912
          <= core_sum (cd_weight file_envp_demo_cd)
               file_envp_demo_fire_list)%Q.
Proof.
  split; [| split; [| split]].
  - exists [], []. reflexivity.
  - exists [[file_envp_demo_w]], [file_envp_demo_a]. reflexivity.
  - unfold file_envp_demo_fire_list. rewrite map_fin_core_core_input.
    apply List.NoDup_cons.
    + intros [Heq | []].
      unfold file_envp_demo_core_stop, file_envp_demo_core_ext,
             file_envp_core, file_core in Heq.
      inversion Heq.
    + apply List.NoDup_cons; [intros [] | apply List.NoDup_nil].
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate.
Qed.

(** The environment really carries mass here too: a core whose argv is
    not the fixed one weighs exactly zero, so the family is not a
    constant. *)
Definition file_envp_demo_core_other_argv : FinCore :=
  mkFinCore [[file_envp_demo_a]] [[file_envp_demo_v]]
    (Fs.fs_create_file file_envp_demo_fs0 file_envp_demo_path [file_envp_demo_nul])
    file_envp_demo_stdin.

Lemma file_envp_demo_off_argv_weighs_nothing :
  cd_weight file_envp_demo_cd file_envp_demo_core_other_argv = 0%Q.
Proof.
  unfold file_envp_demo_cd, file_envp_geometric_argv1.
  cbn [cd_weight file_envp_geometric].
  apply file_envp_geo_weight_off_argv_zero.
  unfold file_envp_demo_core_other_argv, file_envp_demo_argv, path_argv.
  cbn [core_argv]. discriminate.
Qed.

(** THE LOWER HALF of the certificate pair, at a concrete margin. *)
Lemma file_envp_demo_mass_lower_at_a_thousandth :
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (1 - (1 # 1000) <= core_sum (cd_weight file_envp_demo_cd) l)%Q.
Proof.
  unfold file_envp_demo_cd, file_envp_geometric_argv1.
  apply (file_envp_geometric_mass_lower_certificate file_envp_demo_p
           file_envp_demo_r file_envp_demo_q file_envp_demo_argv
           file_envp_demo_fs0 file_envp_demo_path file_envp_demo_stdin
           file_envp_demo_p_nonneg file_envp_demo_p_le_1
           file_envp_demo_r_nonneg file_envp_demo_r_le_1
           file_envp_demo_q_nonneg file_envp_demo_q_le_1 (1 # 1000)%Q);
    reflexivity.
Qed.

(** THE MISCONFIGURATION, at this file's three parameters. *)
Lemma file_envp_demo_misconfiguration_is_invisible :
  ~ argv_names_path file_misconfigured_argv file_example_path
  /\ (0 < cd_weight (file_envp_geometric file_envp_demo_p file_envp_demo_r
                       file_envp_demo_q file_misconfigured_argv Fs.fs_empty
                       file_example_path []
                       file_envp_demo_p_nonneg file_envp_demo_p_le_1
                       file_envp_demo_r_nonneg file_envp_demo_r_le_1
                       file_envp_demo_q_nonneg file_envp_demo_q_le_1)
            (file_envp_core file_misconfigured_argv Fs.fs_empty file_example_path []
               [] []))%Q
  /\ (0 < cd_weight (file_envp_geometric file_envp_demo_p file_envp_demo_r
                       file_envp_demo_q file_misconfigured_argv Fs.fs_empty
                       file_example_path []
                       file_envp_demo_p_nonneg file_envp_demo_p_le_1
                       file_envp_demo_r_nonneg file_envp_demo_r_le_1
                       file_envp_demo_q_nonneg file_envp_demo_q_le_1)
            (file_envp_core file_misconfigured_argv Fs.fs_empty file_example_path []
               [] [Z_to_bv 8 65]))%Q
  /\ fs_file file_other_path
       (core_fs (file_envp_core file_misconfigured_argv Fs.fs_empty file_example_path []
                   [] []))
     = fs_file file_other_path
         (core_fs (file_envp_core file_misconfigured_argv Fs.fs_empty
                     file_example_path [] [] [Z_to_bv 8 65])).
Proof.
  exact (file_envp_geometric_needs_argv_to_name_the_path file_envp_demo_p
           file_envp_demo_r file_envp_demo_q
           file_envp_demo_p_nonneg file_envp_demo_p_le_1
           file_envp_demo_r_nonneg file_envp_demo_r_le_1
           file_envp_demo_q_nonneg file_envp_demo_q_le_1
           eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl).
Qed.

(** The whole-space upper certificate, and the mass as a supremum: the
    two halves that make the declared [1] a two-sided claim here too. *)
Lemma file_envp_demo_whole_space_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight file_envp_demo_cd) l <= 1)%Q.
Proof.
  intros l Hnd. unfold file_envp_demo_cd, file_envp_geometric_argv1.
  apply (file_envp_geometric_mass_upper file_envp_demo_p file_envp_demo_r
           file_envp_demo_q file_envp_demo_argv file_envp_demo_fs0
           file_envp_demo_path file_envp_demo_stdin
           file_envp_demo_p_nonneg file_envp_demo_p_le_1
           file_envp_demo_r_nonneg file_envp_demo_r_le_1
           file_envp_demo_q_nonneg file_envp_demo_q_le_1 l Hnd).
Qed.

Lemma file_envp_demo_mass_not_attained : forall l : list FinProcInput,
  List.NoDup (List.map fin_core l) ->
  ~ (core_sum (cd_weight file_envp_demo_cd) l == 1)%Q.
Proof.
  unfold file_envp_demo_cd, file_envp_geometric_argv1.
  apply (file_envp_geometric_mass_supremum_not_maximum file_envp_demo_p
           file_envp_demo_r file_envp_demo_q file_envp_demo_argv
           file_envp_demo_fs0 file_envp_demo_path file_envp_demo_stdin
           file_envp_demo_p_nonneg file_envp_demo_p_le_1
           file_envp_demo_r_nonneg file_envp_demo_r_le_1
           file_envp_demo_q_nonneg file_envp_demo_q_le_1).
  reflexivity.
Qed.
