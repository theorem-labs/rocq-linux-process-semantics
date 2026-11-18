(** * Examples.measure_lib_demo.Calibrated — the calibrated mixture,
      worked

    DEMO FILE (not part of the trusted specification, and not installed).
    [MeasureLib.calibrated_mixture] is the composition the library was
    requested for: fifteen sixteenths of the mass on standard input over
    ONE fixed launch-time environment, and a sixteenth spread over
    environments as well, at [r = 1 # 5] entries and [q_e = 1 # 33] bytes
    per entry.  It is [MeasureLib.cd_scale] twice and
    [MeasureLib.cd_mix2] once and no new combinator, which is the point
    of it having a name.  This file instantiates it at one stop weight
    and carries it to a [Measure.weight_bound_T].

    ** Why the ceiling comes out as the cylinder's own mass

    The fire set below lies in the fixed environment: every core in it
    has the canonical environment exactly, and a standard input
    extending one NUL byte.  Both components then charge it the same
    number — the stdin-only component through its cylinder, the
    envp-varying component through its cylinder over the EMPTY
    environment prefix, whose environment factor is [1].  The two are
    then scaled by shares that sum to [1], so the mixture's ceiling is
    the cylinder mass itself, [7 # 2048].

    That is worth writing down rather than deriving in the reader's
    head, because it is the property a task actually wants from a
    calibrated mixture: mixing in an environment-varying component costs
    NOTHING on fire sets that do not vary the environment.  A fire set
    that does vary it pays, and pays through the second component's
    environment factor.

    ** What the mixture does buy, and where

    [calib_envp_component_carries_mass] is the bite:
    [MeasureLib.calibrated_mixture_envp_bites] instantiated here, showing
    a core with a non-empty environment that the stdin-only component
    weighs at ZERO and the mixture weighs positively.  Without that, the
    sixteenth would be decoration — the whole reason to mix is that the
    envp-varying component reaches cores the other one cannot see.

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
   The one parameter a task picks, and the canonical environment
   ========================================================================= *)

(** The stop weight is the ONLY thing [MeasureLib.calibrated_mixture]
    leaves open: the two shares and the environment coordinate's two
    parameters are the calibration and are fixed by the library.  A task
    configuration picks [p_stop] per binary by format class. *)
Definition calib_p : Q := (1 # 8)%Q.

Lemma calib_p_nonneg : (0 <= calib_p)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma calib_p_le_1 : (calib_p <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

(** The task's canonical launch-time environment.  It is what the
    stdin-only component FIXES; the envp-varying component takes the same
    argv and file system and no environment at all, which is the whole
    difference between the two. *)
Definition calib_argv : list (list byte) := [[Z_to_bv 8 119; Z_to_bv 8 99]].
Definition calib_envp : list (list byte) := [].
Definition calib_fs : Fs.Fs := Fs.fs_empty.

Definition calib_cd : CoreDistribution :=
  calibrated_mixture calib_p calib_argv calib_envp calib_fs
    calib_p_nonneg calib_p_le_1.

(** The declared mass is [1], and it is the two shares adding up rather
    than a numeral written here: [15 # 16] of one component's declared
    [1] plus [1 # 16] of the other's.  Change one share without the other
    and this stops holding. *)
Lemma calib_mass_is_one : (cd_mass calib_cd == 1)%Q.
Proof.
  unfold calib_cd.
  apply (calibrated_mixture_mass_is_one calib_p calib_argv calib_envp calib_fs
           calib_p_nonneg calib_p_le_1).
Qed.

(* =========================================================================
   The fire set: the canonical environment, standard input from a NUL
   ========================================================================= *)

Definition calib_nul : byte := Z_to_bv 8 0.
Definition calib_a : byte := Z_to_bv 8 65.
Definition calib_bs : list byte := [calib_nul].

(** THE CEILING, as the two component ceilings scaled and added, stated
    as a [Qeq] before it is used so that the number in the demonstrations
    is visibly what the composition yields.  The second component is
    charged its cylinder over the EMPTY environment prefix — the
    fire set fixes an environment rather than a prefix of one, and the
    empty prefix is the one every environment extends. *)
Lemma calib_fire_ceiling :
  (calibrated_co_lambda * stdin_geometric_cylinder_mass calib_p calib_bs
   + calibrated_lambda
     * stdin_envp_geometric_cylinder_mass calib_p calibrated_r calibrated_q
         [] calib_bs
   == 7 # 2048)%Q.
Proof. vm_compute. reflexivity. Qed.

(** THE BOUND.  One [MeasureLib.cd_mix2_bound], one
    [MeasureLib.cd_scale_bound] per component, and one library cylinder
    bound under each — the same four-step shape [MeasureLib]'s worked
    demonstration uses, at a mixture whose components are both geometric
    rather than one finite and one geometric.

    The two side conditions are where the fire set is spent.  For the
    stdin-only component: a fire core is the canonical environment
    followed by an extension of [[0]].  For the envp-varying component:
    the same core, read as an environment extending the empty prefix and
    a standard input extending [[0]] — so the environment existential is
    discharged with the canonical environment itself. *)
Lemma calib_fire_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     exists ext, fin_core f
                 = mkFinCore calib_argv calib_envp calib_fs (calib_bs ++ ext)) ->
  (core_sum (cd_weight calib_cd) l <= 7 # 2048)%Q.
Proof.
  intros l Hnd Hfire.
  rewrite <- calib_fire_ceiling.
  unfold calib_cd, calibrated_mixture.
  apply cd_mix2_bound.
  - apply cd_scale_bound.
    apply (stdin_geometric_bound calib_p calib_argv calib_envp calib_fs
             calib_p_nonneg calib_p_le_1 calib_bs l Hnd).
    intros f Hf. destruct (Hfire f Hf) as [ext Hext].
    exists ext. exact Hext.
  - apply cd_scale_bound.
    apply (stdin_envp_geometric_bound calib_p calibrated_r calibrated_q
             calib_argv calib_fs calib_p_nonneg calib_p_le_1
             calibrated_r_nonneg calibrated_r_le_1
             calibrated_q_nonneg calibrated_q_le_1 [] calib_bs l Hnd).
    intros f Hf. destruct (Hfire f Hf) as [ext Hext].
    exists calib_envp, ext. exact Hext.
Qed.

(** The whole-space certificate for the mixture itself, which is the
    bound a task gets with no description of its fire set at all. *)
Lemma calib_whole_space_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight calib_cd) l <= 1)%Q.
Proof.
  intros l Hnd. unfold calib_cd.
  apply (calibrated_mixture_mass_upper calib_p calib_argv calib_envp calib_fs
           calib_p_nonneg calib_p_le_1 l Hnd).
Qed.

(* =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= *)

Module Calib_D <: DISTRIBUTION.
  Definition w : FinProcInput -> Q := cd_lift calib_cd.
  Definition M : Q := cd_mass calib_cd.
  Definition w_nonneg : forall f, (0 <= w f)%Q := cd_lift_nonneg calib_cd.
  Lemma M_nonneg : (0 <= M)%Q.
  Proof. unfold M. rewrite calib_mass_is_one. exact Qle_0_1. Qed.
  Definition w_core_blind :
    forall f g, fin_core f = fin_core g -> (w f == w g)%Q :=
    cd_lift_core_blind calib_cd.
End Calib_D.

Lemma calib_weight_bound_T_of : forall C b,
  (forall f, Classifier.rejects C f ->
     exists ext, fin_core f
                 = mkFinCore calib_argv calib_envp calib_fs (calib_bs ++ ext)) ->
  (7 # 2048 <= b)%Q ->
  weight_bound_T C Calib_D.w Calib_D.M b.
Proof.
  intros C b Hfire Hb l Hnd Hrej.
  unfold Calib_D.w. rewrite <- core_sum_cd_lift.
  apply (Qle_trans _ (7 # 2048)%Q).
  - apply calib_fire_bound;
      [exact Hnd | intros f Hf; apply Hfire, Hrej, Hf].
  - unfold Calib_D.M. rewrite calib_mass_is_one.
    apply (Qle_trans _ b); [exact Hb | apply Qle_of_Qeq; ring].
Qed.

Lemma calib_weight_bound_T_hundredth : forall C,
  (forall f, Classifier.rejects C f ->
     exists ext, fin_core f
                 = mkFinCore calib_argv calib_envp calib_fs (calib_bs ++ ext)) ->
  weight_bound_T C Calib_D.w Calib_D.M (1 # 100).
Proof.
  intros C Hfire. apply calib_weight_bound_T_of; [exact Hfire |].
  apply (proj1 (Qle_bool_iff _ _)). vm_compute. reflexivity.
Qed.

(* =========================================================================
   Non-vacuity: the sixteenth is not decoration, and the mass is real
   ========================================================================= *)

(** WHAT THE MIXTURE BUYS.  A core with a non-empty environment: the
    stdin-only component weighs it at exactly zero, and the mixture
    weighs it positively.  So the sixteenth reaches cores the
    fifteen-sixteenths cannot see, which is the whole reason to mix
    rather than to declare the stdin-only family alone. *)
Lemma calib_envp_component_carries_mass :
  cd_weight (stdin_geometric calib_p [] [] Fs.fs_empty calib_p_nonneg calib_p_le_1)
    envp_example_named = 0%Q
  /\ (0 < cd_weight (calibrated_mixture calib_p [] [] Fs.fs_empty
                       calib_p_nonneg calib_p_le_1) envp_example_named)%Q.
Proof.
  exact (calibrated_mixture_envp_bites calib_p calib_p_nonneg calib_p_le_1
           eq_refl eq_refl).
Qed.

(** THE LOWER HALF, at a concrete margin: some admissible list weighs
    within a thousandth of the declared [1].  This is the one
    certificate in the library that does NOT compose from its
    components' — both components' masses are suprema that no list
    attains, so the mixture needs one list good for both at once, at
    depths chosen to cover the fixed environment as well as the margin. *)
Lemma calib_mass_lower_at_a_thousandth :
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (1 - (1 # 1000) <= core_sum (cd_weight calib_cd) l)%Q.
Proof.
  unfold calib_cd.
  apply (calibrated_mixture_mass_lower_certificate calib_p calib_argv
           calib_envp calib_fs calib_p_nonneg calib_p_le_1 (1 # 1000)%Q);
    reflexivity.
Qed.

(** Two cores of the fire set, and the slack.  The cylinder holds every
    standard input beginning with a NUL byte, at every length; a
    two-element list weighs strictly less than the ceiling that charges
    for all of them. *)
Definition calib_core_stop : FinCore :=
  mkFinCore calib_argv calib_envp calib_fs [calib_nul].
Definition calib_core_ext : FinCore :=
  mkFinCore calib_argv calib_envp calib_fs [calib_nul; calib_a].

Definition calib_fire_list : list FinProcInput :=
  List.map core_input [calib_core_stop; calib_core_ext].

Lemma calib_fire_slack :
  List.NoDup (List.map fin_core calib_fire_list)
  /\ (forall f, List.In f calib_fire_list ->
        exists ext, fin_core f
                    = mkFinCore calib_argv calib_envp calib_fs
                        (calib_bs ++ ext))
  /\ ~ (7 # 2048 <= core_sum (cd_weight calib_cd) calib_fire_list)%Q.
Proof.
  split; [| split].
  - unfold calib_fire_list. rewrite map_fin_core_core_input.
    apply List.NoDup_cons.
    + intros [Heq | []].
      unfold calib_core_stop, calib_core_ext in Heq. inversion Heq.
    + apply List.NoDup_cons; [intros [] | apply List.NoDup_nil].
  - intros f Hf. unfold calib_fire_list in Hf. cbn [List.map] in Hf.
    destruct Hf as [Hf | [Hf | []]]; subst f; rewrite fin_core_core_input.
    + exists []. reflexivity.
    + exists [calib_a]. reflexivity.
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate.
Qed.
