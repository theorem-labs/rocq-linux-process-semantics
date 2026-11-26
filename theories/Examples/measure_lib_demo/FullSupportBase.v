(** * Examples.measure_lib_demo.FullSupportBase — the full-support base
      family, worked at rate one half

    DEMO FILE (not part of the trusted specification, and not installed).
    Every other file in this directory instantiates a family that weighs
    ZERO off one fixed template.  This one instantiates
    [MeasureLib.full_support_base], under which every core — every argv,
    every environment, every file system, every standard input — weighs
    strictly more than zero, and carries it through to a
    [Measure.weight_bound_T] on a fire set described by an argv and the
    contents of one file, both alone and inside the mixture a task
    actually ships.

    ** The eight rates, and why they are all one half

    A typical base component is
    a product over the four coordinates, with every byte string
    weighing [(1 # 2) * (1 # 512) ^ length] and every list weighing
    [(1 # 2) ^ (count + 1)] times its entries' product.  That is the
    family at all eight rates equal to [1 # 2]: [base_string_law] and
    [base_list_law] below are those two laws, proved against the
    library's own [geo_point] and entry-count shell so that the numbers
    a task prints are visibly the numbers the library weighs by.

    ** The fire set, and its bound

    The fire set is "argv is [prog; pth] and the file at [pth] begins
    with a NUL byte", which is the shape a task describes a
    content-triggered defect in.  It fixes ONE coordinate exactly and
    constrains ONE ENTRY of another while everything else — the
    environment, standard input, every other file, the entry count of
    the file system — stays free, so no cylinder bound covers it.
    [MeasureLib.full_support_base_argv_file_bound] does, at exactly
    the argv's own weight times the
    byte cylinder's mass on the contents coordinate.  Here that is
    [1 # 1125899906842624], which is [2 ^ -50]: forty-one halvings for
    the two-entry argv and nine for the one-byte prefix.

    ** Inside the shipping mixture

    A task does not ship the base family alone; it ships
    [cd_mix2 (cd_scale s structured) (cd_scale (1 - s) base)] with the
    base's share small.  [base_mixture_fire_bound] prices the same fire
    set under that mixture at a share of [6 # 100], with
    [MeasureLib.file_geometric] as the structured component: each
    component is charged through its own bound and the two are added by
    [MeasureLib.cd_mix2_bound].  The base component's charge is the
    smaller term by a wide margin, which is what "the base component is
    there for support, not for mass" means as a number.

    ** Non-vacuity, and the seam

    [base_fire_slack] pins that two cores really are in the fire set
    and weigh strictly less than the ceiling, so the bound is not
    attained; [base_every_core_positive] is full support itself, and
    [base_unsorted_fs_weighs] pins the seam: a core
    whose file system is NOT sorted — and so never [Fs.wf_fs] —
    still carries weight.  That is by design (see the family's header
    in [MeasureLib]); it is stated so nobody mistakes the declared mass
    for the mass reachable by valid images.  Nothing exhibited here is
    claimed valid and nothing is claimed rejected by any classifier. *)

From Stdlib Require Import ZArith NArith List QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  FinInput Measure MeasureLib.
From LinuxProcessSemantics.EquivalenceDefinition Require Classifier.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The rates, and the side conditions they cost
   ========================================================================= *)

(** One rate for all eight slots.  Two
    [Qle] facts and two [Qlt] facts, named once: the constructor takes
    the first pair sixteen times over, and the positivity lemma the
    second pair. *)
Definition base_half : Q := (1 # 2)%Q.

Lemma base_half_nonneg : (0 <= base_half)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma base_half_le_1 : (base_half <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma base_half_pos : (0 < base_half)%Q.
Proof. reflexivity. Qed.
Lemma base_half_lt_1 : (base_half < 1)%Q.
Proof. reflexivity. Qed.

(** THE DISTRIBUTION, declared mass [1]. *)
Definition base_cd : CoreDistribution :=
  full_support_base base_half base_half base_half base_half
    base_half base_half base_half base_half
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1.

Lemma base_mass_is_one : cd_mass base_cd = 1%Q.
Proof. reflexivity. Qed.

(* =========================================================================
   The two laws, as the library weighs them
   ========================================================================= *)

(** Every byte string weighs [(1 # 2) * (1 # 512) ^ length]: the
    per-byte factor [(1 - 1 # 2) * (1 # 256)] is [1 # 512]. *)
Lemma base_string_law : forall s : list byte,
  (geo_point base_half (length s) == (1 # 2) * Qpow (1 # 512) (length s))%Q.
Proof.
  intros s. unfold geo_point, geo_mass, base_half.
  rewrite (Qpow_Qeq ((1 - (1 # 2)) * (1 # 256)) (1 # 512) (length s));
    [reflexivity | vm_compute; reflexivity].
Qed.

(** Every list of [k] entries pays [(1 # 2) ^ (k + 1)] for its count. *)
Lemma base_list_law : forall k : nat,
  (base_half * Qpow (1 - base_half) k == Qpow (1 # 2) (S k))%Q.
Proof.
  intros k. rewrite Qpow_succ. unfold base_half.
  rewrite (Qpow_Qeq (1 - (1 # 2)) (1 # 2) k); [reflexivity | vm_compute; reflexivity].
Qed.

(* =========================================================================
   Full support: every core weighs something
   ========================================================================= *)

Lemma base_every_core_positive : forall c, (0 < cd_weight base_cd c)%Q.
Proof.
  intros c. unfold base_cd.
  apply full_support_base_positive; first
    [exact base_half_pos | exact base_half_lt_1].
Qed.

(** The seam, pinned.  This file system lists its two keys in the wrong
    order, so [Fs.fs_sorted] rejects it and it is never [Fs.wf_fs];
    the family weighs it anyway.  The declared mass [1] is the mass of
    the LAW, and the mass reachable by valid images is less. *)
Definition base_unsorted_fs : Fs.Fs :=
  Fs.mkFs [([Z_to_bv 8 98], Fs.EFile 1); ([Z_to_bv 8 97], Fs.EFile 2)]
    [(1%Z, Fs.mkInode [] 0); (2%Z, Fs.mkInode [Z_to_bv 8 65] 0)] [].

Definition base_unsorted_core : FinCore :=
  mkFinCore [] [] base_unsorted_fs [].

Lemma base_unsorted_fs_weighs :
  Fs.fs_sorted base_unsorted_fs = false
  /\ (0 < cd_weight base_cd base_unsorted_core)%Q.
Proof.
  split; [vm_compute; reflexivity | apply base_every_core_positive].
Qed.

(* =========================================================================
   The fire set: an argv, and the head of one file
   ========================================================================= *)

Definition base_prog : list byte := [Z_to_bv 8 119; Z_to_bv 8 99].
Definition base_pth : Fs.path := [Z_to_bv 8 47; Z_to_bv 8 116].
Definition base_argv : list (list byte) := path_argv base_prog base_pth.
Definition base_nul : byte := Z_to_bv 8 0.
Definition base_a : byte := Z_to_bv 8 65.
Definition base_bs : list byte := [base_nul].

(** THE CEILING, as an exact rational: the argv's weight — a stop after
    two entries, and two two-byte strings — times the mass of the
    one-byte contents cylinder. *)
Lemma base_fire_ceiling :
  (strings_point base_half base_half base_argv * geo_mass base_half (length base_bs)
     == 1 # 1125899906842624)%Q.
Proof. vm_compute. reflexivity. Qed.

(** THE BOUND: every admissible list whose records have the fixed argv
    and a file at [base_pth] beginning with NUL weighs at most the
    ceiling.  One [MeasureLib.full_support_base_argv_file_bound] and the
    [Qeq] that names the number. *)
Lemma base_fire_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_argv f = base_argv /\ file_at_extends base_pth base_bs (fin_core f)) ->
  (core_sum (cd_weight base_cd) l <= 1 # 1125899906842624)%Q.
Proof.
  intros l Hnd Hfire. rewrite <- base_fire_ceiling. unfold base_cd.
  exact (full_support_base_argv_file_bound base_half base_half base_half base_half
           base_half base_half base_half base_half
           base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
           base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
           base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
           base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
           base_argv base_pth base_bs l Hnd Hfire).
Qed.

(* =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= *)

Module Base_D <: DISTRIBUTION.
  Definition w : FinProcInput -> Q := cd_lift base_cd.
  Definition M : Q := cd_mass base_cd.
  Definition w_nonneg : forall f, (0 <= w f)%Q := cd_lift_nonneg base_cd.
  Lemma M_nonneg : (0 <= M)%Q.
  Proof. unfold M. rewrite base_mass_is_one. exact Qle_0_1. Qed.
  Definition w_core_blind :
    forall f g, fin_core f = fin_core g -> (w f == w g)%Q :=
    cd_lift_core_blind base_cd.
End Base_D.

Lemma base_weight_bound_T_of : forall C b,
  (forall f, Classifier.rejects C f ->
     fin_argv f = base_argv /\ file_at_extends base_pth base_bs (fin_core f)) ->
  (1 # 1125899906842624 <= b)%Q ->
  weight_bound_T C Base_D.w Base_D.M b.
Proof.
  intros C b Hfire Hb l Hnd Hrej.
  unfold Base_D.w. rewrite <- core_sum_cd_lift.
  apply (Qle_trans _ (1 # 1125899906842624)%Q).
  - apply base_fire_bound; [exact Hnd | intros f Hf; apply Hfire, Hrej, Hf].
  - unfold Base_D.M. rewrite base_mass_is_one.
    apply (Qle_trans _ b); [exact Hb | apply Qle_of_Qeq; ring].
Qed.

Lemma base_weight_bound_T_ceiling : forall C,
  (forall f, Classifier.rejects C f ->
     fin_argv f = base_argv /\ file_at_extends base_pth base_bs (fin_core f)) ->
  weight_bound_T C Base_D.w Base_D.M (1 # 1125899906842624).
Proof.
  intros C Hfire. apply base_weight_bound_T_of; [exact Hfire | apply Qle_refl].
Qed.

(* =========================================================================
   Non-vacuity: inside the fire set, and strictly under the ceiling
   ========================================================================= *)

(** Two cores of the fire set: the one with nothing but the argv and the
    one-byte file, and one that fills every free coordinate — an
    environment entry, a second file listed BEFORE the named one, a
    longer file at the path, a standard input.  The pair is what makes
    the free coordinates visible as degrees of freedom the bound
    charges for. *)
Definition base_core_stop : FinCore :=
  mkFinCore base_argv [] (Fs.fs_create_file Fs.fs_empty base_pth [base_nul]) [].
Definition base_core_ext : FinCore :=
  mkFinCore base_argv [[base_a]]
    (Fs.mkFs [([base_a], Fs.EFile 1); (base_pth, Fs.EFile 2)]
       [(1%Z, Fs.mkInode [base_a] 0); (2%Z, Fs.mkInode [base_nul; base_a] 0)] [])
    [base_a].

Definition base_fire_list : list FinProcInput :=
  List.map core_input [base_core_stop; base_core_ext].

Lemma base_fire_slack :
  (fin_argv (core_input base_core_stop) = base_argv
   /\ file_at_extends base_pth base_bs base_core_stop)
  /\ (fin_argv (core_input base_core_ext) = base_argv
      /\ file_at_extends base_pth base_bs base_core_ext)
  /\ List.NoDup (List.map fin_core base_fire_list)
  /\ (0 < core_sum (cd_weight base_cd) base_fire_list)%Q
  /\ ~ (1 # 1125899906842624 <= core_sum (cd_weight base_cd) base_fire_list)%Q.
Proof.
  split; [| split; [| split; [| split]]].
  - split; [reflexivity | exists []; reflexivity].
  - split; [reflexivity | exists [base_a]; reflexivity].
  - unfold base_fire_list. rewrite map_fin_core_core_input.
    apply List.NoDup_cons.
    + intros [Heq | []].
      unfold base_core_stop, base_core_ext in Heq. inversion Heq.
    + apply List.NoDup_cons; [intros [] | apply List.NoDup_nil].
  - vm_compute. reflexivity.
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate.
Qed.

(* =========================================================================
   The certificate pair, at concrete numbers
   ========================================================================= *)

Lemma base_whole_space_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight base_cd) l <= 1)%Q.
Proof.
  intros l Hnd. unfold base_cd. apply full_support_base_mass_upper. exact Hnd.
Qed.

Lemma base_mass_not_attained : forall l : list FinProcInput,
  List.NoDup (List.map fin_core l) ->
  ~ (core_sum (cd_weight base_cd) l == 1)%Q.
Proof.
  unfold base_cd. apply full_support_base_mass_supremum_not_maximum.
  exact base_half_lt_1.
Qed.

(** THE LOWER HALF, at a concrete margin.  All eight rates have to be
    POSITIVE for it: a zero on any of them collapses the coordinate it
    governs, and the witness family the certificate builds would then
    weigh nothing there. *)
Lemma base_mass_lower_at_a_thousandth :
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (1 - (1 # 1000) <= core_sum (cd_weight base_cd) l)%Q.
Proof.
  unfold base_cd.
  apply (full_support_base_mass_lower_certificate base_half base_half base_half
           base_half base_half base_half base_half base_half
           base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
           base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
           base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
           base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
           (1 # 1000)%Q);
    reflexivity.
Qed.

(* =========================================================================
   Inside the shipping mixture, at a share of 6 in 100
   ========================================================================= *)

(** The structured component: the input file's contents at [base_pth],
    byte-geometric at [1 # 8], over the fixed argv, an empty
    environment, an otherwise empty file system and empty standard
    input — [MeasureLib.file_geometric_argv1], so the argv and the path
    cannot disagree. *)
Definition base_structured_p : Q := (1 # 8)%Q.
Lemma base_structured_p_nonneg : (0 <= base_structured_p)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma base_structured_p_le_1 : (base_structured_p <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Definition base_structured : CoreDistribution :=
  file_geometric_argv1 base_structured_p base_prog [] Fs.fs_empty base_pth []
    base_structured_p_nonneg base_structured_p_le_1.

(** The two shares: the base component gets [6 # 100]. *)
Definition base_share : Q := (6 # 100)%Q.
Definition structured_share : Q := (94 # 100)%Q.
Lemma base_share_nonneg : (0 <= base_share)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma structured_share_nonneg : (0 <= structured_share)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Definition base_mixture : CoreDistribution :=
  cd_mix2 (cd_scale structured_share structured_share_nonneg base_structured)
          (cd_scale base_share base_share_nonneg base_cd).

Lemma base_mixture_mass_is_one : (cd_mass base_mixture == 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(** The structured component's own fire set — the file's contents
    extend the NUL byte over ITS fixed template — is inside the base
    family's: the template's argv is the fixed one and the file it
    varies is the file at [base_pth]. *)
Lemma base_structured_fire_in_base_fire : forall c,
  in_file_cylinder base_argv [] Fs.fs_empty base_pth [] base_bs c ->
  core_argv c = base_argv /\ file_at_extends base_pth base_bs c.
Proof.
  intros c [ext Hc]. rewrite Hc. split; [reflexivity |].
  exists ext. apply fs_file_file_core.
Qed.

(** THE MIXTURE BOUND on the structured component's fire set: the
    structured component is charged its contents cylinder, the base
    component its argv-and-file marginal, each scaled by its share and
    added.  The number is [94 # 100] of [7 # 2048] plus [6 # 100] of
    [2 ^ -50], reduced. *)
Lemma base_mixture_fire_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_file_cylinder base_argv [] Fs.fs_empty base_pth [] base_bs (fin_core f)) ->
  (core_sum (cd_weight base_mixture) l
     <= 36173932553831 # 11258999068426240)%Q.
Proof.
  intros l Hnd Hfire. unfold base_mixture.
  eapply Qle_trans.
  - apply cd_mix2_bound.
    + apply cd_scale_bound.
      unfold base_structured, file_geometric_argv1.
      apply (file_geometric_bound base_structured_p base_argv [] Fs.fs_empty base_pth []
               base_structured_p_nonneg base_structured_p_le_1 base_bs l Hnd Hfire).
    + apply cd_scale_bound. unfold base_cd.
      apply (full_support_base_argv_file_bound base_half base_half base_half
               base_half base_half base_half base_half base_half
               base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
               base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
               base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
               base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
               base_argv base_pth base_bs l Hnd).
      intros f Hf. exact (base_structured_fire_in_base_fire (fin_core f) (Hfire f Hf)).
  - apply Qle_of_Qeq. vm_compute. reflexivity.
Qed.
