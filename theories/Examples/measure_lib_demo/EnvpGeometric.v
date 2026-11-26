(** * Examples.measure_lib_demo.EnvpGeometric — the environment-varying
      geometric family, worked

    DEMO FILE (not part of the trusted specification, and not installed).
    [MeasureLib]'s worked demonstration instantiates
    [MeasureLib.stdin_geometric], which holds argv, envp and the file
    system FIXED and varies standard input alone.  This file instantiates
    its two-coordinate companion [MeasureLib.stdin_envp_geometric], which
    varies the launch-time ENVIRONMENT as well, and carries it through to
    a [Measure.weight_bound_T].

    ** The three parameters, and why a task has three rather than one

    [p_stop] is the per-byte stop weight on standard input, as before.
    The environment coordinate needs two more, because an environment is
    a list of byte STRINGS and both the number of entries and the length
    of each has to be paid for: [r] is the weight of stopping after an
    entry (so [1 # 4] means a mean of four entries) and [q_e] is the
    per-byte stop weight WITHIN an entry.  [MeasureLib.envp_factor] is
    the running product of the two and [MeasureLib.envp_point] is [r]
    times it, which is what makes the two coordinates multiply in
    [MeasureLib.stdin_envp_geometric_cylinder_mass].

    The numbers here are [p_stop = 1 # 8], [r = 1 # 4], [q_e = 1 # 16],
    and the environment prefix the fire set is charged against is ONE
    entry of ONE byte.  A realistic `NAME=value` entry is a dozen bytes
    and the ceiling is then a rational with a forty-digit denominator; a
    one-byte entry keeps the ceiling at [315 # 536870912], which a
    reader can multiply out by hand from the four factors
    [envp_fire_ceiling] names.  Nothing in the argument depends on the
    length.

    ** What the cylinder is here

    Two existentials rather than one: a core is in the cylinder over
    [(es, bs)] when its environment EXTENDS [es] and its standard input
    EXTENDS [bs], with argv and the file system fixed.  So the fire set
    below contains cores at every environment depth and every input
    length past the two prefixes, not merely the two records
    [envp_fire_list] exhibits — which is what makes the slack in
    [envp_fire_slack] large rather than a rounding.

    ** Non-vacuity

    [envp_fire_slack] pins that the two records really are inside the
    cylinder and weigh strictly less than the ceiling, so the bound is
    not attained; [envp_off_argv_weighs_nothing] pins the other side,
    that the family is not a constant — a core whose argv is not the
    fixed one weighs exactly zero.  Neither record is claimed VALID and
    neither is claimed rejected by any classifier. *)

From Stdlib Require Import ZArith NArith List QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  FinInput Measure MeasureLib.
From LinuxProcessSemantics.EquivalenceDefinition Require Classifier.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The parameters, and the two side conditions each costs
   ========================================================================= *)

Definition envp_argv : list (list byte) := [[Z_to_bv 8 119; Z_to_bv 8 99]].
Definition envp_fs : Fs.Fs := Fs.fs_empty.

Definition envp_p : Q := (1 # 8)%Q.
Definition envp_r : Q := (1 # 4)%Q.
Definition envp_q : Q := (1 # 16)%Q.

(** Six [Qle] facts, two per parameter.  They are named rather than
    inlined for the reason [MeasureLib.worked_share_named_nonneg] is:
    the constructor takes them as arguments, and a task author reading
    this wants to see what that costs — six lines, once. *)
Lemma envp_p_nonneg : (0 <= envp_p)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma envp_p_le_1 : (envp_p <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma envp_r_nonneg : (0 <= envp_r)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma envp_r_le_1 : (envp_r <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma envp_q_nonneg : (0 <= envp_q)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma envp_q_le_1 : (envp_q <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

(** THE DISTRIBUTION.  Its declared mass is [1] by the constructor's own
    numeral, so [b * M] is [b] and the ceiling below can be quoted as a
    single number. *)
Definition envp_cd : CoreDistribution :=
  stdin_envp_geometric envp_p envp_r envp_q envp_argv envp_fs
    envp_p_nonneg envp_p_le_1 envp_r_nonneg envp_r_le_1
    envp_q_nonneg envp_q_le_1.

Lemma envp_mass_is_one : cd_mass envp_cd = 1%Q.
Proof. reflexivity. Qed.

(* =========================================================================
   The fire set: one environment prefix, one input prefix
   ========================================================================= *)

Definition envp_v : byte := Z_to_bv 8 86.
Definition envp_w : byte := Z_to_bv 8 87.
Definition envp_nul : byte := Z_to_bv 8 0.
Definition envp_a : byte := Z_to_bv 8 65.

(** The two prefixes the fire set is charged against: an environment
    beginning with the one-byte entry [V], and a standard input
    beginning with a NUL byte. *)
Definition envp_es : list (list byte) := [[envp_v]].
Definition envp_bs : list byte := [envp_nul].

(** THE CEILING, as an exact rational, stated before it is used so that
    the number in the demonstrations is visibly what the cylinder mass
    IS and not a convenient rounding of it.  The four factors are the
    two the environment coordinate contributes — [1 - r = 3 # 4] for
    continuing past no entry at all, and [q_e (1 - q_e) / 256] for the
    one byte of the entry — and the two the input coordinate
    contributes, [(1 - p) / 256] for the NUL byte. *)
Lemma envp_fire_ceiling :
  (stdin_envp_geometric_cylinder_mass envp_p envp_r envp_q envp_es envp_bs
     == 315 # 536870912)%Q.
Proof. vm_compute. reflexivity. Qed.

(** The same number through the family's own closed form, which is the
    shape a task prints: a power of [1 - r] for the entry count, the
    product of the per-entry weights, and the byte-geometric factor on
    standard input.  Stating both is what keeps the definitional form
    and the printed form from drifting. *)
Lemma envp_fire_ceiling_closed_form :
  (Qpow (1 - envp_r) (length envp_es)
     * entries_geo_product envp_q envp_es
     * (Qpow (1 - envp_p) (length envp_bs)
        * Qpow (1 # 256) (length envp_bs))
   == 315 # 536870912)%Q.
Proof.
  rewrite <- stdin_envp_geometric_cylinder_mass_closed_form.
  exact envp_fire_ceiling.
Qed.

(** THE BOUND: every admissible list drawn from the cylinder weighs at
    most the ceiling.  One [MeasureLib.stdin_envp_geometric_bound] and
    the [Qeq] that names the number; the two existentials the cylinder
    asks for are discharged by the caller, at the fire set it actually
    has. *)
Lemma envp_fire_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_envp_stdin_cylinder envp_argv envp_fs envp_es envp_bs (fin_core f)) ->
  (core_sum (cd_weight envp_cd) l <= 315 # 536870912)%Q.
Proof.
  intros l Hnd Hcyl.
  rewrite <- envp_fire_ceiling.
  unfold envp_cd.
  apply (stdin_envp_geometric_bound envp_p envp_r envp_q envp_argv envp_fs
           envp_p_nonneg envp_p_le_1 envp_r_nonneg envp_r_le_1
           envp_q_nonneg envp_q_le_1 envp_es envp_bs l Hnd Hcyl).
Qed.

(** The OTHER bound the family exports, and the one a task with a
    length-indexed fire set uses instead: every admissible list whose
    members all have standard input of the SAME length [n] weighs at
    most [p (1 - p)^n], with the environment charged nothing at all.
    Instantiated here at [n = 2]. *)
Lemma envp_slice_bound_at_two : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_core f = mkFinCore envp_argv (fin_envp f) envp_fs (fin_stdin f)
     /\ length (fin_stdin f) = 2%nat) ->
  (core_sum (cd_weight envp_cd) l <= 49 # 512)%Q.
Proof.
  intros l Hnd Hslice.
  eapply Qle_trans.
  - unfold envp_cd.
    apply (stdin_envp_geometric_slice_bound envp_p envp_r envp_q envp_argv
             envp_fs envp_p_nonneg envp_p_le_1 envp_r_nonneg envp_r_le_1
             envp_q_nonneg envp_q_le_1 2%nat l Hnd Hslice).
  - apply Qle_of_Qeq. vm_compute. reflexivity.
Qed.

(* =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= *)

Module Envp_D <: DISTRIBUTION.
  Definition w : FinProcInput -> Q := cd_lift envp_cd.
  Definition M : Q := cd_mass envp_cd.
  Definition w_nonneg : forall f, (0 <= w f)%Q := cd_lift_nonneg envp_cd.
  Lemma M_nonneg : (0 <= M)%Q.
  Proof. unfold M. rewrite envp_mass_is_one. exact Qle_0_1. Qed.
  Definition w_core_blind :
    forall f g, fin_core f = fin_core g -> (w f == w g)%Q :=
    cd_lift_core_blind envp_cd.
End Envp_D.

(** The recipe, at any multiplier the ceiling fits under.  The
    classifier hypothesis is where the task's own analysis of its
    program enters, and it is the only place: everything else is the
    library's arithmetic. *)
Lemma envp_weight_bound_T_of : forall C b,
  (forall f, Classifier.rejects C f ->
     in_envp_stdin_cylinder envp_argv envp_fs envp_es envp_bs (fin_core f)) ->
  (315 # 536870912 <= b)%Q ->
  weight_bound_T C Envp_D.w Envp_D.M b.
Proof.
  intros C b Hfire Hb l Hnd Hrej.
  unfold Envp_D.w. rewrite <- core_sum_cd_lift.
  apply (Qle_trans _ (315 # 536870912)%Q).
  - apply envp_fire_bound;
      [exact Hnd | intros f Hf; apply Hfire, Hrej, Hf].
  - unfold Envp_D.M. rewrite envp_mass_is_one.
    apply (Qle_trans _ b); [exact Hb | apply Qle_of_Qeq; ring].
Qed.

(** At a round multiplier a task would plausibly declare: a classifier
    whose reject set lies in this cylinder carries at most a
    thousandth of the mass. *)
Lemma envp_weight_bound_T_thousandth : forall C,
  (forall f, Classifier.rejects C f ->
     in_envp_stdin_cylinder envp_argv envp_fs envp_es envp_bs (fin_core f)) ->
  weight_bound_T C Envp_D.w Envp_D.M (1 # 1000).
Proof.
  intros C Hfire. apply envp_weight_bound_T_of; [exact Hfire |].
  apply (proj1 (Qle_bool_iff _ _)). vm_compute. reflexivity.
Qed.

(** At the tightest multiplier this route reaches. *)
Lemma envp_weight_bound_T_ceiling : forall C,
  (forall f, Classifier.rejects C f ->
     in_envp_stdin_cylinder envp_argv envp_fs envp_es envp_bs (fin_core f)) ->
  weight_bound_T C Envp_D.w Envp_D.M (315 # 536870912).
Proof.
  intros C Hfire. apply envp_weight_bound_T_of; [exact Hfire | apply Qle_refl].
Qed.

(* =========================================================================
   Non-vacuity: inside the cylinder, and off the fixed argv
   ========================================================================= *)

(** Two cores of the cylinder: the one that stops at both prefixes, and
    one that extends BOTH coordinates — a second environment entry and a
    second input byte.  The pair is what makes the cylinder's two
    existentials visible as two independent degrees of freedom. *)
Definition envp_core_stop : FinCore :=
  mkFinCore envp_argv [[envp_v]] envp_fs [envp_nul].
Definition envp_core_ext : FinCore :=
  mkFinCore envp_argv [[envp_v]; [envp_w]] envp_fs [envp_nul; envp_a].

Definition envp_fire_list : list FinProcInput :=
  List.map core_input [envp_core_stop; envp_core_ext].

(** HOW MUCH OF THE CEILING IS REAL.  Four conjuncts.  The first two say
    the two cores really are in the cylinder, by naming the extensions —
    the empty pair for one, one entry and one byte for the other.  The
    third says the list is admissible, so [envp_fire_bound] applies to
    it.  The fourth is the strictness: the two records weigh strictly
    less than the ceiling, so this route carries slack.

    All of that slack is the cylinder's other members — every
    environment past [V] and every input past the NUL byte, at every
    depth, is charged for and absent from a two-element list.  What this
    does NOT say is that no smaller multiplier is provable; a task that
    sums its own cores exactly is entitled to a smaller one. *)
Lemma envp_fire_slack :
  in_envp_stdin_cylinder envp_argv envp_fs envp_es envp_bs envp_core_stop
  /\ in_envp_stdin_cylinder envp_argv envp_fs envp_es envp_bs envp_core_ext
  /\ List.NoDup (List.map fin_core envp_fire_list)
  /\ ~ (315 # 536870912 <= core_sum (cd_weight envp_cd) envp_fire_list)%Q.
Proof.
  split; [| split; [| split]].
  - exists [], []. reflexivity.
  - exists [[envp_w]], [envp_a]. reflexivity.
  - unfold envp_fire_list. rewrite map_fin_core_core_input.
    apply List.NoDup_cons.
    + intros [Heq | []].
      unfold envp_core_stop, envp_core_ext in Heq. inversion Heq.
    + apply List.NoDup_cons; [intros [] | apply List.NoDup_nil].
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate.
Qed.

(** THE OTHER DIRECTION: the family is not the zero distribution and not
    a constant either.  The stopping core carries positive weight — the
    product of the two coordinates' stop weights — and a core whose argv
    is not the fixed one weighs exactly zero, which is
    [MeasureLib.envp_geo_weight_off_argv_zero] at a core this file
    names.  Without the first half every bound above would hold of a
    distribution that weighs nothing. *)
Definition envp_core_other_argv : FinCore :=
  mkFinCore [[envp_a]] [[envp_v]] envp_fs [envp_nul].

Lemma envp_off_argv_weighs_nothing :
  (0 < cd_weight envp_cd envp_core_stop)%Q
  /\ cd_weight envp_cd envp_core_other_argv = 0%Q.
Proof.
  split.
  - unfold envp_cd, envp_core_stop.
    cbn [cd_weight stdin_envp_geometric].
    rewrite envp_geo_weight_match. vm_compute. reflexivity.
  - unfold envp_cd. cbn [cd_weight stdin_envp_geometric].
    apply envp_geo_weight_off_argv_zero.
    unfold envp_core_other_argv, envp_argv. cbn [core_argv]. discriminate.
Qed.

(* =========================================================================
   The certificate pair, at concrete numbers
   ========================================================================= *)

(** The whole-space upper certificate: no admissible list weighs more
    than the declared mass, fire set or not. *)
Lemma envp_whole_space_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight envp_cd) l <= 1)%Q.
Proof.
  intros l Hnd. unfold envp_cd.
  apply (stdin_envp_geometric_mass_upper envp_p envp_r envp_q envp_argv
           envp_fs envp_p_nonneg envp_p_le_1 envp_r_nonneg envp_r_le_1
           envp_q_nonneg envp_q_le_1 l Hnd).
Qed.

(** THE LOWER HALF, at a concrete margin.  All three of [p_stop], [r]
    and [q_e] have to be POSITIVE for it: a zero on any of the three
    collapses the coordinate it governs, and the witness family the
    certificate builds would then weigh nothing.  The library pins each
    of those three degeneracies separately. *)
Lemma envp_mass_lower_at_a_thousandth :
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (1 - (1 # 1000) <= core_sum (cd_weight envp_cd) l)%Q.
Proof.
  unfold envp_cd.
  apply (stdin_envp_geometric_mass_lower_certificate envp_p envp_r envp_q
           envp_argv envp_fs envp_p_nonneg envp_p_le_1 envp_r_nonneg
           envp_r_le_1 envp_q_nonneg envp_q_le_1 (1 # 1000)%Q);
    reflexivity.
Qed.

(** ... and no admissible list attains the mass, so the declared [1] is
    a supremum here too. *)
Lemma envp_mass_not_attained : forall l : list FinProcInput,
  List.NoDup (List.map fin_core l) ->
  ~ (core_sum (cd_weight envp_cd) l == 1)%Q.
Proof.
  unfold envp_cd.
  apply (stdin_envp_geometric_mass_supremum_not_maximum envp_p envp_r envp_q
           envp_argv envp_fs envp_p_nonneg envp_p_le_1 envp_r_nonneg
           envp_r_le_1 envp_q_nonneg envp_q_le_1).
  reflexivity.
Qed.
