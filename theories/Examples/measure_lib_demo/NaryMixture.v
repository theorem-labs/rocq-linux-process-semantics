(** * Examples.measure_lib_demo.NaryMixture — the n-ary mixture, worked

    DEMO FILE (not part of the trusted specification, and not installed:
    see `theories/Examples/dune`).  [MeasureLib]'s worked demonstration
    assembles a distribution out of [MeasureLib.finite_support],
    [MeasureLib.cd_scale] and [MeasureLib.cd_mix2].  It never reaches the
    [n]-ARY mixture, and this file is that instantiation: the three
    combinators [MeasureLib.cd_mix], [MeasureLib.cd_zero] and
    [MeasureLib.cd_sum_over], carried through to a
    [Measure.weight_bound_T] a task could ship.

    ** The shape, and why an [n]-ary mixture is the natural one for it

    A task whose inputs fall into named CLASSES declares one
    component per class and mixes them.  Two classes are [cd_mix2]; three
    or more are a list, and writing a list of three as two nested
    [cd_mix2]s means writing the associativity by hand at every bound.
    The three classes here are read off the first byte of standard
    input — plain text, NUL-led, carriage-return-led — with a quarter of
    the space's mass carried by the class that has no leading control
    byte.

    ** What the [n]-ary bound asks for, and what it gives back

    [MeasureLib.cd_mix_bound] takes a bound FUNCTION [B :
    CoreDistribution -> Q] rather than a list of numbers, so the per-
    component ceilings have to be expressible as a function of the
    component.  That is not a restriction in practice and this file is
    the demonstration of why: the natural statement of a fire set that
    takes a fixed FRACTION of each class is exactly such a function,
    [fun D => (1 # 4) * cd_mass D], and the resulting total is a quarter
    of the mixture's own declared mass by [MeasureLib.cd_mix_mass]
    ([nary_ceiling_is_a_quarter_of_the_mass]).  A task whose per-class
    ceilings are unrelated numbers would instead reach for
    [MeasureLib.cd_mix2] twice; the two are the same object
    ([MeasureLib.cd_mix_nary_agrees]), so nothing is lost either way.

    ** Non-vacuity

    [nary_ceiling_is_attained_and_bites] closes both directions.  The
    fire set's own three records weigh EXACTLY the ceiling, so the bound
    is tight rather than slack — unlike the geometric routes, where the
    mass is a supremum and never attained.  And three records OUTSIDE the
    fire set weigh strictly more than the ceiling, so the fire-set
    hypothesis in [nary_weight_bound_T_of] is load-bearing: drop it and
    the conclusion is false at this multiplier.

    As everywhere in [MeasureLib], the records exhibited here are not
    claimed VALID ([FinInput.valid_fin_input]) and not claimed rejected
    by any classifier.  Exhibiting them is arithmetic. *)

From Stdlib Require Import ZArith NArith List QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  FinInput Measure MeasureLib.
From LinuxProcessSemantics.EquivalenceDefinition Require Classifier.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The fixed launch-time environment, and the bytes the classes turn on
   ========================================================================= *)

(** The three components hold argv, envp and the file system fixed and
    vary only standard input, exactly as [MeasureLib]'s worked
    demonstration does — a program invoked as ["wc"], no environment, an
    empty file system.  Nothing below reads any of the three; writing
    something into argv makes it visible that they are a choice. *)
Definition nary_argv : list (list byte) := [[Z_to_bv 8 119; Z_to_bv 8 99]].
Definition nary_envp : list (list byte) := [].
Definition nary_fs : Fs.Fs := Fs.fs_empty.

Definition nary_core (s : list byte) : FinCore :=
  mkFinCore nary_argv nary_envp nary_fs s.

Definition nary_nul : byte := Z_to_bv 8 0.
Definition nary_cr : byte := Z_to_bv 8 13.
Definition nary_a : byte := Z_to_bv 8 65.
Definition nary_b : byte := Z_to_bv 8 66.
Definition nary_c : byte := Z_to_bv 8 67.

(* =========================================================================
   One [finite_support] per class
   ========================================================================= *)

(** The plain-text class, at half the total: four named inputs, an eighth
    each.  [MeasureLib.entries_nonneg_of_forallb] discharges the
    combinator's one side condition by computation, which is the whole
    of what a task author writes per class. *)
Definition nary_entries_text : list (FinCore * Q) :=
  [(nary_core [], (1 # 8)%Q);
   (nary_core [nary_a], (1 # 8)%Q);
   (nary_core [nary_b], (1 # 8)%Q);
   (nary_core [nary_c], (1 # 8)%Q)].

Lemma nary_entries_text_nonneg :
  forall e, List.In e nary_entries_text -> (0 <= snd e)%Q.
Proof. exact (entries_nonneg_of_forallb nary_entries_text eq_refl). Qed.

(** The NUL-led class, at a quarter: four inputs, a sixteenth each. *)
Definition nary_entries_nul : list (FinCore * Q) :=
  [(nary_core [nary_nul], (1 # 16)%Q);
   (nary_core [nary_nul; nary_a], (1 # 16)%Q);
   (nary_core [nary_nul; nary_b], (1 # 16)%Q);
   (nary_core [nary_nul; nary_c], (1 # 16)%Q)].

Lemma nary_entries_nul_nonneg :
  forall e, List.In e nary_entries_nul -> (0 <= snd e)%Q.
Proof. exact (entries_nonneg_of_forallb nary_entries_nul eq_refl). Qed.

(** The carriage-return-led class, at the remaining quarter. *)
Definition nary_entries_cr : list (FinCore * Q) :=
  [(nary_core [nary_cr], (1 # 16)%Q);
   (nary_core [nary_cr; nary_a], (1 # 16)%Q);
   (nary_core [nary_cr; nary_b], (1 # 16)%Q);
   (nary_core [nary_cr; nary_c], (1 # 16)%Q)].

Lemma nary_entries_cr_nonneg :
  forall e, List.In e nary_entries_cr -> (0 <= snd e)%Q.
Proof. exact (entries_nonneg_of_forallb nary_entries_cr eq_refl). Qed.

Definition nary_text : CoreDistribution :=
  finite_support nary_entries_text nary_entries_text_nonneg.
Definition nary_nul_led : CoreDistribution :=
  finite_support nary_entries_nul nary_entries_nul_nonneg.
Definition nary_cr_led : CoreDistribution :=
  finite_support nary_entries_cr nary_entries_cr_nonneg.

(** THE DISTRIBUTION: the three classes as a list, mixed.  The list is
    named rather than written inline at every use, because
    [MeasureLib.cd_mix_bound]'s hypothesis quantifies over
    [List.In D nary_components] and a reader has to be able to see that
    the three cases below are all of them. *)
Definition nary_components : list CoreDistribution :=
  [nary_text; nary_nul_led; nary_cr_led].

Definition nary_mix : CoreDistribution := cd_mix nary_components.

(** The declared mass is [1], and it is the components' own totals added
    up rather than a number written here: [MeasureLib.cd_mix_mass]
    identifies the mixture's declared mass with
    [MeasureLib.cd_sum_over cd_mass] over the same list, and the four
    numerals then close it. *)
Lemma nary_mass_is_one : (cd_mass nary_mix == 1)%Q.
Proof.
  unfold nary_mix. rewrite cd_mix_mass. vm_compute. reflexivity.
Qed.

(** The unit and the one-element case, pinned.  Without the first, the
    fold could be anything on the empty list and
    [MeasureLib.cd_mix_mass] would still hold; without the second, the
    [Fixpoint] could disagree with its own summand.  This is
    [MeasureLib.cd_mix_nary_agrees] at this file's own components,
    reaching [MeasureLib.cd_zero] — the only place the empty mixture is
    instantiated. *)
Lemma nary_empty_mixture_is_cd_zero :
  cd_mass (cd_mix []) = cd_mass cd_zero
  /\ (cd_weight (cd_mix []) (nary_core [nary_c])
        == cd_weight cd_zero (nary_core [nary_c]))%Q
  /\ (cd_mass (cd_mix [nary_text]) == cd_mass nary_text)%Q.
Proof.
  split; [reflexivity | split; [reflexivity |]].
  vm_compute. reflexivity.
Qed.

(* =========================================================================
   The fire set: a quarter of every class
   ========================================================================= *)

(** THE FIRE SET, as a predicate on cores: the one input per class whose
    last byte is [nary_c].  It is written as three [decide]s for the
    reason [MeasureLib.worked_is_fire] is — [entries_restrict] has to
    COMPUTE, and a support this small is named rather than described.  A
    larger one would use a predicate that describes the set;
    [MeasureLib.finite_support_bound_subset] takes any [bool]-valued
    predicate whatever. *)
Definition nary_is_fire (c : FinCore) : bool :=
  if decide (c = nary_core [nary_c]) then true
  else if decide (c = nary_core [nary_nul; nary_c]) then true
  else if decide (c = nary_core [nary_cr; nary_c]) then true
  else false.

(** THE PER-COMPONENT CEILING, as a function of the component, which is
    the form [MeasureLib.cd_mix_bound] takes.  A quarter of each class's
    declared mass: an eighth of the text class's half, a sixteenth of
    each control-led class's quarter. *)
Definition nary_share (D : CoreDistribution) : Q := ((1 # 4) * cd_mass D)%Q.

(** ... and it really is a quarter of the whole, not merely three
    numbers that happen to add up.  [MeasureLib.cd_mix_mass] is what
    makes this an identity about the mixture rather than an arithmetic
    coincidence about this list. *)
Lemma nary_ceiling_is_a_quarter_of_the_mass :
  (cd_sum_over nary_share nary_components == (1 # 4) * cd_mass nary_mix)%Q.
Proof.
  unfold nary_mix. rewrite cd_mix_mass.
  unfold nary_share, nary_components. cbn [cd_sum_over fold_right]. ring.
Qed.

(** Each component charges the fire set a quarter of its own mass.  The
    three cases are the three components, and each is one
    [MeasureLib.finite_support_bound_subset] — the refinement that
    charges a fire set against the entries it actually names rather than
    against the class's whole declared mass — plus one closed [Qeq]
    between literals. *)
Lemma nary_component_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l -> nary_is_fire (fin_core f) = true) ->
  forall D, List.In D nary_components ->
  (core_sum (cd_weight D) l <= nary_share D)%Q.
Proof.
  intros l Hnd Hfire D HD.
  unfold nary_components in HD.
  destruct HD as [HD | [HD | [HD | []]]]; subst D;
    (eapply Qle_trans;
     [ unfold nary_text, nary_nul_led, nary_cr_led;
       apply (finite_support_bound_subset nary_is_fire _ _ l Hnd Hfire)
     | apply Qle_of_Qeq; vm_compute; reflexivity ]).
Qed.

(** THE BOUND: every admissible list drawn from the fire set weighs at
    most a quarter of the mixture's mass.  One
    [MeasureLib.cd_mix_bound] over the whole list of components, and the
    arithmetic that turns the [MeasureLib.cd_sum_over] it produces into
    the literal a task would print. *)
Lemma nary_fire_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l -> nary_is_fire (fin_core f) = true) ->
  (core_sum (cd_weight nary_mix) l <= 1 # 4)%Q.
Proof.
  intros l Hnd Hfire.
  eapply Qle_trans.
  - unfold nary_mix.
    apply (cd_mix_bound nary_share nary_components l).
    intros D HD. apply nary_component_bound; assumption.
  - apply Qle_of_Qeq. vm_compute. reflexivity.
Qed.

(** The whole-space certificate for the same mixture, which is the other
    bound [MeasureLib.cd_mix_bound_mass] exists for: no admissible list
    at all weighs more than the declared mass, fire set or not.  A task
    that cannot describe its fire set still gets this one. *)
Lemma nary_whole_space_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight nary_mix) l <= cd_mass nary_mix)%Q.
Proof.
  intros l Hnd. unfold nary_mix. apply cd_mix_bound_mass.
  intros D HD. unfold nary_components in HD.
  destruct HD as [HD | [HD | [HD | []]]]; subst D;
    unfold nary_text, nary_nul_led, nary_cr_led;
    apply finite_support_bound; exact Hnd.
Qed.

(* =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= *)

(** Both weight obligations come from the library, as they do for every
    distribution built here: the lift of a [MeasureLib.CoreDistribution]
    is nonnegative by the record's own field and core-blind by
    congruence.  [M_nonneg] is the mixture's declared mass, which
    [nary_mass_is_one] has already identified with [1]. *)
Module Nary_D <: DISTRIBUTION.
  Definition w : FinProcInput -> Q := cd_lift nary_mix.
  Definition M : Q := cd_mass nary_mix.
  Definition w_nonneg : forall f, (0 <= w f)%Q := cd_lift_nonneg nary_mix.
  Lemma M_nonneg : (0 <= M)%Q.
  Proof. unfold M. rewrite nary_mass_is_one. exact Qle_0_1. Qed.
  Definition w_core_blind :
    forall f g, fin_core f = fin_core g -> (w f == w g)%Q :=
    cd_lift_core_blind nary_mix.
End Nary_D.

(** From the library's bound to the obligation itself, at any multiplier
    the ceiling fits under.  The three crossings are the ones
    [MeasureLib.worked_weight_bound_T_of] makes and no others:
    [MeasureLib.core_sum_cd_lift] carries [Measure.sum_weights] of the
    lifted weight to [MeasureLib.core_sum], the classifier hypothesis is
    spent turning "rejected" into "has a fire core", and
    [nary_mass_is_one] turns [b * M] into [b]. *)
Lemma nary_weight_bound_T_of : forall C b,
  (forall f, Classifier.rejects C f -> nary_is_fire (fin_core f) = true) ->
  (1 # 4 <= b)%Q ->
  weight_bound_T C Nary_D.w Nary_D.M b.
Proof.
  intros C b Hfire Hb l Hnd Hrej.
  unfold Nary_D.w. rewrite <- core_sum_cd_lift.
  apply (Qle_trans _ (1 # 4)%Q).
  - apply nary_fire_bound;
      [exact Hnd | intros f Hf; apply Hfire, Hrej, Hf].
  - unfold Nary_D.M. rewrite nary_mass_is_one.
    apply (Qle_trans _ b); [exact Hb | apply Qle_of_Qeq; ring].
Qed.

(** The demonstration at the tightest multiplier this route reaches.
    The arithmetic step is [Qle_refl], and — unlike the geometric
    routes — there is nothing left to give away in the distribution
    either, which is what the next lemma's first two conjuncts say. *)
Lemma nary_weight_bound_T_quarter : forall C,
  (forall f, Classifier.rejects C f -> nary_is_fire (fin_core f) = true) ->
  weight_bound_T C Nary_D.w Nary_D.M (1 # 4).
Proof.
  intros C Hfire. apply nary_weight_bound_T_of; [exact Hfire | apply Qle_refl].
Qed.

(* =========================================================================
   Non-vacuity: the ceiling is attained, and the fire hypothesis bites
   ========================================================================= *)

(** The fire set as an admissible list: one canonical record per fire
    core, through [MeasureLib.core_input]. *)
Definition nary_fire_list : list FinProcInput :=
  List.map core_input
    [nary_core [nary_c]; nary_core [nary_nul; nary_c];
     nary_core [nary_cr; nary_c]].

(** Three records the fire set does NOT name, one of them from the class
    that carries the most mass. *)
Definition nary_off_fire_list : list FinProcInput :=
  List.map core_input
    [nary_core [nary_a]; nary_core [nary_b]; nary_core [nary_nul; nary_a]].

(** BOTH DIRECTIONS.  The first two conjuncts say the ceiling is REAL:
    the fire set's own records form an admissible list and weigh exactly
    [1 # 4], so [nary_weight_bound_T_quarter] is the best this
    distribution admits and not a number with slack hidden in it.  The
    last three say the fire-set hypothesis is LOAD-BEARING: three
    records outside the fire set — computed to be outside, through
    [nary_is_fire] itself rather than argued in prose — are admissible
    and weigh [5 # 16], which is more.  Drop the hypothesis and the
    conclusion is false at this multiplier. *)
Lemma nary_ceiling_is_attained_and_bites :
  List.NoDup (List.map fin_core nary_fire_list)
  /\ (core_sum (cd_weight nary_mix) nary_fire_list == 1 # 4)%Q
  /\ List.NoDup (List.map fin_core nary_off_fire_list)
  /\ List.forallb (fun f => negb (nary_is_fire (fin_core f)))
       nary_off_fire_list = true
  /\ ~ (core_sum (cd_weight nary_mix) nary_off_fire_list <= 1 # 4)%Q.
Proof.
  split; [| split; [| split; [| split]]].
  - unfold nary_fire_list. rewrite map_fin_core_core_input.
    apply List.NoDup_cons.
    + intros [Heq | [Heq | []]]; unfold nary_core in Heq; inversion Heq.
    + apply List.NoDup_cons.
      * intros [Heq | []]; unfold nary_core in Heq; inversion Heq.
      * apply List.NoDup_cons; [intros [] | apply List.NoDup_nil].
  - vm_compute. reflexivity.
  - unfold nary_off_fire_list. rewrite map_fin_core_core_input.
    apply List.NoDup_cons.
    + intros [Heq | [Heq | []]]; unfold nary_core in Heq; inversion Heq.
    + apply List.NoDup_cons.
      * intros [Heq | []]; unfold nary_core in Heq; inversion Heq.
      * apply List.NoDup_cons; [intros [] | apply List.NoDup_nil].
  - vm_compute. reflexivity.
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate.
Qed.

(** The [finite_support] certificate pair's LOWER half, at a concrete
    class: some admissible list weighs the class's declared mass exactly.
    [MeasureLib.finite_support_mass_exact] proves it for every entry
    list; instantiating it here is what makes the whole-space bound
    above a two-sided statement about this distribution rather than a
    one-sided one. *)
Lemma nary_text_mass_exact :
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (core_sum (cd_weight nary_text) l == cd_mass nary_text)%Q.
Proof. unfold nary_text. apply finite_support_mass_exact. Qed.
