(** * Examples.patchclassify_demo.Distribution — the demo's declared
      weight and total

    DEMO FILE (not part of the trusted specification).  The sixth thing
    [EquivalenceDefinition.PatchClassifySpec.SPEC_PATCH_CLASSIFY] takes,
    after the six images, is a [Measure.DISTRIBUTION]: a weight on finite
    inputs and a declared total mass.  This file supplies one for the
    demo and proves the single fact the demo's two bounds are read off.

    ** It is METADATA, and the demo does not get to be judged by it

    [PatchClassifySpec]'s header is explicit that [W] is trusted,
    per-problem metadata: a task ships it, a submission never proves it,
    and [Measure]'s header adds that nothing ties the declared [M] to the
    weight — there is no normalization obligation anywhere in the layer.
    So the two obligations inside [Measure.DISTRIBUTION] are about the
    weight function alone, and both are discharged here by the library's
    own lemmas ([MeasureLib.cd_lift_nonneg] and
    [MeasureLib.cd_lift_core_blind]) with no proof written by hand.
    That is [MeasureLib]'s design claim, cashed at the size of
    distribution this demo ships.

    ** The choice, and what it is NOT chosen to make easy

    [MeasureLib.stdin_geometric] at stop weight [1 # 8], over one fixed
    launch-time environment: a program invoked with one empty argument,
    no environment and an empty file system.  A core weighs
    [p (1 - p)^n / 256^n] when its standard input is [n] bytes long and
    its other three fields are those, and nothing at all otherwise.  The
    declared mass is [1].

    Nothing about this choice is tuned to the demo's classifiers.  It
    could not be: both of them fire on EVERY input, so the set the two
    bounds below measure is the whole space, and the bound they get is
    the one any distribution would give — its own declared mass.  A
    weight concentrated on the inputs the classifiers happen to reject
    would be the dishonest move here, and there is no such thing to
    concentrate on.

    The environment is [Checks.Examples]' one — [[[]]] for argv, nothing
    for the environment, an empty file system — because that is the one
    the demo's own validity witnesses use, so a reader can see that the
    inputs the bites below exhibit are inside the support rather than
    beside it.  It carries no weight in the proof: the certificate this
    file uses holds for every admissible list, including lists of cores
    the weight sends to zero.

    ** The one fact proved here

    [demo_whole_space_bound]: for ANY image and any admissible list of
    finite inputs, the weights already summed do not exceed [1 * M].
    That is [MeasureLib.stdin_geometric_mass_upper] — the whole-space
    certificate — plus the arithmetic that turns [M] into [1 * M].

    Note what it does NOT mention: the classifier, and the reject set.
    [Measure.weight_bound_T]'s hypothesis that every entry of the list is
    rejected is DISCARDED here, which is exactly why the bound is [1]:
    the claim being made is that the fire set weighs no more than
    everything does.  At a fire set that really is everything — which is
    what these two classifiers have — that is the honest bound.

    It is NOT claimed here, or anywhere in the demo, that [1] is the
    LEAST multiplier provable for these classifiers.  That inference is
    the one [MeasureLib]'s header names as the misreading a consumer of
    that library is positioned to make: the certificate pair bounds the
    partial sums over ALL admissible lists, while an obligation ranges
    over the lists a classifier REJECTS, and the supremum over those may
    be strictly smaller.  What the demo does prove, in [Obligations]
    ([Obligations.demo_b_zero_refutable],
    [Obligations.demo_b_half_refutable]), is the weaker and checkable
    thing: against THIS weight and THIS total the multiplier cannot be
    dropped to [0] and cannot be halved, so [b = 1] is a real claim
    rather than a number any distribution would satisfy.

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith NArith List QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit FinInput Classifier Measure MeasureLib.
Import ListNotations.

(* =========================================================================
   The fixed launch-time environment
   ========================================================================= *)

(** One empty argument, no environment, an empty file system — the same
    three [Checks.Examples.demo_input_valid] validates, and the same
    three [MeasureLib.stdin_geometric] holds fixed.  A core whose argv,
    envp or file system differs from these weighs zero. *)
Definition demo_argv : list (list byte) := [[]].
Definition demo_envp : list (list byte) := [].
Definition demo_fs : Fs.Fs := Fs.standard_root Fs.default_cwd.

(* =========================================================================
   The background
   ========================================================================= *)

(** The stop weight.  An authored number, like every other one here:
    [1 # 8] makes a typical standard input a few bytes long and is far
    enough from both [0] and [1] that neither degenerate case is being
    exercised by accident — [MeasureLib]'s worked distribution makes the
    same choice for the same reason. *)
Definition demo_p_stop : Q := (1 # 8)%Q.

Lemma demo_p_stop_nonneg : (0 <= demo_p_stop)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Lemma demo_p_stop_le_1 : (demo_p_stop <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

(** The distribution itself: a geometric law on the length of standard
    input, uniform over the bytes at each length, over the fixed
    environment above.  One combinator, no mixture — the demo has no
    foreground worth naming, since its classifiers do not distinguish
    inputs. *)
Definition demo_cd : CoreDistribution :=
  stdin_geometric demo_p_stop demo_argv demo_envp demo_fs
    demo_p_stop_nonneg demo_p_stop_le_1.

(* =========================================================================
   ... as a [Measure.DISTRIBUTION]
   ========================================================================= *)

(** The module [PatchClassifySpec.SPEC_PATCH_CLASSIFY] takes.  Five
    lines, three of them the library's lemmas: this is
    [MeasureLib.Example_D] and [MeasureLib.Worked_D] at a third
    distribution, and no obligation inside it is a claim about the
    demo. *)
Module DemoDist <: DISTRIBUTION.
  Definition w : FinProcInput -> Q := cd_lift demo_cd.
  Definition M : Q := cd_mass demo_cd.
  Definition w_nonneg : forall f, (0 <= w f)%Q := cd_lift_nonneg demo_cd.
  Definition M_nonneg : (0 <= M)%Q :=
    stdin_geometric_mass_nonneg demo_p_stop demo_argv demo_envp demo_fs
      demo_p_stop_nonneg demo_p_stop_le_1.
  Definition w_core_blind :
    forall f g, fin_core f = fin_core g -> (w f == w g)%Q :=
    cd_lift_core_blind demo_cd.
End DemoDist.

(** The declared total, as a numeral — [eq] and not merely [Qeq],
    because [MeasureLib.stdin_geometric]'s constructor writes it.  This
    is what lets the two bounds below quote a multiplier and a mass as
    one number. *)
Lemma demo_M_is_one : DemoDist.M = 1%Q.
Proof. reflexivity. Qed.

(* =========================================================================
   The whole-space certificate
   ========================================================================= *)

(** Every admissible list weighs at most the declared mass, whatever it
    is drawn from.  [MeasureLib.stdin_geometric_mass_upper] is the
    library's certificate — its proof is the exhaustive disjunction "a
    core either matches the fixed environment, and so lies in the
    cylinder over the empty prefix, or weighs nothing" — and the only
    work here is the crossing between [Measure.sum_weights] of the
    lifted weight and [MeasureLib.core_sum] of the core weight, which
    [MeasureLib.core_sum_cd_lift] makes an [eq] by conversion.

    Stated for an ARBITRARY image, because it says nothing about any
    classifier: the rejection hypothesis of [Measure.weight_bound_T] is
    the one thing the proof never reads. *)
Lemma demo_whole_space_bound : forall C : Image,
  weight_bound_T C DemoDist.w DemoDist.M 1.
Proof.
  intros C l Hnd _.
  unfold DemoDist.w. rewrite <- core_sum_cd_lift.
  apply (Qle_trans _ (cd_mass demo_cd)).
  - unfold demo_cd.
    apply stdin_geometric_mass_upper. exact Hnd.
  - unfold DemoDist.M. apply Qle_of_Qeq. ring.
Qed.

(* =========================================================================
   The distribution bites
   ========================================================================= *)

(** The weight is not the zero function, so the bound above is not a
    statement about a measure that charges nothing.  The empty standard
    input over the fixed environment weighs [1 # 8] — the stop weight
    itself, since [MeasureLib.geo_mass] at length zero is [1]. *)
Definition demo_empty_input : FinProcInput :=
  core_input (mkFinCore demo_argv demo_envp demo_fs []).

Example demo_w_positive : (0 < DemoDist.w demo_empty_input)%Q.
Proof. vm_compute. reflexivity. Qed.

(** ... and it is not the constant function either: a longer standard
    input weighs strictly less, which is what makes the law geometric
    rather than a relabelled counting measure. *)
Definition demo_one_byte_input : FinProcInput :=
  core_input (mkFinCore demo_argv demo_envp demo_fs [Z_to_bv 8 0]).

Example demo_w_decreasing :
  (DemoDist.w demo_one_byte_input < DemoDist.w demo_empty_input)%Q.
Proof. vm_compute. reflexivity. Qed.

(** And the environment really is fixed: a core with a different argv is
    outside the support and weighs nothing.  Without this the "fixed
    launch-time environment" in this file's header would be a
    description of an intention rather than of the weight. *)
Example demo_w_off_environment :
  DemoDist.w (core_input (mkFinCore [[Z_to_bv 8 65]] demo_envp demo_fs []))
  = 0%Q.
Proof. vm_compute. reflexivity. Qed.
