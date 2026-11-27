(** * Examples.measure_lib_demo.StdinGeometric — the standard-input
      family's certificates, worked

    DEMO FILE (not part of the trusted specification, and not installed).
    [MeasureLib]'s own worked demonstration instantiates
    [MeasureLib.stdin_geometric] as the background of a mixture and uses
    its CYLINDER bound.  The family exports three more facts a task
    prints beside a declared mass, and this file instantiates each at
    one concrete stop weight:

    - the LENGTH SLICE, [MeasureLib.stdin_geometric_slice_bound]: every
      admissible list whose members' standard inputs all have the same
      length weighs at most [p (1 - p)^n].  It charges the 256
      alternatives per byte NOTHING, which is what makes it the bound a
      task uses when its fire set is described by length rather than by
      a prefix;
    - the LOWER CERTIFICATE,
      [MeasureLib.stdin_geometric_mass_lower_certificate]: for every
      margin, some admissible list gets within it of the declared mass;
    - and the fact that the mass is a SUPREMUM,
      [MeasureLib.stdin_geometric_mass_supremum_not_maximum]: no
      admissible list attains it.

    The three together are the honest reading of a declared [1]:
    approached to any margin, never reached, and bounded above on every
    list.  A task that prints only the upper half has said nothing about
    whether its declared mass is an overstatement.

    ** The finite witness the lower certificate runs on

    [MeasureLib.geo_lower_witness argv envp fs k] is the family of cores
    whose standard input is SHORTER than [k] bytes, one record each; it
    is finite, duplicate-free, and weighs [1 - (1 - p)^k] exactly
    ([stdin_demo_witness_weighs_the_tail] below).  That closed form is
    where the certificate's margin arithmetic happens, and instantiating
    it at a concrete depth is the cheapest way to see that the
    certificate is a construction rather than an existence claim.

    Nothing exhibited here is claimed VALID and nothing is claimed
    rejected by any classifier. *)

From Stdlib Require Import ZArith NArith List QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  FinInput Measure MeasureLib.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The fixed launch-time environment, and the stop weight
   ========================================================================= *)

Definition stdin_demo_argv : list (list byte) :=
  [[Z_to_bv 8 119; Z_to_bv 8 99]].
Definition stdin_demo_envp : list (list byte) := [].
Definition stdin_demo_fs : Fs.Fs := Fs.fs_empty.

Definition stdin_demo_p : Q := (1 # 8)%Q.

Lemma stdin_demo_p_nonneg : (0 <= stdin_demo_p)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.
Lemma stdin_demo_p_le_1 : (stdin_demo_p <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Definition stdin_demo_cd : CoreDistribution :=
  stdin_geometric stdin_demo_p stdin_demo_argv stdin_demo_envp stdin_demo_fs
    stdin_demo_p_nonneg stdin_demo_p_le_1.

Lemma stdin_demo_mass_is_one : cd_mass stdin_demo_cd = 1%Q.
Proof. reflexivity. Qed.

(* =========================================================================
   The cylinder mass, in both forms
   ========================================================================= *)

Definition stdin_demo_nul : byte := Z_to_bv 8 0.

(** The mass of the cylinder over a two-byte prefix, and the same number
    through the closed form a task prints — a power of [1 - p] for the
    bytes not yet stopped at, and a power of [1 # 256] for the byte
    values themselves.  Stating both is what keeps the definitional form
    and the printed form from drifting apart. *)
Lemma stdin_demo_cylinder_mass_two_bytes :
  (stdin_geometric_cylinder_mass stdin_demo_p
     [stdin_demo_nul; stdin_demo_nul] == 49 # 4194304)%Q
  /\ (Qpow (1 - stdin_demo_p) 2 * Qpow (1 # 256) 2 == 49 # 4194304)%Q.
Proof.
  split; [vm_compute; reflexivity |].
  rewrite <- (stdin_geometric_cylinder_mass_closed_form stdin_demo_p
                [stdin_demo_nul; stdin_demo_nul]).
  vm_compute. reflexivity.
Qed.

(* =========================================================================
   The length slice
   ========================================================================= *)

(** Every admissible list of records whose standard inputs are all
    exactly three bytes long weighs at most [p (1 - p)^3].  Note what the
    hypothesis does NOT say: nothing about WHICH three bytes.  All
    16777216 of them are covered, and the bound is the same one a single
    three-byte prefix would get from the cylinder times 256^3 — which is
    why a length-described fire set is charged so much more than a
    prefix-described one. *)
Lemma stdin_demo_slice_bound_at_three : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_core f = mkFinCore stdin_demo_argv stdin_demo_envp stdin_demo_fs
                    (fin_stdin f)
     /\ length (fin_stdin f) = 3%nat) ->
  (core_sum (cd_weight stdin_demo_cd) l <= 343 # 4096)%Q.
Proof.
  intros l Hnd Hslice.
  eapply Qle_trans.
  - unfold stdin_demo_cd.
    apply (stdin_geometric_slice_bound stdin_demo_p stdin_demo_argv
             stdin_demo_envp stdin_demo_fs stdin_demo_p_nonneg
             stdin_demo_p_le_1 3%nat l Hnd Hslice).
  - apply Qle_of_Qeq. vm_compute. reflexivity.
Qed.

(* =========================================================================
   The lower half, and the supremum
   ========================================================================= *)

(** The witness family at depth four, and what it weighs: every core
    whose standard input is shorter than four bytes, weighing
    [1 - (1 - p)^4] exactly.  Written out here because the certificate
    below is an existential and an existential hides the construction —
    this is the construction, at one depth, with the number it reaches. *)
Lemma stdin_demo_witness_weighs_the_tail :
  (forall f, List.In f (geo_lower_witness stdin_demo_argv stdin_demo_envp
                          stdin_demo_fs 4) ->
     (length (fin_stdin f) <= 3)%nat)
  /\ (core_sum (cd_weight stdin_demo_cd)
        (geo_lower_witness stdin_demo_argv stdin_demo_envp stdin_demo_fs 4)
        == 1 - Qpow (1 - stdin_demo_p) 4)%Q.
Proof.
  exact (stdin_geometric_bound_by_max_length_attained stdin_demo_p
           stdin_demo_argv stdin_demo_envp stdin_demo_fs stdin_demo_p_nonneg
           stdin_demo_p_le_1 3).
Qed.

(** The certificate itself, at a concrete margin: some admissible list
    weighs within a thousandth of the declared mass. *)
Lemma stdin_demo_mass_lower_at_a_thousandth :
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (1 - (1 # 1000) <= core_sum (cd_weight stdin_demo_cd) l)%Q.
Proof.
  unfold stdin_demo_cd.
  apply (stdin_geometric_mass_lower_certificate stdin_demo_p stdin_demo_argv
           stdin_demo_envp stdin_demo_fs stdin_demo_p_nonneg stdin_demo_p_le_1
           (1 # 1000)%Q);
    reflexivity.
Qed.

(** ... and no admissible list at all attains the mass, so the [1] is a
    supremum.  Together with the previous lemma: approachable to any
    margin, reachable at none. *)
Lemma stdin_demo_mass_not_attained : forall l : list FinProcInput,
  List.NoDup (List.map fin_core l) ->
  ~ (core_sum (cd_weight stdin_demo_cd) l == 1)%Q.
Proof.
  unfold stdin_demo_cd.
  apply (stdin_geometric_mass_supremum_not_maximum stdin_demo_p
           stdin_demo_argv stdin_demo_envp stdin_demo_fs stdin_demo_p_nonneg
           stdin_demo_p_le_1).
  reflexivity.
Qed.

(** The whole-space upper certificate at the same distribution, which is
    what makes the three above two-sided: no admissible list weighs more
    than the declared mass either. *)
Lemma stdin_demo_whole_space_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight stdin_demo_cd) l <= 1)%Q.
Proof.
  intros l Hnd. unfold stdin_demo_cd.
  apply (stdin_geometric_mass_upper stdin_demo_p stdin_demo_argv
           stdin_demo_envp stdin_demo_fs stdin_demo_p_nonneg stdin_demo_p_le_1
           l Hnd).
Qed.
