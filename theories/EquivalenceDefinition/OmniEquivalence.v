(** * EquivalenceDefinition.OmniEquivalence — the theorem families, restated through [OmniRun]

    ADDITIVE.  Every definition in [Equivalence], [MustExit] and
    [Classifier] keeps its text; this file gives each statement family
    an [omni_*] twin built from the judgments of [OmniRun] and proves
    the two equivalent, unconditionally and without classical axioms:

      [must_exit_with_iff]                  [MustExit.must_exit_with]
      [error_free_iff], [modeled_iff]       [Equivalence.error_free], [Equivalence.modeled]
      [trace_equiv_iff_omni]                [Equivalence.trace_equiv] on two runs
      [equiv_iff], [strong_equiv_iff]       [Equivalence.equiv], [Equivalence.strong_equiv]
      [strong_universal_iff]                [Equivalence.strong_universal_T]
      [strong_equiv_error_free_iff],
      [strong_universal_error_free_iff]     the error-free shapes
      [agree_iff], [good_input_iff]         [Classifier.agree], [Classifier.good_input]
      [decides_iff], [classifier_total_iff] [Classifier.decides], [Classifier.classifier_total_T]

    The checker-visible names ([Equivalence.SPEC],
    [Equivalence.SPEC_ERROR_FREE], [Equivalence.strong_universal_T],
    ...) are untouched; [OMNI_SPEC] and [OMNI_SPEC_ERROR_FREE] are new
    module types with the same parameter shape, and the functors
    [OmniOfSpec] / [SpecOfOmni] show how a proof in either shape is
    ascribed to the other's module type through the [iff].

    ** How the families read in omni form

    - The escape [Run.bh_all_errors] is [omni_run … errors]: every
      maximal execution ends in an error.
    - [Equivalence.error_free] is [omni_corun … never_errors]: no
      maximal execution that ends ends in an error.
    - [Equivalence.modeled] is [omni_corun … covered]: an error may end
      an execution, but not one taken from a configuration
      [Run.unmodeled_at].
    - [Equivalence.trace_equiv] of two runs is [omni_trace_equiv]:
      agreement on every prefix-closed [OmniRun.cosafe] postcondition
      ([omni_trace_equiv_refinement] is the refinement-pair
      introduction rule).
    - [MustExit.must_exit_with code] is [omni_run … (exits_with code)].
    - [Classifier.agree]'s existential error facts are [omni_may]:
      some maximal execution ends the named way.

    [Equivalence.strong_equiv]'s shape — the [modeled] conjunct BESIDE
    [equiv], never as an antecedent — is kept verbatim in
    [omni_strong_equiv]; so is every quantifier shell ([Run.valid_entry]
    per image, [Run.valid_input] on the shared input, the role budgets
    [State.source_alloc_limit] / [State.target_alloc_limit], the
    per-entry existentials of [Classifier.agree]). *)

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   Compat: [MustExit.must_exit_at] / [must_exit_with]
   ========================================================================= *)

(** The right-to-left direction is stated over an arbitrary
    postcondition entailing [exits_with], because [induction] on an
    [exec] whose postcondition is a concrete term abstracts it away. *)
Lemma exec_exits_must_exit_at : forall segs code c (Q : post),
  exec segs c Q ->
  (forall tr o, Q tr o -> exits_with code tr o) ->
  must_exit_at segs code c.
Proof.
  intros segs code c Q H.
  induction H as [c Q Hh HQ | c Q Hh Hprog Herr Hnext IH]; intros Himp.
  - destruct (Himp _ _ HQ) as (Hex & Hk).
    exact (must_exit_at_halted _ _ _ Hex Hk).
  - apply must_exit_at_running; [exact Hh | exact Hprog | |].
    + intros evs Hss. exact (Himp _ _ (Herr evs Hss)).
    + intros evs c' Hss. apply (IH evs c' Hss).
      intros tr o Hq. exact (Himp (evs ++ tr) o Hq).
Qed.

Lemma must_exit_at_iff : forall segs code c,
  must_exit_at segs code c <-> exec segs c (exits_with code).
Proof.
  intros segs code c; split.
  - intros H. induction H as [c Hh Hk | c Hh Hprog Hnoerr Hnext IH].
    + apply exec_halt; [rewrite Hh; discriminate | exact (conj Hh Hk)].
    + apply exec_step; [exact Hh | exact Hprog | |].
      * intros evs Hss. exfalso. exact (Hnoerr evs Hss).
      * intros evs c' Hss. exact (IH evs c' Hss).
  - intros H. exact (exec_exits_must_exit_at _ _ _ _ H (fun _ _ h => h)).
Qed.

Lemma must_exit_with_iff : forall code img lim en inp,
  must_exit_with code img lim en inp <-> omni_run img lim en inp (exits_with code).
Proof.
  intros code [segs pc ph] lim [sp brk0 mbase rnd] inp.
  cbn [must_exit_with omni_run]. apply must_exit_at_iff.
Qed.

(* =========================================================================
   Compat: the behaviour-level predicates of [Equivalence]
   ========================================================================= *)

Lemma error_free_iff : forall img lim en inp,
  error_free (run img lim en inp) <-> omni_corun img lim en inp never_errors.
Proof. intros. apply bh_errors_iff. Qed.

Lemma modeled_iff : forall img lim en inp,
  modeled (run img lim en inp)
  <-> omni_corun img lim en inp (covered (img_segments img)).
Proof. intros. apply bh_unmodeled_iff. Qed.

(** Trace equivalence of two runs is agreement on every prefix-closed
    omni postcondition. *)
Definition omni_trace_equiv (img1 : Image) (lim1 : Z) (en1 : ExecEntry)
    (img2 : Image) (lim2 : Z) (en2 : ExecEntry) (inp : ProcInput) : Prop :=
  forall P, prefix_closed P ->
    (omni_cosafe img1 lim1 en1 inp P <-> omni_cosafe img2 lim2 en2 inp P).

Lemma trace_equiv_iff_omni : forall img1 lim1 en1 img2 lim2 en2 inp,
  trace_equiv (bh_traces (run img1 lim1 en1 inp)) (bh_traces (run img2 lim2 en2 inp))
  <-> omni_trace_equiv img1 lim1 en1 img2 lim2 en2 inp.
Proof. intros. unfold trace_equiv, omni_trace_equiv. apply bh_traces_iff. Qed.

(** The introduction rule: each run's trace set is a prefix
    postcondition the other run satisfies (a refinement in each
    direction). *)
Lemma omni_trace_equiv_refinement : forall img1 lim1 en1 img2 lim2 en2 inp,
  omni_trace_equiv img1 lim1 en1 img2 lim2 en2 inp
  <-> (omni_cosafe img1 lim1 en1 inp (bh_traces (run img2 lim2 en2 inp))
       /\ omni_cosafe img2 lim2 en2 inp (bh_traces (run img1 lim1 en1 inp))).
Proof.
  intros [segs1 pc1 ph1] lim1 [sp1 brk1 mb1 rnd1] [segs2 pc2 ph2] lim2 [sp2 brk2 mb2 rnd2] inp.
  unfold omni_trace_equiv. cbn [run bh_traces omni_cosafe].
  split.
  - intros H. apply obs_equiv_iff_refinement. apply obs_equiv_iff_cosafe. exact H.
  - intros H. apply obs_equiv_iff_cosafe. apply obs_equiv_iff_refinement. exact H.
Qed.

(** [Equivalence.equiv] on two runs: the escape, or trace agreement
    with an error-free target. *)
Definition omni_equiv (imgS : Image) (limS : Z) (enS : ExecEntry)
    (imgT : Image) (limT : Z) (enT : ExecEntry) (inp : ProcInput) : Prop :=
  omni_run imgS limS enS inp errors
  \/ (omni_trace_equiv imgS limS enS imgT limT enT inp
      /\ omni_corun imgT limT enT inp never_errors).

Lemma equiv_iff : forall imgS limS enS imgT limT enT inp,
  equiv (run imgS limS enS inp) (run imgT limT enT inp)
  <-> omni_equiv imgS limS enS imgT limT enT inp.
Proof.
  intros imgS limS enS imgT limT enT inp. unfold equiv, omni_equiv.
  rewrite (bh_all_errors_iff imgS limS enS inp).
  rewrite (trace_equiv_iff_omni imgS limS enS imgT limT enT inp).
  rewrite (bh_errors_iff imgT limT enT inp).
  reflexivity.
Qed.

(** The two policy consequences, in omni form. *)
Lemma omni_all_errors_equiv_any : forall imgS limS enS imgT limT enT inp,
  omni_run imgS limS enS inp errors -> omni_equiv imgS limS enS imgT limT enT inp.
Proof. intros; left; assumption. Qed.

Lemma omni_equiv_target_never_errors : forall imgS limS enS imgT limT enT inp,
  omni_equiv imgS limS enS imgT limT enT inp ->
  ~ omni_run imgS limS enS inp errors ->
  omni_corun imgT limT enT inp never_errors.
Proof.
  intros imgS limS enS imgT limT enT inp [Hall | (_ & Hnoerr)] Hsurvives;
    [contradiction | exact Hnoerr].
Qed.

(* =========================================================================
   The theorem statements, parameterised over the two images
   ========================================================================= *)

Section Spec.

Variable source_image : Image.
Variable target_image : Image.

(** [Equivalence.strong_equiv], with [modeled] as [covered] BESIDE the
    equivalence — the same conjunct shape; see the comment on
    [Equivalence.modeled] for why it is not an antecedent. *)
Definition omni_strong_equiv (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  omni_corun source_image source_alloc_limit en_source inp
    (covered (img_segments source_image))
  /\ omni_equiv source_image source_alloc_limit en_source
                target_image target_alloc_limit en_target inp.

Lemma strong_equiv_iff : forall en_source en_target inp,
  strong_equiv source_image target_image en_source en_target inp
  <-> omni_strong_equiv en_source en_target inp.
Proof.
  intros en_source en_target inp. unfold strong_equiv, omni_strong_equiv.
  rewrite (modeled_iff source_image source_alloc_limit en_source inp).
  rewrite (equiv_iff source_image source_alloc_limit en_source
             target_image target_alloc_limit en_target inp).
  reflexivity.
Qed.

Definition omni_strong_universal_T : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    omni_strong_equiv en_source en_target inp.

Lemma strong_universal_iff :
  strong_universal_T source_image target_image <-> omni_strong_universal_T.
Proof.
  unfold strong_universal_T, omni_strong_universal_T.
  split; intros H en_source en_target inp Hs Ht Hi;
    apply strong_equiv_iff; apply H; assumption.
Qed.

(** [Equivalence.strong_equiv_error_free]: both runs never error, and
    the trace sets agree. *)
Definition omni_strong_equiv_error_free (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  omni_corun source_image source_alloc_limit en_source inp never_errors
  /\ omni_corun target_image target_alloc_limit en_target inp never_errors
  /\ omni_trace_equiv source_image source_alloc_limit en_source
                      target_image target_alloc_limit en_target inp.

Lemma strong_equiv_error_free_iff : forall en_source en_target inp,
  strong_equiv_error_free source_image target_image en_source en_target inp
  <-> omni_strong_equiv_error_free en_source en_target inp.
Proof.
  intros en_source en_target inp.
  unfold strong_equiv_error_free, omni_strong_equiv_error_free.
  rewrite (error_free_iff source_image source_alloc_limit en_source inp).
  rewrite (error_free_iff target_image target_alloc_limit en_target inp).
  rewrite (trace_equiv_iff_omni source_image source_alloc_limit en_source
             target_image target_alloc_limit en_target inp).
  reflexivity.
Qed.

Definition omni_strong_universal_error_free_T : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    omni_strong_equiv_error_free en_source en_target inp.

Lemma strong_universal_error_free_iff :
  strong_universal_error_free_T source_image target_image
  <-> omni_strong_universal_error_free_T.
Proof.
  unfold strong_universal_error_free_T, omni_strong_universal_error_free_T.
  split; intros H en_source en_target inp Hs Ht Hi;
    apply strong_equiv_error_free_iff; apply H; assumption.
Qed.

(** The error-free shape is the stronger one, proved in omni terms:
    [never_errors] entails [covered], and the right disjunct of
    [omni_equiv] is exactly its last two conjuncts. *)
Lemma omni_strong_equiv_error_free_implies : forall en_source en_target inp,
  omni_strong_equiv_error_free en_source en_target inp ->
  omni_strong_equiv en_source en_target inp.
Proof.
  intros en_source en_target inp (Hsrc & Htgt & Htr).
  split.
  - destruct source_image as [segs pc ph], en_source as [sp brk0 mbase rnd].
    cbn [omni_corun img_segments] in *.
    exact (coexec_conseq _ _ _ _ Hsrc (never_errors_covered _)).
  - right. split; assumption.
Qed.

Lemma omni_strong_universal_error_free_implies :
  omni_strong_universal_error_free_T -> omni_strong_universal_T.
Proof.
  intros H en_source en_target inp Hs Ht Hi.
  apply omni_strong_equiv_error_free_implies, H; assumption.
Qed.

(** Where the two shapes diverge, as a refutation and in omni terms: an
    [exec … errors] judgment is realised by SOME maximal execution
    ([OmniRun.exec_realizes]), which ends in an error, and
    [coexec … never_errors] forbids exactly that ([OmniRun.coexec_sound]).
    The escape is therefore inconsistent with the error-free shape, not
    merely unused by it. *)
Lemma omni_strong_equiv_error_free_no_all_errors_escape :
  forall en_source en_target inp,
    omni_run source_image source_alloc_limit en_source inp errors ->
    ~ omni_strong_equiv_error_free en_source en_target inp.
Proof.
  intros en_source en_target inp Hall (Hsrc & _ & _).
  destruct source_image as [segs pc ph], en_source as [sp brk0 mbase rnd].
  cbn [omni_run omni_corun] in *.
  destruct (exec_realizes _ _ _ Hall) as (tr & o & Hm & Herr).
  exact (coexec_sound _ _ _ _ Hm _ Hsrc Herr).
Qed.

(** One erroring maximal execution at one valid triple refutes the
    whole error-free universal statement. *)
Lemma omni_strong_universal_error_free_refuted_by_source_error :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    omni_may source_image source_alloc_limit en_source inp errors ->
    ~ omni_strong_universal_error_free_T.
Proof.
  intros en_source en_target inp Hs Ht Hi Hmay H.
  destruct (H en_source en_target inp Hs Ht Hi) as (Hsrc & _ & _).
  destruct source_image as [segs pc ph], en_source as [sp brk0 mbase rnd].
  cbn [omni_may omni_corun] in *.
  destruct Hmay as (tr & o & Hm & Herr).
  exact (coexec_sound _ _ _ _ Hm _ Hsrc Herr).
Qed.

End Spec.

(* =========================================================================
   OMNI_SPEC / OMNI_SPEC_ERROR_FREE — the module types, and the bridges
   ========================================================================= *)

(** Same parameter shape as [Equivalence.SPEC]; only the statement is
    the omni one.  [Equivalence.IMAGE_WF] is unchanged and is still
    ascribed alongside, for the reason given there. *)
Module Type OMNI_SPEC (Source : MemImage) (Target : MemImage).
  Parameter omni_strong_universal :
    omni_strong_universal_T
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End OMNI_SPEC.

Module Type OMNI_SPEC_ERROR_FREE (Source : MemImage) (Target : MemImage).
  Parameter omni_strong_universal_error_free :
    omni_strong_universal_error_free_T
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End OMNI_SPEC_ERROR_FREE.

(** A proof in the legacy shape ascribes to the omni module type, and
    conversely: this is the whole consumer story.  A proof written
    against [omni_strong_universal_T] discharges [Equivalence.SPEC] by
    [SpecOfOmni], so the checker a consumer pins need not change. *)
Module OmniOfSpec (Source : MemImage) (Target : MemImage)
    (S : SPEC Source Target) <: OMNI_SPEC Source Target.
  Definition omni_strong_universal :=
    proj1 (strong_universal_iff _ _) S.strong_universal.
End OmniOfSpec.

Module SpecOfOmni (Source : MemImage) (Target : MemImage)
    (O : OMNI_SPEC Source Target) <: SPEC Source Target.
  Definition strong_universal :=
    proj2 (strong_universal_iff _ _) O.omni_strong_universal.
End SpecOfOmni.

Module OmniOfSpecErrorFree (Source : MemImage) (Target : MemImage)
    (S : SPEC_ERROR_FREE Source Target) <: OMNI_SPEC_ERROR_FREE Source Target.
  Definition omni_strong_universal_error_free :=
    proj1 (strong_universal_error_free_iff _ _) S.strong_universal_error_free.
End OmniOfSpecErrorFree.

Module SpecErrorFreeOfOmni (Source : MemImage) (Target : MemImage)
    (O : OMNI_SPEC_ERROR_FREE Source Target) <: SPEC_ERROR_FREE Source Target.
  Definition strong_universal_error_free :=
    proj2 (strong_universal_error_free_iff _ _) O.omni_strong_universal_error_free.
End SpecErrorFreeOfOmni.

(* =========================================================================
   Compat: the classifier families
   ========================================================================= *)

Lemma ex_and_iff : forall (A : Type) (V P P' : A -> Prop),
  (forall x, P x <-> P' x) ->
  ((exists x, V x /\ P x) <-> (exists x, V x /\ P' x)).
Proof.
  intros A V P P' H; split; intros (x & Hv & Hp); exists x; split;
    try exact Hv; apply H; exact Hp.
Qed.

(** [Classifier.agree]: trace agreement at every valid entry pair, and
    the three per-entry existential facts — may-error, must-error,
    may-leave-the-model — matched across the two images. *)
Definition omni_agree (X Y : Image) (lim : Z) (inp : ProcInput) : Prop :=
  (forall enX enY,
     valid_entry X enX inp -> valid_entry Y enY inp ->
     omni_trace_equiv X lim enX Y lim enY inp)
  /\ ((exists en, valid_entry X en inp /\ omni_may X lim en inp errors)
      <-> (exists en, valid_entry Y en inp /\ omni_may Y lim en inp errors))
  /\ ((exists en, valid_entry X en inp /\ omni_run X lim en inp errors)
      <-> (exists en, valid_entry Y en inp /\ omni_run Y lim en inp errors))
  /\ ((exists en, valid_entry X en inp
                  /\ omni_may X lim en inp (uncovered (img_segments X)))
      <-> (exists en, valid_entry Y en inp
                      /\ omni_may Y lim en inp (uncovered (img_segments Y)))).

Lemma agree_iff : forall X Y lim inp,
  agree X Y lim inp <-> omni_agree X Y lim inp.
Proof.
  intros X Y lim inp. unfold agree, omni_agree.
  assert (H1 : (forall enX enY, valid_entry X enX inp -> valid_entry Y enY inp ->
                 trace_equiv (bh_traces (run X lim enX inp)) (bh_traces (run Y lim enY inp)))
               <-> (forall enX enY, valid_entry X enX inp -> valid_entry Y enY inp ->
                 omni_trace_equiv X lim enX Y lim enY inp)).
  { split; intros H enX enY Hx Hy; apply trace_equiv_iff_omni; apply H; assumption. }
  rewrite H1.
  rewrite (ex_and_iff _ _ _ _ (fun en => bh_errors_may_iff X lim en inp)).
  rewrite (ex_and_iff _ _ _ _ (fun en => bh_errors_may_iff Y lim en inp)).
  rewrite (ex_and_iff _ _ _ _ (fun en => bh_all_errors_iff X lim en inp)).
  rewrite (ex_and_iff _ _ _ _ (fun en => bh_all_errors_iff Y lim en inp)).
  rewrite (ex_and_iff _ _ _ _ (fun en => bh_unmodeled_may_iff X lim en inp)).
  rewrite (ex_and_iff _ _ _ _ (fun en => bh_unmodeled_may_iff Y lim en inp)).
  reflexivity.
Qed.

Definition omni_good_input (O1 O2 : Image) (inp : ProcInput) : Prop :=
  forall en1 en2,
    valid_entry O1 en1 inp -> valid_entry O2 en2 inp ->
    omni_strong_equiv_error_free O1 O2 en1 en2 inp.

Lemma good_input_iff : forall O1 O2 inp,
  good_input O1 O2 inp <-> omni_good_input O1 O2 inp.
Proof.
  intros O1 O2 inp. unfold good_input, omni_good_input.
  split; intros H en1 en2 H1 H2; apply strong_equiv_error_free_iff; apply H; assumption.
Qed.

(** [Classifier.decides], with [MustExit.must_exit_with] read as
    [omni_run … (exits_with verdict)]. *)
Definition omni_decides (C : Image) (spec : ProcInput -> Prop) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en,
      valid_entry C en (to_proc_input f) ->
      (omni_run C classifier_alloc_limit en (to_proc_input f) (exits_with verdict_accept)
       <-> spec (to_proc_input f))
      /\ (omni_run C classifier_alloc_limit en (to_proc_input f) (exits_with verdict_accept)
          \/ omni_run C classifier_alloc_limit en (to_proc_input f) (exits_with verdict_reject)).

Lemma decides_iff : forall C spec,
  decides C spec <-> omni_decides C spec.
Proof.
  intros C spec. unfold decides, omni_decides.
  split; intros H f Hf en Hen; destruct (H f Hf en Hen) as (Hspec & Htot).
  - split.
    + rewrite <- Hspec. symmetry. apply must_exit_with_iff.
    + destruct Htot as [Ha | Hr]; [left | right]; apply must_exit_with_iff; assumption.
  - split.
    + rewrite <- Hspec. apply must_exit_with_iff.
    + destruct Htot as [Ha | Hr]; [left | right]; apply must_exit_with_iff; assumption.
Qed.

(** The spec side of [omni_decides] is respected up to [iff], which is
    what lets the two classifier obligations be restated below. *)
Lemma omni_decides_spec_iff : forall C (spec spec' : ProcInput -> Prop),
  (forall inp, spec inp <-> spec' inp) ->
  (omni_decides C spec <-> omni_decides C spec').
Proof.
  intros C spec spec' Hs. unfold omni_decides.
  split; intros H f Hf en Hen; destruct (H f Hf en Hen) as (Hspec & Htot);
    split; try exact Htot; rewrite Hspec; [apply Hs | symmetry; apply Hs].
Qed.

Definition omni_classifier_total_T (Cl : Image) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en,
      valid_entry Cl en (to_proc_input f) ->
      omni_run Cl classifier_alloc_limit en (to_proc_input f) (exits_with verdict_accept)
      \/ omni_run Cl classifier_alloc_limit en (to_proc_input f) (exits_with verdict_reject).

Lemma classifier_total_iff : forall Cl,
  classifier_total_T Cl <-> omni_classifier_total_T Cl.
Proof.
  intros Cl. unfold classifier_total_T, omni_classifier_total_T.
  split; intros H f Hf en Hen; destruct (H f Hf en Hen) as [Ha | Hr];
    [left | right | left | right]; apply must_exit_with_iff; assumption.
Qed.

Lemma omni_decides_implies_total : forall C spec,
  omni_decides C spec -> omni_classifier_total_T C.
Proof. intros C spec Hdec f Hf en Hen. exact (proj2 (Hdec f Hf en Hen)). Qed.

Definition omni_classifies_patch_diff_T (O1 P1 O2 P2 C : Image) : Prop :=
  omni_decides C (fun inp => omni_agree O1 P1 source_alloc_limit inp
                             /\ omni_agree O2 P2 target_alloc_limit inp).

Lemma classifies_patch_diff_iff : forall O1 P1 O2 P2 C,
  classifies_patch_diff_T O1 P1 O2 P2 C <-> omni_classifies_patch_diff_T O1 P1 O2 P2 C.
Proof.
  intros O1 P1 O2 P2 C. unfold classifies_patch_diff_T, omni_classifies_patch_diff_T.
  rewrite decides_iff. apply omni_decides_spec_iff.
  intros inp. rewrite (agree_iff O1 P1), (agree_iff O2 P2). reflexivity.
Qed.

Definition omni_classifies_good_inputs_T (O1 O2 C : Image) : Prop :=
  omni_decides C (omni_good_input O1 O2).

Lemma classifies_good_inputs_iff : forall O1 O2 C,
  classifies_good_inputs_T O1 O2 C <-> omni_classifies_good_inputs_T O1 O2 C.
Proof.
  intros O1 O2 C. unfold classifies_good_inputs_T, omni_classifies_good_inputs_T.
  rewrite decides_iff. apply omni_decides_spec_iff. apply good_input_iff.
Qed.
