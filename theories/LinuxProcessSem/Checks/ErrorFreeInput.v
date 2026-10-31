(** * LinuxProcessSem.Checks.ErrorFreeInput — the buggy / not-buggy gate, witnessed

    Not part of the trusted specification: QA on
    [Classifier.error_free_input] and
    [Classifier.classifies_error_free_inputs_T], in the style of
    [Checks/Examples.v] and [Checks/EntryStackFits.v].

    [EquivalenceDefinition.Classifier] states what the gate of a
    two-region submission decides — whether the ORIGINAL program is
    error-free on the input — and proves that of ABSTRACT images.
    Nothing there exhibits an original.  A predicate that no concrete
    binary is ever shown to satisfy, and none to refute, would leave
    both its bite and its vacuity lemma free, so this file runs the
    definition on the two concrete riscv64 images
    [Checks/Examples.v] already built and one concrete input, and pins
    both answers:

    - PART 1 — the two regions, inhabited.  [Checks.Examples.exit0_image]
      is error-free on this input at EVERY entry [execve] could have
      chosen, which is what [Classifier.error_free_input] quantifies
      over; [Checks.Examples.undecodable_image] is not, refuted from ONE
      valid entry, which is all a refutation needs.
    - PART 2 — what those answers oblige a gate to do.  A gate meeting
      [Classifier.classifies_error_free_inputs_T] for the undecodable
      original must exit 1 on this input, and one meeting it for the
      exit-0 original must exit 0 — at every valid entry of its own, in
      both cases, and whatever else the gate does.
    - PART 3 — the vacuity route the trusted file names, biting the
      ORIGINAL rather than the gate: an original that does not load is
      not-buggy everywhere, so a gate that decides correctly about it
      accepts the whole input space and the second program of the split
      is never asked about anything.

    Which of the four reasons at the top of [Checks/Examples.v] admits
    this file: the FIRST.  [Classifier.error_free_input] is a [forall]
    over every valid [Run.ExecEntry] ending in [Equivalence.error_free],
    itself the negation of a reachability claim about a whole run tree,
    and [Classifier.decides] adds a [MustExit.must_exit_with] over that
    same tree.  A real run shows one execution of one
    of these binaries; it cannot show all of them, and it has no notion
    of a region at all.

    The images and the entry are reused rather than rebuilt —
    [Checks.Examples.exit0_image], [Checks.Examples.undecodable_image]
    and [Checks.Examples.demo_entry], with
    [Checks.Examples.exits_c_must_exit_at] as the evaluator that
    discharges the run tree.  Only the input record is new, and only
    because the gate statements are indexed by
    [FinInput.FinProcInput]. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit FinInput Classifier.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The input everything below runs on
   ========================================================================= *)

(** One empty argument, no environment, an empty file system, no
    standard input — the input [Checks/Examples.v]'s own witnesses use,
    named here so the statements below read as claims about a fixed
    input rather than about a literal repeated eleven times. *)
Definition efi_demo_input : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

Lemma efi_demo_input_valid : valid_input efi_demo_input.
Proof. exact demo_input_valid. Qed.

(** The same input as a [FinInput.FinProcInput], which is what
    [Classifier.decides] quantifies over: the gate obligations are
    stated on finite inputs, for the reason
    [EquivalenceDefinition.Classifier]'s header gives — a verdict is an
    observable event, so accept sets are open in the prefix topology and
    the properties worth classifying are not.  [efi_demo_to_proc_input]
    pins that the two records agree by computation rather than by the
    reader's eye. *)
Definition efi_demo_fin : FinProcInput :=
  mkFinProcInput [[]] [] [] [] demo_uid demo_gid demo_groups net_silent
                 default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48 [] []
                 default_kernel.

Lemma efi_demo_to_proc_input : to_proc_input efi_demo_fin = efi_demo_input.
Proof. reflexivity. Qed.

(** It is a VALID finite input, which every gate statement below needs:
    an obligation quantified over valid inputs is refuted by nothing
    else, and a region containing only invalid inputs is a region no
    program is ever asked about. *)
Lemma efi_demo_fin_valid : valid_fin_input efi_demo_fin.
Proof.
  unfold valid_fin_input. rewrite efi_demo_to_proc_input.
  exact efi_demo_input_valid.
Qed.

(* =========================================================================
   PART 1 — the two regions, inhabited
   ========================================================================= *)

(** The exit-0 image must exit 0 AT EVERY ENTRY, at the SOURCE role's
    budget.  Both halves of that sentence are the point.

    Every entry, because [Classifier.error_free_input] is a [forall]
    over them and one entry would not do it: the original has to behave
    however [execve] placed its stack, break and mmap base, and whatever
    16 AT_RANDOM bytes it drew.  It is
    provable here for the reason [Checks/Examples.v]'s header gives for
    this program — it makes no memory access at all beyond its own
    instruction fetches — so all four entry fields are left as VARIABLES
    and the fuel evaluator reduces past them.  An original that consulted
    its stack pointer, or read the bytes AT_RANDOM points at, would leave
    the reduction stuck on one, which is the honest outcome rather than a
    slow one.

    [State.source_alloc_limit], because that is the budget
    [Classifier.error_free_input] names, and it is not
    [Classifier.classifier_alloc_limit] (which is what the GATE would run
    at) and not [Cases.Prelude.demo_limit] (which
    [Checks.Examples.exit0_image_must_exit_zero] uses). *)
Lemma exit0_must_exit_zero_at_source_budget : forall en,
  must_exit_with verdict_accept exit0_image source_alloc_limit en efi_demo_input.
Proof.
  intros en. destruct en as [sp brk0 mbase rnd].
  cbn [must_exit_with exit0_image]. unfold init_config.
  apply (exits_c_must_exit_at _ _ 8); [reflexivity | reflexivity |].
  vm_compute. reflexivity.
Qed.

(** THE NOT-BUGGY REGION IS INHABITED: this input is in it, for the
    exit-0 original.  The step from "must exit 0" to "never errors" is
    [MustExit.must_exit_with_no_error], which is what lets a
    [MustExit.must_exit_with] obligation stand in for an error-freedom
    one — a binary that decides by exiting cannot also be allowed to
    fault.  The entry hypothesis is discarded rather than used: the
    exit-0 image behaves at EVERY entry, valid or not, which is stronger
    than the definition asks for. *)
Lemma exit0_error_free_input : error_free_input exit0_image efi_demo_input.
Proof.
  intros en _.
  exact (must_exit_with_no_error _ _ _ _ _
           (exit0_must_exit_zero_at_source_budget en)).
Qed.

(** THE BUGGY REGION IS INHABITED TOO, at the same input for a different
    original: the undecodable image errors on its first fetch, so it is
    not error-free there.  One valid entry is enough, which is the
    asymmetry [Classifier.error_free_input]'s [forall] creates and
    [Classifier.error_free_input_refuted_by_error] is the elimination
    rule for.

    The error is reached through [Equivalence.run_unmodeled_errors]:
    leaving the modeled surface is a special case of erroring, and
    [Checks.Examples.run_of_undecodable_image_is_unmodeled_at_demo_entry]
    is already stated at [State.source_alloc_limit] — the budget this
    predicate names — rather than at [Cases.Prelude.demo_limit]. *)
Lemma undecodable_not_error_free_input :
  ~ error_free_input undecodable_image efi_demo_input.
Proof.
  apply (error_free_input_refuted_by_error _ _ demo_entry).
  - apply demo_entry_valid_undecodable. exact efi_demo_input_valid.
  - apply run_unmodeled_errors,
      run_of_undecodable_image_is_unmodeled_at_demo_entry.
Qed.

(** The two answers really are different answers, which is the fact a
    region boundary is made of.  Asserted as a pair rather than left to
    a reader who has both lemmas in hand, because a predicate constant
    on the images anyone tries it on would carve no boundary at all and
    every disjointness fact about the two regions would be free. *)
Lemma error_free_input_separates_the_two_images :
  error_free_input exit0_image efi_demo_input
  /\ ~ error_free_input undecodable_image efi_demo_input.
Proof.
  split; [exact exit0_error_free_input | exact undecodable_not_error_free_input].
Qed.

(* =========================================================================
   PART 2 — what those answers oblige a gate to do
   ========================================================================= *)

(** A gate that decides this predicate about the UNDECODABLE original
    must exit 1 on this input, at every valid entry of its own.  The
    gate is quantified, not exhibited, because the claim is about what
    the obligation FORCES rather than about a binary.  Exhibiting one is
    a different and much larger piece of work — the shape of it is
    [Examples.patchclassify_demo.Obligations], which builds a concrete
    classifier for each of the other two properties in this family and
    proves [Classifier.decides] of it — and no image has been built for
    THIS property.

    Note the budget the conclusion is at:
    [Classifier.classifier_alloc_limit], the one the gate RUNS at, while
    the hypothesis feeding it was about the original's run at
    [State.source_alloc_limit].  The two budgets appear in one statement
    and never in one run. *)
Lemma gate_for_undecodable_original_must_exit_one : forall C enC,
  classifies_error_free_inputs_T undecodable_image C ->
  valid_entry C enC (to_proc_input efi_demo_fin) ->
  must_exit_with verdict_reject C classifier_alloc_limit enC
    (to_proc_input efi_demo_fin).
Proof.
  intros C enC Hdec HenC.
  apply (classifies_error_free_inputs_T_rejects_error
           undecodable_image C efi_demo_fin demo_entry enC Hdec
           efi_demo_fin_valid).
  - rewrite efi_demo_to_proc_input.
    apply demo_entry_valid_undecodable. exact efi_demo_input_valid.
  - rewrite efi_demo_to_proc_input.
    apply run_unmodeled_errors,
      run_of_undecodable_image_is_unmodeled_at_demo_entry.
  - exact HenC.
Qed.

(** ... and the same input read as a member of the gate's REJECT SET,
    which is the reading the measure layer sums over
    ([Classifier.rejects] is [FinInput.valid_fin_input] together with
    the negation of [Classifier.accepts]).  Stated as well as the exit
    code because the two are the same fact only for a gate with an
    inhabited entry space, and that hypothesis is where the difference
    lives. *)
Lemma gate_for_undecodable_original_rejects : forall C enC,
  classifies_error_free_inputs_T undecodable_image C ->
  valid_entry C enC (to_proc_input efi_demo_fin) ->
  rejects C efi_demo_fin.
Proof.
  intros C enC Hdec HenC.
  apply (classifies_error_free_inputs_T_refutes_acceptance
           undecodable_image C efi_demo_fin demo_entry enC Hdec
           efi_demo_fin_valid).
  - rewrite efi_demo_to_proc_input.
    apply demo_entry_valid_undecodable. exact efi_demo_input_valid.
  - rewrite efi_demo_to_proc_input.
    apply run_unmodeled_errors,
      run_of_undecodable_image_is_unmodeled_at_demo_entry.
  - exact HenC.
Qed.

(** ... and the other direction, for the exit-0 original: the gate must
    ACCEPT, at every valid entry, which is [Classifier.accepts] itself.
    Both directions are pinned because the obligation is an iff and
    either half alone would be met by a gate with one fixed answer. *)
Lemma gate_for_exit0_original_accepts : forall C,
  classifies_error_free_inputs_T exit0_image C ->
  accepts C efi_demo_fin.
Proof.
  intros C Hdec.
  apply (classifies_error_free_inputs_T_accepts_error_free
           exit0_image C efi_demo_fin Hdec efi_demo_fin_valid).
  rewrite efi_demo_to_proc_input. exact exit0_error_free_input.
Qed.

(** The two verdicts a gate is forced into at this one input are
    incompatible, so no single image is a correct gate for both
    originals.  That is the sharpest form of "the boundary is not the
    submission's to choose": the gate's answer is determined by which
    original it is asked about.

    The contradiction runs through [MustExit.must_exit_with_exclusive]
    against [Classifier.verdict_accept_neq_reject], and it needs one
    valid entry of the gate to have anything to contradict — with none,
    [Classifier.decides_vacuous_no_entries] hands both hypotheses to the
    same image for free, so the statement stripped of that entry would
    be false.  It is the [Equivalence.IMAGE_WF] obligation showing up in
    the smallest possible statement. *)
Lemma no_gate_serves_both_originals : forall C enC,
  valid_entry C enC (to_proc_input efi_demo_fin) ->
  classifies_error_free_inputs_T undecodable_image C ->
  classifies_error_free_inputs_T exit0_image C ->
  False.
Proof.
  intros C enC HenC Hbad Hgood.
  apply verdict_accept_neq_reject.
  symmetry.
  exact (must_exit_with_exclusive _ _ _ _ _ _
           (gate_for_undecodable_original_must_exit_one C enC Hbad HenC)
           (gate_for_exit0_original_accepts C Hgood enC HenC)).
Qed.

(* =========================================================================
   PART 3 — the vacuity route, biting the ORIGINAL
   ========================================================================= *)

(** An original that does not load is NOT-BUGGY EVERYWHERE, so a gate
    that decides correctly about it accepts the whole input space: the
    not-buggy region is everything, the second program of the split is
    never asked about any input, and its own slice obligation holds with
    nothing established about its binary.

    [Obad] is quantified rather than exhibited, because the tree carries
    no concrete image for which [Run.valid_entry] is empty at a valid
    input — [Run.valid_sp] and [Run.valid_mmap_base] do not depend on
    the image, and [Equivalence.image_brk_satisfiable_entry] inhabits the
    rest for a well-formed one.  The hypothesis is exactly
    [Classifier.error_free_input_vacuous_no_entries]'s.

    WHICH IMAGE THE HOLE IS IN is the point of stating this here at all.
    [Classifier.accepts_vacuous_no_entries] and
    [Classifier.decides_vacuous_no_entries] are about the GATE failing to
    load; this survives a gate that is perfectly well-formed and doing
    its job correctly.  A checker that ascribed [Equivalence.IMAGE_WF] to
    its gate images and forgot the original would be pinning exactly
    this. *)
Lemma unloadable_original_makes_the_gate_accept_everything :
  forall Obad C,
    classifies_error_free_inputs_T Obad C ->
    (forall f en, ~ valid_entry Obad en (to_proc_input f)) ->
    forall f, valid_fin_input f -> accepts C f.
Proof.
  intros Obad C Hdec Hno.
  exact (classifies_error_free_inputs_T_vacuous_accepts_everything
           Obad C Hdec Hno).
Qed.

(** ... including at the one input this file computes on, which is
    where the route costs something.  A checker looking at two submitted
    originals that both fail to do anything — one that traps on its
    first instruction, one that does not load — would call those the
    same failure.  The gate is forced to REFUSE this input for the
    first ([gate_for_undecodable_original_rejects]) and forced to ACCEPT
    it for the second, so the two get OPPOSITE verdicts and the second
    is the one that costs the checker the whole partition. *)
Lemma unloadable_original_flips_the_refusal : forall Obad C,
  classifies_error_free_inputs_T Obad C ->
  (forall f en, ~ valid_entry Obad en (to_proc_input f)) ->
  accepts C efi_demo_fin.
Proof.
  intros Obad C Hdec Hno.
  exact (unloadable_original_makes_the_gate_accept_everything
           Obad C Hdec Hno efi_demo_fin efi_demo_fin_valid).
Qed.

(* =========================================================================
   PART 4 — the same two answers, under the configuration layer
   ========================================================================= *)

(** The undecodable image is uncovered under EVERY configuration, not
    just under may-fail.  Turning a spurious-failure family off removes
    executions ([Run.run_scfg_sub_unmodeled] runs the other way), so
    nothing carries an uncovered point down from the may-fail run for
    free — but nothing has to here, because this image is unmodeled at
    its FIRST FETCH, before any syscall and so before any family can
    fire.  The witness is the empty [Run.star_cfg], which exists at every
    [cfg] by [Run.star_cfg_refl].

    This is the one fact Part 1 does not already give under a
    configuration; the accepting side is inherited, below. *)
Lemma undecodable_unmodeled_scfg : forall cfg,
  bh_unmodeled (run_scfg cfg undecodable_image source_alloc_limit demo_entry
                  efi_demo_input).
Proof.
  intros cfg.
  cbn [run_scfg bh_unmodeled undecodable_image demo_entry]. unfold init_config.
  eexists [], _. split; [apply star_cfg_refl |].
  unfold unmodeled_at. cbn [cfg_ms cfg_model].
  split; [reflexivity |]. left. split; [reflexivity |].
  split; [| vm_compute; reflexivity].
  match goal with
  | |- mi_account_step ?segs ?ms ?model = _ =>
      rewrite (mi_account_step_no_lazy segs ms model ltac:(reflexivity))
  end.
  vm_compute. reflexivity.
Qed.

(** THE BUGGY REGION, under every configuration.  Leaving the modeled
    surface is a special case of erroring at each [cfg] too
    ([Run.run_scfg_unmodeled_errors]), so the undecodable original is
    outside the not-buggy region however the task configured its
    families. *)
Lemma undecodable_not_error_free_input_s : forall cfg,
  ~ error_free_input_s cfg undecodable_image efi_demo_input.
Proof.
  intros cfg.
  apply (error_free_input_s_refuted_by_error cfg _ _ demo_entry).
  - apply demo_entry_valid_undecodable. exact efi_demo_input_valid.
  - apply run_scfg_unmodeled_errors, undecodable_unmodeled_scfg.
Qed.

(** THE NOT-BUGGY REGION, under every configuration, and this half is
    inherited rather than recomputed: fewer executions cannot add an
    error, which is
    [Classifier.error_free_input_s_of_error_free_input].  So the exit-0
    original stays not-buggy at every [cfg], and the two images are
    separated under every configuration, not only under may-fail. *)
Lemma exit0_error_free_input_s : forall cfg,
  error_free_input_s cfg exit0_image efi_demo_input.
Proof.
  intros cfg.
  exact (error_free_input_s_of_error_free_input cfg exit0_image efi_demo_input
           exit0_error_free_input).
Qed.

Lemma error_free_input_s_separates_the_two_images : forall cfg,
  error_free_input_s cfg exit0_image efi_demo_input
  /\ ~ error_free_input_s cfg undecodable_image efi_demo_input.
Proof.
  intros cfg.
  split; [exact (exit0_error_free_input_s cfg)
         | exact (undecodable_not_error_free_input_s cfg)].
Qed.

(** What that obliges a CONFIGURED gate to do, at every configuration:
    exit 1 on this input for the undecodable original and accept it for
    the exit-0 one, at every valid entry of its own, with the gate's own
    run pinned to [Run.forced_only_cfg] the way
    [Classifier.classifies_error_free_inputs_T_s] pins it.  The gate is
    quantified, as in Part 2 and for the same reason. *)
Lemma gate_s_for_undecodable_original_must_exit_one : forall cfg C enC,
  classifies_error_free_inputs_T_s cfg undecodable_image C ->
  valid_entry C enC (to_proc_input efi_demo_fin) ->
  must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit enC
    (to_proc_input efi_demo_fin).
Proof.
  intros cfg C enC Hdec HenC.
  apply (classifies_error_free_inputs_T_s_rejects_error
           cfg undecodable_image C efi_demo_fin demo_entry enC Hdec
           efi_demo_fin_valid).
  - rewrite efi_demo_to_proc_input.
    apply demo_entry_valid_undecodable. exact efi_demo_input_valid.
  - rewrite efi_demo_to_proc_input.
    apply run_scfg_unmodeled_errors, undecodable_unmodeled_scfg.
  - exact HenC.
Qed.

Lemma gate_s_for_exit0_original_accepts : forall cfg C,
  classifies_error_free_inputs_T_s cfg exit0_image C ->
  accepts_fo C efi_demo_fin.
Proof.
  intros cfg C Hdec.
  apply (classifies_error_free_inputs_T_s_accepts_error_free
           cfg exit0_image C efi_demo_fin Hdec efi_demo_fin_valid).
  rewrite efi_demo_to_proc_input. exact (exit0_error_free_input_s cfg).
Qed.

(** ... and the separation survives: no image is a correct configured
    gate for both originals, at any configuration.  Part 2's statement
    with the whole configuration layer underneath it, and the same
    valid-entry hypothesis for the same reason —
    [Classifier.decides_fo_vacuous_no_entries] hands both hypotheses to
    an unloadable gate for free. *)
Lemma no_gate_s_serves_both_originals : forall cfg C enC,
  valid_entry C enC (to_proc_input efi_demo_fin) ->
  classifies_error_free_inputs_T_s cfg undecodable_image C ->
  classifies_error_free_inputs_T_s cfg exit0_image C ->
  False.
Proof.
  intros cfg C enC HenC Hbad Hgood.
  apply verdict_accept_neq_reject.
  symmetry.
  exact (must_exit_with_scfg_exclusive _ _ _ _ _ _ _
           (gate_s_for_undecodable_original_must_exit_one cfg C enC Hbad HenC)
           (gate_s_for_exit0_original_accepts cfg C Hgood enC HenC)).
Qed.

(** The [_fo] name carries the same three facts, and they are the
    [Run.may_fail_cfg] instances of the three above through
    [Classifier.classifies_error_free_inputs_T_fo_iff_s_may_fail].  Stated
    under that name because the [_fo] form is one a checker emits, so a
    reader checking what it obliges should not have to find the
    rewrite. *)
Lemma gate_fo_for_undecodable_original_must_exit_one : forall C enC,
  classifies_error_free_inputs_T_fo undecodable_image C ->
  valid_entry C enC (to_proc_input efi_demo_fin) ->
  must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit enC
    (to_proc_input efi_demo_fin).
Proof.
  intros C enC Hdec HenC.
  apply (gate_s_for_undecodable_original_must_exit_one may_fail_cfg C enC);
    [| exact HenC].
  exact (proj1 (classifies_error_free_inputs_T_fo_iff_s_may_fail _ C) Hdec).
Qed.

Lemma gate_fo_for_exit0_original_accepts : forall C,
  classifies_error_free_inputs_T_fo exit0_image C ->
  accepts_fo C efi_demo_fin.
Proof.
  intros C Hdec.
  apply (gate_s_for_exit0_original_accepts may_fail_cfg C).
  exact (proj1 (classifies_error_free_inputs_T_fo_iff_s_may_fail _ C) Hdec).
Qed.

Lemma no_gate_fo_serves_both_originals : forall C enC,
  valid_entry C enC (to_proc_input efi_demo_fin) ->
  classifies_error_free_inputs_T_fo undecodable_image C ->
  classifies_error_free_inputs_T_fo exit0_image C ->
  False.
Proof.
  intros C enC HenC Hbad Hgood.
  apply (no_gate_s_serves_both_originals may_fail_cfg C enC HenC).
  - exact (proj1 (classifies_error_free_inputs_T_fo_iff_s_may_fail _ C) Hbad).
  - exact (proj1 (classifies_error_free_inputs_T_fo_iff_s_may_fail _ C) Hgood).
Qed.
