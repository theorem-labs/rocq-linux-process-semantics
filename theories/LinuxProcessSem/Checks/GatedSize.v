(** * LinuxProcessSem.Checks.GatedSize — a two-gate partition, worked out

    Not part of the trusted specification: QA on the definitions in
    [EquivalenceDefinition.GatedSize], in the style of [Checks/Examples.v]
    and [Checks/EntryStackFits.v].

    [EquivalenceDefinition.GatedSize] states that a list of gate images
    cuts the finite input space into disjoint, exhaustive parts, and
    proves it of ABSTRACT images.  Nothing there exhibits a gate.  A
    partition of the input space that no pair of real programs is ever
    shown to produce would be a definition satisfied by nothing, and the
    disjointness lemmas would be free.  So this file runs the definitions
    on two concrete riscv64 binaries and one concrete input, and shows
    all three slice shapes inhabited:

    - PART 1 — the two verdicts.  Two three-instruction images, one
      exiting 0 and one exiting 1.  The accepting verdict is proved for
      EVERY entry the kernel could have chosen, which is what
      [Classifier.accepts] quantifies over; the refusal is proved from
      ONE valid entry, which is all a refutation needs.
    - PART 2 — the three shapes, each inhabited by reordering the same
      two gates: the FIRST slice, a LATER slice (whose earlier gate
      really does refuse), and the RESIDUE.
    - PART 3 — disjointness, applied rather than restated: the concrete
      slice facts of Part 2 are fed to
      [GatedSize.slices_disjoint_accept_accept] and
      [GatedSize.slices_disjoint_accept_rest], and what comes back is a
      refutation of the other slices at this input.
    - PART 4 — [GatedSize.slices_exhaustive] instantiated at each of
      those gate lists, with the per-gate decidability hypothesis
      discharged from Part 1 rather than assumed.  Then the one-program
      case: no gates, one part, the whole input space.
    - PART 5 — the vacuity route the trusted file names, shown biting a
      concrete partition: one image with no valid entry, placed among
      the gates, empties the residue even though the gate beside it
      genuinely refuses every input.
    - PART 6 — the weight bound, refuted concretely at two inputs whose
      cores differ, and carried across
      [GatedSize.weight_bound_pred_of_classifier] to the classifier
      reading it generalises, then SATISFIED at the one-program slice,
      whose complement is empty and whose bound is therefore [0].
    - PART 7 — the two per-slice obligations refuted on a concrete image
      pair.  Both shapes get a positive and a negative case here:
      [GatedSize.gated_slice_T] and [GatedSize.gated_slice_error_free_T]
      hold of every predicate for a pair proved equivalent outright
      (Part 4), and both are refuted outright by the undecodable image
      (Part 7).
    - PART 8 — the same partition and the same obligations under a
      spurious-failure configuration.  The two verdicts are proved again
      at the pinned reading rather than carried over, and Part 7's two
      refutations are proved at EVERY [Run.SpuriousCfg] rather than at
      one.

    Which of the four reasons at the top of [Checks/Examples.v] admits
    this file: the FIRST.  [Classifier.accepts] is a [forall] over every
    valid [Run.ExecEntry] ending in [MustExit.must_exit_with], itself a
    claim about a whole run tree, and no finite set of traces establishes
    either.  A real run shows one execution of one of
    these binaries; it cannot show all of them, and it has no notion of
    a slice at all.

    The images and the entry are the ones [Checks/Examples.v] already
    built — [Checks.Examples.exit0_image] and [Checks.Examples.demo_entry],
    with [Checks.Examples.exits_c_must_exit_at] as the evaluator that
    discharges the run tree — reused rather than rebuilt.  Only the
    exit-1 twin is new.  Part 8 needs a second evaluator for the pinned
    reading, [Checks.SpuriousCfg.exits_c_must_exit_at_cfg], which is the
    same [Checks.Examples.exits_c] over [Run.sstep_cfg]; that is the one
    import this file takes beyond [Checks/Examples.v]. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples SpuriousCfg.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit FinInput Classifier Measure GatedSize.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   PART 1 — two gates, and what each one answers
   ========================================================================= *)

(** The refusing gate: [Checks.Examples.exit0_image]'s program with one
    immediate changed.  Three instructions at 0x100, as the hex the
    loader would have produced — [addi a7, x0, 93] (0x05d00893),
    [addi a0, x0, 1] (0x00100513), [ecall] (0x00000073), little-endian.
    Same base, same size, same program headers as the exit-0 image, so
    the two are interchangeable everywhere [Run.valid_entry] is
    concerned and the only difference between them is the verdict. *)
Definition exit1_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 12;
  seg_perms := "r-x"%string;
  seg_bytes := ["9308d0051305100073000000"%pstring]
|}.
Definition exit1_segments : list Segment := [exit1_segment].
Definition exit1_image : Image := mkImage exit1_segments 0x100 demo_phdrs.

(** The input the whole file runs on: one empty argument, no
    environment, an empty file system, no standard input.  A
    [FinInput.FinProcInput], because that is what a slice predicate is
    defined on; [FinInput.to_proc_input] carries it to the
    [State.ProcInput] the runs consume, and
    [gated_demo_to_proc_input] pins that the two agree by
    computation rather than by the reader's eye. *)
Definition gated_demo_fin : FinProcInput :=
  mkFinProcInput [[]] [] [] [] demo_uid demo_gid demo_groups net_silent
                 default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48 [] [] true true.

Lemma gated_demo_to_proc_input :
  to_proc_input gated_demo_fin
  = mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.
Proof. reflexivity. Qed.

(** It is a VALID finite input, which every statement below needs: an
    obligation quantified over valid inputs is refuted by nothing else,
    and a slice containing only invalid inputs is a slice no program is
    ever asked about. *)
Lemma gated_demo_fin_valid : valid_fin_input gated_demo_fin.
Proof.
  unfold valid_fin_input. rewrite gated_demo_to_proc_input.
  exact demo_input_valid.
Qed.

(** The exit-1 image really is startable at
    [Checks.Examples.demo_entry] on this input.  Copied from
    [Checks.Examples.demo_entry_valid_exit0] because the two images have
    the same reservation, and needed for the refusal below: a refutation
    of [Classifier.accepts] that named an INVALID entry would refute
    nothing, since the definition never quantified over it. *)
Lemma demo_entry_valid_exit1 : forall inp,
  valid_input inp -> valid_entry exit1_image demo_entry inp.
Proof.
  intros inp Hvalid.
  rewrite (valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvalid)).
  destruct Hvalid as (Hargv & Henvp & _).
  pose proof (entry_stack_span_bound _ _ Hargv Henvp).
  cbn [exit1_image demo_entry].
  unfold valid_sp, valid_brk, valid_mmap_base, entry_stack_fits.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  unfold entry_stack_span_max, sp_window_lo, sp_window_hi in *.
  repeat split; try lia; vm_compute; try reflexivity; try discriminate.
Qed.

(** The accepting verdict, AT EVERY ENTRY.  [Classifier.accepts] is a
    [forall] over entries, so one entry would not do it, and this is the
    direction the definition makes hard: the program must exit 0 however
    [execve] placed its stack, break and mmap base, and whatever 16
    AT_RANDOM bytes it drew.  It is provable here
    for the reason [Checks.Examples]'s header gives for the same
    program — it makes no memory access at all beyond its own
    instruction fetches — so all four entry fields are left as VARIABLES
    and the fuel evaluator reduces past them.  A gate that consulted its
    stack pointer, or read the bytes AT_RANDOM points at, would leave the
    reduction stuck on one, which is the honest outcome rather than a
    slow one.

    Note the budget: [Classifier.classifier_alloc_limit], the one
    [Classifier.accepts] runs a gate at, not
    [Cases.Prelude.demo_limit] and not either of the two roles'
    budgets that [Equivalence.strong_equiv] hardwires. *)
Lemma gate_exit0_accepts : Classifier.accepts exit0_image gated_demo_fin.
Proof.
  intros en _.
  destruct en as [sp brk0 mbase rnd].
  cbn [must_exit_with exit0_image]. unfold init_config.
  apply (exits_c_must_exit_at _ _ 8); [reflexivity | reflexivity |].
  vm_compute. reflexivity.
Qed.

(** ... and the refusal.  Exiting 1 at ONE valid entry is enough, which
    is the asymmetry [Classifier.accepts]'s [forall] creates and
    [Classifier.rejects_by_exit1] is the introduction rule for: the step
    from "exits 1 here" to "does not accept" runs through
    [MustExit.must_exit_with_exclusive] against
    [Classifier.verdict_accept_neq_reject]. *)
Lemma gate_exit1_rejects : Classifier.rejects exit1_image gated_demo_fin.
Proof.
  apply (rejects_by_exit1 _ _ demo_entry).
  - exact gated_demo_fin_valid.
  - apply demo_entry_valid_exit1. rewrite gated_demo_to_proc_input.
    exact demo_input_valid.
  - cbn [must_exit_with exit1_image demo_entry]. unfold init_config.
    apply (exits_c_must_exit_at _ _ 8); [reflexivity | reflexivity |].
    vm_compute. reflexivity.
Qed.

Lemma gate_exit1_refuses : ~ Classifier.accepts exit1_image gated_demo_fin.
Proof. exact (proj2 gate_exit1_rejects). Qed.

(* =========================================================================
   PART 2 — all three slice shapes, inhabited
   ========================================================================= *)

(** The three gate lists.  The same two images in three arrangements,
    which is enough to put this one input in each of the three shapes in
    turn — a slice is a property of the input AND the list, and reading
    it off one fixed list would show at most one shape. *)
Definition gates_accept_first : list Image := [exit0_image; exit1_image].
Definition gates_accept_second : list Image := [exit1_image; exit0_image].
Definition gates_refuse_all : list Image := [exit1_image; exit1_image].

(** THE FIRST SLICE: the leading gate accepts, and there is no earlier
    gate to refuse. *)
Lemma slice_first_inhabited : slice_accept [] exit0_image gated_demo_fin.
Proof.
  split; [exact gate_exit0_accepts | apply List.Forall_nil].
Qed.

(** A LATER SLICE, and the interesting one: the accepting gate is
    reached only because the gate before it refuses, and that refusal is
    proved rather than assumed.  This is the shape a submission's second
    program is measured on. *)
Lemma slice_second_inhabited :
  slice_accept [exit1_image] exit0_image gated_demo_fin.
Proof.
  split; [exact gate_exit0_accepts |].
  apply List.Forall_cons; [exact gate_exit1_refuses | apply List.Forall_nil].
Qed.

(** THE RESIDUE: every gate refuses, so the input falls through to the
    final program, which has no gate of its own. *)
Lemma slice_residue_inhabited : slice_rest gates_refuse_all gated_demo_fin.
Proof.
  unfold gates_refuse_all, slice_rest.
  apply List.Forall_cons; [exact gate_exit1_refuses |].
  apply List.Forall_cons; [exact gate_exit1_refuses | apply List.Forall_nil].
Qed.

(* =========================================================================
   PART 3 — disjointness, applied
   ========================================================================= *)

(** The trusted disjointness lemmas, used the way a consumer uses them:
    a concrete slice fact goes in and a refutation of a competing slice
    comes out.  Here [GatedSize.slices_disjoint_accept_accept] turns
    "this input is in the second slice of [gates_accept_second]" into
    "it is not in the first", with no further computation on the
    binaries — the leading gate's refusal is already recorded in the
    slice fact. *)
Lemma slice_first_of_accept_second_refuted :
  ~ slice_accept [] exit1_image gated_demo_fin.
Proof.
  intros Hfirst.
  apply (slices_disjoint_accept_accept [] exit1_image [exit1_image] exit0_image
           gated_demo_fin); [| exact Hfirst | exact slice_second_inhabited].
  left. reflexivity.
Qed.

(** ... and [GatedSize.slices_disjoint_accept_rest] empties the residue
    of [gates_accept_first] at this input: an input the leading gate
    accepts never reaches the final program. *)
Lemma residue_of_accept_first_refuted :
  ~ slice_rest gates_accept_first gated_demo_fin.
Proof.
  intros Hrest.
  apply (slices_disjoint_accept_rest [] exit0_image gates_accept_first
           gated_demo_fin); [| exact slice_first_inhabited | exact Hrest].
  unfold gates_accept_first. left. reflexivity.
Qed.

(** The same in the other arrangement: the input is in the second slice
    of [gates_accept_second], so it is not in that list's residue
    either. *)
Lemma residue_of_accept_second_refuted :
  ~ slice_rest gates_accept_second gated_demo_fin.
Proof.
  intros Hrest.
  apply (slices_disjoint_accept_rest [exit1_image] exit0_image
           gates_accept_second gated_demo_fin);
    [| exact slice_second_inhabited | exact Hrest].
  unfold gates_accept_second. right. left. reflexivity.
Qed.

(* =========================================================================
   PART 4 — exhaustiveness, instantiated
   ========================================================================= *)

(** The per-gate decidability hypothesis [GatedSize.slices_exhaustive]
    asks for, discharged for these gates at this input from Part 1
    rather than assumed.  This is the point of stating excluded middle
    as a hypothesis: for a gate whose verdict is actually settled, the
    instance is a proof, and nothing classical enters the file. *)
Lemma gates_accept_first_decidable : forall G,
  In G gates_accept_first ->
  Classifier.accepts G gated_demo_fin \/ ~ Classifier.accepts G gated_demo_fin.
Proof.
  intros G Hin. destruct Hin as [Heq | [Heq | []]]; subst G.
  - left. exact gate_exit0_accepts.
  - right. exact gate_exit1_refuses.
Qed.

Lemma gates_refuse_all_decidable : forall G,
  In G gates_refuse_all ->
  Classifier.accepts G gated_demo_fin \/ ~ Classifier.accepts G gated_demo_fin.
Proof.
  intros G Hin. destruct Hin as [Heq | [Heq | []]]; subst G.
  - right. exact gate_exit1_refuses.
  - right. exact gate_exit1_refuses.
Qed.

(** Exhaustiveness landing in the LEFT disjunct, with the decomposition
    it hands back read off: the accepting gate is the head, its prefix
    is empty, and the slice is the one Part 2 exhibited. *)
Lemma gates_accept_first_exhaustive :
  (exists prev G suffix,
     gates_accept_first = prev ++ G :: suffix /\ slice_accept prev G gated_demo_fin)
  \/ slice_rest gates_accept_first gated_demo_fin.
Proof.
  apply slices_exhaustive. exact gates_accept_first_decidable.
Qed.

(** ... and landing in the RIGHT one: with every gate refusing, the
    input is in the residue and no decomposition exists.  Both halves
    are asserted, because the disjunction alone would be satisfied by
    the wrong side. *)
Lemma gates_refuse_all_exhaustive :
  ((exists prev G suffix,
      gates_refuse_all = prev ++ G :: suffix /\ slice_accept prev G gated_demo_fin)
   \/ slice_rest gates_refuse_all gated_demo_fin)
  /\ ~ (exists prev G suffix,
          gates_refuse_all = prev ++ G :: suffix
          /\ slice_accept prev G gated_demo_fin).
Proof.
  split.
  - apply slices_exhaustive. exact gates_refuse_all_decidable.
  - intros (prev & G & suffix & Heq & Hacc & _).
    assert (Hin : In G gates_refuse_all).
    { rewrite Heq. apply List.in_elt. }
    destruct Hin as [Hg | [Hg | []]]; subst G; exact (gate_exit1_refuses Hacc).
Qed.

(** The one-program case, which is where the whole family has to agree
    with the ungated measure: no gates, one part, and that part is the
    entire input space.  A submission that declares no gates is asked
    for exactly [Equivalence.strong_universal_T] restricted to the
    finite inputs, by [GatedSize.gated_slice_of_universal] at
    [P := slice_rest []]. *)
Lemma one_program_residue_is_everything : slice_rest [] gated_demo_fin.
Proof. apply slice_rest_nil. Qed.

Lemma one_program_obligation_is_the_baseline : forall Src A,
  strong_universal_T Src A -> gated_slice_T Src A (slice_rest []).
Proof. intros Src A H. exact (gated_slice_of_universal Src A _ H). Qed.

(** ... and the error-free twin, which is owed for the same reason: a
    task that keeps [Equivalence.strong_universal_error_free_T] rather
    than the baseline gets the one-program case back on the same terms,
    with no separate scheme and no weaker obligation. *)
Lemma one_program_error_free_obligation_is_the_baseline : forall Src A,
  strong_universal_error_free_T Src A ->
  gated_slice_error_free_T Src A (slice_rest []).
Proof.
  intros Src A H. exact (gated_slice_error_free_of_universal Src A _ H).
Qed.

(* =========================================================================
   PART 5 — the vacuity route, biting a concrete partition
   ========================================================================= *)

(** What an image that does not load does to a partition, shown against
    a gate that really works.  [Gbad] is quantified rather than
    exhibited, because the tree carries no concrete image for which
    [Run.valid_entry] is empty at a valid input — [Run.valid_sp] and
    [Run.valid_mmap_base] do not depend on the image, and
    [Equivalence.image_brk_satisfiable_entry] inhabits the rest for a
    well-formed one.  The hypothesis is exactly
    [Classifier.accepts_vacuous_no_entries]'s, and everything else here
    is concrete.

    First half: such an image ACCEPTS, so its slice is the whole residue
    left by the gates before it.  The direction is the one a reader gets
    backwards — "no valid entry" is not "accepts nothing". *)
Lemma vacuous_gate_swallows_the_residue : forall Gbad,
  (forall en, ~ valid_entry Gbad en (to_proc_input gated_demo_fin)) ->
  slice_accept [exit1_image] Gbad gated_demo_fin.
Proof.
  intros Gbad Hno.
  apply (proj2 (slice_accept_vacuous_no_entries [exit1_image] Gbad _ Hno)).
  apply List.Forall_cons; [exact gate_exit1_refuses | apply List.Forall_nil].
Qed.

(** Second half, and the one that costs a checker: the residue is now
    EMPTY at this input, even though [exit1_image] beside it genuinely
    refuses every input it is offered.  The final program is never asked
    about this input at all, and its [GatedSize.gated_slice_T]
    obligation holds with nothing established about its binary.

    The remedy is not in this layer: a consuming checker ascribes
    [Equivalence.IMAGE_WF] to every gate image it names, which is what
    [Measure]'s header already requires for the classifier image and
    [Equivalence]'s for the two compared ones. *)
Lemma vacuous_gate_empties_the_residue : forall Gbad,
  (forall en, ~ valid_entry Gbad en (to_proc_input gated_demo_fin)) ->
  ~ slice_rest [exit1_image; Gbad] gated_demo_fin.
Proof.
  intros Gbad Hno.
  apply (slice_rest_vacuous_no_entries [exit1_image; Gbad] Gbad gated_demo_fin);
    [| exact Hno].
  right. left. reflexivity.
Qed.

(* =========================================================================
   PART 6 — the weight bound, refuted concretely
   ========================================================================= *)

(** A second valid input, differing from the first only in its standard
    input.  [FinInput.valid_fin_input] says nothing about [fin_stdin]
    ([FinInput.valid_fin_input_stdin_irrelevant]), so it is valid for
    the same reason the first is; and standard input is part of the
    CORE, so the two cores differ, which is what
    [GatedSize.weight_bound_pred_refutable] asks for. *)
Definition gated_demo_fin_stdin : FinProcInput :=
  mkFinProcInput [[]] [] [] [Z_to_bv 8 65] demo_uid demo_gid demo_groups
                 net_silent default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48
                 [] [] true true.

Lemma gated_demo_fin_stdin_valid : valid_fin_input gated_demo_fin_stdin.
Proof.
  unfold valid_fin_input, to_proc_input, gated_demo_fin_stdin. cbn.
  exact demo_input_valid.
Qed.

Lemma gated_demo_cores_differ :
  fin_core gated_demo_fin <> fin_core gated_demo_fin_stdin.
Proof.
  unfold fin_core, gated_demo_fin, gated_demo_fin_stdin. cbn.
  intros H. inversion H.
Qed.

(** The exit-1 gate refuses the second input too, for the same reason
    and at the same entry: the program never reads standard input, so
    the fuel evaluator closes it unchanged. *)
Lemma gate_exit1_refuses_stdin :
  ~ Classifier.accepts exit1_image gated_demo_fin_stdin.
Proof.
  apply proj2 with (A := valid_fin_input gated_demo_fin_stdin).
  apply (rejects_by_exit1 _ _ demo_entry).
  - exact gated_demo_fin_stdin_valid.
  - apply demo_entry_valid_exit1. exact gated_demo_fin_stdin_valid.
  - cbn [must_exit_with exit1_image demo_entry]. unfold init_config.
    apply (exits_c_must_exit_at _ _ 8); [reflexivity | reflexivity |].
    vm_compute. reflexivity.
Qed.

(** Two valid inputs with distinct cores outside the predicate refute
    the unit bound.  So a [GatedSize.weight_bound_pred_T] claim is a
    real restriction on how much of the input space can sit outside a
    slice — not something every predicate and every distribution
    satisfies — and this is the concrete instance of that. *)
Lemma unit_bound_refuted_at_exit1_gate :
  ~ weight_bound_pred_T (Classifier.accepts exit1_image)
      (fun _ => 1%Q) 1%Q 1%Q.
Proof.
  apply (weight_bound_pred_refutable _ gated_demo_fin gated_demo_fin_stdin).
  - exact gated_demo_fin_valid.
  - exact gate_exit1_refuses.
  - exact gated_demo_fin_stdin_valid.
  - exact gate_exit1_refuses_stdin.
  - exact gated_demo_cores_differ.
Qed.

(** ... and the same refutation read back as a [Measure.weight_bound_T]
    one, through [GatedSize.weight_bound_pred_of_classifier].  This is
    the bridge working in the direction a consumer needs it: the two
    statements are the same statement at
    [P := Classifier.accepts C], so a refutation of either is a
    refutation of both, and the gated measure does not weaken the bound
    the ungated one asked for. *)
Lemma unit_bound_refuted_as_classifier_bound :
  ~ weight_bound_T exit1_image (fun _ => 1%Q) 1%Q 1%Q.
Proof.
  intros Hbound.
  exact (unit_bound_refuted_at_exit1_gate
           (proj1 (weight_bound_pred_of_classifier _ _ _ _) Hbound)).
Qed.

(** THE BOUND IS SATISFIABLE, and at the one-program slice it is
    satisfiable at [0].  Part 6's refutation on its own would leave open
    that [GatedSize.weight_bound_pred_T] is a predicate nothing meets,
    which would make the refutation free; this is the other half.

    The instance is the one-program case again, and the number is not a
    vacuity: [GatedSize.slice_rest []] is the WHOLE input space
    ([one_program_residue_is_everything]), so its complement is empty,
    so no admissible list exists to weigh and the bound is [0] rather
    than merely small.  Reading that as evidence about a binary would be
    the mistake — it is evidence about the PARTITION, and it is exactly
    what a consumer needs when it charges unproven mass at the dearest
    slice: with one program there is no unproven mass.

    It holds for EVERY weight and every declared total, because the
    proof never looks at either.  The list is empty by
    [GatedSize.slice_rest_nil], and an empty sum is [0]. *)
Lemma one_program_bound_pred_at_zero : forall (w : FinProcInput -> Q) (M : Q),
  weight_bound_pred_T (slice_rest []) w M 0%Q.
Proof.
  intros w M l Hnd Hall.
  destruct l as [| f l].
  - cbn [sum_weights fold_right]. rewrite Qmult_0_l. apply Qle_refl.
  - exfalso. destruct (Hall f (or_introl eq_refl)) as [_ Hout].
    exact (Hout (slice_rest_nil f)).
Qed.

(** The same bound at any multiplier a task might declare, through
    [GatedSize.weight_bound_pred_mono] — the trusted monotonicity lemma
    applied rather than restated.  [0 <= M] is the hypothesis that lemma
    needs and cannot get from anywhere else, for the reason [Measure]'s
    header gives: [M] is declared, not summed, so nothing forces it to
    agree in sign with the weights it is the total of. *)
Lemma one_program_bound_pred_at_any : forall (w : FinProcInput -> Q) (M b : Q),
  (0 <= M)%Q -> (0 <= b)%Q -> weight_bound_pred_T (slice_rest []) w M b.
Proof.
  intros w M b HM Hb.
  apply (weight_bound_pred_mono _ w M 0%Q b HM Hb).
  apply one_program_bound_pred_at_zero.
Qed.

(* =========================================================================
   PART 7 — both per-slice obligations refuted on a concrete image pair
   ========================================================================= *)

(** [GatedSize.gated_slice_refuted] and its error-free twin, applied.
    The image is [Checks.Examples.undecodable_image] run against itself:
    its first instruction fetch leaves the modeled surface, at the
    ASLR-valid [Checks.Examples.demo_entry] and at
    [State.source_alloc_limit] — which is the budget both slice
    obligations seed the SOURCE run with, and the reason
    [Checks.Examples.run_of_undecodable_image_is_unmodeled_at_demo_entry]
    is stated at that budget rather than at
    [Cases.Prelude.demo_limit].

    The predicate is [GatedSize.slice_rest []], the whole input space, so
    the refutation is at the widest slice.  By
    [GatedSize.gated_slice_mono] a refutation there does NOT carry to a
    narrower one — monotonicity runs the other way — which is why the
    input is exhibited rather than left abstract: it is [gated_demo_fin]
    that must be in the slice, and it is.

    Refuting the baseline shape goes through the [Equivalence.modeled]
    conjunct, which is the one the error-free shape does not have. *)
Lemma undecodable_refutes_the_slice :
  ~ gated_slice_T undecodable_image undecodable_image (slice_rest []).
Proof.
  apply (gated_slice_refuted _ _ _ gated_demo_fin demo_entry demo_entry).
  - exact gated_demo_fin_valid.
  - apply slice_rest_nil.
  - apply demo_entry_valid_undecodable. exact gated_demo_fin_valid.
  - apply demo_entry_valid_undecodable. exact gated_demo_fin_valid.
  - intros [Hmodeled _]. apply Hmodeled.
    rewrite gated_demo_to_proc_input.
    exact run_of_undecodable_image_is_unmodeled_at_demo_entry.
Qed.

(** ... and the error-free shape, refuted at the same triple by the same
    fetch.  The route differs, and the difference is the point: there is
    no [Equivalence.modeled] conjunct to fail, so the refutation goes
    through SOURCE ERROR-FREEDOM instead, via
    [Equivalence.run_unmodeled_errors] — leaving the modeled surface is
    a special case of erroring, and the error-free shape forbids
    erroring outright.  This is the concrete witness that
    [GatedSize.gated_slice_error_free_T] is a real obligation and not
    merely a second name for the first. *)
Lemma undecodable_refutes_the_error_free_slice :
  ~ gated_slice_error_free_T undecodable_image undecodable_image (slice_rest []).
Proof.
  apply (gated_slice_error_free_refuted _ _ _ gated_demo_fin demo_entry demo_entry).
  - exact gated_demo_fin_valid.
  - apply slice_rest_nil.
  - apply demo_entry_valid_undecodable. exact gated_demo_fin_valid.
  - apply demo_entry_valid_undecodable. exact gated_demo_fin_valid.
  - intros ((Hsrc & _) & _ & _). apply Hsrc, run_unmodeled_errors.
    rewrite gated_demo_to_proc_input.
    exact run_of_undecodable_image_is_unmodeled_at_demo_entry.
Qed.

(* =========================================================================
   PART 8 — the same partition and the same obligations, under a
   spurious-failure configuration
   ========================================================================= *)

(** [EquivalenceDefinition.GatedSize]'s configuration section states two
    things that pull in opposite directions, and this part runs both on
    the concrete images so a reader can see they really do:

    - the GATES are read under [Run.forced_only_cfg] whatever the task
      chose ([Classifier.accepts_fo]), so Part 1's two verdicts are
      re-established at the pinned reading rather than carried over.
      Carrying them over is not impossible — [Classifier.accepts_fo_of_accepts]
      does it given [Classifier.classifier_decided] — but that premise
      has no proof for these images either, so re-proving is the shorter
      route rather than the only one;
    - the PROGRAMS are judged under the task's [cfg], so Part 7's
      refutations have to hold at EVERY [cfg] rather than at one.

    Both work out here, and for different reasons.  The verdicts survive
    the pin because these two binaries make no syscall but [exit], which
    belongs to no family ([Checks.SpuriousCfg.exit_has_no_family]), so no
    filter touches either run.  The refutations survive every
    configuration because the undecodable image leaves the modeled
    surface on its FIRST FETCH, which is an instruction step, and the
    filter touches no instruction step. *)

(** The accepting verdict at the pinned reading, at every entry.
    [Checks.SpuriousCfg.exits_c_must_exit_at_cfg] is the evaluator, and
    it is the same [Checks.Examples.exits_c] over [Run.sstep_cfg]. *)
Lemma gate_exit0_accepts_fo : Classifier.accepts_fo exit0_image gated_demo_fin.
Proof.
  intros en _.
  destruct en as [sp brk0 mbase rnd].
  cbn [must_exit_with_scfg exit0_image]. unfold init_config.
  apply (exits_c_must_exit_at_cfg _ _ _ 8); [reflexivity | reflexivity |].
  vm_compute. reflexivity.
Qed.

(** ... and the refusal, from ONE valid entry, through
    [Classifier.rejects_fo_by_exit1]. *)
Lemma gate_exit1_rejects_fo : Classifier.rejects_fo exit1_image gated_demo_fin.
Proof.
  apply (rejects_fo_by_exit1 _ _ demo_entry).
  - exact gated_demo_fin_valid.
  - apply demo_entry_valid_exit1. rewrite gated_demo_to_proc_input.
    exact demo_input_valid.
  - cbn [must_exit_with_scfg exit1_image demo_entry]. unfold init_config.
    apply (exits_c_must_exit_at_cfg _ _ _ 8); [reflexivity | reflexivity |].
    vm_compute. reflexivity.
Qed.

Lemma gate_exit1_refuses_fo : ~ Classifier.accepts_fo exit1_image gated_demo_fin.
Proof. exact (proj2 gate_exit1_rejects_fo). Qed.

(** The three slice shapes, inhabited at the pinned reading, by the same
    three arrangements of the same two gates. *)
Lemma slice_first_inhabited_fo : slice_accept_fo [] exit0_image gated_demo_fin.
Proof.
  split; [exact gate_exit0_accepts_fo | apply List.Forall_nil].
Qed.

Lemma slice_second_inhabited_fo :
  slice_accept_fo [exit1_image] exit0_image gated_demo_fin.
Proof.
  split; [exact gate_exit0_accepts_fo |].
  apply List.Forall_cons; [exact gate_exit1_refuses_fo | apply List.Forall_nil].
Qed.

Lemma slice_residue_inhabited_fo : slice_rest_fo gates_refuse_all gated_demo_fin.
Proof.
  unfold gates_refuse_all, slice_rest_fo.
  apply List.Forall_cons; [exact gate_exit1_refuses_fo |].
  apply List.Forall_cons; [exact gate_exit1_refuses_fo | apply List.Forall_nil].
Qed.

(** Disjointness applied at the pinned reading, the way a consumer uses
    it: a concrete slice fact goes in and a refutation of a competing
    slice comes out. *)
Lemma residue_of_accept_first_refuted_fo :
  ~ slice_rest_fo gates_accept_first gated_demo_fin.
Proof.
  intros Hrest.
  apply (slices_disjoint_accept_rest_fo [] exit0_image gates_accept_first
           gated_demo_fin); [| exact slice_first_inhabited_fo | exact Hrest].
  unfold gates_accept_first. left. reflexivity.
Qed.

(** Exhaustiveness at the pinned reading, with the per-gate hypothesis
    discharged from the two verdicts above rather than assumed — the
    same point Part 4 makes, and the reason excluded middle stays a
    hypothesis rather than becoming an axiom of the file. *)
Lemma gates_accept_first_decidable_fo : forall G,
  In G gates_accept_first ->
  Classifier.accepts_fo G gated_demo_fin \/ ~ Classifier.accepts_fo G gated_demo_fin.
Proof.
  intros G Hin. destruct Hin as [Heq | [Heq | []]]; subst G.
  - left. exact gate_exit0_accepts_fo.
  - right. exact gate_exit1_refuses_fo.
Qed.

Lemma gates_accept_first_exhaustive_fo :
  (exists prev G suffix,
     gates_accept_first = prev ++ G :: suffix
     /\ slice_accept_fo prev G gated_demo_fin)
  \/ slice_rest_fo gates_accept_first gated_demo_fin.
Proof.
  apply slices_exhaustive_fo. exact gates_accept_first_decidable_fo.
Qed.

(** THE VACUITY ROUTE IS NOT CLOSED BY THE PIN, which is the half of
    Part 5 a reader might hope the configuration layer repaired.  A gate
    image with no valid entry still ACCEPTS every input under
    [Run.forced_only_cfg] — the route runs through the entry quantifier,
    which no configuration touches — so it still swallows the residue
    the earlier gates left. *)
Lemma vacuous_gate_swallows_the_residue_fo : forall Gbad,
  (forall en, ~ valid_entry Gbad en (to_proc_input gated_demo_fin)) ->
  slice_accept_fo [exit1_image] Gbad gated_demo_fin.
Proof.
  intros Gbad Hno.
  apply (proj2 (slice_accept_fo_vacuous_no_entries [exit1_image] Gbad _ Hno)).
  apply List.Forall_cons; [exact gate_exit1_refuses_fo | apply List.Forall_nil].
Qed.

(** The one-program case under a configuration: a submission that
    declares no gates is asked for exactly
    [Equivalence.strong_universal_T_scfg] at its own configuration,
    restricted to the finite inputs.  The port of
    [one_program_obligation_is_the_baseline], and the [cfg] is shared
    between hypothesis and conclusion because there is no lemma taking
    one configuration to another. *)
Lemma one_program_residue_is_everything_fo : slice_rest_fo [] gated_demo_fin.
Proof. apply slice_rest_fo_nil. Qed.

Lemma one_program_obligation_is_the_baseline_scfg : forall cfg Src A,
  strong_universal_T_scfg cfg Src A -> gated_slice_T_scfg cfg Src A (slice_rest_fo []).
Proof. intros cfg Src A H. exact (gated_slice_T_scfg_of_universal cfg Src A _ H). Qed.

Lemma one_program_error_free_obligation_is_the_baseline_scfg : forall cfg Src A,
  strong_universal_error_free_T_scfg cfg Src A ->
  gated_slice_error_free_T_scfg cfg Src A (slice_rest_fo []).
Proof.
  intros cfg Src A H. exact (gated_slice_error_free_T_scfg_of_universal cfg Src A _ H).
Qed.

(** The undecodable image is uncovered under EVERY configuration at this
    entry and this input.  Turning a family off removes executions and
    carries nothing down for free, so this cannot be inherited from
    [Checks.Examples.run_of_undecodable_image_is_unmodeled_at_demo_entry]
    — but it does not need to be: the fetch that leaves the modeled
    surface is the FIRST step, an instruction step, and no filter
    touches an instruction step.  The witness is the empty
    [Run.star_cfg], which exists at every [cfg]. *)
Lemma undecodable_unmodeled_scfg_at_demo_entry : forall cfg,
  bh_unmodeled (run_scfg cfg undecodable_image source_alloc_limit demo_entry
                  (to_proc_input gated_demo_fin)).
Proof.
  intros cfg.
  rewrite gated_demo_to_proc_input.
  cbn [run_scfg bh_unmodeled undecodable_image demo_entry]. unfold init_config.
  match goal with
  | |- reaches_unmodeled_cfg _ _ ?c => exists [], c
  end.
  split; [apply star_cfg_refl |].
  split; [reflexivity |]. left. split; [reflexivity |].
  cbn [cfg_ms cfg_model].
  match goal with
  | |- mi_account_step ?segs ?ms ?model = _ =>
      rewrite (mi_account_step_no_lazy segs ms model ltac:(reflexivity))
  end.
  cbn [mkProcInput in_argv in_envp in_uid in_hwcap].
  rewrite undecodable_step_unmodeled_at_demo_entry. reflexivity.
Qed.

(** Part 7's two refutations, now at every configuration.  The baseline
    shape fails through the [Equivalence.modeled] conjunct and the
    error-free shape through source error-freedom, which is the same
    split the unparameterized pair makes and for the same reason: the
    error-free shape has no [Equivalence.modeled] conjunct to fail.

    Quantified over [cfg] rather than stated at one, which is what says
    the configured obligation is a real claim wherever a task lands
    rather than only under may-fail. *)
Lemma undecodable_refutes_the_slice_scfg : forall cfg,
  ~ gated_slice_T_scfg cfg undecodable_image undecodable_image (slice_rest_fo []).
Proof.
  intros cfg.
  apply (gated_slice_T_scfg_refuted _ _ _ _ gated_demo_fin demo_entry demo_entry).
  - exact gated_demo_fin_valid.
  - apply slice_rest_fo_nil.
  - apply demo_entry_valid_undecodable. exact gated_demo_fin_valid.
  - apply demo_entry_valid_undecodable. exact gated_demo_fin_valid.
  - intros [Hmodeled _]. apply Hmodeled.
    exact (undecodable_unmodeled_scfg_at_demo_entry cfg).
Qed.

Lemma undecodable_refutes_the_error_free_slice_scfg : forall cfg,
  ~ gated_slice_error_free_T_scfg cfg undecodable_image undecodable_image
      (slice_rest_fo []).
Proof.
  intros cfg.
  apply (gated_slice_error_free_T_scfg_refuted _ _ _ _ gated_demo_fin
           demo_entry demo_entry).
  - exact gated_demo_fin_valid.
  - apply slice_rest_fo_nil.
  - apply demo_entry_valid_undecodable. exact gated_demo_fin_valid.
  - apply demo_entry_valid_undecodable. exact gated_demo_fin_valid.
  - intros ((Hsrc & _) & _ & _). apply Hsrc, run_scfg_unmodeled_errors.
    exact (undecodable_unmodeled_scfg_at_demo_entry cfg).
Qed.
