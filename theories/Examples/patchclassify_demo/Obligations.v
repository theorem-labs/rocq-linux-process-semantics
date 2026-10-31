(** * Examples.patchclassify_demo.Obligations — the five obligations
      [PatchClassifySpec.SPEC_PATCH_CLASSIFY] asks for

    DEMO FILE (not part of the trusted specification).  [Images] built
    the six images, [Verdicts] proved what each one does at every valid
    entry on every input, [Traces] proved what each one EMITS, and
    [Distribution] declared a weight.  This file is the payoff: the five
    [Parameter]s of
    [EquivalenceDefinition.PatchClassifySpec.SPEC_PATCH_CLASSIFY], proved
    of those six images and that distribution, so that the surface has a
    satisfying instance.

    ** The five, and where each one's content is

    - [P1_P2_strong_universal]: the two patched binaries are observably
      equivalent.  All of its content is [Traces]': the two trace sets
      are the same two-element set, and equality of the sets is the
      whole of [Equivalence.equiv]'s non-escape branch.  Note that the
      two images being byte-identical does NOT make it trivial —
      [Equivalence.strong_universal_T] quantifies the two
      [Run.ExecEntry] records INDEPENDENTLY and runs the two sides at
      DIFFERENT allocation budgets, so a program whose observable
      behavior depended on the stack placement, the break, the mmap base
      or the budget would fail this theorem against itself.  What makes
      it come out is that these programs depend on none of them, which
      is [Verdicts]' indifference lemma, and it had to be proved.
    - [C1_classifies_patch_diff]: the patch-difference classifier fires
      everywhere, correctly.  Its spec is FALSE on every input, because
      [O1] exits 1 and [P1] exits 0, so the classifier is right to fire;
      the iff is then two refutations and the totality disjunct is the
      verdict from [Verdicts].
    - [C2_classifies_good_inputs]: the same shape over the other
      question.  Both originals here are ERROR-FREE, so the refutation
      cannot go through [Equivalence.strong_equiv_error_free]'s two
      error clauses and goes through the trace clause instead — the two
      originals disagree on every input.
    - [C1_weight_bound] and [C2_weight_bound], both at [b = 1]: see
      [Distribution].  The fire set is the whole input space, so the
      whole-space certificate is what discharges them.  That the
      multiplier is not free is a separate claim and is proved
      separately, at the end of this file: it cannot be dropped to [0]
      and it cannot be halved.  It is NOT proved that [1] is the least
      provable multiplier — see [demo_b_half_refutable] for why that is
      a different statement.

    ** What is deliberately degenerate, said out loud

    Both classifiers fire on EVERY valid finite input, and both bounds
    are the trivial multiplier.  That is not a shortcut taken to make
    the proofs go through — it is the CORRECT answer for this pair of
    originals, and the honest bound for a fire set that really is
    everything.  The demo's README names the refinement that would make
    the numbers interesting (a program that reads its input, whose
    classifier fires on a cylinder rather than on the whole space, with
    [b < 1] from a cylinder bound), and why it is a separate exercise.

    What the degeneracy must not be allowed to become is vacuity, and
    the two are easy to confuse.  A classifier image with no valid entry
    would satisfy both classifier obligations
    ([Classifier.decides_vacuous_no_entries]) and both weight bounds at
    every multiplier including zero
    ([Classifier.accepts_vacuous_no_entries]) with nothing established.
    The bites at the end of this file are what separate the demo from
    that: the classifier images have valid entries, exhibited; their
    reject sets contain named inputs; and a distribution that charged a
    unit per input would REFUSE the bound proved here.

    ** [Classifier.agree] on the second pair is a bonus, not an
       obligation

    [Classifier.classifies_patch_diff_T]'s spec is the CONJUNCTION
    [agree O1 P1 ... /\ agree O2 P2 ...], and the first conjunct is false
    everywhere, so the conjunction is false everywhere whatever the
    second one says.  [O2_P2_agree] below proves the second one anyway,
    because a reader checking that the classifier's verdict is CORRECT
    rather than merely consistent wants to see that the demo did not
    quietly rely on both pairs differing.  It is stated as what it is. *)

From Stdlib Require Import ZArith NArith List QArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit FinInput Classifier Measure MeasureLib.
From LinuxProcessSemantics.Examples.patchclassify_demo Require Import
  Images Verdicts Traces Distribution.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   Valid entries: the premise every obligation quantifies over is
   INHABITED, per image
   ========================================================================= *)

(** Every statement below ranges over valid [Run.ExecEntry]s, and an
    image with none satisfies all of them saying nothing — the vacuity
    route [Classifier]'s and [PatchClassifySpec]'s headers both name.
    [Equivalence.image_brk_satisfiable_entry] turns [Images]' six
    [Equivalence.image_brk_satisfiable] checks into the witnesses, one
    line each.

    THE INPUT IS A PARAMETER, and must be: [Run.valid_entry] asks that
    the entry stack image fit below the top of the address space
    ([Run.entry_stack_fits]), and that image is built from the input's
    argv and envp.  Its fifth conjunct
    ([Run.entry_launch_ok_va]) reads even more of the input — the
    kernel build, the exec file name and the two string lists together
    decide where [execve] may put the stack top, [sp] and the mmap
    base, since [create_elf_tables] (fs/binfmt_elf.c, Linux v6.18.46,
    commit 1f99e9ab748f) lays the block from exactly those.  So an
    entry is valid FOR AN INPUT, and inhabitation
    is a statement about one — with [Run.valid_input] as the premise,
    since it is [Run.valid_argv] and [Run.valid_envp] that cap the span
    at [Run.entry_stack_span_max] and leave the bottom of the sp window
    room for it, and [Run.valid_launch] (its thirteenth conjunct) that
    caps the whole block at the E2BIG limit so that a stack pointer
    exists at all.  An input outside those caps has no valid entry at
    all,
    and every statement below that quantifies an entry carries the
    validity premise for exactly that reason.

    These are not decoration: two of the proofs below REFUTE a universal
    over valid entries ([Classifier.agree]'s trace conjunct, and
    [Classifier.good_input]), which cannot be done without exhibiting an
    entry at which to refute it. *)

Lemma O1_valid_entry_exists : forall inp,
  valid_input inp -> exists en, valid_entry O1_image en inp.
Proof. intros inp H. apply image_brk_satisfiable_entry;
  [exact H | exact O1_brk_satisfiable]. Qed.

Lemma O2_valid_entry_exists : forall inp,
  valid_input inp -> exists en, valid_entry O2_image en inp.
Proof. intros inp H. apply image_brk_satisfiable_entry;
  [exact H | exact O2_brk_satisfiable]. Qed.

Lemma P1_valid_entry_exists : forall inp,
  valid_input inp -> exists en, valid_entry P1_image en inp.
Proof. intros inp H. apply image_brk_satisfiable_entry;
  [exact H | exact P1_brk_satisfiable]. Qed.

Lemma P2_valid_entry_exists : forall inp,
  valid_input inp -> exists en, valid_entry P2_image en inp.
Proof. intros inp H. apply image_brk_satisfiable_entry;
  [exact H | exact P2_brk_satisfiable]. Qed.

Lemma C1_valid_entry_exists : forall inp,
  valid_input inp -> exists en, valid_entry C1_image en inp.
Proof. intros inp H. apply image_brk_satisfiable_entry;
  [exact H | exact C1_brk_satisfiable]. Qed.

Lemma C2_valid_entry_exists : forall inp,
  valid_input inp -> exists en, valid_entry C2_image en inp.
Proof. intros inp H. apply image_brk_satisfiable_entry;
  [exact H | exact C2_brk_satisfiable]. Qed.

(** The trap that makes the six lemmas above worth writing rather than
    copying an entry from the QA file: [Checks.Examples.demo_entry] is
    NOT a valid entry for these images.  Its program break is 0x1000,
    which is below the demo's page-rounded image top — the demo's
    segments reach 0x11150, where the [Checks] fixture's reach 0x10c.
    Copying it would have produced an unsatisfiable premise and a
    refutation that refuted nothing.

    IT IS STILL THE BREAK THAT FAILS, and that is worth checking rather
    than assuming, because [Checks.Examples.demo_entry] moved: it is
    now [demo_entry_of demo_proc_input], the launch entry
    [Run.launch_entry_va] builds, since no CLOSED entry can satisfy
    [Run.valid_entry]'s fifth conjunct — [Run.valid_launch_sp] places
    [sp] from the input's own argv, envp and exec file name
    ([create_elf_tables], fs/binfmt_elf.c, Linux v6.18.46, commit
    1f99e9ab748f).  That move changed the stack pointer, the mmap base
    and the draw; it left [Run.en_brk] at 0x1000, which is the field
    this refutation reads.  The fifth conjunct cannot rescue the entry
    either: it says nothing about the break, so the SECOND conjunct
    [Run.valid_brk] fails at every input exactly as before, and the
    statement stays a universal over inputs rather than one pinned to
    [Checks.Examples.demo_proc_input]. *)
Example demo_entry_is_not_valid_here : forall inp,
  ~ valid_entry O1_image demo_entry inp.
Proof.
  intros inp (_ & Hbrk & _). destruct Hbrk as (Hlo & _).
  vm_compute in Hlo. apply Hlo. reflexivity.
Qed.

(* =========================================================================
   The verdicts bite on the four images [Verdicts] left out
   ========================================================================= *)

(** [Verdicts] refutes the wrong code for [O1] and [P1], the pair the
    patch-difference classifier is asked about.  The same refutation is
    what [Classifier.decides] needs of the CLASSIFIER images — "does not
    exit 0" is half of "the verdict is 1" — and the remaining two
    originals get it for symmetry.

    Each is stated from the verdict of its OWN image rather than
    borrowed from a sibling that happens to share a segment list.
    Conversion would allow the borrowing ([Images]' header says so
    plainly); the discipline is what keeps these four honest if the two
    classifiers are ever given different code. *)

Theorem O2_does_not_exit_one : forall lim en inp,
  ~ must_exit_with verdict_reject O2_image lim en inp.
Proof.
  intros lim en inp H.
  apply verdict_accept_neq_reject.
  exact (must_exit_with_exclusive _ _ _ _ _ _ (O2_must_exit_zero lim en inp) H).
Qed.

Theorem P2_does_not_exit_one : forall lim en inp,
  ~ must_exit_with verdict_reject P2_image lim en inp.
Proof.
  intros lim en inp H.
  apply verdict_accept_neq_reject.
  exact (must_exit_with_exclusive _ _ _ _ _ _ (P2_must_exit_zero lim en inp) H).
Qed.

Theorem C1_does_not_exit_zero : forall lim en inp,
  ~ must_exit_with verdict_accept C1_image lim en inp.
Proof.
  intros lim en inp H.
  apply verdict_accept_neq_reject.
  exact (must_exit_with_exclusive _ _ _ _ _ _ H (C1_must_exit_one lim en inp)).
Qed.

Theorem C2_does_not_exit_zero : forall lim en inp,
  ~ must_exit_with verdict_accept C2_image lim en inp.
Proof.
  intros lim en inp H.
  apply verdict_accept_neq_reject.
  exact (must_exit_with_exclusive _ _ _ _ _ _ H (C2_must_exit_one lim en inp)).
Qed.

(* =========================================================================
   OBLIGATION 1: the two patches are observably equivalent
   ========================================================================= *)

(** The error-free flavor, which is what actually falls out here: both
    patches are error-free ([Verdicts]) and their trace sets are the
    same two-element set ([Traces]).  [Equivalence.strong_equiv_error_free]
    is exactly those three conjuncts.

    Proved first because it is the STRONGER statement and it is free:
    the demo's programs cannot error, so nothing is being claimed that
    the images do not support.  The baseline obligation the SPEC asks
    for is derived from it below, by the library's own implication. *)
Theorem P1_P2_strong_universal_error_free :
  strong_universal_error_free_T P1_image P2_image.
Proof.
  intros en_source en_target inp _ _ _.
  unfold strong_equiv_error_free, error_free.
  split; [| split].
  - exact (P1_error_free _ _ _).
  - exact (P2_error_free _ _ _).
  - intros tr. split; intros Ht.
    + apply (proj2 (P2_traces _ _ _ _)). exact (proj1 (P1_traces _ _ _ _) Ht).
    + apply (proj2 (P1_traces _ _ _ _)). exact (proj1 (P2_traces _ _ _ _) Ht).
Qed.

(** THE OBLIGATION, as [PatchClassifySpec.SPEC_PATCH_CLASSIFY] declares
    it.  [Equivalence.strong_universal_error_free_implies] is the step,
    and it is the reason the stronger flavor is safe to prove first —
    the baseline check never rejects a pair the error-free proof
    accepts. *)
Theorem P1_P2_strong_universal : strong_universal_T P1_image P2_image.
Proof.
  exact (strong_universal_error_free_implies _ _
           P1_P2_strong_universal_error_free).
Qed.

(* =========================================================================
   What the patch-difference classifier is asked about
   ========================================================================= *)

(** The first pair NEVER agrees.  [O1] exits 1 and [P1] exits 0, so the
    exit-1 event is a trace of the original and not a trace of the
    patch, at the one pair of valid entries the refutation names — and
    [Classifier.agree]'s trace conjunct is universal over entry pairs,
    so one pair is enough to refute it.

    The trace conjunct is the ONLY available route, and that is a fact
    rather than a preference: [Verdicts]' error and modeled facts make
    conjuncts two, three and four of [Classifier.agree] HOLD for this
    pair, since neither program can error, all-error or leave the
    modeled surface at any entry.  A refutation that reached for an
    error mismatch would have nothing to reach for.

    Note what the input premise is and is not doing: these programs read
    nothing, so the pair disagrees on the CONTENT of every
    [State.ProcInput] whatever.  [Run.valid_input] is needed only to
    have an entry to disagree at — [Classifier.agree] is a universal
    over entries valid for the input, and an input whose argv or envp
    overruns [Run.entry_stack_span_max] has none, which would make
    [agree] hold with nothing in it.  The classifier obligation only
    needs the valid finite inputs, so nothing is lost. *)
Theorem O1_P1_never_agree : forall inp,
  valid_input inp -> ~ agree O1_image P1_image source_alloc_limit inp.
Proof.
  intros inp Hinp Hag.
  destruct (O1_valid_entry_exists inp Hinp) as (en1 & Hen1).
  destruct (P1_valid_entry_exists inp Hinp) as (en2 & Hen2).
  destruct Hag as (Htr & _).
  apply (P1_never_emits_exit_one source_alloc_limit en2 inp).
  apply (proj1 (Htr en1 en2 Hen1 Hen2 _)).
  exact (O1_emits_exactly_exit_one source_alloc_limit en1 inp).
Qed.

(** The second pair ALWAYS agrees — a bonus and not an obligation, per
    this file's header: the conjunction the classifier decides is
    already false on its first conjunct.  It is proved because a reader
    should be able to see that the classifier fires for the right
    reason.

    All four conjuncts are discharged, and three of them by the SAME
    facts that made the refutation above go through the trace conjunct:
    neither image can error, all-error or go unmodeled, so each of the
    three existential iffs holds with both sides empty. *)
Theorem O2_P2_agree : forall inp,
  agree O2_image P2_image target_alloc_limit inp.
Proof.
  intros inp. split; [| split; [| split]].
  - intros enX enY _ _ tr. split; intros Ht.
    + apply (proj2 (P2_traces _ _ _ _)). exact (proj1 (O2_traces _ _ _ _) Ht).
    + apply (proj2 (O2_traces _ _ _ _)). exact (proj1 (P2_traces _ _ _ _) Ht).
  - split; intros (en & _ & Hb); exfalso;
      [ exact (O2_error_free _ _ _ Hb) | exact (P2_error_free _ _ _ Hb) ].
  - split; intros (en & _ & Hb); exfalso;
      [ exact (O2_error_free _ _ _ (run_all_errors_errors _ _ _ _ Hb))
      | exact (P2_error_free _ _ _ (run_all_errors_errors _ _ _ _ Hb)) ].
  - split; intros (en & _ & Hb); exfalso;
      [ exact (O2_modeled _ _ _ Hb) | exact (P2_modeled _ _ _ Hb) ].
Qed.

(** ... so the classifier's spec is false everywhere, which is the
    sentence the obligation below consumes. *)
Corollary patch_diff_spec_false : forall inp,
  valid_input inp ->
  ~ (agree O1_image P1_image source_alloc_limit inp
     /\ agree O2_image P2_image target_alloc_limit inp).
Proof. intros inp Hinp (Hag & _). exact (O1_P1_never_agree inp Hinp Hag). Qed.

(* =========================================================================
   OBLIGATION 2: the patch-difference classifier
   ========================================================================= *)

(** [C1] decides, on every valid finite input at every valid entry,
    whether both patches preserved behavior — by answering "no"
    everywhere, which is correct everywhere.

    Both halves of [Classifier.decides] are here.  The IFF: exiting 0 is
    impossible ([C1_does_not_exit_zero]), and the spec is false
    ([patch_diff_spec_false]), so the two sides are both false and the
    equivalence holds — with each side refuted separately rather than
    one being inferred from the other, which is what makes this a
    correctness claim and not a tautology.  TOTALITY: the classifier
    exits 1, always, at every budget and every entry ([Verdicts]). *)
Theorem C1_classifies_patch_diff :
  classifies_patch_diff_T O1_image P1_image O2_image P2_image C1_image.
Proof.
  intros f Hf en Hen. split.
  - split.
    + intros H0. exfalso. exact (C1_does_not_exit_zero _ _ _ H0).
    + intros Hspec. exfalso. exact (patch_diff_spec_false _ Hf Hspec).
  - right. exact (C1_must_exit_one _ _ _).
Qed.

(** ** The same obligation with the classifier's AT_HWCAP word declared

    [Classifier.decides_fo_hwcap_splits] fired at a classifier that
    really decides something, which is what makes this a check and not a
    shape.  A vacuous instance would satisfy the split lemma too
    ([Classifier.decides_fo_vacuous_no_entries] gives one for free from
    an image with no valid entry) and would say nothing about whether
    declaring preserves a verdict.  [C1_image] answers at every valid
    entry on every valid input ([C1_classifies_patch_diff]), so the iff
    below is about an obligation with content.

    THE IFF IS UNCONDITIONAL at this image and this spec.  It is the
    claim a checker relies on: a task's two declared obligations are
    together exactly the undeclared one, so declaring narrows what the
    task must survive and loses nothing.

    WHAT THE INSTANCE BELOW ASSUMES, and it is not about the capability
    word.  [C1_classifies_patch_diff] is stated over
    [Classifier.decides], whose verdicts are [MustExit.must_exit_with];
    the declared obligations are over [Classifier.decides_fo], whose
    verdicts are pinned to [Run.forced_only_cfg].  The bridge between
    them ([Classifier.decides_fo_of_decides]) needs
    [Classifier.classifier_decided] — that the classifier's own run is
    decided under forced-only — and nothing in this demo establishes
    that for [C1_image]; it is a fact about the binary's runtime, not
    about its verdicts.  So the instance carries that premise by name
    rather than pretending to it.

    [C1_image] carries no vector probe, so under the premise it
    satisfies BOTH declarations rather than only one.  A classifier that
    DID probe would satisfy the V-less declaration and refute the other,
    and the undeclared obligation with it; that asymmetry is the reason
    the declaration exists and is pinned at the instruction level in
    [Checks.Cases.Hwcap]. *)

Definition C1_patch_diff_spec (inp : ProcInput) : Prop :=
  agree O1_image P1_image source_alloc_limit inp
  /\ agree O2_image P2_image target_alloc_limit inp.

Theorem C1_patch_diff_is_exactly_its_two_declarations :
  decides_fo C1_image C1_patch_diff_spec
  <-> (decides_fo_hwcap_rv64gc C1_image C1_patch_diff_spec
       /\ decides_fo_hwcap_rv64gcv C1_image C1_patch_diff_spec).
Proof. apply decides_fo_hwcap_splits. Qed.

Theorem C1_decides_patch_diff_under_each_declaration :
  classifier_decided C1_image ->
  decides_fo_hwcap_rv64gc C1_image C1_patch_diff_spec
  /\ decides_fo_hwcap_rv64gcv C1_image C1_patch_diff_spec.
Proof.
  intros Hdec.
  apply C1_patch_diff_is_exactly_its_two_declarations.
  exact (decides_fo_of_decides C1_image C1_patch_diff_spec Hdec
           C1_classifies_patch_diff).
Qed.

(** …and back, with no premise at all: the two declared obligations give
    the undeclared one at this image, so a checker that accepts two
    declared proofs has the statement that says nothing about the
    hart. *)
Theorem C1_declarations_recover_the_undeclared_obligation :
  decides_fo_hwcap_rv64gc C1_image C1_patch_diff_spec ->
  decides_fo_hwcap_rv64gcv C1_image C1_patch_diff_spec ->
  decides_fo C1_image C1_patch_diff_spec.
Proof.
  intros Hgc Hgcv.
  apply C1_patch_diff_is_exactly_its_two_declarations.
  exact (conj Hgc Hgcv).
Qed.

(* =========================================================================
   What the good-input classifier is asked about
   ========================================================================= *)

(** No input is good.  [Classifier.good_input] is
    [Equivalence.strong_equiv_error_free] at all entry pairs — error
    freedom of both originals AND equality of their trace sets — and the
    refutation goes through the trace clause, not through the error
    clauses.

    That is worth saying plainly, because the obvious guess is wrong.
    [O1] is the DEFECT of this exercise and it does not crash: it exits
    1, cleanly, on every input ([Verdicts.O1_error_free]).  So both
    originals satisfy the two error-freedom conjuncts, and what fails is
    that one of them reports failure where the other reports success —
    which is exactly the defect a good-input classifier is supposed to
    notice. *)
Theorem O1_O2_no_good_input : forall inp,
  valid_input inp -> ~ good_input O1_image O2_image inp.
Proof.
  intros inp Hinp Hg.
  destruct (O1_valid_entry_exists inp Hinp) as (en1 & Hen1).
  destruct (O2_valid_entry_exists inp Hinp) as (en2 & Hen2).
  destruct (Hg en1 en2 Hen1 Hen2) as (_ & _ & Htr).
  apply (O2_never_emits_exit_one target_alloc_limit en2 inp).
  apply (proj1 (Htr _)).
  exact (O1_emits_exactly_exit_one source_alloc_limit en1 inp).
Qed.

(* =========================================================================
   OBLIGATION 3: the good-input classifier
   ========================================================================= *)

(** [C2] decides whether the two originals were already error-free
    equivalent — by answering "no" everywhere, which is again correct
    everywhere.  Same shape as [C1_classifies_patch_diff], different
    question and a different refutation underneath it. *)
Theorem C2_classifies_good_inputs :
  classifies_good_inputs_T O1_image O2_image C2_image.
Proof.
  intros f Hf en Hen. split.
  - split.
    + intros H0. exfalso. exact (C2_does_not_exit_zero _ _ _ H0).
    + intros Hspec. exfalso. exact (O1_O2_no_good_input _ Hf Hspec).
  - right. exact (C2_must_exit_one _ _ _).
Qed.

(* =========================================================================
   OBLIGATIONS 4 and 5: the two weight bounds, at [b1 = b2 = 1]
   ========================================================================= *)

(** Both classifiers reject everything, so the set the bound measures is
    the whole input space.
    [Distribution.demo_whole_space_bound] is the whole-space certificate
    of [MeasureLib.stdin_geometric] with the arithmetic done; neither
    bound reads anything about the classifier it is stated for, which is
    the accurate way to prove a claim about a fire set that is
    everything — and it is also why proving the multiplier NECESSARY is
    separate work, done at the end of this file.

    The two are stated separately, one per classifier image, because
    [PatchClassifySpec.SPEC_PATCH_CLASSIFY] declares them separately —
    and because [C1] and [C2] share a segment list, so a single lemma
    "the bound holds for the classifier" would silently be doing the
    work of two. *)
Theorem C1_weight_bound : weight_bound_T C1_image DemoDist.w DemoDist.M 1.
Proof. exact (demo_whole_space_bound C1_image). Qed.

Theorem C2_weight_bound : weight_bound_T C2_image DemoDist.w DemoDist.M 1.
Proof. exact (demo_whole_space_bound C2_image). Qed.

(* =========================================================================
   The obligations bite
   ========================================================================= *)

(** A finite input over the distribution's fixed launch-time
    environment, with a chosen standard input.  Built through
    [MeasureLib.core_input] so that [MeasureLib.fin_core_core_input]
    reads its core back with no computation — the two records below
    differ in exactly the field the measure layer charges for. *)
Definition demo_input (s : list byte) : FinProcInput :=
  core_input (mkFinCore demo_argv demo_envp demo_fs s).

(** ... and it really is a valid finite input, whatever the standard
    input: [FinInput.valid_fin_input] constrains argv, envp, the file
    system, the two ids, the soft descriptor limit, the blocked signal
    mask, the published hart capabilities and the exec file name, and
    says nothing about
    [FinInput.fin_stdin].  All eight come from [MeasureLib.core_input],
    which puts zero in the descriptor limit and the mask — inside
    [Run.valid_nofile]'s ceiling, and the empty mask
    [Run.valid_sigmask] asks for — [StackLayout.hwcap_rv64gc] in the
    hwcap, because [Run.valid_hwcap] admits two words and a zero is
    neither, and [State.default_execfn] in the name.  Without this the
    reject-set bites below would be about
    records the obligations never quantify over.

    The last three conjuncts get the guarded arms
    [Checks.Examples.demo_input_valid] writes and for the reasons argued
    there: [Run.valid_nofile] is a [Z.le], which [intros []] would strip
    to a bare [False], so it is decided as a boolean through
    [Z.leb_le]; and [Run.valid_sigmask] is an equality of BITVECTORS,
    whose well-formedness proofs [vm_compute] leaves built differently,
    so [bv_eq] has to reduce it to the underlying integers before
    [reflexivity] can close it.  [Run.valid_hwcap] needs an arm of its
    own for a third reason: it is a DISJUNCTION, and neither
    [reflexivity] nor [lia] picks a side.

    [Fs.fs_image_real], the FIFTH conjunct, needs no arm of its own:
    [demo_fs] is the empty image, with no key to be non-canonical and
    no key under another, so the boolean computes to [true] and the
    [reflexivity] at the end of the chain closes it.

    [Run.valid_launch], the THIRTEENTH conjunct, needs three arms for a
    fourth reason: [repeat split] may or may not have taken it apart
    already, so each half is also written on its own.  Its first half
    is about [State.in_execfn], which
    [MeasureLib.core_input] fills with [State.default_execfn], the
    one-byte relative path "a" — a name [getname_flags] (fs/namei.c,
    Linux v6.18.46, commit 1f99e9ab748f) can return, so
    [Run.valid_path_name]'s side of the disjunction is the one to take,
    and the no-NUL half needs [bv_unsigned] before [discriminate] for
    the reason the [valid_sigmask] arm needs [bv_eq].  Its second half
    is the E2BIG cap [bprm_stack_limits] (fs/exec.c) computes, and this
    demo's one empty argument, empty environment and one-byte name are
    far under it. *)
Lemma demo_input_is_valid : forall s, valid_fin_input (demo_input s).
Proof.
  intros s.
  unfold valid_fin_input, valid_input, valid_argv, valid_envp, valid_creds,
    valid_id, demo_input, core_input, to_proc_input, demo_argv, demo_envp,
    demo_fs.
  cbn [mkProcInput in_argv in_envp in_fs in_uid in_gid in_nofile in_sigmask
       in_hwcap in_execfn
       fin_argv fin_envp fin_image_fs fin_uid fin_gid fin_nofile fin_sigmask
       fin_hwcap fin_execfn total_arg_bytes length].
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try (unfold valid_hwcap; left;
         first [ reflexivity | apply bv_eq; vm_compute; reflexivity ]);
    try (unfold valid_launch; split;
         [ unfold valid_execfn, valid_path_name; left; split;
           [ vm_compute; lia
           | intros [Hz | []]; apply (f_equal bv_unsigned) in Hz;
             vm_compute in Hz; discriminate ]
         | unfold e2big_limit; apply Z.leb_le; vm_compute; reflexivity ]);
    try (unfold valid_execfn, valid_path_name; left; split;
         [ vm_compute; lia
         | intros [Hz | []]; apply (f_equal bv_unsigned) in Hz;
           vm_compute in Hz; discriminate ]);
    try (unfold e2big_limit; apply Z.leb_le; vm_compute; reflexivity);
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | cbn; lia
                 | intros [] ].
  all: try valid_urandom_default.
Qed.

(** THE REJECT SET IS EVERYTHING.  [Classifier.rejects] is the negation
    of [Classifier.accepts], and refuting a universal over valid entries
    needs one exhibited entry — which is what
    [C1_valid_entry_exists] is for.  Without a statement of this shape
    the two bounds above would be compatible with an empty fire set,
    which is the vacuity [Measure]'s header warns about. *)
Lemma C1_rejects_every_valid_input : forall f,
  valid_fin_input f -> rejects C1_image f.
Proof.
  intros f Hf. destruct (C1_valid_entry_exists _ Hf) as (en & Hen).
  exact (rejects_by_exit1 _ _ _ Hf Hen (C1_must_exit_one _ _ _)).
Qed.

Lemma C2_rejects_every_valid_input : forall f,
  valid_fin_input f -> rejects C2_image f.
Proof.
  intros f Hf. destruct (C2_valid_entry_exists _ Hf) as (en & Hen).
  exact (rejects_by_exit1 _ _ _ Hf Hen (C2_must_exit_one _ _ _)).
Qed.

(** ... AND THAT COSTS SOMETHING.  Two rejected inputs with distinct
    cores are enough to REFUTE the bound [1] under the unit weight at
    total [1] ([Measure.weight_bound_refutable]).  So the demo's [b = 1]
    is not a number that any classifier and any distribution would
    satisfy: it is a claim about this distribution, and a differently
    normalized one over the same reject set fails it.

    This is the bite the whole-space certificate needs, because that
    certificate never reads the reject set — the proof of the bound
    would go through unchanged for a classifier that accepted
    everything.  What separates the two cases is here.

    It is NOT yet a statement about [Distribution.DemoDist], because it
    changes the weight.  The next three lemmas are. *)
Example demo_reject_set_refutes_a_unit_weight :
  ~ weight_bound_T C1_image (fun _ => 1%Q) 1%Q 1%Q.
Proof.
  apply (weight_bound_refutable C1_image
           (demo_input []) (demo_input [Z_to_bv 8 0])).
  - exact (C1_rejects_every_valid_input _ (demo_input_is_valid _)).
  - exact (C1_rejects_every_valid_input _ (demo_input_is_valid _)).
  - unfold demo_input. rewrite !fin_core_core_input. congruence.
Qed.

(* =========================================================================
   ... and the multiplier cannot be dropped, against the demo's OWN
   distribution
   ========================================================================= *)

(** [MeasureLib]'s lower witness family, shown to lie inside the demo's
    reject set.  [MeasureLib.geo_lower_witness] is literally
    [map (fun s => core_input (mkFinCore argv envp fs s)) (short_inputs k)]
    — the same family [demo_input] belongs to — so at the demo's own
    launch-time environment every member is one of the records
    [demo_input_is_valid] validates.

    This one-line bridge is the step [MeasureLib]'s header says a
    consumer must NOT read in for free: the library is explicit that its
    lower certificate says nothing about whether the witness cores are
    rejected by anything, or even valid.  Here they are both, and it is
    proved rather than assumed — which is the only reason the two
    refutations below are available to this demo. *)
Lemma demo_geo_witness_rejected : forall (C : Image),
  (forall f, valid_fin_input f -> rejects C f) ->
  forall k f,
    List.In f (geo_lower_witness demo_argv demo_envp demo_fs k) ->
    rejects C f.
Proof.
  intros C Hall k f Hin. unfold geo_lower_witness in Hin.
  apply List.in_map_iff in Hin. destruct Hin as (s & <- & _).
  exact (Hall _ (demo_input_is_valid s)).
Qed.

(** THE MULTIPLIER IS NOT FREE, at [b = 0].  One rejected input of
    positive weight is enough: the empty standard input weighs [1 # 8]
    under [Distribution.DemoDist] ([Distribution.demo_w_positive]), and
    a bound of [0] would have to hold of the one-element list naming
    it.  So the two obligations are not the ones an image with no valid
    entry gets for nothing — that image would satisfy [b = 0]
    ([Classifier.accepts_vacuous_no_entries]). *)
Lemma demo_b_zero_refutable : forall (C : Image),
  (forall f, valid_fin_input f -> rejects C f) ->
  ~ weight_bound_T C DemoDist.w DemoDist.M 0.
Proof.
  intros C Hall Hb.
  assert (Hnd : List.NoDup (List.map fin_core [demo_input []])).
  { cbn [List.map]. apply List.NoDup_cons;
      [intros [] | apply List.NoDup_nil]. }
  assert (Hrej : forall f, List.In f [demo_input []] -> rejects C f).
  { intros f [<- | []]. exact (Hall _ (demo_input_is_valid [])). }
  specialize (Hb _ Hnd Hrej).
  apply (proj2 (Qle_bool_iff _ _)) in Hb. vm_compute in Hb. discriminate.
Qed.

(** ... and not at [b = 1 # 2] either, which is the sharper claim and
    the one that needs the library's lower witness.  The family at
    [k = 6] — every standard input of length under six, over the fixed
    environment — is admissible ([MeasureLib.geo_lower_witness_nodup]),
    every member of it is rejected (above), and it weighs exactly
    [1 - (7 # 8) ^ 6 = 144495 # 262144], a shade over 0.55.  A bound of
    half the declared mass would have to cover it, and does not.

    WHAT THIS DOES AND DOES NOT SAY.  It says the demo's [b = 1] is a
    real claim about [Distribution.DemoDist]: the multiplier cannot be
    halved, so the number is not one that any distribution and any
    classifier would satisfy.  It does NOT say [1] is the LEAST provable
    multiplier, and that gap is deliberate rather than an omission —
    [MeasureLib]'s header names the inference from "the declared mass is
    the least upper bound of the admissible partial sums" to "the [b * M]
    of [Measure.weight_bound_T] cannot be lowered for a given fire set"
    as the misreading a consumer of that library is positioned to make.
    Every [b] strictly between [144495 # 262144] and [1] is left open
    here, and closing the gap would take a lower certificate over the
    REJECTED lists specifically, at every [k] rather than at one. *)
Lemma demo_b_half_refutable : forall (C : Image),
  (forall f, valid_fin_input f -> rejects C f) ->
  ~ weight_bound_T C DemoDist.w DemoDist.M (1 # 2).
Proof.
  intros C Hall Hb.
  destruct (stdin_geometric_mass_lower_witness demo_p_stop demo_argv
              demo_envp demo_fs demo_p_stop_nonneg demo_p_stop_le_1 6)
    as (Hnd & Hsum).
  specialize (Hb (geo_lower_witness demo_argv demo_envp demo_fs 6) Hnd
                 (demo_geo_witness_rejected C Hall 6)).
  unfold DemoDist.w in Hb. rewrite <- core_sum_cd_lift in Hb.
  unfold demo_cd in Hb. rewrite Hsum in Hb.
  apply (proj2 (Qle_bool_iff _ _)) in Hb. vm_compute in Hb.
  (* [discriminate Hb], NOT bare [discriminate]: the bare form scans
     every hypothesis for a discriminable equality, and [Hsum] is one
     ([Qeq] unfolds to an equation between [Z]s) whose left-hand side
     names the whole witness family -- normalizing it would enumerate
     every standard input shorter than six bytes. *)
  discriminate Hb.
Qed.

(** The two instances, one per classifier image and stated separately
    for the reason the two bounds are: [C1] and [C2] share a segment
    list, and a single lemma about "the classifier" would be doing the
    work of two. *)
Example C1_bound_needs_the_multiplier :
  ~ weight_bound_T C1_image DemoDist.w DemoDist.M 0
  /\ ~ weight_bound_T C1_image DemoDist.w DemoDist.M (1 # 2).
Proof.
  split; [ exact (demo_b_zero_refutable _ C1_rejects_every_valid_input)
         | exact (demo_b_half_refutable _ C1_rejects_every_valid_input) ].
Qed.

Example C2_bound_needs_the_multiplier :
  ~ weight_bound_T C2_image DemoDist.w DemoDist.M 0
  /\ ~ weight_bound_T C2_image DemoDist.w DemoDist.M (1 # 2).
Proof.
  split; [ exact (demo_b_zero_refutable _ C2_rejects_every_valid_input)
         | exact (demo_b_half_refutable _ C2_rejects_every_valid_input) ].
Qed.

(** The classifiers ANSWER, observably.  [Classifier.decides]' totality
    disjunct is a claim about exit codes; this turns it into the event an
    observer of the run would actually read, through
    [MustExit.must_exit_with_realizes] — and [Traces] pins the trace
    exactly, so the answer is the only thing either classifier ever
    emits. *)
Example C1_answers_one : forall f en,
  bh_traces (run C1_image classifier_alloc_limit en (to_proc_input f))
            [ExitEv verdict_reject (in_fs (to_proc_input f))].
Proof.
  intros f en. apply (proj2 (C1_traces _ _ _ _)). right. reflexivity.
Qed.

(** ... and never the other one, so a reader of the exit code is not
    reading a coin flip.  This is [Classifier.decides]' iff seen from
    the trace side. *)
Example C1_never_answers_zero : forall f en,
  ~ bh_traces (run C1_image classifier_alloc_limit en (to_proc_input f))
              [ExitEv verdict_accept (in_fs (to_proc_input f))].
Proof.
  intros f en.
  exact (no_exit_zero_trace_of_exit_one C1_image C1_traces
           classifier_alloc_limit en (to_proc_input f)).
Qed.

(** Neither classifier accepts anything.  The mechanism is
    [Classifier.rejects_by_exit1], inside
    [C1_rejects_every_valid_input] above: it takes the valid entry as an
    argument and turns the exit-1 verdict there into the failure of
    [Classifier.accepts]' universal.  So the inhabitation of the entry
    space is spent here, but through that lemma rather than through any
    transfer from [Classifier.decides]. *)
Example C1_accepts_nothing : forall f,
  valid_fin_input f -> ~ accepts C1_image f.
Proof.
  intros f Hf.
  exact (proj2 (C1_rejects_every_valid_input f Hf)).
Qed.

Example C2_accepts_nothing : forall f,
  valid_fin_input f -> ~ accepts C2_image f.
Proof.
  intros f Hf.
  exact (proj2 (C2_rejects_every_valid_input f Hf)).
Qed.

(** The transfer that DOES spend the inhabitation, stated because it is
    the useful export: under [Classifier.decides], accepting an input
    and the spec holding of it are the same statement.  It needs the
    entry space inhabited — [Classifier.accepts] is a universal over
    valid entries and says nothing when there are none
    ([Classifier.accepts_vacuous_no_entries]) — and
    [C1_valid_entry_exists] is that hypothesis AT A VALID INPUT.

    [Classifier.decides_accepts_iff] is not used, and the reason is a
    mismatch worth naming rather than working around silently: it asks
    for [forall g, exists en, valid_entry C en (to_proc_input g)], over
    every finite input and not only the valid ones, and no image can
    supply that — [Run.valid_entry]'s [Run.entry_stack_fits] conjunct
    fails outright once argv or envp overruns
    [Run.entry_stack_span_max], which nothing constrains on an invalid
    input.  Its own proof applies the hypothesis only at the [f] it
    already has [Run.valid_input] for, so the premise is stronger than
    the argument uses; the two steps are written out here instead, at
    the hypothesis that is actually available.

    Read against [C1_accepts_nothing] it is the demo's whole story in
    one line: the left side is false everywhere, so the right side is
    too, so the classifier fires everywhere and is right to. *)
Example C1_accepts_iff_spec : forall f,
  valid_fin_input f ->
  (accepts C1_image f
   <-> (agree O1_image P1_image source_alloc_limit (to_proc_input f)
        /\ agree O2_image P2_image target_alloc_limit (to_proc_input f))).
Proof.
  intros f Hf. destruct (C1_valid_entry_exists _ Hf) as (en0 & Hen0).
  split.
  - intros Hacc.
    exact (proj1 (proj1 (C1_classifies_patch_diff f Hf en0 Hen0))
                 (Hacc en0 Hen0)).
  - intros Hspec en Hen.
    exact (proj2 (proj1 (C1_classifies_patch_diff f Hf en Hen)) Hspec).
Qed.

Example C2_accepts_iff_spec : forall f,
  valid_fin_input f ->
  (accepts C2_image f <-> good_input O1_image O2_image (to_proc_input f)).
Proof.
  intros f Hf. destruct (C2_valid_entry_exists _ Hf) as (en0 & Hen0).
  split.
  - intros Hacc.
    exact (proj1 (proj1 (C2_classifies_good_inputs f Hf en0 Hen0))
                 (Hacc en0 Hen0)).
  - intros Hspec en Hen.
    exact (proj2 (proj1 (C2_classifies_good_inputs f Hf en Hen)) Hspec).
Qed.
