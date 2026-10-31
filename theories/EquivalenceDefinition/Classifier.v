(** * EquivalenceDefinition.Classifier — total deciders over finite inputs

    TRUST BOUNDARY: this file is part of the trusted specification.
    Proof files never edit it.  A top-level check that ascribes against a
    module type mentioning [classifies_patch_diff_T] or
    [classifies_good_inputs_T] depends on the definitions here remaining
    fixed, exactly as the baseline check depends on [Equivalence].

    [Equivalence] states obligations about the RELATION between two
    binaries — the baseline shape and its error-free strengthening;
    [MustExit] states an obligation about ONE
    binary — it terminates, on every resolution of the
    nondeterminism, with a named exit code.  This file puts the two
    together.  A CLASSIFIER is a third binary whose exit code is a truth
    value about the other two: it exits 0 on exactly the inputs where the
    programs it is asked about agree, and 1 on the others.

    Three questions have to be answered before that sentence is a
    theorem, and each is answered differently from the way an equivalence
    statement answers it.  Which inputs must it answer on.  What
    "answers" means when [execve] places the stack somewhere new on every
    run.  And whether it may decline to answer at all.

    ** Finite inputs only, and why that is not a weakening in disguise

    A verdict is an OBSERVABLE EVENT.  [MustExit.must_exit_with_realizes]
    is the precise form: a run that must exit with [code] has a finite
    trace ending in [State.ExitEv] carrying it.  Finite is the operative
    word — the classifier reached its answer after reading finitely much
    of standard input, so every input agreeing with this one on that
    prefix gets the same answer.  Accept sets are therefore OPEN in the
    prefix topology on input streams.

    The properties worth classifying are not open.  [agree] says the two
    programs behave the same on this input — no divergence anywhere, at
    any depth — which is an intersection of one condition per prefix:
    closed, and in general not open.  An accept set is open and that set
    is not, so no classifier accepts exactly it.  Exact classification
    over INFINITE streams is therefore an impossibility rather than a
    difficulty, and no amount of proof effort by a task author retires
    it.

    The tempting next step — "a set both open and closed must be
    trivial" — is NOT available here and should not be added back.  The
    prefix topology on byte streams is Cantor space: compact and TOTALLY
    disconnected, where non-trivial clopen sets are the norm rather than
    the exception, since every cylinder is one.  The openness argument
    above appeals to no such principle, and it is the whole of the
    argument.

    TOTALITY sharpens the same conclusion by a second route, and this
    one does use compactness.  A classifier total on every infinite
    stream has BOTH its accept and its reject set open, so the two
    together cover the stream space by cylinders; the space is compact,
    so finitely many of those cylinders already cover it, and each fixes
    a bounded number of leading bytes.  The verdict would then be
    determined by a UNIFORMLY BOUNDED lookahead into standard input —
    which outlaws every classifier that must read to end of input before
    it can answer, and that is most of them.

    Restricting the QUANTIFIER is the honest response, and it is the one
    [FinInput] is built for: [FinInput.FinProcInput] carries a finite
    standard input as a list, [FinInput.valid_fin_input] is
    [Run.valid_input] of the input it denotes and nothing more, and
    [FinInput.valid_finite_input_surjection] says quantifying over valid
    finite records is the same quantifier as quantifying over valid
    finite [State.ProcInput]s.  Restricting the MODEL instead — a
    [Run.valid_input] that rejected endless pipes — would be a lie about
    Linux and would weaken every equivalence statement in the tree;
    [FinInput]'s header makes that argument at length.

    What narrows here is only the classifier obligation.  The patch
    obligations it accompanies, [Equivalence.strong_universal_T] and
    [Equivalence.strong_universal_error_free_T], stay fully general over
    every valid input including the infinite ones.

    ** The verdict is per-entry; the classified property absorbs entries

    [Run.ExecEntry] holds the four choices [execve] makes
    non-deterministically — stack pointer, program break, mmap base, and
    the 16 AT_RANDOM bytes — and the two roles are treated
    asymmetrically here on purpose.

    The property being classified ABSORBS them, so that it is a
    predicate on the input alone ([spec : ProcInput -> Prop] below, which
    is what makes [decides] a shared shape rather than two).  [agree]
    compares trace sets at ALL entry pairs and compares the three error
    facts existentially per program; [good_input] is
    [Equivalence.strong_equiv_error_free] at all entry pairs.

    The verdict is required ROBUST to them: [decides] quantifies the
    classifier's entry universally INSIDE the obligation, demanding the
    iff at every valid entry.  Both directions of that matter.  A
    classifier that accepts under one layout and rejects under another
    has not decided anything — and this is not an exotic failure, it is
    what any program that hashes or prints a stack address does.
    [decides_verdict_entry_uniform] reads the requirement back out: under
    [decides] the exit-0 verdict at one valid entry is the exit-0 verdict
    at every valid entry, which is the sentence a checker needs when it
    runs the binary once and treats the result as the answer.

    ** Totality, and why a diverging rejection is not a rejection

    [decides] conjoins the iff with a DISJUNCTION: on every valid finite
    input, at every valid entry, all executions exit 0 or all exit 1.
    [MustExit.must_exit_with] already rules out crashing, running off the
    edge of the model, wedging and diverging for the verdict it names —
    but only for the verdict it names.  Without the disjunct a classifier
    could satisfy the iff by exiting 0 on exactly the inputs in [spec]
    and LOOPING FOREVER on the others: [must_exit_with verdict_accept
    <-> spec] holds
    of that program, and it decides nothing.

    That reading is not merely weaker; it is operationally invisible.  A
    rejection delivered by divergence cannot be distinguished from a
    rejection still being computed, so nothing observing the process can
    ever conclude "rejected" — a checking pipeline waiting for it waits
    forever, and a timeout is a guess, not a reading.  Requiring the
    disjunct makes rejection an event: [decides_exit1_iff] turns the two
    conjuncts into the statement one actually wants, that exiting 1 IS
    the rejection, and it needs both halves — the iff to know [~ spec]
    excludes exit 0, totality to know that something happens at all.

    The price is paid by the task author, deliberately.  Proving the
    reject side becomes as much work as proving the accept side, and the
    familiar tricks are outlawed: crash-as-rejection is out
    ([MustExit.must_exit_with] refutes any run that can error),
    out-of-memory is out, and "no output" is out.

    That conjunct is also named on its own, as [classifier_total_T], for
    a consumer that wants the two halves of [decides] separately —
    [decides_implies_total] is the projection, and the definition's own
    header records how much more than "total" it asks for.

    ** What [agree] compares, and the warning that goes with it

    Four conjuncts.  The first compares finite trace-prefix sets at ALL
    pairs of valid entries, inheriting the ASLR philosophy of
    [Equivalence.strong_equiv], which quantifies its two entry records
    independently for the same reason: a program whose observable
    behavior depends on where the stack landed is not one this
    development can state an equivalence about.

    TASK AUTHORS MUST KNOW THE CONSEQUENCE.  All-entry-pairs equality is
    applied to a program against itself as readily as against its patch,
    so [agree X X lim inp] is FALSE for a program that prints a stack
    address: two entries give two traces and the sets differ.
    [agree_self_refuted_by_entry_leak] is that statement, machine-checked
    rather than left as advice.  An original binary that leaks entry
    data on paths meant to count as correct therefore disagrees with
    everything, including itself, the patch-difference classifier's spec
    degenerates to the empty set, and the measure bound the task asks for
    degenerates with it.  Such a program is not a hard instance of this
    kind of task; it is outside it.

    The other three conjuncts compare [Run.bh_errors],
    [Run.bh_all_errors] and [Run.bh_unmodeled] as iffs between
    existentials over valid entries — CAN this program error at some
    entry, iff can that one.  Existential because these are facts about
    what a program is capable of, and the entry it does it from is not
    observable to anyone comparing the two programs.  They are not
    implied by the first conjunct: errors are not trace prefixes, so two
    programs can have identical prefix sets while one of them faults and
    the other returns, which is exactly the argument [Equivalence.equiv]
    makes for carrying its own [~ bh_errors] conjunct.

    Note what [agree] does NOT say: neither side has to be error-free.
    It is an AGREEMENT — the two programs may agree to crash.  That is
    required of it, because the difference a patch classifier must detect
    includes "the patch turned a crash into a return".  [good_input] is
    the other predicate, and the other question: it is
    [Equivalence.strong_equiv_error_free] at all entry pairs, so it does
    demand error-freedom of both sides, because what it asks is whether
    the ORIGINAL pair was already behaving well on this input.

    ** The vacuity route is the usual one, and it is load-bearing here

    Every quantifier in this file ranges over VALID entries, so an image
    with none satisfies [decides] for every [spec]
    ([decides_vacuous_no_entries]) and [accepts] every input
    ([accepts_vacuous_no_entries]) — which empties the reject set and
    makes any measure bound over it hold for free.

    What makes this worth a section rather than a footnote is that the
    hole is ONE-SIDED, and the one-sided form is the reachable one.  A
    single unloadable image is enough: an entry-less [Y] agrees with a
    well-behaved [X] on every input
    ([agree_vacuous_no_second_entries]) — a patch binary that fails to
    load "agrees with" its original — and an entry-less [O2] alone makes
    every input good ([good_input_vacuous_no_second_entries]).  "Both
    images broken" is a scenario nobody reaches by accident; "the patch
    did not load" is one a task author reaches on a Tuesday.

    A consuming checker must therefore ascribe [Equivalence.IMAGE_WF]
    for EVERY image it names — the classifier images as much as the
    program images, and each of the program images individually rather
    than trusting that one good image vouches for its partner — exactly
    as the baseline check does;
    [Equivalence.image_brk_satisfiable_entry] is the lemma in that group
    that turns the assertion into the inhabited-entry hypothesis
    [decides_accepts_iff] and [decides_rejects_iff] take — ONE VALID
    INPUT AT A TIME, since it also needs [Run.valid_input] for the input
    at hand in order to place the entry stack, which is why that
    hypothesis is quantified over the VALID finite inputs rather than
    over all of them. *)

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State StackLayout Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The budget a classifier runs under
   ========================================================================= *)

(** The allocation budget every classifier run in this file is seeded
    with.  It ALIASES the TARGET role's budget
    ([State.target_alloc_limit]) rather than naming a third constant.

    Aliasing a budget is a thing to be careful about, so here is the
    argument.  The reason [State.source_alloc_limit] and
    [State.target_alloc_limit] differ at all is that they are compared:
    [Equivalence.strong_equiv] and [Equivalence.strong_equiv_error_free]
    run each side at ITS role's budget, and
    [classifies_patch_diff_T] keeps that discipline for the two
    original/patched pairs, so a patch cannot make an
    allocation-behavior change disappear by being judged at the other
    role's ceiling.  The classifier is not a side of any of those
    comparisons.  Its budget occurs only inside
    [MustExit.must_exit_with], which speaks about a single run of a
    single image, and no statement anywhere puts it next to another
    budget.  So the failure mode aliasing usually has — two things that
    ought to differ silently becoming one — has no site here.

    What the alias does decide, and this is why it is written as one:
    the classifier inherits the target role's ENVIRONMENT obligation
    rather than acquiring a new one.  These budgets are model
    capacities nothing machine-checks a deployment against; a runtime that lets a process
    exceed the ceiling the theorem was proved under is running a
    different program from the one the proof is about, and a classifier
    proved TOTAL under this ceiling can perfectly well fail to answer
    under a smaller one.  Reusing the target's value means a deployment
    that already hosts the target binary correctly hosts the classifier
    correctly, with one ceiling to configure instead of two.  It also
    fixes what happens if the role budgets are ever changed
    independently: the classifier follows the target, by this
    definition, rather than by a reader's inference. *)
Definition classifier_alloc_limit : Z := target_alloc_limit.

(* =========================================================================
   The classified properties
   ========================================================================= *)

(** Per-input behavioral agreement between two images run at ONE shared
    budget: what a patch-difference classifier is asked about, for one
    original/patched pair.  See this file's header for the argument
    behind each conjunct, and for the warning that the first one makes
    this predicate irreflexive on programs whose traces depend on the
    [execve] placements. *)
Definition agree (X Y : Image) (lim : Z) (inp : ProcInput) : Prop :=
  (forall enX enY,
     valid_entry X enX inp -> valid_entry Y enY inp ->
     trace_equiv (bh_traces (run X lim enX inp))
                 (bh_traces (run Y lim enY inp)))
  /\ ((exists en, valid_entry X en inp /\ bh_errors (run X lim en inp))
      <-> (exists en, valid_entry Y en inp /\ bh_errors (run Y lim en inp)))
  /\ ((exists en, valid_entry X en inp /\ bh_all_errors (run X lim en inp))
      <-> (exists en, valid_entry Y en inp /\ bh_all_errors (run Y lim en inp)))
  /\ ((exists en, valid_entry X en inp /\ bh_unmodeled (run X lim en inp))
      <-> (exists en, valid_entry Y en inp /\ bh_unmodeled (run Y lim en inp))).

(** The good inputs of the original pair: the inputs on which the two
    ORIGINALS are already error-free equivalent, at every pair of valid
    entries.  This is [Equivalence.strong_equiv_error_free] with its two
    entry records universally quantified, so each side runs at its own
    role's budget and neither side may fault — unlike [agree], which
    lets the two programs agree to crash.  The difference is the
    difference between the two classifiers' questions: [agree] asks
    whether patching changed anything, [good_input] asks whether there
    was anything wrong to begin with. *)
Definition good_input (O1 O2 : Image) (inp : ProcInput) : Prop :=
  forall en1 en2,
    valid_entry O1 en1 inp -> valid_entry O2 en2 inp ->
    strong_equiv_error_free O1 O2 en1 en2 inp.

(* =========================================================================
   [agree] and [good_input] bite
   ========================================================================= *)

(** An error-capability mismatch refutes [agree].  Stated from a
    hypothesis pack rather than from two concrete images: exhibiting a
    pair of images that really run this way is example-side work, in the
    spirit of [Checks.Examples.run_of_undecodable_image_refutes_modeled],
    and the point being made here is about the DEFINITION — the second
    conjunct is not decoration, one program being able to fault where the
    other cannot is by itself a disagreement, even when the two have
    identical trace sets. *)
Lemma agree_refuted_by_error_mismatch : forall X Y lim inp enX,
  valid_entry X enX inp ->
  bh_errors (run X lim enX inp) ->
  (forall en, valid_entry Y en inp -> ~ bh_errors (run Y lim en inp)) ->
  ~ agree X Y lim inp.
Proof.
  intros X Y lim inp enX HenX Herr HY (_ & Herrs & _ & _).
  destruct (proj1 Herrs (ex_intro _ enX (conj HenX Herr)))
    as (en & Hen & Herr').
  exact (HY en Hen Herr').
Qed.

(** The self-disagreement warning from this file's header, mechanized: a
    program with a trace available at one valid entry and not at another
    fails [agree] AGAINST ITSELF.  Nothing pathological is required of
    such a program — printing a pointer is enough — so this is the shape
    of the constraint task authors are under, and the reason the
    all-entry-pairs conjunct is called out in the authoring guidance
    rather than left to be discovered from a failed proof. *)
Lemma agree_self_refuted_by_entry_leak : forall X lim inp en1 en2 tr,
  valid_entry X en1 inp ->
  valid_entry X en2 inp ->
  bh_traces (run X lim en1 inp) tr ->
  ~ bh_traces (run X lim en2 inp) tr ->
  ~ agree X X lim inp.
Proof.
  intros X lim inp en1 en2 tr H1 H2 Hin Hout (Htr & _).
  exact (Hout (proj1 (Htr en1 en2 H1 H2 tr) Hin)).
Qed.

(** [agree] is SYMMETRIC.  Worth stating for its own sake — a predicate
    called "agree" that distinguished its two arguments would be
    misnamed, and nothing in the definition privileges either side: the
    two images share one budget, the trace conjunct quantifies both
    entries, and each of the three error conjuncts is an iff.  It is
    also what lets each one-sided fact below be stated once and
    mirrored, instead of twice with the roles swapped. *)
Lemma agree_sym : forall X Y lim inp,
  agree X Y lim inp -> agree Y X lim inp.
Proof.
  intros X Y lim inp (Htr & Herr & Hall & Hun).
  split; [| split; [| split]].
  - intros enY enX HY HX tr.
    split; [exact (proj2 (Htr enX enY HX HY tr))
           | exact (proj1 (Htr enX enY HX HY tr))].
  - split; [exact (proj2 Herr) | exact (proj1 Herr)].
  - split; [exact (proj2 Hall) | exact (proj1 Hall)].
  - split; [exact (proj2 Hun) | exact (proj1 Hun)].
Qed.

(** The other side: [agree] is satisfiable — and the cheapest way to
    satisfy it is the vacuity route, stated here in the form that is
    actually REACHABLE.  ONE image with no valid entry is enough: if
    [Y] has none, its side of every conjunct is empty, and [agree X Y]
    then holds of any [X] that cannot error, all-error or go unmodeled
    at any entry of its own.  Concretely, a patch binary that fails to
    load "agrees with" a well-behaved original, on every input, and the
    patch-difference classifier is entitled to accept everything.

    That is the scenario a task author reaches by accident, which is why
    it is stated ahead of the symmetric [agree_vacuous_no_entries]
    below: "both binaries are unloadable" is a case nobody meets, and a
    vacuity lemma that only covers it understates the hole it is there
    to warn about.  The three hypotheses on [X] are not decoration —
    without them the error conjuncts are refutable, which is exactly
    [agree_refuted_by_error_mismatch].  Nothing here closes the route;
    the [Equivalence.IMAGE_WF] ascription does, per image, which is the
    argument this file's header makes. *)
Lemma agree_vacuous_no_second_entries : forall X Y lim inp,
  (forall en, ~ valid_entry Y en inp) ->
  (forall en, valid_entry X en inp -> ~ bh_errors (run X lim en inp)) ->
  (forall en, valid_entry X en inp -> ~ bh_all_errors (run X lim en inp)) ->
  (forall en, valid_entry X en inp -> ~ bh_unmodeled (run X lim en inp)) ->
  agree X Y lim inp.
Proof.
  intros X Y lim inp HY Herr Hall Hun.
  split; [| split; [| split]].
  - intros enX enY _ Hy. exfalso. exact (HY enY Hy).
  - split; [ intros (en & Hen & Hb); exfalso; exact (Herr en Hen Hb)
           | intros (en & Hen & _); exfalso; exact (HY en Hen) ].
  - split; [ intros (en & Hen & Hb); exfalso; exact (Hall en Hen Hb)
           | intros (en & Hen & _); exfalso; exact (HY en Hen) ].
  - split; [ intros (en & Hen & Hb); exfalso; exact (Hun en Hen Hb)
           | intros (en & Hen & _); exfalso; exact (HY en Hen) ].
Qed.

(** The mirror image, by [agree_sym]: an unloadable ORIGINAL is as
    vacuous as an unloadable patch, and neither direction is the
    privileged one. *)
Lemma agree_vacuous_no_first_entries : forall X Y lim inp,
  (forall en, ~ valid_entry X en inp) ->
  (forall en, valid_entry Y en inp -> ~ bh_errors (run Y lim en inp)) ->
  (forall en, valid_entry Y en inp -> ~ bh_all_errors (run Y lim en inp)) ->
  (forall en, valid_entry Y en inp -> ~ bh_unmodeled (run Y lim en inp)) ->
  agree X Y lim inp.
Proof.
  intros X Y lim inp HX Herr Hall Hun.
  apply agree_sym, agree_vacuous_no_second_entries; assumption.
Qed.

(** The both-sided form, now a corollary: two images with no valid entry
    agree on every input, about nothing.  The hypotheses on [X] that
    [agree_vacuous_no_second_entries] asks for are discharged by [X]
    having no valid entry either. *)
Lemma agree_vacuous_no_entries : forall X Y lim inp,
  (forall en, ~ valid_entry X en inp) ->
  (forall en, ~ valid_entry Y en inp) ->
  agree X Y lim inp.
Proof.
  intros X Y lim inp HX HY.
  apply agree_vacuous_no_second_entries.
  - exact HY.
  - intros en Hen. exfalso. exact (HX en Hen).
  - intros en Hen. exfalso. exact (HX en Hen).
  - intros en Hen. exfalso. exact (HX en Hen).
Qed.

(** [good_input] bites for the reason the error-free shape exists: one
    erroring resolution of the first original, at one valid entry pair,
    refutes it.  So the good-input classifier's spec is not a predicate every
    input satisfies, and an original that crashes on an input is not
    quietly counted as behaving well there. *)
Lemma good_input_refuted_by_source_error : forall O1 O2 inp en1 en2,
  valid_entry O1 en1 inp ->
  valid_entry O2 en2 inp ->
  bh_errors (run O1 source_alloc_limit en1 inp) ->
  ~ good_input O1 O2 inp.
Proof.
  intros O1 O2 inp en1 en2 H1 H2 Herr Hg.
  destruct (Hg en1 en2 H1 H2) as (Hef & _ & _).
  exact (error_free_unkilled_error_free _ Hef Herr).
Qed.

(** ... and it has the same vacuity route, from EITHER image alone.
    [good_input] quantifies both entries with a validity hypothesis
    apiece, so one unloadable image empties the range whichever one it
    is — there is no "at least the other original was fine" to fall back
    on.  Both halves are stated because a reader checking the
    [Equivalence.IMAGE_WF] obligation needs to see that it is per image
    and not per pair. *)
Lemma good_input_vacuous_no_first_entries : forall O1 O2 inp,
  (forall en, ~ valid_entry O1 en inp) -> good_input O1 O2 inp.
Proof.
  intros O1 O2 inp H en1 en2 H1 _. exfalso. exact (H en1 H1).
Qed.

Lemma good_input_vacuous_no_second_entries : forall O1 O2 inp,
  (forall en, ~ valid_entry O2 en inp) -> good_input O1 O2 inp.
Proof.
  intros O1 O2 inp H en1 en2 _ H2. exfalso. exact (H en2 H2).
Qed.

(* =========================================================================
   The buggy / not-buggy split: what the gate of a two-region submission
   decides
   ========================================================================= *)

(** THE VARIANT, in the gated family's words.  The gated-size shapes let
    a submission split its work into several programs, one per PART of
    the input space, and be charged the expectation of the parts rather
    than the maximum; the parts are carved out by GATE IMAGES, a gate
    being a binary that exits 0 on the inputs its program is meant to
    handle and 1 on the others, with [accepts] the reading of "exits 0".
    The BUGGY / NOT-BUGGY TWO-REGION variant is that family with exactly
    two programs, and therefore exactly one gate, and it fixes what the
    gate decides: whether THE ORIGINAL PROGRAM IS ERROR-FREE ON THIS
    INPUT.  The two regions are the inputs the original handles without
    faulting and the inputs on which it faults — "not buggy" and
    "buggy" — and which region an input falls in is the gate's verdict
    on it, not a property of the submission.

    Three obligations make up the variant and only ONE of them is new
    here.  Each of the two slice programs owes [GatedSize.gated_slice_T]
    against the original on its own region — the first at
    [GatedSize.slice_accept []] of this gate, the second at
    [GatedSize.slice_rest] of the one-element gate list — which is the
    existing gated statement used unchanged.  The two together — the
    binary the submission actually ships — owe
    [Equivalence.strong_universal_T] against the original, ungated,
    which is the baseline statement used unchanged.  What neither of
    those says is what the gate is FOR, and a gate whose meaning is left
    to prose is a gate a submission may define however it likes: the
    region boundary would then be chosen by the thing being measured.
    So the gate's meaning is stated here, in the trusted file that
    already owns [agree] and [good_input], and the checker emits these
    two names.

    The checker-side design for the gated family lives outside this
    repository and is not cited by path; nothing below depends on it.

    WHY HERE AND NOT BESIDE THE SLICES.  The slice shapes are agnostic
    about what a gate decides — [GatedSize.slice_accept] consumes
    [accepts] and nothing else, which is what lets
    [GatedSize.slices_disjoint_accept_accept] be proved of abstract
    images — while this is a statement about what a particular gate's
    exit code MEANS.
    That is this file's subject: [agree] is the patch-difference gate's
    meaning and [good_input] is the good-input gate's, and
    [classifies_error_free_inputs_T] below is the third in that list,
    sharing their [decides] shape exactly.  Putting it here also keeps
    it available to a consumer that wants the predicate without the
    measure arithmetic the slice file carries. *)

(** The inputs on which the original never faults: at EVERY entry
    [execve] could have chosen, the original's run is [error_free].

    This is written to be, conjunct for conjunct, the SOURCE SIDE of
    [Equivalence.strong_equiv_error_free] with the entry universally
    quantified — the same [Equivalence.error_free], which is
    [~ Run.bh_errors] and so is refuted by ONE erroring resolution of
    the nondeterminism, and the same budget, [State.source_alloc_limit].
    A reader checking that this predicate says what the variant's name
    claims should compare it against that definition and nothing else.

    "AND MODELED" IS NOT A SECOND CONJUNCT, and its absence is not a
    weakening.  Error-freedom subsumes [Equivalence.modeled] on the
    behaviors [Run.run] builds, because everything the model declines to
    interpret takes the error transition
    ([Equivalence.run_unmodeled_errors]); that is exactly why
    [Equivalence.strong_equiv_error_free] carries no [Equivalence.modeled]
    conjunct either, and [error_free_input_modeled] reads the
    consequence back out rather than leaving it to be re-derived.

    THE BUDGET IS THE SOURCE ROLE'S, NOT THE CLASSIFIER'S, and the two
    never meet.  A gate deciding this predicate RUNS at
    [classifier_alloc_limit], through [decides] and [MustExit.must_exit_with];
    the property it decides is about a run of the ORIGINAL, at the
    budget every equivalence statement compares the original at.  Naming
    [classifier_alloc_limit] here instead would ask the gate about a
    program run under a ceiling no equivalence statement uses, and the
    two slice obligations would then be about different runs from the
    one the gate sorted. *)
Definition error_free_input (O : Image) (inp : ProcInput) : Prop :=
  forall en, valid_entry O en inp ->
    error_free_unkilled (run O source_alloc_limit en inp).
  (* [error_free_unkilled] AND NOT [error_free]: the gate is named for
     an input that does not make the original crash, and a death by a
     fatal signal is a crash that takes no error transition.  Before
     the write arms could raise SIGPIPE no run under [Run.valid_input]
     could end in one, so the two predicates agreed; one can now
     ([Sys.Fs.ReadWrite.write_spec]), and with the weaker predicate
     this gate would sort an input on which the original dies into the
     error-free side.  The same decision [Equivalence.strong_equiv_error_free]
     takes, for the same reason. *)

(** ... and the consequence just argued for: on an error-free input the
    original is also covered by the model at every valid entry.  The
    contrapositive of [Equivalence.run_unmodeled_errors], applied under
    the entry quantifier. *)
Lemma error_free_input_modeled : forall O inp en,
  error_free_input O inp ->
  valid_entry O en inp ->
  modeled (run O source_alloc_limit en inp).
Proof.
  intros O inp en Hef Hen.
  exact (run_error_free_modeled _ _ _ _
           (error_free_unkilled_error_free _ (Hef en Hen))).
Qed.

(** THE BITE.  One erroring resolution, at one valid entry, and the
    input is not error-free — so the predicate is not one every input
    satisfies, and the gate's two regions are not the whole space and
    the empty set.  Both hypotheses are load-bearing: an error at an
    INVALID entry is a run the definition never quantified over, and the
    error hypothesis is the EXISTENTIAL [Run.bh_errors] rather than
    [Run.bh_all_errors] because [Equivalence.error_free] negates the
    existential — one erroring resolution is already enough, and asking
    for every execution to error would state a weaker lemma.

    This is [good_input_refuted_by_source_error]'s shape at one image
    instead of two, and it bites for the same reason: the error-free
    family exists precisely to stop a faulting original from being
    counted as behaving well. *)
Lemma error_free_input_refuted_by_error : forall O inp en,
  valid_entry O en inp ->
  bh_errors (run O source_alloc_limit en inp) ->
  ~ error_free_input O inp.
Proof.
  intros O inp en Hen Herr Hef.
  exact (error_free_unkilled_error_free _ (Hef en Hen) Herr).
Qed.

(** THE VACUITY ROUTE, in the family's style and with the same answer.
    An original with no valid entry at an input is error-free THERE,
    having executed nothing: the quantifier's range is empty and
    strengthening what sits under it repairs nothing.  As with
    [good_input_vacuous_no_first_entries] and
    [accepts_vacuous_no_entries], the direction is the one a reader gets
    backwards — an original that does not load is not "buggy
    everywhere", it is NOT-BUGGY EVERYWHERE.

    What that means for the gate is stated separately, and it is worse
    than it looks:
    [classifies_error_free_inputs_T_vacuous_accepts_everything] below.
    Nothing here closes the route; the [Equivalence.IMAGE_WF] ascription
    a consuming checker makes for every image it names does, and it is
    owed for the ORIGINAL here, which is an image this file's header
    already covers. *)
Lemma error_free_input_vacuous_no_entries : forall O inp,
  (forall en, ~ valid_entry O en inp) -> error_free_input O inp.
Proof.
  intros O inp Hno en Hen. exfalso. exact (Hno en Hen).
Qed.

(** THE POSITIVE RELATION TO [good_input].  An input on which the
    original is error-free equivalent to ITSELF is an input on which the
    original does not fault: instantiate both entry quantifiers at the
    same entry and take the first conjunct of
    [Equivalence.strong_equiv_error_free].  So the two gates of the
    family do not disagree where they overlap — the good-input gate's
    question, asked of one image against itself, is at least as strong
    as this one's. *)
Lemma good_input_self_error_free_input : forall O inp,
  good_input O O inp -> error_free_input O inp.
Proof.
  intros O inp Hg en Hen.
  exact (proj1 (Hg en en Hen Hen)).
Qed.

(** The two-image form, and the hypothesis it needs.  [good_input O1 O2]
    still bounds the FIRST image's runs — its first conjunct is about
    [O1] alone — but only through a quantifier that also ranges over
    [O2]'s entries, so one valid entry of [O2] has to be produced before
    anything about [O1] can be read off.  Stated with that entry as a
    hypothesis rather than derived from well-formedness, because this
    file assumes nothing about the images it quantifies over. *)
Lemma good_input_error_free_input : forall O1 O2 inp en2,
  valid_entry O2 en2 inp ->
  good_input O1 O2 inp ->
  error_free_input O1 inp.
Proof.
  intros O1 O2 inp en2 H2 Hg en1 H1.
  exact (proj1 (Hg en1 en2 H1 H2)).
Qed.

(** ... and why that hypothesis cannot be dropped, mechanized rather
    than asserted.  Take an [O2] that does not load: [good_input O1 O2]
    then holds of every input ([good_input_vacuous_no_second_entries])
    whatever [O1] does, including an [O1] that faults — which
    [error_free_input] refuses.  So the implication above is genuinely
    conditional, and a reader who took [good_input] to bound the first
    image on its own would have the two gates disagreeing exactly where
    the vacuity route runs.

    Both halves are asserted together, as [Measure]'s and the slice
    file's counterexample lemmas are: the pair of facts is the content,
    and an implication between them would be the weaker statement. *)
Lemma good_input_not_error_free_input : forall O1 O2 inp en1,
  (forall en, ~ valid_entry O2 en inp) ->
  valid_entry O1 en1 inp ->
  bh_errors (run O1 source_alloc_limit en1 inp) ->
  good_input O1 O2 inp /\ ~ error_free_input O1 inp.
Proof.
  intros O1 O2 inp en1 Hno H1 Herr.
  split.
  - exact (good_input_vacuous_no_second_entries O1 O2 inp Hno).
  - exact (error_free_input_refuted_by_error O1 inp en1 H1 Herr).
Qed.

(* =========================================================================
   The two verdicts
   ========================================================================= *)

(** The accepting and rejecting exit codes.

    Written PLAIN, with no [bv_and … 255] wrapper, per the convention
    [MustExit]'s header sets out and argues for: the exit spec applies
    the mask before the status reaches the model, so [State.m_halted]
    already holds the Linux-observable low byte, and
    [MustExit.must_exit_with] compares it directly.  Both words are
    already in [0 .. 255], so [must_exit_with verdict_accept] is
    precisely "exit(0)
    as a waiting parent sees it".  Re-masking would be propositionally
    harmless and syntactically different, and syntactic form is what
    matters: [MustExit.must_exit_with_exclusive] concludes a bare
    equality of codes, which [verdict_accept_neq_reject] below then
    contradicts. *)
Definition verdict_accept : word := Z_to_bv 64 0.
Definition verdict_reject : word := Z_to_bv 64 1.

(** The two verdicts are different words.  Everything that reads a
    classifier's answer as a decision rests on this: without it,
    [MustExit.must_exit_with_exclusive] would be an equality with nothing
    to contradict, and "exits 0" and "exits 1" could both hold.  Proved
    through [bv_unsigned] rather than by [discriminate] on the
    bitvector records, since those carry a well-formedness field. *)
Lemma verdict_accept_neq_reject : verdict_accept <> verdict_reject.
Proof.
  intros H. apply (f_equal bv_unsigned) in H.
  unfold verdict_accept, verdict_reject in H. rewrite !Z_to_bv_unsigned in H.
  vm_compute in H. discriminate.
Qed.

(* =========================================================================
   The classifier obligation
   ========================================================================= *)

(** The shared classifier shape: [C] is a TOTAL, entry-robust decider for
    [spec] on finite inputs.  On every valid [FinInput.FinProcInput] and
    at every valid entry of [C], exiting 0 is equivalent to the input
    satisfying [spec], and one of the two verdicts is reached.

    All three restrictions in that sentence are argued for in this file's
    header: finite inputs because acceptance is finitely observable and
    agreement is not, per-entry because a verdict that depends on where
    [execve] put the stack is not a verdict, totality because a rejection
    that never terminates cannot be observed.  [decides_exit1_iff] is the
    consequence the two conjuncts exist to produce.

    Note that [spec] is a predicate on [State.ProcInput], not on the
    finite record: the property being classified is the same property an
    equivalence statement would name, and only the QUANTIFIER is
    restricted.  [FinInput.to_proc_input] is where the restriction is
    applied, and [FinInput.valid_finite_input_surjection] is what lets a
    reader check this statement against the informal "for every valid
    finite input" without reasoning about the record.

    WHAT SATISFIES THIS, AND WHAT STILL DOES NOT.  The predicate is
    satisfied vacuously by an image with no valid entry, for every
    [spec] ([decides_vacuous_no_entries]), and this file's header covers
    that route: why the one-sided form is reachable, and why only a
    consuming checker's [Equivalence.IMAGE_WF] ascription closes it.
    Note that the header argues reachability for an entry-less PROGRAM
    image — a patch binary that failed to load — and then extends the
    [IMAGE_WF] requirement to the classifier image without arguing that
    case separately.  Either way that hole is the header's subject and
    not this note's, and this is not a second telling of it.

    It is ALSO satisfied non-vacuously, which is what says the
    obligation is demanding rather than merely unmet.
    [Examples.patchclassify_demo.Obligations] proves
    [classifies_patch_diff_T] of a concrete image and
    [classifies_good_inputs_T] of another — both are [decides] by
    definition — beside
    [Examples.patchclassify_demo.Obligations.C1_valid_entry_exists] and
    [Examples.patchclassify_demo.Obligations.C2_valid_entry_exists],
    which hand back an entry at EVERY valid input and so rule out the
    vacuous route for those two images.  [classifier_total_T] follows
    from either by [decides_implies_total]; [accepts] has its own
    witness in [Checks.GatedSize.gate_exit0_accepts]; and
    [Measure.weight_bound_T] is proved of both demo classifiers
    ([Examples.patchclassify_demo.Obligations.C1_weight_bound],
    [Examples.patchclassify_demo.Obligations.C2_weight_bound]) with the
    same file refuting the bound at smaller values, so the number is not
    free either.

    WHAT IS STILL MISSING is narrower than "a witness", and worth
    naming because it is the half of the correctness iff a task actually
    depends on.  Both demo classifiers REJECT every valid input
    ([Examples.patchclassify_demo.Obligations.C1_rejects_every_valid_input],
    [Examples.patchclassify_demo.Obligations.C2_rejects_every_valid_input]),
    so no [decides] instance in this tree ever ACCEPTS anything: the
    accepting direction of the iff is unexercised.
    [Checks.GatedSize.gate_exit0_accepts] accepts, but
    [Checks.Examples.exit0_image] is not proved to [decides] any
    property, so the two halves have not been met by one image. *)
Definition decides (C : Image) (spec : ProcInput -> Prop) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en,
      valid_entry C en (to_proc_input f) ->
      (must_exit_with verdict_accept C classifier_alloc_limit en (to_proc_input f)
       <-> spec (to_proc_input f))
      /\ (must_exit_with verdict_accept C classifier_alloc_limit en (to_proc_input f)
          \/ must_exit_with verdict_reject C classifier_alloc_limit en (to_proc_input f)).

(** The TOTALITY conjunct of [decides], named on its own: on every valid
    finite input, at every valid entry, the classifier reaches one of the
    two verdicts.  It is named because a consumer that wants the two
    halves of [decides] separately should cite a name from this trusted
    file rather than retype the quantifier prefix into scaffold text of
    its own, which is the same reason [classifies_patch_diff_T] and
    [classifies_good_inputs_T] exist as definitions instead of as
    unfoldings.

    "Total" undersells what this asks for, and the gap is worth stating
    because a reader who takes the name at face value will underestimate
    the obligation.  [MustExit.must_exit_with] is not "terminates with a
    code": it refutes every execution that reaches the error transition
    ([MustExit.must_exit_with_no_error]) and, through that, every
    execution that runs off the edge of the model
    ([MustExit.must_exit_with_modeled]).  So this one definition says
    MODELLED AND NO-ERROR ON EVERY VALID FINITE INPUT AT EVERY VALID
    ENTRY — the three tricks the header's totality section outlaws,
    crash-as-rejection, out-of-memory and "no output", are excluded by
    it alone, with no error-freedom conjunct alongside.

    [decides] is therefore this conjoined with the per-input correctness
    iff, and [decides_implies_total] is the projection.  Only that
    direction holds: a classifier can answer on everything and answer
    wrongly, which is [decides_refuted_by_wrong_verdict]. *)
Definition classifier_total_T (Cl : Image) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en,
      valid_entry Cl en (to_proc_input f) ->
      must_exit_with verdict_accept Cl classifier_alloc_limit en (to_proc_input f)
      \/ must_exit_with verdict_reject Cl classifier_alloc_limit en (to_proc_input f).

(** The projection, so that a consumer holding a [decides] hypothesis can
    hand the totality half to something that asks for it by name without
    unfolding either definition. *)
Lemma decides_implies_total : forall (C : Image) (spec : ProcInput -> Prop),
  decides C spec -> classifier_total_T C.
Proof.
  intros C spec Hdec f Hf en Hen. exact (proj2 (Hdec f Hf en Hen)).
Qed.

(** The patch-difference classifier's obligation: [C] decides, on finite
    inputs, whether BOTH patches preserved behavior.  Each original is
    compared with its patch at that pair's own role budget —
    [State.source_alloc_limit] for the first pair,
    [State.target_alloc_limit] for the second — so a patch cannot hide a
    change in allocation behavior by being judged at the other role's
    ceiling.  The spec is the CONJUNCTION, so the classifier accepts only
    where both pairs agree and fires wherever either differs. *)
Definition classifies_patch_diff_T (O1 P1 O2 P2 C : Image) : Prop :=
  decides C (fun inp => agree O1 P1 source_alloc_limit inp
                        /\ agree O2 P2 target_alloc_limit inp).

(** The good-input classifier's obligation: [C] decides, on finite
    inputs, whether the two ORIGINALS were already error-free
    equivalent.  Same shape, different question — see [good_input]. *)
Definition classifies_good_inputs_T (O1 O2 C : Image) : Prop :=
  decides C (good_input O1 O2).

(** THE GATE OF THE BUGGY / NOT-BUGGY TWO-REGION VARIANT: [C] decides,
    on finite inputs, whether the ORIGINAL is error-free on the input.
    The same [decides] shape as the two obligations above, over ONE
    image rather than a pair, because the question is about the original
    alone and not about a relation between two binaries.

    This is the whole of what the variant adds.  Each of the two slice
    programs owes [GatedSize.gated_slice_T] against [O] on its region,
    and the shipped binary owes [Equivalence.strong_universal_T] against
    [O] outright; both are existing statements, used unchanged, and
    neither pins the boundary between the regions.  This does.

    Everything [decides] demands is demanded here: totality at every
    valid entry on every valid finite input, which by
    [MustExit.must_exit_with] already means the gate itself is modeled
    and never faults, and the per-input correctness iff.  In particular
    a gate that CRASHES on the inputs it means to reject decides
    nothing ([decides_refuted_by_undecided]) — the failure mode is worth
    naming for this variant specifically, since a gate whose job is to
    find the inputs the original faults on is a gate a submission is
    tempted to write by running the original. *)
Definition classifies_error_free_inputs_T (O C : Image) : Prop :=
  decides C (error_free_input O).

(* =========================================================================
   Accept and reject as sets of finite inputs
   ========================================================================= *)

(** The classifier accepts [f]: every valid entry exits 0.  This is the
    form the measure layer quantifies over, and it is stated
    independently of [decides] on purpose — a weight bound is a claim
    about a SET of inputs, and it should not silently presuppose that the
    classifier is a decider.  Under [decides] the two readings coincide
    ([decides_accepts_iff]). *)
Definition accepts (C : Image) (f : FinProcInput) : Prop :=
  forall en,
    valid_entry C en (to_proc_input f) ->
    must_exit_with verdict_accept C classifier_alloc_limit en (to_proc_input f).

(** ... and rejects it: a valid finite input it does not accept.  The
    LARGEST reading of rejection — the negation of [accepts], rather than
    "exits 1" — so that a measure bound stated over it is self-contained
    and conservative, covering an input the classifier answers 1 on, one
    it answers inconsistently across entries, and one it fails to answer
    at all.  Under [decides] the readings collapse: totality makes the
    unanswered case impossible and [decides_rejects_iff] identifies the
    rest with [~ spec]. *)
Definition rejects (C : Image) (f : FinProcInput) : Prop :=
  valid_fin_input f /\ ~ accepts C f.

(** Acceptance is not a claim about nothing: an accepting run really
    emits [State.ExitEv] carrying [verdict_accept], by
    [MustExit.must_exit_with_realizes].  The [Run.valid_entry] hypothesis is
    what makes this a statement rather than a vacuity — see
    [accepts_vacuous_no_entries]. *)
Lemma accepts_realizes : forall C f en,
  valid_entry C en (to_proc_input f) ->
  accepts C f ->
  exists tr fs,
    bh_traces (run C classifier_alloc_limit en (to_proc_input f))
              (tr ++ [ExitEv verdict_accept fs]).
Proof.
  intros C f en Hen Ha.
  exact (must_exit_with_realizes _ _ _ _ _ (Ha en Hen)).
Qed.

(** [accepts] is refutable: one valid entry at which the classifier does
    not exit 0 is enough, which is the per-entry robustness requirement
    seen from the negative side. *)
Lemma accepts_refuted_by_entry : forall C f en,
  valid_entry C en (to_proc_input f) ->
  ~ must_exit_with verdict_accept C classifier_alloc_limit en (to_proc_input f) ->
  ~ accepts C f.
Proof.
  intros C f en Hen Hno Ha. exact (Hno (Ha en Hen)).
Qed.

(** [rejects] is ESTABLISHABLE, which is the direction the other lemmas
    about it do not supply: [decides_rejects_iff] has [decides] in
    hypothesis position and [decides_accepts_or_rejects] concludes a
    disjunction, so without this one nothing in the file ever concludes
    [rejects C f].  A single valid entry that exits 1 does it, and no
    [decides] hypothesis is needed — which matters, because the measure
    layer quantifies over [rejects] without assuming the classifier is a
    decider.  The step from "exits 1 here" to "does not accept" is
    [MustExit.must_exit_with_exclusive] against
    [verdict_accept_neq_reject]: both
    verdicts at one entry would make the two words equal. *)
Lemma rejects_by_exit1 : forall C f en,
  valid_fin_input f ->
  valid_entry C en (to_proc_input f) ->
  must_exit_with verdict_reject C classifier_alloc_limit en (to_proc_input f) ->
  rejects C f.
Proof.
  intros C f en Hf Hen H1.
  split; [exact Hf |].
  intros Ha.
  apply verdict_accept_neq_reject. symmetry.
  exact (must_exit_with_exclusive _ _ _ _ _ _ H1 (Ha en Hen)).
Qed.

(** The vacuity route at the measure layer, and the sharpest reason the
    [Equivalence.IMAGE_WF] ascription is not optional: an image with no
    valid entry ACCEPTS EVERY INPUT, so its reject set is empty and any
    weight bound over that set — including a bound of zero — holds with
    nothing whatever established about the binary.  A checker that pinned
    the classifier statements and the bounds but omitted the
    well-formedness assertion for the classifier image would be pinning
    exactly this. *)
Lemma accepts_vacuous_no_entries : forall C f,
  (forall en, ~ valid_entry C en (to_proc_input f)) -> accepts C f.
Proof.
  intros C f H en Hen. exfalso. exact (H en Hen).
Qed.

(* =========================================================================
   Transfer: what [decides] gives a consumer
   ========================================================================= *)

(** Exiting 1 IS the rejection.  This is the lemma the totality conjunct
    was added for, and it consumes both halves of [decides]: the forward
    direction goes through [MustExit.must_exit_with_exclusive], which
    turns "exits 1 and, by the iff, would also have to exit 0" into
    [verdict_accept = verdict_reject] and so into
    [verdict_accept_neq_reject]; the backward direction is where
    totality is spent, since without it [~ spec] would leave open that
    the classifier simply never answers. *)
Lemma decides_exit1_iff : forall (C : Image) (spec : ProcInput -> Prop),
  decides C spec ->
  forall f en,
    valid_fin_input f ->
    valid_entry C en (to_proc_input f) ->
    (must_exit_with verdict_reject C classifier_alloc_limit en (to_proc_input f)
     <-> ~ spec (to_proc_input f)).
Proof.
  intros C spec Hdec f en Hf Hen.
  destruct (Hdec f Hf en Hen) as [Hiff Htot].
  split.
  - intros H1 Hspec.
    apply verdict_accept_neq_reject. symmetry.
    exact (must_exit_with_exclusive _ _ _ _ _ _ H1 (proj2 Hiff Hspec)).
  - intros Hns.
    destruct Htot as [H0 | H1]; [exfalso; exact (Hns (proj1 Hiff H0)) | exact H1].
Qed.

(** The verdict does not depend on the entry: this is the entry
    robustness of [decides] read back out, and the fact a checker relies
    on when it runs the classifier once under whatever layout the kernel
    chose and treats the exit code as the answer.  It goes through
    [spec], which is entry-free by construction — that is what the
    property-side entry absorption in [agree] and [good_input] buys.

    [spec] is quantified but does not occur in the conclusion: what the
    lemma says is that SOME decided property forces uniformity, and
    which one is immaterial.  So a call site either supplies the
    [decides] hypothesis first, which determines it, or reaches for
    [eapply]; there is no form of this statement in which the verdict
    alone names the property. *)
Lemma decides_verdict_entry_uniform :
  forall (C : Image) (spec : ProcInput -> Prop) f en1 en2,
    decides C spec ->
    valid_fin_input f ->
    valid_entry C en1 (to_proc_input f) ->
    valid_entry C en2 (to_proc_input f) ->
    must_exit_with verdict_accept C classifier_alloc_limit en1 (to_proc_input f) ->
    must_exit_with verdict_accept C classifier_alloc_limit en2 (to_proc_input f).
Proof.
  intros C spec f en1 en2 Hdec Hf Hen1 Hen2 H1.
  exact (proj2 (proj1 (Hdec f Hf en2 Hen2))
               (proj1 (proj1 (Hdec f Hf en1 Hen1)) H1)).
Qed.

(** [accepts] is [spec], for a decider.  The direction from [spec] to
    [accepts] is the per-entry iff applied at each entry in turn and
    needs nothing extra; the direction from [accepts] to [spec] needs the
    entry space to be INHABITED, because [accepts] is a universal over
    valid entries and says nothing when there are none
    ([accepts_vacuous_no_entries]).

    THE HYPOTHESIS IS STATED AT THE VALID INPUTS AND NOWHERE ELSE, and
    the restriction is not caution: [Run.valid_entry] carries
    [Run.entry_stack_fits], so an input whose argv alone outruns the sp
    window has no valid entry under ANY image, and the unrestricted form
    [forall g, exists en, valid_entry C en (to_proc_input g)] is false
    for every [C] — [Checks.EntryStackFits.no_image_has_an_entry_for_every_input]
    proves exactly that.  A lemma taking the unrestricted form would be
    not merely demanding but unusable, and the proof never needed it:
    it instantiates the hypothesis only at the [f] it already holds
    [valid_fin_input] for.

    Downstream the hypothesis is discharged by the well-formedness
    assertion a checker already makes:
    [Equivalence.image_brk_satisfiable_entry] takes
    [Equivalence.image_brk_satisfiable] of the classifier image's segments
    TOGETHER WITH a [Run.valid_input] proof for the input at hand, and
    returns exactly this [exists en, valid_entry C en] — under that
    premise and not without it, which is the shape reproduced here.
    [valid_fin_input] is [Run.valid_input] of [to_proc_input], so the
    two match with no glue. *)
Lemma decides_accepts_iff : forall (C : Image) (spec : ProcInput -> Prop),
  decides C spec ->
  (forall g, valid_fin_input g -> exists en, valid_entry C en (to_proc_input g)) ->
  forall f,
    valid_fin_input f ->
    (accepts C f <-> spec (to_proc_input f)).
Proof.
  intros C spec Hdec Hinh f Hf. destruct (Hinh f Hf) as [en0 Hen0].
  split.
  - intros Hacc. exact (proj1 (proj1 (Hdec f Hf en0 Hen0)) (Hacc en0 Hen0)).
  - intros Hspec en Hen. exact (proj2 (proj1 (Hdec f Hf en Hen)) Hspec).
Qed.

(** ... and so the reject set of a decider is exactly the valid finite
    inputs outside [spec].  This is the statement the measure layer needs
    in order for a bound on [rejects] to be a bound on the classifier's
    FIRE SET as a task author understands it, rather than on the larger
    set [rejects] conservatively names.  The inhabited-entry hypothesis
    is inherited from [decides_accepts_iff] and discharged the same way.

    One step remains between this and what [Measure.weight_bound_T]
    charges for, and it is taken there rather than here: that bound is
    indexed by [FinInput.fin_core], so the set it measures is the set of
    CORES with a rejected representative.  This lemma is stated per
    record, which is the right level for it — [spec] is a predicate on
    [State.ProcInput] — and [Measure]'s header carries the argument for
    the quotient. *)
Lemma decides_rejects_iff : forall (C : Image) (spec : ProcInput -> Prop),
  decides C spec ->
  (forall g, valid_fin_input g -> exists en, valid_entry C en (to_proc_input g)) ->
  forall f,
    valid_fin_input f ->
    (rejects C f <-> valid_fin_input f /\ ~ spec (to_proc_input f)).
Proof.
  intros C spec Hdec Hinh f Hf.
  pose proof (decides_accepts_iff C spec Hdec Hinh f Hf) as Hacc.
  unfold rejects. split.
  - intros [Hf' Hna].
    split; [exact Hf' | intros Hspec; exact (Hna (proj2 Hacc Hspec))].
  - intros [Hf' Hns].
    split; [exact Hf' | intros Ha; exact (Hns (proj1 Hacc Ha))].
Qed.

(** Every valid finite input is accepted or rejected, CONSTRUCTIVELY —
    no excluded middle is used, the disjunction comes from the totality
    conjunct and the case analysis is on which verdict the classifier
    reaches.  This is what makes the reject set of a decider a set one
    can reason about finitarily, which is what the weighted-measure layer
    needs before it can sum anything — it quantifies over finite lists of
    rejected inputs, duplicate-free on [FinInput.fin_core]. *)
Lemma decides_accepts_or_rejects : forall (C : Image) (spec : ProcInput -> Prop) f,
  decides C spec ->
  (forall g, valid_fin_input g -> exists en, valid_entry C en (to_proc_input g)) ->
  valid_fin_input f ->
  accepts C f \/ rejects C f.
Proof.
  intros C spec f Hdec Hinh Hf.
  pose proof (decides_accepts_iff C spec Hdec Hinh f Hf) as Hacc.
  destruct (Hinh f Hf) as [en0 Hen0].
  destruct (proj2 (Hdec f Hf en0 Hen0)) as [H0 | H1].
  - left. apply (proj2 Hacc). exact (proj1 (proj1 (Hdec f Hf en0 Hen0)) H0).
  - right. split; [exact Hf |].
    intros Ha.
    exact (proj1 (decides_exit1_iff C spec Hdec f en0 Hf Hen0) H1
                 (proj1 Hacc Ha)).
Qed.

(* =========================================================================
   [decides] and [classifier_total_T] bite
   ========================================================================= *)

(** [classifier_total_T] BITES: one valid entry, one valid finite input,
    neither verdict, and the named obligation is false.  Stated first
    because it is the primitive fact — [decides_refuted_by_undecided]
    below is this composed with [decides_implies_total], rather than a
    second copy of the same case analysis — and because a definition
    that a checker is asked to pin should come with the statement that
    it is refutable at all.  What it is NOT is a non-vacuity proof for a
    particular image: exhibiting a binary that really reaches neither
    verdict is example-side work, and [decides_vacuous_no_entries]'
    warning applies here unchanged, in the form
    [classifier_total_T_vacuous_no_entries]. *)
Lemma classifier_total_T_refuted_by_undecided : forall (Cl : Image) f en,
  valid_fin_input f ->
  valid_entry Cl en (to_proc_input f) ->
  ~ must_exit_with verdict_accept Cl classifier_alloc_limit en (to_proc_input f) ->
  ~ must_exit_with verdict_reject Cl classifier_alloc_limit en (to_proc_input f) ->
  ~ classifier_total_T Cl.
Proof.
  intros Cl f en Hf Hen H0 H1 Htot.
  destruct (Htot f Hf en Hen) as [Hy | Hn]; [exact (H0 Hy) | exact (H1 Hn)].
Qed.

(** ... and it has [decides]' vacuity route, for [decides]' reason: the
    entry quantifier is the only thing standing between the definition
    and triviality, so an image that fails to load is TOTAL, and a
    checker pinning [classifier_total_T] on its own still owes the
    [Equivalence.IMAGE_WF] ascription for the classifier image.  Naming
    the totality half separately does not create a new hole, but it does
    create a new place to fall into the existing one. *)
Lemma classifier_total_T_vacuous_no_entries : forall (Cl : Image),
  (forall f en, ~ valid_entry Cl en (to_proc_input f)) ->
  classifier_total_T Cl.
Proof.
  intros Cl H f Hf en Hen. exfalso. exact (H f en Hen).
Qed.

(** The totality refutation.  A classifier that at one valid entry, on
    one valid finite input, reaches neither verdict — it diverges, or
    wedges, or faults, all of which [MustExit.must_exit_with] refutes —
    decides nothing, whatever [spec] is.  This is the definition-level
    form of the obligation the header argues for; the run-level
    witnesses are example-side, in the spirit of
    [Checks.Examples.run_of_undecodable_image_is_unmodeled], and an
    undecodable image is one of them since it errors immediately and so
    refutes [MustExit.must_exit_with] at every code.

    Note that [spec] is universally quantified: no property, however
    chosen, rescues a classifier that fails to answer.  A shape in which
    totality could be traded against a cleverer spec would not be a
    decision procedure.

    The proof goes through [classifier_total_T_refuted_by_undecided] and
    [decides_implies_total]: the same fact, read at the two names. *)
Lemma decides_refuted_by_undecided : forall (C : Image) (spec : ProcInput -> Prop) f en,
  valid_fin_input f ->
  valid_entry C en (to_proc_input f) ->
  ~ must_exit_with verdict_accept C classifier_alloc_limit en (to_proc_input f) ->
  ~ must_exit_with verdict_reject C classifier_alloc_limit en (to_proc_input f) ->
  ~ decides C spec.
Proof.
  intros C spec f en Hf Hen H0 H1 Hdec.
  exact (classifier_total_T_refuted_by_undecided C f en Hf Hen H0 H1
           (decides_implies_total C spec Hdec)).
Qed.

(** The correctness refutation, the other half of what [decides] claims:
    accepting an input outside [spec] refutes it.  Without this lemma's
    content the predicate could have been "always answers", with the
    property along for the ride. *)
Lemma decides_refuted_by_wrong_verdict : forall (C : Image) (spec : ProcInput -> Prop) f en,
  valid_fin_input f ->
  valid_entry C en (to_proc_input f) ->
  must_exit_with verdict_accept C classifier_alloc_limit en (to_proc_input f) ->
  ~ spec (to_proc_input f) ->
  ~ decides C spec.
Proof.
  intros C spec f en Hf Hen H0 Hns Hdec.
  exact (Hns (proj1 (proj1 (Hdec f Hf en Hen)) H0)).
Qed.

(** And the vacuity route, stated where it cannot be missed: an image
    with no valid entry decides EVERY property, including contradictory
    ones.  Nothing in this file closes that — a premise that is
    unsatisfiable is not repaired by strengthening what sits under it —
    so the [Equivalence.IMAGE_WF] ascription for the classifier image is
    part of the obligation a checker must make, not an optional extra.
    See this file's header, and [accepts_vacuous_no_entries] for the
    same hole at the measure layer. *)
Lemma decides_vacuous_no_entries : forall (C : Image) (spec : ProcInput -> Prop),
  (forall f en, ~ valid_entry C en (to_proc_input f)) -> decides C spec.
Proof.
  intros C spec H f Hf en Hen. exfalso. exact (H f en Hen).
Qed.

(* =========================================================================
   What the buggy / not-buggy gate owes, read back out
   ========================================================================= *)

(** THE REFUTATION BITE AT THE GATE.  An input the original faults on is
    an input this gate must EXIT 1 on, at every valid entry of its own —
    not merely one it is permitted to reject.  So a submission cannot
    widen its not-buggy region by pointing the gate at inputs the
    original does not survive: accepting one of them refutes the
    obligation outright ([decides_refuted_by_wrong_verdict] is the same
    fact from the other side).

    The route is [decides_exit1_iff], which is where the totality
    conjunct is spent: without it, "does not accept" would leave open a
    gate that simply never answers, and never answering is how a gate
    that decides by running the original would behave on exactly the
    inputs this lemma is about. *)
Lemma classifies_error_free_inputs_T_rejects_error :
  forall (O C : Image) f en enC,
    classifies_error_free_inputs_T O C ->
    valid_fin_input f ->
    valid_entry O en (to_proc_input f) ->
    bh_errors (run O source_alloc_limit en (to_proc_input f)) ->
    valid_entry C enC (to_proc_input f) ->
    must_exit_with verdict_reject C classifier_alloc_limit enC (to_proc_input f).
Proof.
  intros O C f en enC Hdec Hf Hen Herr HenC.
  apply (proj2 (decides_exit1_iff C (error_free_input O) Hdec f enC Hf HenC)).
  exact (error_free_input_refuted_by_error O (to_proc_input f) en Hen Herr).
Qed.

(** ... and the same fact as a REFUTATION OF ACCEPTANCE, which is the
    form a consumer of the measure layer needs: an input the original
    faults on lands in the gate's reject set, [rejects] being the
    widest reading of rejection and the one a weight bound is stated
    over.

    The step from "exits 1 here" to "does not accept" needs one valid
    entry of the gate and cannot be taken without it: with none,
    [decides_vacuous_no_entries] gives the first hypothesis for free and
    [accepts_vacuous_no_entries] makes the gate accept every input, so
    every other hypothesis holds and the conclusion is false.  That
    entry is the [Equivalence.IMAGE_WF] obligation for the gate image,
    appearing where it is actually spent. *)
Lemma classifies_error_free_inputs_T_refutes_acceptance :
  forall (O C : Image) f en enC,
    classifies_error_free_inputs_T O C ->
    valid_fin_input f ->
    valid_entry O en (to_proc_input f) ->
    bh_errors (run O source_alloc_limit en (to_proc_input f)) ->
    valid_entry C enC (to_proc_input f) ->
    rejects C f.
Proof.
  intros O C f en enC Hdec Hf Hen Herr HenC.
  split; [exact Hf |].
  intros Hacc.
  apply verdict_accept_neq_reject. symmetry.
  exact (must_exit_with_exclusive _ _ _ _ _ _
           (classifies_error_free_inputs_T_rejects_error
              O C f en enC Hdec Hf Hen Herr HenC)
           (Hacc enC HenC)).
Qed.

(** ... and the accepting direction, for completeness: an error-free
    input is one the gate must exit 0 on, again at every valid entry.
    Together with the lemma above this is what makes the gate's exit
    code a reading of the original's behavior rather than a choice the
    submission makes. *)
Lemma classifies_error_free_inputs_T_accepts_error_free :
  forall (O C : Image) f,
    classifies_error_free_inputs_T O C ->
    valid_fin_input f ->
    error_free_input O (to_proc_input f) ->
    accepts C f.
Proof.
  intros O C f Hdec Hf Hef en Hen.
  exact (proj2 (proj1 (Hdec f Hf en Hen)) Hef).
Qed.

(** THE VACUITY ROUTE'S PRICE, stated where a checker will meet it.  An
    ORIGINAL that does not load is error-free on every input
    ([error_free_input_vacuous_no_entries]), so a gate that correctly
    decides this predicate about it accepts EVERYTHING.  The whole input
    space is then the not-buggy region, the second program is never
    asked about any input, and the submission is charged for one
    program while proving nothing about the other.

    Note which image the hole is in.  [decides_vacuous_no_entries] and
    [accepts_vacuous_no_entries] are about the CLASSIFIER image failing
    to load; this one is about the ORIGINAL, and it survives a
    perfectly well-formed gate — the gate here is doing its job
    correctly.  A checker that ascribed [Equivalence.IMAGE_WF] to its
    gate images and forgot the original would be pinning exactly this,
    which is why this file's header asks for the ascription on EVERY
    image a checker names rather than on the classifiers. *)
Lemma classifies_error_free_inputs_T_vacuous_accepts_everything :
  forall (O C : Image),
    classifies_error_free_inputs_T O C ->
    (forall f en, ~ valid_entry O en (to_proc_input f)) ->
    forall f, valid_fin_input f -> accepts C f.
Proof.
  intros O C Hdec Hno f Hf.
  apply (classifies_error_free_inputs_T_accepts_error_free O C f Hdec Hf).
  apply error_free_input_vacuous_no_entries.
  intros en. exact (Hno f en).
Qed.

(* =========================================================================
   The classifier pinned to FORCED-ONLY; the property under the task's
   configuration ([Run.SpuriousCfg])
   =========================================================================

   The problem, in this file's vocabulary: [decides] asks for a
   verdict on EVERY resolution of the nondeterminism, and under the
   may-fail reading one resolution of any classifier that opens its
   input file is the environment refusing the open.  That run reaches
   neither verdict — it cannot both fail closed and report the content
   — so no content-dependent classifier satisfies [decides], whatever
   the task.  The same holds for every injected arm: [dup], [pipe2],
   [getcwd], a [getrandom] interrupted.

   The repair keeps two readings apart, deliberately:

   - THE CLASSIFIER'S OWN RUN is pinned to [Run.forced_only_cfg], for
     every family, whatever the task chose.  A classifier is asked to
     decide, so its own reads must not be refusable without cause; and
     the pin is a WEAKENING of the obligation, never a different one
     ([decides_fo_of_decides]: a decider under may-fail is a decider
     here).  These are the [_fo] names.
   - THE PROPERTY IT CLASSIFIES is evaluated under the TASK'S
     configuration, [agree_s cfg] and [good_input_s cfg], because that
     is what the task's own equivalence obligation is stated under
     ([Equivalence.SPEC_SCFG]): a patch judged under may-fail must be
     classified against may-fail agreement.  These are the [_s cfg]
     names, and [classifies_patch_diff_T_s cfg] / [classifies_good_inputs_T_s cfg]
     put the two together.

   At [Run.may_fail_cfg] the [_s] properties are the ones above
   ([agree_s_may_fail], [good_input_s_may_fail]); the [_fo] verdict is
   never the one above, by design.  Everything else — finite inputs
   only, per-entry robustness, totality, the vacuity route through an
   entry-less image — is inherited unchanged, and each lemma below is
   the [_fo] twin of the one it is named after. *)

(* -------------------------------------------------------------------------
   The classified properties, under a configuration
   ------------------------------------------------------------------------- *)

Definition agree_s (cfg : SpuriousCfg) (X Y : Image) (lim : Z) (inp : ProcInput) : Prop :=
  (forall enX enY,
     valid_entry X enX inp -> valid_entry Y enY inp ->
     trace_equiv (bh_traces (run_scfg cfg X lim enX inp))
                 (bh_traces (run_scfg cfg Y lim enY inp)))
  /\ ((exists en, valid_entry X en inp /\ bh_errors (run_scfg cfg X lim en inp))
      <-> (exists en, valid_entry Y en inp /\ bh_errors (run_scfg cfg Y lim en inp)))
  /\ ((exists en, valid_entry X en inp /\ bh_all_errors (run_scfg cfg X lim en inp))
      <-> (exists en, valid_entry Y en inp /\ bh_all_errors (run_scfg cfg Y lim en inp)))
  /\ ((exists en, valid_entry X en inp /\ bh_unmodeled (run_scfg cfg X lim en inp))
      <-> (exists en, valid_entry Y en inp /\ bh_unmodeled (run_scfg cfg Y lim en inp))).

Definition good_input_s (cfg : SpuriousCfg) (O1 O2 : Image) (inp : ProcInput) : Prop :=
  forall en1 en2,
    valid_entry O1 en1 inp -> valid_entry O2 en2 inp ->
    strong_equiv_error_free_scfg cfg O1 O2 en1 en2 inp.

Lemma agree_s_may_fail : forall X Y lim inp,
  agree_s may_fail_cfg X Y lim inp <-> agree X Y lim inp.
Proof.
  intros X Y lim inp. unfold agree_s, agree.
  assert (Htr : forall enX enY,
            trace_equiv (bh_traces (run_scfg may_fail_cfg X lim enX inp))
                        (bh_traces (run_scfg may_fail_cfg Y lim enY inp))
            <-> trace_equiv (bh_traces (run X lim enX inp))
                            (bh_traces (run Y lim enY inp))).
  { intros enX enY.
    apply trace_equiv_behavior_equiv; apply run_scfg_may_fail. }
  assert (Hfld : forall (P : behavior -> Prop) Z,
            (forall b b', behavior_equiv b b' -> (P b <-> P b')) ->
            ((exists en, valid_entry Z en inp /\ P (run_scfg may_fail_cfg Z lim en inp))
             <-> (exists en, valid_entry Z en inp /\ P (run Z lim en inp)))).
  { intros P Z HP.
    split; intros (en & Hen & Hb); exists en; (split; [exact Hen |]);
      apply (HP _ _ (run_scfg_may_fail Z lim en inp)); exact Hb. }
  pose proof (Hfld bh_errors X (fun b b' H => proj1 (proj2 H))) as HeX.
  pose proof (Hfld bh_errors Y (fun b b' H => proj1 (proj2 H))) as HeY.
  pose proof (Hfld bh_all_errors X (fun b b' H => proj1 (proj2 (proj2 H)))) as HaX.
  pose proof (Hfld bh_all_errors Y (fun b b' H => proj1 (proj2 (proj2 H)))) as HaY.
  pose proof (Hfld bh_unmodeled X (fun b b' H => proj2 (proj2 (proj2 H)))) as HuX.
  pose proof (Hfld bh_unmodeled Y (fun b b' H => proj2 (proj2 (proj2 H)))) as HuY.
  split; intros (H1 & H2 & H3 & H4);
    (split; [intros enX enY HX HY; apply Htr; exact (H1 enX enY HX HY) |]);
    (split; [tauto |]); (split; tauto).
Qed.

Lemma good_input_s_may_fail : forall O1 O2 inp,
  good_input_s may_fail_cfg O1 O2 inp <-> good_input O1 O2 inp.
Proof.
  intros O1 O2 inp. unfold good_input_s, good_input.
  split; intros H en1 en2 H1 H2; specialize (H en1 en2 H1 H2);
    apply strong_equiv_error_free_scfg_may_fail; exact H.
Qed.

Lemma agree_s_sym : forall cfg X Y lim inp,
  agree_s cfg X Y lim inp -> agree_s cfg Y X lim inp.
Proof.
  intros cfg X Y lim inp (Htr & Herr & Hall & Hun).
  split; [| split; [| split]].
  - intros enY enX HY HX tr.
    split; [exact (proj2 (Htr enX enY HX HY tr))
           | exact (proj1 (Htr enX enY HX HY tr))].
  - split; [exact (proj2 Herr) | exact (proj1 Herr)].
  - split; [exact (proj2 Hall) | exact (proj1 Hall)].
  - split; [exact (proj2 Hun) | exact (proj1 Hun)].
Qed.

(** [good_input_s] bites under every configuration, for the reason
    [good_input] does: one erroring resolution of the first original
    under [cfg], at one valid entry pair, refutes it. *)
Lemma good_input_s_refuted_by_source_error : forall cfg O1 O2 inp en1 en2,
  valid_entry O1 en1 inp ->
  valid_entry O2 en2 inp ->
  bh_errors (run_scfg cfg O1 source_alloc_limit en1 inp) ->
  ~ good_input_s cfg O1 O2 inp.
Proof.
  intros cfg O1 O2 inp en1 en2 H1 H2 Herr Hg.
  destruct (Hg en1 en2 H1 H2) as (Hef & _ & _).
  exact (error_free_unkilled_error_free _ Hef Herr).
Qed.

(* -------------------------------------------------------------------------
   The classifier obligation, pinned to forced-only
   ------------------------------------------------------------------------- *)

(** [decides] with the classifier's own run under [Run.forced_only_cfg]:
    the same two conjuncts, the same quantifiers, the verdict predicate
    [MustExit.must_exit_with_scfg forced_only_cfg] in place of
    [MustExit.must_exit_with].  [spec] is still a predicate on
    [State.ProcInput], and still evaluated wherever the task says —
    [classifies_patch_diff_T_s] and [classifies_good_inputs_T_s] pass it
    a property under the task's configuration. *)
Definition decides_fo (C : Image) (spec : ProcInput -> Prop) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en,
      valid_entry C en (to_proc_input f) ->
      (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
       <-> spec (to_proc_input f))
      /\ (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
          \/ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f)).

Definition classifier_total_T_fo (Cl : Image) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en,
      valid_entry Cl en (to_proc_input f) ->
      must_exit_with_scfg forced_only_cfg verdict_accept Cl classifier_alloc_limit en (to_proc_input f)
      \/ must_exit_with_scfg forced_only_cfg verdict_reject Cl classifier_alloc_limit en (to_proc_input f).

Lemma decides_fo_implies_total : forall (C : Image) (spec : ProcInput -> Prop),
  decides_fo C spec -> classifier_total_T_fo C.
Proof.
  intros C spec Hdec f Hf en Hen. exact (proj2 (Hdec f Hf en Hen)).
Qed.

(** The two task-facing obligations: the property under the task's
    configuration [cfg], the classifier under forced-only. *)
Definition classifies_patch_diff_T_s (cfg : SpuriousCfg) (O1 P1 O2 P2 C : Image) : Prop :=
  decides_fo C (fun inp => agree_s cfg O1 P1 source_alloc_limit inp
                           /\ agree_s cfg O2 P2 target_alloc_limit inp).

Definition classifies_good_inputs_T_s (cfg : SpuriousCfg) (O1 O2 C : Image) : Prop :=
  decides_fo C (good_input_s cfg O1 O2).

(* -------------------------------------------------------------------------
   The classifier obligation with the capability word DECLARED
   ------------------------------------------------------------------------- *)

(** [decides_fo] with the task's AT_HWCAP declaration as a hypothesis on
    the input, in the shape [Run.valid_input_hwcap_rv64gc] gives the
    equivalence layer.  THE CLASSIFIER BINARIES TAKE THE SAME PROBE as
    the binaries they classify: a classifier that reads [vlenb] to learn
    whether it has a vector unit executes, under an advertised V, a word
    the model declines ([Run.valid_input_hwcap_rv64gc]'s comment and
    [Checks.Cases.Hwcap] carry the mechanism), so its run is
    [Run.MachineUnmodeled], no [MustExit.must_exit_with_scfg] holds of it
    and the undeclared obligation is FALSE.  Declaring is how such a task
    states what it can prove.

    THE HYPOTHESIS IS ON [to_proc_input f], not on a new [FinProcInput]
    field predicate, and deliberately: [FinInput.to_proc_input] carries
    [fin_hwcap] into [in_hwcap] unchanged, so the equation here is the
    same claim [Run.valid_input_hwcap_rv64gc] makes about the input the
    equivalence layer quantifies over, and a task whose classifier
    statement and equivalence statement both declare is declaring one
    thing rather than two that happen to agree.

    [decides] -- the unconfigured obligation -- gets NO declared twin.
    Every task that needs one is stated under a configuration
    ([decides_fo_of_decides] carries a proof of the stronger one into
    this shape), so a twin there would be a definition nothing
    quantifies over. *)
Definition decides_fo_hwcap_rv64gc (C : Image) (spec : ProcInput -> Prop) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    in_hwcap (to_proc_input f) = hwcap_rv64gc ->
    forall en,
      valid_entry C en (to_proc_input f) ->
      (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
       <-> spec (to_proc_input f))
      /\ (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
          \/ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f)).

Definition decides_fo_hwcap_rv64gcv (C : Image) (spec : ProcInput -> Prop) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    in_hwcap (to_proc_input f) = hwcap_rv64gcv ->
    forall en,
      valid_entry C en (to_proc_input f) ->
      (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
       <-> spec (to_proc_input f))
      /\ (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
          \/ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f)).

(** Each declaration is a NARROWING: the undeclared obligation answers
    every input either declared one does. *)
Lemma decides_fo_hwcap_rv64gc_of_decides_fo : forall C spec,
  decides_fo C spec -> decides_fo_hwcap_rv64gc C spec.
Proof. intros C spec H f Hf _ en Hen. exact (H f Hf en Hen). Qed.

Lemma decides_fo_hwcap_rv64gcv_of_decides_fo : forall C spec,
  decides_fo C spec -> decides_fo_hwcap_rv64gcv C spec.
Proof. intros C spec H f Hf _ en Hen. exact (H f Hf en Hen). Qed.

(** …and the two are EXACTLY the undeclared obligation, because
    [valid_fin_input] IS [Run.valid_input] of the denoted input
    ([FinInput.valid_fin_input]) and its capability clause is the
    two-word disjunction.  This is what makes declaring a restriction on
    the task rather than a weakening of the checker: proving both
    declared obligations proves the undeclared one, so a task that says
    nothing about its hart is held to both readings. *)
Lemma decides_fo_hwcap_splits : forall C spec,
  decides_fo C spec
  <-> (decides_fo_hwcap_rv64gc C spec /\ decides_fo_hwcap_rv64gcv C spec).
Proof.
  intros C spec. split.
  - intros H. split;
      [ exact (decides_fo_hwcap_rv64gc_of_decides_fo C spec H)
      | exact (decides_fo_hwcap_rv64gcv_of_decides_fo C spec H) ].
  - intros (Hgc & Hgcv) f Hf en Hen.
    destruct Hf as (a & b & c & k & r & d & e & g & [Hw | Hw] & ab & v).
    + apply Hgc; try assumption.
      exact (conj a (conj b (conj c (conj k (conj r (conj d (conj e (conj g (conj (or_introl Hw) (conj ab v)))))))))).
    + apply Hgcv; try assumption.
      exact (conj a (conj b (conj c (conj k (conj r (conj d (conj e (conj g (conj (or_intror Hw) (conj ab v)))))))))).
Qed.

(** The declared obligation still implies totality on the inputs it
    speaks about, which is the half a consumer reads first. *)
Lemma decides_fo_hwcap_rv64gc_total : forall C spec f en,
  decides_fo_hwcap_rv64gc C spec ->
  valid_fin_input f ->
  in_hwcap (to_proc_input f) = hwcap_rv64gc ->
  valid_entry C en (to_proc_input f) ->
  must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
  \/ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f).
Proof. intros C spec f en H Hf Hw Hen. exact (proj2 (H f Hf Hw en Hen)). Qed.

Lemma decides_fo_hwcap_rv64gcv_total : forall C spec f en,
  decides_fo_hwcap_rv64gcv C spec ->
  valid_fin_input f ->
  in_hwcap (to_proc_input f) = hwcap_rv64gcv ->
  valid_entry C en (to_proc_input f) ->
  must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
  \/ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f).
Proof. intros C spec f en H Hf Hw Hen. exact (proj2 (H f Hf Hw en Hen)). Qed.

(** The two task-facing obligations of this section, declared.  Same
    substitution as the undeclared pair above, so a task reads down the
    column its declaration names. *)
Definition classifies_patch_diff_T_s_hwcap_rv64gc
    (cfg : SpuriousCfg) (O1 P1 O2 P2 C : Image) : Prop :=
  decides_fo_hwcap_rv64gc C (fun inp => agree_s cfg O1 P1 source_alloc_limit inp
                                        /\ agree_s cfg O2 P2 target_alloc_limit inp).

Definition classifies_patch_diff_T_s_hwcap_rv64gcv
    (cfg : SpuriousCfg) (O1 P1 O2 P2 C : Image) : Prop :=
  decides_fo_hwcap_rv64gcv C (fun inp => agree_s cfg O1 P1 source_alloc_limit inp
                                         /\ agree_s cfg O2 P2 target_alloc_limit inp).

Definition classifies_good_inputs_T_s_hwcap_rv64gc
    (cfg : SpuriousCfg) (O1 O2 C : Image) : Prop :=
  decides_fo_hwcap_rv64gc C (good_input_s cfg O1 O2).

Definition classifies_good_inputs_T_s_hwcap_rv64gcv
    (cfg : SpuriousCfg) (O1 O2 C : Image) : Prop :=
  decides_fo_hwcap_rv64gcv C (good_input_s cfg O1 O2).

Lemma classifies_patch_diff_T_s_hwcap_splits : forall cfg O1 P1 O2 P2 C,
  classifies_patch_diff_T_s cfg O1 P1 O2 P2 C
  <-> (classifies_patch_diff_T_s_hwcap_rv64gc cfg O1 P1 O2 P2 C
       /\ classifies_patch_diff_T_s_hwcap_rv64gcv cfg O1 P1 O2 P2 C).
Proof. intros. apply decides_fo_hwcap_splits. Qed.

Lemma classifies_good_inputs_T_s_hwcap_splits : forall cfg O1 O2 C,
  classifies_good_inputs_T_s cfg O1 O2 C
  <-> (classifies_good_inputs_T_s_hwcap_rv64gc cfg O1 O2 C
       /\ classifies_good_inputs_T_s_hwcap_rv64gcv cfg O1 O2 C).
Proof. intros. apply decides_fo_hwcap_splits. Qed.

(* -------------------------------------------------------------------------
   Accept and reject, pinned to forced-only
   ------------------------------------------------------------------------- *)

Definition accepts_fo (C : Image) (f : FinProcInput) : Prop :=
  forall en,
    valid_entry C en (to_proc_input f) ->
    must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f).

Definition rejects_fo (C : Image) (f : FinProcInput) : Prop :=
  valid_fin_input f /\ ~ accepts_fo C f.

(** Acceptance under the pin is still a claim about the REAL program:
    the accepting run emits [State.ExitEv] carrying [verdict_accept] in
    the UNFILTERED run, by [MustExit.must_exit_with_scfg_realizes_run].
    The filter removed resolutions; it did not invent the verdict. *)
Lemma accepts_fo_realizes : forall C f en,
  valid_entry C en (to_proc_input f) ->
  accepts_fo C f ->
  exists tr fs,
    bh_traces (run C classifier_alloc_limit en (to_proc_input f))
              (tr ++ [ExitEv verdict_accept fs]).
Proof.
  intros C f en Hen Ha.
  exact (must_exit_with_scfg_realizes_run _ _ _ _ _ _ (Ha en Hen)).
Qed.

Lemma accepts_fo_refuted_by_entry : forall C f en,
  valid_entry C en (to_proc_input f) ->
  ~ must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f) ->
  ~ accepts_fo C f.
Proof.
  intros C f en Hen Hno Ha. exact (Hno (Ha en Hen)).
Qed.

Lemma rejects_fo_by_exit1 : forall C f en,
  valid_fin_input f ->
  valid_entry C en (to_proc_input f) ->
  must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f) ->
  rejects_fo C f.
Proof.
  intros C f en Hf Hen H1.
  split; [exact Hf |].
  intros Ha.
  apply verdict_accept_neq_reject. symmetry.
  exact (must_exit_with_scfg_exclusive _ _ _ _ _ _ _ H1 (Ha en Hen)).
Qed.

Lemma accepts_fo_vacuous_no_entries : forall C f,
  (forall en, ~ valid_entry C en (to_proc_input f)) -> accepts_fo C f.
Proof.
  intros C f H en Hen. exfalso. exact (H en Hen).
Qed.

(* -------------------------------------------------------------------------
   Transfer: what [decides_fo] gives a consumer
   ------------------------------------------------------------------------- *)

Lemma decides_fo_exit1_iff : forall (C : Image) (spec : ProcInput -> Prop),
  decides_fo C spec ->
  forall f en,
    valid_fin_input f ->
    valid_entry C en (to_proc_input f) ->
    (must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f)
     <-> ~ spec (to_proc_input f)).
Proof.
  intros C spec Hdec f en Hf Hen.
  destruct (Hdec f Hf en Hen) as [Hiff Htot].
  split.
  - intros H1 Hspec.
    apply verdict_accept_neq_reject. symmetry.
    exact (must_exit_with_scfg_exclusive _ _ _ _ _ _ _ H1 (proj2 Hiff Hspec)).
  - intros Hns.
    destruct Htot as [H0 | H1]; [exfalso; exact (Hns (proj1 Hiff H0)) | exact H1].
Qed.

Lemma decides_fo_verdict_entry_uniform :
  forall (C : Image) (spec : ProcInput -> Prop) f en1 en2,
    decides_fo C spec ->
    valid_fin_input f ->
    valid_entry C en1 (to_proc_input f) ->
    valid_entry C en2 (to_proc_input f) ->
    must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en1 (to_proc_input f) ->
    must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en2 (to_proc_input f).
Proof.
  intros C spec f en1 en2 Hdec Hf Hen1 Hen2 H1.
  exact (proj2 (proj1 (Hdec f Hf en2 Hen2))
               (proj1 (proj1 (Hdec f Hf en1 Hen1)) H1)).
Qed.

(** The [_fo] twins of the three transfer lemmas, and the
    inhabited-entry hypothesis is stated AT THE VALID INPUTS here for
    the reason [decides_accepts_iff] gives at length: the unrestricted
    [forall g, exists en, valid_entry C en (to_proc_input g)] is false
    for every image
    ([Checks.EntryStackFits.no_image_has_an_entry_for_every_input]), so
    a lemma taking it would typecheck and never be applicable.  Each
    proof instantiates the hypothesis only at an [f] it already holds
    [FinInput.valid_fin_input] for. *)
Lemma decides_fo_accepts_iff : forall (C : Image) (spec : ProcInput -> Prop),
  decides_fo C spec ->
  (forall g, valid_fin_input g -> exists en, valid_entry C en (to_proc_input g)) ->
  forall f,
    valid_fin_input f ->
    (accepts_fo C f <-> spec (to_proc_input f)).
Proof.
  intros C spec Hdec Hinh f Hf. destruct (Hinh f Hf) as [en0 Hen0].
  split.
  - intros Hacc. exact (proj1 (proj1 (Hdec f Hf en0 Hen0)) (Hacc en0 Hen0)).
  - intros Hspec en Hen. exact (proj2 (proj1 (Hdec f Hf en Hen)) Hspec).
Qed.

Lemma decides_fo_rejects_iff : forall (C : Image) (spec : ProcInput -> Prop),
  decides_fo C spec ->
  (forall g, valid_fin_input g -> exists en, valid_entry C en (to_proc_input g)) ->
  forall f,
    valid_fin_input f ->
    (rejects_fo C f <-> valid_fin_input f /\ ~ spec (to_proc_input f)).
Proof.
  intros C spec Hdec Hinh f Hf.
  pose proof (decides_fo_accepts_iff C spec Hdec Hinh f Hf) as Hacc.
  unfold rejects_fo. split.
  - intros [Hf' Hna].
    split; [exact Hf' | intros Hspec; exact (Hna (proj2 Hacc Hspec))].
  - intros [Hf' Hns].
    split; [exact Hf' | intros Ha; exact (Hns (proj1 Hacc Ha))].
Qed.

Lemma decides_fo_accepts_or_rejects : forall (C : Image) (spec : ProcInput -> Prop) f,
  decides_fo C spec ->
  (forall g, valid_fin_input g -> exists en, valid_entry C en (to_proc_input g)) ->
  valid_fin_input f ->
  accepts_fo C f \/ rejects_fo C f.
Proof.
  intros C spec f Hdec Hinh Hf.
  pose proof (decides_fo_accepts_iff C spec Hdec Hinh f Hf) as Hacc.
  destruct (Hinh f Hf) as [en0 Hen0].
  destruct (proj2 (Hdec f Hf en0 Hen0)) as [H0 | H1].
  - left. apply (proj2 Hacc). exact (proj1 (proj1 (Hdec f Hf en0 Hen0)) H0).
  - right. split; [exact Hf |].
    intros Ha.
    exact (proj1 (decides_fo_exit1_iff C spec Hdec f en0 Hf Hen0) H1
                 (proj1 Hacc Ha)).
Qed.

(* -------------------------------------------------------------------------
   [decides_fo] and [classifier_total_T_fo] bite
   ------------------------------------------------------------------------- *)

Lemma classifier_total_T_fo_refuted_by_undecided : forall (Cl : Image) f en,
  valid_fin_input f ->
  valid_entry Cl en (to_proc_input f) ->
  ~ must_exit_with_scfg forced_only_cfg verdict_accept Cl classifier_alloc_limit en (to_proc_input f) ->
  ~ must_exit_with_scfg forced_only_cfg verdict_reject Cl classifier_alloc_limit en (to_proc_input f) ->
  ~ classifier_total_T_fo Cl.
Proof.
  intros Cl f en Hf Hen H0 H1 Htot.
  destruct (Htot f Hf en Hen) as [Hy | Hn]; [exact (H0 Hy) | exact (H1 Hn)].
Qed.

Lemma classifier_total_T_fo_vacuous_no_entries : forall (Cl : Image),
  (forall f en, ~ valid_entry Cl en (to_proc_input f)) ->
  classifier_total_T_fo Cl.
Proof.
  intros Cl H f Hf en Hen. exfalso. exact (H f en Hen).
Qed.

Lemma decides_fo_refuted_by_undecided : forall (C : Image) (spec : ProcInput -> Prop) f en,
  valid_fin_input f ->
  valid_entry C en (to_proc_input f) ->
  ~ must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f) ->
  ~ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f) ->
  ~ decides_fo C spec.
Proof.
  intros C spec f en Hf Hen H0 H1 Hdec.
  exact (classifier_total_T_fo_refuted_by_undecided C f en Hf Hen H0 H1
           (decides_fo_implies_total C spec Hdec)).
Qed.

Lemma decides_fo_refuted_by_wrong_verdict : forall (C : Image) (spec : ProcInput -> Prop) f en,
  valid_fin_input f ->
  valid_entry C en (to_proc_input f) ->
  must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f) ->
  ~ spec (to_proc_input f) ->
  ~ decides_fo C spec.
Proof.
  intros C spec f en Hf Hen H0 Hns Hdec.
  exact (Hns (proj1 (proj1 (Hdec f Hf en Hen)) H0)).
Qed.

Lemma decides_fo_vacuous_no_entries : forall (C : Image) (spec : ProcInput -> Prop),
  (forall f en, ~ valid_entry C en (to_proc_input f)) -> decides_fo C spec.
Proof.
  intros C spec H f Hf en Hen. exfalso. exact (H f en Hen).
Qed.

(* -------------------------------------------------------------------------
   The pin is a weakening
   ------------------------------------------------------------------------- *)

(** The filter's question is answered on every run of [C] the
    obligations quantify over: every valid finite input, every valid
    entry.  This is [MustExit.run_decided] at the classifier's own
    budget, and it is the premise under which the three lemmas below
    say that what [decides] certifies, [decides_fo] certifies too — so
    pinning the classifier to forced-only asks for LESS, never for
    something else.  See the KNOWN GAP in [Run.v]'s spurious-failure
    section for why it is a premise. *)
Definition classifier_decided (C : Image) : Prop :=
  forall f en,
    valid_fin_input f ->
    valid_entry C en (to_proc_input f) ->
    run_decided forced_only_cfg C classifier_alloc_limit en (to_proc_input f).

Lemma accepts_fo_of_accepts : forall C f,
  classifier_decided C ->
  valid_fin_input f ->
  accepts C f -> accepts_fo C f.
Proof.
  intros C f Hdec Hf Ha en Hen.
  exact (must_exit_with_scfg_of_must_exit_with _ _ _ _ _ _ (Hdec f en Hf Hen) (Ha en Hen)).
Qed.

Lemma rejects_of_rejects_fo : forall C f,
  classifier_decided C ->
  rejects_fo C f -> rejects C f.
Proof.
  intros C f Hdec (Hf & Hna).
  split; [exact Hf |]. intros Ha. exact (Hna (accepts_fo_of_accepts C f Hdec Hf Ha)).
Qed.

Lemma decides_fo_of_decides : forall (C : Image) (spec : ProcInput -> Prop),
  classifier_decided C ->
  decides C spec -> decides_fo C spec.
Proof.
  intros C spec Hdec H f Hf en Hen.
  destruct (H f Hf en Hen) as [Hiff Htot].
  pose proof (must_exit_with_scfg_of_must_exit_with forced_only_cfg verdict_accept
                C classifier_alloc_limit en (to_proc_input f) (Hdec f en Hf Hen)) as Hacc.
  pose proof (must_exit_with_scfg_of_must_exit_with forced_only_cfg verdict_reject
                C classifier_alloc_limit en (to_proc_input f) (Hdec f en Hf Hen)) as Hrej.
  split.
  - split.
    + intros Hfo. destruct Htot as [H0 | H1].
      * exact (proj1 Hiff H0).
      * exfalso. apply verdict_accept_neq_reject.
        exact (must_exit_with_scfg_exclusive _ _ _ _ _ _ _ Hfo (Hrej H1)).
    + intros Hspec. exact (Hacc (proj2 Hiff Hspec)).
  - destruct Htot as [H0 | H1]; [left; exact (Hacc H0) | right; exact (Hrej H1)].
Qed.

(* -------------------------------------------------------------------------
   The buggy / not-buggy gate, under a configuration
   ------------------------------------------------------------------------- *)

(** The [_s] twin of [error_free_input], and it is the same edit the two
    properties above take: [Run.run_scfg cfg] in place of [Run.run],
    nothing else moved.  It stays, conjunct for conjunct, the SOURCE
    SIDE of [Equivalence.strong_equiv_error_free_scfg] with the entry
    universally quantified — the relation this variant's two slice
    programs are judged by under the task's configuration — exactly as
    the unparameterized form is that of
    [Equivalence.strong_equiv_error_free].

    Which configuration this is evaluated under is the task's, not the
    gate's, for the reason this section's header gives: an original
    judged under may-fail must be sorted by may-fail error-freedom, or
    the regions would be carved by a different notion of "buggy" from
    the one the slice obligations are stated under. *)
Definition error_free_input_s (cfg : SpuriousCfg) (O : Image) (inp : ProcInput) : Prop :=
  forall en, valid_entry O en inp ->
    error_free_unkilled (run_scfg cfg O source_alloc_limit en inp).

(** At [Run.may_fail_cfg] it is the property above, which is what lets
    the unparameterized statements keep their text.  Through
    [Run.run_scfg_may_fail], the same route [agree_s_may_fail] and
    [good_input_s_may_fail] take. *)
Lemma error_free_input_s_may_fail : forall O inp,
  error_free_input_s may_fail_cfg O inp <-> error_free_input O inp.
Proof.
  intros O inp. unfold error_free_input_s, error_free_input.
  split; intros H en Hen;
    [ apply (proj1 (error_free_unkilled_scfg_may_fail O source_alloc_limit en inp))
    | apply (proj2 (error_free_unkilled_scfg_may_fail O source_alloc_limit en inp)) ];
    exact (H en Hen).
Qed.

(** Turning a family OFF cannot make an original buggy: fewer executions
    cannot add an error, so error-freedom is inherited downward from
    the may-fail reading, [Equivalence.error_free_scfg_of_error_free]
    under the entry quantifier.  The converse fails, and that is the
    point of parameterising rather than fixing a configuration — an
    original that only faults on a refused [openat] is not-buggy under
    forced-only and buggy under may-fail, and the two configurations
    therefore draw the region boundary in different places. *)
Lemma error_free_input_s_of_error_free_input : forall cfg O inp,
  error_free_input O inp -> error_free_input_s cfg O inp.
Proof.
  intros cfg O inp H en Hen.
  exact (error_free_unkilled_scfg_of_error_free_unkilled cfg O source_alloc_limit
           en inp (H en Hen)).
Qed.

(** ... and it BITES under every configuration, exactly as the
    unparameterized form does: one erroring resolution, at one valid
    entry, of the run [cfg] admits.  Which resolutions those are is what
    [cfg] decides, and that is the whole content of parameterising —
    the refutation is the same shape at every configuration and lands on
    a different set of inputs at each. *)
Lemma error_free_input_s_refuted_by_error : forall cfg O inp en,
  valid_entry O en inp ->
  bh_errors (run_scfg cfg O source_alloc_limit en inp) ->
  ~ error_free_input_s cfg O inp.
Proof.
  intros cfg O inp en Hen Herr Hef.
  exact (error_free_unkilled_error_free _ (Hef en Hen) Herr).
Qed.

(** The vacuity route survives the parameterisation untouched, because
    it runs through the ENTRY quantifier and not through the run: an
    original with no valid entry is error-free under every [cfg], having
    executed nothing.  Turning families off cannot repair an empty
    range any more than strengthening what sits under it can. *)
Lemma error_free_input_s_vacuous_no_entries : forall cfg O inp,
  (forall en, ~ valid_entry O en inp) -> error_free_input_s cfg O inp.
Proof.
  intros cfg O inp Hno en Hen. exfalso. exact (Hno en Hen).
Qed.

(** Coverage, under a configuration: [Run.run_scfg_unmodeled_errors] is
    the [_scfg] image of [Equivalence.run_unmodeled_errors], so
    error-freedom subsumes [Equivalence.modeled] here for the reason it
    does there, and [Equivalence.strong_equiv_error_free_scfg] carries
    no [Equivalence.modeled] conjunct for the same reason. *)
Lemma error_free_input_s_modeled : forall cfg O inp en,
  error_free_input_s cfg O inp ->
  valid_entry O en inp ->
  modeled (run_scfg cfg O source_alloc_limit en inp).
Proof.
  intros cfg O inp en Hef Hen Hun.
  exact (error_free_unkilled_error_free _ (Hef en Hen)
           (run_scfg_unmodeled_errors cfg O source_alloc_limit en inp Hun)).
Qed.

(** The positive relation to [good_input_s], the [_s] twin of
    [good_input_self_error_free_input] and the same one-line argument:
    instantiate both entry quantifiers at the same entry and take the
    first conjunct of [Equivalence.strong_equiv_error_free_scfg].  So
    the two gates of the family agree where they overlap under EVERY
    configuration, not only under may-fail. *)
Lemma good_input_s_self_error_free_input_s : forall cfg O inp,
  good_input_s cfg O O inp -> error_free_input_s cfg O inp.
Proof.
  intros cfg O inp Hg en Hen.
  exact (proj1 (Hg en en Hen Hen)).
Qed.

(** The task-facing obligation: the property under the task's
    configuration [cfg], the gate itself under
    [Run.forced_only_cfg].  Same split as
    [classifies_patch_diff_T_s] and [classifies_good_inputs_T_s], and
    for the same reason — a gate is asked to DECIDE, so its own reads
    must not be refusable without cause, while what it decides is the
    task's question. *)
Definition classifies_error_free_inputs_T_s (cfg : SpuriousCfg) (O C : Image) : Prop :=
  decides_fo C (error_free_input_s cfg O).

(* -------------------------------------------------------------------------
   The buggy / not-buggy gate, pinned to forced-only
   ------------------------------------------------------------------------- *)

(** THE FORCED-ONLY TWIN, with the unparameterized property: the gate's
    own run pinned to [Run.forced_only_cfg] through [decides_fo], the
    property left at [error_free_input].  This is the name a checker
    emits when it states the gate obligation without carrying the task's
    configuration into it.

    It is NOT a third reading.  [classifies_error_free_inputs_T_fo_iff_s_may_fail]
    below shows it is exactly [classifies_error_free_inputs_T_s] at
    [Run.may_fail_cfg] — the two differ only in how the property is
    spelled, and [error_free_input_s_may_fail] identifies those.  The
    name exists because a consumer that has no configuration to pass
    should not have to pass [Run.may_fail_cfg] and then rewrite.

    ONE ASYMMETRY IS WORTH NAMING because a reader will look for it.
    Neither [classifies_patch_diff_T] nor [classifies_good_inputs_T] has
    a [_fo] name; those two kinds carry the plain and the [_s cfg] forms
    only.  Nothing here argues they should not have one — this file
    simply does not add names to definitions it is not changing. *)
Definition classifies_error_free_inputs_T_fo (O C : Image) : Prop :=
  decides_fo C (error_free_input O).

(** The declared twins of the two gate obligations, in the shape the
    section above gives the patch-classifier ones.  Same reason: a gate
    binary that probes for a vector unit is unmodeled under an advertised
    V, so the undeclared obligation is false for it and the declared one
    is what such a task can prove. *)
Definition classifies_error_free_inputs_T_s_hwcap_rv64gc
    (cfg : SpuriousCfg) (O C : Image) : Prop :=
  decides_fo_hwcap_rv64gc C (error_free_input_s cfg O).

Definition classifies_error_free_inputs_T_s_hwcap_rv64gcv
    (cfg : SpuriousCfg) (O C : Image) : Prop :=
  decides_fo_hwcap_rv64gcv C (error_free_input_s cfg O).

Definition classifies_error_free_inputs_T_fo_hwcap_rv64gc (O C : Image) : Prop :=
  decides_fo_hwcap_rv64gc C (error_free_input O).

Definition classifies_error_free_inputs_T_fo_hwcap_rv64gcv (O C : Image) : Prop :=
  decides_fo_hwcap_rv64gcv C (error_free_input O).

Lemma classifies_error_free_inputs_T_s_hwcap_splits : forall cfg O C,
  classifies_error_free_inputs_T_s cfg O C
  <-> (classifies_error_free_inputs_T_s_hwcap_rv64gc cfg O C
       /\ classifies_error_free_inputs_T_s_hwcap_rv64gcv cfg O C).
Proof. intros. apply decides_fo_hwcap_splits. Qed.

Lemma classifies_error_free_inputs_T_fo_hwcap_splits : forall O C,
  classifies_error_free_inputs_T_fo O C
  <-> (classifies_error_free_inputs_T_fo_hwcap_rv64gc O C
       /\ classifies_error_free_inputs_T_fo_hwcap_rv64gcv O C).
Proof. intros. apply decides_fo_hwcap_splits. Qed.

(** The identification just claimed, and it is a clean [iff] rather than
    an implication: both sides are [decides_fo] of the SAME classifier
    at the SAME budget, differing only in the property, and
    [error_free_input_s_may_fail] is itself an [iff].  Nothing about the
    gate's own run has to move, which is why no [classifier_decided]
    premise appears here and does appear below. *)
Lemma classifies_error_free_inputs_T_fo_iff_s_may_fail : forall O C,
  classifies_error_free_inputs_T_fo O C
  <-> classifies_error_free_inputs_T_s may_fail_cfg O C.
Proof.
  intros O C. unfold classifies_error_free_inputs_T_fo,
    classifies_error_free_inputs_T_s, decides_fo.
  split; intros H f Hf en Hen; destruct (H f Hf en Hen) as [Hiff Htot];
    (split; [| exact Htot]); split.
  - intros Hacc.
    exact (proj2 (error_free_input_s_may_fail O (to_proc_input f)) (proj1 Hiff Hacc)).
  - intros Hs.
    exact (proj2 Hiff (proj1 (error_free_input_s_may_fail O (to_proc_input f)) Hs)).
  - intros Hacc.
    exact (proj1 (error_free_input_s_may_fail O (to_proc_input f)) (proj1 Hiff Hacc)).
  - intros Hs.
    exact (proj2 Hiff (proj2 (error_free_input_s_may_fail O (to_proc_input f)) Hs)).
Qed.

(** The pin is a WEAKENING, which is the property the whole [_fo] layer
    is built to have: a gate that decides under may-fail decides under
    forced-only, given the filter's question answered on every run the
    obligation quantifies over.  [decides_fo_of_decides] carries it
    unchanged — the property does not move, only the gate's own run —
    and the [classifier_decided] premise is the same one
    [accepts_fo_of_accepts] and [rejects_of_rejects_fo] need.  The KNOWN
    GAP in [Run.v]'s spurious-failure section says why it is a premise
    rather than a theorem. *)
Lemma classifies_error_free_inputs_T_fo_of_unparameterized : forall O C,
  classifier_decided C ->
  classifies_error_free_inputs_T O C ->
  classifies_error_free_inputs_T_fo O C.
Proof.
  intros O C Hcd Hdec.
  exact (decides_fo_of_decides C (error_free_input O) Hcd Hdec).
Qed.

(** ... and the [_s] form at [Run.may_fail_cfg] is that composed with
    the identification above, rather than a second case analysis.
    Stated separately because it is the shape a consumer holding a
    configuration reaches for. *)
Lemma classifies_error_free_inputs_T_s_may_fail_of_unparameterized :
  forall O C,
    classifier_decided C ->
    classifies_error_free_inputs_T O C ->
    classifies_error_free_inputs_T_s may_fail_cfg O C.
Proof.
  intros O C Hcd Hdec.
  exact (proj1 (classifies_error_free_inputs_T_fo_iff_s_may_fail O C)
           (classifies_error_free_inputs_T_fo_of_unparameterized O C Hcd Hdec)).
Qed.

(* -------------------------------------------------------------------------
   What the configured and forced-only gates owe, read back out
   ------------------------------------------------------------------------- *)

(** THE REFUTATION BITE, at the task-facing obligation.  An input the
    original faults on UNDER [cfg] is an input the gate must exit 1 on,
    at every valid entry of its own.  The [_s] twin of
    [classifies_error_free_inputs_T_rejects_error], through
    [decides_fo_exit1_iff], and the same place the totality conjunct is
    spent.

    Read the two configurations in the statement: the erroring run is
    the ORIGINAL's, under [cfg], at [State.source_alloc_limit]; the
    verdict is the GATE's, under [Run.forced_only_cfg], at
    [classifier_alloc_limit].  They are different runs of different
    images under different configurations, and the obligation is exactly
    the claim that the second tracks the first. *)
Lemma classifies_error_free_inputs_T_s_rejects_error :
  forall cfg (O C : Image) f en enC,
    classifies_error_free_inputs_T_s cfg O C ->
    valid_fin_input f ->
    valid_entry O en (to_proc_input f) ->
    bh_errors (run_scfg cfg O source_alloc_limit en (to_proc_input f)) ->
    valid_entry C enC (to_proc_input f) ->
    must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit enC
      (to_proc_input f).
Proof.
  intros cfg O C f en enC Hdec Hf Hen Herr HenC.
  apply (proj2 (decides_fo_exit1_iff C (error_free_input_s cfg O) Hdec f enC Hf HenC)).
  exact (error_free_input_s_refuted_by_error cfg O (to_proc_input f) en Hen Herr).
Qed.

(** ... and as a refutation of acceptance, which is the reading the
    measure layer sums over: [rejects_fo] is [FinInput.valid_fin_input]
    with the negation of [accepts_fo].  One valid entry of the gate is
    needed and cannot be dropped, for [accepts_fo_vacuous_no_entries]'s
    reason. *)
Lemma classifies_error_free_inputs_T_s_refutes_acceptance :
  forall cfg (O C : Image) f en enC,
    classifies_error_free_inputs_T_s cfg O C ->
    valid_fin_input f ->
    valid_entry O en (to_proc_input f) ->
    bh_errors (run_scfg cfg O source_alloc_limit en (to_proc_input f)) ->
    valid_entry C enC (to_proc_input f) ->
    rejects_fo C f.
Proof.
  intros cfg O C f en enC Hdec Hf Hen Herr HenC.
  split; [exact Hf |].
  intros Hacc.
  apply verdict_accept_neq_reject. symmetry.
  exact (must_exit_with_scfg_exclusive _ _ _ _ _ _ _
           (classifies_error_free_inputs_T_s_rejects_error
              cfg O C f en enC Hdec Hf Hen Herr HenC)
           (Hacc enC HenC)).
Qed.

(** The accepting direction.  Together with the two above this is what
    makes the configured gate's exit code a reading of the original's
    behavior UNDER THAT CONFIGURATION rather than a choice the
    submission makes. *)
Lemma classifies_error_free_inputs_T_s_accepts_error_free :
  forall cfg (O C : Image) f,
    classifies_error_free_inputs_T_s cfg O C ->
    valid_fin_input f ->
    error_free_input_s cfg O (to_proc_input f) ->
    accepts_fo C f.
Proof.
  intros cfg O C f Hdec Hf Hef en Hen.
  exact (proj2 (proj1 (Hdec f Hf en Hen)) Hef).
Qed.

(** THE VACUITY ROUTE'S PRICE, under a configuration, and the answer is
    the same at every [cfg] because the route runs through the entry
    quantifier: an ORIGINAL that does not load is error-free everywhere,
    so a gate that decides correctly about it accepts the whole input
    space, the second program of the split is never asked anything, and
    the submission is charged for one program while proving nothing
    about the other.

    The hole is in the ORIGINAL, not the gate, which is what
    [decides_fo_vacuous_no_entries] and [accepts_fo_vacuous_no_entries]
    are about; this survives a perfectly well-formed gate doing its job
    correctly. *)
Lemma classifies_error_free_inputs_T_s_vacuous_accepts_everything :
  forall cfg (O C : Image),
    classifies_error_free_inputs_T_s cfg O C ->
    (forall f en, ~ valid_entry O en (to_proc_input f)) ->
    forall f, valid_fin_input f -> accepts_fo C f.
Proof.
  intros cfg O C Hdec Hno f Hf.
  apply (classifies_error_free_inputs_T_s_accepts_error_free cfg O C f Hdec Hf).
  apply error_free_input_s_vacuous_no_entries.
  intros en. exact (Hno f en).
Qed.

(** The four bites at the [_fo] name, each the [Run.may_fail_cfg]
    instance of the one above it through
    [classifies_error_free_inputs_T_fo_iff_s_may_fail].  They are stated
    rather than left to the reader because the [_fo] form is a name a
    checker emits, and a definition a consumer is asked to pin should
    carry its own refutations under that name instead of through a
    rewrite the consumer has to find. *)
Lemma classifies_error_free_inputs_T_fo_rejects_error :
  forall (O C : Image) f en enC,
    classifies_error_free_inputs_T_fo O C ->
    valid_fin_input f ->
    valid_entry O en (to_proc_input f) ->
    bh_errors (run O source_alloc_limit en (to_proc_input f)) ->
    valid_entry C enC (to_proc_input f) ->
    must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit enC
      (to_proc_input f).
Proof.
  intros O C f en enC Hdec Hf Hen Herr HenC.
  apply (proj2 (decides_fo_exit1_iff C (error_free_input O) Hdec f enC Hf HenC)).
  exact (error_free_input_refuted_by_error O (to_proc_input f) en Hen Herr).
Qed.

Lemma classifies_error_free_inputs_T_fo_refutes_acceptance :
  forall (O C : Image) f en enC,
    classifies_error_free_inputs_T_fo O C ->
    valid_fin_input f ->
    valid_entry O en (to_proc_input f) ->
    bh_errors (run O source_alloc_limit en (to_proc_input f)) ->
    valid_entry C enC (to_proc_input f) ->
    rejects_fo C f.
Proof.
  intros O C f en enC Hdec Hf Hen Herr HenC.
  split; [exact Hf |].
  intros Hacc.
  apply verdict_accept_neq_reject. symmetry.
  exact (must_exit_with_scfg_exclusive _ _ _ _ _ _ _
           (classifies_error_free_inputs_T_fo_rejects_error
              O C f en enC Hdec Hf Hen Herr HenC)
           (Hacc enC HenC)).
Qed.

Lemma classifies_error_free_inputs_T_fo_accepts_error_free :
  forall (O C : Image) f,
    classifies_error_free_inputs_T_fo O C ->
    valid_fin_input f ->
    error_free_input O (to_proc_input f) ->
    accepts_fo C f.
Proof.
  intros O C f Hdec Hf Hef en Hen.
  exact (proj2 (proj1 (Hdec f Hf en Hen)) Hef).
Qed.

Lemma classifies_error_free_inputs_T_fo_vacuous_accepts_everything :
  forall (O C : Image),
    classifies_error_free_inputs_T_fo O C ->
    (forall f en, ~ valid_entry O en (to_proc_input f)) ->
    forall f, valid_fin_input f -> accepts_fo C f.
Proof.
  intros O C Hdec Hno f Hf.
  apply (classifies_error_free_inputs_T_fo_accepts_error_free O C f Hdec Hf).
  apply error_free_input_vacuous_no_entries.
  intros en. exact (Hno f en).
Qed.
