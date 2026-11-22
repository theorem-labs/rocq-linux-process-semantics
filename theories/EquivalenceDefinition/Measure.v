(** * EquivalenceDefinition.Measure — weighted measure of the fire set

    TRUST BOUNDARY: this file is part of the trusted specification.
    Proof files never edit it.  A top-level check that ascribes against
    a module type carrying [weight_bound_T] depends on the definitions
    here remaining fixed, exactly as the baseline check depends on
    [Equivalence].

    [Classifier.rejects] names a SET of finite inputs — the ones a
    classifier does not accept — with no size on it.  A task
    that asks "how much of the input space does the classifier reject"
    needs a way to add sizes up, and this file is that: a
    task-supplied WEIGHT on [FinInput.FinProcInput], and the claim that
    no finite list of rejected inputs with pairwise distinct CORES sums
    past a stated multiple of a declared total.  Cores, not records: the
    reason is the third section below, and it is the difference between
    an obligation and an unsatisfiable one.

    ** First use of [QArith] in this tree, and what that changes

    Every numeric quantity elsewhere in this development is a
    bitvector or a [Z]; sizes, codes, budgets, all decided by
    [vm_compute; reflexivity] against a concrete value.  [Q]'s
    propositional equality for that idiom is [Qeq] (written [==]), NOT
    Leibniz [eq]: two [Q] values built from different
    numerator/denominator pairs can be [Qeq] without being [eq], so
    [vm_compute; reflexivity] on a `_ = _ : Prop` goal over [Q] is not
    merely slow, it is the wrong tool — it can fail on values a reader
    would call equal, or (worse) succeed only for a syntactically
    particular representative.  This layer keeps to what stays true
    under [Qeq] as much as under [eq]: the obligation and every bound it
    states are [Qle] facts ([weight_bound_T] itself, and the three
    transport lemmas below), the one equality it states is a [Qeq] and
    not an [eq] ([sum_weights_ext]), nothing here decides a [Q] equality
    by computation, and a downstream consumer that wants to show a
    submitted bound to a reader PRINTS the [Q] value rather than
    comparing it against one.  [weight_bound_refutable]'s proof
    does reach for [vm_compute], and that is not a contradiction of the
    warning above: it runs on a [Qle_bool] fact — a BOOLEAN, where the
    [Qeq] question is already collapsed away by [Qle_bool]'s
    definition — reducing it to a literal [true] or [false] and
    closing with [discriminate], never on a [Q] equality of open or
    checker-supplied terms the way the forbidden pattern would.

    ** [NoDup] is Leibniz equality ON CORES, and both halves are load-bearing

    [weight_bound_T] quantifies over lists whose CORES are
    duplicate-free — [List.NoDup] applied to [List.map
    FinInput.fin_core l], with [List.NoDup]'s ordinary,
    Leibniz-equality reading, nothing custom.  [List.NoDup] is
    written qualified throughout this file rather than bare [NoDup]
    for the reason [Checks.DispatchSurface.nodup_of_listed_once]'s
    comment already gives: [stdpp], in scope here through [BvBase],
    shadows the standard library's [NoDup] with one of its own, so an
    unqualified [NoDup] would silently pick up the wrong predicate.

    *** Why cores, and not records: the record reading is unprovable

    [FinInput.FinProcInput] carries seven fields the classifier is not
    obliged to look at — [fin_uid], [fin_gid], [fin_groups], [fin_net],
    [fin_nofile], [fin_sigmask], [fin_hwcap] — and two of them range
    over infinitely many values a valid input may take
    ([in_groups] is a [list word] of any length, bounded where
    [Kernel.Groups.getgroups_spec] reads it rather than in
    [Run.valid_input]; [in_net] is any [State.NetQueue]).  The other
    five are words, so their fibres are finite before any clause is
    read, and each is narrowed further by one: [Run.valid_creds] for
    [fin_uid] and [fin_gid], [Run.valid_nofile] for [fin_nofile],
    [Run.valid_sigmask] for [fin_sigmask], and [Run.valid_hwcap] for
    [fin_hwcap], which it cuts down to exactly two values.  None of
    that weakens the argument: one infinite fibre is all this needs.
    A classifier whose behavior does not depend on the launch
    environment therefore rejects either ALL of a core's launch
    environments or none of them.  That is a claim about the PROGRAM,
    not a consequence of any definition here, and it takes more than
    "issues no credential or network syscall": TWO of the seven are
    published on the initial stack, [in_uid] as AT_UID and AT_EUID and
    [in_hwcap] as AT_HWCAP ([StackLayout.auxv_entries], filled from the
    run's [State.in_uid] and [State.in_hwcap] by
    [Run.init_machine_state]), so a program can read the launching user,
    and the hart's extension mask, with no syscall at all.  The
    condition is the whole of it — no credential, network or
    signal-mask syscall AND no read of AT_UID/AT_EUID or AT_HWCAP off
    the initial stack.  [fin_gid], [fin_groups], [fin_net],
    [fin_nofile] and [fin_sigmask] reach a program only through
    syscalls; [fin_uid] and [fin_hwcap] do not.

    Read [NoDup] on the record and the obligation dies on contact with a
    nonempty reject set.  One rejected input yields the infinite family
    of [FinInput.fin_core_fibre_infinite]: pairwise distinct, hence
    [List.NoDup]; every member as VALID as the original, since
    [Run.valid_input] reads nothing the family varies (the lemma carries
    that conjunct); hence admissible lists of every length, every member
    rejected.  Any weight blind to the launch environment — which every
    weight this layer motivates is, and which [DISTRIBUTION]'s
    [w_core_blind] later makes an obligation — gives each member the
    same value, so if that value is positive the partial sums grow
    without bound and NO [b] can bound them; a task with a nonempty fire
    set and a weight positive on it could not prove [weight_bound_T] at
    any [b] whatever.  That is not a demanding
    obligation, it is an unsatisfiable one, and an unsatisfiable
    obligation is a worse failure than a vacuous one — the vacuous kind
    at least admits the submissions it should.

    Quotienting by the launch environment is the fix: the fire set this
    layer measures is a set of CORES, a core is bad when any of its
    representatives is rejected, and each core is charged once.
    [FinInput.fin_core_env_eq] pins that the core forgets the launch
    environment and nothing else, and [w_core_blind] is what makes the
    per-core charge well defined.

    *** Why Leibniz equality on cores is honest

    The core cannot hold two DIFFERENT representations of what a real
    input would consider the same value.  Three of its four fields are
    lists — of [byte] (itself [bv 8], a stdpp record carrying a
    well-formedness field, not a bare integer) and of byte strings — and
    Leibniz equality on them is honest too, but not because they are
    "plain": two bytes of the same value are Leibniz-equal only via
    proof irrelevance on that well-formedness field, through stdpp's
    [bv_eq].  The fourth field is an [Fs.Fs] that reaches this record
    only through [Classifier.rejects] and
    [FinInput.valid_fin_input], both of which factor through
    [Run.valid_input] and so require [Fs.valid_fs] of the embedded file
    system.  It is [Fs.valid_fs] that pins the canonical,
    strictly-sorted form among its conjuncts — that is an attribute of
    [Fs.valid_fs], not an assumption made here — and without it a single
    directory could arrive under two unequal-but-equivalent [Fs.Fs]
    values, letting [NoDup] undercount duplicates that are really the
    same rejected input.

    *** What the quotient costs

    Stated plainly, because it is a WEAKENING and this file's register
    is where such things get said out loud.  [List.NoDup (List.map
    fin_core l)] implies [List.NoDup l] ([List.NoDup_map_inv]) and not
    conversely, so the hypothesis is strictly STRONGER and the
    obligation therefore asks about strictly FEWER lists: every list the
    new obligation covers was already covered by the record-indexed one,
    and lists that repeat a core are no longer asked about at all.  The
    bound is retained on exactly the lists with pairwise distinct cores
    and dropped on exactly the ones that repeat a core.  Which is the
    whole point — those dropped lists are the ones that made the
    record-indexed reading unsatisfiable — but it does mean this
    obligation does NOT imply the record-indexed one, and no reader
    should take it as doing so.  A task whose classifier genuinely
    varied its verdict with the credentials or the network would have
    its extra rejections charged at most once per core here.  That is
    the price of having an obligation at all, and the reject-set reading
    it buys — bad CORE, not bad record — is the one a task author means
    when they say "how much of the input space does this fire on".

    ** A finite partial sum, not a series

    "The measure of the fire set is at most [b] times the total [M]"
    is read here in its most literal, finitary form: for every finite
    list of rejected inputs actually exhibited, no two sharing a core,
    the weights already summed do not exceed [b * M].  There is no limit,
    no infinite series, no normalization obligation tying [M] to 1 —
    [M] is trusted metadata a [DISTRIBUTION] declares alongside its
    weight function [w], never itself proved from anything here.  [b]
    is chosen by the submission, not by this file; [weight_bound_mono]
    is what makes every [b'] at least as large as a proven [b]
    provable too, which is the fact that lets a checker trust a printed
    [b] as an upper-bound claim rather than an exact one. *)

From Stdlib Require Import ZArith NArith List QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State StackLayout Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   Summing weights over a list of inputs
   ========================================================================= *)

(** The sum of [w] over [l], zero on the empty list.  Plain
    [fold_right] over rational addition — the fold itself would
    typecheck over any element type, so the reason
    [FinInput.FinProcInput] exists rather than [State.ProcInput] is not
    this recursion but the WEIGHT FUNCTION [w] it applies: [w] must
    compute, a structural recursion over the input bytes that a
    coinductive [State.InputStream] rules out, and its representation
    must be canonical — both per [FinInput]'s header. *)
Definition sum_weights (w : FinProcInput -> Q) (l : list FinProcInput) : Q :=
  fold_right (fun f acc => (w f + acc)%Q) 0%Q l.

(** The two computation rules, by conversion.  They are stated rather
    than left to [cbn] so that a proof about a weight can [rewrite] its
    way through a list without unfolding the definition, which is what
    keeps [sum_weights_ext] below a three-line induction. *)
Lemma sum_weights_nil : forall w, sum_weights w [] = 0%Q.
Proof. reflexivity. Qed.

Lemma sum_weights_cons : forall w f l,
  sum_weights w (f :: l) = (w f + sum_weights w l)%Q.
Proof. reflexivity. Qed.

(** [sum_weights] respects pointwise [Qeq] in the WEIGHT.  It belongs
    here rather than in a proof file because it is a fact about this
    file's own definition and mentions nothing else, and because
    [weight_bound_qeq] below — which transports [M] and [b] and says
    nothing about [w] — would otherwise be the only transport this layer
    offers, leaving the [w] direction to be re-proved by every consumer
    that needs it.  Stating it changes no definition and adds no
    obligation: this file's trust boundary is [sum_weights],
    [weight_bound_T] and [DISTRIBUTION], and none of the three moves. *)
Lemma sum_weights_ext : forall (w1 w2 : FinProcInput -> Q) l,
  (forall f, (w1 f == w2 f)%Q) ->
  (sum_weights w1 l == sum_weights w2 l)%Q.
Proof.
  intros w1 w2 l Hext. induction l as [| f l IH]; [reflexivity |].
  rewrite !sum_weights_cons, IH, (Hext f). reflexivity.
Qed.

(* =========================================================================
   The weight-bound obligation
   ========================================================================= *)

(** [C]'s rejected inputs never weigh more than [b] times the declared
    total [M], as witnessed by every finite duplicate-free sample:
    for ANY list all of whose entries [Classifier.rejects] under [C] and
    whose CORES are duplicate-free, the sum does not exceed [b * M].
    Universal over the list, not existential over one — a submission
    cannot pick a favorable sample, because the statement has to hold for
    every one, including the largest core-duplicate-free list a reader
    can exhibit.

    Duplicate-freedom is read on [FinInput.fin_core], not on the record:
    each core is charged at most once, however many launch environments
    it is offered under.  The header argues why at length; the short
    version is that reading it on the record makes the bound unprovable
    the moment anything is rejected.  Note which way this cuts — it is a
    strictly STRONGER hypothesis than [List.NoDup l]
    ([List.NoDup_map_inv]), so this is a weaker obligation than the
    record-indexed one would be, deliberately.

    That strength has one hole, and it is not this file's to close: an
    image [C] with no valid entry at all makes [Classifier.accepts]
    hold of every input vacuously
    ([Classifier.accepts_vacuous_no_entries]), which empties the
    reject set and makes [weight_bound_T C w M 0] — and so every
    larger [b], by [weight_bound_mono] — provable for ANY [w] and
    [M], said nothing about.  [Classifier]'s header names this route
    and its remedy: a consuming checker must ascribe
    [Equivalence.IMAGE_WF] to every image it names, [C] included, which
    is what keeps this statement from being satisfied by a classifier
    that was never a valid program. *)
Definition weight_bound_T (C : Image) (w : FinProcInput -> Q) (M b : Q) : Prop :=
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (forall f, In f l -> rejects C f) ->
    (sum_weights w l <= b * M)%Q.

(* =========================================================================
   The declared distribution
   ========================================================================= *)

(** A task-supplied weight function and total, sealed as a module type
    so that they arrive by INSTANTIATION rather than by definition here.
    The instantiation is TRUSTED METADATA SUPPLIED WITH THE TASK, not
    something the submission chooses — [PatchClassifySpec]'s header says
    the same thing and is the authority on it.  The distinction is
    load-bearing rather than editorial: [DISTRIBUTION] constrains [w]
    only by [w_nonneg] and [w_core_blind], both of which
    [fun _ => 0%Q] satisfies, so a submission free to pick [w] could
    discharge [weight_bound_T] at [b = 0] for any classifier whatever
    and the two bounds in [SPEC_PATCH_CLASSIFY] would measure nothing.
    Inside a module type these names do not collide
    with anything else declared in this file or in a consumer that
    imports both; a consumer refers to them module-qualified, as [W.w]
    and [W.M] for a module [W : DISTRIBUTION].

    [w_core_blind] is what makes the per-core charge in
    [weight_bound_T] WELL DEFINED: the bound counts each
    [FinInput.fin_core] once, so a weight that could tell two records
    with the same core apart would leave "the weight of a core"
    ambiguous, and which representative the list happened to name would
    change the sum.  The obligation is trivial for any real weight
    function — it recurses over argv, envp, the file system and standard
    input, which is precisely the core (see [FinInput]'s record) — but it
    is stated rather than assumed, because "the natural ones all satisfy
    it" is not something this file can check.  Note it is blindness to
    the whole LAUNCH ENVIRONMENT, credentials as well as network: a
    weight peeking at [FinInput.fin_uid] is as ill-defined here as one
    peeking at [FinInput.fin_net]. *)
Module Type DISTRIBUTION.
  Parameter w : FinProcInput -> Q.
  Parameter M : Q.
  Parameter w_nonneg : forall f, (0 <= w f)%Q.
  (* [weight_bound_mono] needs this and cannot get it from [w_nonneg]:
     [M] is declared, not summed, so nothing here forces it to agree in
     sign with the weights it is the total of.  Without it a consumer
     holding a [W : DISTRIBUTION] has nothing to discharge that
     hypothesis with, and [PatchClassifySpec]'s reading of a printed [b]
     as an upper bound rests on exactly that lemma. *)
  Parameter M_nonneg : (0 <= M)%Q.
  Parameter w_core_blind :
    forall f g, fin_core f = fin_core g -> (w f == w g)%Q.
End DISTRIBUTION.

(* =========================================================================
   Monotonicity
   ========================================================================= *)

(** A bound proved at [b] is a bound at any larger [b'], given [M]
    nonnegative: [sum_weights w l <= b * M <= b' * M] by transitivity,
    where the second step needs [0 <= M] because multiplying an
    inequality by a possibly-negative quantity can flip it. *)
Lemma weight_bound_mono : forall C w M b b',
  (0 <= M)%Q -> (b <= b')%Q ->
  weight_bound_T C w M b -> weight_bound_T C w M b'.
Proof.
  intros C w M b b' HM Hbb' Hbound l Hnd Hall.
  eapply Qle_trans.
  - exact (Hbound l Hnd Hall).
  - apply Qmult_le_compat_r; assumption.
Qed.

(** [weight_bound_T] transports along [Qeq] in [M] and [b] together: a
    submission's [1#2] and a checker's [2#4] name the same bound.  This
    is what cashes in the header's claim that the layer "stays true
    under [Qeq] as much as under [eq]" — [Qle_comp]'s [Proper] instance
    lets [rewrite] carry the fact across both equations at once, so no
    consumer has to hand-roll the transport per problem. *)
Lemma weight_bound_qeq : forall C w M M' b b',
  (M == M')%Q -> (b == b')%Q ->
  weight_bound_T C w M b -> weight_bound_T C w M' b'.
Proof.
  intros C w M M' b b' HM Hb Hbound l Hnd Hall.
  specialize (Hbound l Hnd Hall).
  rewrite HM, Hb in Hbound.
  exact Hbound.
Qed.

(** The third transport, and the one the other two do not give: a
    pointwise [Qeq] change of the WEIGHT.  [weight_bound_mono] moves
    [b], [weight_bound_qeq] moves [M] and [b], and neither says anything
    about [w] — so without this a submission that proved its bound for
    one representative of a weight would have to re-prove it for every
    other, which is the situation the header's [Qeq]-not-[eq] warning
    describes.  The classifier, the mass and the multiplier are
    untouched here; only the weight moves, and it moves within one
    [Qeq] class. *)
Lemma weight_bound_T_ext : forall C w1 w2 M b,
  (forall f, (w1 f == w2 f)%Q) ->
  weight_bound_T C w1 M b -> weight_bound_T C w2 M b.
Proof.
  intros C w1 w2 M b Hext Hbound l Hnd Hall.
  rewrite <- (sum_weights_ext w1 w2 l Hext).
  exact (Hbound l Hnd Hall).
Qed.

(* =========================================================================
   [weight_bound_T] bites
   ========================================================================= *)

(** The bound [1] at unit weight and total [1] fails as soon as two
    inputs with DISTINCT CORES are both rejected: the two-element list
    [[f1; f2]] has duplicate-free cores and sums to [2], and [2 <= 1 * 1]
    is false.  This is the definition-level refutation — a
    [weight_bound_T] claim is a real restriction on the size of the
    reject set, not a statement every distribution and every classifier
    satisfies trivially.

    The hypothesis is [fin_core f1 <> fin_core f2] rather than
    [f1 <> f2], and the strengthening is exactly the content of the
    quotient: two rejected records that differ only in their launch
    environment no longer refute anything, because the obligation never
    charged for the second one.  A witness pair must now differ in argv,
    envp, the file system or standard input — which is the pair a reader
    would have had in mind anyway. *)
Lemma weight_bound_refutable : forall C f1 f2,
  rejects C f1 -> rejects C f2 -> fin_core f1 <> fin_core f2 ->
  ~ weight_bound_T C (fun _ => 1%Q) 1%Q 1%Q.
Proof.
  intros C f1 f2 Hr1 Hr2 Hne Hbound.
  assert (Hnd : List.NoDup (List.map fin_core [f1; f2])).
  { cbn [List.map].
    apply List.NoDup_cons.
    - intros Hin. destruct Hin as [Heq | Hin]; [exact (Hne (eq_sym Heq)) | exact Hin].
    - apply List.NoDup_cons; [intros Hin; exact Hin | apply List.NoDup_nil]. }
  assert (Hall : forall f, In f [f1; f2] -> rejects C f).
  { intros f Hin. destruct Hin as [Heq | Hin].
    - subst f. exact Hr1.
    - destruct Hin as [Heq | Hin].
      + subst f. exact Hr2.
      + destruct Hin. }
  specialize (Hbound [f1; f2] Hnd Hall).
  apply (proj2 (Qle_bool_iff _ _)) in Hbound.
  vm_compute in Hbound.
  discriminate.
Qed.

(* =========================================================================
   The weight bound over the classifier pinned to forced-only
   ========================================================================= *)

(** [weight_bound_T] with [Classifier.rejects_fo] in place of
    [Classifier.rejects]: the same lists, the same duplicate-freedom on
    cores, the same sum.  What changes is which inputs count as
    rejected — under the pin, an input the environment could only
    refuse by a refusal the state did not force is no longer one — and
    that direction is a WEAKENING of the bound wherever the filter's
    question is answered ([weight_bound_T_fo_of_weight_bound_T]), for
    the reason [Classifier.rejects_of_rejects_fo] gives. *)
Definition weight_bound_T_fo (C : Image) (w : FinProcInput -> Q) (M b : Q) : Prop :=
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (forall f, In f l -> rejects_fo C f) ->
    (sum_weights w l <= b * M)%Q.

Lemma weight_bound_fo_mono : forall C w M b b',
  (0 <= M)%Q -> (b <= b')%Q ->
  weight_bound_T_fo C w M b -> weight_bound_T_fo C w M b'.
Proof.
  intros C w M b b' HM Hbb' Hbound l Hnd Hall.
  eapply Qle_trans.
  - exact (Hbound l Hnd Hall).
  - apply Qmult_le_compat_r; assumption.
Qed.

Lemma weight_bound_fo_qeq : forall C w M M' b b',
  (M == M')%Q -> (b == b')%Q ->
  weight_bound_T_fo C w M b -> weight_bound_T_fo C w M' b'.
Proof.
  intros C w M M' b b' HM Hb Hbound l Hnd Hall.
  specialize (Hbound l Hnd Hall).
  rewrite HM, Hb in Hbound.
  exact Hbound.
Qed.

Lemma weight_bound_T_fo_of_weight_bound_T : forall C w M b,
  classifier_decided C ->
  weight_bound_T C w M b -> weight_bound_T_fo C w M b.
Proof.
  intros C w M b Hdec Hbound l Hnd Hall.
  apply (Hbound l Hnd).
  intros f Hin. exact (rejects_of_rejects_fo C f Hdec (Hall f Hin)).
Qed.

(** ... and it bites exactly as [weight_bound_refutable] does. *)
Lemma weight_bound_fo_refutable : forall C f1 f2,
  rejects_fo C f1 -> rejects_fo C f2 -> fin_core f1 <> fin_core f2 ->
  ~ weight_bound_T_fo C (fun _ => 1%Q) 1%Q 1%Q.
Proof.
  intros C f1 f2 Hr1 Hr2 Hne Hbound.
  assert (Hnd : List.NoDup (List.map fin_core [f1; f2])).
  { cbn [List.map].
    apply List.NoDup_cons.
    - intros Hin. destruct Hin as [Heq | Hin]; [exact (Hne (eq_sym Heq)) | exact Hin].
    - apply List.NoDup_cons; [intros Hin; exact Hin | apply List.NoDup_nil]. }
  assert (Hall : forall f, In f [f1; f2] -> rejects_fo C f).
  { intros f Hin. destruct Hin as [Heq | Hin].
    - subst f. exact Hr1.
    - destruct Hin as [Heq | Hin].
      + subst f. exact Hr2.
      + destruct Hin. }
  specialize (Hbound [f1; f2] Hnd Hall).
  apply (proj2 (Qle_bool_iff _ _)) in Hbound.
  vm_compute in Hbound.
  discriminate.
Qed.

(* =========================================================================
   The maybe bound
   ========================================================================= *)

(** The maybe bound: [C]'s maybe inputs never weigh more than [b] times
    the declared total [M], for every list whose cores are
    duplicate-free.  It is [weight_bound_T_fo] with
    [Classifier.maybe_fo] in place of [Classifier.rejects_fo]: it counts
    each valid input that does not get yes at every start state and does
    not get no at every start state.  Jason's decision on ZLIB-1
    (2026-11-03) and BET-618.

    The existing bound [weight_bound_T_fo] does not change.  It counts
    "no" and "maybe" together, as Jason said, and
    [maybe_bound_T_fo_of_weight_bound_T_fo] carries a proof of it to
    this bound.

    An image with no valid entry has an empty maybe set
    ([Classifier.maybe_fo]), so it satisfies this bound at [0] for every
    [w] and [M].  This is the route [weight_bound_T] names, and
    [Equivalence.IMAGE_WF] in the consuming checker closes it.
    [Checks.GatedSize.gate_exit2_refutes_maybe_bound_zero] refutes the
    bound at [0] for an image that exits 2. *)
Definition maybe_bound_T_fo (C : Image) (w : FinProcInput -> Q) (M b : Q) : Prop :=
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (forall f, In f l -> maybe_fo C f) ->
    (sum_weights w l <= b * M)%Q.

(** [maybe_bound_T_fo] over the maybe inputs that declare the capability
    word, in the shape of [Classifier.maybe_empty_T_fo_hwcap_rv64gc]. *)
Definition maybe_bound_T_fo_hwcap_rv64gc (C : Image) (w : FinProcInput -> Q) (M b : Q) : Prop :=
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (forall f, In f l -> maybe_fo C f /\ in_hwcap (to_proc_input f) = hwcap_rv64gc) ->
    (sum_weights w l <= b * M)%Q.

Definition maybe_bound_T_fo_hwcap_rv64gcv (C : Image) (w : FinProcInput -> Q) (M b : Q) : Prop :=
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (forall f, In f l -> maybe_fo C f /\ in_hwcap (to_proc_input f) = hwcap_rv64gcv) ->
    (sum_weights w l <= b * M)%Q.

(** An empty maybe set gives a maybe bound of [0], for every weight and
    every total: the only list whose entries are all maybe inputs is the
    empty list, and it sums to [0].  This is how a proof of the exact
    statement reaches the maybe bound, through
    [Classifier.maybe_empty_T_fo_of_decides_fo]. *)
Lemma maybe_bound_T_fo_zero_of_maybe_empty : forall C w M,
  maybe_empty_T_fo C -> maybe_bound_T_fo C w M 0.
Proof.
  intros C w M Hempty l _ Hall.
  destruct l as [| f l].
  - rewrite sum_weights_nil. rewrite Qmult_0_l. apply Qle_refl.
  - exfalso. exact (Hempty f (Hall f (or_introl eq_refl))).
Qed.

Lemma maybe_bound_T_fo_hwcap_rv64gc_zero_of_maybe_empty : forall C w M,
  maybe_empty_T_fo_hwcap_rv64gc C -> maybe_bound_T_fo_hwcap_rv64gc C w M 0.
Proof.
  intros C w M Hempty l _ Hall.
  destruct l as [| f l].
  - rewrite sum_weights_nil. rewrite Qmult_0_l. apply Qle_refl.
  - exfalso. exact (Hempty f (proj2 (Hall f (or_introl eq_refl)))
                      (proj1 (Hall f (or_introl eq_refl)))).
Qed.

Lemma maybe_bound_T_fo_hwcap_rv64gcv_zero_of_maybe_empty : forall C w M,
  maybe_empty_T_fo_hwcap_rv64gcv C -> maybe_bound_T_fo_hwcap_rv64gcv C w M 0.
Proof.
  intros C w M Hempty l _ Hall.
  destruct l as [| f l].
  - rewrite sum_weights_nil. rewrite Qmult_0_l. apply Qle_refl.
  - exfalso. exact (Hempty f (proj2 (Hall f (or_introl eq_refl)))
                      (proj1 (Hall f (or_introl eq_refl)))).
Qed.

(** A maybe bound proved at [b] is a maybe bound at any larger [b'],
    given [M] nonnegative, for the reason [weight_bound_mono] gives. *)
Lemma maybe_bound_fo_mono : forall C w M b b',
  (0 <= M)%Q -> (b <= b')%Q ->
  maybe_bound_T_fo C w M b -> maybe_bound_T_fo C w M b'.
Proof.
  intros C w M b b' HM Hbb' Hbound l Hnd Hall.
  eapply Qle_trans.
  - exact (Hbound l Hnd Hall).
  - apply Qmult_le_compat_r; assumption.
Qed.

(** The existing bound gives the maybe bound at the same [b]: the maybe
    set is inside the set [weight_bound_T_fo] counts
    ([Classifier.maybe_fo_rejects_fo]). *)
Lemma maybe_bound_T_fo_of_weight_bound_T_fo : forall C w M b,
  weight_bound_T_fo C w M b -> maybe_bound_T_fo C w M b.
Proof.
  intros C w M b H l Hnd Hall.
  apply H; [exact Hnd |].
  intros f Hin. exact (maybe_fo_rejects_fo C f (Hall f Hin)).
Qed.
